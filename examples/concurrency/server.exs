# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/concurrency/server.exs
#
# A client spawns a server, sends it every element of a list, and collects the
# replies. The law holds for every schedule. The proof shows that the program
# has no races, since each process only talks to the other, so one run
# determines the outcome of every schedule, then evaluates that run for any
# input list with Lynx.Concurrent.Config.advance.
ExUnit.start()

defmodule ServerProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  # A server process answers each request with the doubled value.
  def double_all(xs) do
    parent = self()
    server = spawn(fn -> serve(parent, xs) end)
    request(server, xs)
    collect(xs)
  end

  defp serve(_parent, []), do: :ok

  defp serve(parent, [_ | rest]) do
    receive do
      {:request, x} ->
        send(parent, {:reply, x * 2})
        serve(parent, rest)
    end
  end

  defp request(_server, []), do: :ok

  defp request(server, [x | rest]) do
    send(server, {:request, x})
    request(server, rest)
  end

  defp collect([]), do: []

  defp collect([_ | rest]) do
    receive do
      {:reply, y} -> [y | collect(rest)]
    end
  end

  def double([]), do: []
  def double([x | rest]), do: [x * 2 | double(rest)]

  laws "server" do
    prelude ~LEAN"""
    module

    public import Lynx

    @[expose] public section

    namespace ServerProof

    open Lynx

    /-- The root sends requests to the server, which replies to the root. -/
    def talk (sender receiver : PID) : Prop :=
      (sender = [] ∧ receiver = [1]) ∨ (sender = [1] ∧ receiver = [])

    theorem single : Concurrent.Single talk := by
      refine ⟨?_, ?_⟩
      · intro sender sender' receiver talks talks'
        rcases talks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases talks' with ⟨same, other⟩ | ⟨same, other⟩ <;>
          first | exact same.symm | simp at other
      · intro sender receiver talks
        rcases talks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inr ⟨1, rfl⟩
        · exact .inl ⟨[1], rfl⟩

    /-- The length of a list term, which bounds the steps of each phase. -/
    def len : Term → Nat
      | .cons _ rest => len rest + 1
      | _ => 0

    /-- What the server replies for a list of integers. -/
    def doubled : Term → Term
      | .cons (.integer n) rest => .cons (.integer (n * 2)) (doubled rest)
      | other => other

    /-- The requests the root sends for a list. -/
    def requests : Term → List Term
      | .cons x rest => .tuple #[.atom "request", x] :: requests rest
      | _ => []

    end ServerProof
    """

    law double_all_doubles(xs),
      requires: is_integer_list(xs),
      expects: double_all(xs) == double(xs),
      proof: ~LEAN"""
      -- The root receives once per element, and so does the server it spawns
      -- one level down.
      refine ⟨ServerProof.len xs + 1, fun depth deep => ?_⟩
      obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' deep
      rw [← Nat.add_assoc]
      open Lynx Lynx.Concurrent ServerProof in
      · have serve_talks : ∀ (d : Dispatcher) (xs : Term),
            («serve/2» d (.pid []) xs).Talks talk [1] 0 := by
          intro d xs
          induction d, xs using «serve/2».induct with
          | case1 => simp [«serve/2»]; exact .ok
          | case2 _ rest _ _ _ _ ih =>
            rw [«serve/2»]
            simp only [Result.receiveWith, ReceiveTimeout.ofTerm, Result.ok_bind]
            refine .receive fun reply => ?_
            cases reply with
            | none => exact .ok
            | some x =>
              simp only
              cases Erlang.erlang.«*/2» x (.integer 2) with
              | error => simp [Result.ofExcept]; exact .error
              | ok v =>
                simp only [Result.ofExcept, Result.ok_bind, Erlang.erlang.«send/2»,
                  Result.send_bind]
                exact .send (.inr ⟨rfl, rfl⟩) ih
          | case3 d _ _ deeper =>
            rcases d with ⟨_, _, _, _ | inner⟩
            · simp [«serve/2»]; exact .error
            · exact absurd rfl (deeper _ _ _ inner)
          | case4 => simp [«serve/2»]; exact .error
        have request_talks : ∀ (d : Dispatcher) (xs : Term) (next : Term → Result)
              (talks : ∀ value, (next value).Talks talk [] 1),
            («request/2» d (.pid [1]) xs >>= next).Talks talk [] 1 := by
          intro d xs next talks
          induction xs using «request/2».induct with
          | case1 => simpa [«request/2»] using talks _
          | case2 x rest ih =>
            rw [«request/2»]
            simp only [Erlang.erlang.«send/2», Result.send_bind, Result.ok_bind]
            exact .send (.inl ⟨rfl, rfl⟩) ih
          | case3 _ notNil notCons =>
            rw [«request/2»]
            · simp only [Result.error_bind]; exact .error
            · exact notNil
            · exact notCons
        have collect_talks : ∀ (d : Dispatcher) (xs : Term) (next : Term → Result)
              (talks : ∀ value, (next value).Talks talk [] 1),
            («collect/1» d xs >>= next).Talks talk [] 1 := by
          intro d xs next talks
          induction d, xs using «collect/1».induct generalizing next with
          | case1 => simpa [«collect/1»] using talks _
          | case2 _ rest _ _ _ _ ih =>
            rw [«collect/1»]
            simp only [Result.receiveWith, ReceiveTimeout.ofTerm, Result.ok_bind,
              Result.receive_bind]
            refine .receive fun reply => ?_
            cases reply with
            | none => simpa using talks _
            | some y =>
              simp only [bind_assoc, Result.pure_eq_ok, Result.ok_bind]
              exact ih _ fun _ => talks _
          | case3 d _ _ deeper =>
            rcases d with ⟨_, _, _, _ | inner⟩
            · simp [«collect/1»]; exact .error
            · exact absurd rfl (deeper _ _ _ inner)
          | case4 _ _ notNil notCons =>
            rw [«collect/1»]
            · simp only [Result.error_bind]; exact .error
            · exact notNil
            · exact notCons
        -- No races: the root only sends to its child, which only replies to the root.
        have root_talks : ∀ (k : Nat) (xs : Term),
            (Lynx.apply «double_all_doubles:ensures/1» Erlang.program.fun_table (k + 1) xs).Talks
              talk [] 0 := by
          intro k xs
          simp only [Lynx.apply_eq, «double_all_doubles:ensures/1», «double_all/1»,
            Erlang.erlang.«self/0», Erlang.erlang.«spawn/1», bind_assoc, Result.ok_bind,
            Result.pure_eq_ok, Result.schedule_bind]
          refine .get fun env self => .schedule ?_ ?_
          · rw [Erlang.program.«Elixir.ServerProofsTest:-double_all/1-fun-0-/0».call, self]
            exact serve_talks _ _
          · refine request_talks _ _ _ fun _ => collect_talks _ _ _ fun doubled => ?_
            cases «double/1» xs <;>
              simp only [Result.ofExcept, Result.ok_bind, Result.error_bind]
            · exact .error
            · cases Erlang.erlang.«==/2» doubled _ <;> first | exact .ok | exact .error

        -- The root sends every request while the server waits.
        have requests_phase : ∀ (R : Term → Result) (server : Concurrent.Task Term) (ys : Term)
              (valid : «is_integer_list/1» ys = .ok (.atom "true")) (state : State)
              (process : ProcessState) (found : state.processes [1] = some process)
              (rootCalm : (state.process []).signal = none),
            ∃ state' : State, state'.processes [1] =
                some { process with mailbox := process.mailbox ++ requests ys } ∧
              (∀ other, other ≠ [1] → state'.processes other = state.processes other) ∧
              (Config.running state
                  [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1])
                    ys >>= R, some⟩), ([1], server)] none false).advance (len ys) =
                .running state' [([], ⟨R (.atom "ok"), some⟩), ([1], server)] none false := by
          intro R server ys valid state process found rootCalm
          induction ys using «request/2».induct generalizing state process with
          | case1 =>
            exact ⟨state, by simp [found, requests], fun _ _ => rfl, by simp [«request/2», len]⟩
          | case2 x rest ih =>
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simp only [«is_integer_list/1»] at valid
              cases x <;> simp [Erlang.erlang.«is_integer/1»] at valid <;> exact valid
            have delivered : (state.deliver [1] (Term.tuple #[.atom "request", x])).processes [1] =
                some { process with
                  mailbox := process.mailbox ++ [(Term.tuple #[.atom "request", x])] } := by
              simp [State.deliver, found, State.update]
            obtain ⟨state', found', others, advanced⟩ :=
              ih validRest (state.deliver [1] (Term.tuple #[.atom "request", x])) _ delivered
                (by simpa [State.deliver, found, State.update, State.process] using rootCalm)
            refine ⟨state', by simp [found', requests], fun other distinct => ?_, ?_⟩
            · rw [others other distinct]
              simp [State.deliver, found, State.update, distinct]
            · rw [show len (.cons x rest) = 1 + len rest by simp [len]; omega, Config.advance_add]
              have step : (Config.running state
                  [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1])
                    (.cons x rest) >>= R, some⟩), ([1], server)] none false).advance 1 =
                  .running (state.deliver [1] (Term.tuple #[.atom "request", x]))
                    [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1])
                      rest >>= R, some⟩), ([1], server)] none false := by
                rw [«request/2»]
                simp [Config.advance, Config.successors, splits, Task.transitions,
                  Erlang.erlang.«send/2», Transition.apply, rootCalm]
              rw [step, advanced]
          | case3 ys notNil notCons =>
            cases ys <;> simp [«is_integer_list/1»] at valid notNil notCons
        -- The server answers a request, then the root collects the reply, in three steps each.
        have replies_phase : ∀ (K : Term → Result) (zs : Term)
              (valid : «is_integer_list/1» zs = .ok (.atom "true")) (state : State)
              (root server : ProcessState) (rootFound : state.processes [] = some root)
              (rootEmpty : root.mailbox = []) (serverFound : state.processes [1] = some server)
              (serverMailbox : server.mailbox = requests zs)
              (rootCalm : root.signal = none) (serverCalm : server.signal = none)
              (rootAlone : root.links = [] ∧ root.monitors = [])
              (serverAlone : server.links = [] ∧ server.monitors = []),
            ∃ state' : State,
              (state'.process []).signal = none ∧ (state'.process [1]).signal = none ∧
              (state'.process []).links = [] ∧ (state'.process []).monitors = [] ∧
              (state'.process [1]).links = [] ∧ (state'.process [1]).monitors = [] ∧
              (Config.running state
                  [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs + 1)) zs >>=
                    K, some⟩),
                   ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs))
                     (.pid []) zs))]
                  none false).advance (3 * len zs) =
                .running state' [([], ⟨K (doubled zs), some⟩),
                  ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table depth)
                    (.pid []) .nil))]
                  none false := by
          intro K zs valid state root server rootFound rootEmpty serverFound serverMailbox rootCalm
            serverCalm rootAlone serverAlone
          -- collect/1 and serve/2 also recurse on their dispatcher, so induct on
          -- the list alone, as request/2 does.
          induction zs using «request/2».induct generalizing K state root server with
          | case1 =>
            exact ⟨state, by simp [State.process, rootFound, rootCalm],
              by simp [State.process, serverFound, serverCalm],
              by simp [State.process, rootFound, rootAlone.1],
              by simp [State.process, rootFound, rootAlone.2],
              by simp [State.process, serverFound, serverAlone.1],
              by simp [State.process, serverFound, serverAlone.2],
              by simp [«collect/1», len, doubled]⟩
          | case2 x rest ih =>
            obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
              cases x <;> simp [«is_integer_list/1», Erlang.erlang.«is_integer/1»] at valid ⊢
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simpa [«is_integer_list/1», Erlang.erlang.«is_integer/1»] using valid
            have three : ∃ state3 : State,
                state3.processes [] = some { root with mailbox := [] } ∧
                state3.processes [1] = some { server with mailbox := requests rest } ∧
                (Config.running state
                  [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table
                    (depth + len (.cons (.integer n) rest) + 1)) (.cons (.integer n) rest) >>= K, some⟩),
                   ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table
                     (depth + len (.cons (.integer n) rest))) (.pid []) (.cons (.integer n) rest)))]
                  none false).advance 3 =
                  .running state3
                    [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest + 1)) rest >>=
                      fun r => K (.cons (.integer (n * 2)) r), some⟩),
                     ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest))
                       (.pid []) rest))] none false := by
              refine ⟨?state3, ?_, ?_, ?advanced⟩
              case advanced =>
                rw [«collect/1».eq_def _ (.cons (.integer n) rest),
                  «serve/2».eq_def _ _ (.cons (.integer n) rest)]
                simp [Config.advance, Config.successors, splits, Task.transitions, Task.child,
                  Result.receiveWith, ReceiveTimeout.ofTerm, State.view, State.process, rootFound,
                  serverFound, rootEmpty, serverMailbox, requests, selectMessage,
                  Erlang.erlang.«send/2», Transition.apply, State.update, State.deliver, rootCalm,
                  serverCalm, len, Dispatcher.ofTable, Dispatcher.step]
                rfl
              all_goals simp [rootCalm, serverCalm]
            obtain ⟨state3, found, found', advanced⟩ := three
            obtain ⟨state', rootCalm', serverCalm', alone⟩ :=
              ih (fun r => K (.cons (.integer (n * 2)) r)) validRest state3 _ _ found rfl found' rfl
                rootCalm serverCalm rootAlone serverAlone
            obtain ⟨rootLinks', rootMonitors', serverLinks', serverMonitors', advanced'⟩ := alone
            refine ⟨state', rootCalm', serverCalm', rootLinks', rootMonitors', serverLinks',
              serverMonitors', ?_⟩
            rw [show 3 * len (.cons (.integer n) rest) = 3 + 3 * len rest by simp [len]; omega,
              Config.advance_add, advanced, advanced']
            rfl
          | case3 zs notNil notCons =>
            cases zs <;> simp [«is_integer_list/1»] at valid notNil notCons
        have double_ok : ∀ (xs : Term) (valid : «is_integer_list/1» xs = .ok (.atom "true")),
            «double/1» xs = .ok (doubled xs) := by
          intro xs valid
          induction xs using «double/1».induct with
          | case1 => rfl
          | case2 x rest ih =>
            obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
              cases x <;> simp [«is_integer_list/1», Erlang.erlang.«is_integer/1»] at valid ⊢
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simpa [«is_integer_list/1», Erlang.erlang.«is_integer/1»] using valid
            simp [«double/1», ih validRest, doubled]
          | case3 xs notNil notCons =>
            cases xs <;> simp [«is_integer_list/1»] at valid notNil notCons
        have valid : «is_integer_list/1» xs = .ok (.atom "true") := requires
        -- Spawn the server.
        have start : ∃ state : State, state.processes [] = some { children := 1 } ∧
            state.processes [1] = some {} ∧
            (Config.start {} (Lynx.apply «double_all_doubles:ensures/1» Erlang.program.fun_table
              (depth + len xs + 1) xs)).advance 3 =
              .running state
                [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1]) xs >>=
                    fun _ => «collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) xs >>=
                      fun collected => Result.ofExcept («double/1» xs) >>=
                        fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected), some⟩),
                 ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs))
                   (.pid []) xs))]
                none false := by
          refine ⟨?state, ?_, ?_, ?advanced⟩
          case advanced =>
            simp [Lynx.apply_eq, «double_all_doubles:ensures/1», «double_all/1»,
              Erlang.erlang.«self/0», Erlang.erlang.«spawn/1», get, getThe, MonadStateOf.get,
              Config.advance, Config.successors, splits, Task.transitions, isRequest, State.spawnWith,
              State.spawn,
              State.initial, State.process, State.update, Task.root,
              Erlang.program.«Elixir.ServerProofsTest:-double_all/1-fun-0-/0».call, «-double_all/1-fun-0-/2», Transition.apply]
            rfl
          all_goals simp
        obtain ⟨state, rootFound, serverFound, started⟩ := start
        -- Send every request.
        obtain ⟨state', serverFound', others, requested⟩ := requests_phase
          (fun _ => «collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) xs >>=
            fun collected => Result.ofExcept («double/1» xs) >>=
              fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected))
          (Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs)) (.pid []) xs))
          xs valid state _ serverFound (by simp [State.process, rootFound])
        -- Answer every request.
        obtain ⟨state'', rootCalm'', serverCalm'', rootLinks'', rootMonitors'', serverLinks'',
          serverMonitors'', replied⟩ := replies_phase
          (fun collected => Result.ofExcept («double/1» xs) >>=
              fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected))
          xs valid state' { children := 1 } _
          (by rw [others [] (by simp), rootFound]) rfl serverFound' (by simp) rfl (by simp)
          ⟨rfl, rfl⟩ (by simp)
        have total : (Config.start {}
            (Lynx.apply «double_all_doubles:ensures/1» Erlang.program.fun_table (depth + len xs + 1) xs)).advance
              (3 + len xs + 3 * len xs + 2) =
            (Config.running state''
              [([], ⟨Result.ofExcept («double/1» xs) >>=
                  fun expected => Result.ofExcept (Erlang.erlang.«==/2» (doubled xs) expected), some⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table depth)
                 (.pid []) .nil))]
              none false).advance 2 := by
          rw [Config.advance_add, Config.advance_add, Config.advance_add, started, requested]
          exact congrArg (Config.advance 2) replied
        -- Neither process is linked or monitored, so each exit only removes it.
        have rootExit : state''.terminate [] (.atom "normal") = state''.update [] none := by
          simp [State.terminate, rootLinks'', rootMonitors'']
        have serverRecord : (state''.update [] none).process [1] = state''.process [1] := by
          simp [State.process, State.update]
        have serverCalmAfter : ((state''.update [] none).process [1]).signal = none := by
          rw [serverRecord]; exact serverCalm''
        have serverExit : (state''.update [] none).terminate [1] (.atom "normal") =
            (state''.update [] none).update [1] none := by
          simp [State.terminate, serverRecord, serverLinks'', serverMonitors'']
        -- The root compares the doubled list with itself, then both processes exit.
        have finished : (Config.running state''
              [([], ⟨Result.ofExcept («double/1» xs) >>=
                  fun expected => Result.ofExcept (Erlang.erlang.«==/2» (doubled xs) expected), some⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table depth)
                 (.pid []) .nil))]
              none false).advance 2 =
            .running ((state''.update [] none).update [1] none) []
              (some (.ok Lynx.Term.true, state''.view [])) false := by
          simp [double_ok xs valid, Erlang.erlang.«==/2», Config.advance, Config.successors,
            splits, Task.transitions, Task.child, «serve/2», Transition.apply, Lynx.Term.true,
            rootCalm'', rootExit, serverCalmAfter, serverExit]
        -- Without races, this run determines the outcome of every schedule.
        rw [concurrent_eq_advance _ (Config.RaceFree.of_talks single (root_talks _ xs)) _
          (by rw [total, finished]; rfl) schedule, total, finished]
        rfl
      """
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
