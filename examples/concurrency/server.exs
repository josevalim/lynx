# LYNX_DEBUG=lean LYNX_CACHE=0 mix run examples/concurrency/server.exs
#
# A client spawns a server, sends it every element of a list, and collects the
# replies. The law holds for every run. The proof shows that the program
# has no races, since each process only talks to the other, so one run
# determines the outcome of every run, then evaluates that run for any
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

    open Lynx Lynx.Concurrent

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

    /-- The requests in transit from the root to the server for a list. -/
    def requests : Term → List Envelope
      | .cons x rest => ⟨[], [1], .message (.tuple #[.atom "request", x])⟩ :: requests rest
      | _ => []

    /-- A signal that comes before none of the signals in transit goes last. -/
    theorem enqueue_last {envelope : Envelope} {inTransit : List Envelope}
        (after : ∀ other ∈ inTransit, envelope.before other = false) :
        enqueue envelope inTransit = inTransit ++ [envelope] := by
      induction inTransit with
      | nil => rfl
      | cons head rest ih =>
        simp only [enqueue, after head (by simp), Bool.false_eq_true, ↓reduceIte, List.cons_append]
        rw [ih fun other mem => after other (by simp [mem])]

    theorem mem_requests {xs : Term} {envelope : Envelope} (mem : envelope ∈ requests xs) :
        envelope.source = [] ∧ envelope.target = [1] := by
      induction xs using requests.induct with
      | case1 x rest ih =>
        simp only [requests, List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact ⟨rfl, rfl⟩
        · exact ih mem
      | case2 xs notCons => cases xs <;> simp_all [requests]

    /-- Replies are sent after every request. -/
    theorem enqueue_reply {xs : Term} {message : Term} :
        enqueue ⟨[1], [], .message message⟩ (requests xs) = requests xs ++ [⟨[1], [], .message message⟩] :=
      enqueue_last fun other mem => by
        obtain ⟨source, target⟩ := mem_requests mem
        simp [Envelope.before, source, target, pidBefore]

    /-- Requests are signals of a single pair, which arrive one at a time. -/
    theorem deliverableFrom_requests (xs : Term) (before : List Envelope) (seen : List (PID × PID))
        (contains : seen.contains ([], [1]) = true) (tail : List Envelope) :
        deliverableFrom before seen (requests xs ++ tail) =
          deliverableFrom (before ++ requests xs) seen tail := by
      induction xs using requests.induct generalizing before with
      | case1 x rest ih =>
        simp only [requests, List.cons_append, deliverableFrom, contains, ↓reduceIte]
        rw [ih]; simp
      | case2 xs notCons =>
        cases xs <;> simp_all [requests]

    theorem deliverableFrom_requests_nil (xs : Term) (before : List Envelope) (seen : List (PID × PID))
        (contains : seen.contains ([], [1]) = true) :
        deliverableFrom before seen (requests xs) = [] := by
      simpa [deliverableFrom] using deliverableFrom_requests xs before seen contains []

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
                exact .send (.inr ⟨rfl, rfl⟩) (fun _ below => by simp at below) ih
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
            exact .send (.inl ⟨rfl, rfl⟩) (fun _ below => by simp at below; omega) ih
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
              (valid : «is_integer_list/1» ys = .ok (.atom "true")) (state : State) (sent : List Envelope)
              (transit : state.inTransit = sent) (pairs : ∀ other ∈ sent, other.source = [] ∧ other.target = [1]),
            (Config.running state
                [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1))
                  (.pid [1]) ys >>= R, some⟩), ([1], server)] none false).advance (len ys) =
              .running { state with inTransit := sent ++ requests ys }
                [([], ⟨R (.atom "ok"), some⟩), ([1], server)] none false := by
          intro R server ys valid state sent transit pairs
          induction ys using «request/2».induct generalizing state sent with
          | case1 =>
            subst transit
            simp [«request/2», len, requests]
          | case2 x rest ih =>
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simp only [«is_integer_list/1»] at valid
              cases x <;> simp [Erlang.erlang.«is_integer/1»] at valid <;> exact valid
            have sentLast : enqueue ⟨[], [1], .message (.tuple #[.atom "request", x])⟩ sent =
                sent ++ [⟨[], [1], .message (.tuple #[.atom "request", x])⟩] :=
              enqueue_last fun other mem => by
                obtain ⟨source, target⟩ := pairs other mem
                simp [Envelope.before, source, target, pidBefore]
            rw [show len (.cons x rest) = 1 + len rest by simp [len]; omega, Config.advance_add]
            have step : (Config.running state
                [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1))
                  (.pid [1]) (.cons x rest) >>= R, some⟩), ([1], server)] none false).advance 1 =
                .running { state with inTransit := sent ++ [⟨[], [1], .message (.tuple #[.atom "request", x])⟩] }
                  [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1))
                    (.pid [1]) rest >>= R, some⟩), ([1], server)] none false := by
              rw [«request/2»]
              simp [Config.advance, Config.successors, splits, Task.transitions, Task.own,
                Erlang.erlang.«send/2», Transition.apply, State.emit, transit, sentLast]
            rw [step, ih validRest _ _ rfl fun other mem => by
              simp only [List.mem_append, List.mem_singleton] at mem
              rcases mem with mem | rfl
              · exact pairs other mem
              · exact ⟨rfl, rfl⟩]
            simp [requests]
          | case3 ys notNil notCons =>
            cases ys <;> simp [«is_integer_list/1»] at valid notNil notCons
        -- The server answers each request, then the root collects the reply, in five steps.
        have round : ∀ (K : Term → Result) (n : Int) (rest : Term) (state : State)
            (root server : ProcessState) (rootFound : state.processes [] = some root)
            (rootEmpty : root.mailbox = []) (serverFound : state.processes [1] = some server)
            (serverEmpty : server.mailbox = []) (transit : state.inTransit = requests (.cons (.integer n) rest))
            (idle : state.timers = []) (shape : rest = .nil ∨ ∃ y rest', rest = .cons y rest'),
            ∃ state' : State,
              (Config.running state
                [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table
                  (depth + len (.cons (.integer n) rest) + 1)) (.cons (.integer n) rest) >>= K, some⟩),
                 ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table
                   (depth + len (.cons (.integer n) rest))) (.pid []) (.cons (.integer n) rest)))]
                none false).advance 5 =
                .running state'
                  [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest + 1)) rest >>=
                    fun r => K (.cons (.integer (n * 2)) r), some⟩),
                   ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest))
                     (.pid []) rest))] none false ∧
              state'.timers = [] ∧
              state'.processes [] = some { root with mailbox := [] } ∧
              state'.processes [1] = some { server with mailbox := [] } ∧
              state'.inTransit = requests rest := by
          intro K n rest state root server rootFound rootEmpty serverFound serverEmpty transit idle shape
          rw [«collect/1».eq_def _ (.cons (.integer n) _), «serve/2».eq_def _ _ (.cons (.integer n) _)]
          rcases shape with rfl | ⟨y, rest', rfl⟩ <;>
          simp [Config.advance, Config.successors, splits, Task.transitions, Task.own, Task.deliveries,
            Task.delivery, Task.child, Result.receiveWith, ReceiveTimeout.ofTerm, State.view, State.process,
            rootFound, serverFound, rootEmpty, serverEmpty, transit, requests, deliverable, deliverableFrom,
            selectMessage, Erlang.erlang.«send/2», Transition.apply, State.update, State.modify, State.append,
            State.emit, State.receive, enqueue, enqueue_reply, deliverableFrom_requests,
            deliverableFrom_requests_nil, len, Dispatcher.ofTable, Dispatcher.step, idle,
            State.firing, firstOfEach, Envelope.before, pidBefore]
        -- Every request is answered.
        have replies_phase : ∀ (K : Term → Result) (zs : Term)
              (valid : «is_integer_list/1» zs = .ok (.atom "true")) (state : State)
              (root server : ProcessState) (rootFound : state.processes [] = some root)
              (rootEmpty : root.mailbox = []) (serverFound : state.processes [1] = some server)
              (serverEmpty : server.mailbox = []) (transit : state.inTransit = requests zs)
              (idle : state.timers = []),
            ∃ state' : State,
              (Config.running state
                  [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs + 1)) zs >>=
                    K, some⟩),
                   ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs))
                     (.pid []) zs))]
                  none false).advance (5 * len zs) =
                .running state' [([], ⟨K (doubled zs), some⟩),
                  ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table depth)
                    (.pid []) .nil))]
                  none false ∧
              state'.timers = [] ∧ state'.inTransit = [] ∧
              (∃ root', state'.processes [] = some root' ∧ root'.links = root.links ∧
                root'.monitors = root.monitors) ∧
              (∃ server', state'.processes [1] = some server' ∧ server'.links = server.links ∧
                server'.monitors = server.monitors) := by
          intro K zs valid state root server rootFound rootEmpty serverFound serverEmpty transit idle
          -- collect/1 and serve/2 also recurse on their dispatcher, so induct on
          -- the list alone, as request/2 does.
          induction zs using «request/2».induct generalizing K state root server with
          | case1 =>
            exact ⟨state, by simp [«collect/1», len, doubled], idle, by simpa [requests] using transit,
              ⟨root, rootFound, rfl, rfl⟩, ⟨server, serverFound, rfl, rfl⟩⟩
          | case2 x rest ih =>
            obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
              cases x <;> simp [«is_integer_list/1», Erlang.erlang.«is_integer/1»] at valid ⊢
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simpa [«is_integer_list/1», Erlang.erlang.«is_integer/1»] using valid
            have shape : rest = .nil ∨ ∃ y rest', rest = .cons y rest' := by
              cases rest <;> simp [«is_integer_list/1»] at validRest ⊢
            obtain ⟨state5, advanced, idle5, found, found', transit5⟩ :=
              round K n rest state root server rootFound rootEmpty serverFound serverEmpty transit idle shape
            obtain ⟨state', advanced', idle', transit', ⟨root', rootFound', links, monitors⟩,
                ⟨server', serverFound', links', monitors'⟩⟩ :=
              ih (fun r => K (.cons (.integer (n * 2)) r)) validRest state5 _ _ found rfl found' rfl
                transit5 idle5
            refine ⟨state', ?_, idle', transit', ⟨root', rootFound', links, monitors⟩,
              ⟨server', serverFound', links', monitors'⟩⟩
            rw [show 5 * len (.cons (.integer n) rest) = 5 + 5 * len rest by simp [len]; omega,
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
        -- Without races, one run determines the outcome of every run, whatever
        -- time elapses before timers are canceled.
        refine concurrent_of_advance _ (3 + len xs + 5 * len xs + 2)
          (fun _ => Config.RaceFree.of_talks single (root_talks _ xs)) fun elapsed => ?_
        -- Spawn the server.
        have start : ∃ state : State,
            (Config.start {} (Lynx.apply «double_all_doubles:ensures/1» Erlang.program.fun_table
              (depth + len xs + 1) xs) elapsed).advance 3 =
              .running state
                [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1]) xs >>=
                    fun _ => «collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) xs >>=
                      fun collected => Result.ofExcept («double/1» xs) >>=
                        fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected), some⟩),
                 ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs))
                   (.pid []) xs))]
                none false ∧
            state.timers = [] ∧ state.inTransit = [] ∧ state.processes [] = some { children := 1 } ∧
            state.processes [1] = some {} := by
          simp [Lynx.apply_eq, «double_all_doubles:ensures/1», «double_all/1»,
            Erlang.erlang.«self/0», Erlang.erlang.«spawn/1», get, getThe, MonadStateOf.get,
            Config.advance, Config.successors, splits, Task.transitions, Task.own, isRequest, State.spawnWith,
            State.spawn, State.initial, State.process, State.update, Task.root,
            Erlang.program.«Elixir.ServerProofsTest:-double_all/1-fun-0-/0».call, «-double_all/1-fun-0-/2»,
            Transition.apply]
        obtain ⟨state, started, idle, transit, rootFound, serverFound⟩ := start
        -- Send every request, then answer each.
        obtain ⟨state', replied, idle', transit', ⟨root, rootFound', rootLinks, rootMonitors⟩,
            ⟨server, serverFound', serverLinks, serverMonitors⟩⟩ := replies_phase
          (fun collected => Result.ofExcept («double/1» xs) >>=
            fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected))
          xs valid { state with inTransit := [] ++ requests xs } { children := 1 } {} rootFound rfl
          serverFound rfl (by simp) idle
        rw [Config.advance_add, Config.advance_add, Config.advance_add, started,
          requests_phase _ _ xs valid state [] transit (by simp), replied]
        -- The root compares the doubled list with itself, then both processes exit.
        simp [double_ok xs valid, Erlang.erlang.«==/2», Config.advance, Config.successors, splits,
          Task.transitions, Task.own, Task.ended, Task.deliveries, Task.child, «serve/2», Transition.apply,
          State.terminate, State.process, State.update, rootFound', serverFound', rootLinks, rootMonitors,
          serverLinks, serverMonitors, idle', transit', deliverable, deliverableFrom, State.firing,
          firstOfEach, Config.outcome, Lynx.Term.true]
      """
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
