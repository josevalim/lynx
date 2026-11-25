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

    open Lynx Lynx.Concurrent

    namespace ServerProof

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
        rcases talks with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

    /-- What the server replies for a list of integers. -/
    def doubled : Term → Term
      | .cons (.integer n) rest => .cons (.integer (n * 2)) (doubled rest)
      | other => other

    /-- The requests queued at the server for a list. -/
    def requests : Term → List Entry
      | .cons x rest => ⟨[], .message (.tuple #[.atom "request", x])⟩ :: requests rest
      | _ => []

    /-- A queue of messages from processes. -/
    def Messages (queue : List Entry) : Prop :=
      ∀ entry ∈ queue, (∃ message, entry.signal = .message message) ∧ entry.source ≠ clock

    theorem requests_quiet (xs : Term) : Messages (requests xs) := by
      induction xs using requests.induct with
      | case1 x rest ih =>
        simp only [Messages, requests, List.mem_cons, forall_eq_or_imp]
        exact ⟨⟨⟨_, rfl⟩, by simp [clock]⟩, ih⟩
      | case2 xs notCons => cases xs <;> simp_all [requests, Messages]

    /-- The length of a list term, which bounds the steps of each phase. -/
    def len : Term → Nat
      | .cons _ rest => len rest + 1
      | _ => 0

    /-- A record of a process that only queues messages and handles them into its mailbox. -/
    theorem quiet_record {children : Nat} {queue : List Entry} {mailbox : List Term}
        (messages : Messages queue) : ({ children, queue, mailbox } : ProcessState).Quiet :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, messages⟩

    theorem messages_nil : Messages [] := by simp [Messages]

    theorem messages_request {rest : List Entry} (message : Term) (messages : Messages rest) :
        Messages (⟨[], .message message⟩ :: rest) := by
      simp only [Messages, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨⟨_, rfl⟩, by simp [clock]⟩, messages⟩

    theorem messages_reply (message : Term) : Messages [⟨[1], .message message⟩] := by simp [Messages, clock]

    theorem normalize_two {first second : PID} {record record' : ProcessState} {timers : List Timer}
        {elapsed : PID → Nat → Nat} (quiet : record.Quiet) (quiet' : record'.Quiet) :
        ({ processes := [(first, record), (second, record')], timers, elapsed } : State).normalize =
          { processes := [(first, record), (second, record')], timers, elapsed } :=
      State.normalize_of_quiet (by simp [quiet, quiet'])

    theorem root_server : @BEq.beq (List Nat) Kernel.pidBEq [1] [] = false := rfl

    theorem messages_append {sent : List Entry} (message : Term) (messages : Messages sent) :
        Messages (sent ++ [⟨[], .message message⟩]) := by
      intro entry mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | rfl
      · exact messages entry mem
      · exact ⟨⟨_, rfl⟩, by simp [clock]⟩

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
      · have serve_talks : ∀ (d : Dispatcher) (xs : Term), («serve/2» d (.pid []) xs).Talks talk [1] := by
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
                simp only [Result.ofExcept, Result.ok_bind, Erlang.erlang.«send/2», Result.send_bind]
                exact .send (.inr ⟨rfl, rfl⟩) ih
          | case3 d _ _ deeper =>
            rcases d with ⟨_, _, _, _ | inner⟩
            · simp [«serve/2»]; exact .error
            · exact absurd rfl (deeper _ _ _ inner)
          | case4 => simp [«serve/2»]; exact .error
        have request_talks : ∀ (d : Dispatcher) (xs : Term) (next : Term → Result)
              (talks : ∀ value, (next value).Talks talk []),
            («request/2» d (.pid [1]) xs >>= next).Talks talk [] := by
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
              (talks : ∀ value, (next value).Talks talk []),
            («collect/1» d xs >>= next).Talks talk [] := by
          intro d xs next talks
          induction d, xs using «collect/1».induct generalizing next with
          | case1 => simpa [«collect/1»] using talks _
          | case2 _ rest _ _ _ _ ih =>
            rw [«collect/1»]
            simp only [Result.receiveWith, ReceiveTimeout.ofTerm, Result.ok_bind, Result.receive_bind]
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
        -- The root spawns the server alone, then both only talk to each other.
        have started : ∀ elapsed, (Config.start {} (Lynx.apply «double_all_doubles:ensures/1» Erlang.program.fun_table
            (depth + len xs + 1) xs) elapsed).advance 3 =
            .running { processes := [([], { children := 1 }), ([1], {})], elapsed }
              [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1]) xs >>=
                  fun _ => «collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) xs >>=
                    fun collected => Result.ofExcept («double/1» xs) >>=
                      fun expected => Result.ofExcept (Erlang.erlang.«==/2» collected expected), some, none⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs)) (.pid []) xs))]
              none false := by
          intro elapsed
          simp [Lynx.apply_eq, «double_all_doubles:ensures/1», «double_all/1»,
            Erlang.erlang.«self/0», Erlang.erlang.«spawn/1», get, getThe, MonadStateOf.get,
            Config.advance, Config.successors, splits, Task.transitions, Task.own, Task.handle, isRequest, State.spawnWith,
            State.initial, State.process, Task.root, Transition.apply, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq,
            Kernel.filterMap_eq, State.record, Kernel.lookup_eq,
            Erlang.program.«Elixir.ServerProofsTest:-double_all/1-fun-0-/0».call, «-double_all/1-fun-0-/2»]
          rw [State.normalize_of_quiet (by simp [State.set, insertRecord, Kernel.insertSorted_eq, insertSorted, Kernel.filter_eq, pidBefore,
            ProcessState.Quiet])]
          simp [State.set, insertRecord, Kernel.insertSorted_eq, insertSorted, Kernel.filter_eq, pidBefore]
        have raceFree : ∀ elapsed, RaceFree (Config.start {} (Lynx.apply «double_all_doubles:ensures/1»
            Erlang.program.fun_table (depth + len xs + 1) xs) elapsed) := by
          intro elapsed
          refine RaceFree.of_advance 3 (fun step below => ?_) ?_
          · match step, below with
            | 0, _ | 1, _ | 2, _ =>
              simp [Lynx.apply_eq, «double_all_doubles:ensures/1», «double_all/1»,
                Erlang.erlang.«self/0», Erlang.erlang.«spawn/1», get, getThe, MonadStateOf.get,
                Config.advance, Config.successors, splits, Task.transitions, Task.own, Task.handle, isRequest,
                State.spawnWith, State.initial, State.process, Task.root, Transition.apply, Kernel.append_eq,
                Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq, State.record, Kernel.lookup_eq, State.phases,
                State.exitLinks, State.phase, State.firing, firstOfEach]
          · obtain ⟨events, run⟩ := Config.run_advance 3 (Config.start {} (Lynx.apply «double_all_doubles:ensures/1»
              Erlang.program.fun_table (depth + len xs + 1) xs) elapsed)
            rw [started] at run ⊢
            refine RaceFree.of_talks single run ?_ ?_
            · refine ⟨⟨rfl, rfl⟩, fun processId process found => ?_⟩
              simp only [State.record, Kernel.lookup_eq, List.lookup_cons, List.lookup_nil] at found
              split at found <;> (try split at found) <;> simp only [Option.some.injEq, reduceCtorEq] at found <;>
                subst found <;> simp [ProcessState.Quiet]
            · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
              refine ⟨⟨trivial, request_talks _ _ _ fun _ => collect_talks _ _ _ fun doubled => ?_⟩,
                ⟨rfl, serve_talks _ _⟩⟩
              cases «double/1» xs <;> simp only [Result.ofExcept, Result.ok_bind, Result.error_bind]
              · exact .error
              · cases Erlang.erlang.«==/2» doubled _ <;> first | exact .ok | exact .error
        -- The root sends every request while the server waits.
        have requests_phase : ∀ elapsed (R : Term → Result) (server : Concurrent.Task Term) (ys : Term)
            (valid : «is_integer_list/1» ys = .ok (.atom "true")) (sent : List Entry) (messages : Messages sent),
            (Config.running { processes := [([], { children := 1 }), ([1], { queue := sent })], elapsed }
              [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1]) ys >>= R,
                some, none⟩), ([1], server)] none false).advance (len ys) =
            .running { processes := [([], { children := 1 }), ([1], { queue := sent ++ requests ys })], elapsed }
              [([], ⟨R (.atom "ok"), some, none⟩), ([1], server)] none false := by
          intro elapsed R server ys valid sent messages
          induction ys using «request/2».induct generalizing sent with
          | case1 => simp [«request/2», len, requests]
          | case2 x rest ih =>
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simp only [«is_integer_list/1»] at valid
              cases x <;> simp [Erlang.erlang.«is_integer/1»] at valid <;> exact valid
            rw [show len (.cons x rest) = 1 + len rest by simp [len]; omega, Config.advance_add]
            have step : (Config.running { processes := [([], { children := 1 }), ([1], { queue := sent })], elapsed }
                [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1])
                  (.cons x rest) >>= R, some, none⟩), ([1], server)] none false).advance 1 =
                .running { processes := [([], { children := 1 }),
                  ([1], { queue := sent ++ [⟨[], .message (.tuple #[.atom "request", x])⟩] })], elapsed }
                  [([], ⟨«request/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len xs + 1)) (.pid [1]) rest >>= R,
                    some, none⟩), ([1], server)] none false := by
              rw [«request/2»]
              simp [root_server, Config.advance, Config.successors, splits, Task.transitions, Task.own,
                Erlang.erlang.«send/2», Transition.apply, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, State.send,
                State.enqueue, State.process, State.record, Kernel.lookup_eq, State.set, insertRecord, Kernel.insertSorted_eq, insertSorted,
                Kernel.filter_eq, pidBefore, List.lookup, normalize_two, quiet_record, messages_nil,
                messages_append _ messages]
            rw [step, ih validRest _ (messages_append _ messages)]
            simp [requests]
          | case3 ys notNil notCons =>
            cases ys <;> simp [«is_integer_list/1»] at valid notNil notCons
        -- The server answers each request, then the root collects the reply, in five steps.
        have round : ∀ elapsed (K : Term → Result) (n : Int) (rest : Term)
            (shape : rest = .nil ∨ ∃ y rest', rest = .cons y rest'),
            (Config.running { processes := [([], { children := 1 }), ([1], { queue := requests (.cons (.integer n) rest) })], elapsed }
              [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table
                  (depth + len (.cons (.integer n) rest) + 1)) (.cons (.integer n) rest) >>= K, some, none⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table
                  (depth + len (.cons (.integer n) rest))) (.pid []) (.cons (.integer n) rest)))]
              none false).advance 5 =
            .running { processes := [([], { children := 1 }), ([1], { queue := requests rest })], elapsed }
              [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest + 1)) rest >>=
                  fun r => K (.cons (.integer (n * 2)) r), some, none⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len rest))
                  (.pid []) rest))]
              none false := by
          intro elapsed K n rest shape
          rw [«collect/1».eq_def _ (.cons (.integer n) _), «serve/2».eq_def _ _ (.cons (.integer n) _)]
          rcases shape with rfl | ⟨y, rest', rfl⟩ <;>
          simp (maxDischargeDepth := 4) [Config.advance, Config.successors, splits, Task.transitions, Task.own, Task.handle, Task.child,
            Result.receiveWith, ReceiveTimeout.ofTerm, State.view, State.process, State.record, Kernel.lookup_eq,
            List.lookup, root_server, requests, selectMessage,
            Erlang.erlang.«send/2», Transition.apply, State.handle, State.append, State.modify, State.set, insertRecord, Kernel.insertSorted_eq,
            insertSorted, Kernel.filter_eq, pidBefore, State.send, State.enqueue, len, Dispatcher.ofTable,
            Dispatcher.step, Kernel.append_eq, Kernel.flatMap_eq, Kernel.map_eq, Kernel.filterMap_eq, State.phases,
            State.exitLinks, State.phase, State.firing, firstOfEach, State.awaitedEntry, normalize_two, quiet_record,
            requests_quiet, messages_nil, messages_reply, messages_request]
        -- Every request is answered.
        have replies_phase : ∀ elapsed (K : Term → Result) (zs : Term)
            (valid : «is_integer_list/1» zs = .ok (.atom "true")),
            (Config.running { processes := [([], { children := 1 }), ([1], { queue := requests zs })], elapsed }
              [([], ⟨«collect/1» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs + 1)) zs >>= K, some, none⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + len zs)) (.pid []) zs))]
              none false).advance (5 * len zs) =
            .running { processes := [([], { children := 1 }), ([1], {})], elapsed }
              [([], ⟨K (doubled zs), some, none⟩),
               ([1], Task.child («serve/2» (Dispatcher.ofTable Erlang.program.fun_table depth) (.pid []) .nil))]
              none false := by
          intro elapsed K zs valid
          induction zs using «request/2».induct generalizing K with
          | case1 => simp [«collect/1», len, doubled, requests]
          | case2 x rest ih =>
            obtain ⟨n, rfl⟩ : ∃ n, x = .integer n := by
              cases x <;> simp [«is_integer_list/1», Erlang.erlang.«is_integer/1»] at valid ⊢
            have validRest : «is_integer_list/1» rest = .ok (.atom "true") := by
              simpa [«is_integer_list/1», Erlang.erlang.«is_integer/1»] using valid
            have shape : rest = .nil ∨ ∃ y rest', rest = .cons y rest' := by
              cases rest <;> simp [«is_integer_list/1»] at validRest ⊢
            rw [show 5 * len (.cons (.integer n) rest) = 5 + 5 * len rest by simp [len]; omega,
              Config.advance_add, round elapsed K n rest shape, ih (fun r => K (.cons (.integer (n * 2)) r)) validRest]
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
        refine concurrent_of_advance _ (3 + len xs + 5 * len xs + 2) raceFree fun elapsed => ?_
        rw [Config.advance_add, Config.advance_add, Config.advance_add, started elapsed,
          requests_phase elapsed _ _ xs valid [] messages_nil]
        simp only [List.nil_append]
        rw [replies_phase elapsed _ xs valid]
        -- The root compares the doubled list with itself, then both processes end.
        simp [double_ok xs valid, Erlang.erlang.«==/2», Config.advance, Config.successors, splits,
          Task.transitions, Task.own, Task.ended, Task.handle, Task.child, «serve/2», Transition.apply, State.terminate,
          State.process, State.record, Kernel.lookup_eq, List.lookup, root_server,
          State.set, insertRecord, Kernel.insertSorted_eq, insertSorted, Kernel.filter_eq, pidBefore, Kernel.append_eq, Kernel.flatMap_eq,
          Kernel.map_eq, Kernel.filterMap_eq, Kernel.foldl_eq, State.normalize_eq, State.normalizeRecord, State.phases,
          State.exitLinks, State.phase, State.firing, firstOfEach, Config.outcome, Lynx.Term.true, ProcessState.finished]
      """
  end

  defp is_integer_list([h | t]), do: is_integer(h) and is_integer_list(t)
  defp is_integer_list([]), do: true
  defp is_integer_list(_), do: false
end
