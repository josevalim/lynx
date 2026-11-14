namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! `disjoint?/2` on element types. -/

theorem not_true {c : Except Exception Term}
    (h : (do let w ← c; Erlang.erlang.«not/1» w) = .ok (.atom "true")) : c = .ok (.atom "false") := by
  cases c with
  | error e => simp at h
  | ok w =>
    change Erlang.erlang.«not/1» w = _ at h
    unfold Erlang.erlang.«not/1» at h
    split at h <;> simp_all

end Elixir.STTDescrProofsTest
