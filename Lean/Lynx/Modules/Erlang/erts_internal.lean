module

public import Lynx.Term
public import Lynx.Purity

public section

/-! Internal BIFs emitted by the Erlang compiler. -/

namespace Erlang.erts_internal
open Lynx

/-- Starts a map generator in a comprehension. The iterator is returned fully
expanded as nested `{Key, Value, Next}` tuples ending in `none`, in the
unspecified order of `Term.mapEntries`. Other generators yield `[]`, which the
compiled comprehension reports as `bad_generator`. Iterators from
`maps:iterator/1` are not modeled. -/
#lynx_pure @[expose] def «mc_iterator/1» : Term → Result
  | .map entries =>
    .ok ((Term.mapEntries entries).foldr (fun entry rest => .tuple #[entry.1, entry.2, rest]) (.atom "none"))
  | _ => .ok .nil

/-- Refills a partially traversed iterator. Iterators from `mc_iterator/1` are
fully expanded, so compiled comprehensions never reach this function. -/
#lynx_pure @[expose] def «mc_refill/1» (_iterator : Term) : Result :=
  .error (.error (.atom "badarg"))

@[simp] theorem mc_refill_eq (iterator : Term) :
    «mc_refill/1» iterator = .error (.error (.atom "badarg")) := rfl

/-- Comprehensions recurse on refilled iterators, which cannot occur. Well-founded
definitions drop that recursive call before proving termination and deriving
their induction principles. -/
@[wf_preprocess ↓] theorem mc_refill_bind {α : Type} (iterator : Term) (next : Term → Result α) :
    («mc_refill/1» iterator >>= next) = .error (.error (.atom "badarg")) := rfl

end Erlang.erts_internal
