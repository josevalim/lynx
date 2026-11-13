module

public import Lynx.Term

public section

namespace Erlang.lists
open Lynx

/-- Reverse a proper list onto an arbitrary tail, or raise `badarg`. -/
@[expose] def «reverse/2» : Term → Term → Except Exception Term
  | .nil, tail => .ok tail
  | .cons head rest, tail => «reverse/2» rest (.cons head tail)
  | _, _ => .error (.error (.atom "badarg"))

/-- Test membership by exact equality, returning at the first match. Reaching an
improper tail or a non-list raises `badarg`. -/
@[expose] def «member/2» : Term → Term → Except Exception Term
  | _, .nil => .ok Term.false
  | element, .cons head tail =>
    if Term.compareExact (Term.fuel element head) element head = .eq then .ok Term.true else «member/2» element tail
  | _, _ => .error (.error (.atom "badarg"))

/-- The first tuple whose element at a position compares equal to a key, or
`false`. Elements that are not tuples, or are shorter, are skipped. -/
@[expose] def «keyfind/3» (key position : Term) : Term → Except Exception Term
  | .nil => match position with
    | .integer index => if index ≥ 1 then .ok Term.false else .error (.error (.atom "badarg"))
    | _ => .error (.error (.atom "badarg"))
  | .cons head tail =>
    match position with
    | .integer index =>
      if index < 1 then .error (.error (.atom "badarg")) else
      match head with
      | .tuple elements =>
        match elements[index.toNat - 1]? with
        | some element =>
          if Term.compare (Term.fuel element key) element key = .eq then .ok head else «keyfind/3» key position tail
        | none => «keyfind/3» key position tail
      | _ => «keyfind/3» key position tail
    | _ => .error (.error (.atom "badarg"))
  | _ => .error (.error (.atom "badarg"))

end Erlang.lists
