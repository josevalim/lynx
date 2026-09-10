import Lynx.Term
import Lynx.Term.Map
import Lynx.Tactic

namespace Lynx.Modules.Maps
open Term.Map

#lynx_pure def new_0 : Result := .ok Term.emptyMap

#lynx_pure @[lynx_opaque] def get_2 (key input : Term) : Result :=
  match input with
  | .map entries =>
    match find key entries with
    | some v => .ok v
    | none => .error (.error (.tuple #[.atom "badkey", key]))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[simp] theorem get_map (k : Term) (entries : Entries) :
    get_2 k (.map entries) = match find k entries with
      | some v => .ok v
      | none => .error (.error (.tuple #[.atom "badkey", k])) := rfl

#lynx_pure @[lynx_opaque] def put_3 (key value input : Term) : Result :=
  match input with
  | .map entries => .ok (.map (put key value entries))
  | _ => .error (.error (.tuple #[.atom "badmap", input]))

@[simp] theorem put_map (k v : Term) (entries : Entries) :
    put_3 k v (.map entries) = .ok (.map (put k v entries)) := rfl

#lynx_pure @[lynx_opaque] def merge_2 (left right : Term) : Result :=
  match left, right with
  | .map a, .map b => .ok (.map (merge a b))
  | .map _, _ => .error (.error (.tuple #[.atom "badmap", right]))
  | _, _ => .error (.error (.tuple #[.atom "badmap", left]))

@[simp] theorem merge_map (a b : Entries) :
    merge_2 (.map a) (.map b) = .ok (.map (merge a b)) := rfl

@[simp] theorem merge_empty_right (entries : Entries) :
    merge_2 (.map entries) Term.emptyMap = .ok (.map entries) := rfl

end Lynx.Modules.Maps
