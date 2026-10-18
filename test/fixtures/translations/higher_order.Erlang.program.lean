module

public import Lynx
public import Erlang.higher_order

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  #[Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.higher_order.«$lynx_fun_0/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.higher_order.«$lynx_fun_1/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))]

@[simp↓]
theorem fun_table_apply_0_bind {α : Type} (depth : Nat) (varg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Term.apply (Lynx.Term.function 0 1 #[]) #[varg1] >>= next) =
      Lynx.Result.resolve fun_table depth
        (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_0/1» varg1) >>= next) :=
  Lynx.Result.resolve_apply_pure fun_table depth 0 1 #[] #[varg1]
    (fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.higher_order.«$lynx_fun_0/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
    next (by rfl) (by rfl)

@[simp↓]
theorem fun_table_apply_0_bind_explicit {α : Type} (depth : Nat) (varg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 0 1 #[]) #[varg1]) next) =
      Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_0/1» varg1))
          next) :=
  by exact fun_table_apply_0_bind depth varg1 next

@[simp]
theorem fun_table_apply_0 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table depth (Lynx.Term.apply (Lynx.Term.function 0 1 #[]) #[varg1]) =
      Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_0/1» varg1) :=
  by
  simpa only [(Lynx.Result.bind_ok),
    (Lynx.Result.resolve_of_isPure fun_table depth
        (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_0/1» varg1)) (by simp))] using
    fun_table_apply_0_bind depth varg1 (fun value => Lynx.Result.ok value)

@[simp↓]
theorem fun_table_apply_1_bind {α : Type} (depth : Nat) (varg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Term.apply (Lynx.Term.function 1 1 #[]) #[varg1] >>= next) =
      Lynx.Result.resolve fun_table depth
        (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_1/1» varg1) >>= next) :=
  Lynx.Result.resolve_apply_pure fun_table depth 1 1 #[] #[varg1]
    (fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.higher_order.«$lynx_fun_1/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
    next (by rfl) (by rfl)

@[simp↓]
theorem fun_table_apply_1_bind_explicit {α : Type} (depth : Nat) (varg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 1 1 #[]) #[varg1]) next) =
      Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_1/1» varg1))
          next) :=
  by exact fun_table_apply_1_bind depth varg1 next

@[simp]
theorem fun_table_apply_1 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table depth (Lynx.Term.apply (Lynx.Term.function 1 1 #[]) #[varg1]) =
      Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_1/1» varg1) :=
  by
  simpa only [(Lynx.Result.bind_ok),
    (Lynx.Result.resolve_of_isPure fun_table depth
        (Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_1/1» varg1)) (by simp))] using
    fun_table_apply_1_bind depth varg1 (fun value => Lynx.Result.ok value)

end

end Erlang.program
