module

public import Lynx
import Lynx.Runner.Elab
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

@[simp]
theorem fun_table_pure_0 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 0 1 #[])
        #[varg1] =
      Erlang.higher_order.«$lynx_fun_0/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_0 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 0 1 #[])
        #[varg1] =
      Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_0/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_pure_1 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 1 #[])
        #[varg1] =
      Erlang.higher_order.«$lynx_fun_1/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 1) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_1 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 1 #[])
        #[varg1] =
      Lynx.Result.ofExcept (Erlang.higher_order.«$lynx_fun_1/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 1) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

end

end Erlang.program
