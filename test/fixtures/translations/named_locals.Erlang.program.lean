module

public import Lynx
public import Erlang.named_locals

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  #[Lynx.Term.FunEntry.apply fun lynxDispatch => fun captures args =>
      match captures, args with
      | #[vcap1], #[varg1] => Erlang.named_locals.«$lynx_fun_0/2» lynxDispatch vcap1 varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[] => Erlang.named_locals.«$lynx_fun_1/0»
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))]

@[simp]
theorem fun_table_pure_0 (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function 0 1 #[vcap1]) #[varg1] =
      Erlang.named_locals.«$lynx_fun_0/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1 varg1 :=
  Lynx.Dispatcher.pure_apply (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_0 (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function 0 1 #[vcap1]) #[varg1] =
      Lynx.Result.ofExcept
        (Erlang.named_locals.«$lynx_fun_0/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
          varg1) :=
  Lynx.Dispatcher.call_apply (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_pure_1 (depth : Nat) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 0 #[])
        #[] =
      Erlang.named_locals.«$lynx_fun_1/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 1) (arity := 0)
    (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_1 (depth : Nat) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 0 #[])
        #[] =
      Lynx.Result.ofExcept Erlang.named_locals.«$lynx_fun_1/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 1) (arity := 0)
    (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

end

end Erlang.program
