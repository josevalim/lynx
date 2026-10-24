module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.functions

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  #[Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[vcap1], #[varg1] => Erlang.functions.«$lynx_fun_0/2» vcap1 varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.functions.«inc/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.functions.«remember/1» lynxDispatch varg1
      | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
      match captures, args with
      | #[vcap1], #[varg1] => Erlang.functions.«$lynx_fun_3/2» lynxDispatch vcap1 varg1
      | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[varg1] => Erlang.functions.«$lynx_fun_4/1» varg1
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[] => Erlang.functions.«zero/0»
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))]

@[simp]
theorem fun_table_pure_0 (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 0 1 #[vcap1])
        #[varg1] =
      Erlang.functions.«$lynx_fun_0/2» vcap1 varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_0 (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 0 1 #[vcap1])
        #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«$lynx_fun_0/2» vcap1 varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 0) (arity := 1)
    (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_pure_1 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 1 #[])
        #[varg1] =
      Erlang.functions.«inc/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 1) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_1 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 1 1 #[])
        #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«inc/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 1) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_2 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function 2 1 #[]) #[varg1] =
      Erlang.functions.«remember/1» (Lynx.Dispatcher.ofTable fun_table depth) varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (depth := depth) (id := 2) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_3 (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function 3 1 #[vcap1]) #[varg1] =
      Erlang.functions.«$lynx_fun_3/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1 varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (depth := depth) (id := 3) (arity := 1)
    (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_pure_4 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 4 1 #[])
        #[varg1] =
      Erlang.functions.«$lynx_fun_4/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 4) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_4 (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 4 1 #[])
        #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«$lynx_fun_4/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 4) (arity := 1)
    (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem fun_table_pure_5 (depth : Nat) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 5 0 #[])
        #[] =
      Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (id := 5) (arity := 0)
    (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

@[simp]
theorem fun_table_call_5 (depth : Nat) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth) (Lynx.Term.function 5 0 #[])
        #[] =
      Lynx.Result.ofExcept Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (id := 5) (arity := 0)
    (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

end

end Erlang.program
