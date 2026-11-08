module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.functions

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  [Lynx.Term.FunDef.mk "functions" "-make/1-fun-0-" 1
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [vcap1], [varg1] => Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "functions" "-make_store/1-fun-0-" 1
      (Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
        match (captures).toList, (args).toList with
        | [vcap1], [varg1] => Erlang.functions.«-make_store/1-fun-0-/2» lynxDispatch vcap1 varg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "functions" "inc" 1
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [varg1] => Erlang.functions.«inc/1» varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "functions" "remember" 1
      (Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
        match (captures).toList, (args).toList with
        | [], [varg1] => Erlang.functions.«remember/1» lynxDispatch varg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "functions" "zero" 0
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [] => Erlang.functions.«zero/0»
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

@[simp]
theorem «functions:-make/1-fun-0-/1».pure (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "-make/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "-make/1-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «functions:-make/1-fun-0-/1».call (depth : Nat) (vcap1 : Lynx.Term) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "-make/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "-make/1-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «functions:-make_store/1-fun-0-/1».call (depth : Nat) (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function "functions" "-make_store/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.functions.«-make_store/1-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
        varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (depth := depth) (module := "functions")
    (name := "-make_store/1-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments := #[varg1])
    (by rfl) (by rfl)

@[simp]
theorem «functions:inc/1».pure (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "inc" 1 #[]) #[varg1] =
      Erlang.functions.«inc/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "inc") (arity := 1) (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «functions:inc/1».call (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "inc" 1 #[]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«inc/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "inc") (arity := 1) (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «functions:remember/1».call (depth : Nat) (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function "functions" "remember" 1 #[]) #[varg1] =
      Erlang.functions.«remember/1» (Lynx.Dispatcher.ofTable fun_table depth) varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (depth := depth) (module := "functions")
    (name := "remember") (arity := 1) (captures := #[]) (arguments := #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «functions:zero/0».pure (depth : Nat) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "zero" 0 #[]) #[] =
      Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "zero") (arity := 0) (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

@[simp]
theorem «functions:zero/0».call (depth : Nat) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "functions" "zero" 0 #[]) #[] =
      Lynx.Result.ofExcept Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "functions") (name :=
    "zero") (arity := 0) (captures := #[]) (arguments := #[]) (by rfl) (by rfl)

end

end Erlang.program
