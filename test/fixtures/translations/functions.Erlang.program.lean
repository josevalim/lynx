module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.functions

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  [Lynx.Term.FunDef.mk "functions" "zero" 0
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [] => Erlang.functions.«zero/0»
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "functions" "-make/1-fun-0-" 1
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
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

private theorem fun_table.sorted : Lynx.Dispatcher.sorted fun_table = true := by decide +kernel

private theorem «functions:zero/0».entry :
    Lynx.Dispatcher.find fun_table "functions" "zero" 0 =
      some
        (Lynx.Term.FunEntry.pure fun captures args =>
          match (captures).toList, (args).toList with
          | [], [] => Erlang.functions.«zero/0»
          | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 0) fun_table.sorted rfl

@[simp]
theorem «functions:zero/0».pure (depth : Nat) {external : Bool} :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "zero" 0 #[]) #[] =
      Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "zero") (arity := 0) (captures := #[]) (arguments := #[])
    «functions:zero/0».entry (by rfl)

@[simp]
theorem «functions:zero/0».call (depth : Nat) {external : Bool} :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "zero" 0 #[]) #[] =
      Lynx.Result.ofExcept Erlang.functions.«zero/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "zero") (arity := 0) (captures := #[]) (arguments := #[])
    «functions:zero/0».entry (by rfl)

private theorem «functions:-make/1-fun-0-/1».entry :
    Lynx.Dispatcher.find fun_table "functions" "-make/1-fun-0-" 1 =
      some
        (Lynx.Term.FunEntry.pure fun captures args =>
          match (captures).toList, (args).toList with
          | [vcap1], [varg1] => Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1
          | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 1) fun_table.sorted rfl

@[simp]
theorem «functions:-make/1-fun-0-/1».pure (depth : Nat) {external : Bool} (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "-make/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "-make/1-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments :=
    #[varg1]) «functions:-make/1-fun-0-/1».entry (by rfl)

@[simp]
theorem «functions:-make/1-fun-0-/1».call (depth : Nat) {external : Bool} (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "-make/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«-make/1-fun-0-/2» vcap1 varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "-make/1-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments :=
    #[varg1]) «functions:-make/1-fun-0-/1».entry (by rfl)

private theorem «functions:-make_store/1-fun-0-/1».entry :
    Lynx.Dispatcher.find fun_table "functions" "-make_store/1-fun-0-" 1 =
      some
        (Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
          match (captures).toList, (args).toList with
          | [vcap1], [varg1] => Erlang.functions.«-make_store/1-fun-0-/2» lynxDispatch vcap1 varg1
          | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 2) fun_table.sorted rfl

@[simp]
theorem «functions:-make_store/1-fun-0-/1».call (depth : Nat) {external : Bool} (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function external "functions" "-make_store/1-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.functions.«-make_store/1-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
        varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (external := external) (depth := depth)
    (module := "functions") (name := "-make_store/1-fun-0-") (arity := 1) (captures := #[vcap1])
    (arguments := #[varg1]) «functions:-make_store/1-fun-0-/1».entry (by rfl)

private theorem «functions:inc/1».entry :
    Lynx.Dispatcher.find fun_table "functions" "inc" 1 =
      some
        (Lynx.Term.FunEntry.pure fun captures args =>
          match (captures).toList, (args).toList with
          | [], [varg1] => Erlang.functions.«inc/1» varg1
          | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 3) fun_table.sorted rfl

@[simp]
theorem «functions:inc/1».pure (depth : Nat) {external : Bool} (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "inc" 1 #[]) #[varg1] =
      Erlang.functions.«inc/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "inc") (arity := 1) (captures := #[]) (arguments := #[varg1])
    «functions:inc/1».entry (by rfl)

@[simp]
theorem «functions:inc/1».call (depth : Nat) {external : Bool} (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "functions" "inc" 1 #[]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.functions.«inc/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "functions") (name := "inc") (arity := 1) (captures := #[]) (arguments := #[varg1])
    «functions:inc/1».entry (by rfl)

private theorem «functions:remember/1».entry :
    Lynx.Dispatcher.find fun_table "functions" "remember" 1 =
      some
        (Lynx.Term.FunEntry.effectful fun lynxDispatch => fun captures args =>
          match (captures).toList, (args).toList with
          | [], [varg1] => Erlang.functions.«remember/1» lynxDispatch varg1
          | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 4) fun_table.sorted rfl

@[simp]
theorem «functions:remember/1».call (depth : Nat) {external : Bool} (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function external "functions" "remember" 1 #[]) #[varg1] =
      Erlang.functions.«remember/1» (Lynx.Dispatcher.ofTable fun_table depth) varg1 :=
  Lynx.Dispatcher.call_effectful (table := fun_table) (external := external) (depth := depth)
    (module := "functions") (name := "remember") (arity := 1) (captures := #[]) (arguments :=
    #[varg1]) «functions:remember/1».entry (by rfl)

end

end Erlang.program
