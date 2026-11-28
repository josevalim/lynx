module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.named_locals

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  [Lynx.Term.FunDef.mk "named_locals" "-self_reference/0-fun-0-" 0
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [] => Erlang.named_locals.«-self_reference/0-fun-0-/0»
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "named_locals" "-named/2-fun-0-" 1
      (Lynx.Term.FunEntry.apply fun lynxDispatch => fun captures args =>
        match (captures).toList, (args).toList with
        | [vcap1], [varg1] => Erlang.named_locals.«-named/2-fun-0-/2» lynxDispatch vcap1 varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

private theorem fun_table.sorted : Lynx.Dispatcher.sorted fun_table = true := by decide +kernel

private theorem «named_locals:-self_reference/0-fun-0-/0».entry :
    Lynx.Dispatcher.find fun_table "named_locals" "-self_reference/0-fun-0-" 0 =
      some
        (Lynx.Term.FunEntry.pure fun captures args =>
          match (captures).toList, (args).toList with
          | [], [] => Erlang.named_locals.«-self_reference/0-fun-0-/0»
          | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 0) fun_table.sorted rfl

@[simp]
theorem «named_locals:-self_reference/0-fun-0-/0».pure (depth : Nat) {external : Bool} :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "named_locals" "-self_reference/0-fun-0-" 0 #[]) #[] =
      Erlang.named_locals.«-self_reference/0-fun-0-/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "named_locals") (name := "-self_reference/0-fun-0-") (arity := 0) (captures := #[])
    (arguments := #[]) «named_locals:-self_reference/0-fun-0-/0».entry (by rfl)

@[simp]
theorem «named_locals:-self_reference/0-fun-0-/0».call (depth : Nat) {external : Bool} :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function external "named_locals" "-self_reference/0-fun-0-" 0 #[]) #[] =
      Lynx.Result.ofExcept Erlang.named_locals.«-self_reference/0-fun-0-/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (external := external) (depth := depth) (module :=
    "named_locals") (name := "-self_reference/0-fun-0-") (arity := 0) (captures := #[])
    (arguments := #[]) «named_locals:-self_reference/0-fun-0-/0».entry (by rfl)

private theorem «named_locals:-named/2-fun-0-/1».entry :
    Lynx.Dispatcher.find fun_table "named_locals" "-named/2-fun-0-" 1 =
      some
        (Lynx.Term.FunEntry.apply fun lynxDispatch => fun captures args =>
          match (captures).toList, (args).toList with
          | [vcap1], [varg1] => Erlang.named_locals.«-named/2-fun-0-/2» lynxDispatch vcap1 varg1
          | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))) :=
  Lynx.Dispatcher.find_of_sorted (index := 1) fun_table.sorted rfl

@[simp]
theorem «named_locals:-named/2-fun-0-/1».pure (depth : Nat) {external : Bool} (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function external "named_locals" "-named/2-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.named_locals.«-named/2-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
        varg1 :=
  Lynx.Dispatcher.pure_apply (table := fun_table) (external := external) (depth := depth) (module :=
    "named_locals") (name := "-named/2-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments :=
    #[varg1]) «named_locals:-named/2-fun-0-/1».entry (by rfl)

@[simp]
theorem «named_locals:-named/2-fun-0-/1».call (depth : Nat) {external : Bool} (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function external "named_locals" "-named/2-fun-0-" 1 #[vcap1]) #[varg1] =
      Lynx.Result.ofExcept
        (Erlang.named_locals.«-named/2-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
          varg1) :=
  Lynx.Dispatcher.call_apply (table := fun_table) (external := external) (depth := depth) (module :=
    "named_locals") (name := "-named/2-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments :=
    #[varg1]) «named_locals:-named/2-fun-0-/1».entry (by rfl)

end

end Erlang.program
