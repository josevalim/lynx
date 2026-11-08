module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.named_locals

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  [Lynx.Term.FunDef.mk "named_locals" "-named/2-fun-0-" 1
      (Lynx.Term.FunEntry.apply fun lynxDispatch => fun captures args =>
        match (captures).toList, (args).toList with
        | [vcap1], [varg1] => Erlang.named_locals.«-named/2-fun-0-/2» lynxDispatch vcap1 varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "named_locals" "-self_reference/0-fun-0-" 0
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [] => Erlang.named_locals.«-self_reference/0-fun-0-/0»
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

@[simp]
theorem «named_locals:-named/2-fun-0-/1».pure (depth : Nat) (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function "named_locals" "-named/2-fun-0-" 1 #[vcap1]) #[varg1] =
      Erlang.named_locals.«-named/2-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
        varg1 :=
  Lynx.Dispatcher.pure_apply (table := fun_table) (depth := depth) (module := "named_locals")
    (name := "-named/2-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments := #[varg1]) (by rfl)
    (by rfl)

@[simp]
theorem «named_locals:-named/2-fun-0-/1».call (depth : Nat) (vcap1 : Lynx.Term)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table (depth + 1))
        (Lynx.Term.function "named_locals" "-named/2-fun-0-" 1 #[vcap1]) #[varg1] =
      Lynx.Result.ofExcept
        (Erlang.named_locals.«-named/2-fun-0-/2» (Lynx.Dispatcher.ofTable fun_table depth) vcap1
          varg1) :=
  Lynx.Dispatcher.call_apply (table := fun_table) (depth := depth) (module := "named_locals")
    (name := "-named/2-fun-0-") (arity := 1) (captures := #[vcap1]) (arguments := #[varg1]) (by rfl)
    (by rfl)

@[simp]
theorem «named_locals:-self_reference/0-fun-0-/0».pure (depth : Nat) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "named_locals" "-self_reference/0-fun-0-" 0 #[]) #[] =
      Erlang.named_locals.«-self_reference/0-fun-0-/0» :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "named_locals")
    (name := "-self_reference/0-fun-0-") (arity := 0) (captures := #[]) (arguments := #[]) (by rfl)
    (by rfl)

@[simp]
theorem «named_locals:-self_reference/0-fun-0-/0».call (depth : Nat) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "named_locals" "-self_reference/0-fun-0-" 0 #[]) #[] =
      Lynx.Result.ofExcept Erlang.named_locals.«-self_reference/0-fun-0-/0» :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "named_locals")
    (name := "-self_reference/0-fun-0-") (arity := 0) (captures := #[]) (arguments := #[]) (by rfl)
    (by rfl)

end

end Erlang.program
