module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.higher_order

@[expose] public section

namespace Erlang.program

section

set_option «match».ignoreUnusedAlts true

def fun_table : Lynx.Term.FunTable :=
  [Lynx.Term.FunDef.mk "higher_order" "-map_returns_list_requires/2-fun-0-" 1
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [varg1] => Erlang.higher_order.«-map_returns_list_requires/2-fun-0-/1» varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))),
    Lynx.Term.FunDef.mk "higher_order" "-map_returns_list_requires/2-fun-1-" 1
      (Lynx.Term.FunEntry.pure fun captures args =>
        match (captures).toList, (args).toList with
        | [], [varg1] => Erlang.higher_order.«-map_returns_list_requires/2-fun-1-/1» varg1
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))]

@[simp]
theorem «higher_order:-map_returns_list_requires/2-fun-0-/1».pure (depth : Nat)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "higher_order" "-map_returns_list_requires/2-fun-0-" 1 #[]) #[varg1] =
      Erlang.higher_order.«-map_returns_list_requires/2-fun-0-/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "higher_order")
    (name := "-map_returns_list_requires/2-fun-0-") (arity := 1) (captures := #[]) (arguments :=
    #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «higher_order:-map_returns_list_requires/2-fun-0-/1».call (depth : Nat)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "higher_order" "-map_returns_list_requires/2-fun-0-" 1 #[]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.higher_order.«-map_returns_list_requires/2-fun-0-/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "higher_order")
    (name := "-map_returns_list_requires/2-fun-0-") (arity := 1) (captures := #[]) (arguments :=
    #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «higher_order:-map_returns_list_requires/2-fun-1-/1».pure (depth : Nat)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.pure (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "higher_order" "-map_returns_list_requires/2-fun-1-" 1 #[]) #[varg1] =
      Erlang.higher_order.«-map_returns_list_requires/2-fun-1-/1» varg1 :=
  Lynx.Dispatcher.pure_pure (table := fun_table) (depth := depth) (module := "higher_order")
    (name := "-map_returns_list_requires/2-fun-1-") (arity := 1) (captures := #[]) (arguments :=
    #[varg1]) (by rfl) (by rfl)

@[simp]
theorem «higher_order:-map_returns_list_requires/2-fun-1-/1».call (depth : Nat)
    (varg1 : Lynx.Term) :
    Lynx.Dispatcher.call (Lynx.Dispatcher.ofTable fun_table depth)
        (Lynx.Term.function "higher_order" "-map_returns_list_requires/2-fun-1-" 1 #[]) #[varg1] =
      Lynx.Result.ofExcept (Erlang.higher_order.«-map_returns_list_requires/2-fun-1-/1» varg1) :=
  Lynx.Dispatcher.call_pure (table := fun_table) (depth := depth) (module := "higher_order")
    (name := "-map_returns_list_requires/2-fun-1-") (arity := 1) (captures := #[]) (arguments :=
    #[varg1]) (by rfl) (by rfl)

end

end Erlang.program
