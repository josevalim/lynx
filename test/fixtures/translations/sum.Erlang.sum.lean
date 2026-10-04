module

public import Lynx
public import Lynx.Modules.Erlang.erlang
public import Erlang.lists

@[expose] public section

namespace Erlang.sum

#lynx_pure
  def «sum/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.lists.«sum/1» _0

#lynx_pure
  def «sum_singleton_requires/1» (_0 : Lynx.Term) : Lynx.Result :=
    Erlang.erlang.«is_integer/1» _0

#lynx_pure
  def «sum_empty_ensures/0» : Lynx.Result := do
    let _0 ← «sum/1» Lynx.Term.nil
    Erlang.erlang.«==/2» _0 (Lynx.Term.integer 0)

#lynx_pure
  def «sum_singleton_ensures/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _1 ← «sum/1» (Lynx.Term.cons _0 Lynx.Term.nil)
    Erlang.erlang.«==/2» _1 _0

theorem «sum_empty/0» : «sum_empty_ensures/0» = Lynx.Result.ok Lynx.Term.true := by
  simp [«sum_empty_ensures/0», «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2»,
    Erlang.erlang.«==/2»]

theorem «sum_singleton/1» (x : Lynx.Term)
    (requires : «sum_singleton_requires/1» x = Lynx.Result.ok Lynx.Term.true) :
    «sum_singleton_ensures/1» x = Lynx.Result.ok Lynx.Term.true := by
  cases x <;>
    simp [«sum_singleton_requires/1», «sum_singleton_ensures/1», Erlang.erlang.«is_integer/1»,
      «sum/1», Erlang.lists.«sum/1», Erlang.lists.«sum/2», Erlang.erlang.«==/2»] at requires ⊢

theorem «sum_empty_again/0» : «sum_empty_ensures/0» = Lynx.Result.ok Lynx.Term.true := by
  exact «sum_empty/0»

end Erlang.sum
