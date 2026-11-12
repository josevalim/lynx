module

public import Lynx
import Lynx.Runner.Elab
public import Erlang.protocols
meta import Erlang.protocols

@[expose] public section

namespace Erlang.protocols.laws

theorem «size_list/1» (list : Lynx.Term)
    (requires : «size_list_requires/1» list = Except.ok Lynx.Term.true) :
    «size_list_ensures/1» list = Except.ok Lynx.Term.true := by
  cases h : Erlang.erlang.«length/1» list with
  | error => simp [«size_list_requires/1», h] at requires
  | ok length =>
    cases list
    case nil | cons =>
      simp [«size_list_ensures/1», «size/1», Elixir.Lynx.Support.Size.«size/1»,
        Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
        Elixir.Lynx.Support.Size.List.«size/1», Erlang.erlang.«=:=/2», h]
    all_goals simp [Erlang.erlang.«length/1»] at h

theorem «size_struct/0» : «size_struct_ensures/0» = Except.ok Lynx.Term.true := by
  simp [«size_struct_ensures/0», «size/1», Elixir.Lynx.Support.Size.«size/1»,
    Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
    Elixir.Lynx.Support.Size.Lynx.Support.Point.«size/1», Erlang.erlang.«=:=/2»,
    Lynx.Term.getMapKeys]

theorem «size_undefined/1» (value : Lynx.Term)
    (requires : «size_undefined_requires/1» value = Except.ok Lynx.Term.true) :
    «size_undefined_ensures/1» value = Except.ok Lynx.Term.true := by
  cases value <;> simp [«size_undefined_requires/1», Erlang.erlang.«is_float/1»] at requires
  simp [«size_undefined_ensures/1», «size/1», Elixir.Lynx.Support.Size.«size/1»,
    Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
    Lynx.Exception.classTerm, Lynx.Exception.reason, Lynx.Term.getMapKeys,
    Lynx.Term.exactCompare_atoms, Erlang.erlang.«=:=/2»]

theorem «describe_fallback/1» (value : Lynx.Term)
    (requires : «describe_fallback_requires/1» value = Except.ok Lynx.Term.true) :
    «describe_fallback_ensures/1» value = Except.ok Lynx.Term.true := by
  cases value <;> simp [«describe_fallback_requires/1», Erlang.erlang.«is_integer/1»] at requires
  simp [«describe_fallback_ensures/1», «describe/2», Elixir.Lynx.Support.Describe.«describe/2»,
    Elixir.Lynx.Support.Describe.«impl_for!/1», Elixir.Lynx.Support.Describe.«impl_for/1»,
    Elixir.Lynx.Support.Describe.Any.«describe/2», Erlang.erlang.«=:=/2»]

end Erlang.protocols.laws
