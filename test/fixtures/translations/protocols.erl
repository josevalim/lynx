-module(protocols).
-export([size/1, describe/2,
         size_list_requires/1, size_list_ensures/1,
         size_struct_ensures/0,
         size_undefined_requires/1, size_undefined_ensures/1,
         describe_fallback_requires/1, describe_fallback_ensures/1]).

%% Protocols in test/support are consolidated with the project. Each protocol
%% function selects the implementation module with impl_for!/1 and calls it
%% directly, so dispatch reduces like any other match. Improper lists are
%% lists too, but both sides raise for them.
-law #{name => {size_list, [list]}, requires => size_list_requires, ensures => size_list_ensures}.
-proof ~"""
cases h : Erlang.erlang.«length/1» list with
| error => simp [«size_list_requires/1», h] at requires
| ok length =>
  cases list
  case nil | cons =>
    simp [«size_list_ensures/1», «size/1», Elixir.Lynx.Support.Size.«size/1»,
      Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
      Elixir.Lynx.Support.Size.List.«size/1», Erlang.erlang.«=:=/2», h]
  all_goals simp [Erlang.erlang.«length/1»] at h
""".

%% Structs dispatch to their own implementation, not the one for maps.
-law #{name => {size_struct, []}, ensures => size_struct_ensures}.
-proof ~"""
simp [«size_struct_ensures/0», «size/1», Elixir.Lynx.Support.Size.«size/1»,
  Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
  Elixir.Lynx.Support.Size.Lynx.Support.Point.«size/1», Erlang.erlang.«=:=/2»,
  Lynx.Term.getMapKeys]
""".

%% Values without an implementation raise Protocol.UndefinedError.
-law #{name => {size_undefined, [value]}, requires => size_undefined_requires, ensures => size_undefined_ensures}.
-proof ~"""
cases value <;> simp [«size_undefined_requires/1», Erlang.erlang.«is_float/1»] at requires
simp [«size_undefined_ensures/1», «size/1», Elixir.Lynx.Support.Size.«size/1»,
  Elixir.Lynx.Support.Size.«impl_for!/1», Elixir.Lynx.Support.Size.«impl_for/1»,
  Lynx.Exception.classTerm, Lynx.Exception.reason, Lynx.Term.getMapKeys,
  Lynx.Term.exactCompare_atoms, Erlang.erlang.«=:=/2»]
""".

%% Protocols falling back to Any dispatch values without an implementation there.
-law #{name => {describe_fallback, [value]}, requires => describe_fallback_requires, ensures => describe_fallback_ensures}.
-proof ~"""
cases value <;> simp [«describe_fallback_requires/1», Erlang.erlang.«is_integer/1»] at requires
simp [«describe_fallback_ensures/1», «describe/2», Elixir.Lynx.Support.Describe.«describe/2»,
  Elixir.Lynx.Support.Describe.«impl_for!/1», Elixir.Lynx.Support.Describe.«impl_for/1»,
  Elixir.Lynx.Support.Describe.Any.«describe/2», Erlang.erlang.«=:=/2»]
""".

size(Data) -> 'Elixir.Lynx.Support.Size':size(Data).
describe(Data, Prefix) -> 'Elixir.Lynx.Support.Describe':describe(Data, Prefix).

size_list_requires(List) -> length(List) >= 0.
size_list_ensures(List) -> size(List) =:= length(List).

size_struct_ensures() -> size(#{'__struct__' => 'Elixir.Lynx.Support.Point', x => 1, y => 2}) =:= 2.

size_undefined_requires(Value) -> is_float(Value).
size_undefined_ensures(Value) ->
    try size(Value) of
        _ -> false
    catch
        error:#{'__struct__' := 'Elixir.Protocol.UndefinedError', value := Value} -> true
    end.

describe_fallback_requires(Value) -> is_integer(Value).
describe_fallback_ensures(Value) -> describe(Value, prefix) =:= {prefix, any}.
