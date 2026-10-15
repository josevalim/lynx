-module(bitstring_matching).
-export([empty/1, literal/1, partial_literal/1, binary_literal/1, string_literal/1, signed_literal/1, integers/1, integer_sized/1, integer_external_size/2,
         float64/1, binary_tail/1, bitstring_tail/1, binary_literal_tail/1,
         bitstring_literal_tail/1, binary_fixed/2,
         bitstring_fixed/2, nested/1, guarded/1, alias/1, pinned/2]).

empty(<<>>) -> empty;
empty(_) -> other.

literal(<<1, 2, 5:3>>) -> matched;
literal(_) -> other.

partial_literal(<<5:3>>) -> matched;
partial_literal(_) -> other.

binary_literal(<<97, 98, 99>>) -> matched;
binary_literal(_) -> other.

string_literal(<<"abc">>) -> matched;
string_literal(_) -> other.

signed_literal(<<-1:8/signed, 16#123:24/little>>) -> matched;
signed_literal(_) -> other.

integers(<<A:8/unsigned, B:12/signed-big, C:12/signed-little>>) -> {A, B, C};
integers(_) -> other.

integer_sized(<<Size:8, X:Size/signed-little, Tail/bitstring>>) -> {Size, X, Tail};
integer_sized(_) -> other.

integer_external_size(Size, Bits) ->
    case Bits of <<X:Size/unit:3, Tail/bitstring>> -> {X, Tail}; _ -> other end.

float64(<<X:64/float-big, Y:64/float-little>>) -> {X, Y};
float64(_) -> other.

binary_tail(<<Tag:3, Tail/binary>>) -> {Tag, Tail};
binary_tail(_) -> other.

bitstring_tail(<<Tag:3, Tail/bitstring>>) -> {Tag, Tail};
bitstring_tail(_) -> other.

binary_literal_tail(<<1:3, Tail/binary>>) -> Tail;
binary_literal_tail(_) -> other.

bitstring_literal_tail(<<1:3, Tail/bitstring>>) -> Tail;
bitstring_literal_tail(_) -> other.

binary_fixed(Size, Bits) ->
    case Bits of <<Tag:3, Tail:Size/binary>> -> {Tag, Tail}; _ -> other end.

bitstring_fixed(Size, Bits) ->
    case Bits of <<Tag:3, Tail:Size/bitstring>> -> {Tag, Tail}; _ -> other end.

nested({tag, [#{bits := <<X:8, Rest/bitstring>>}]}) -> {X, Rest};
nested(_) -> other.

guarded(<<X:8, Rest/binary>>) when X > 10 -> {large, X, Rest};
guarded(<<X:8, Rest/bitstring>>) -> {small, X, Rest};
guarded(_) -> other.

alias(<<X:8, Rest/bitstring>> = Whole) -> {X, Rest, Whole};
alias(_) -> other.

pinned(X, Bits) ->
    case Bits of <<X:8, Rest/bitstring>> -> {X, Rest}; _ -> other end.
