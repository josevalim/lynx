-module(bitstring_matching).
-export([empty/1, empty_or_byte/1, literal/1, partial_literal/1, binary_literal/1, string_literal/1, signed_literal/1, integers/1, integer_sized/1, integer_external_size/2,
         utf8/1, utf8_little/1, utf16/1, utf16_big/1, utf16_little/1,
         utf32/1, utf32_big/1, utf32_little/1, utf_mixed/1, utf_literal/1, utf_pinned/2,
         float64/1, binary_tail/1, bitstring_tail/1, binary_literal_tail/1,
         bitstring_literal_tail/1, binary_fixed/2,
         bitstring_fixed/2, binary_prefix/2, nested/1, guarded/1, alias/1, pinned/2]).

%% A literal binary beside segment clauses is matched as segments too.
empty_or_byte(<<X, Rest/binary>>) -> {X, Rest};
empty_or_byte(<<>>) -> empty;
empty_or_byte(_) -> other.

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

binary_prefix(Size, Bits) ->
    case Bits of <<Prefix:Size/binary, Tag:3, Tail/bitstring>> -> {Prefix, Tag, Tail}; _ -> other end.

nested({tag, [#{bits := <<X:8, Rest/bitstring>>}]}) -> {X, Rest};
nested(_) -> other.

guarded(<<X:8, Rest/binary>>) when X > 10 -> {large, X, Rest};
guarded(<<X:8, Rest/bitstring>>) -> {small, X, Rest};
guarded(_) -> other.

alias(<<X:8, Rest/bitstring>> = Whole) -> {X, Rest, Whole};
alias(_) -> other.

pinned(X, Bits) ->
    case Bits of <<X:8, Rest/bitstring>> -> {X, Rest}; _ -> other end.

utf8(<<X/utf8, Rest/bitstring>>) -> {X, Rest};
utf8(_) -> other.

utf8_little(<<X/utf8-little, Rest/bitstring>>) -> {X, Rest};
utf8_little(_) -> other.

utf16(<<X/utf16, Rest/bitstring>>) -> {X, Rest};
utf16(_) -> other.

utf16_big(<<X/utf16-big, Rest/bitstring>>) -> {X, Rest};
utf16_big(_) -> other.

utf16_little(<<X/utf16-little, Rest/bitstring>>) -> {X, Rest};
utf16_little(_) -> other.

utf32(<<X/utf32, Rest/bitstring>>) -> {X, Rest};
utf32(_) -> other.

utf32_big(<<X/utf32-big, Rest/bitstring>>) -> {X, Rest};
utf32_big(_) -> other.

utf32_little(<<X/utf32-little, Rest/bitstring>>) -> {X, Rest};
utf32_little(_) -> other.

utf_mixed(<<Tag:3, X/utf8, Y/utf16-little, Z/utf32-big, Rest/bitstring>>) ->
    {Tag, X, Y, Z, Rest};
utf_mixed(_) -> other.

utf_literal(<<16#20ac/utf8, 16#1f600/utf16-little, 16#10ffff/utf32-big>>) -> matched;
utf_literal(_) -> other.

utf_pinned(X, Bits) ->
    case Bits of <<X/utf8, X/utf16-big, X/utf32-little>> -> matched; _ -> other end.
