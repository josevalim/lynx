-module(binary_construction).
-export([empty/0, integer_default/1, integer_big/2, integer_signed_big/2, integer_little/2,
         integer_signed_little/2, integer_unit/2, integer_max_unit/2,
         integer_mixed/1, integer_invalid_size/1,
         float_default/1, float_big/1, float_little/1, float_unit/1,
         float_mixed/1, float16/1, float32/1,
         utf8/1, utf8_little/1, utf16/1, utf16_big/1, utf16_little/1,
         utf32/1, utf32_big/1, utf32_little/1, utf_mixed/1,
         binary_all/1, bitstring_all/1, binary_prefix/2, bitstring_unit/2, binary_mixed/2]).

empty() -> <<>>.
integer_default(X) -> <<X>>.
integer_big(X, Size) -> <<X:Size/unsigned-big>>.
integer_signed_big(X, Size) -> <<X:Size/signed-big>>.
integer_little(X, Size) -> <<X:Size/unsigned-little>>.
integer_signed_little(X, Size) -> <<X:Size/signed-little>>.
integer_unit(X, Size) -> <<X:Size/unit:3>>.
integer_max_unit(X, Size) -> <<X:Size/unit:256>>.
integer_mixed(X) -> <<1:3, X:12/little, -1:5/signed>>.
integer_invalid_size(X) -> <<X:(-1)>>.

float_default(X) -> <<X/float>>.
float_big(X) -> <<X:64/float-big>>.
float_little(X) -> <<X:64/float-little>>.
float_unit(X) -> <<X:8/float-unit:8>>.
float_mixed(X) -> <<1:3, X:64/float-little, -1:5/signed>>.
float16(X) -> <<X:16/float>>.
float32(X) -> <<X:32/float>>.

binary_all(X) -> <<X/binary>>.
bitstring_all(X) -> <<X/bitstring>>.
binary_prefix(X, Size) -> <<X:Size/binary>>.
bitstring_unit(X, Size) -> <<X:Size/binary-unit:3>>.
binary_mixed(X, Y) -> <<1:3, X/bitstring, Y/binary, 0:1>>.

utf8(X) -> <<X/utf8>>.
utf8_little(X) -> <<X/utf8-little>>.
utf16(X) -> <<X/utf16>>.
utf16_big(X) -> <<X/utf16-big>>.
utf16_little(X) -> <<X/utf16-little>>.
utf32(X) -> <<X/utf32>>.
utf32_big(X) -> <<X/utf32-big>>.
utf32_little(X) -> <<X/utf32-little>>.
utf_mixed(X) -> <<1:3, X/utf8, X/utf16-little, X/utf32-big, 0:1>>.
