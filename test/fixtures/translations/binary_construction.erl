-module(binary_construction).
-export([empty/0, integer_default/1, integer_big/2, integer_signed_big/2, integer_little/2,
         integer_signed_little/2, integer_unit/2, integer_mixed/1, integer_invalid_size/1,
         float_default/1, float_big/1, float_little/1, float_unit/1,
         float_mixed/1, float16/1, float32/1]).

empty() -> <<>>.
integer_default(X) -> <<X>>.
integer_big(X, Size) -> <<X:Size/unsigned-big>>.
integer_signed_big(X, Size) -> <<X:Size/signed-big>>.
integer_little(X, Size) -> <<X:Size/unsigned-little>>.
integer_signed_little(X, Size) -> <<X:Size/signed-little>>.
integer_unit(X, Size) -> <<X:Size/unit:3>>.
integer_mixed(X) -> <<1:3, X:12/little, -1:5/signed>>.
integer_invalid_size(X) -> <<X:(-1)>>.

float_default(X) -> <<X/float>>.
float_big(X) -> <<X:64/float-big>>.
float_little(X) -> <<X:64/float-little>>.
float_unit(X) -> <<X:8/float-unit:8>>.
float_mixed(X) -> <<1:3, X:64/float-little, -1:5/signed>>.
float16(X) -> <<X:16/float>>.
float32(X) -> <<X:32/float>>.
