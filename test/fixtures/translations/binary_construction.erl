-module(binary_construction).
-export([empty/0, integer_default/1, integer_big/2, integer_signed_big/2, integer_little/2,
         integer_signed_little/2, integer_unit/2, integer_mixed/1, integer_invalid_size/1]).

empty() -> <<>>.
integer_default(X) -> <<X>>.
integer_big(X, Size) -> <<X:Size/unsigned-big>>.
integer_signed_big(X, Size) -> <<X:Size/signed-big>>.
integer_little(X, Size) -> <<X:Size/unsigned-little>>.
integer_signed_little(X, Size) -> <<X:Size/signed-little>>.
integer_unit(X, Size) -> <<X:Size/unit:3>>.
integer_mixed(X) -> <<1:3, X:12/little, -1:5/signed>>.
integer_invalid_size(X) -> <<X:(-1)>>.
