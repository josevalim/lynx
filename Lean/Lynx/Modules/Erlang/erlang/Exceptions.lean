module

public import Lynx.Pure

public section

namespace Erlang.erlang
open Lynx

#lynx_pure @[expose] def «throw/1» (reason : Term) : Result := .error (.throw reason)

#lynx_pure @[expose] def «exit/1» (reason : Term) : Result := .error (.exit reason)

end Erlang.erlang
