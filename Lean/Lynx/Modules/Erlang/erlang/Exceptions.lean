module

public import Lynx.Pure

public section

namespace Erlang.erlang
open Lynx

/-- The argument list only supplies stack trace metadata, which Result does not model. -/
#lynx_pure @[expose] def «error/2» (reason _arguments : Term) : Result := .error (.error reason)

#lynx_pure @[expose] def «throw/1» (reason : Term) : Result := .error (.throw reason)

#lynx_pure @[expose] def «exit/1» (reason : Term) : Result := .error (.exit reason)

end Erlang.erlang
