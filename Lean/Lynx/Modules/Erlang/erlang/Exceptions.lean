module

public import Lynx.Term

public section

namespace Erlang.erlang
open Lynx

/-- The argument list only supplies stack trace metadata, which Result does not model. -/
@[expose] def «error/2» (reason _arguments : Term) : Except Exception Term := .error (.error reason)

/-- Error options describe stack trace formatting, which Result does not model. -/
@[expose] def «error/3» (reason _arguments _options : Term) : Except Exception Term := .error (.error reason)

@[expose] def «throw/1» (reason : Term) : Except Exception Term := .error (.throw reason)

@[expose] def «exit/1» (reason : Term) : Except Exception Term := .error (.exit reason)

end Erlang.erlang
