import Lynx.Modules.Erlang.Definitions

namespace Lynx.Modules.Erlang

@[simp] theorem append_nil_left (right : Term) :
    append_2 .nil right = .ok right := rfl

@[simp] theorem append_cons (head tail right : Term) :
    append_2 (.cons head tail) right =
      (append_2 tail right >>= fun rest => .ok (.cons head rest)) := rfl

end Lynx.Modules.Erlang
