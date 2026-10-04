module

public import Lynx

@[expose] public section

namespace Erlang.literal

#lynx_pure
  def «integers/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.integer (-1))
        (Lynx.Term.cons (Lynx.Term.integer 0)
          (Lynx.Term.cons (Lynx.Term.integer 1)
            (Lynx.Term.cons (Lynx.Term.integer 9223372036854775808) Lynx.Term.nil))))

#lynx_pure
  def «atoms/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.atom "foo")
        (Lynx.Term.cons (Lynx.Term.atom "bar baz") Lynx.Term.nil))

#lynx_pure
  def «empty_list/0» : Lynx.Result :=
    pure Lynx.Term.nil

end Erlang.literal
