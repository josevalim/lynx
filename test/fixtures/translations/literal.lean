module

public import Lynx

namespace Erlang.literal

#lynx_pure
  public def «atoms/0» : Lynx.Result :=
    Lynx.Result.ok
      (Lynx.Term.cons (Lynx.Term.atom "foo")
        (Lynx.Term.cons (Lynx.Term.atom "bar baz") Lynx.Term.nil))

#lynx_pure
  public def «empty_list/0» : Lynx.Result :=
    Lynx.Result.ok Lynx.Term.nil

#lynx_pure
  public def «integers/0» : Lynx.Result :=
    Lynx.Result.ok
      (Lynx.Term.cons (Lynx.Term.integer (-1))
        (Lynx.Term.cons (Lynx.Term.integer 0)
          (Lynx.Term.cons (Lynx.Term.integer 1)
            (Lynx.Term.cons (Lynx.Term.integer 9223372036854775808) Lynx.Term.nil))))

end Erlang.literal
