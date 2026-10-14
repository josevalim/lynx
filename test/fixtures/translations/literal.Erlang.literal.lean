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

#lynx_pure
  def «tuples/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.tuple #[])
        (Lynx.Term.cons (Lynx.Term.tuple #[Lynx.Term.atom "ok"])
          (Lynx.Term.cons (Lynx.Term.tuple #[Lynx.Term.atom "ok", Lynx.Term.integer 1])
            (Lynx.Term.cons
              (Lynx.Term.tuple
                #[Lynx.Term.atom "nested",
                  Lynx.Term.tuple
                    #[Lynx.Term.integer 1, Lynx.Term.cons (Lynx.Term.atom "foo") Lynx.Term.nil]])
              Lynx.Term.nil))))

#lynx_pure
  def «computed_tuples/1» (_0 : Lynx.Term) : Lynx.Result :=
    pure
      (Lynx.Term.tuple
        #[Lynx.Term.atom "ok", _0, Lynx.Term.tuple #[_0, Lynx.Term.cons _0 Lynx.Term.nil]])

#lynx_pure
  def «maps/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.map [])
        (Lynx.Term.cons
          (Lynx.Term.map
            [(Lynx.Term.atom "a", Lynx.Term.integer 1),
              (Lynx.Term.integer 1, Lynx.Term.map [(Lynx.Term.atom "b", Lynx.Term.integer 2)])])
          Lynx.Term.nil))

#lynx_pure
  def «computed_maps/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result := do
    let _2 ← pure (Lynx.Term.map [(_0, _1), (_0, Lynx.Term.integer 1)])
    pure (Lynx.Term.map [(_0, _2), (Lynx.Term.atom "a", Lynx.Term.integer 1)])

#lynx_pure
  def «floats/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.float ⟨Bool.true, 1023, 2251799813685248⟩)
        (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 0, 0⟩)
          (Lynx.Term.cons (Lynx.Term.float ⟨Bool.true, 0, 0⟩)
            (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 1023, 0⟩)
              (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 1019, 2702159776422298⟩)
                (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 26, 1528457577689945⟩)
                  (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 0, 1⟩)
                    (Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 2046, 4503599627370495⟩)
                      (Lynx.Term.cons
                        (Lynx.Term.tuple
                          #[Lynx.Term.atom "nested",
                            Lynx.Term.cons (Lynx.Term.float ⟨Bool.false, 1023, 2251799813685248⟩)
                              Lynx.Term.nil])
                        (Lynx.Term.cons
                          (Lynx.Term.map
                            [(Lynx.Term.float ⟨Bool.false, 1023, 0⟩,
                                Lynx.Term.float ⟨Bool.false, 1019, 2702159776422298⟩),
                              (Lynx.Term.integer 1, Lynx.Term.atom "integer")])
                          Lynx.Term.nil))))))))))

end Erlang.literal
