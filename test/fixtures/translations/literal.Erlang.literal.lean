module

public import Lynx
public import Lynx.Modules.Erlang.erlang

@[expose] public section

namespace Erlang.literal

section

set_option «match».ignoreUnusedAlts true

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

#lynx_pure
  def «bitstrings/0» : Lynx.Result :=
    pure
      (Lynx.Term.cons (Lynx.Term.bitstring ⟨#[0, 255]⟩ 0 (by decide))
        (Lynx.Term.cons (Lynx.Term.bitstring ⟨#[160]⟩ 3 (by decide))
          (Lynx.Term.cons (Lynx.Term.bitstring ⟨#[128, 255, 128]⟩ 1 (by decide)) Lynx.Term.nil)))

def lynx_literal_xcr6qjiw : Lynx.Term :=
  Lynx.Term.tuple
    #[Lynx.Term.integer 0, Lynx.Term.integer 1, Lynx.Term.integer 2, Lynx.Term.integer 3,
      Lynx.Term.integer 4, Lynx.Term.integer 5, Lynx.Term.integer 6, Lynx.Term.integer 7,
      Lynx.Term.integer 8, Lynx.Term.integer 9, Lynx.Term.integer 10, Lynx.Term.integer 11,
      Lynx.Term.integer 12, Lynx.Term.integer 13, Lynx.Term.integer 14, Lynx.Term.integer 15,
      Lynx.Term.integer 16, Lynx.Term.integer 17, Lynx.Term.integer 18, Lynx.Term.integer 19,
      Lynx.Term.integer 20, Lynx.Term.integer 21, Lynx.Term.integer 22, Lynx.Term.integer 23,
      Lynx.Term.integer 24, Lynx.Term.integer 25, Lynx.Term.integer 26, Lynx.Term.integer 27,
      Lynx.Term.integer 28, Lynx.Term.integer 29, Lynx.Term.integer 30, Lynx.Term.integer 31]

#lynx_pure
  def «table/0» : Lynx.Result :=
    pure lynx_literal_xcr6qjiw

#lynx_pure
  def «table_lookup/1» (_0 : Lynx.Term) : Lynx.Result := do
    let _3 ← Erlang.erlang.«element/2» _0 lynx_literal_xcr6qjiw
    let _1 ← Erlang.erlang.«+/2» _0 (Lynx.Term.integer 1)
    let _2 ← Erlang.erlang.«element/2» _1 lynx_literal_xcr6qjiw
    pure (Lynx.Term.tuple #[_3, _2])

def lynx_literal_bbjy4hhz : Lynx.Term :=
  Lynx.Term.cons (Lynx.Term.integer 1)
    (Lynx.Term.cons (Lynx.Term.integer 2)
      (Lynx.Term.cons (Lynx.Term.integer 3)
        (Lynx.Term.cons (Lynx.Term.integer 4)
          (Lynx.Term.cons (Lynx.Term.integer 5)
            (Lynx.Term.cons (Lynx.Term.integer 6)
              (Lynx.Term.cons (Lynx.Term.integer 7)
                (Lynx.Term.cons (Lynx.Term.integer 8)
                  (Lynx.Term.cons
                    (Lynx.Term.cons (Lynx.Term.integer 9)
                      (Lynx.Term.cons (Lynx.Term.integer 10)
                        (Lynx.Term.cons (Lynx.Term.integer 11)
                          (Lynx.Term.cons (Lynx.Term.integer 12)
                            (Lynx.Term.cons (Lynx.Term.integer 13)
                              (Lynx.Term.cons (Lynx.Term.integer 14)
                                (Lynx.Term.cons (Lynx.Term.integer 15)
                                  (Lynx.Term.cons (Lynx.Term.integer 16) Lynx.Term.nil))))))))
                    Lynx.Term.nil))))))))

#lynx_pure
  def «pooled_list/0» : Lynx.Result :=
    pure lynx_literal_bbjy4hhz

def lynx_literal_pzlvkmdt : Lynx.Term :=
  Lynx.Term.map
    [(Lynx.Term.atom "nested",
        Lynx.Term.map
          [(Lynx.Term.integer 15, Lynx.Term.integer 15),
            (Lynx.Term.integer 14, Lynx.Term.integer 14),
            (Lynx.Term.integer 13, Lynx.Term.integer 13),
            (Lynx.Term.integer 12, Lynx.Term.integer 12),
            (Lynx.Term.integer 11, Lynx.Term.integer 11),
            (Lynx.Term.integer 10, Lynx.Term.integer 10),
            (Lynx.Term.integer 9, Lynx.Term.integer 9)]),
      (Lynx.Term.integer 8, Lynx.Term.integer 8), (Lynx.Term.integer 7, Lynx.Term.integer 7),
      (Lynx.Term.integer 6, Lynx.Term.integer 6), (Lynx.Term.integer 5, Lynx.Term.integer 5),
      (Lynx.Term.integer 4, Lynx.Term.integer 4), (Lynx.Term.integer 3, Lynx.Term.integer 3),
      (Lynx.Term.integer 2, Lynx.Term.integer 2), (Lynx.Term.integer 1, Lynx.Term.integer 1)]

#lynx_pure
  def «pooled_map/0» : Lynx.Result :=
    pure lynx_literal_pzlvkmdt

def lynx_literal_sxllxy4x : Lynx.Term :=
  Lynx.Term.bitstring
    ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32]⟩
    0 (by decide)

#lynx_pure
  def «pooled_binary/0» : Lynx.Result :=
    pure lynx_literal_sxllxy4x

def lynx_literal_25irwduj : Lynx.Term :=
  Lynx.Term.tuple
    #[Lynx.Term.atom "nested",
      Lynx.Term.tuple
        #[Lynx.Term.integer 0, Lynx.Term.integer 1, Lynx.Term.integer 2, Lynx.Term.integer 3,
          Lynx.Term.integer 4, Lynx.Term.integer 5, Lynx.Term.integer 6, Lynx.Term.integer 7,
          Lynx.Term.integer 8, Lynx.Term.integer 9, Lynx.Term.integer 10, Lynx.Term.integer 11,
          Lynx.Term.integer 12, Lynx.Term.integer 13, Lynx.Term.integer 14, Lynx.Term.integer 15,
          Lynx.Term.integer 16, Lynx.Term.integer 17, Lynx.Term.integer 18, Lynx.Term.integer 19,
          Lynx.Term.integer 20, Lynx.Term.integer 21, Lynx.Term.integer 22, Lynx.Term.integer 23,
          Lynx.Term.integer 24, Lynx.Term.integer 25, Lynx.Term.integer 26, Lynx.Term.integer 27,
          Lynx.Term.integer 28, Lynx.Term.integer 29, Lynx.Term.integer 30, Lynx.Term.integer 31]]

#lynx_pure
  def «pooled_nested/0» : Lynx.Result :=
    pure lynx_literal_25irwduj

end

end Erlang.literal
