module

public import Lynx

@[expose] public section

namespace Erlang.binary_construction

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  def «empty/0» : Lynx.Result :=
    pure (Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide))

#lynx_pure
  def «integer_default/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer 8) 1 Bool.false

#lynx_pure
  def «integer_big/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.false

#lynx_pure
  def «integer_signed_big/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.false

#lynx_pure
  def «integer_little/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.true

#lynx_pure
  def «integer_signed_little/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.true

#lynx_pure
  def «integer_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 3 Bool.false

#lynx_pure
  def «integer_mixed/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.bind
      (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
      (fun lynxBinarySegment✝ =>
        Lynx.Result.bind
          (Lynx.Result.bind
            (Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer 12) 1 Bool.true)
            (fun lynxBinarySegment✝ =>
              Lynx.Result.bind
                (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer (-1)) (Lynx.Term.integer 5) 1
                  Bool.false)
                (fun lynxBinaryTail✝ =>
                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
          (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

#lynx_pure
  def «integer_invalid_size/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer (-1)) 1 Bool.false

end

end Erlang.binary_construction
