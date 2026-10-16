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
  def «integer_max_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.integerSegment _0 _1 256 Bool.false

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

#lynx_pure
  def «float_default/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

#lynx_pure
  def «float_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

#lynx_pure
  def «float_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 64 Bool.true

#lynx_pure
  def «float_unit/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

#lynx_pure
  def «float_mixed/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.bind
      (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
      (fun lynxBinarySegment✝ =>
        Lynx.Result.bind
          (Lynx.Result.bind (Lynx.Term.Bitstring.floatSegment _0 64 Bool.true)
            (fun lynxBinarySegment✝ =>
              Lynx.Result.bind
                (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer (-1)) (Lynx.Term.integer 5) 1
                  Bool.false)
                (fun lynxBinaryTail✝ =>
                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
          (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

#lynx_pure
  def «float16/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 16 Bool.false

#lynx_pure
  def «float32/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.floatSegment _0 32 Bool.false

#lynx_pure
  def «binary_all/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 8

#lynx_pure
  def «bitstring_all/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 1

#lynx_pure
  def «binary_prefix/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.binarySegment _0 _1 8

#lynx_pure
  def «bitstring_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.binarySegment _0 _1 3

#lynx_pure
  def «binary_mixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.bind
      (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
      (fun lynxBinarySegment✝ =>
        Lynx.Result.bind
          (Lynx.Result.bind (Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 1)
            (fun lynxBinarySegment✝ =>
              Lynx.Result.bind
                (Lynx.Result.bind (Lynx.Term.Bitstring.binarySegment _1 (Lynx.Term.atom "all") 8)
                  (fun lynxBinarySegment✝ =>
                    Lynx.Result.bind
                      (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 0)
                        (Lynx.Term.integer 1) 1 Bool.false)
                      (fun lynxBinaryTail✝ =>
                        Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
                (fun lynxBinaryTail✝ =>
                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
          (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

#lynx_pure
  def «utf8/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf8Segment _0

#lynx_pure
  def «utf8_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf8Segment _0

#lynx_pure
  def «utf16/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf16Segment _0 Bool.false

#lynx_pure
  def «utf16_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf16Segment _0 Bool.false

#lynx_pure
  def «utf16_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf16Segment _0 Bool.true

#lynx_pure
  def «utf32/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf32Segment _0 Bool.false

#lynx_pure
  def «utf32_big/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf32Segment _0 Bool.false

#lynx_pure
  def «utf32_little/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Term.Bitstring.utf32Segment _0 Bool.true

#lynx_pure
  def «utf_mixed/1» (_0 : Lynx.Term) : Lynx.Result :=
    Lynx.Result.bind
      (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
      (fun lynxBinarySegment✝ =>
        Lynx.Result.bind
          (Lynx.Result.bind (Lynx.Term.Bitstring.utf8Segment _0)
            (fun lynxBinarySegment✝ =>
              Lynx.Result.bind
                (Lynx.Result.bind (Lynx.Term.Bitstring.utf16Segment _0 Bool.true)
                  (fun lynxBinarySegment✝ =>
                    Lynx.Result.bind
                      (Lynx.Result.bind (Lynx.Term.Bitstring.utf32Segment _0 Bool.false)
                        (fun lynxBinarySegment✝ =>
                          Lynx.Result.bind
                            (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 0)
                              (Lynx.Term.integer 1) 1 Bool.false)
                            (fun lynxBinaryTail✝ =>
                              Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
                      (fun lynxBinaryTail✝ =>
                        Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
                (fun lynxBinaryTail✝ =>
                  Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
          (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

end

end Erlang.binary_construction
