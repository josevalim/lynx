module

public import Lynx

@[expose] public section

namespace Erlang.binary_construction

section

set_option «match».ignoreUnusedAlts true

def «empty/0» : Except Lynx.Exception Lynx.Term :=
  pure (Lynx.Term.bitstring ⟨#[]⟩ 0 (by decide))

def «integer_default/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer 8) 1 Bool.false

def «integer_big/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.false

def «integer_signed_big/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.false

def «integer_little/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.true

def «integer_signed_little/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 1 Bool.true

def «integer_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 3 Bool.false

def «integer_max_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 _1 256 Bool.false

def «integer_mixed/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Except.bind
    (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
    (fun lynxBinarySegment✝ =>
      Except.bind
        (Except.bind (Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer 12) 1 Bool.true)
          (fun lynxBinarySegment✝ =>
            Except.bind
              (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer (-1)) (Lynx.Term.integer 5) 1
                Bool.false)
              (fun lynxBinaryTail✝ =>
                Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
        (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

def «integer_invalid_size/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.integerSegment _0 (Lynx.Term.integer (-1)) 1 Bool.false

def «float_default/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

def «float_big/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

def «float_little/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 64 Bool.true

def «float_unit/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 64 Bool.false

def «float_mixed/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Except.bind
    (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
    (fun lynxBinarySegment✝ =>
      Except.bind
        (Except.bind (Lynx.Term.Bitstring.floatSegment _0 64 Bool.true)
          (fun lynxBinarySegment✝ =>
            Except.bind
              (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer (-1)) (Lynx.Term.integer 5) 1
                Bool.false)
              (fun lynxBinaryTail✝ =>
                Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
        (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

def «float16/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 16 Bool.false

def «float32/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.floatSegment _0 32 Bool.false

def «binary_all/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 8

def «bitstring_all/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 1

def «binary_prefix/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.binarySegment _0 _1 8

def «bitstring_unit/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.binarySegment _0 _1 3

def «binary_mixed/2» (_0 : Lynx.Term) (_1 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Except.bind
    (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
    (fun lynxBinarySegment✝ =>
      Except.bind
        (Except.bind (Lynx.Term.Bitstring.binarySegment _0 (Lynx.Term.atom "all") 1)
          (fun lynxBinarySegment✝ =>
            Except.bind
              (Except.bind (Lynx.Term.Bitstring.binarySegment _1 (Lynx.Term.atom "all") 8)
                (fun lynxBinarySegment✝ =>
                  Except.bind
                    (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 0) (Lynx.Term.integer 1)
                      1 Bool.false)
                    (fun lynxBinaryTail✝ =>
                      Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
              (fun lynxBinaryTail✝ =>
                Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝)))
        (fun lynxBinaryTail✝ => Lynx.Term.Bitstring.append lynxBinarySegment✝ lynxBinaryTail✝))

def «utf8/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf8Segment _0

def «utf8_little/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf8Segment _0

def «utf16/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf16Segment _0 Bool.false

def «utf16_big/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf16Segment _0 Bool.false

def «utf16_little/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf16Segment _0 Bool.true

def «utf32/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf32Segment _0 Bool.false

def «utf32_big/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf32Segment _0 Bool.false

def «utf32_little/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Lynx.Term.Bitstring.utf32Segment _0 Bool.true

def «utf_mixed/1» (_0 : Lynx.Term) : Except Lynx.Exception Lynx.Term :=
  Except.bind
    (Lynx.Term.Bitstring.integerSegment (Lynx.Term.integer 1) (Lynx.Term.integer 3) 1 Bool.false)
    (fun lynxBinarySegment✝ =>
      Except.bind
        (Except.bind (Lynx.Term.Bitstring.utf8Segment _0)
          (fun lynxBinarySegment✝ =>
            Except.bind
              (Except.bind (Lynx.Term.Bitstring.utf16Segment _0 Bool.true)
                (fun lynxBinarySegment✝ =>
                  Except.bind
                    (Except.bind (Lynx.Term.Bitstring.utf32Segment _0 Bool.false)
                      (fun lynxBinarySegment✝ =>
                        Except.bind
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
