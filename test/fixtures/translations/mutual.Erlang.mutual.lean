module

public import Lynx

@[expose] public section

namespace Erlang.mutual

section

set_option «match».ignoreUnusedAlts true

#lynx_pure
  mutual
    def «odd/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.atom "false")
      | Lynx.Term.cons _2 vXs => «even/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «even/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.atom "true")
      | Lynx.Term.cons _2 vXs => «odd/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    def «first/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 0)
      | Lynx.Term.cons _2 vXs => «second/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «second/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 1)
      | Lynx.Term.cons _2 vXs => «third/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    def «third/1» (_0 : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.nil => pure (Lynx.Term.integer 2)
      | Lynx.Term.cons _2 vXs => «first/1» vXs
      | _1 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
  end

#lynx_pure
  mutual
    def «outer/3» (_0 : Lynx.Term) (vYs : Lynx.Term) (vZs : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.cons vX vXs => «middle/5» vYs vXs vYs vZs vX
      | Lynx.Term.nil => pure Lynx.Term.nil
      | _5 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    termination_by (sizeOf✝ _0, (0, 0))
    def «middle/5» (_0 : Lynx.Term) (vXs : Lynx.Term) (vYs : Lynx.Term) (vZs : Lynx.Term)
        (vX : Lynx.Term) : Lynx.Result :=
      match _0 with
      | Lynx.Term.cons vY vRest => «inner/6» vZs vRest vXs vYs vZs (Lynx.Term.tuple #[vX, vY])
      | Lynx.Term.nil => «outer/3» vXs vYs vZs
      | _9 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    termination_by (sizeOf✝ vXs, (1 + sizeOf✝ _0, 0))
    def «inner/6» (_0 : Lynx.Term) (vPending : Lynx.Term) (vXs : Lynx.Term) (vYs : Lynx.Term)
        (vZs : Lynx.Term) (_5 : Lynx.Term) : Lynx.Result :=
      match _0, _5 with
      | Lynx.Term.cons vZ vRest, vPair => do
        let _6 ← «inner/6» vRest vPending vXs vYs vZs vPair
        pure (Lynx.Term.cons (Lynx.Term.tuple #[vPair, vZ]) _6)
      | Lynx.Term.nil, Lynx.Term.tuple ⟨[vX, _13]⟩ => «middle/5» vPending vXs vYs vZs vX
      | _12, _7 => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "function_clause"))
    termination_by (sizeOf✝ vXs, (1 + sizeOf✝ vPending, 1 + sizeOf✝ _0))
  end

#lynx_pure
  def «identity/1» (_0 : Lynx.Term) : Lynx.Result :=
    pure _0

#lynx_pure
  def «triples/3» (_0 : Lynx.Term) (_1 : Lynx.Term) (_2 : Lynx.Term) : Lynx.Result :=
    «outer/3» _0 _1 _2

end

end Erlang.mutual
