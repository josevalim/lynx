import Benchmarks.Common

open Lynx LynxBench
set_option Elab.async false

#bench "erlang/sum-contract"
theorem erlang_sum_contract : Satisfies sumTerm sumExpects sumEnsures := by
  lynx_verify

#bench "erlang/sum-append"
theorem erlang_sum_append : Property appendExpects appendExpression := by
  lynx_verify
