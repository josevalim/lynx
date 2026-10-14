# Used by "mix format"
[
  inputs: ["{mix,.formatter}.exs", "{config,lib,test}/**/*.{ex,exs}"],
  locals_without_parens: [law: 2, laws: 2, termination_suffix: 2],
  export: [locals_without_parens: [law: 2, laws: 2, termination_suffix: 2]]
]
