# Used by "mix format"
locals_without_parens = [
  law: 2,
  laws: 2,
  termination_suffix: 2,
  cutoff: 1,
  prelude: 1,
  postlude: 1
]

[
  inputs: ["{mix,.formatter}.exs", "{config,lib,test}/**/*.{ex,exs}"],
  locals_without_parens: locals_without_parens,
  export: [locals_without_parens: locals_without_parens]
]
