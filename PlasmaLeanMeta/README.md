# PlasmaLeanMeta/

`meta` code compiled to native code (`precompileModules = true` in `lakefile.toml`), so that proof
builders run about 10× faster than in the interpreter. It depends only on Lean.

- [`EvalCert.lean`](EvalCert.lean): the builder of `eval_cert`, `eval_cert?` and `eval_decide`, a
  call-by-value evaluator that produces an `ECert` proof term node by node, with shared subterms
  and untrusted fast paths for leaf values. It is imported by
  `PlasmaLean/Certificates/EvalCert.lean`, which holds the predicate `ECert` and its soundness
  theorem.

Nothing here is trusted: the kernel checks the terms it produces. A change here makes every
`eval_cert`/`fiv_cert` module stale (hundreds of modules); rebuild them one at a time. Keep this
library free of Mathlib imports so that it compiles quickly.
