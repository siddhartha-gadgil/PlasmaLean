# LeanTheory

A minimal, general template for formalizing a **mathematical-physics theory in Lean 4** with
**verified numerics** and **proof-term certificates**. It was extracted from a larger project
by removing everything domain-specific and keeping the general machinery:

- an architecture that separates the *model* (laws stated as typeclasses, never axioms) from its
  *sanity checks*, *bridges*, general *theory*, numerical *certificates* and concrete *designs*;
- a certificate toolkit that turns large numerical checks into explicit proof terms checked by the
  Lean kernel (no `decide`, no `native_decide`, standard axioms only);
- general analysis used by such certificates (strip/Fourier Banach algebras, KAM-type Newton
  iterations, analytic composition, Sturm–Picone–Riccati comparison, ODE barriers);
- agent skills and a workstation pipeline for offloading heavy numerics and builds.

A small worked example (a one-dimensional harmonic oscillator) runs through every layer.

## Getting started

```bash
scripts/setup.sh                    # installs elan if missing, fetches the Mathlib cache, builds
scripts/setup.sh --check-axioms     # ... and runs the axiom audit
scripts/setup.sh --python           # ... and creates the Python venv for oracle scripts
```

`scripts/setup.sh` is idempotent (Linux and macOS); `scripts/setup.sh --help` lists its options.
By hand: install [elan](https://github.com/leanprover/elan), then `lake exe cache get`,
`lake build`, `lake env lean scripts/check_axioms.lean`. The toolchain is pinned in
`lean-toolchain` (Lean and Mathlib `v4.34.1`).

## Architecture

```text
LeanTheory.lean          Root: imports every module of the default build
LeanTheory/
  Kernel/                Model laws as typeclasses (no axioms)          Kernel/Example.lean
  Sanity/                Degenerate cases, instances, counterexamples  Sanity/Example.lean
  Bridge/                Composition theorems between laws and results Bridge/Example.lean
  Theory/                General mathematics (KAM, Stability, Fields)
  Certificates/          Certificate formats, soundness theorems, proof-term builders
  Design/                Concrete certified candidates (empty in the template)
  SubsetSum.lean         Reference pattern: large proofs as explicit proof terms
LeanTheoryMeta/          `meta` code of `eval_cert`, precompiled to native code
scripts/                 Setup, axiom audit, kernel_fact audit, workstation pipeline
notes/                   Method notes: domain libraries, model contracts, plan skeleton
.agents/skills/          Agent skills (`.claude` is a symlink to `.agents`)
```

- **Kernel.** The domain model: definitions, and laws as typeclasses that theorems take as
  hypotheses. Kept small. Never an `axiom`.
- **Sanity.** For each law: a degenerate case, a concrete instance (so the law is satisfiable and
  theorems are not vacuous) and a counterexample (so the law excludes what it should).
- **Bridge.** Theorems that compose laws with each other and with theory or certificate results,
  with every hypothesis explicit.
- **Theory.** General mathematics, independent of the domain model.
- **Certificates.** Exact data plus checkers with soundness theorems; large checks are built as
  explicit proof terms whose leaves are kernel facts.
- **Design.** Concrete candidates whose properties are proved by composing the layers above.

The worked example: `Kernel/Example` states Newton's law for the oscillator as the typeclass
`OscillatorLaw` and proves `energy_conserved`; `Sanity/Example` gives the free particle, the
instance `cos`/`-sin` and the non-instance `exp`; `Bridge/Example` proves time-shift invariance,
superposition and `amplitude_bound`; `Certificates/Example` certifies, with `kernel_fact`, an
energy bound for 21 exact initial states and concludes `amplitude_cert`: `3 x(t)² ≤ 1` for all
time along every trajectory starting at one of them.

## Certificate toolkit

| Tactic / pattern | Module | Certifies |
| --- | --- | --- |
| SubsetSum pattern | `SubsetSum` | Reference: inductive certificate predicate, soundness by induction, `meta` builder producing the proof term |
| `kernel_fact` | `Certificates/KernelFact` | Closed facts (`∧`, `≤`, `<`, `≠`, `=` on `ℕ`/`ℚ`, list and bounded quantifiers) as proof terms with kernel-fact leaves |
| `eval_cert [f…]`, `eval_decide` | `Certificates/EvalCert`, `LeanTheoryMeta/EvalCert` | Evaluation of closed terms (integers, rationals, balls, records, lists, recursion), node by node with shared subterms |
| `fiv_cert`, `fiv_decide` | `Certificates/EvalCertFIv` | `eval_cert` preset for fixed-point interval (ball) arithmetic |
| `bool_cert` | `Certificates/BoolCert` | Boolean checkers recursing over lists, as explicit certificates |
| `icc_cert`, `icc_close` | `Certificates/IccListCert` | Finite sums and quantifiers over integer intervals |
| `kron_proof`, `kron2_proof`, `kron_lt` | `Certificates/KronProof`, `KronProof2D` | Kronecker-substitution ball checks (polynomial norms) as proof terms |
| `l1kron_cert`, `fampack_cert` | `Certificates/DigitSumCert`, `FamPackCert` | Digit sums and packed images of polynomial families |
| `QPoly.checkOn` | `Certificates/PolyInterval` | Polynomial lower bounds on every real point of an interval |
| radii polynomial, contraction | `Certificates/RadiiPolynomial`, `Contraction` | Existence of a true zero near an approximate one |
| `FIv` balls, validated trig | `Certificates/ValidatedQuadrature`, `ValidatedTrig(Fast)` | Sound interval arithmetic, `sqrt`, `exp`, trig, quadrature |

(`eval_decide` and `fiv_decide` are evaluation certificates of `decide p`, not the `decide`
tactic.) See [LeanTheory/Certificates/README.md](LeanTheory/Certificates/README.md) for every
module.

## Policies

- **No `decide` of any kind** (`decide`, `decide +kernel`, `decide_cbv`, `native_decide`): use
  `norm_num`/`rfl` for a few closed facts, `kernel_fact`/`eval_cert` for medium checks and the
  SubsetSum pattern for large ones.
- **Standard axioms only**: `lake env lean scripts/check_axioms.lean` must pass (only `propext`,
  `Classical.choice`, `Quot.sound`). No `sorry`, `axiom`, `admit`.
- **Zero warnings** in `lake build` (including the 100-character line linter).
- **≤ 6 GB per Lean process**: split large certificates over several modules; build heavy
  modules in small groups rather than letting Lake compile many at once.
- Every module, definition and theorem has a docstring; every new definition or certificate
  format has sanity theorems (degenerate case, instance, accepted and rejected fixtures).

## Workstation workflow

Heavy untrusted numerics and first builds of large certificates run on a workstation through
`scripts/workstation/run.sh <task>`, which pushes a `workstation/*` branch with measurements and
a laptop verdict. On the laptop, "update from workstation" (skill `workstation-update`) re-checks
and merges passing runs. Compiled modules can be shared with `scripts/workstation/oleans.py`.
See [Workstation.md](Workstation.md).

## Starting a new theory

1. Rename the library if you like (`LeanTheory` in `lakefile.toml`, the directories and the
   namespaces), and state the goals in `notes/implementation-plan.md`.
2. Write the kernel: definitions plus laws as typeclasses, following `Kernel/Example` and
   [notes/domain-libraries.md](notes/domain-libraries.md); record the contracts in
   [notes/formalization/00-model-contracts.md](notes/formalization/00-model-contracts.md).
3. Add the sanity triad for every law (`Sanity/Example`).
4. Build theory and bridges; prove semantic soundness theorems for any checker you add.
5. Generate certificates with an untrusted oracle (Python in `scripts/`), validate every bound
   in exact arithmetic before emitting Lean, and prove them with the toolkit above.
6. Compose them in `Design/`, register entry points in `scripts/check_axioms.lean` and imports in
   `LeanTheory.lean`.

The skills in [.agents/skills](.agents/skills/README.md) (`lean-proofs`, `certify-numerics`,
`discover-theory`, `formalize-theory`, `audit-domain`, `domain-design`, `workstation-update`)
describe each step for an agent.

**Future work.** A configurable documentation pipeline (handbook site and progress slideshow
generated from the notes) existed in the original project and was removed from the template.

## License

Apache 2.0; see [LICENSE](LICENSE).
