# A differential-form kernel for the vacuum and force-balance laws

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-41` |
| Title | Differential-form language for the kernel laws, with equivalences to the vector language |
| Kind | formalization |
| Addresses | `G-11` (contract infrastructure, kernel level); the "Rosetta stone" page of the exposition suite |
| Depends on | `Kernel/Vacuum` (`VacuumField`, `fieldDiv`, `fieldCurl`), `Kernel/Equilibrium` (`ForceBalance`), Mathlib's `extDeriv` (`Mathlib.Analysis.Calculus.DifferentialForm.Basic`) |
| Dependency requirement | the kernel laws as compiled; `extDeriv ω x = alternatizeUncurryFin (fderiv ℝ ω x)` (Mathlib definition) |
| Produces | `PlasmaLean/Kernel/Forms.lean` (kernel file), `PlasmaLean/Sanity/Forms.lean` (25 sanity theorems), `PlasmaLean/Theory/Fields/FormBridges.lean` (theory-layer bridges) |
| Difficulty | routine–moderate: finite-dimensional multilinear algebra; the care is in the choice of degrees and signs |
| Status | verified: vacuum and force-balance laws (kernel); first integral, symmetric flux, weak quasisymmetry, Beltrami fields and the contact condition (theory layer) |
| Lean evidence | default build: `PlasmaLean.Forms.flat`, `flux`, `density`, `hodge`, `extDeriv_flat`, `extDeriv_flux`, `VacuumForm`, `vacuumForm_flux_iff`, `vacuumField_fluxSymm_iff`, `FormForceBalance`, `formForceBalance_iff`, `forceBalance_iff`, `form_field_tangency`; `PlasmaLean.Sanity.Forms.*`; in `Theory/Fields/FormBridges`: `formFirstIntegralOn_flux_iff`, `formSymmetricFlux_iff`, `formWeakQS_flux_iff`, `formBeltramiOn_flat_iff`, `wedge12_apply`, `isContactAt_of_beltrami`, `helicalField_contact` |
| Audit evidence | not audited (new kernel file; audit findings V-1 and E-1 are restated as `vacuumForm_empty`, `formForceBalance_of_interior`) |
| Last updated | 16 November 2026: created with the Lean modules; same day, pointer to the extended Rosetta-stone page, and the theory-layer bridges implemented (`Theory/Fields/FormBridges`) |

## Purpose and scope

The exposition page `docs/PlasmaLean_Exposition_Suite/rosetta-stone.html` relates stellarator
physics to differential geometry in prose. This note records how far that correspondence is now
Lean code: maps in both directions between the vector language of the kernel and the language of
differential forms, proved inverse to each other, with the kernel laws proved equivalent under
them. It is an **addition** to the kernel (user decision, 16 November 2026): no existing
definition or theorem is changed or replaced.

Setting: `ℝ³ = Euclid3` with the Euclidean metric and standard orientation. `Form k` is the space
of real continuous alternating `k`-linear maps on `Euclid3` (the value of a differential `k`-form
at a point); a differential form is a function `Euclid3 → Form k`. Out of scope: forms on a
manifold other than `ℝ³`, other metrics, integration of forms, cohomology.

## Dependencies

- Compiled: `VacuumField`, `fieldDiv`, `fieldCurl`, `divOp`, `curlOp`, `ForceBalance`,
  `field_tangency`, and the sanity theorems of `Sanity/Vacuum`, `Sanity/AuditVacuum`,
  `Sanity/Equilibrium`, `Sanity/AuditEquilibrium`.
- Mathlib: `extDeriv`, `ContinuousAlternatingMap.alternatizeUncurryFin`, `curryLeft`,
  `Orientation.volumeForm` (with the Hadamard bound `abs_volumeForm_apply_le`, used for
  continuity), `Module.Basis.ext_alternating`.

## Sources and prior work

Standard vector-calculus/exterior-calculus dictionary in `ℝ³` (for example Frankel, *The Geometry
of Physics*, §2.9 and §3.3; Arnold–Khesin, *Topological Methods in Hydrodynamics*, Ch. I). The
request and the two design constraints are the user's (16 November 2026): choose the degree of
each form naturally (1-forms and 2-forms are isomorphic in `ℝ³`), and add to the current code
rather than replace it.

## Theory development

**Choice of degrees.** In `ℝ³` a vector can be written as a 1-form or as a 2-form. The choice
follows what the object is integrated over:

| Physics | Geometry | Lean |
| --- | --- | --- |
| scalar `p`, `ψ` | 0-form | `Euclid3 → ℝ` |
| `∇p` | 1-form `dp` (along curves) | `formGrad p`, `flat (∇p)` |
| field intensity `B♭` (Ampère) | 1-form `⋆ω_B` | `flat B = hodge (flux B)` |
| magnetic field `B` | 2-form `ω_B = ι_B vol` (flux through surfaces) | `flux B` |
| current density `J` | 2-form `ω_J = ι_J vol` | `flux J` |
| `∇ · B` | 3-form `dω_B` (over volumes) | `density (∇ · B)` |
| `∇ × B` | 2-form `d(⋆ω_B)` | `flux (∇ × B)` |

The Hodge star `hodge : Form 2 ≃ₗ Form 1` is the only place where the identification of
1-forms with 2-forms is used; it is where the metric enters.

**Equivalences.** Each is a linear equivalence with an explicit inverse (evaluation on Cartesian
unit vectors): `flat : Euclid3 ≃ₗ Form 1` (`v ↦ ⟪v, ·⟫`), `flux : Euclid3 ≃ₗ Form 2`
(`v ↦ ι_v vol`), `density : ℝ ≃ₗ Form 3` (`c ↦ c vol`), `hodge := flux.symm.trans flat`, and
pointwise `fluxField : (Euclid3 → Euclid3) ≃ (Euclid3 → Form 2)`. Surjectivity is proved by
checking forms on tuples of distinct basis vectors (`ext_basis`).

**Dictionary for `d`.** Both sides use the Fréchet derivative, so no differentiability
hypothesis is needed: `extDeriv_flat` (`d(B♭) = flux (∇ × B)`), `extDeriv_flux`
(`d(ι_B vol) = (∇ · B) vol`), `extDeriv_formGrad`. The proofs reduce to the algebraic statements
`alternatize_flat`, `alternatize_flux` about a derivative operator `L`, which are checked after
applying the inverse equivalence, i.e. on basis vectors.

**Laws.** `VacuumForm Ω ω`: `Ω` open, `ω` of class `C²`, `dω = 0` (Gauss), `d(⋆ω) = 0` (Ampère
without current). `FormForceBalance ωB ωJ dp`: `ι_B ω_J = dp` with `B = flux.symm ωB`; the sign
is fixed by `curryLeft_flux` (`ι_B ι_J vol = (J × B)♭`) and checked by the pinch fixture. The
algebraic kernel uses `Vec3 = Fin 3 → ℝ`; the bridge goes through `vec : Vec3 ≃ₗ Euclid3`.

**Sanity checks.** Statements are made afresh in form language; proofs of the checks of the laws
are transported from the vector-language checks through the `iff` theorems (the basis-value and
round-trip checks are proved directly).

**Other layers.** A theorem of the theory or design layers about `VacuumField` or `ForceBalance`
applies to forms by one use of `vacuumField_fluxSymm_iff` or `forceBalance_iff`
(`form_field_tangency` is the example). Restating such a theorem in form language is still a
manual step; its proof is a single transport.

## Claims and evidence

All compiled Lean theorems, default build, standard axioms only (`scripts/check_axioms.lean`).

1. `flat`, `flux`, `density`, `hodge`, `vec`, `fluxField` are equivalences (both directions
   explicit). No hypotheses.
2. `extDeriv_flat`, `extDeriv_flux`: unconditional, at every point.
3. `vacuumForm_flux_iff : VacuumForm Ω (fluxField B) ↔ VacuumField Ω B` and
   `vacuumField_fluxSymm_iff : VacuumField Ω (fluxField.symm ω) ↔ VacuumForm Ω ω`.
4. `formForceBalance_iff`, `forceBalance_iff`: `FormForceBalance` and `ForceBalance` correspond in
   both directions. As for `ForceBalance`, `dp` is supplied data (finding E-1 carries over:
   `formForceBalance_of_interior`).
5. `form_field_tangency`: `dp(B) = 0` under `FormForceBalance`, transported from `field_tangency`.
6. `Sanity/Forms`: accepted fixtures (zero and constant forms, the hyperbolic field's flux form,
   which equals `⋆dp` for its potential; uniform, parallel and pinch balances), rejected fixtures
   (rotation field: closed, not co-closed; identity field: `dω = 3 vol`; perpendicular data;
   reversed sign), regressions V-1 and E-1.

## Difficulty, barriers and readiness

- **Covered Rosetta entries:** solenoidal field, vacuum field, MHS equilibrium.
- **Lean-ready with the same pattern:** flux-surface first integral (`dψ(B) = 0`), weak
  quasisymmetry (`cross (B x) (ξ x) = -gradient ψ x` as `ι_ξ ω_B = ± dψ`; the sign is to be fixed
  by a fixture), and `Fields.magneticTwoForm B u v = flux B ![u, v]`.
- **Not a dictionary question:** rotation number, Boozer charts, harmonic-map univalence, coil
  reach, non-constant conformal modulus. The geometric objects themselves (manifolds, charts,
  uniformization) are missing, so no equivalence can supply them.
- **No differential-geometric content to translate:** the Fusion, Transport and slab kernels.
- **Library gap:** Mathlib has `extDeriv` on normed spaces only; forms on manifolds would need a
  different carrier, and the equivalences would become bundle isomorphisms.

## Outputs and next dependencies

- New modules `Kernel/Forms`, `Sanity/Forms`, imported by `PlasmaLean.lean`; eight entry points
  added to `scripts/check_axioms.lean`.
- Next: the first-integral and weak-quasisymmetry bridges; a strict audit of the new kernel file
  (skill `plasmalean-audit-domain`).
- **Rosetta-stone page extended (16 November 2026, after a literature search).** The page
  `docs/PlasmaLean_Exposition_Suite/rosetta-stone.html` now has 29 entries (was 14), each with its
  sources. It names further bridges that fit `Kernel/Forms`, none of them in Lean yet: the
  Beltrami predicate `extDeriv (fun y => flat (B y)) x = λ • flux (B x)`, and
  `Kinetic.SymmetricFlux B G K` as `ι_K ω_B = ± dψ` (sign to be fixed by a fixture), besides the
  first integral and weak quasisymmetry listed above.
- **Theory-layer bridges implemented (16 November 2026).** `PlasmaLean/Theory/Fields/FormBridges.lean`
  (default build, standard axioms; it is a theory file, since the kernel does not import the theory
  layer). All are compiled Lean theorems:
  - `curryLeft_flux_cross` (`ι_w ι_v vol = (v × w)♭`), `flat_gradient` (`(∇ψ)♭ = dψ`, no
    hypothesis), `flux_apply_eq_magneticTwoForm`.
  - First integral: `FormFirstIntegralOn`, `formFirstIntegralOn_flux_iff`.
  - Symmetric flux: `FormSymmetricFlux` (`ι_K ω = -γ`), `formSymmetricFlux_iff` with
    `Kinetic.SymmetricFlux`. The sign is settled: `SymmetricFlux B G K` is `ι_K ω_B = -G♭`.
  - Weak quasisymmetry: `FormWeakQS` (`d(ι_ξ vol) = 0`, `ι_ξ ω = -dψ`, `d|B|(ξ) = 0`),
    `formWeakQS_flux_iff`; fixtures `formWeakQS_uniform`, `formWeakQS_screw` transported.
  - Beltrami: `IsBeltramiOn` (new vector-language predicate `∇ × B = λB`), `FormBeltramiOn`
    (`dβ = λ ⋆β`), `formBeltramiOn_flat_iff`.
  - Contact condition: `wedge12` (defined through the equivalences, and proved to be the
    alternating product in `wedge12_apply`), `IsContactAt` (`β ∧ dβ ≠ 0`),
    `isContactAt_flat_iff` (`⟪B, ∇ × B⟫ ≠ 0`), `isContactAt_of_beltrami` (the pointwise half of
    the Etnyre–Ghrist correspondence), `VacuumField.not_isContactAt`.
  - Fixtures: the helical field `(cos z, sin z, 0)` is Beltrami with `λ = -1` and contact
    everywhere (`helicalField_beltrami`, `helicalField_contact`; it is `Equilibrium.helicalSlab`
    on `ℝ³`, `helicalField_eq_helicalSlab`); rejected `λ = 1`
    (`helicalField_not_beltrami_one`); constant fields are Beltrami with `λ = 0` and not contact.
  - Not covered: the Reeb field, the converse direction (a metric adapted to a contact form),
    a wedge product of general degrees, toroidal Beltrami fields.
