# Strict audit of the differential-form modules, 16 November 2026

Skill: `plasmalean-audit-domain`, proof policy `plasmalean-lean-proofs`.

| Item | Value |
| --- | --- |
| Previous audited commit | `921a8c3` (refresh audit, 31 October 2026) |
| Audited commit | `1e5d4f3` (branch `tauceti`, 16 November 2026); corrections are in the commit that adds this record |
| Toolchain | Lean `v4.35.0`; TauCeti `v4.35.0`; Mathlib transitive at `0740637` |
| Scope | **partial audit**: `PlasmaLean/Kernel/Forms.lean` (new kernel file), `PlasmaLean/Sanity/Forms.lean`, `PlasmaLean/Theory/Fields/FormBridges.lean`, and the claims about them in note N-45, the plan and the Rosetta-stone page. Not in scope: everything else changed since `921a8c3` (the Dommaschk certification, the TauCeti migration and other work of 1–16 November), which still needs a refresh audit |
| Method | the author's own pass plus an independent read-only sub-audit that was given the files and a red-team checklist, not the author's conclusions. Its scratch checks compiled; each finding below was re-checked against the source before it was accepted |

## Commands run

- Scans of the three files for `sorry`, `admit`, `axiom`, `native_decide`, any `decide` variant,
  `unsafe`, `instance`: no forbidden construct; one global instance (AF-L1).
- `lake env lean` on each changed file during correction; `lake build` (3946 jobs, zero
  warnings) on the workstation with a plain parallel build.
- `lake env lean scripts/check_axioms.lean`: passed, "Axiom audit passed for 51135 PlasmaLean
  declarations"; the 22 `#print axioms` lines for the form modules show standard axioms only.
- `scripts/check_axioms_heavy.lean` was not run (no on-demand module imports these files).

## Kernel inventory: `Kernel/Forms.lean`

12 definitions and laws, 26 theorems. Every declaration was read.

| Declaration | Kind | Status after the audit |
| --- | --- | --- |
| `Form`, `stdBasis` | abbreviations | correct |
| `volForm` | definition (Mathlib's volume form for the standard orientation, made continuous by the Hadamard bound) | correct; `volForm_apply` (determinant), `volForm_vec`, `Sanity/Forms.volForm_frame`, `volForm_frame_swap` |
| `flat`, `flux`, `density` | linear equivalences with explicit inverses | correct; orientation `flux e₀ = dy ∧ dz`, inverse reads `(ω₁₂, ω₂₀, ω₀₁)`; basis values checked directly (`flux_coordVec`, `AuditForms.flux_coordVec_one`, `flux_coordVec_two`) |
| `hodge` | equivalence `Form 2 ≃ₗ Form 1`, defined as `flux.symm.trans flat` | correct, one degree only; independent characterisation added (`AuditForms.wedge_eq_inner_hodge`) |
| `formGrad` | definition (`dp`) | correct; `extDeriv_formGrad` |
| `extDeriv_flat`, `extDeriv_flux` | dictionary theorems | correct and genuinely unconditional (both sides totalize to `0`); Mathlib's normalization has no factorials; independent check `AuditForms.extDeriv_x_dy`; mutual consistency `AuditForms.div_curl_eq_zero` |
| `VacuumForm` | law (structure, 4 fields) | equivalent to `VacuumField` both ways with the same `C²` regularity; vacuous on `∅` (`vacuumForm_empty`, as V-1); regularity field shown load-bearing (`AuditForms.absField_not_vacuumForm`) |
| `fluxField` | equivalence of fields | correct |
| `vec` | equivalence `Vec3 ≃ₗ Euclid3` | correct |
| `FormForceBalance` | law (class, 1 field) | says `J × B = ∇p` with the kernel's sign (`curryLeft_flux`; direct determinant check `AuditForms.interior_pinch_direct`); vacuous for `dp := ι_B ω_J` (`formForceBalance_of_interior`, as E-1) |
| `form_field_tangency`, `form_current_tangency`, `formGradient_zero_iff_force_free` | theorems | the last two were missing and are added (AF-M7) |

## Findings

No exported theorem was false. The sign, orientation and normalization conventions are mutually
consistent. All findings except AF-L4 and AF-L5 are resolved in the same commit.

| ID | Severity | Location | Summary | Resolution |
| --- | --- | --- | --- | --- |
| AF-H1 | **high** (documentation) | `FormBridges.lean` module doc | The doc said symmetric-flux fixtures were transported; none existed | doc corrected; `formSymmetricFlux_uniform`, `not_formSymmetricFlux_uniform`, `formSymmetricFlux_zero` added |
| AF-M1 | medium | `IsBeltramiOn`, `FormBeltramiOn` | No regularity clause: by totalized `fderiv` a field with a kink was "Beltrami with `λ = 0`" at the kink. The docstring said "force-free" although `∇ · B = 0` is not required and the zero field satisfies it for every `λ`. No link to the kernel's force balance | **definitions changed**: both now require differentiability at each point. Docstrings state the scope. `IsBeltramiOn.formForceBalance` (Beltrami ⇒ `ι_B ω_J = 0`), `isBeltramiOn_iff_curl`. Regressions `absField_curl_equation`, `absField_not_beltrami`, `zero_beltrami`, `id_beltrami_not_solenoidal`; `helicalField_div`, `helicalField_forceFree` |
| AF-M2 | medium | `Sanity/Forms.lean` | Every `VacuumForm` and `FormForceBalance` check was transported through the dictionary under test, so a convention error shared by `flux` and the dictionary would pass | `extDeriv_x_dy` (from Mathlib's `extDeriv_apply`), `interior_pinch_direct`, `div_curl_eq_zero` (from `extDeriv_extDeriv`), `wedge_eq_inner_hodge`, `wedge12_dx_dydz`, `wedge12_dx_dzdx` |
| AF-M3 | medium | `VacuumForm` | The totalization regression of the vector kernel (`absField`) was not carried over | `absField_form_closed_coclosed`, `absField_not_vacuumForm` |
| AF-M4 | medium | `FormSymmetricFlux` | `γ` is free data, so `γ := -ι_K ω` always satisfies the law (the E-1 hazard); the module doc wrote "with `γ = dψ`"; no first-integral consequence | docstring and module doc corrected; regression `formSymmetricFlux_of_interior`; `FormSymmetricFlux.formFirstIntegralOn` |
| AF-M5 | medium | `FormWeakQS`, `FormFirstIntegralOn` | Incomplete triads: no rejected fixture, no vacuity regression, one fixture for first integrals | `formWeakQS_zero`, `not_formWeakQS_mirror`, `formFirstIntegralOn_const`, `not_formFirstIntegralOn_x`, `not_formFirstIntegralOn_of_not_differentiableAt`; docstring states that `ω` need not be closed |
| AF-M6 | medium | `IsContactAt`, `wedge12` | Every negative fixture had zero curl; no value check; only one direction of the Beltrami statement | `rotationField_not_contact` (curl `≠ 0`, not contact), `helicalField_wedge` (`β ∧ dβ = -vol`: a negative contact form), `IsBeltramiOn.isContactAt_iff` (sharp) |
| AF-M7 | medium | `Kernel/Forms.lean` | Missing analogues of `current_tangency` and `gradient_zero_iff_force_free` | `form_current_tangency`, `formGradient_zero_iff_force_free`; `AuditForms.form_tangencies`, `form_force_free_nonvacuum` |
| AF-L1 | low | `Kernel/Forms.lean` | A global `Fact (finrank ℝ Euclid3 = 3)` instance was exported from a kernel file | made `local` |
| AF-L2 | low | `FormBridges.lean`, `Sanity/Forms.lean` | `VacuumField.not_isContactAt` and `VacuumForm.const_smul` were declared in the wrong namespace, so dot notation failed | renamed `not_isContactAt_of_vacuumField`, `vacuumForm_const_smul` |
| AF-L3 | low | module docs | Unbacked statements: `flat (∇p)` in the kernel table; "Clebsch flux form `dψ ∧ dχ`"; "four notions"; the star on 1-forms | docs corrected; `flux_cross_apply` proves `ι_{a♯ × b♯} vol = a ∧ b` |
| AF-L4 | low, **open** | `Sanity/Forms.lean` | `hodge_dydz`, `formPinch_tangency` and the three round-trip theorems hold by definition and test nothing | kept (harmless); superseded by `Sanity/AuditForms` |
| AF-L5 | low, **open** | `FormBridges.lean` | Fixtures of the theory file are in the file itself and in the namespace `PlasmaLean.Forms`; no Beltrami fixture with non-constant `λ`; `forceBalance_smul_*` not transported; `wedge12` covers degrees (1,2) only; `‖flux v‖` is not related to `‖v‖`; no Reeb field | recorded; none blocks a claim |

**Changed definitions.** `IsBeltramiOn` and `FormBeltramiOn` (introduced in `1e5d4f3`) now carry a
differentiability clause. They had no users outside `FormBridges.lean`. Renamed declarations:
`VacuumField.not_isContactAt` → `not_isContactAt_of_vacuumField`; `VacuumForm.const_smul` →
`vacuumForm_const_smul`.

## Assumption ledger

- No physical law is introduced. `VacuumForm` and `FormForceBalance` are restatements of
  `VacuumField` and `ForceBalance`, proved equivalent; they inherit those laws' envelopes and
  their vacuity findings V-1 and E-1.
- Supplied data, never derived: `dp` in `FormForceBalance`; `γ` in `FormSymmetricFlux`; `ψ` and
  `ξ` in `FormWeakQS`; `λ` in the Beltrami predicates.
- Mathematical setting: `ℝ³`, Euclidean metric, standard orientation; Mathlib's `extDeriv` with
  the convention `dω(v₀, …) = Σ (−1)ⁱ D ω(…; v̂ᵢ) vᵢ`.

## Scope statement

- **Proved:** the equivalences; `d(B♭) = flux(∇ × B)` and `d(ι_B vol) = (∇ · B) vol` at every
  point; the two kernel laws and the four theory notions are equivalent to their vector forms;
  a Beltrami field (differentiable, curl equation) has zero Lorentz force and, where `λ ≠ 0` and
  `B ≠ 0`, a contact form `B♭`.
- **Not proved:** anything on a manifold other than `ℝ³`; integration, Stokes' theorem or
  cohomology for these forms; a general wedge product; the Reeb field or the converse of the
  Etnyre–Ghrist correspondence; existence of any equilibrium or surface. No contract clause
  C1–C5 is affected.

## Sanity coverage after the audit

| Law or predicate | Degenerate | Instance | Counterexample | Risk-specific |
| --- | --- | --- | --- | --- |
| `VacuumForm` | `zero_vacuumForm` | `hyperbolic_vacuumForm` | `rotation_not_vacuumForm`, `id_not_vacuumForm` | `vacuumForm_empty`, `absField_not_vacuumForm`, `extDeriv_x_dy`, `div_curl_eq_zero` |
| `FormForceBalance` | `uniformFormBalance` | `formPinch_force_inward` | `formForceBalance_rejects_perp`, `…_rejects_reversed` | `formForceBalance_of_interior`, `interior_pinch_direct`, `form_tangencies` |
| `FormFirstIntegralOn` | `formFirstIntegralOn_const` | `clebsch_formFirstIntegral_left` | `not_formFirstIntegralOn_x` | `not_formFirstIntegralOn_of_not_differentiableAt` |
| `FormSymmetricFlux` | `formSymmetricFlux_zero` | `formSymmetricFlux_uniform` | `not_formSymmetricFlux_uniform` | `formSymmetricFlux_of_interior` |
| `FormWeakQS` | `formWeakQS_uniform` | `formWeakQS_screw` | `not_formWeakQS_mirror` | `formWeakQS_zero` |
| `IsBeltramiOn` | `const_beltrami` | `helicalField_beltrami` | `helicalField_not_beltrami_one` | `absField_not_beltrami`, `zero_beltrami`, `id_beltrami_not_solenoidal` |
| `IsContactAt` | `const_not_contact` | `helicalField_contact` | `rotationField_not_contact` | `helicalField_wedge`, `IsBeltramiOn.isContactAt_iff` |

## Next

- A refresh audit of everything else changed since `921a8c3`.
- AF-L5: a Beltrami fixture with non-constant `λ`.
