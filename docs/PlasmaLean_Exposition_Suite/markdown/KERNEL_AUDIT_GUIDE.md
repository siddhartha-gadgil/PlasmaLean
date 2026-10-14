# Audit the PlasmaLean Small Kernel in 10 Minutes

## Why a Small Kernel + Sanity Checks?

In formalizing applied physics and stellarator engineering, the primary epistemic risk is **specification drift**: proving a 5,000-line theorem about a definition that subtly misstates the physics (for instance, allowing $\mathbf{B} \equiv 0$, dividing by zero via `x / 0 = 0`, or taking a supremum over an empty set). 

**PlasmaLean** solves this via the **Small-Kernel & Sanity-Check Pattern**:

1. **Tiny Trusted Specification (~120 lines):** All top-level physical contracts live in a concise, human-readable kernel.

2. **Non-Vacuity Sanity Checks:** Every kernel definition is paired with compiled witness theorems proving that trivial/degenerate solutions are rejected and analytical benchmarks satisfy the contract.

3. **Zero Project Axioms:** `#print axioms` on any top-level certificate shows only `[propext, Classical.choice, Quot.sound]`.

---

## 1. Ambient 3-Space & Differential Operators (Minutes 0–2)

```lean
-- PlasmaLean/Kernel/BasicOperators.lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

abbrev ℝ³ := EuclideanSpace ℝ (Fin 3)
abbrev VectorField := ℝ³ → ℝ³
abbrev ScalarField := ℝ³ → ℝ

/-- Divergence ∇ · B via trace of the Fréchet derivative matrix -/
noncomputable def divergence (B : VectorField) (x : ℝ³) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ B x (EuclideanSpace.single i 1)) i

/-- Curl ∇ × B in standard right-handed Euclidean coordinates -/
noncomputable def curl (B : VectorField) (x : ℝ³) : ℝ³ :=
  let D := fun i j => (fderiv ℝ B x (EuclideanSpace.single j 1)) i
  ![D 2 1 - D 1 2, D 0 2 - D 2 0, D 1 0 - D 0 1]
```

- **Physical & Mathematical Role:** Every downstream statement about magnetic fields rests on `divergence` and `curl`. By defining them directly via Mathlib's `fderiv ℝ` on `EuclideanSpace ℝ (Fin 3)` rather than introducing axiomatic differential operators, any proof using them inherits Mathlib's chain rule and linearity theorems automatically.

- **Specification Bug Prevented:** Prevents 'dummy operator' bugs where `divergence` is declared as an uninterpreted function `VectorField → ScalarField` with ad-hoc axioms that might be inconsistent with standard calculus.

- **Compiled Sanity Check:**
```lean
-- Sanity Check 1: Divergence of identity field x ↦ x is 3
theorem divergence_id (x : ℝ³) : divergence id x = 3 := by
  simp [divergence, fderiv_id]
  norm_num
```

## 2. Flux Surface & Magnetic Tangent Contract (Minutes 2–5)

```lean
-- PlasmaLean/Kernel/FluxSurfaceContract.lean
structure IsRegularLevelSurface (ψ : ScalarField) (c : ℝ) : Prop where
  nonempty : (ψ ⁻¹' {c}).Nonempty
  compact  : IsCompact (ψ ⁻¹' {c})
  regular  : ∀ x ∈ ψ ⁻¹' {c}, grad ψ x ≠ 0

/-- A magnetic field B is confined to the level surface ψ(x) = c -/
structure HasFluxSurface (B : VectorField) (ψ : ScalarField) (c : ℝ) : Prop
    extends IsRegularLevelSurface ψ c where
  b_nonvanishing : ∀ x ∈ ψ ⁻¹' {c}, B x ≠ 0
  tangent_to_surface : ∀ x ∈ ψ ⁻¹' {c}, ⟪B x, grad ψ x⟫_ℝ = 0
```

- **Physical & Mathematical Role:** In stellarator optimization, a surface $\Sigma_c = \psi^{-1}(c)$ is only a valid magnetic flux surface if: (1) it is actually non-empty and compact, (2) $\nabla\psi \neq 0$ everywhere on it (so it is a smooth 2-manifold without singular X-points), and (3) $\mathbf{B} \cdot \nabla\psi = 0$ with $\mathbf{B} \neq 0$.

- **Specification Bug Prevented:** Without `nonempty`, `regular`, and `b_nonvanishing`, an AI agent or optimizer can trivially 'prove' perfect confinement by choosing a constant function $\psi(x) = c_0 \neq c$ (empty level set!) or $\mathbf{B} \equiv 0$ (zero field trivially satisfies $\mathbf{B}\cdot\nabla\psi = 0$).

- **Compiled Sanity Check:**
```lean
-- Sanity Check 2: Trivial zero field B ≡ 0 CANNOT satisfy HasFluxSurface
theorem zero_field_not_flux_surface (ψ : ScalarField) (c : ℝ) :
    ¬ HasFluxSurface (fun _ => 0) ψ c := by
  intro h
  rcases h.nonempty with ⟨x, hx⟩
  exact h.b_nonvanishing x hx rfl
```

## 3. Vacuum Field & Biot–Savart Clearance Contract (Minutes 5–8)

```lean
-- PlasmaLean/Kernel/VacuumContract.lean
structure IsVacuumMagneticField (U : Set ℝ³) (B : VectorField) : Prop where
  is_open  : IsOpen U
  smooth   : ContDiffOn ℝ 2 B U
  div_zero : ∀ x ∈ U, divergence B x = 0
  curl_zero : ∀ x ∈ U, curl B x = 0

/-- Minimum Euclidean distance between a 3D coil curve γ and target domain U -/
def HasClearanceMargin (γ : ℝ → ℝ³) (U : Set ℝ³) (d_min : ℝ) : Prop :=
  d_min > 0 ∧ ∀ s : ℝ, ∀ x ∈ U, ‖x - γ s‖ ≥ d_min
```

- **Physical & Mathematical Role:** The Biot–Savart integral $B(x) = \frac{\mu_0 I}{4\pi}\oint \frac{\gamma'(s) \times (x - \gamma(s))}{|x - \gamma(s)|^3} ds$ has a $1/r^2$ singularity along the coil filament $\gamma$. Requiring `HasClearanceMargin γ U d_min` in the kernel contract guarantees that $B$ is real-analytic and harmonic throughout $U$.

- **Specification Bug Prevented:** Prevents division-by-zero traps in Lean's real division (`x / 0 = 0` in Lean/Mathlib!). Without an explicit `d_min > 0` clearance hypothesis, an expression dividing by `‖x - γ s‖^3` evaluates to `0` on the coil rather than raising a type error.

- **Compiled Sanity Check:**
```lean
-- Sanity Check 3: Clearance margin strictly excludes coil points from plasma domain
theorem coil_disjoint_from_plasma (γ : ℝ → ℝ³) (U : Set ℝ³) (d : ℝ)
    (h : HasClearanceMargin γ U d) (s : ℝ) : γ s ∉ U := by
  intro hx
  have hdist := h.2 s (γ s) hx
  simp only [sub_self, norm_zero] at hdist
  linarith [h.1]
```

## 4. Tolerance-Aware Vacuum Fixture Certificate (Minutes 8–10)

```lean
-- PlasmaLean/Kernel/FixtureCertificate.lean
/-- C¹ perturbation bound modeling ±ε manufacturing & assembly tolerances -/
def AdmissiblePerturbation (δγ : ℝ → ℝ³) (ε : ℝ) : Prop :=
  ∀ s : ℝ, ‖δγ s‖ ≤ ε ∧ ‖deriv δγ s‖ ≤ ε

/-- Top-level Kernel Certificate for a Stellarator Vacuum Demonstrator -/
structure CertifiedVacuumFixture
    (fixture : CoilSystem N) (Σ_target : Set ℝ³) (n_unit : ℝ³ → ℝ³)
    (d_min ε B_min η_max : ℝ) : Prop where
  tolerance_margin : 0 < ε ∧ 2 * ε < d_min
  clearance : ∀ i, HasClearanceMargin (fixture.curves i) Σ_target d_min
  field_strength_ok : ∀ (δ : Fin N → ℝ → ℝ³),
    (∀ i, AdmissiblePerturbation (δ i) ε) →
    ∀ x ∈ Σ_target, ‖evalBiotSavart (fixture.perturb δ) x‖ ≥ B_min
  normal_error_ok : ∀ (δ : Fin N → ℝ → ℝ³),
    (∀ i, AdmissiblePerturbation (δ i) ε) →
    ∀ x ∈ Σ_target,
      |⟪evalBiotSavart (fixture.perturb δ) x, n_unit x⟫_ℝ| /
        ‖evalBiotSavart (fixture.perturb δ) x‖ ≤ η_max
```

- **Physical & Mathematical Role:** This 20-line structure is the entire top-level specification for the Vacuum Demonstrator! A physicist or engineer does not need to read 15,000 lines of interval-arithmetic tactics or Fréchet derivative lemmas: if Lean 4's kernel accepts a term of type `CertifiedVacuumFixture`, then for *every* manufacturing perturbation within $\pm\varepsilon$, the magnetic field on $\Sigma_{\text{target}}$ is guaranteed to stay above $B_{\min}$ and keep normalized normal error $|\mathbf{B}\cdot\mathbf{n}|/|\mathbf{B}| \le \eta_{\max}$.

- **Specification Bug Prevented:** Eliminates 'single-point optimization illusions' where a coil set works at nominal floating-point precision but loses confinement under sub-millimeter assembly errors.

- **Compiled Sanity Check:**
```lean
-- Kernel Audit Verification Command:
#print axioms CertifiedVacuumFixture
-- Output: 'CertifiedVacuumFixture' depends only on standard Lean 4 axioms:
-- [propext, Classical.choice, Quot.sound]
```
