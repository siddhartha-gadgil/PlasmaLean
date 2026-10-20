/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CanonicalMomentum
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Guiding-centre Noether theorem in a vacuum Boozer-coordinate model (rung M4)

**This is a reduced MODEL, not a theorem about the Lorentz force.** The state is
`(ψ, θ, φ, ρ)`: toroidal flux `ψ` (divided by `2π`), Boozer poloidal and toroidal angles `θ, φ`,
and parallel gyroradius `ρ = ρ_∥ = m v_∥/(qB)`. The field enters through its strength
`B(ψ, θ, φ)`, the constant covariant toroidal component `G` (vacuum: `I = K = 0`), and the
poloidal flux `ψ_p(ψ)` with rotational transform `ι = dψ_p/dψ`. The magnetic moment `μ` is a
constant. The equations of motion are the Euler–Lagrange equations of Littlejohn's
guiding-centre phase-space Lagrangian written in Boozer variables (White & Boozer, Phys.
Fluids 1982; White, *The Theory of Toroidally Confined Plasmas*, ch. 3; R. G. Littlejohn,
J. Plasma Phys. 29 (1983) 111):

    L = q ψ θ̇ + q (G ρ − ψ_p(ψ)) φ̇ − H,     H = q² ρ² B²/(2m) + μ B,

    ψ̇ = −(mμ + q²ρ²B) ∂_θB/(mq)
    θ̇ = (μ/q + qρ²B/m) ∂_ψB + qρB² ι/(Gm)
    φ̇ = qρB²/(Gm)
    ρ̇ = −(mμ + q²ρ²B)(∂_φB + ι ∂_θB)/(Gmq).

The derivation of this system from the Newton–Lorentz equations (guiding-centre asymptotics,
validity of the Boozer chart, `μ` conservation) is **not formalized**. The Euler–Lagrange form,
energy conservation and the momentum identity were checked symbolically (sympy, generic `B` and
`ψ_p`). The `(ψ, θ)` chart is singular on the magnetic axis, so `B` is only required to be
differentiable on `{ψ > 0}`, and orbits are required to stay there. `BoozerGCOrbit` asks for
the equations at all times (used for exact-QS all-time trapping); `BoozerGCOrbitOn … T` asks
for them only on `[0, T]` (used for all finite-time results, so orbits that later reach the
axis or leave the region are covered).
Orbits are supplied, not constructed.

**Helicity convention.** For a symmetry direction `ξ = N ∂_θ + M ∂_φ`, quasisymmetry means
`ξB = 0`, i.e. `B = B(ψ, Mθ − Nφ)`. Quasi-axisymmetry (QA) is `(N, M) = (0, 1)`; tokamak
axisymmetry is the same. The helical momentum is `P = q (N ψ − M ψ_p(ψ) + M G ρ)`.

Results:

* `boozerEnergy_conserved`: `H` is constant along every orbit;
* `helicalMomentum_hasDerivAt`: `dP/dt = −(q²ρ²B/m + μ) · ξB` (exact identity);
* `helicalMomentum_conserved`: exact quasisymmetry `ξB ≡ 0` gives exact conservation of `P`;
* `helicalMomentum_drift_le`: `|P(t) − P(0)| ≤ (2H/B_min) ε t` while `|ξB| ≤ ε`, `B ≥ B_min`;
* `rho_deviation_passing`: pitch-set bound on `|ρ(t) − ρ(0)|` for passing particles;
* `boozerGC_trapped_until`: finite-time confinement `ψ ≤ c'` on `[0, T]` from the gap
  `|MG| Δρ + (2H/(|q| B_min)) ε T ≤ ι_min (c' − ψ(0))`; `boozerGC_trapped_until_time` gives
  the explicit `T(ε) ∝ 1/ε`;
* `boozerGC_trapped`: exact quasisymmetry gives confinement for all `t ≥ 0`;
* sanity: `constField` (constant `B`), its explicit orbit `constField_orbit` (non-vacuity),
  `constField_psi_const`, and `symmetryDefect_zero_of_const`.

The confinement time is linear in `1/ε` because the symmetry-breaking forcing is treated as
worst-case and constant-sign; no averaging of the oscillating defect is used.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Kinetic

/-- The linear form `(x, y, z) ↦ a x + b y + c z` on `ℝ × ℝ × ℝ` (a gradient). -/
@[expose] def gradCLM (a b c : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    b • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
    c • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Evaluation of `gradCLM`. -/
@[simp] theorem gradCLM_apply (a b c : ℝ) (p : ℝ × ℝ × ℝ) :
    gradCLM a b c p = a * p.1 + b * p.2.1 + c * p.2.2 := by
  simp [gradCLM]

/-- Vacuum Boozer-coordinate field data: field strength `B(ψ, θ, φ)` with its partial
derivatives (on the chart domain `ψ > 0`), poloidal flux `ψ_p` with `ψ_p' = ι`, and the constant
covariant toroidal component `G` (vacuum: `I = 0`). -/
structure BoozerField where
  /-- Field strength `|B|` as a function of `(ψ, θ, φ)`. -/
  B : ℝ → ℝ → ℝ → ℝ
  /-- `∂B/∂ψ`. -/
  Bψ : ℝ → ℝ → ℝ → ℝ
  /-- `∂B/∂θ`. -/
  Bθ : ℝ → ℝ → ℝ → ℝ
  /-- `∂B/∂φ`. -/
  Bφ : ℝ → ℝ → ℝ → ℝ
  /-- Poloidal flux (divided by `2π`) as a function of `ψ`. -/
  ψp : ℝ → ℝ
  /-- Rotational transform `ι = dψ_p/dψ`. -/
  ι : ℝ → ℝ
  /-- Covariant toroidal component (`B = G ∇φ` in vacuum Boozer form). -/
  G : ℝ
  /-- `B` is differentiable on the chart domain `ψ > 0` with the stated partials. -/
  hasFDerivAt_B : ∀ p : ℝ × ℝ × ℝ, 0 < p.1 →
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => B p.1 p.2.1 p.2.2)
      (gradCLM (Bψ p.1 p.2.1 p.2.2) (Bθ p.1 p.2.1 p.2.2) (Bφ p.1 p.2.1 p.2.2)) p
  /-- `ψ_p' = ι` on `ψ > 0`. -/
  hasDerivAt_ψp : ∀ x, 0 < x → HasDerivAt ψp (ι x) x

/-- Evaluate a function of the Boozer coordinates along a trajectory. -/
@[expose] def along (f : ℝ → ℝ → ℝ → ℝ) (ψ θ φ : ℝ → ℝ) (t : ℝ) : ℝ := f (ψ t) (θ t) (φ t)

/-- The vacuum Boozer guiding-centre equations of motion (standard model; see the module
docstring), as `HasDerivAt` hypotheses on a supplied trajectory that stays in `ψ > 0`. -/
structure BoozerGCOrbit (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) : Prop where
  /-- The orbit stays in the chart domain. -/
  pos : ∀ t, 0 < ψ t
  /-- Radial (flux) equation. -/
  dψ : ∀ t, HasDerivAt ψ
    (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) * along F.Bθ ψ θ φ t / (m * q)) t
  /-- Poloidal angle equation. -/
  dθ : ∀ t, HasDerivAt θ
    ((μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) * along F.Bψ ψ θ φ t +
      q * ρ t * along F.B ψ θ φ t ^ 2 * F.ι (ψ t) / (F.G * m)) t
  /-- Toroidal angle equation. -/
  dφ : ∀ t, HasDerivAt φ (q * ρ t * along F.B ψ θ φ t ^ 2 / (F.G * m)) t
  /-- Parallel gyroradius equation. -/
  dρ : ∀ t, HasDerivAt ρ
    (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) *
      (along F.Bφ ψ θ φ t + F.ι (ψ t) * along F.Bθ ψ θ φ t) / (F.G * m * q)) t

/-- The same equations required only on the time interval `[0, T]` (the trajectory stays in
`ψ > 0` there). `HasDerivAt` at the endpoints means the solution exists on a neighbourhood of
`[0, T]`. Nothing is assumed about the orbit after `T` (it may hit the axis or leave). -/
structure BoozerGCOrbitOn (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (T : ℝ) : Prop where
  /-- The orbit stays in the chart domain on `[0, T]`. -/
  pos : ∀ t ∈ Set.Icc 0 T, 0 < ψ t
  /-- Radial (flux) equation. -/
  dψ : ∀ t ∈ Set.Icc 0 T, HasDerivAt ψ
    (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) * along F.Bθ ψ θ φ t / (m * q)) t
  /-- Poloidal angle equation. -/
  dθ : ∀ t ∈ Set.Icc 0 T, HasDerivAt θ
    ((μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) * along F.Bψ ψ θ φ t +
      q * ρ t * along F.B ψ θ φ t ^ 2 * F.ι (ψ t) / (F.G * m)) t
  /-- Toroidal angle equation. -/
  dφ : ∀ t ∈ Set.Icc 0 T, HasDerivAt φ (q * ρ t * along F.B ψ θ φ t ^ 2 / (F.G * m)) t
  /-- Parallel gyroradius equation. -/
  dρ : ∀ t ∈ Set.Icc 0 T, HasDerivAt ρ
    (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) *
      (along F.Bφ ψ θ φ t + F.ι (ψ t) * along F.Bθ ψ θ φ t) / (F.G * m * q)) t

variable {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- Chain rule for the field strength along an orbit. -/
theorem BoozerGCOrbit.hasDerivAt_B (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (t : ℝ) :
    HasDerivAt (along F.B ψ θ φ)
      (along F.Bψ ψ θ φ t *
          (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) * along F.Bθ ψ θ φ t / (m * q)) +
        along F.Bθ ψ θ φ t *
          ((μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) * along F.Bψ ψ θ φ t +
            q * ρ t * along F.B ψ θ φ t ^ 2 * F.ι (ψ t) / (F.G * m)) +
        along F.Bφ ψ θ φ t * (q * ρ t * along F.B ψ θ φ t ^ 2 / (F.G * m))) t := by
  have hc := (h.dψ t).prodMk ((h.dθ t).prodMk (h.dφ t))
  have := (F.hasFDerivAt_B (ψ t, θ t, φ t) (h.pos t)).comp_hasDerivAt t hc
  simp only [Function.comp_def, gradCLM_apply] at this
  exact this

/-- Field strength along an orbit is continuous. -/
theorem BoozerGCOrbit.continuous_B (h : BoozerGCOrbit F m q μ ψ θ φ ρ) :
    Continuous (along F.B ψ θ φ) :=
  continuous_iff_continuousAt.mpr fun t => (h.hasDerivAt_B t).continuousAt

/-- The flux coordinate along an orbit is continuous. -/
theorem BoozerGCOrbit.continuous_ψ (h : BoozerGCOrbit F m q μ ψ θ φ ρ) : Continuous ψ :=
  continuous_iff_continuousAt.mpr fun t => (h.dψ t).continuousAt

/-- The parallel gyroradius along an orbit is continuous. -/
theorem BoozerGCOrbit.continuous_ρ (h : BoozerGCOrbit F m q μ ψ θ φ ρ) : Continuous ρ :=
  continuous_iff_continuousAt.mpr fun t => (h.dρ t).continuousAt

/-- An all-time orbit is an orbit on every interval `[0, T]`. -/
theorem BoozerGCOrbit.on (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (T : ℝ) :
    BoozerGCOrbitOn F m q μ ψ θ φ ρ T where
  pos t _ := h.pos t
  dψ t _ := h.dψ t
  dθ t _ := h.dθ t
  dφ t _ := h.dφ t
  dρ t _ := h.dρ t

/-- An orbit on `[0, T]` is an orbit on every `[0, t]` with `t ≤ T`. -/
theorem BoozerGCOrbitOn.mono {T t : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (htT : t ≤ T) :
    BoozerGCOrbitOn F m q μ ψ θ φ ρ t where
  pos s hs := h.pos s ⟨hs.1, hs.2.trans htT⟩
  dψ s hs := h.dψ s ⟨hs.1, hs.2.trans htT⟩
  dθ s hs := h.dθ s ⟨hs.1, hs.2.trans htT⟩
  dφ s hs := h.dφ s ⟨hs.1, hs.2.trans htT⟩
  dρ s hs := h.dρ s ⟨hs.1, hs.2.trans htT⟩

/-- Chain rule for the field strength along an orbit on `[0, T]`. -/
theorem BoozerGCOrbitOn.hasDerivAt_B {T : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    HasDerivAt (along F.B ψ θ φ)
      (along F.Bψ ψ θ φ t *
          (-(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) * along F.Bθ ψ θ φ t / (m * q)) +
        along F.Bθ ψ θ φ t *
          ((μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) * along F.Bψ ψ θ φ t +
            q * ρ t * along F.B ψ θ φ t ^ 2 * F.ι (ψ t) / (F.G * m)) +
        along F.Bφ ψ θ φ t * (q * ρ t * along F.B ψ θ φ t ^ 2 / (F.G * m))) t := by
  have hc := (h.dψ t ht).prodMk ((h.dθ t ht).prodMk (h.dφ t ht))
  have := (F.hasFDerivAt_B (ψ t, θ t, φ t) (h.pos t ht)).comp_hasDerivAt t hc
  simp only [Function.comp_def, gradCLM_apply] at this
  exact this

/-! ## Energy -/

/-- Guiding-centre energy `H = q²ρ²B²/(2m) + μB = ½ m v_∥² + μ B` along a trajectory. -/
@[expose] def boozerEnergy (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t ^ 2 / (2 * m) + μ * along F.B ψ θ φ t

/-- Parallel velocity `v_∥ = q ρ B/m` along a trajectory. -/
@[expose] def parallelVelocity (F : BoozerField) (m q : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q * ρ t * along F.B ψ θ φ t / m

/-- `H = ½ m v_∥² + μ B`. -/
theorem boozerEnergy_eq_parallel (hm : m ≠ 0) (t : ℝ) :
    boozerEnergy F m q μ ψ θ φ ρ t =
      m * parallelVelocity F m q ψ θ φ ρ t ^ 2 / 2 + μ * along F.B ψ θ φ t := by
  unfold boozerEnergy parallelVelocity
  field_simp

/-- The energy has zero time derivative along every orbit. -/
theorem boozerEnergy_hasDerivAt (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0)
    (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (t : ℝ) :
    HasDerivAt (boozerEnergy F m q μ ψ θ φ ρ) 0 t := by
  have hB := h.hasDerivAt_B t
  have hρ := h.dρ t
  have := ((((hρ.mul hρ).const_mul (q ^ 2)).mul (hB.mul hB)).div_const (2 * m)).add
    (hB.const_mul μ)
  convert this using 1
  · funext s; simp only [boozerEnergy, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [Pi.mul_apply]
    field_simp
    ring

/-- **Energy conservation** in the Boozer guiding-centre model. -/
theorem boozerEnergy_conserved (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0)
    (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (s t : ℝ) :
    boozerEnergy F m q μ ψ θ φ ρ s = boozerEnergy F m q μ ψ θ φ ρ t :=
  is_const_of_deriv_eq_zero
    (fun r => (boozerEnergy_hasDerivAt hm hq hG h r).differentiableAt)
    (fun r => (boozerEnergy_hasDerivAt hm hq hG h r).deriv) s t

/-- The energy has zero time derivative on `[0, T]` along an orbit on `[0, T]`. -/
theorem boozerEnergy_hasDerivAt_on (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ht : t ∈ Set.Icc 0 T) :
    HasDerivAt (boozerEnergy F m q μ ψ θ φ ρ) 0 t := by
  have hB := h.hasDerivAt_B ht
  have hρ := h.dρ t ht
  have := ((((hρ.mul hρ).const_mul (q ^ 2)).mul (hB.mul hB)).div_const (2 * m)).add
    (hB.const_mul μ)
  convert this using 1
  · funext s; simp only [boozerEnergy, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [Pi.mul_apply]
    field_simp
    ring

/-- **Energy conservation on `[0, T]`**: `H(t) = H(0)` for `t ∈ [0, T]`. -/
theorem boozerEnergy_eq_on (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ht : t ∈ Set.Icc 0 T) :
    boozerEnergy F m q μ ψ θ φ ρ t = boozerEnergy F m q μ ψ θ φ ρ 0 := by
  have := invariant_drift (K' := fun _ => 0) (ε := 0)
    (fun s hs => boozerEnergy_hasDerivAt_on hm hq hG h hs) (fun _ _ => by simp) ht
  rw [zero_mul] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-! ## Helical momentum -/

/-- Symmetry-breaking derivative `ξB = N ∂_θB + M ∂_φB` for `ξ = N ∂_θ + M ∂_φ`. -/
@[expose] def symmetryDefect (F : BoozerField) (N M : ℝ) (x θ φ : ℝ) : ℝ :=
  N * F.Bθ x θ φ + M * F.Bφ x θ φ

/-- Helical (canonical) momentum `P = q (N ψ − M ψ_p(ψ) + M G ρ)` along a trajectory. -/
@[expose] def helicalMomentum (F : BoozerField) (q N M : ℝ) (ψ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q * (N * ψ t - M * F.ψp (ψ t) + M * F.G * ρ t)

/-- **Momentum identity**: `dP/dt = −(q²ρ²B/m + μ) · ξB`. -/
theorem helicalMomentum_hasDerivAt (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) (N M : ℝ)
    (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (t : ℝ) :
    HasDerivAt (helicalMomentum F q N M ψ ρ)
      (-(q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t / m + μ) *
        symmetryDefect F N M (ψ t) (θ t) (φ t)) t := by
  have hψ := h.dψ t
  have hp := (F.hasDerivAt_ψp (ψ t) (h.pos t)).comp t hψ
  have := (((hψ.const_mul N).sub (hp.const_mul M)).add ((h.dρ t).const_mul (M * F.G))).const_mul q
  convert this using 1
  · funext s; simp only [helicalMomentum, Function.comp_def, Pi.add_apply, Pi.sub_apply]
  · simp only [symmetryDefect, along]
    field_simp
    ring

/-- Momentum identity on `[0, T]` for an orbit on `[0, T]`. -/
theorem helicalMomentum_hasDerivAt_on (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) (N M : ℝ)
    {T t : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ht : t ∈ Set.Icc 0 T) :
    HasDerivAt (helicalMomentum F q N M ψ ρ)
      (-(q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t / m + μ) *
        symmetryDefect F N M (ψ t) (θ t) (φ t)) t := by
  have hψ := h.dψ t ht
  have hp := (F.hasDerivAt_ψp (ψ t) (h.pos t ht)).comp t hψ
  have := (((hψ.const_mul N).sub (hp.const_mul M)).add
    ((h.dρ t ht).const_mul (M * F.G))).const_mul q
  convert this using 1
  · funext s; simp only [helicalMomentum, Function.comp_def, Pi.add_apply, Pi.sub_apply]
  · simp only [symmetryDefect, along]
    field_simp
    ring

/-- **Exact quasisymmetry** (`ξB ≡ 0` on `ψ > 0`) gives exact conservation of `P`. -/
theorem helicalMomentum_conserved (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {N M : ℝ}
    (hQS : ∀ x θ φ, 0 < x → symmetryDefect F N M x θ φ = 0)
    (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (s t : ℝ) :
    helicalMomentum F q N M ψ ρ s = helicalMomentum F q N M ψ ρ t := by
  have hd (r : ℝ) : HasDerivAt (helicalMomentum F q N M ψ ρ) 0 r := by
    have := helicalMomentum_hasDerivAt hm hq hG N M h r
    rwa [hQS _ _ _ (h.pos r), mul_zero] at this
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s t

/-- Rate bound: for `m > 0`, `μ ≥ 0`, `B ≥ B_min > 0`,
`0 ≤ q²ρ²B/m + μ ≤ 2H/B_min`. -/
theorem momentum_rate_le {m q μ ρ B Bmin : ℝ} (hm : 0 < m) (hμ : 0 ≤ μ) (hBmin : 0 < Bmin)
    (hB : Bmin ≤ B) :
    0 ≤ q ^ 2 * ρ ^ 2 * B / m + μ ∧
      q ^ 2 * ρ ^ 2 * B / m + μ ≤ 2 * (q ^ 2 * ρ ^ 2 * B ^ 2 / (2 * m) + μ * B) / Bmin := by
  have hB0 : 0 < B := lt_of_lt_of_le hBmin hB
  have hk : 0 ≤ q ^ 2 * ρ ^ 2 * B / m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [le_div_iff₀ hBmin]
  have e : 2 * (q ^ 2 * ρ ^ 2 * B ^ 2 / (2 * m) + μ * B) =
      (q ^ 2 * ρ ^ 2 * B / m + μ) * B + μ * B := by field_simp; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ q ^ 2 * ρ ^ 2 * B / m + μ),
    mul_nonneg hμ hB0.le]

/-- **Momentum drift**: if on `[0, t]` the orbit sees `B ≥ B_min > 0` and `|ξB| ≤ ε`, then
`|P(t) − P(0)| ≤ (2 H(0)/B_min) ε t`. Only an orbit on `[0, t]` is needed. -/
theorem helicalMomentum_drift_le (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M Bmin ε t : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ t) (hBmin : 0 < Bmin) (ht : 0 ≤ t)
    (hB : ∀ s ∈ Set.Icc 0 t, Bmin ≤ along F.B ψ θ φ s)
    (hξ : ∀ s ∈ Set.Icc 0 t, |symmetryDefect F N M (ψ s) (θ s) (φ s)| ≤ ε) :
    |helicalMomentum F q N M ψ ρ t - helicalMomentum F q N M ψ ρ 0| ≤
      2 * boozerEnergy F m q μ ψ θ φ ρ 0 / Bmin * ε * t := by
  refine invariant_drift (fun s hs => helicalMomentum_hasDerivAt_on hm.ne' hq hG N M h hs)
    (fun s hs => ?_) ⟨ht, le_rfl⟩
  obtain ⟨h0, h1⟩ := momentum_rate_le (q := q) (ρ := ρ s) hm hμ hBmin (hB s hs)
  have hE : boozerEnergy F m q μ ψ θ φ ρ s = boozerEnergy F m q μ ψ θ φ ρ 0 :=
    boozerEnergy_eq_on hm.ne' hq hG h hs
  unfold boozerEnergy at hE
  rw [hE] at h1
  rw [abs_mul, abs_neg, abs_of_nonneg h0]
  exact mul_le_mul h1 (hξ s hs) (abs_nonneg _) (h0.trans h1)

/-! ## Passing-particle bound on the parallel-gyroradius excursion -/

/-- Algebra: if `u, u₀` have the same sign, `|u|, |u₀| ≥ w > 0` and `|u² − u₀²| ≤ D`, then
`|u − u₀| ≤ D/(2w)`. -/
theorem abs_sub_le_of_sq {u u₀ w D : ℝ} (hw : 0 < w) (hu : w ^ 2 ≤ u ^ 2) (hu₀ : w ^ 2 ≤ u₀ ^ 2)
    (hs : 0 < u * u₀) (hD : |u ^ 2 - u₀ ^ 2| ≤ D) : |u - u₀| ≤ D / (2 * w) := by
  have a1 : w ≤ |u| := by have := sq_le_sq.mp hu; rwa [abs_of_pos hw] at this
  have a2 : w ≤ |u₀| := by have := sq_le_sq.mp hu₀; rwa [abs_of_pos hw] at this
  have hsum : |u + u₀| = |u| + |u₀| := by
    rw [abs_add_eq_add_abs_iff]
    rcases lt_or_gt_of_ne (show u₀ ≠ 0 by rintro rfl; simp at hs) with h | h
    · right; constructor <;> nlinarith
    · left; constructor <;> nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc |u - u₀| * (2 * w) ≤ |u - u₀| * |u + u₀| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); rw [hsum]; linarith
    _ = |u ^ 2 - u₀ ^ 2| := by rw [← abs_mul]; ring_nf
    _ ≤ D := hD

/-- Algebra: excursion of `ρ = m u/(qB)` from excursions of `u` and `B`. -/
theorem abs_rho_sub_le {m q u u₀ B B₀ Bmin Bmax X U : ℝ} (hm : 0 < m) (hq : q ≠ 0)
    (hBmin : 0 < Bmin) (hB : Bmin ≤ B ∧ B ≤ Bmax) (hB₀ : Bmin ≤ B₀ ∧ B₀ ≤ Bmax)
    (hX : |u - u₀| ≤ X) (hU : |u₀| ≤ U) :
    |m * u / (q * B) - m * u₀ / (q * B₀)| ≤
      m / |q| * (X / Bmin + U * (Bmax - Bmin) / Bmin ^ 2) := by
  have hBp : 0 < B := lt_of_lt_of_le hBmin hB.1
  have hB₀p : 0 < B₀ := lt_of_lt_of_le hBmin hB₀.1
  have e : m * u / (q * B) - m * u₀ / (q * B₀) =
      m / q * ((u - u₀) / B + u₀ * (B₀ - B) / (B * B₀)) := by field_simp; ring
  rw [e, abs_mul, abs_div, abs_of_pos hm]
  gcongr
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hX
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hU
  calc |(u - u₀) / B + u₀ * (B₀ - B) / (B * B₀)|
      ≤ |(u - u₀) / B| + |u₀ * (B₀ - B) / (B * B₀)| := abs_add_le _ _
    _ ≤ X / Bmin + U * (Bmax - Bmin) / Bmin ^ 2 := by
      gcongr
      · rw [abs_div, abs_of_pos hBp]
        exact div_le_div₀ hX0 hX hBmin hB.1
      · rw [abs_div, abs_mul, abs_of_pos (mul_pos hBp hB₀p), sq]
        have hd : |B₀ - B| ≤ Bmax - Bmin := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        exact div_le_div₀ (by nlinarith) (mul_le_mul hU hd (abs_nonneg _) hU0)
          (by positivity) (mul_le_mul hB.1 hB₀.1 hBmin.le hBp.le)

/-- **Passing-particle excursion bound.** Let `Q = 2H(0)/m` (the squared speed). If on
`[0, t]` the orbit sees `B ∈ [B_min, B_max]`, and initially `v_∥(0)² ≥ w² + Q (B_max − B_min)/B_min`
with `w > 0` (a passing pitch), and `Q ≤ U²`, then `v_∥` keeps its sign and
`|ρ(t) − ρ(0)| ≤ (m/|q|) ((B_max − B_min)/B_min²) (Q/(2w) + U)`. -/
theorem rho_deviation_passing (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {Bmin Bmax w U t : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ t) (hBmin : 0 < Bmin)
    (hw : 0 < w)
    (ht : 0 ≤ t)
    (hB : ∀ s ∈ Set.Icc 0 t, Bmin ≤ along F.B ψ θ φ s ∧ along F.B ψ θ φ s ≤ Bmax)
    (hpass : w ^ 2 + 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / m * (Bmax - Bmin) / Bmin ≤
      parallelVelocity F m q ψ θ φ ρ 0 ^ 2)
    (hU : 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / m ≤ U ^ 2) (hU0 : 0 ≤ U) :
    |ρ t - ρ 0| ≤ m / |q| * ((Bmax - Bmin) / Bmin ^ 2) *
      (2 * boozerEnergy F m q μ ψ θ φ ρ 0 / m / (2 * w) + U) := by
  set E := boozerEnergy F m q μ ψ θ φ ρ 0 with hEdef
  set u := parallelVelocity F m q ψ θ φ ρ with hudef
  set Bt := along F.B ψ θ φ with hBt
  have hB0 := hB 0 ⟨le_rfl, ht⟩
  have hBpos : ∀ s ∈ Set.Icc 0 t, 0 < Bt s := fun s hs => lt_of_lt_of_le hBmin (hB s hs).1
  -- energy in terms of `u`
  have h0t : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht⟩
  have hEs : ∀ s ∈ Set.Icc 0 t, m * u s ^ 2 / 2 + μ * Bt s = E := fun s hs => by
    rw [hudef, hBt, ← boozerEnergy_eq_parallel hm.ne', hEdef]
    exact boozerEnergy_eq_on hm.ne' hq hG h hs
  have hμB : μ * Bt 0 ≤ E := by have := hEs 0 h0t; nlinarith [sq_nonneg (u 0)]
  have hμle : μ ≤ E / Bmin := by
    rw [le_div_iff₀ hBmin]
    nlinarith [mul_le_mul_of_nonneg_left hB0.1 hμ]
  have hE0 : 0 ≤ E := le_trans (mul_nonneg hμ (hBpos 0 ⟨le_rfl, ht⟩).le) hμB
  -- change of `u²`
  have hdiff : ∀ s ∈ Set.Icc 0 t, |u s ^ 2 - u 0 ^ 2| ≤ 2 * E / m * (Bmax - Bmin) / Bmin := by
    intro s hs
    have e : u s ^ 2 - u 0 ^ 2 = 2 * μ / m * (Bt 0 - Bt s) := by
      have h1 := hEs s hs; have h2 := hEs 0 h0t; field_simp; linarith
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have hd : |Bt 0 - Bt s| ≤ Bmax - Bmin :=
      abs_sub_le_iff.mpr ⟨by linarith [(hB s hs).1, hB0.2], by linarith [(hB s hs).2, hB0.1]⟩
    have hd0 : 0 ≤ Bmax - Bmin := (abs_nonneg _).trans hd
    calc 2 * μ / m * |Bt 0 - Bt s| ≤ 2 * (E / Bmin) / m * (Bmax - Bmin) := by
          gcongr
      _ = 2 * E / m * (Bmax - Bmin) / Bmin := by field_simp
  have hlow : ∀ s ∈ Set.Icc 0 t, w ^ 2 ≤ u s ^ 2 := by
    intro s hs
    have := (abs_le.mp (hdiff s hs)).1
    linarith
  -- sign preservation by the intermediate value theorem
  have hucont : ContinuousOn u (Set.Icc 0 t) := by
    have hρc : ContinuousOn ρ (Set.Icc 0 t) :=
      fun s hs => (h.dρ s hs).continuousAt.continuousWithinAt
    have hBc : ContinuousOn (along F.B ψ θ φ) (Set.Icc 0 t) :=
      fun s hs => (h.hasDerivAt_B hs).continuousAt.continuousWithinAt
    rw [hudef]; unfold parallelVelocity
    exact ((continuousOn_const.mul hρc).mul hBc).div_const m
  have hsign : ∀ s ∈ Set.Icc 0 t, 0 < u s * u 0 := by
    intro s hs
    by_contra hneg
    push Not at hneg
    have hg : ContinuousOn (fun r => u r * u 0) (Set.Icc 0 s) :=
      (hucont.mono (Set.Icc_subset_Icc le_rfl hs.2)).mul continuousOn_const
    have h00 : 0 < u 0 * u 0 := by nlinarith [hlow 0 ⟨le_rfl, ht⟩]
    obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc' hs.1 hg
      (show (0 : ℝ) ∈ Set.Icc (u s * u 0) (u 0 * u 0) from ⟨hneg, h00.le⟩)
    have hu0 : u 0 ≠ 0 := by rintro h0; simp [h0] at h00
    have huσ : u σ = 0 := by
      rcases mul_eq_zero.mp hσ0 with h' | h'
      · exact h'
      · exact absurd h' hu0
    have := hlow σ ⟨hσ.1, hσ.2.trans hs.2⟩
    rw [huσ] at this
    nlinarith
  have hts : t ∈ Set.Icc 0 t := ⟨ht, le_rfl⟩
  have hX := abs_sub_le_of_sq hw (hlow t hts) (hlow 0 ⟨le_rfl, ht⟩) (hsign t hts) (hdiff t hts)
  have hu0U : |u 0| ≤ U := by
    have : u 0 ^ 2 ≤ U ^ 2 := by
      have := hEs 0 h0t
      have : u 0 ^ 2 ≤ 2 * E / m := by
        rw [le_div_iff₀ hm]; nlinarith [mul_nonneg hμ (hBpos 0 ⟨le_rfl, ht⟩).le]
      linarith
    exact abs_le_of_sq_le_sq' this hU0 |> abs_le.mpr
  have hρ : ∀ s ∈ Set.Icc 0 t, ρ s = m * u s / (q * Bt s) := fun s hs => by
    have := (hBpos s hs).ne'
    simp only [hudef, hBt, parallelVelocity] at this ⊢
    field_simp
  rw [hρ t hts, hρ 0 ⟨le_rfl, ht⟩]
  have := abs_rho_sub_le hm hq hBmin (hB t hts) hB0 hX hu0U
  calc _ ≤ _ := this
    _ = _ := by field_simp

/-! ## Finite-time and all-time confinement -/

/-- **Trapped until `T`** (guiding-centre analogue of `noether_orbit_trapped_until`).

Hypotheses on the region `R = {0 < ψ ≤ c}`: `B ≥ B_min > 0` and `|ξB| ≤ ε`; the twist
condition `ι_min (x − ψ(0)) ≤ |f(x) − f(ψ(0))|` for `f(x) = N x − M ψ_p(x)` and
`ψ(0) ≤ x ≤ c` (e.g. QA with `ι ≥ ι_min`); an orbit-width bound `|ρ(t) − ρ(0)| ≤ Δρ` valid
while the orbit has stayed in `R` (see `rho_deviation_passing`); and the gap
`|MG| Δρ + (2H(0)/(|q| B_min)) ε T ≤ ι_min (c' − ψ(0))` with `c' < c`.
Then `ψ(t) ≤ c'` for all `t ∈ [0, T]`. The orbit is only required to exist on `[0, T]`. -/
theorem boozerGC_trapped_until (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c c' ιmin Bmin ε Δρ T : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T)
    (hcc : c' < c) (hψ0 : ψ 0 ≤ c') (hBmin : 0 < Bmin) (hε : 0 ≤ ε) (hι : 0 < ιmin)
    (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ ε)
    (hmono : ∀ x, ψ 0 ≤ x → x ≤ c →
      ιmin * (x - ψ 0) ≤ |(N * x - M * F.ψp x) - (N * ψ 0 - M * F.ψp (ψ 0))|)
    (hΔρ : ∀ t ∈ Set.Icc 0 T, (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) → |ρ t - ρ 0| ≤ Δρ)
    (hgap : |M * F.G| * Δρ + 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / (|q| * Bmin) * ε * T ≤
      ιmin * (c' - ψ 0)) :
    ∀ t ∈ Set.Icc 0 T, ψ t ≤ c' := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hT)
  have hqp : 0 < |q| := abs_pos.mpr hq
  set E := boozerEnergy F m q μ ψ θ φ ρ 0 with hEdef
  have hE0 : 0 ≤ E := by
    have hB0 := hBlow _ (θ 0) (φ 0) (h.pos 0 ⟨le_rfl, hT⟩) (hψ0.trans hcc.le)
    have : 0 ≤ along F.B ψ θ φ 0 := hBmin.le.trans hB0
    rw [hEdef]; unfold boozerEnergy
    positivity
  have hrate : 0 ≤ 2 * E / (|q| * Bmin) * ε := by positivity
  -- extend `ψ` continuously from `[0, T]` to `ℝ` (clamping time) to use `trapped_until`
  set f : ℝ → ℝ := fun s => ψ (Set.projIcc 0 T hT s) with hfdef
  have hψc : ContinuousOn ψ (Set.Icc 0 T) :=
    fun s hs => (h.dψ s hs).continuousAt.continuousWithinAt
  have hfc : Continuous f := hψc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun s => Subtype.mem _)
  have hfeq : ∀ s ∈ Set.Icc 0 T, f s = ψ s := fun s hs => by
    simp only [hfdef, Set.projIcc_of_mem hT hs]
  have hf0 : f 0 = ψ 0 := hfeq 0 ⟨le_rfl, hT⟩
  intro t₀ ht₀
  rw [← hfeq t₀ ht₀]
  refine trapped_until hfc hcc (hf0 ▸ hψ0) (fun t ht hhist' => ?_) t₀ ht₀
  have hsub : ∀ s ∈ Set.Icc 0 t, s ∈ Set.Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hhist : ∀ s ∈ Set.Icc 0 t, ψ s ≤ c := fun s hs => by
    rw [← hfeq s (hsub s hs)]; exact hhist' s hs
  rw [hfeq t ht]
  rcases le_or_gt (ψ t) (ψ 0) with hle | hgt
  · linarith
  have hdrift := helicalMomentum_drift_le hm hq hG hμ (N := N) (M := M) (ε := ε)
    (h.mono ht.2) hBmin ht.1
    (fun s hs => hBlow _ _ _ (h.pos s (hsub s hs)) (hhist s hs))
    (fun s hs => hξ _ _ _ (h.pos s (hsub s hs)) (hhist s hs))
  have hρd := hΔρ t ht hhist
  have hm1 := hmono (ψ t) hgt.le (hhist t ⟨ht.1, le_rfl⟩)
  -- `q (Δf) = ΔP − q M G Δρ`
  have e : q * ((N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))) =
      (helicalMomentum F q N M ψ ρ t - helicalMomentum F q N M ψ ρ 0) -
        q * (M * F.G) * (ρ t - ρ 0) := by
    unfold helicalMomentum; ring
  have hqf : |q| * |(N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))| ≤
      2 * E / Bmin * ε * t + |q| * (|M * F.G| * Δρ) := by
    rw [← abs_mul, e]
    refine (abs_sub _ _).trans (add_le_add hdrift ?_)
    rw [abs_mul, abs_mul, mul_assoc]
    gcongr
  have hf : |(N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))| ≤
      2 * E / (|q| * Bmin) * ε * t + |M * F.G| * Δρ := by
    have e2 : 2 * E / (|q| * Bmin) * ε * t + |M * F.G| * Δρ =
        (2 * E / Bmin * ε * t + |q| * (|M * F.G| * Δρ)) / |q| := by field_simp
    rw [e2, le_div_iff₀ hqp]; linarith
  have htT : 2 * E / (|q| * Bmin) * ε * t ≤ 2 * E / (|q| * Bmin) * ε * T :=
    mul_le_mul_of_nonneg_left ht.2 hrate
  have : ιmin * (ψ t - ψ 0) ≤ ιmin * (c' - ψ 0) := by linarith
  have := le_of_mul_le_mul_left this hι
  linarith

/-- **Explicit time `T(ε) ∝ 1/ε`.** With `ε > 0` and `H(0) > 0`, the orbit satisfies `ψ ≤ c'` on
`[0, T(ε)]` with
`T(ε) = (ι_min (c' − ψ(0)) − |MG| Δρ) |q| B_min/(2 H(0) ε)` (vacuous if the orbit-width margin
`ι_min (c' − ψ(0)) − |MG| Δρ` is negative, since then `T(ε) < 0`). -/
theorem boozerGC_trapped_until_time (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c c' ιmin Bmin ε Δρ : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ ((ιmin * (c' - ψ 0) - |M * F.G| * Δρ) * |q| * Bmin /
        (2 * boozerEnergy F m q μ ψ θ φ ρ 0 * ε)))
    (hcc : c' < c) (hψ0 : ψ 0 ≤ c') (hBmin : 0 < Bmin) (hε : 0 < ε) (hι : 0 < ιmin)
    (hE : 0 < boozerEnergy F m q μ ψ θ φ ρ 0)
    (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ ε)
    (hmono : ∀ x, ψ 0 ≤ x → x ≤ c →
      ιmin * (x - ψ 0) ≤ |(N * x - M * F.ψp x) - (N * ψ 0 - M * F.ψp (ψ 0))|)
    (hΔρ : ∀ t ∈ Set.Icc 0 ((ιmin * (c' - ψ 0) - |M * F.G| * Δρ) * |q| * Bmin /
        (2 * boozerEnergy F m q μ ψ θ φ ρ 0 * ε)),
      (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) → |ρ t - ρ 0| ≤ Δρ) :
    ∀ t ∈ Set.Icc 0 ((ιmin * (c' - ψ 0) - |M * F.G| * Δρ) * |q| * Bmin /
        (2 * boozerEnergy F m q μ ψ θ φ ρ 0 * ε)), ψ t ≤ c' := by
  have hqp : 0 < |q| := abs_pos.mpr hq
  refine boozerGC_trapped_until hm hq hG hμ h hcc hψ0 hBmin hε.le hι hBlow hξ hmono hΔρ ?_
  apply le_of_eq
  field_simp
  ring

/-- **Exact quasisymmetry: all-time confinement.** With `ξB ≡ 0` on the region, the gap
`|MG| Δρ ≤ ι_min (c' − ψ(0))` keeps `ψ ≤ c'` for every `t ≥ 0`. -/
theorem boozerGC_trapped (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c c' ιmin Bmin Δρ : ℝ} (h : BoozerGCOrbit F m q μ ψ θ φ ρ)
    (hcc : c' < c) (hψ0 : ψ 0 ≤ c') (hBmin : 0 < Bmin) (hι : 0 < ιmin)
    (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (hmono : ∀ x, ψ 0 ≤ x → x ≤ c →
      ιmin * (x - ψ 0) ≤ |(N * x - M * F.ψp x) - (N * ψ 0 - M * F.ψp (ψ 0))|)
    (hΔρ : ∀ t, 0 ≤ t → (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) → |ρ t - ρ 0| ≤ Δρ)
    (hgap : |M * F.G| * Δρ ≤ ιmin * (c' - ψ 0)) (t : ℝ) (ht : 0 ≤ t) : ψ t ≤ c' :=
  boozerGC_trapped_until hm hq hG hμ (ε := 0) (T := t) (h.on t) hcc hψ0 hBmin le_rfl hι hBlow
    (fun x θ φ hx hxc => by rw [hQS x θ φ hx hxc, abs_zero]) hmono
    (fun s hs hhist => hΔρ s hs.1 hhist) (by simpa using hgap)
    t ⟨ht, le_rfl⟩

/-! ## Sanity checks -/

/-- Degenerate model: constant field strength `B₀`, constant transform `ι₀`
(`ψ_p = ι₀ ψ`), covariant component `G`. -/
@[expose] def constField (B₀ ι₀ G : ℝ) : BoozerField where
  B _ _ _ := B₀
  Bψ _ _ _ := 0
  Bθ _ _ _ := 0
  Bφ _ _ _ := 0
  ψp x := ι₀ * x
  ι _ := ι₀
  G := G
  hasFDerivAt_B p _ := by
    simpa [gradCLM] using hasFDerivAt_const B₀ p
  hasDerivAt_ψp x _ := by simpa using (hasDerivAt_id x).const_mul ι₀

/-- A constant field is exactly symmetric in every helicity. -/
theorem symmetryDefect_zero_of_const (B₀ ι₀ G N M x θ φ : ℝ) :
    symmetryDefect (constField B₀ ι₀ G) N M x θ φ = 0 := by
  simp [symmetryDefect, constField]

/-- Non-vacuity: in the constant field, `ψ ≡ ψ₀ > 0`, `ρ ≡ ρ₀`, and uniformly rotating angles
`θ = θ₀ + ι₀ Ω t`, `φ = φ₀ + Ω t` with `Ω = q ρ₀ B₀²/(G m)` form an orbit. -/
theorem constField_orbit {B₀ ι₀ G m q μ ψ₀ θ₀ φ₀ ρ₀ : ℝ} (hψ₀ : 0 < ψ₀) :
    BoozerGCOrbit (constField B₀ ι₀ G) m q μ (fun _ => ψ₀)
      (fun t => θ₀ + ι₀ * (q * ρ₀ * B₀ ^ 2 / (G * m)) * t)
      (fun t => φ₀ + q * ρ₀ * B₀ ^ 2 / (G * m) * t) (fun _ => ρ₀) where
  pos _ := hψ₀
  dψ t := by simpa [constField, along] using hasDerivAt_const t ψ₀
  dθ t := by
    have := ((hasDerivAt_id t).const_mul (ι₀ * (q * ρ₀ * B₀ ^ 2 / (G * m)))).const_add θ₀
    convert this using 1
    · funext s; simp
    · simp [constField, along]; ring
  dφ t := by
    have := ((hasDerivAt_id t).const_mul (q * ρ₀ * B₀ ^ 2 / (G * m))).const_add φ₀
    convert this using 1
    · funext s; simp
    · simp [constField, along]
  dρ t := by simpa [constField, along] using hasDerivAt_const t ρ₀

/-- In a constant field, the flux coordinate of every orbit is constant (`ψ̇ = 0`). -/
theorem constField_psi_const {B₀ ι₀ G m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (h : BoozerGCOrbit (constField B₀ ι₀ G) m q μ ψ θ φ ρ) (s t : ℝ) : ψ s = ψ t := by
  have hd (r : ℝ) : HasDerivAt ψ 0 r := by
    simpa [constField, along] using h.dψ r
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s t

end PlasmaLean.Kinetic.Boozer
