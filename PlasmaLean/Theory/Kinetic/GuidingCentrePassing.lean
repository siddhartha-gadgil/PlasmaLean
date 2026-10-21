/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CurlProduct
public import PlasmaLean.Theory.Kinetic.GuidingCentreLittlejohn
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Passing guiding centres with `μ ≥ 0` are field lines of an energy-dependent field

For a `LittlejohnOrbit m q μ B X v` (static `B`, no electric field) the energy
`E = m v_∥²/2 + μ|B(X)|` is conserved (`energy_const`). If `v_∥` never vanishes (a *passing*
orbit) it has a constant sign `σ = ±1`, so `v_∥(t) = σ w(X(t))` with
`w(x) = √(2(E − μ|B(x)|)/m)`. Put
`ρ_{E,μ}(x) = σ (m/q) w(x)` (`rhoE`) and `B̃_{E,μ} = B + ∇×(ρ_{E,μ} b)` (`modFieldFn`).

**The identity** (pointwise along the orbit, proved here). By the curl product rule
(`curl_fderiv_smul`), `∇×(ρ b) = ρ ∇×b + ∇ρ × b`. Since `∇ρ = −σ μ ∇|B| / (q w)`,
`v_∥ ∇ρ × b = −(μ/q) ∇|B| × b = (μ/q) b × ∇|B|` (using `σ² = 1`), and `ρ(X) = m v_∥/q`. Hence
`v_∥ B̃_{E,μ}(X) = v_∥ (B + (m v_∥/q) ∇×b) + (μ/q) b × ∇|B| = v_∥ B* + (μ/q) b × ∇|B|`,
which is exactly `B*_∥ Ẋ` in the Littlejohn equation: the grad-B drift `(μ/q) b × ∇|B|` is
absorbed into the `∇ρ × b` part of `∇×(ρ b)`. Therefore
`dX/dt = (v_∥/B*_∥) B̃_{E,μ}(X)` (`littlejohn_passing_isFieldLine`). The sign condition
`μ ≥ 0` is not needed for the identity; it only matters for which particles are passing.
(The identity was also checked symbolically with sympy for general `B`.)

Results.

* `rhoE`, `modFieldFn`, `passSign`.
* `modFieldFn_eq`: `B̃ = B + ρ ∇×b + ∇ρ × b` (curl product rule).
* `hasGradientAt_rhoE`: `∇ρ_{E,μ} = −σ μ/(q w) ∇|B|` where `w > 0`.
* `passing_velocity_identity`: the vector identity above, for abstract `ρ(x)`, `∇ρ(x)`.
* `vpar_eq_sign_sqrt`: `v_∥(t) = σ √(2(E − μ|B(X t)|)/m)` for passing orbits.
* `littlejohn_passing_isFieldLine`: `dX/dt = (v_∥/B*_∥) B̃_{E,μ}(X)`.
* `modFieldFn_divFree`: `∇·B̃_{E,μ} = 0` when `∇·B = 0` and `ρ b` is `C²`
  (`contDiffAt_rhoE` supplies `C²` of `ρ_{E,μ}` where `w > 0`).
* `littlejohn_passing_reparam`, `littlejohn_passing_reparam_neg`, `littlejohn_passing_confined`,
  `littlejohn_passing_confined_neg`: with the rate `v_∥/B*_∥` continuous and bounded away from
  zero (`≥ c > 0` or `≤ −c < 0`), the orbit is a time-changed field line of `±B̃_{E,μ}`, so any
  all-time field-line confinement theorem for `B̃_{E,μ}` transfers to the orbit.
* sanity: `rhoE_mu_zero`, `modFieldFn_const`, `littlejohn_passing_mu_zero` (`μ = 0` recovers
  `modField (m v_∥(0)/q)` of `velocity_eq_modField`), `modFieldFn_uniform` (uniform field:
  `B̃ = B₀`).

**Not done here (later, costly).** Confinement of the orbit requires an invariant torus (KAM) of
the field `B̃_{E,μ}` for the fixed `(E, μ, σ)`: one must generate the flow form of
`B + ∇×(ρ_{E,μ} b)` (a second square-root node `√(1 − λ|B|)`, `λ = μB₀/E`), certify its
divergence-free structure and an exact invariant torus as in the `μ = 0` pipeline, and check on the
torus region that `v_∥` stays bounded away from zero (`λ max|B| < 1`, i.e. `λ < 0.85`) and that
`B*_∥` is continuous and bounded (for curl-free fields `B*_∥ = |B|`, `BstarPar_field`). These
discharge `hconf` and `hge` of `littlejohn_passing_confined`.
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace PlasmaLean.Kinetic.GCPassing
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Kinetic.GCLittlejohn Filter

/-- The sign of a passing orbit: `1` if `v > 0`, else `−1`. -/
@[expose] def passSign (v : ℝ) : ℝ := if 0 < v then 1 else -1

/-- The energy-dependent gyro-length `ρ_{E,μ}(x) = σ (m/q) √(2(E − μ|B(x)|)/m)`. -/
@[expose] def rhoE (m q μ E σ : ℝ) (B : Space → Space) (x : Space) : ℝ :=
  σ * (m / q) * √(2 * (E - μ * ‖B x‖) / m)

/-- The modified field with a position-dependent gyro-length, `B̃ = B + ∇×(ρ b)`. -/
@[expose] def modFieldFn (ρ : Space → ℝ) (B : Space → Space) (x : Space) : Space :=
  B x + curl (fderiv ℝ (fun y => ρ y • bhat B y) x)

/-- `passSign v = 1` for `v > 0`. -/
theorem passSign_of_pos {v : ℝ} (h : 0 < v) : passSign v = 1 := by simp [passSign, h]

/-- `passSign v = −1` for `v < 0`. -/
theorem passSign_of_neg {v : ℝ} (h : v < 0) : passSign v = -1 := by
  simp [passSign, not_lt.2 h.le]

/-- `passSign v` squares to one. -/
theorem passSign_sq (v : ℝ) : passSign v ^ 2 = 1 := by
  unfold passSign; split_ifs <;> norm_num

/-- **Expanded modified field** (curl product rule): `B̃ = B + ρ ∇×b + ∇ρ × b`. -/
theorem modFieldFn_eq {ρ : Space → ℝ} {B : Space → Space} {x : Space}
    (hρ : DifferentiableAt ℝ ρ x) (hb : DifferentiableAt ℝ (bhat B) x) :
    modFieldFn ρ B x = B x + ρ x • curlb B x + cross (gradient ρ x) (bhat B x) := by
  rw [modFieldFn, curl_fderiv_smul hρ hb, curlb, add_assoc]

/-- Gradient of `ρ_{E,μ}`: `∇ρ = −σ μ/(q w) ∇|B|` with `w = √(2(E − μ|B|)/m) > 0`. -/
theorem hasGradientAt_rhoE {m q μ E σ : ℝ} {B : Space → Space} {x : Space}
    (hm : m ≠ 0) (hn : DifferentiableAt ℝ (fun y => ‖B y‖) x)
    (hu : 0 < 2 * (E - μ * ‖B x‖) / m) :
    HasGradientAt (rhoE m q μ E σ B)
      ((-(σ * μ) / (q * √(2 * (E - μ * ‖B x‖) / m))) • gradAbsB B x) x := by
  have hg : HasGradientAt (fun y => ‖B y‖) (gradAbsB B x) x := hn.hasGradientAt
  rw [hasGradientAt_iff_hasFDerivAt] at hg ⊢
  have hlin : HasFDerivAt (fun y => 2 * (E - μ * ‖B y‖) / m)
      ((-(2 * μ / m)) • InnerProductSpace.toDual ℝ Space (gradAbsB B x)) x := by
    have := (((hg.const_mul μ).const_sub E).const_mul 2).mul_const m⁻¹
    convert this using 1
    · funext y; simp [div_eq_mul_inv]
    · ext v; simp; ring
  have hs := (hlin.sqrt hu.ne').const_mul (σ * (m / q))
  have hw : 0 < √(2 * (E - μ * ‖B x‖) / m) := Real.sqrt_pos.2 hu
  refine hs.congr_fderiv ?_
  rw [map_smul, smul_smul, smul_smul]
  congr 1
  field_simp

/-- `ρ_{E,μ}` is differentiable where `w > 0`. -/
theorem differentiableAt_rhoE {m q μ E σ : ℝ} {B : Space → Space} {x : Space}
    (hm : m ≠ 0) (hn : DifferentiableAt ℝ (fun y => ‖B y‖) x)
    (hu : 0 < 2 * (E - μ * ‖B x‖) / m) : DifferentiableAt ℝ (rhoE m q μ E σ B) x :=
  (hasGradientAt_rhoE hm hn hu).differentiableAt

/-- `ρ_{E,μ}` is `C²` where `|B|` is `C²` and `w > 0`. -/
theorem contDiffAt_rhoE {m q μ E σ : ℝ} {B : Space → Space} {x : Space}
    (hn : ContDiffAt ℝ 2 (fun y => ‖B y‖) x) (hu : 0 < 2 * (E - μ * ‖B x‖) / m) :
    ContDiffAt ℝ 2 (rhoE m q μ E σ B) x := by
  have hlin : ContDiffAt ℝ 2 (fun y => 2 * (E - μ * ‖B y‖) / m) x :=
    (contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_const.mul hn))).div_const m
  exact contDiffAt_const.mul (hlin.sqrt hu.ne')

/-- **The passing velocity identity** (pointwise vector algebra). If `ρ(x) = m v/q` and
`v ∇ρ(x) = −(μ/q) ∇|B|(x)`, then `v (B + ρ ∇×b + ∇ρ × b) = v B* + (μ/q) b × ∇|B|`. -/
theorem passing_velocity_identity {m q μ v r : ℝ} {g : Space} (B : Space → Space) (x : Space)
    (hr : r = m * v / q) (hg : v • g = -(μ / q) • gradAbsB B x) :
    v • (B x + r • curlb B x + cross g (bhat B x)) =
      v • Bstar m q B v x + (μ / q) • cross (bhat B x) (gradAbsB B x) := by
  have hcross : v • cross g (bhat B x) = (μ / q) • cross (bhat B x) (gradAbsB B x) := by
    have h0 := congrArg (· 0) hg
    have h1 := congrArg (· 1) hg
    have h2 := congrArg (· 2) hg
    simp only [PiLp.smul_apply, smul_eq_mul] at h0 h1 h2
    obtain ⟨c0, c1, c2⟩ := cross_coords g (bhat B x)
    obtain ⟨d0, d1, d2⟩ := cross_coords (bhat B x) (gradAbsB B x)
    apply space_ext <;> simp only [PiLp.smul_apply, smul_eq_mul, c0, c1, c2, d0, d1, d2]
    · linear_combination (bhat B x 2) * h1 - (bhat B x 1) * h2
    · linear_combination (bhat B x 0) * h2 - (bhat B x 2) * h0
    · linear_combination (bhat B x 1) * h0 - (bhat B x 0) * h1
  rw [smul_add, hcross, Bstar, hr, smul_add]

/-- A passing orbit keeps the sign of `v_∥(0)` (intermediate value theorem). -/
theorem passSign_mul_abs {v : ℝ → ℝ} (hc : Continuous v) (hv0 : ∀ t, v t ≠ 0) (t : ℝ) :
    passSign (v 0) * |v t| = v t := by
  have key : ∀ a b : ℝ, v a < 0 → 0 < v b → False := fun a b ha hb => by
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := a) (b := b) hc.continuousOn
      (Set.mem_uIcc.2 (Or.inl ⟨ha.le, hb.le⟩))
    exact hv0 s hs
  rcases lt_or_gt_of_ne (hv0 t) with ht | ht <;> rcases lt_or_gt_of_ne (hv0 0) with h0 | h0
  · rw [passSign_of_neg h0, abs_of_neg ht]; ring
  · exact (key t 0 ht h0).elim
  · exact (key 0 t h0 ht).elim
  · rw [passSign_of_pos h0, abs_of_pos ht]; ring

/-- **Parallel velocity of a passing orbit**: `v_∥(t) = σ √(2(E − μ|B(X t)|)/m)` with
`σ = passSign (v_∥(0))` and `E = H(X 0, v_∥ 0)`; moreover the radicand is positive. -/
theorem vpar_eq_sign_sqrt {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hv0 : ∀ t, v t ≠ 0)
    (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t)) (t : ℝ) :
    0 < 2 * (hamiltonian m μ B (X 0) (v 0) - μ * ‖B (X t)‖) / m ∧
    v t = passSign (v 0) * √(2 * (hamiltonian m μ B (X 0) (v 0) - μ * ‖B (X t)‖) / m) := by
  have hE := energy_const h hm.ne' hn t
  have hrad : 2 * (hamiltonian m μ B (X 0) (v 0) - μ * ‖B (X t)‖) / m = v t ^ 2 := by
    rw [hamiltonian, ← hE]; field_simp; ring
  have hc : Continuous v := continuous_iff_continuousAt.2 fun s => (h.hv s).continuousAt
  rw [hrad, Real.sqrt_sq_eq_abs, passSign_mul_abs hc hv0 t]
  have := hv0 t
  exact ⟨by positivity, rfl⟩

/-- **Passing guiding centres move along `B̃_{E,μ}`**: for a Littlejohn orbit with `v_∥` never
zero, `dX/dt = (v_∥/B*_∥) B̃_{E,μ}(X)`, where `B̃_{E,μ} = B + ∇×(ρ_{E,μ} b)`,
`ρ_{E,μ} = σ (m/q) √(2(E − μ|B|)/m)`, `E = H(X 0, v_∥ 0)`, `σ = passSign (v_∥ 0)`. -/
theorem littlejohn_passing_isFieldLine {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hq : q ≠ 0)
    (hv0 : ∀ t, v t ≠ 0) (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t))
    (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t)) (t : ℝ) :
    HasDerivAt X ((v t / BstarPar m q B (v t) (X t)) •
      modFieldFn (rhoE m q μ (hamiltonian m μ B (X 0) (v 0)) (passSign (v 0)) B) B (X t)) t := by
  set E := hamiltonian m μ B (X 0) (v 0)
  set σ := passSign (v 0)
  obtain ⟨hu, hvt⟩ := vpar_eq_sign_sqrt h hm hv0 hn t
  set w := √(2 * (E - μ * ‖B (X t)‖) / m)
  have hw : 0 < w := Real.sqrt_pos.2 hu
  have hgr := hasGradientAt_rhoE (q := q) (σ := σ) hm.ne' (hn t) hu
  rw [modFieldFn_eq hgr.differentiableAt (hb t), hgr.gradient]
  have hσ : σ ^ 2 = 1 := passSign_sq _
  have hid := passing_velocity_identity (m := m) (q := q) (μ := μ) (v := v t)
    (r := rhoE m q μ E σ B (X t)) (g := (-(σ * μ) / (q * w)) • gradAbsB B (X t)) B (X t)
    (by rw [rhoE, hvt]; ring)
    (by rw [smul_smul, hvt]; congr 1; field_simp; linear_combination (-μ) * hσ)
  convert h.hX t using 1
  rw [div_eq_inv_mul, ← smul_smul, hid]

/-! ### Divergence -/

/-- **`B̃ = B + ∇×(ρ b)` is divergence free** when `∇·B = 0`, `B` is differentiable and `ρ b` is
`C²` at the point. -/
theorem modFieldFn_divFree {ρ : Space → ℝ} {B : Space → Space} {x : Space}
    (hB : DifferentiableAt ℝ B x) (hρb : ContDiffAt ℝ 2 (fun y => ρ y • bhat B y) x)
    (hdiv : divergence (fderiv ℝ B x) = 0) :
    divergence (fderiv ℝ (modFieldFn ρ B) x) = 0 := by
  set F := fun y => ρ y • bhat B y
  have hdd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hρb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y => curl (fderiv ℝ F y)) x :=
    curlCLM.differentiableAt.comp x hdd
  rw [show modFieldFn ρ B = B + fun y => curl (fderiv ℝ F y) from rfl,
    (hB.hasFDerivAt.add hc.hasFDerivAt).fderiv]
  have hlin : ∀ L M : Space →L[ℝ] Space, divergence (L + M) = divergence L + divergence M :=
    fun L M => by simp [divergence, map_add]
  rw [hlin, hdiv, divergence_curl hρb, add_zero]

/-- `B̃_{E,μ}` is divergence free where `∇·B = 0`, `B` is differentiable, `|B|` and `b` are `C²`
and `w > 0`. -/
theorem modFieldFn_rhoE_divFree {m q μ E σ : ℝ} {B : Space → Space} {x : Space}
    (hB : DifferentiableAt ℝ B x) (hn : ContDiffAt ℝ 2 (fun y => ‖B y‖) x)
    (hb : ContDiffAt ℝ 2 (bhat B) x) (hu : 0 < 2 * (E - μ * ‖B x‖) / m)
    (hdiv : divergence (fderiv ℝ B x) = 0) :
    divergence (fderiv ℝ (modFieldFn (rhoE m q μ E σ B) B) x) = 0 :=
  modFieldFn_divFree hB ((contDiffAt_rhoE hn hu).smul hb) hdiv

/-! ### Reparametrization and confinement transfer -/

/-- **Passing orbits are time-changed field lines of `B̃_{E,μ}`** when the rate `v_∥/B*_∥` is
continuous and `≥ c > 0`. -/
theorem littlejohn_passing_reparam {m q μ c : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hq : q ≠ 0)
    (hv0 : ∀ t, v t ≠ 0) (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t))
    (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t)) (hc : 0 < c)
    (hcont : Continuous fun t => v t / BstarPar m q B (v t) (X t))
    (hge : ∀ t, c ≤ v t / BstarPar m q B (v t) (X t)) :
    ∃ (γ : ℝ → Space) (S : ℝ → ℝ),
      IsFieldLine (modFieldFn (rhoE m q μ (hamiltonian m μ B (X 0) (v 0)) (passSign (v 0)) B) B) γ
        ∧ S 0 = 0 ∧ ∀ t, X t = γ (S t) :=
  isFieldLine_of_rate_ge hc hcont hge (littlejohn_passing_isFieldLine h hm hq hv0 hn hb)

/-- Negative-rate version (`v_∥/B*_∥ ≤ −c < 0`): a time-changed field line of `−B̃_{E,μ}`. -/
theorem littlejohn_passing_reparam_neg {m q μ c : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hq : q ≠ 0)
    (hv0 : ∀ t, v t ≠ 0) (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t))
    (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t)) (hc : 0 < c)
    (hcont : Continuous fun t => v t / BstarPar m q B (v t) (X t))
    (hle : ∀ t, v t / BstarPar m q B (v t) (X t) ≤ -c) :
    ∃ (γ : ℝ → Space) (S : ℝ → ℝ),
      IsFieldLine (fun x =>
        -modFieldFn (rhoE m q μ (hamiltonian m μ B (X 0) (v 0)) (passSign (v 0)) B) B x) γ
        ∧ S 0 = 0 ∧ ∀ t, X t = γ (S t) := by
  refine isFieldLine_of_rate_ge (lam := fun t => -(v t / BstarPar m q B (v t) (X t))) hc
    hcont.neg (fun t => by linarith [hle t]) fun t => ?_
  simpa [neg_smul, smul_neg] using littlejohn_passing_isFieldLine h hm hq hv0 hn hb t

/-- **Confinement transfer for passing orbits.** If every field line of `B̃_{E,μ}` starting in `Ω`
stays in `Ω` for all time, then so does every passing guiding centre whose rate `v_∥/B*_∥` is
continuous and bounded below by `c > 0`. -/
theorem littlejohn_passing_confined {m q μ c : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} {Ω : Set Space} (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hq : q ≠ 0)
    (hv0 : ∀ t, v t ≠ 0) (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t))
    (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t)) (hc : 0 < c)
    (hcont : Continuous fun t => v t / BstarPar m q B (v t) (X t))
    (hge : ∀ t, c ≤ v t / BstarPar m q B (v t) (X t))
    (hconf : ∀ γ : ℝ → Space,
      IsFieldLine (modFieldFn (rhoE m q μ (hamiltonian m μ B (X 0) (v 0)) (passSign (v 0)) B) B) γ
        → γ 0 ∈ Ω → ∀ s, γ s ∈ Ω)
    (h0 : X 0 ∈ Ω) (t : ℝ) : X t ∈ Ω := by
  obtain ⟨γ, S, hγ, hS0, hXγ⟩ := littlejohn_passing_reparam h hm hq hv0 hn hb hc hcont hge
  rw [hXγ]
  exact hconf γ hγ (by rw [← hS0, ← hXγ]; exact h0) (S t)

/-- Confinement transfer, negative-rate version (field lines of `−B̃_{E,μ}`). -/
theorem littlejohn_passing_confined_neg {m q μ c : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} {Ω : Set Space} (h : LittlejohnOrbit m q μ B X v) (hm : 0 < m) (hq : q ≠ 0)
    (hv0 : ∀ t, v t ≠ 0) (hn : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t))
    (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t)) (hc : 0 < c)
    (hcont : Continuous fun t => v t / BstarPar m q B (v t) (X t))
    (hle : ∀ t, v t / BstarPar m q B (v t) (X t) ≤ -c)
    (hconf : ∀ γ : ℝ → Space, IsFieldLine (fun x =>
        -modFieldFn (rhoE m q μ (hamiltonian m μ B (X 0) (v 0)) (passSign (v 0)) B) B x) γ
        → γ 0 ∈ Ω → ∀ s, γ s ∈ Ω)
    (h0 : X 0 ∈ Ω) (t : ℝ) : X t ∈ Ω := by
  obtain ⟨γ, S, hγ, hS0, hXγ⟩ := littlejohn_passing_reparam_neg h hm hq hv0 hn hb hc hcont hle
  rw [hXγ]
  exact hconf γ hγ (by rw [← hS0, ← hXγ]; exact h0) (S t)

/-! ### Sanity checks -/

/-- For `μ = 0`, `ρ_{E,0} = m v_∥(0)/q` (with `E = m v_∥(0)²/2`, `σ = sign v_∥(0)`). -/
theorem rhoE_mu_zero {m q v₀ : ℝ} (hm : 0 < m) (hv₀ : v₀ ≠ 0) (B : Space → Space)
    (x₀ x : Space) :
    rhoE m q 0 (hamiltonian m 0 B x₀ v₀) (passSign v₀) B x = m * v₀ / q := by
  have hrad : 2 * (hamiltonian m 0 B x₀ v₀ - 0 * ‖B x‖) / m = v₀ ^ 2 := by
    rw [hamiltonian]; field_simp; ring
  have hs : passSign v₀ * |v₀| = v₀ := by
    rcases lt_or_gt_of_ne hv₀ with h | h
    · rw [passSign_of_neg h, abs_of_neg h]; ring
    · rw [passSign_of_pos h, abs_of_pos h]; ring
  rw [rhoE, hrad, Real.sqrt_sq_eq_abs]
  linear_combination (m / q) * hs

/-- A constant gyro-length recovers `modField`: `B + ∇×(r b) = B + r ∇×b`. -/
theorem modFieldFn_const (r : ℝ) {B : Space → Space} {x : Space}
    (hb : DifferentiableAt ℝ (bhat B) x) :
    modFieldFn (fun _ => r) B x = modField r B x := by
  rw [modFieldFn, curl_fderiv_const_smul r hb, modField, curlb]

/-- **`μ = 0` sanity check**: the passing field `B̃_{E,0}` along the orbit is the field
`modField (m v_∥(0)/q)` of `velocity_eq_modField`. -/
theorem littlejohn_passing_mu_zero {m q : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (hm : 0 < m) (hv0 : v 0 ≠ 0) (hb : ∀ t, DifferentiableAt ℝ (bhat B) (X t))
    (t : ℝ) :
    modFieldFn (rhoE m q 0 (hamiltonian m 0 B (X 0) (v 0)) (passSign (v 0)) B) B (X t) =
      modField (m * v 0 / q) B (X t) := by
  have hfun : rhoE m q 0 (hamiltonian m 0 B (X 0) (v 0)) (passSign (v 0)) B =
      fun _ => m * v 0 / q := funext fun x => rhoE_mu_zero hm hv0 B (X 0) x
  rw [hfun, modFieldFn_const _ (hb t)]

/-- **Uniform field sanity check**: for `B ≡ B₀`, `ρ_{E,μ}` is constant and `B̃_{E,μ} = B₀`. -/
theorem modFieldFn_uniform (m q μ E σ : ℝ) (B₀ x : Space) :
    modFieldFn (rhoE m q μ E σ (fun _ => B₀)) (fun _ => B₀) x = B₀ := by
  have : (fun y => rhoE m q μ E σ (fun _ => B₀) y • bhat (fun _ : Space => B₀) y) =
      fun _ => rhoE m q μ E σ (fun _ => B₀) 0 • (‖B₀‖⁻¹ • B₀) := rfl
  simp [modFieldFn, this, curl]

end PlasmaLean.Kinetic.GCPassing
