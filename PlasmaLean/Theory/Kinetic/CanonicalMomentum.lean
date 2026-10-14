/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.FullOrbit
public import PlasmaLean.Theory.Kinetic.ApproximateInvariant
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Canonical toroidal momentum and all-time full-orbit confinement (task K2)

For a magnetic field symmetric under rotations about the vertical axis, with poloidal flux
function `ψ`, the canonical angular momentum `p_φ = m (x × v)_z + q ψ(x)` is conserved by
the Newton–Lorentz flow. Together with conservation of speed this confines a charged
particle to a band `|ψ(x(t)) - ψ(x(0))| ≤ (m |v| / |q|)(‖x(t)‖ + ‖x(0)‖)`.

The symmetry enters only through the explicit hypothesis `AxisymmetricFlux B G`:
`(x × (v × B(x)))_z = -⟪G(x), v⟫` for all `x, v`, where `G = ∇ψ`. For `B = ∇ψ × ∇φ`
plus a toroidal part, with axisymmetric `ψ`, this is an algebraic identity; the polynomial
example below checks it by `ring`.

Main results:

* `canonicalMomentum_conserved`: exact conservation for every orbit;
* `flux_band`: the quantitative band;
* `trapped_of_gap`: a continuity (intermediate value) argument turning a pointwise forbidden
  band of `ψ` values into confinement for all time, forwards and backwards;
* `PolyTokamak.orbit_confined`: in an explicit polynomial axisymmetric field, every particle
  with normalized rigidity `m |v| ≤ |q| / 64` starting with `ψ ≤ 1/64` stays in the solid
  torus `{ψ ≤ 11/192}`, hence at major radius `R² ≥ 1/2`, for ALL times.

Scope: the example is dimensionless and tokamak-like (axisymmetric), not a stellarator.
Non-relativistic full orbits, static fields, no collisions or radiation; existence of the
trajectory is supplied. Quasisymmetric stellarators have only an approximate analogue in
guiding-centre theory; that transfer is a separate obligation.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic
open PlasmaLean.Fields WithLp
open scoped RealInnerProductSpace

/-- The vertical component of the angular momentum per unit mass, `(x × v)_z`. -/
@[expose] def angularZ (x v : Space) : ℝ := x 0 * v 1 - x 1 * v 0

/-- Axisymmetric flux structure: the vertical torque of the magnetic force equals minus
the rate of change of `ψ`, encoded by its gradient `G`. -/
@[expose] def AxisymmetricFlux (B G : Space → Space) : Prop :=
  ∀ x v : Space, angularZ x (cross v (B x)) = -⟪G x, v⟫

/-- Coordinates of a differentiable curve in Euclidean space are differentiable. -/
theorem hasDerivAt_coord {x : ℝ → Space} {x' : Space} {t : ℝ} (h : HasDerivAt x x' t)
    (i : Fin 3) : HasDerivAt (fun s => x s i) (x' i) t := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t h
  exact this

/-- `|(x × v)_z| ≤ ‖x‖ ‖v‖`. -/
theorem abs_angularZ_le (x v : Space) : |angularZ x v| ≤ ‖x‖ * ‖v‖ := by
  have hx := EuclideanSpace.norm_sq_eq x
  have hv := EuclideanSpace.norm_sq_eq v
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hx hv
  have hsq : angularZ x v ^ 2 ≤ (‖x‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, hx, hv, angularZ]
    nlinarith [sq_nonneg (x 0 * v 0 + x 1 * v 1), sq_nonneg (x 2 * v 0), sq_nonneg (x 2 * v 1),
      sq_nonneg (x 0 * v 2), sq_nonneg (x 1 * v 2), sq_nonneg (x 2 * v 2)]
  exact abs_le_of_sq_le_sq' hsq (by positivity) |> abs_le.mpr

/-- Canonical angular momentum `m (x × v)_z + q ψ(x)` along an orbit. -/
@[expose] def canonicalMomentum (m q : ℝ) (ψ : Space → ℝ) (x v : ℝ → Space) (t : ℝ) : ℝ :=
  m * angularZ (x t) (v t) + q * ψ (x t)

/-- Conservation of canonical angular momentum in an axisymmetric magnetic field. -/
theorem canonicalMomentum_conserved {m q : ℝ} {B G : Space → Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : AxisymmetricFlux B G) (s t : ℝ) :
    canonicalMomentum m q ψ x v s = canonicalMomentum m q ψ x v t := by
  have hd (r : ℝ) : HasDerivAt (canonicalMomentum m q ψ x v) 0 r := by
    obtain ⟨a, ha, hlaw⟩ := h.newton r
    have hx := h.position r
    have hL : HasDerivAt (fun s => angularZ (x s) (v s))
        (x r 0 * a 1 - x r 1 * a 0) r := by
      have := ((hasDerivAt_coord hx 0).mul (hasDerivAt_coord ha 1)).sub
        ((hasDerivAt_coord hx 1).mul (hasDerivAt_coord ha 0))
      convert this using 1
      · funext s; rfl
      · ring
    have hp : HasDerivAt (fun s => ψ (x s)) ⟪G (x r), v r⟫ r :=
      (hψ (x r)).comp_hasDerivAt r hx
    change HasDerivAt (fun s => m * angularZ (x s) (v s) + q * ψ (x s)) 0 r
    convert (hL.const_mul m).add (hp.const_mul q) using 1
    have h0 := congrArg (fun w : Space => w 0) hlaw
    have h1 := congrArg (fun w : Space => w 1) hlaw
    simp only [PiLp.smul_apply, smul_eq_mul, zero_add] at h0 h1
    have key := hB (x r) (v r)
    unfold angularZ at key
    linear_combination (-(x r 0)) * h1 + (x r 1) * h0 - q * key
  refine is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => ?_) s t
  exact (hd r).deriv

/-- Quantitative flux band: `|q| |ψ(x t) - ψ(x 0)| ≤ |m| ‖v 0‖ (‖x t‖ + ‖x 0‖)`. -/
theorem flux_band {m q : ℝ} (hm : m ≠ 0) {B G : Space → Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : AxisymmetricFlux B G) (t : ℝ) :
    |q| * |ψ (x t) - ψ (x 0)| ≤ |m| * ‖v 0‖ * (‖x t‖ + ‖x 0‖) := by
  have hc := canonicalMomentum_conserved h hψ hB 0 t
  unfold canonicalMomentum at hc
  have hs := speed_conserved hm h t 0
  have e : q * (ψ (x t) - ψ (x 0)) = m * (angularZ (x 0) (v 0) - angularZ (x t) (v t)) := by
    linarith
  rw [← abs_mul, e, abs_mul, mul_assoc]
  gcongr
  calc |angularZ (x 0) (v 0) - angularZ (x t) (v t)|
      ≤ |angularZ (x 0) (v 0)| + |angularZ (x t) (v t)| := abs_sub _ _
    _ ≤ ‖x 0‖ * ‖v 0‖ + ‖x t‖ * ‖v t‖ := add_le_add (abs_angularZ_le _ _) (abs_angularZ_le _ _)
    _ = ‖v 0‖ * (‖x t‖ + ‖x 0‖) := by rw [hs]; ring

/-- Continuity trapping: a continuous real function of time that starts at most `c'` and
can never take a value in the gap `(c', c]` stays at most `c'` for all times. -/
theorem trapped_of_gap {f : ℝ → ℝ} (hf : Continuous f) {c' c : ℝ} (hcc : c' < c)
    (h0 : f 0 ≤ c') (gap : ∀ t, f t ≤ c → f t ≤ c') (t : ℝ) : f t ≤ c' := by
  by_contra hlt
  push Not at hlt
  have hct : c < f t := by
    by_contra hle
    exact absurd (gap t (not_lt.mp hle)) (not_le.mpr hlt)
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hf.continuousOn
    (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hct.le⟩))
  have := gap s hs.le
  linarith

/-- Positions along a Lorentz orbit form a continuous curve. -/
theorem LorentzOrbit.continuous_position {m q : ℝ} {E B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q E B x v) : Continuous x :=
  continuous_iff_continuousAt.mpr fun t => (h.position t).continuousAt

/-- All-time confinement in an axisymmetric field. Hypotheses: `hreg` says points with
`ψ ≤ c` have norm at most `ρ`; `hgap` is the band bound `ψ(x 0) + k (ρ + ‖x 0‖) ≤ c' < c`
with normalized rigidity `k = |m| ‖v 0‖ / |q|`. Then `ψ(x t) ≤ c'` for every real `t`. -/
theorem orbit_trapped {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {B G : Space → Space}
    {ψ : Space → ℝ} {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : AxisymmetricFlux B G)
    {c' c ρ : ℝ} (hcc : c' < c) (hρ : 0 ≤ ρ) (hreg : ∀ y, ψ y ≤ c → ‖y‖ ≤ ρ)
    (hgap : ψ (x 0) + |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) ≤ c') (t : ℝ) : ψ (x t) ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hcont : Continuous fun s => ψ (x s) :=
    (continuous_iff_continuousAt.mpr fun y => (hψ y).continuousAt).comp
      h.continuous_position
  have hk : 0 ≤ |m| * ‖v 0‖ / |q| := by positivity
  refine trapped_of_gap hcont hcc ?_ (fun s hs => ?_) t
  · have : 0 ≤ |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) := by
      positivity
    linarith
  · have hb := flux_band hm h hψ hB s
    have hn := hreg _ hs
    have h1 : ψ (x s) - ψ (x 0) ≤ |m| * ‖v 0‖ / |q| * (‖x s‖ + ‖x 0‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hqpos]
      nlinarith [le_abs_self (ψ (x s) - ψ (x 0))]
    have h2 : |m| * ‖v 0‖ / |q| * (‖x s‖ + ‖x 0‖) ≤ |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    linarith

/-! ## Imperfect symmetry: finite-time confinement

A symmetry-breaking (ripple or quasisymmetry-defect) field changes the canonical momentum
at a rate bounded by the defect `δ`. The flux band then widens linearly in time, giving
confinement for an explicit time inversely proportional to `δ`. -/

/-- Defect of axisymmetric flux structure on a region `S`: the vertical magnetic torque
differs from `-⟪G, w⟫` by at most `δ ‖w‖`. -/
@[expose] def FluxDefectOn (B G : Space → Space) (S : Set Space) (δ : ℝ) : Prop :=
  ∀ y ∈ S, ∀ w : Space, |angularZ y (cross w (B y)) + ⟪G y, w⟫| ≤ δ * ‖w‖

/-- Exact axisymmetric structure has zero defect everywhere. -/
theorem AxisymmetricFlux.defect_zero {B G : Space → Space} (h : AxisymmetricFlux B G)
    (S : Set Space) : FluxDefectOn B G S 0 := by
  intro y _ w
  rw [h y w]; simp

/-- Bootstrap (first-exit) lemma: if, on `[0,T]`, staying below `c` up to time `t` forces
`f t ≤ c' < c`, then `f ≤ c'` on all of `[0,T]`. -/
theorem trapped_until {f : ℝ → ℝ} (hf : Continuous f) {c' c T : ℝ} (hcc : c' < c)
    (h0 : f 0 ≤ c') (step : ∀ t ∈ Set.Icc 0 T, (∀ s ∈ Set.Icc 0 t, f s ≤ c) → f t ≤ c') :
    ∀ t ∈ Set.Icc 0 T, f t ≤ c' := by
  intro t₀ ht₀
  by_contra hlt
  push Not at hlt
  set A := {s | s ∈ Set.Icc 0 t₀ ∧ c ≤ f s} with hA
  rcases Set.eq_empty_or_nonempty A with hE | hne
  · refine absurd (step t₀ ht₀ (fun s hs => ?_)) (not_le.mpr hlt)
    by_contra hcs
    have : s ∈ A := ⟨hs, (not_le.mp hcs).le⟩
    rw [hE] at this
    exact this
  · have hcl : IsClosed A := isClosed_Icc.inter (isClosed_le continuous_const hf)
    have hbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf A
    have hτ : τ ∈ A := hcl.csInf_mem hne hbdd
    have before : ∀ s ∈ Set.Icc 0 t₀, s < τ → f s < c := fun s hs hsτ => by
      by_contra hcs
      exact absurd (csInf_le hbdd ⟨hs, not_lt.mp hcs⟩) (not_le.mpr hsτ)
    obtain ⟨σ, hσ, hfσ⟩ := intermediate_value_Icc hτ.1.1 hf.continuousOn
      (show c ∈ Set.Icc (f 0) (f τ) from ⟨by linarith, hτ.2⟩)
    have hστ : τ ≤ σ := csInf_le hbdd ⟨⟨hσ.1, hσ.2.trans hτ.1.2⟩, hfσ.ge⟩
    have heq : σ = τ := le_antisymm hσ.2 hστ
    have hτT : τ ∈ Set.Icc 0 T := ⟨hτ.1.1, hτ.1.2.trans ht₀.2⟩
    have := step τ hτT (fun s hs => by
      rcases hs.2.lt_or_eq with h | h
      · exact (before s ⟨hs.1, hs.2.trans hτ.1.2⟩ h).le
      · rw [h, ← heq, hfσ])
    rw [← heq, hfσ] at this
    linarith

/-- Widened flux band under a symmetry defect, valid while the orbit stays in `S`. -/
theorem approx_flux_band {m q : ℝ} (hm : m ≠ 0) {B G : Space → Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {S : Set Space} {δ : ℝ}
    (hB : FluxDefectOn B G S δ) {t : ℝ} (ht : 0 ≤ t) (hin : ∀ s ∈ Set.Icc 0 t, x s ∈ S) :
    |q| * |ψ (x t) - ψ (x 0)| ≤
      |m| * ‖v 0‖ * (‖x t‖ + ‖x 0‖) + |q| * δ * ‖v 0‖ * t := by
  have hd (r : ℝ) : HasDerivAt (canonicalMomentum m q ψ x v)
      (q * (angularZ (x r) (cross (v r) (B (x r))) + ⟪G (x r), v r⟫)) r := by
    obtain ⟨a, ha, hlaw⟩ := h.newton r
    have hx := h.position r
    have hL : HasDerivAt (fun s => angularZ (x s) (v s))
        (x r 0 * a 1 - x r 1 * a 0) r := by
      have := ((hasDerivAt_coord hx 0).mul (hasDerivAt_coord ha 1)).sub
        ((hasDerivAt_coord hx 1).mul (hasDerivAt_coord ha 0))
      convert this using 1
      · funext s; rfl
      · ring
    have hp : HasDerivAt (fun s => ψ (x s)) ⟪G (x r), v r⟫ r :=
      (hψ (x r)).comp_hasDerivAt r hx
    change HasDerivAt (fun s => m * angularZ (x s) (v s) + q * ψ (x s)) _ r
    convert (hL.const_mul m).add (hp.const_mul q) using 1
    have h0 := congrArg (fun w : Space => w 0) hlaw
    have h1 := congrArg (fun w : Space => w 1) hlaw
    simp only [PiLp.smul_apply, smul_eq_mul, zero_add] at h0 h1
    unfold angularZ
    linear_combination (-(x r 0)) * h1 + (x r 1) * h0
  have hbound : ∀ s ∈ Set.Icc 0 t,
      |q * (angularZ (x s) (cross (v s) (B (x s))) + ⟪G (x s), v s⟫)| ≤ |q| * δ * ‖v 0‖ := by
    intro s hs
    rw [abs_mul, mul_assoc, ← speed_conserved hm h s 0]
    exact mul_le_mul_of_nonneg_left (hB _ (hin s hs) _) (abs_nonneg q)
  have hdrift := invariant_drift (fun s _ => hd s) hbound ⟨ht, le_rfl⟩
  unfold canonicalMomentum at hdrift
  have hs := speed_conserved hm h t 0
  have e : q * (ψ (x t) - ψ (x 0)) = (m * angularZ (x t) (v t) + q * ψ (x t) -
      (m * angularZ (x 0) (v 0) + q * ψ (x 0))) +
      m * (angularZ (x 0) (v 0) - angularZ (x t) (v t)) := by ring
  rw [← abs_mul, e]
  have hang : |m * (angularZ (x 0) (v 0) - angularZ (x t) (v t))| ≤
      |m| * ‖v 0‖ * (‖x t‖ + ‖x 0‖) := by
    rw [abs_mul, mul_assoc]
    gcongr
    calc |angularZ (x 0) (v 0) - angularZ (x t) (v t)|
        ≤ |angularZ (x 0) (v 0)| + |angularZ (x t) (v t)| := abs_sub _ _
      _ ≤ ‖x 0‖ * ‖v 0‖ + ‖x t‖ * ‖v t‖ :=
          add_le_add (abs_angularZ_le _ _) (abs_angularZ_le _ _)
      _ = ‖v 0‖ * (‖x t‖ + ‖x 0‖) := by rw [hs]; ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |q| * δ * ‖v 0‖ * t + |m| * ‖v 0‖ * (‖x t‖ + ‖x 0‖) := add_le_add hdrift hang
    _ = _ := by ring

/-- Finite-time confinement under a symmetry defect on the region `{ψ ≤ c}`: if
`ψ(x 0) + k (ρ + ‖x 0‖) + δ ‖v 0‖ T ≤ c' < c`, then `ψ(x t) ≤ c'` for all `t ∈ [0,T]`. -/
theorem orbit_trapped_until {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {B G : Space → Space}
    {ψ : Space → ℝ} {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {c' c ρ δ T : ℝ} (hcc : c' < c)
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hB : FluxDefectOn B G {y | ψ y ≤ c} δ)
    (hreg : ∀ y, ψ y ≤ c → ‖y‖ ≤ ρ)
    (hgap : ψ (x 0) + |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) + δ * ‖v 0‖ * T ≤ c') :
    ∀ t ∈ Set.Icc 0 T, ψ (x t) ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hcont : Continuous fun s => ψ (x s) :=
    (continuous_iff_continuousAt.mpr fun y => (hψ y).continuousAt).comp
      h.continuous_position
  have hk : 0 ≤ |m| * ‖v 0‖ / |q| := by positivity
  refine trapped_until hcont hcc ?_ (fun t ht hhist => ?_)
  · have : 0 ≤ |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) + δ * ‖v 0‖ * T := by positivity
    linarith
  · have hb := approx_flux_band hm h hψ hB ht.1 (fun s hs => hhist s hs)
    have hn := hreg _ (hhist t ⟨ht.1, le_rfl⟩)
    have h1 : ψ (x t) - ψ (x 0) ≤ |m| * ‖v 0‖ / |q| * (‖x t‖ + ‖x 0‖) + δ * ‖v 0‖ * t := by
      have : |q| * (ψ (x t) - ψ (x 0)) ≤
          |q| * (|m| * ‖v 0‖ / |q| * (‖x t‖ + ‖x 0‖) + δ * ‖v 0‖ * t) := by
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hqpos.ne']
        nlinarith [le_abs_self (ψ (x t) - ψ (x 0))]
      exact le_of_mul_le_mul_left this hqpos
    have h2 : |m| * ‖v 0‖ / |q| * (‖x t‖ + ‖x 0‖) ≤ |m| * ‖v 0‖ / |q| * (ρ + ‖x 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    have h3 : δ * ‖v 0‖ * t ≤ δ * ‖v 0‖ * T :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith

end PlasmaLean.Kinetic
