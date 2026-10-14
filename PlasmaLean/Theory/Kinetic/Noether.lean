/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CanonicalMomentum
public import PlasmaLean.Theory.Fields.FirstIntegral
public import PlasmaLean.Theory.Fields.FieldDerivative

/-!
# Noether momentum for an arbitrary Euclidean symmetry (task K2)

Generalizes `CanonicalMomentum` from rotations about the vertical axis to any Killing
field `K` of Euclidean space: `K` is differentiable with derivative `DK x` antisymmetric,
`⟪DK x v, v⟫ = 0`. Rotations, translations and helical screw motions `(-x₁, x₀, h)` are
the examples relevant to tokamaks, straight cylinders and helical (straight-stellarator)
configurations.

The symmetry of the magnetic field enters through `SymmetricFlux B G K`:
`⟪K x, v × B x⟫ = -⟪G x, v⟫` for all `x, v`, with `G = ∇ψ`. Then

* `noetherMomentum_conserved`: `m ⟪K(x), v⟫ + q ψ(x)` is constant along every
  Newton–Lorentz orbit in the static magnetic field;
* `noether_flux_band`: `|q| |ψ(x t) - ψ(x 0)| ≤ |m| ‖v 0‖ (‖K(x t)‖ + ‖K(x 0)‖)`;
* `noether_orbit_trapped`: all-time confinement in `{ψ ≤ c'}` from a bound on `‖K‖` over
  `{ψ ≤ c}` (no bound on `‖x‖` is needed, so regions unbounded along a symmetry
  direction are allowed);
* `noether_orbit_trapped_until`: finite-time confinement under a symmetry defect `δ`;
* `SymmetricFlux.firstIntegral`: `ψ` is also an exact field-line first integral;
* `symmetricFlux_of_cross`: the algebraic construction `B = |K|⁻² (∇ψ × K + F K)` of a
  symmetric field from an invariant `ψ` (`⟪K, ∇ψ⟫ = 0`).

Non-relativistic full orbits in static fields; trajectories are supplied. Exact
symmetries are idealizations: toroidal stellarators have at most approximate
(quasi-)symmetry, whose guiding-centre consequences are a separate obligation.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic
open PlasmaLean.Fields WithLp
open scoped RealInnerProductSpace

/-- A Killing field of Euclidean space with explicit derivative: `DK x` is antisymmetric. -/
structure IsKilling (K : Space → Space) (DK : Space → Space →L[ℝ] Space) : Prop where
  deriv : ∀ y, HasFDerivAt K (DK y) y
  antisymm : ∀ y v, ⟪DK y v, v⟫ = 0

/-- Symmetric flux structure: the torque of the magnetic force about the symmetry `K`
equals minus the rate of change of `ψ`, whose gradient is `G`. -/
@[expose] def SymmetricFlux (B G K : Space → Space) : Prop :=
  ∀ x v : Space, ⟪K x, cross v (B x)⟫ = -⟪G x, v⟫

/-- Symmetry defect on a region `S`. -/
@[expose] def SymmetricFluxDefectOn (B G K : Space → Space) (S : Set Space) (δ : ℝ) : Prop :=
  ∀ y ∈ S, ∀ w : Space, |⟪K y, cross w (B y)⟫ + ⟪G y, w⟫| ≤ δ * ‖w‖

/-- Exact symmetric structure has zero defect. -/
theorem SymmetricFlux.defect_zero {B G K : Space → Space} (h : SymmetricFlux B G K)
    (S : Set Space) : SymmetricFluxDefectOn B G K S 0 := by
  intro y _ w
  rw [h y w]; simp

/-- Noether momentum `m ⟪K(x), v⟫ + q ψ(x)` along an orbit. -/
@[expose] def noetherMomentum (m q : ℝ) (K : Space → Space) (ψ : Space → ℝ)
    (x v : ℝ → Space) (t : ℝ) : ℝ :=
  m * ⟪K (x t), v t⟫ + q * ψ (x t)

/-- Derivative of the Noether momentum: `q (⟪K, v × B⟫ + ⟪G, v⟫)`. -/
theorem noetherMomentum_hasDerivAt {m q : ℝ} {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (r : ℝ) :
    HasDerivAt (noetherMomentum m q K ψ x v)
      (q * (⟪K (x r), cross (v r) (B (x r))⟫ + ⟪G (x r), v r⟫)) r := by
  obtain ⟨a, ha, hlaw⟩ := h.newton r
  have hx := h.position r
  have hKx : HasDerivAt (fun s => K (x s)) (DK (x r) (v r)) r :=
    (hK.deriv (x r)).comp_hasDerivAt r hx
  have hin := hKx.inner ℝ ha
  have hp : HasDerivAt (fun s => ψ (x s)) ⟪G (x r), v r⟫ r :=
    (hψ (x r)).comp_hasDerivAt r hx
  change HasDerivAt (fun s => m * ⟪K (x s), v s⟫ + q * ψ (x s)) _ r
  convert (hin.const_mul m).add (hp.const_mul q) using 1
  have hanti := hK.antisymm (x r) (v r)
  have hma : m * ⟪K (x r), a⟫ = q * ⟪K (x r), cross (v r) (B (x r))⟫ := by
    rw [← inner_smul_right, hlaw, zero_add, inner_smul_right]
  rw [hanti, add_zero, hma]
  ring

/-- Conservation of the Noether momentum in a symmetric static magnetic field. -/
theorem noetherMomentum_conserved {m q : ℝ} {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : SymmetricFlux B G K) (s t : ℝ) :
    noetherMomentum m q K ψ x v s = noetherMomentum m q K ψ x v t := by
  have hd (r : ℝ) : HasDerivAt (noetherMomentum m q K ψ x v) 0 r := by
    have := noetherMomentum_hasDerivAt h hK hψ r
    rwa [hB, neg_add_cancel, mul_zero] at this
  refine is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => ?_) s t
  exact (hd r).deriv

/-- Momentum difference bound used by the bands. -/
private theorem momentum_diff_le {m : ℝ} (a b u w : Space) (hs : ‖u‖ = ‖w‖) :
    |m * (⟪a, w⟫ - ⟪b, u⟫)| ≤ |m| * ‖w‖ * (‖b‖ + ‖a‖) := by
  rw [abs_mul, mul_assoc]
  gcongr
  calc |⟪a, w⟫ - ⟪b, u⟫| ≤ |⟪a, w⟫| + |⟪b, u⟫| := abs_sub _ _
    _ ≤ ‖a‖ * ‖w‖ + ‖b‖ * ‖u‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖w‖ * (‖b‖ + ‖a‖) := by rw [hs]; ring

/-- Quantitative flux band from the Noether momentum. -/
theorem noether_flux_band {m q : ℝ} (hm : m ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : SymmetricFlux B G K) (t : ℝ) :
    |q| * |ψ (x t) - ψ (x 0)| ≤ |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) := by
  have hc := noetherMomentum_conserved h hK hψ hB 0 t
  unfold noetherMomentum at hc
  have e : q * (ψ (x t) - ψ (x 0)) = m * (⟪K (x 0), v 0⟫ - ⟪K (x t), v t⟫) := by linarith
  rw [← abs_mul, e]
  exact momentum_diff_le _ _ _ _ (speed_conserved hm h t 0)

/-- All-time confinement from a Noether symmetry. `hreg`: on `{ψ ≤ c}` the symmetry
field has norm at most `κ`; `hgap`: `ψ(x 0) + k (κ + ‖K(x 0)‖) ≤ c' < c` with normalized
rigidity `k = |m| ‖v 0‖ / |q|`. Then `ψ(x t) ≤ c'` for every real `t`. -/
theorem noether_orbit_trapped {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : SymmetricFlux B G K)
    {c' c κ : ℝ} (hcc : c' < c) (hκ : 0 ≤ κ) (hreg : ∀ y, ψ y ≤ c → ‖K y‖ ≤ κ)
    (hgap : ψ (x 0) + |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) ≤ c') (t : ℝ) :
    ψ (x t) ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hcont : Continuous fun s => ψ (x s) :=
    (continuous_iff_continuousAt.mpr fun y => (hψ y).continuousAt).comp
      h.continuous_position
  have hk : 0 ≤ |m| * ‖v 0‖ / |q| := by positivity
  refine trapped_of_gap hcont hcc ?_ (fun s hs => ?_) t
  · have : 0 ≤ |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) := by positivity
    linarith
  · have hb := noether_flux_band hm h hK hψ hB s
    have hn := hreg _ hs
    have h1 : ψ (x s) - ψ (x 0) ≤ |m| * ‖v 0‖ / |q| * (‖K (x s)‖ + ‖K (x 0)‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hqpos]
      nlinarith [le_abs_self (ψ (x s) - ψ (x 0))]
    have h2 : |m| * ‖v 0‖ / |q| * (‖K (x s)‖ + ‖K (x 0)‖) ≤
        |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    linarith

/-- Widened band under a symmetry defect, valid while the orbit stays in `S`. -/
theorem noether_approx_band {m q : ℝ} (hm : m ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {S : Set Space} {δ : ℝ}
    (hB : SymmetricFluxDefectOn B G K S δ) {t : ℝ} (ht : 0 ≤ t)
    (hin : ∀ s ∈ Set.Icc 0 t, x s ∈ S) :
    |q| * |ψ (x t) - ψ (x 0)| ≤
      |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) + |q| * δ * ‖v 0‖ * t := by
  have hbound : ∀ s ∈ Set.Icc 0 t,
      |q * (⟪K (x s), cross (v s) (B (x s))⟫ + ⟪G (x s), v s⟫)| ≤ |q| * δ * ‖v 0‖ := by
    intro s hs
    rw [abs_mul, mul_assoc, ← speed_conserved hm h s 0]
    exact mul_le_mul_of_nonneg_left (hB _ (hin s hs) _) (abs_nonneg q)
  have hdrift := invariant_drift (fun s _ => noetherMomentum_hasDerivAt h hK hψ s) hbound
    ⟨ht, le_rfl⟩
  unfold noetherMomentum at hdrift
  have e : q * (ψ (x t) - ψ (x 0)) = (m * ⟪K (x t), v t⟫ + q * ψ (x t) -
      (m * ⟪K (x 0), v 0⟫ + q * ψ (x 0))) + m * (⟪K (x 0), v 0⟫ - ⟪K (x t), v t⟫) := by
    ring
  rw [← abs_mul, e]
  have hang := momentum_diff_le (m := m) (K (x 0)) (K (x t)) (v t) (v 0)
    (speed_conserved hm h t 0)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |q| * δ * ‖v 0‖ * t + |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) :=
        add_le_add hdrift hang
    _ = _ := by ring

/-- Finite-time confinement under a symmetry defect on `{ψ ≤ c}`. -/
theorem noether_orbit_trapped_until {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0)
    {B G K : Space → Space} {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {c' c κ δ T : ℝ} (hcc : c' < c)
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hB : SymmetricFluxDefectOn B G K {y | ψ y ≤ c} δ) (hreg : ∀ y, ψ y ≤ c → ‖K y‖ ≤ κ)
    (hgap : ψ (x 0) + |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) + δ * ‖v 0‖ * T ≤ c') :
    ∀ t ∈ Set.Icc 0 T, ψ (x t) ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hcont : Continuous fun s => ψ (x s) :=
    (continuous_iff_continuousAt.mpr fun y => (hψ y).continuousAt).comp
      h.continuous_position
  have hk : 0 ≤ |m| * ‖v 0‖ / |q| := by positivity
  refine trapped_until hcont hcc ?_ (fun t ht hhist => ?_)
  · have : 0 ≤ |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) + δ * ‖v 0‖ * T := by positivity
    linarith
  · have hb := noether_approx_band hm h hK hψ hB ht.1 (fun s hs => hhist s hs)
    have hn := hreg _ (hhist t ⟨ht.1, le_rfl⟩)
    have h1 : ψ (x t) - ψ (x 0) ≤
        |m| * ‖v 0‖ / |q| * (‖K (x t)‖ + ‖K (x 0)‖) + δ * ‖v 0‖ * t := by
      have : |q| * (ψ (x t) - ψ (x 0)) ≤
          |q| * (|m| * ‖v 0‖ / |q| * (‖K (x t)‖ + ‖K (x 0)‖) + δ * ‖v 0‖ * t) := by
        rw [mul_add, ← mul_assoc, mul_div_cancel₀ _ hqpos.ne']
        nlinarith [le_abs_self (ψ (x t) - ψ (x 0))]
      exact le_of_mul_le_mul_left this hqpos
    have h2 : |m| * ‖v 0‖ / |q| * (‖K (x t)‖ + ‖K (x 0)‖) ≤
        |m| * ‖v 0‖ / |q| * (κ + ‖K (x 0)‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    have h3 : δ * ‖v 0‖ * t ≤ δ * ‖v 0‖ * T :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith

/-- A symmetric field is tangent to the level sets of `ψ`: `ψ` is a field-line first
integral, so its sublevel sets are also field-line barriers. -/
theorem SymmetricFlux.firstIntegral {B G K : Space → Space} {ψ : Space → ℝ}
    (hB : SymmetricFlux B G K) (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) :
    FirstIntegralOn B ψ Set.univ := by
  intro y _
  refine ⟨(hψ y).differentiableAt, ?_⟩
  rw [(hψ y).fderiv]
  have h := hB y (B y)
  have hc : cross (B y) (B y) = 0 := by simp [cross, cross_self]
  rw [hc, inner_zero_right, eq_comm, neg_eq_zero] at h
  simpa using h

/-! ## Constructing symmetric fields and standard Killing fields -/

/-- Triple-product expansion: `⟪K, v × (G × K)⟫ = ⟪K, G⟫ ⟪v, K⟫ - ‖K‖² ⟪v, G⟫`. -/
theorem inner_cross_cross (K G v : Space) :
    ⟪K, cross v (cross G K)⟫ = ⟪K, G⟫ * ⟪v, K⟫ - ‖K‖ ^ 2 * ⟪v, G⟫ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cross, crossProduct, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Algebraic construction: if `⟪K, G⟫ = 0` and `K ≠ 0`, the field
`|K|⁻² (G × K + F K)` has torque `-⟪G, v⟫` about `K`. -/
theorem symmetricFlux_of_cross (K G v : Space) (F : ℝ) (hKG : ⟪K, G⟫ = 0)
    (hK : ‖K‖ ^ 2 ≠ 0) :
    ⟪K, cross v ((‖K‖ ^ 2)⁻¹ • (cross G K + F • K))⟫ = -⟪G, v⟫ := by
  rw [← crossBilinear_apply, map_smul, map_add, map_smul, inner_smul_right, inner_add_right,
    inner_smul_right, crossBilinear_apply, crossBilinear_apply, inner_cross_self',
    inner_cross_cross, hKG, real_inner_comm v G]
  rw [mul_zero, add_zero, zero_mul, zero_sub, mul_neg, ← mul_assoc, inv_mul_cancel₀ hK,
    one_mul]

/-- The generator of rotations about the vertical axis, `v ↦ (-v₁, v₀, 0)`. -/
@[expose] def rotGen : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => toLp 2 ![-v 1, v 0, 0]
      map_add' := fun u w => by
        ext i; fin_cases i <;> simp; ring
      map_smul' := fun a u => by
        ext i; fin_cases i <;> simp }

/-- Coordinates of the rotation generator. -/
theorem rotGen_apply (v : Space) : rotGen v = toLp 2 ![-v 1, v 0, 0] := rfl

/-- The rotation generator is antisymmetric. -/
theorem rotGen_antisymm (v : Space) : ⟪rotGen v, v⟫ = 0 := by
  simp [rotGen_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Helical (screw) Killing field with pitch length `h`: `(-x₁, x₀, h)`. `h = 0` is the
rotation about the vertical axis. -/
@[expose] def helicalK (h : ℝ) (x : Space) : Space := rotGen x + toLp 2 ![0, 0, h]

/-- Coordinates of the helical Killing field. -/
theorem helicalK_apply (h : ℝ) (x : Space) : helicalK h x = toLp 2 ![-x 1, x 0, h] := by
  ext i; fin_cases i <;> simp [helicalK, rotGen_apply]

/-- Every screw motion generator is a Killing field. -/
theorem helicalK_killing (h : ℝ) : IsKilling (helicalK h) (fun _ => rotGen) where
  deriv _ := rotGen.hasFDerivAt.add_const _
  antisymm _ v := rotGen_antisymm v

/-- Translation along the vertical axis is a Killing field with zero derivative. -/
theorem translation_killing (e : Space) : IsKilling (fun _ => e) (fun _ => 0) where
  deriv _ := hasFDerivAt_const e _
  antisymm _ v := by simp

/-- Norm of the helical Killing field: `‖K‖² = x₀² + x₁² + h²`. -/
theorem helicalK_norm_sq (h : ℝ) (x : Space) :
    ‖helicalK h x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, helicalK_apply]
  simp [Fin.sum_univ_three]
  ring

/-- Sanity: for the rotation (`h = 0`) the Noether pairing is the vertical angular
momentum `(x × v)_z`, so `SymmetricFlux` recovers `AxisymmetricFlux`. -/
theorem helicalK_zero_inner (x w : Space) : ⟪helicalK 0 x, w⟫ = angularZ x w := by
  simp [helicalK_apply, angularZ, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- `SymmetricFlux` for the rotation is exactly `AxisymmetricFlux`. -/
theorem symmetricFlux_rotation_iff (B G : Space → Space) :
    SymmetricFlux B G (helicalK 0) ↔ AxisymmetricFlux B G := by
  simp only [SymmetricFlux, AxisymmetricFlux, helicalK_zero_inner]

end PlasmaLean.Kinetic
