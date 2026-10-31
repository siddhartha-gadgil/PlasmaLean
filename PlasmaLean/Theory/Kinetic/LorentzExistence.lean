/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.ODEContinuation
public import PlasmaLean.Theory.Kinetic.CanonicalMomentum
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Existence of Newton–Lorentz orbits for all time (audit finding MA-M2)

`LorentzOrbit m q 0 B x v` (in `FullOrbit`) is a property of a *supplied* trajectory. The
confinement theorems built on it (`orbit_trapped`, `SolovevAlpha.reactor_alpha_confined`) say
"every orbit with property X stays confined"; this file supplies the existence half.

The Newton–Lorentz system in a static magnetic field is the first-order system
`y' = lorentzField m q B y` on phase space `Space × Space`, `y = (x, v)`,
`lorentzField m q B (x, v) = (v, (q/m) v × B(x))`.

Results:

* `lorentzOrbit_of_flow`: a global solution of the first-order system is a `LorentzOrbit`
  (for `m ≠ 0`);
* `lorentzField_contDiffOn`: `lorentzField` is `C¹` on `V × Space` when `B` is `C¹` on `V`;
* interval conservation laws for solutions on a closed time interval `[a, b]`: speed
  (`speed_eq_Icc`) and, for an axisymmetric field, canonical angular momentum
  (`canonicalMomentum_eq_Icc`), the flux band and the trapping argument (`orbit_trapped_Icc`);
* `lorentz_apriori_univ`: for a field that is `C¹` on all of space, position and velocity
  stay in `closedBall x₀ (|v₀| T) × closedBall 0 |v₀|` up to time `T` (a priori bound);
* **`lorentzOrbit_exists`**: if `B` is `C¹` on all of space and `m ≠ 0`, then for every initial
  position `x₀` and velocity `v₀` there is a Lorentz orbit defined for all real times with
  `x 0 = x₀`, `v 0 = v₀`;
* **`lorentzOrbit_exists_of_apriori`**: the same for a field that is `C¹` only on an open set `V`
  (e.g. off the vertical axis), provided interval solutions from `(x₀, v₀)` are a priori trapped
  in compact subsets of `V × Space`;
* sanity: `lorentzOrbit_exists_uniform` (uniform field, any initial data).

Scope: the model is the non-relativistic Newton–Lorentz equation in a static magnetic field
(no electric field, no radiation or collisions). Uniqueness is not stated here.
-/

public section
noncomputable section
namespace PlasmaLean.Kinetic
open PlasmaLean.Fields PlasmaLean.Fields.ODEGlobal Set WithLp
open scoped RealInnerProductSpace

/-- The Newton–Lorentz vector field on phase space: `(x, v) ↦ (v, (q/m) v × B(x))`. -/
@[expose] def lorentzField (m q : ℝ) (B : Space → Space) (y : Space × Space) : Space × Space :=
  (y.2, (q / m) • cross y.2 (B y.1))

/-- First component of a curve in phase space: derivative of the position part. -/
theorem hasDerivAt_prod_fst {γ : ℝ → Space × Space} {y : Space × Space} {t : ℝ}
    (h : HasDerivAt γ y t) : HasDerivAt (fun s => (γ s).1) y.1 t :=
  (hasFDerivAt_fst (p := γ t)).comp_hasDerivAt t h

/-- Second component of a curve in phase space: derivative of the velocity part. -/
theorem hasDerivAt_prod_snd {γ : ℝ → Space × Space} {y : Space × Space} {t : ℝ}
    (h : HasDerivAt γ y t) : HasDerivAt (fun s => (γ s).2) y.2 t :=
  (hasFDerivAt_snd (p := γ t)).comp_hasDerivAt t h

/-- A global solution of the first-order Newton–Lorentz system is a Lorentz orbit. -/
theorem lorentzOrbit_of_flow {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    {γ : ℝ → Space × Space} (hγ : ∀ t, HasDerivAt γ (lorentzField m q B (γ t)) t) :
    LorentzOrbit m q (fun _ => 0) B (fun t => (γ t).1) (fun t => (γ t).2) where
  position t := (hasDerivAt_prod_fst (hγ t))
  newton t := ⟨_, (hasDerivAt_prod_snd (hγ t)), by
    simp only [lorentzField, zero_add, smul_smul]
    rw [mul_div_cancel₀ q hm]⟩

/-- Coordinates of the cross product. -/
theorem cross_coords (u w : Space) :
    cross u w 0 = u 1 * w 2 - u 2 * w 1 ∧ cross u w 1 = u 2 * w 0 - u 0 * w 2 ∧
      cross u w 2 = u 0 * w 1 - u 1 * w 0 := by
  simp [cross, cross_apply]

/-- The cross product is a smooth function of its two factors. -/
theorem contDiff_cross : ContDiff ℝ 1 (fun p : Space × Space => cross p.1 p.2) := by
  refine contDiff_piLp' 2 fun i => ?_
  have hc : ∀ (j : Fin 3), ContDiff ℝ 1 (fun p : Space × Space => p.1 j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).contDiff.comp contDiff_fst
  have hd : ∀ (j : Fin 3), ContDiff ℝ 1 (fun p : Space × Space => p.2 j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).contDiff.comp contDiff_snd
  fin_cases i
  · simp only [Fin.zero_eta, (cross_coords _ _).1]
    exact ((hc 1).mul (hd 2)).sub ((hc 2).mul (hd 1))
  · simp only [Fin.mk_one, (cross_coords _ _).2.1]
    exact ((hc 2).mul (hd 0)).sub ((hc 0).mul (hd 2))
  · simp only [Fin.reduceFinMk, (cross_coords _ _).2.2]
    exact ((hc 0).mul (hd 1)).sub ((hc 1).mul (hd 0))

/-- The Newton–Lorentz vector field is `C¹` on `V × Space` when `B` is `C¹` on `V`. -/
theorem lorentzField_contDiffOn (m q : ℝ) {B : Space → Space} {V : Set Space}
    (hB : ContDiffOn ℝ 1 B V) : ContDiffOn ℝ 1 (lorentzField m q B) (V ×ˢ univ) := by
  have hB' : ContDiffOn ℝ 1 (fun y : Space × Space => B y.1) (V ×ˢ univ) :=
    hB.comp contDiffOn_fst (fun y hy => hy.1)
  have hpair : ContDiffOn ℝ 1 (fun y : Space × Space => (y.2, B y.1)) (V ×ˢ univ) :=
    contDiffOn_snd.prodMk hB'
  have hcr : ContDiffOn ℝ 1 (fun y : Space × Space => cross y.2 (B y.1)) (V ×ˢ univ) :=
    contDiff_cross.comp_contDiffOn hpair
  exact contDiffOn_snd.prodMk (hcr.const_smul (q / m))

/-! ## Conservation laws on a closed time interval -/

/-- A real function with zero derivative on `[a, b]` is constant there. -/
theorem eq_of_hasDerivAt_zero_Icc {g : ℝ → ℝ} {a b : ℝ} (hg : ∀ t ∈ Icc a b, HasDerivAt g 0 t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : g s = g t := by
  have hcont : ContinuousOn g (Icc a b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun u hu => (hg u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
  rw [hc s hs, hc t ht]

/-- Speed is conserved along a solution of the Newton–Lorentz system on `[a, b]`. -/
theorem speed_eq_Icc {m q : ℝ} {B : Space → Space} {γ : ℝ → Space × Space} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (lorentzField m q B (γ t)) t) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : ‖(γ s).2‖ = ‖(γ t).2‖ := by
  have hd : ∀ r ∈ Icc a b, HasDerivAt (fun u => ‖(γ u).2‖ ^ 2) 0 r := by
    intro r hr
    have := (hasDerivAt_prod_snd (hγ r hr)).norm_sq
    convert this using 1
    simp [lorentzField, inner_smul_right, inner_cross_self]
  have h2 := eq_of_hasDerivAt_zero_Icc hd hs ht
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Canonical angular momentum `m (x × v)_z + q ψ(x)` is conserved along a solution on `[a, b]` in
an axisymmetric field (`AxisymmetricFlux B G`, `∇ψ = G`). -/
theorem canonicalMomentum_eq_Icc {m q : ℝ} (hm : m ≠ 0) {B G : Space → Space}
    {ψ : Space → ℝ} (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : AxisymmetricFlux B G)
    {γ : ℝ → Space × Space} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (lorentzField m q B (γ t)) t) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    m * angularZ (γ s).1 (γ s).2 + q * ψ (γ s).1 =
      m * angularZ (γ t).1 (γ t).2 + q * ψ (γ t).1 := by
  have hd : ∀ r ∈ Icc a b,
      HasDerivAt (fun u => m * angularZ (γ u).1 (γ u).2 + q * ψ (γ u).1) 0 r := by
    intro r hr
    have hx : HasDerivAt (fun u => (γ u).1) (γ r).2 r := (hasDerivAt_prod_fst (hγ r hr))
    have hv : HasDerivAt (fun u => (γ u).2) ((q / m) • cross (γ r).2 (B (γ r).1)) r :=
      (hasDerivAt_prod_snd (hγ r hr))
    set a := (q / m) • cross (γ r).2 (B (γ r).1) with ha
    have hL : HasDerivAt (fun u => angularZ (γ u).1 (γ u).2)
        ((γ r).1 0 * a 1 - (γ r).1 1 * a 0) r := by
      have := ((hasDerivAt_coord hx 0).mul (hasDerivAt_coord hv 1)).sub
        ((hasDerivAt_coord hx 1).mul (hasDerivAt_coord hv 0))
      convert this using 1
      · funext u; rfl
      · ring
    have hp : HasDerivAt (fun u => ψ (γ u).1) ⟪G (γ r).1, (γ r).2⟫ r := by
      have := (hψ (γ r).1).comp_hasDerivAt r hx
      simpa [Function.comp_def] using this
    convert (hL.const_mul m).add (hp.const_mul q) using 1
    have key := hB (γ r).1 (γ r).2
    unfold angularZ at key
    have e0 : a 0 = q / m * cross (γ r).2 (B (γ r).1) 0 := by simp [ha]
    have e1 : a 1 = q / m * cross (γ r).2 (B (γ r).1) 1 := by simp [ha]
    rw [e0, e1]
    field_simp
    linear_combination (-q) * key
  exact eq_of_hasDerivAt_zero_Icc hd hs ht

/-- Continuity trapping on an interval: a function continuous on `[a, b] ∋ 0`, at most `c'` at
time `0`, that never takes a value in the gap `(c', c]`, stays at most `c'` on `[a, b]`. -/
theorem trapped_of_gap_Icc {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (ha : a ≤ 0)
    (hb : 0 ≤ b) {c' c : ℝ} (hcc : c' < c) (h0 : f 0 ≤ c')
    (gap : ∀ t ∈ Icc a b, f t ≤ c → f t ≤ c') : ∀ t ∈ Icc a b, f t ≤ c' := by
  intro t ht
  by_contra hlt
  push Not at hlt
  have hct : c < f t := by
    by_contra hle
    exact absurd (gap t ht (not_lt.mp hle)) (not_le.mpr hlt)
  have hsub : uIcc 0 t ⊆ Icc a b := uIcc_subset_Icc ⟨ha, hb⟩ ht
  obtain ⟨s, hs, hfs⟩ := intermediate_value_uIcc (a := 0) (b := t) (hf.mono hsub)
    (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hct.le⟩))
  have := gap s (hsub hs) hfs.le
  linarith

/-- **Trapping on an interval** (interval version of `orbit_trapped`). In an axisymmetric field, a
solution of the Newton–Lorentz system on `[a, b] ∋ 0` with the band hypothesis
`ψ(x 0) + k (ρ + ‖x 0‖) ≤ c' < c` (`k = |m| ‖v 0‖ / |q|`, points with `ψ ≤ c` have norm `≤ ρ`)
satisfies `ψ(x t) ≤ c'` on `[a, b]`. -/
theorem orbit_trapped_Icc {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {B G : Space → Space}
    {ψ : Space → ℝ} (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : AxisymmetricFlux B G)
    {c' c ρ : ℝ} (hcc : c' < c) (hρ : 0 ≤ ρ) (hreg : ∀ y, ψ y ≤ c → ‖y‖ ≤ ρ)
    {γ : ℝ → Space × Space} {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (lorentzField m q B (γ t)) t)
    (hgap : ψ (γ 0).1 + |m| * ‖(γ 0).2‖ / |q| * (ρ + ‖(γ 0).1‖) ≤ c') :
    ∀ t ∈ Icc a b, ψ (γ t).1 ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have h0m : (0 : ℝ) ∈ Icc a b := ⟨ha, hb⟩
  have hcont : ContinuousOn (fun s => ψ (γ s).1) (Icc a b) := fun s hs =>
    ((hψ _).continuousAt.comp (hasDerivAt_prod_fst (hγ s hs)).continuousAt).continuousWithinAt
  have hk : 0 ≤ |m| * ‖(γ 0).2‖ / |q| := by positivity
  refine trapped_of_gap_Icc hcont ha hb hcc ?_ (fun s hs hsc => ?_)
  · have : 0 ≤ |m| * ‖(γ 0).2‖ / |q| * (ρ + ‖(γ 0).1‖) := by positivity
    linarith
  · -- the flux band from conservation of canonical momentum and speed
    have hc := canonicalMomentum_eq_Icc hm hψ hB hγ h0m hs
    have hsp := speed_eq_Icc hγ hs h0m
    have e : q * (ψ (γ s).1 - ψ (γ 0).1) =
        m * (angularZ (γ 0).1 (γ 0).2 - angularZ (γ s).1 (γ s).2) := by linarith
    have hband : |q| * |ψ (γ s).1 - ψ (γ 0).1| ≤ |m| * ‖(γ 0).2‖ * (‖(γ s).1‖ + ‖(γ 0).1‖) := by
      rw [← abs_mul, e, abs_mul, mul_assoc]
      gcongr
      calc |angularZ (γ 0).1 (γ 0).2 - angularZ (γ s).1 (γ s).2|
          ≤ |angularZ (γ 0).1 (γ 0).2| + |angularZ (γ s).1 (γ s).2| := abs_sub _ _
        _ ≤ ‖(γ 0).1‖ * ‖(γ 0).2‖ + ‖(γ s).1‖ * ‖(γ s).2‖ :=
            add_le_add (abs_angularZ_le _ _) (abs_angularZ_le _ _)
        _ = ‖(γ 0).2‖ * (‖(γ s).1‖ + ‖(γ 0).1‖) := by rw [hsp]; ring
    have hn := hreg _ hsc
    have h1 : ψ (γ s).1 - ψ (γ 0).1 ≤ |m| * ‖(γ 0).2‖ / |q| * (‖(γ s).1‖ + ‖(γ 0).1‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hqpos]
      nlinarith [le_abs_self (ψ (γ s).1 - ψ (γ 0).1)]
    have h2 : |m| * ‖(γ 0).2‖ / |q| * (‖(γ s).1‖ + ‖(γ 0).1‖) ≤
        |m| * ‖(γ 0).2‖ / |q| * (ρ + ‖(γ 0).1‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    linarith

/-! ## Global existence -/

/-- **A priori bound for a globally `C¹` field.** Up to time `T`, a solution of the Newton–Lorentz
system from `(x₀, v₀)` stays in `closedBall x₀ (|v₀| T) × closedBall 0 |v₀|` (speed is conserved
and the position moves at that speed). -/
theorem lorentz_apriori_univ (m q : ℝ) (B : Space → Space) (x₀ v₀ : Space) :
    APrioriBounded (lorentzField m q B) univ (x₀, v₀) := by
  intro T
  refine ⟨Metric.closedBall x₀ (‖v₀‖ * T) ×ˢ Metric.closedBall 0 ‖v₀‖,
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), subset_univ _,
    fun c hc γ h0 hγ t ht => ?_⟩
  have h0m : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith [hc.1], hc.1⟩
  have hsp : ∀ s ∈ Icc (-c) c, ‖(γ s).2‖ = ‖v₀‖ := fun s hs => by
    rw [speed_eq_Icc hγ hs h0m, h0]
  refine ⟨?_, by simp [hsp t ht]⟩
  have hmv := (convex_Icc (-c) c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => (γ s).1) (f' := fun s => (γ s).2) (C := ‖v₀‖)
    (fun s hs => (hasDerivAt_prod_fst (hγ s hs)).hasDerivWithinAt) (fun s hs => (hsp s hs).le)
    h0m ht
  have h0x : (γ 0).1 = x₀ := by rw [h0]
  rw [h0x, sub_zero, Real.norm_eq_abs] at hmv
  rw [Metric.mem_closedBall, dist_eq_norm]
  have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1, hc.2], by linarith [ht.2, hc.2]⟩
  calc ‖(γ t).1 - x₀‖ ≤ ‖v₀‖ * |t| := hmv
    _ ≤ ‖v₀‖ * T := mul_le_mul_of_nonneg_left habs (norm_nonneg _)

/-- **Global existence of Newton–Lorentz orbits for a `C¹` field.** If `B` is `C¹` on all of space
and `m ≠ 0`, then for every initial position `x₀` and velocity `v₀` there is a Lorentz orbit
`(x, v) : ℝ → Space × Space`, defined for all real times, with `x 0 = x₀` and `v 0 = v₀`. -/
theorem lorentzOrbit_exists {m q : ℝ} (hm : m ≠ 0) {B : Space → Space} (hB : ContDiff ℝ 1 B)
    (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x v ∧ x 0 = x₀ ∧ v 0 = v₀ := by
  have hf : ContDiffOn ℝ 1 (lorentzField m q B) univ := by
    simpa using lorentzField_contDiffOn m q (V := univ) hB.contDiffOn
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_of_apriori isOpen_univ hf (mem_univ (x₀, v₀))
    (lorentz_apriori_univ m q B x₀ v₀)
  exact ⟨_, _, lorentzOrbit_of_flow hm hγ, by rw [hγ0], by rw [hγ0]⟩

/-- **Global existence under an a priori bound.** If `B` is `C¹` on an open set `V ∋ x₀`, `m ≠ 0`,
and every solution of the Newton–Lorentz system from `(x₀, v₀)` on a finite interval is a priori
trapped in a compact subset of `V × Space`, then there is a Lorentz orbit defined for all real times
with `x 0 = x₀`, `v 0 = v₀`. -/
theorem lorentzOrbit_exists_of_apriori {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    {V : Set Space} (hV : IsOpen V) (hB : ContDiffOn ℝ 1 B V) {x₀ v₀ : Space} (hx₀ : x₀ ∈ V)
    (hbd : APrioriBounded (lorentzField m q B) (V ×ˢ univ) (x₀, v₀)) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x v ∧ x 0 = x₀ ∧ v 0 = v₀ := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_of_apriori (hV.prod isOpen_univ)
    (lorentzField_contDiffOn m q hB) (mk_mem_prod hx₀ (mem_univ v₀)) hbd
  exact ⟨_, _, lorentzOrbit_of_flow hm hγ, by rw [hγ0], by rw [hγ0]⟩

/-- Sanity (concrete instance): in the uniform field `B₀ e_z` every initial condition starts a
Lorentz orbit for all time (compare the explicit helices of `helix_orbit`). -/
theorem lorentzOrbit_exists_uniform {m q : ℝ} (hm : m ≠ 0) (B₀ : ℝ) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) (uniformField B₀) x v ∧ x 0 = x₀ ∧
      v 0 = v₀ :=
  lorentzOrbit_exists hm contDiff_const x₀ v₀

end PlasmaLean.Kinetic
