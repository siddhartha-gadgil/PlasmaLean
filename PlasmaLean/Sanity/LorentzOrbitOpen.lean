/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.LorentzOrbitOpen
public import PlasmaLean.Sanity.CurvatureObstruction

/-!
# Sanity checks for `Theory/Kinetic/LorentzOrbitOpen`

Fields used: the field of a straight wire `wireField = (−y, x, 0) / (x² + y²)` on
`wireRegion = {x² + y² > 0}` (`Sanity/CurvatureObstruction`), which is `C²` there, is singular
on the axis and has no scalar potential on its domain (`wireField_no_potential` in
`Sanity/FormTopology`); the non-Lipschitz electric field `rootField y = √|y₀| e_x`.

* Accepted (wire field, no electric field). `wire_orbit_exists_local`: for `m ≠ 0`, from every
  point off the axis, with every velocity, at every initial time, there is a Lorentz orbit on
  an open interval of times that stays off the axis. `wire_orbit_unique`: two orbits on an
  interval of times that stay off the axis and agree at one time agree on the interval.
  `wire_speed_eq`: the speed is constant along such an orbit. None of the earlier theorems
  applies: the field is not `C¹` on all of space.
* Accepted (explicit orbit). `wire_rest_orbit`: a particle at rest off the axis is an orbit
  for all times; `wire_rest_unique`: every orbit that starts at rest and stays off the axis
  is this one (position constant, velocity zero).
* Rejected (regularity matters). For `E = rootField`, `B = 0`, `m = q = 1` the equation is
  `x'' = √|x|`. `rootField_rest_orbit` (rest at the origin) and `rootField_quartic_orbit`
  (`x = (t⁴/144) e_x`) are two orbits for all times with the same position and velocity at
  time `0` (`rootField_two_orbits`). Hence `rootField` is not `C¹` on all of space
  (`rootField_not_contDiff`, proved FROM the uniqueness theorem), and the regularity hypothesis
  of `lorentzOrbitOn_unique_of_contDiffOn` cannot be dropped.
* Rejected (`m = 0`). `massless_two_orbits`: for `m = 0` with `E = B = 0` Newton's law is
  `0 = 0`, and both rest and `x = t² e_x` are orbits with the same initial data; the hypothesis
  `m ≠ 0` of the uniqueness theorem cannot be dropped.

Not proved here: an explicit moving orbit in the wire field, and an application of the
confinement theorem `lorentzOrbit_existsUnique_of_confined` to a concrete non-trivial field.
-/

@[expose] public section

namespace PlasmaLean.Sanity.LorentzOrbitOpen

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Sanity
open Set WithLp
open scoped RealInnerProductSpace

/-- The cross product with the zero vector on the right vanishes. -/
theorem cross_zero_right (u : Space) : cross u 0 = 0 := by
  simp [cross]

/-- The cross product with the zero vector on the left vanishes. -/
theorem cross_zero_left (u : Space) : cross 0 u = 0 := by
  simp [cross]

/-! ## The wire field -/

/-- The wire field is `C¹` on the complement of the axis. -/
theorem wireField_contDiffOn_one : ContDiffOn ℝ 1 wireField wireRegion :=
  wireField_vacuum.contDiffOn.of_le (by norm_num)

/-- Accepted: local existence of Lorentz orbits in the wire field, from every point off the
axis with every velocity, staying off the axis. -/
theorem wire_orbit_exists_local {m : ℝ} (hm : m ≠ 0) (q : ℝ) {x₀ : Space}
    (hx₀ : x₀ ∈ wireRegion) (v₀ : Space) (t₀ : ℝ) :
    ∃ ε > 0, ∃ x v : ℝ → Space,
      LorentzOrbitOn m q (fun _ => 0) wireField x v (Ioo (t₀ - ε) (t₀ + ε)) ∧
        x t₀ = x₀ ∧ v t₀ = v₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), x t ∈ wireRegion :=
  lorentzOrbitOn_exists_local_of_contDiffOn hm isOpen_wireRegion contDiffOn_const
    wireField_contDiffOn_one hx₀ v₀ t₀

/-- Accepted: uniqueness of Lorentz orbits in the wire field among orbits that stay off the
axis, on any interval of times. -/
theorem wire_orbit_unique {m : ℝ} (hm : m ≠ 0) (q : ℝ) {s : Set ℝ} (hs : s.OrdConnected)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbitOn m q (fun _ => 0) wireField x₁ v₁ s)
    (h₂ : LorentzOrbitOn m q (fun _ => 0) wireField x₂ v₂ s)
    (hU₁ : ∀ t ∈ s, x₁ t ∈ wireRegion) (hU₂ : ∀ t ∈ s, x₂ t ∈ wireRegion)
    (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀) : EqOn x₁ x₂ s ∧ EqOn v₁ v₂ s :=
  lorentzOrbitOn_unique_of_contDiffOn hm isOpen_wireRegion contDiffOn_const
    wireField_contDiffOn_one hs ht₀ h₁ h₂ hU₁ hU₂ hx hv

/-- Accepted: the speed is constant along a Lorentz orbit in the wire field that stays off the
axis. -/
theorem wire_speed_eq {m : ℝ} (hm : m ≠ 0) (q : ℝ) {s : Set ℝ} (hs : s.OrdConnected)
    {x v : ℝ → Space} (h : LorentzOrbitOn m q (fun _ => 0) wireField x v s)
    (hxU : ∀ t ∈ s, x t ∈ wireRegion) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖v a‖ = ‖v b‖ :=
  h.speed_eq_of_electric_zero hm hs (fun _ _ => rfl) hxU ha hb

/-- Accepted (explicit orbit): a particle at rest is a Lorentz orbit for all times in any
magnetic field without electric field, in particular in the wire field. -/
theorem wire_rest_orbit (m q : ℝ) (x₀ : Space) :
    LorentzOrbit m q (fun _ => 0) wireField (fun _ => x₀) (fun _ => 0) where
  position t := hasDerivAt_const t x₀
  newton t := ⟨0, hasDerivAt_const t 0, by simp [cross_zero_left]⟩

/-- Accepted: an orbit in the wire field that starts at rest off the axis and stays off the
axis remains at rest. -/
theorem wire_rest_unique {m : ℝ} (hm : m ≠ 0) (q : ℝ) {s : Set ℝ} (hs : s.OrdConnected)
    (h0 : (0 : ℝ) ∈ s) {x v : ℝ → Space} (h : LorentzOrbitOn m q (fun _ => 0) wireField x v s)
    (hxU : ∀ t ∈ s, x t ∈ wireRegion) (hv : v 0 = 0) :
    (∀ t ∈ s, x t = x 0) ∧ ∀ t ∈ s, v t = 0 := by
  have key := wire_orbit_unique hm q hs h0 h ((wire_rest_orbit m q (x 0)).on s) hxU
    (fun _ _ => hxU 0 h0) rfl hv
  exact ⟨fun t ht => key.1 ht, fun t ht => key.2 ht⟩

/-! ## A non-Lipschitz electric field: two orbits from the same data -/

/-- The first Cartesian unit vector. -/
noncomputable def ex : Space := EuclideanSpace.single 0 1

/-- The electric field `√|y₀| e_x`; it is continuous but not Lipschitz near `y₀ = 0`. -/
noncomputable def rootField (y : Space) : Space := √|y 0| • ex

/-- The first coordinate of a multiple of `e_x`. -/
theorem smul_ex_zero (c : ℝ) : (c • ex) 0 = c := by
  simp [ex]

/-- Rejected fixture, first orbit: rest at the origin is a Lorentz orbit of `rootField` with
no magnetic field, `m = q = 1`. -/
theorem rootField_rest_orbit :
    LorentzOrbit 1 1 rootField (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  position t := hasDerivAt_const t 0
  newton t := ⟨0, hasDerivAt_const t 0, by simp [rootField, cross_zero_right]⟩

/-- Rejected fixture, second orbit: `x = (t⁴/144) e_x`, `v = (t³/36) e_x` is a Lorentz orbit of
`rootField` with no magnetic field, `m = q = 1` (`x'' = t²/12 = √|x|`). -/
theorem rootField_quartic_orbit :
    LorentzOrbit 1 1 rootField (fun _ => 0) (fun t => (t ^ 4 / 144) • ex)
      (fun t => (t ^ 3 / 36) • ex) where
  position t := by
    have h := ((hasDerivAt_pow 4 t).div_const 144).smul_const ex
    convert h using 2
    simp only [Nat.cast_ofNat]
    ring
  newton t := by
    refine ⟨(t ^ 2 / 12) • ex, ?_, ?_⟩
    · have h := ((hasDerivAt_pow 3 t).div_const 36).smul_const ex
      convert h using 2
      simp only [Nat.cast_ofNat]
      ring
    · have hs : √|t ^ 4 / 144| = t ^ 2 / 12 := by
        rw [abs_of_nonneg (by positivity), show t ^ 4 / 144 = (t ^ 2 / 12) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      simp only [rootField, smul_ex_zero, hs, cross_zero_right, add_zero, one_smul]

/-- **Rejected: non-uniqueness for a non-Lipschitz electric field.** For `E = rootField`,
`B = 0`, `m = q = 1` there are two different Lorentz orbits for all times with the same
position and velocity at time `0`. -/
theorem rootField_two_orbits :
    ∃ x₁ v₁ x₂ v₂ : ℝ → Space, LorentzOrbit 1 1 rootField (fun _ => 0) x₁ v₁ ∧
      LorentzOrbit 1 1 rootField (fun _ => 0) x₂ v₂ ∧ x₁ 0 = x₂ 0 ∧ v₁ 0 = v₂ 0 ∧
        x₁ 1 ≠ x₂ 1 := by
  refine ⟨_, _, _, _, rootField_rest_orbit, rootField_quartic_orbit, by simp, by simp, ?_⟩
  intro h
  have h0 := congrArg (fun y : Space => y 0) h
  simp only [smul_ex_zero] at h0
  norm_num at h0

/-- **Rejected: `rootField` is not `C¹`.** Otherwise `lorentzOrbitOn_unique_of_contDiffOn` (with
`U = Space`) would make the two orbits of `rootField_two_orbits` equal. So the regularity
hypothesis of the uniqueness theorem cannot be dropped. -/
theorem rootField_not_contDiff : ¬ ContDiff ℝ 1 rootField := by
  intro hE
  obtain ⟨x₁, v₁, x₂, v₂, h₁, h₂, hx, hv, hne⟩ := rootField_two_orbits
  have key := lorentzOrbitOn_unique_of_contDiffOn (U := univ) one_ne_zero isOpen_univ
    hE.contDiffOn contDiffOn_const ordConnected_univ (mem_univ (0 : ℝ)) (h₁.on univ)
    (h₂.on univ) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) hx hv
  exact hne (key.1 (mem_univ 1))

/-! ## The degenerate case `m = 0` -/

/-- **Rejected: `m = 0`.** With `m = 0` and `E = B = 0` Newton's law reads `0 = 0`: rest at the
origin and `x = t² e_x` are two different Lorentz orbits with the same position and velocity
at time `0`, although the fields are smooth. So the hypothesis `m ≠ 0` of the uniqueness
theorem cannot be dropped. -/
theorem massless_two_orbits (q : ℝ) :
    ∃ x₁ v₁ x₂ v₂ : ℝ → Space, LorentzOrbit 0 q (fun _ => 0) (fun _ => 0) x₁ v₁ ∧
      LorentzOrbit 0 q (fun _ => 0) (fun _ => 0) x₂ v₂ ∧ x₁ 0 = x₂ 0 ∧ v₁ 0 = v₂ 0 ∧
        x₁ 1 ≠ x₂ 1 := by
  refine ⟨fun _ => 0, fun _ => 0, fun t => (t ^ 2) • ex, fun t => (2 * t) • ex,
    ⟨fun t => hasDerivAt_const t 0,
      fun t => ⟨0, hasDerivAt_const t 0, by simp [cross_zero_right]⟩⟩,
    ⟨fun t => ?_, fun t => ⟨(2 : ℝ) • ex, ?_, by simp [cross_zero_right]⟩⟩, by simp, by simp,
    ?_⟩
  · have h := (hasDerivAt_pow 2 t).smul_const ex
    convert h using 2
    simp
  · have h := ((hasDerivAt_id t).const_mul 2).smul_const ex
    convert h using 2
    all_goals simp
  · intro h
    have h0 := congrArg (fun y : Space => y 0) h
    simp only [smul_ex_zero] at h0
    norm_num at h0

end PlasmaLean.Sanity.LorentzOrbitOpen
