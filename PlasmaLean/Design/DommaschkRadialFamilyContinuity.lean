/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialActionAlternative
public import PlasmaLean.Design.DommaschkCompactLaunchPhases
public import PlasmaLean.Theory.Fields.TrajectoryFamilyContinuity

/-! # Continuity of the physical strength and arclength over a radial family of signed paths -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialFamilyContinuity

open Set Fields Contract Forms Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkRadialActionAlternative DommaschkMirrorLaunch DommaschkFirstMirrorWell
open DommaschkJacobian (euclideanFlow)
open DommaschkSignedTraceDomain DommaschkCartesianAngleFlow DommaschkCompactLaunchPhases
open DommaschkNativeWellAction Kinetic.FirstWellContinuation Kinetic.MirrorActionEnvelope
open Kinetic.MirrorHeightAction

/-- Cartesian image of the known regular cylindrical box over the chosen angular interval. -/
def window (a b : ℝ) : Set Space :=
  (fun q : ℝ × ℝ × ℝ => cylPoint q.1 q.2.1 q.2.2) ''
    (Icc (7 / 8) 1 ×ˢ (Icc a b ×ˢ Icc (- (5 / 64)) (5 / 64)))

theorem compact_window (a b : ℝ) : IsCompact (window a b) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
    (continuous_cylinder continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd))

theorem window_regular {a b : ℝ} : window a b ⊆ regular := by
  rintro _ ⟨⟨r,t,z⟩, ⟨hr, _, hz⟩, rfl⟩
  let p : Plane := coordinates.symm ![r,z]
  exact in_regular (p := p) ⟨hr, abs_le.mpr hz⟩ t

theorem point_mem {a b t : ℝ} {y : ℝ → Plane} (ht : t ∈ Icc a b) (reg : Region (y t)) :
    point y t ∈ window a b :=
  ⟨⟨y t 0, t, y t 1⟩, ⟨reg.1, ht, abs_le.mp reg.2⟩, rfl⟩

/-- Enclosed physical equations on the full window. A trace carried beyond its end caps
has the required ordinary derivatives there. -/
structure Enclosed (y : ℝ → Plane) (a b : ℝ) : Prop where
  ode : ∀ t ∈ Icc a b, HasDerivAt y (euclideanFlow 0 1 t (y t)) t
  region : ∀ t ∈ Icc a b, Region (y t)

theorem Enclosed.cartesian {y : ℝ → Plane} {a b t : ℝ} (e : Enclosed y a b) (ht : t ∈ Icc a b) :
    HasDerivAt (point y) (velocity (point y t)) t :=
  cartesian_ode (e.ode t ht) (e.region t ht)

theorem Enclosed.density_eq {y : ℝ → Plane} {a b t : ℝ} (e : Enclosed y a b) (ht : t ∈ Icc a b) :
    density y t = ‖velocity (point y t)‖ :=
  congrArg norm (e.cartesian ht).deriv

theorem Enclosed.mono {y : ℝ → Plane} {a b A B : ℝ} (e : Enclosed y A B)
    (sub : Icc a b ⊆ Icc A B) : Enclosed y a b :=
  ⟨fun t ht => e.ode t (sub ht), fun t ht => e.region t (sub ht)⟩

/-- The original radial birth varies continuously at every fixed launch phase. -/
theorem continuous_birth (uC zC uA zA : FA) (φ : ℝ) :
    Continuous (fun u : Radius => location uC zC uA zA u φ) := by
  have blendR (A C : ℝ) : Continuous fun u : Radius => blend u A C :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  exact continuous_cylinder (blendR _ _) continuous_const (blendR _ _)

set_option maxRecDepth 12000 in
/-- The physical ODE and the common spatial enclosure supply joint continuity of both
observables. Individual traces can be chosen independently at each radius. -/
theorem capped_of_births {Y : Radius → ℝ → Plane} {uC zC uA zA : FA} {φ b : ℝ}
    (pos : 0 < b) (time : φ ∈ Icc (-b) b)
    (born : ∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ))
    (paths : ∀ u, Enclosed (Y u) (-b) b) (low : ∀ u, field (Y u) 0 < level)
    (back : ∀ u, level < field (Y u) (-b)) (fwd : ∀ u, level < field (Y u) b) :
    CappedFamily (fun u => field (Y u)) (fun u => density (Y u)) (fun _ => level) b := by
  have cb : Continuous fun u => point (Y u) φ :=
    (continuous_birth uC zC uA zA φ).congr fun u => by
      unfold point location
      rw [born u]
      rfl
  have joint := TrajectoryFamily.continuousOn_of_enclosed (V := velocity) (compact_window (-b) b)
    (fun _ hx => velocity_smooth (window_regular hx)) time cb
    (fun u t ht => (paths u).cartesian ht) (fun u t ht => point_mem ht ((paths u).region t ht))
  have reg (q : Radius × ℝ) (hq : q ∈ (univ : Set Radius) ×ˢ Icc (-b) b) :
      point (Y q.1) q.2 ∈ regular := in_regular ((paths q.1).region q.2 hq.2) q.2
  refine ⟨pos, continuous_const, ?_, ?_, low, back, fwd⟩
  · intro q hq
    change ContinuousWithinAt (fun z : Radius × ℝ => ‖B (point (Y z.1) z.2)‖) _ q
    exact (strength_smooth (reg q hq)).continuousAt.comp_continuousWithinAt
      (f := fun z : Radius × ℝ => point (Y z.1) z.2) (joint q hq)
  · have cv : ContinuousOn (fun q : Radius × ℝ => ‖velocity (point (Y q.1) q.2)‖)
        (univ ×ˢ Icc (-b) b) := fun q hq =>
      (velocity_smooth (reg q hq)).continuousAt.norm.comp_continuousWithinAt
        (f := fun z : Radius × ℝ => point (Y z.1) z.2) (joint q hq)
    exact cv.congr fun q hq => ((paths q.1).density_eq hq.2)

/-- Two independently selected field lines issuing from the same position agree on
the common window, including both endpoints. Their true arclength densities agree too. -/
theorem Enclosed.agree {y z : ℝ → Plane} {a b φ : ℝ}
    (p : Enclosed y a b) (q : Enclosed z a b) (time : φ ∈ Icc a b) (born : y φ = z φ) :
    EqOn (field y) (field z) (Icc a b) ∧ EqOn (density y) (density z) (Icc a b) := by
  obtain ⟨K, lip⟩ := TrajectoryFamily.compact_lipschitz (V := velocity) (compact_window a b)
    (fun _ hx => velocity_smooth (window_regular hx))
  have pos : point y φ = point z φ := by simp only [point, born]
  have common : EqOn (point y) (point z) (Icc a b) := by
    intro t ht
    have bound := TrajectoryFamily.dist_from_birth lip time ht
      (fun s hs => p.cartesian hs) (fun s hs => q.cartesian hs)
      (fun s hs => point_mem hs (p.region s hs)) (fun s hs => point_mem hs (q.region s hs))
    rw [pos, dist_self, zero_mul] at bound
    exact dist_le_zero.mp bound
  constructor
  · intro t ht
    exact congrArg (fun x => ‖B x‖) (common ht)
  · intro t ht
    rw [p.density_eq ht, q.density_eq ht, common ht]

/-- A well proved on one trajectory transfers to another original trajectory on
their overlap. Neither field line needs to agree outside the certified overlap. -/
theorem transfer_well {y z : ℝ → Plane} {a b φ l r H : ℝ}
    (p : Enclosed y a b) (q : Enclosed z a b) (time : φ ∈ Icc a b) (born : y φ = z φ)
    (well : LaunchWell (field y) 0 H l r) (cover : Icc l r ⊆ Icc a b) :
    LaunchWell (field z) 0 H l r ∧
      action (field y) (density y) l r H = action (field z) (density z) l r H := by
  obtain ⟨cf,cw⟩ := p.agree q time born
  have lr := (well.left_lt.trans well.lt_right).le
  constructor
  · exact ⟨well.left_lt, well.lt_right, (cf (cover (left_mem_Icc.mpr lr))).symm.trans well.left_hit,
      (cf (cover (right_mem_Icc.mpr lr))).symm.trans well.right_hit,
      fun t ht => (cf (cover (Ioo_subset_Icc_self ht))) ▸ well.accessible t ht⟩
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le lr] at ht
    simp only [cf (cover ht), cw (cover ht)]

/-- At the QA2R upper height, comparing independent endpoint solutions requires only
their overlap through the first mirrors. The outer caps of the interpolating family
may lie farther along the clock than those independently certified endpoint traces. -/
theorem alternative_of_passages {uC zC uA zA : FA} {φ b l r L R : ℝ} {y z : ℝ → Plane}
    {Y : Radius → ℝ → Plane} (wide : 327 / 64 ≤ b)
    (time : φ ∈ Icc (-(327 / 64)) (327 / 64))
    (born : ∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ))
    (py : Enclosed y (-(327 / 64)) (327 / 64)) (pz : Enclosed z (-(327 / 64)) (327 / 64))
    (byl : y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ))
    (byr : z φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ))
    (wy : LaunchWell (field y) 0 level l r) (wz : LaunchWell (field z) 0 level L R)
    (sy : Icc l r ⊆ Icc (-(327 / 64)) (327 / 64))
    (sz : Icc L R ⊆ Icc (-(327 / 64)) (327 / 64))
    (lo : action (field y) (density y) l r level < target)
    (hi : target < action (field z) (density z) L R level)
    (paths : ∀ u, Enclosed (Y u) (-b) b) (early : ∀ u, field (Y u) 0 < level)
    (back : ∀ u, level < field (Y u) (-b)) (fwd : ∀ u, level < field (Y u) b) :
    Alternative Y := by
  have within := Icc_subset_Icc (neg_le_neg wide) wide
  obtain ⟨left, massL⟩ := transfer_well py ((paths inner).mono within) time
    (byl.trans (born inner).symm) wy sy
  obtain ⟨right, massR⟩ := transfer_well pz ((paths outer).mono within) time
    (byr.trans (born outer).symm) wz sz
  apply of_endpoint_wells left right (massL ▸ lo) (massR ▸ hi) Y b rfl rfl
  exact capped_of_births (by linarith) (within time) born paths early back fwd

/-- A nonzero time derivative on both first contacts rules out the grazing alternative.
It suffices to check the two contacts on each curve. -/
theorem prescribed_of_regular {Y : Radius → ℝ → Plane} (alt : Alternative Y)
    (simple : ∀ u l r, LaunchWell (field (Y u)) 0 level l r →
      deriv (field (Y u)) l ≠ 0 ∧ deriv (field (Y u)) r ≠ 0) :
    ∃ (u : Radius) (l r : ℝ), (u : ℝ) ∈ Ioo (47 / 100) (239 / 500) ∧
      LaunchWell (field (Y u)) 0 level l r ∧
      action (field (Y u)) (density (Y u)) l r level = target := by
  rcases alt with found | ⟨u, l, r, well, left | right⟩
  · exact found
  · exact False.elim ((simple u l r well).1 left.deriv_eq_zero)
  · exact False.elim ((simple u l r well).2 right.deriv_eq_zero)

end PlasmaLean.Design.DommaschkRadialFamilyContinuity
