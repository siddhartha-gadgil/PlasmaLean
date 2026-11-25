/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSharpFlightBounds
public import PlasmaLean.Design.DommaschkPhysicalActionExit
public import PlasmaLean.Theory.Kinetic.MirrorActionTransverse

/-! # Flight time and action response on the completed outer physical face -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOuterFaceFlight
open Set MeasureTheory Certificates.PositionFrameSlabs
open DommaschkNativeWellAction DommaschkRadialFamilyContinuity DommaschkFirstMirrorLaunchSign
open DommaschkMirrorTubeCrossing DommaschkSignedTraceDensity DommaschkPhysicalActionPanel
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightBand Kinetic.MirrorHeightAction
open Kinetic.MirrorActionFlight

abbrev core : ℝ := 317 / 64
abbrev limit : ℝ := 327 / 64
abbrev H := Icc (height false : ℝ) (height true : ℝ)
abbrev Side (f : ℝ → ℝ) := Branch f core limit (height false) (height true) (1 / 400)
def mass (y : ℝ → Plane) := action (field y) (density y) (-limit) limit

private theorem clock_bound {f w : ℝ → ℝ} (p : Side f) (h : H)
    (near : level - 1 / 100000 ≤ (h : ℝ))
    (weights : ∀ t ∈ Ioo 0 (p.time h), w t ≤ 5 / 4)
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * ((h : ℝ) - f t)))
      volume 0 (p.time h)) : oneWayBounceTime w f h 0 (p.time h) < 226 := by
  have ord : (height false : ℝ) ≤ height true := by norm_num [height]
  let s := p.time ⟨height false, le_rfl, ord⟩
  let r := p.time h
  have slow : s ∈ Ioo core limit := p.interior_time _
  have fast : r ∈ Ioo core limit := p.interior_time _
  have gap (t : ℝ) (ht : t ∈ Ioo 0 s) : (1 / 32 : ℝ)^2 ≤ 2 * ((h : ℝ) - f t) := by
    have low := p.before ⟨height false, le_rfl, ord⟩ t ⟨ht.1.le, ht.2⟩
    norm_num [height] at low
    unfold level at near
    linarith
  have estimate := branch_time_upper (D := 21) (A := 32) (W := 5/4) p ord h
    (by norm_num [core]) (by norm_num) (by norm_num [height]) (by norm_num)
    (by norm_num) (by norm_num) (h.2.2.trans (by norm_num [height])) weights gap finite
  have root : Real.sqrt (r - s) ≤ 2/5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · dsimp [core, limit] at slow fast
      linarith [slow.1, fast.2]
  change oneWayBounceTime w f h 0 _ ≤ s * _ + _ * Real.sqrt (r - s) at estimate
  have endS := slow.2
  unfold limit at endS
  linarith only [estimate, endS, root]

theorem well {y : ℝ → Plane} (p : Side (field y)) (m : Side (fun t => field y (-t)))
    (h : H) {φ : ℝ} (small : |φ| ≤ 1 / 2 ^ 19) :
    LaunchWell (field y) φ h (-m.time h) (p.time h) := by
  have sl := (m.interior_time h).1
  have sr := (p.interior_time h).1
  obtain ⟨l,r⟩ := abs_le.mp small
  dsimp [core] at sl sr
  refine ⟨by linarith, by linarith, m.hit h, p.hit h, fun t ht => ?_⟩
  rcases le_total 0 t with pos | neg
  · exact p.before h t ⟨pos, ht.2⟩
  · simpa only [neg_neg] using m.before h (-t) ⟨neg_nonneg.mpr neg, by linarith [ht.1]⟩

/-- On the true outer line, the physical time is the ordinary derivative with respect to
height. For the top part of the band the two outward flight estimates give an upper bound. -/
theorem response {y : ℝ → Plane} (e : Enclosed y (-limit) limit) (p : Side (field y))
    (m : Side (fun t => field y (-t))) (h : H) :
    let time := oneWayBounceTime (density y) (field y) h (-m.time h) (p.time h)
    mass y h = action (field y) (density y) (-m.time h) (p.time h) h ∧
      HasDerivAt (mass y) time h ∧ 0 < time ∧ (level - 1 / 100000 ≤ (h : ℝ) → time < 452) := by
  let g := fun t => density y t / Real.sqrt (2 * ((h : ℝ) - field y t))
  have w := well p m h (φ := 0) (by norm_num)
  have al := neg_le_neg (m.interior_time h).2.le
  have rb := (p.interior_time h).2.le
  have sub := Icc_subset_Icc al rb
  have cy : ContinuousOn y (Icc (-limit) limit) :=
    fun t ht => (e.ode t ht).continuousAt.continuousWithinAt
  have cf : ContinuousOn (field y) (Icc (-limit) limit) := by
    change ContinuousOn (fun t => strength t (y t)) _
    simpa only [one_mul] using continuousOn_strength cy 1
      (fun t ht => (by norm_num : (0 : ℝ) < 7/8).trans_le (e.region t ht).1.1)
  have eq (t : ℝ) (ht : t ∈ Icc (-limit) limit) :
      density y t = arcDensity (y t 0) t (y t 1) := by
    have box := e.region t ht
    exact arcDensity_of_ode (e.ode t ht) ((by norm_num : (0 : ℝ) < 7/8).trans_le box.1.1)
      ((by norm_num : (0 : ℝ) < 1/64).trans (DommaschkSignedTraceDenominator.regular t box.1 box.2))
  have cw := (continuousOn_density_region cy e.region).congr eq
  have left (t : ℝ) (ht : t ∈ Ico (-limit) (-m.time h)) : (h : ℝ) < field y t := by
    simpa only [neg_neg] using m.after h (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have right (t : ℝ) (ht : t ∈ Ioc (p.time h) limit) : (h : ℝ) < field y t := p.after h t ht
  have extL (t : ℝ) (ht : t ∈ Icc (-limit) (-m.time h)) : (h : ℝ) ≤ field y t := by
    rcases ht.2.eq_or_lt with eq | lt
    · rw [eq, w.left_hit]
    · exact (left t ⟨ht.1, lt⟩).le
  have extR (t : ℝ) (ht : t ∈ Icc (p.time h) limit) : (h : ℝ) ≤ field y t := by
    rcases ht.1.eq_or_lt with eq | lt
    · rw [← eq, w.right_hit]
    · exact (right t ⟨lt, ht.2⟩).le
  obtain ⟨v, pv, dv⟩ := p.transverse h
  obtain ⟨u, pu, du⟩ := m.transverse h
  have pos : 0 < (1 / 400 : ℝ) / (2 * (h : ℝ)) :=
    div_pos (by norm_num) (mul_pos (by norm_num)
      ((by norm_num [height] : 0 < (height false : ℝ)).trans_le h.2.1))
  have db : HasDerivAt (field y) (-u) (-m.time h) := by
    have dd : HasDerivAt (fun t => field y (-t)) u (- -m.time h) := by simpa only [neg_neg] using du
    simpa only [Function.comp_def, neg_neg, mul_neg_one] using
      dd.comp (-m.time h) (hasDerivAt_neg (-m.time h))
  obtain ⟨finite, positive⟩ := w.finite_bounce_time (cf.mono sub) (cw.mono sub)
    (fun t ht => by simpa only [eq t (sub (Ioo_subset_Icc_self ht))] using
      ((by norm_num : (0 : ℝ) < 7/8).trans_le
        (density_lower t (e.region t (sub (Ioo_subset_Icc_self ht))))))
    db (neg_lt_zero.mpr (pos.trans pu)) dv (pos.trans pv)
  have d := hasDerivAt_two_mirrors al rb w cf cw left right db (neg_ne_zero.mpr (pos.trans pu).ne')
    dv (pos.trans pv).ne'
  rw [time_eq_between al rb finite extL extR] at d
  have lr := w.left_lt.le.trans w.lt_right.le
  refine ⟨action_eq_between al lr rb cf cw extL extR, d, positive, fun near => ?_⟩
  change IntervalIntegrable g volume (-m.time h) (p.time h) at finite
  have l0 := w.left_lt.le
  have r0 := w.lt_right.le
  have pre := finite.mono_set (by rw [uIcc_of_le l0, uIcc_of_le lr]; exact Icc_subset_Icc_right r0)
  have post := finite.mono_set (by rw [uIcc_of_le r0, uIcc_of_le lr]; exact Icc_subset_Icc_left l0)
  have weights (t : ℝ) (ht : t ∈ Ioo (-m.time h) (p.time h)) : density y t ≤ 5/4 := by
    rw [eq t (sub (Ioo_subset_Icc_self ht))]
    exact (DommaschkToroidalFieldBounds.density_upper (e.region t (sub (Ioo_subset_Icc_self ht)))
      ((w.accessible t ht).le.trans h.2.2)).trans (by norm_num [height])
  have fr := clock_bound p h near (fun t ht => weights t ⟨l0.trans_lt ht.1, ht.2⟩) post
  have flip : IntervalIntegrable (fun t => g (-t)) volume 0 (m.time h) := by
    simpa only [zero_sub, sub_zero, neg_neg] using pre.symm.comp_sub_left 0
  have bk := clock_bound (w := fun t => density y (-t)) m h near
    (fun t ht => weights (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) flip
  change (∫ t in 0..m.time h, g (-t)) < 226 at bk
  rw [intervalIntegral.integral_comp_neg] at bk
  simp only [neg_zero] at bk
  change (∫ t in 0..p.time h, g t) < 226 at fr
  change (∫ t in (-m.time h)..p.time h, g t) < 452
  rw [← intervalIntegral.integral_add_adjacent_intervals pre post]
  linarith

abbrev top : H := ⟨height true, by constructor <;> norm_num [height]⟩

theorem top_lipschitz {y : ℝ → Plane} (e : Enclosed y (-limit) limit) (p : Side (field y))
    (m : Side (fun t => field y (-t))) {x : ℝ} (hx : x ∈ Icc (level - 1 / 100000) level) :
    |mass y x - mass y level| ≤ 452 * |x - level| := by
  let band := Icc (level - 1 / 100000) level
  have control (v : ℝ) (hv : v ∈ band) :
      DifferentiableAt ℝ (mass y) v ∧ ‖deriv (mass y) v‖ ≤ 452 := by
    have near : level - 1 / 100000 ≤ v := hv.1
    have bottom : (height false : ℝ) ≤ level - 1 / 100000 := by norm_num [height, level]
    have inH : v ∈ H := ⟨bottom.trans near,
      hv.2.trans (by norm_num [height, level])⟩
    obtain ⟨_, d, pos, bound⟩ := response e p m ⟨v, inH⟩
    refine ⟨d.differentiableAt, ?_⟩
    rw [d.deriv, Real.norm_eq_abs, abs_of_pos pos]
    exact (bound near).le
  exact (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
    (fun v hv => (control v hv).1) (fun v hv => (control v hv).2)
    (right_mem_Icc.mpr (by linarith)) hx

/-- One actual outer birth line works for all heights. The strongest action floor here
uses the measured upper-height quadrature and the physical time bound on the same line. -/
def Result (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) : Prop :=
  ∃ (y : ℝ → Plane), y φ = coordinates.symm (DommaschkMirrorLaunch.birth uC zC uA zA (239/500) φ) ∧
    Enclosed y (-limit) limit ∧ ∀ h : H, ∃ l r,
      LaunchWell (field y) φ h l r ∧ mass y h = action (field y) (density y) l r h ∧
      HasDerivAt (mass y) (oneWayBounceTime (density y) (field y) h l r) h ∧
      (level - 1/100000 ≤ (h : ℝ) → oneWayBounceTime (density y) (field y) h l r < 452 ∧
        target + 19/10000 - 452 * (level - (h : ℝ)) < mass y h)

theorem of_outer_witness {uC zC uA zA : Theory.KAM.FA} {φ L R : ℝ} {y : ℝ → Plane}
    (small : |φ| ≤ 1 / 2 ^ 19)
    (born : y φ = coordinates.symm (DommaschkMirrorLaunch.birth uC zC uA zA (239 / 500) φ))
    (e : Enclosed y (-limit) limit) (p : Side (field y)) (m : Side (fun t => field y (-t)))
    (w : LaunchWell (field y) 0 level L R)
    (lower : 790254733800996141875465767 / 580284393415022003858964480 ≤
      action (field y) (density y) L R level) : Result uC zC uA zA φ := by
  have same := well p m top (φ := 0) (by norm_num)
  have height_eq : (top : ℝ) = level := by norm_num [top, height, level]
  rw [height_eq] at same
  obtain ⟨leq, req⟩ := w.unique same
  have base := (response e p m top).1
  rw [height_eq, ← leq, ← req] at base
  have slack : target + 19/10000 < mass y level := by
    rw [base]
    exact lt_of_lt_of_le (by norm_num [target]) lower
  refine ⟨y, born, e, fun h => ⟨-m.time h, p.time h, well p m h small, ?_⟩⟩
  obtain ⟨eq, d, _, hi⟩ := response e p m h
  refine ⟨eq, d, fun near => ⟨hi near, ?_⟩⟩
  have hlim : (h : ℝ) ≤ level := h.2.2.trans (by norm_num [height, level])
  have gap := top_lipschitz e p m ⟨near, hlim⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hlim), neg_sub, abs_sub_comm] at gap
  exact (sub_lt_sub_right slack _).trans_le (sub_le_comm.mp ((le_abs_self _).trans gap))

end PlasmaLean.Design.DommaschkOuterFaceFlight
