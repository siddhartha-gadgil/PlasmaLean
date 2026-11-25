/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialAccessibleBirth
public import PlasmaLean.Design.DommaschkRibbonFirstMirrors
public import PlasmaLean.Design.DommaschkToroidalFieldBounds
public import PlasmaLean.Theory.Kinetic.MirrorTimeActionBounds

/-! # Height-dependent first mirrors on the full radial ribbon -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialMirrorHeightBand

open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkRibbonFirstMirrors
open DommaschkSignedMirrorBand DommaschkMirrorTubeCrossing DommaschkRadialFamilyContinuity
open DommaschkNativeWellAction Kinetic.MirrorHeightBand Kinetic.MirrorActionEnvelope
open DommaschkSignedTraceDensity DommaschkPhysicalActionPanel

abbrev clearance : ℝ := level - 1/48000
abbrev lower : ℝ := level - 1/50000
abbrev upper : ℝ := level + 1/30000
abbrev Heights := Icc lower upper
abbrev Positive (y : ℝ → Plane) := Branch (field y) lowerClock capClock lower upper derivativeFloor
abbrev Negative (y : ℝ → Plane) :=
  Branch (fun t => field y (-t)) lowerClock capClock lower upper derivativeFloor

theorem signed_window {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock) :
    ContinuousOn (field y) (Icc (-capClock) capClock) := by
  have cy : ContinuousOn y (Icc (-capClock) capClock) :=
    fun t ht => (e.ode t ht).continuousAt.continuousWithinAt
  change ContinuousOn (fun t => strength t (y t)) _
  simpa only [one_mul] using continuousOn_strength cy 1
    (fun t ht => lt_of_lt_of_le (by norm_num : (0:ℝ) < 7/8) (e.region t ht).1.1)

private theorem reverse_flow (t : ℝ) (x : Plane) :
    -DommaschkJacobian.euclideanFlow 0 1 (-t) x =
      DommaschkJacobian.euclideanFlow 0 (-1) t x := by
  ext j
  fin_cases j <;> simp [DommaschkJacobian.euclideanFlow,DommaschkBounceField.physicalFlow]

theorem signed_rates {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    (rates : Rates y lowerClock capClock derivativeFloor) {t : ℝ}
    (ht : t ∈ Icc lowerClock capClock) :
    Rate (field y) derivativeFloor t ∧ Rate (fun u => field y (-u)) derivativeFloor t := by
  have a : 0 ≤ t := (by norm_num [lowerClock] : 0 ≤ lowerClock).trans ht.1
  have b : 0 ≤ capClock := by norm_num [capClock]
  have db := (e.ode (-t) ⟨neg_le_neg ht.2,(neg_nonpos.mpr a).trans b⟩).scomp t (hasDerivAt_neg t)
  exact rates t ht (e.ode t ⟨(neg_nonpos.mpr b).trans a,ht.2⟩)
    (by simpa only [Function.comp_def,neg_one_smul,reverse_flow] using db)

/-- Both clocks have a unique increasing inverse on the entire closed height interval. -/
theorem branches {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    (early : Below y 0 lowerClock clearance)
    (caps : upper < field y (-capClock) ∧ upper < field y capClock)
    (rates : Rates y lowerClock capClock derivativeFloor) :
    Nonempty (Positive y) ∧ Nonempty (Negative y) := by
  have cf := signed_window e
  have a : 0 ≤ lowerClock := by norm_num [lowerClock]
  have b : lowerClock < capClock := by norm_num [lowerClock,capClock]
  have cc : ContinuousOn (field y) (Icc lowerClock capClock) :=
    cf.mono (Icc_subset_Icc_left (by norm_num [lowerClock,capClock]))
  have cb : ContinuousOn (fun t => field y (-t)) (Icc lowerClock capClock) :=
    cf.comp continuous_neg.continuousOn (fun t ht => ⟨neg_le_neg ht.2,
      (neg_nonpos.mpr (a.trans ht.1)).trans (a.trans b.le)⟩)
  have one {f : ℝ → ℝ} (nn : ∀ t, 0 ≤ f t) (co : ContinuousOn f (Icc lowerClock capClock))
      (lo : ∀ t ∈ Icc 0 lowerClock, f t < clearance) (hi : upper < f capClock)
      (slope : ∀ t ∈ Ioo lowerClock capClock, Rate f derivativeFloor t) :
      Nonempty (Branch f lowerClock capClock lower upper derivativeFloor) := by
    have base := lo lowerClock ⟨a,le_rfl⟩
    have hit := intermediate_value_Ioo b.le co (show upper ∈ Ioo (f lowerClock) (f capClock) from
      ⟨base.trans (by norm_num [clearance,upper,level]),hi⟩)
    exact exists_branch a b (by norm_num [lower,level]) (by norm_num [derivativeFloor]) nn co
      (fun t ht => (lo t ht).trans (by norm_num [clearance,lower,level])) hit slope
  exact ⟨one (fun _ => norm_nonneg _) cc (fun t ht => (early t ht).1) caps.2
    (fun _ ht => (signed_rates e rates (Ioo_subset_Icc_self ht)).1),
    one (fun _ => norm_nonneg _) cb (fun t ht => (early t ht).2) caps.1
    (fun _ ht => (signed_rates e rates (Ioo_subset_Icc_self ht)).2)⟩

/-- The first well contains every admitted birth phase. Its endpoints depend on the trajectory
and height, and remain the same when the birth is recentered within the accessible segment. -/
theorem birth_well {y : ℝ → Plane} (p : Positive y) (m : Negative y) (h : Heights)
    {φ : ℝ} (small : |φ| ≤ 1 / 2 ^ 19) : LaunchWell (field y) φ h (-m.time h) (p.time h) := by
  have lo := (m.interior_time h).1
  have hi := (p.interior_time h).1
  obtain ⟨l,r⟩ := abs_le.mp small
  refine ⟨by norm_num [lowerClock] at lo; linarith, by norm_num [lowerClock] at hi; linarith,
    m.hit h,p.hit h,?_⟩
  intro t ht
  rcases le_total 0 t with pos | neg
  · exact p.before h t ⟨pos,ht.2⟩
  · simpa only [neg_neg] using m.before h (-t) ⟨neg_nonneg.mpr neg,by linarith [ht.1]⟩

/-- The common inverse Lipschitz bound is in absolute physical angle per unit of field height. -/
theorem clock_displacement {y : ℝ → Plane} (p : Positive y) (m : Negative y) (h j : Heights) :
    |p.time h - p.time j| ≤ 34740 * |(h:ℝ)-j| ∧
    |m.time h - m.time j| ≤ 34740 * |(h:ℝ)-j| := by
  have bound : 2*upper/derivativeFloor ≤ 34740 := by norm_num [upper,level,derivativeFloor]
  have one := mul_le_mul_of_nonneg_right bound (abs_nonneg ((h:ℝ)-j))
  exact ⟨(p.time_lipschitz (by norm_num [lower,level])
    (by norm_num [derivativeFloor]) h j).trans one,
    (m.time_lipschitz (by norm_num [lower,level])
      (by norm_num [derivativeFloor]) h j).trans one⟩

abbrev weight (y : ℝ → Plane) (t : ℝ) := arcDensity (y t 0) t (y t 1)

theorem cartesian_weight {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    {t : ℝ} (ht : t ∈ Icc (-capClock) capClock) : density y t = weight y t := by
  have box := e.region t ht
  exact arcDensity_of_ode (e.ode t ht)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) box.1.1)
    ((by norm_num : (0 : ℝ) < 1 / 64).trans (DommaschkSignedTraceDenominator.regular t box.1 box.2))

/-- The physical arclength-weighted one-way time exists at every level of this closed band. -/
theorem flight {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    (p : Positive y) (m : Negative y) (h : Heights) :
    IntervalIntegrable (fun t => weight y t / Real.sqrt (2*((h:ℝ)-field y t))) volume
      (-m.time h) (p.time h) ∧
    0 < oneWayBounceTime (weight y) (field y) h (-m.time h) (p.time h) := by
  have well := birth_well p m h (φ := 0) (by norm_num)
  have sub := Icc_subset_Icc (neg_le_neg (m.interior_time h).2.le) (p.interior_time h).2.le
  have cy : ContinuousOn y (Icc (-capClock) capClock) :=
    fun t ht => (e.ode t ht).continuousAt.continuousWithinAt
  obtain ⟨v,hv,dv⟩ := p.transverse h
  obtain ⟨u,hu,du⟩ := m.transverse h
  have pos : 0 < derivativeFloor / (2*(h:ℝ)) := div_pos (by norm_num [derivativeFloor])
    (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num [lower,level]) h.2.1))
  have db : HasDerivAt (field y) (-u) (-m.time h) := by
    have dd : HasDerivAt (fun t => field y (-t)) u (- -m.time h) := by simpa only [neg_neg] using du
    simpa only [Function.comp_def,neg_neg,mul_neg_one] using
      dd.comp (-m.time h) (hasDerivAt_neg (-m.time h))
  exact well.finite_bounce_time ((signed_window e).mono sub)
    ((continuousOn_density_region cy e.region).mono sub)
    (fun t ht => lt_of_lt_of_le (by norm_num : (0:ℝ) < 7/8)
      (density_lower t (e.region t (sub (Ioo_subset_Icc_self ht)))))
    db (neg_neg_of_pos (pos.trans hu)) dv (pos.trans hv)

private theorem half_bound {f w : ℝ → ℝ} (h : Heights)
    (p : Branch f lowerClock capClock lower upper derivativeFloor)
    (cf : ContinuousOn f (Icc lowerClock capClock)) (nn : ∀ t, 0 ≤ f t)
    (low : ∀ t ∈ Ioo 0 lowerClock, f t < clearance)
    (rates : ∀ t ∈ Ioo lowerClock capClock, Rate f derivativeFloor t)
    (dens : ∀ t ∈ Ioo 0 (p.time h), w t ≤ 5 / 4)
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * ((h : ℝ) - f t)))
      volume 0 (p.time h)) :
    (∫ t in 0..p.time h, w t / Real.sqrt (2 * ((h : ℝ) - f t))) < 5000 := by
  have hr := p.interior_time h
  have a : (0:ℝ) ≤ lowerClock := by norm_num [lowerClock]
  have sep : Kinetic.MirrorProfileStability.SlopeSeparatedOn (fun t => f t ^ 2)
      (Icc lowerClock capClock) derivativeFloor := by
    apply Kinetic.MirrorProfileStability.separated_of_derivative (convex_Icc _ _)
      ((continuous_pow 2).comp_continuousOn cf)
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨v,_,d⟩ := rates t ht
      exact d.differentiableAt.differentiableWithinAt
    · left
      intro t ht
      rw [interior_Icc] at ht
      obtain ⟨v,hv,d⟩ := rates t ht
      exact d.deriv.symm ▸ hv.le
  have central (t : ℝ) (ht : t ∈ Ioo 0 lowerClock) :
      w t / Real.sqrt (2*((h:ℝ)-f t)) ≤ (5/4)*775 := by
    have low' := low t ht
    have hh := h.2.1
    have gap : ((1/775:ℝ)^2) ≤ 2*((h:ℝ)-f t) := by
      norm_num [lower,clearance,level] at low' hh ⊢
      linarith
    have speed : 1/775 ≤ Real.sqrt (2*((h:ℝ)-f t)) := by simpa using Real.sqrt_le_sqrt gap
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/775) speed)).mpr
    calc
      w t ≤ 5/4 := dens t ⟨ht.1,ht.2.trans hr.1⟩
      _ = (5/4*775)*(1/775:ℝ) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left speed (by norm_num)
  have wing (t : ℝ) (ht : t ∈ Ioo lowerClock (p.time h)) :
      w t / Real.sqrt (2*((h:ℝ)-f t)) ≤ 165 / Real.sqrt (p.time h - t) := by
    have member : t ∈ Ioo 0 (p.time h) := ⟨a.trans_lt ht.1,ht.2⟩
    have under := p.before h t ⟨member.1.le,member.2⟩
    have dt := sub_pos.mpr ht.2
    have gap := sep _ (Ioo_subset_Icc_self hr) t ⟨ht.1.le,ht.2.le.trans hr.2.le⟩
    dsimp only at gap
    rw [p.hit,abs_of_pos dt,abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (nn t) under.le 2))]
      at gap
    have factor : (h:ℝ) ≤ derivativeFloor * 132^2 := h.2.2.trans (by
      norm_num [upper,level,derivativeFloor])
    have delta : p.time h-t ≤ (132:ℝ)^2*(2*((h:ℝ)-f t)) := by
      norm_num [derivativeFloor] at factor gap ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr factor) (sub_nonneg.mpr under.le),
        sq_nonneg ((h:ℝ)-f t)]
    have sr := Real.sqrt_le_sqrt delta
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (132:ℝ)^2),Real.sqrt_sq (by norm_num)] at sr
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr dt)).mpr
    calc
      w t * Real.sqrt (p.time h-t) ≤ (5/4)*Real.sqrt (p.time h-t) :=
        mul_le_mul_of_nonneg_right (dens t member) (Real.sqrt_nonneg _)
      _ ≤ _ := by convert mul_le_mul_of_nonneg_left sr (by norm_num : (0:ℝ) ≤ 5/4) using 1; ring
  have bound := half_time_upper a hr.1.le finite central wing
  have short : p.time h-lowerClock ≤ (1/2:ℝ)^2 := by
    have x := hr.2
    norm_num [capClock,lowerClock] at x ⊢
    linarith
  have sq : Real.sqrt (p.time h-lowerClock) ≤ 1/2 := Real.sqrt_le_iff.mpr ⟨by norm_num,short⟩
  norm_num [lowerClock] at bound sq ⊢
  linarith only [bound,sq]

/-- A common physical one-way flight-time bound. Time uses the normalized Hamiltonian speed
with Cartesian arclength as its spatial parameter. -/
theorem flight_bounds {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    (early : Below y 0 lowerClock clearance) (rates : Rates y lowerClock capClock derivativeFloor)
    (p : Positive y) (m : Negative y) (h : Heights) :
    let T := oneWayBounceTime (weight y) (field y) h (-m.time h) (p.time h)
    14 < T ∧ T < 10000 := by
  let g := fun t => weight y t / Real.sqrt (2*((h:ℝ)-field y t))
  have a : (0:ℝ) ≤ lowerClock := by norm_num [lowerClock]
  have hm := m.interior_time h
  have hp := p.interior_time h
  have l : -m.time h ≤ 0 := neg_nonpos.mpr (a.trans hm.1.le)
  have r : 0 ≤ p.time h := a.trans hp.1.le
  have sub := Icc_subset_Icc (neg_le_neg hm.2.le) hp.2.le
  have well := birth_well p m h (φ := 0) (by norm_num)
  have finite := (flight e p m h).1
  have left : IntervalIntegrable g volume (-m.time h) 0 := finite.mono_set (by
    rw [uIcc_of_le l, uIcc_of_le (l.trans r)]; exact Icc_subset_Icc_right r)
  have right : IntervalIntegrable g volume 0 (p.time h) := finite.mono_set (by
    rw [uIcc_of_le r, uIcc_of_le (l.trans r)]; exact Icc_subset_Icc_left l)
  have ref : IntervalIntegrable (fun t => g (-t)) volume 0 (m.time h) := by
    simpa only [sub_zero,zero_sub,neg_neg] using left.symm.comp_sub_left 0
  have weights (t : ℝ) (ht : t ∈ Ioo (-m.time h) (p.time h)) : weight y t ≤ 5/4 := by
    have wt := DommaschkToroidalFieldBounds.density_upper
      (e.region t (sub (Ioo_subset_Icc_self ht))) (well.accessible t ht).le
    exact wt.trans ((mul_le_mul_of_nonneg_right h.2.2 (by norm_num : (0:ℝ) ≤ 8/7)).trans
      (by norm_num [upper,level]))
  have fc := signed_window e
  have front := half_bound h p (fc.mono (Icc_subset_Icc_left (by norm_num [lowerClock,capClock])))
    (fun _ => norm_nonneg _) (fun t ht => (early t (Ioo_subset_Icc_self ht)).1)
    (fun _ ht => (signed_rates e rates (Ioo_subset_Icc_self ht)).1)
    (fun t ht => weights t ⟨l.trans_lt ht.1,ht.2⟩) right
  have bc : ContinuousOn (fun t => field y (-t)) (Icc lowerClock capClock) :=
    fc.comp continuous_neg.continuousOn (fun t ht => ⟨neg_le_neg ht.2,
      (neg_nonpos.mpr (a.trans ht.1)).trans (by norm_num [capClock])⟩)
  have back := half_bound h m bc (fun _ => norm_nonneg _)
    (fun t ht => (early t (Ioo_subset_Icc_self ht)).2)
    (fun _ ht => (signed_rates e rates (Ioo_subset_Icc_self ht)).2)
    (w := fun t => weight y (-t))
    (fun t ht => weights (-t) ⟨neg_lt_neg ht.2,(neg_neg_of_pos ht.1).trans_le r⟩) ref
  change (∫ t in 0..m.time h, g (-t)) < 5000 at back
  change (∫ t in 0..p.time h, g t) < 5000 at front
  rw [intervalIntegral.integral_comp_neg,neg_zero] at back
  change 14 < ∫ t in (-m.time h)..p.time h, g t ∧ (∫ t in (-m.time h)..p.time h, g t) < 10000
  constructor
  · have speed (t : ℝ) (ht : t ∈ Ioo (-m.time h) (p.time h)) :
        Real.sqrt (2*((h:ℝ)-field y t)) ≤ 61/100 := by
      have low := DommaschkToroidalFieldBounds.strength_lower t
        (e.region t (sub (Ioo_subset_Icc_self ht)))
      change 7/8 < field y t at low
      apply Real.sqrt_le_iff.mpr
      have hh := h.2.2
      norm_num [upper,level] at hh
      exact ⟨by norm_num, by linarith⟩
    have base := well.time_lower (by norm_num : (0:ℝ) ≤ 7/8)
      (fun t ht => density_lower t (e.region t (sub (Ioo_subset_Icc_self ht)))) speed finite
    apply lt_of_lt_of_le _ base
    have x := hp.1
    have z := hm.1
    norm_num [lowerClock] at x z ⊢
    linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals left right]
    linarith only [front,back]

/-- The same pair of height-dependent inverse branches supplies all birth phases,
the physical flight interval, and the two signed slopes. -/
def Verified (y : ℝ → Plane) : Prop :=
  ∃ (p : Positive y) (m : Negative y),
    (∀ h j : Heights, |p.time h - p.time j| ≤ 34740 * |(h : ℝ) - j| ∧
      |m.time h - m.time j| ≤ 34740 * |(h : ℝ) - j|) ∧
    ∀ h : Heights,
      (∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → LaunchWell (field y) φ h (-m.time h) (p.time h)) ∧
      deriv (field y) (-m.time h) < -(derivativeFloor / (2 * (h : ℝ))) ∧
      derivativeFloor / (2 * (h : ℝ)) < deriv (field y) (p.time h) ∧
      IntervalIntegrable (fun t => weight y t / Real.sqrt (2 * ((h : ℝ) - field y t)))
        volume (-m.time h) (p.time h) ∧
      14 < oneWayBounceTime (density y) (field y) h (-m.time h) (p.time h) ∧
      oneWayBounceTime (density y) (field y) h (-m.time h) (p.time h) < 10000

theorem verified {y : ℝ → Plane} (e : Enclosed y (-capClock) capClock)
    (early : Below y 0 lowerClock clearance)
    (caps : upper < field y (-capClock) ∧ upper < field y capClock)
    (rates : Rates y lowerClock capClock derivativeFloor) : Verified y := by
  obtain ⟨⟨p⟩,⟨m⟩⟩ := branches e early caps rates
  refine ⟨p,m,clock_displacement p m,?_⟩
  intro h
  obtain ⟨v,hv,dv⟩ := p.transverse h
  obtain ⟨u,hu,du⟩ := m.transverse h
  have d : HasDerivAt (fun t => field y (-t)) u (- -m.time h) := by simpa only [neg_neg] using du
  have left : HasDerivAt (field y) (-u) (-m.time h) := by
    simpa only [Function.comp_def,neg_neg,mul_neg_one] using
      d.comp (-m.time h) (hasDerivAt_neg (-m.time h))
  have ordered : -m.time h ≤ p.time h := by
    have zero : 0 ≤ lowerClock := by norm_num [lowerClock]
    linarith [(m.interior_time h).1,(p.interior_time h).1]
  have eq : oneWayBounceTime (density y) (field y) h (-m.time h) (p.time h) =
      oneWayBounceTime (weight y) (field y) h (-m.time h) (p.time h) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ordered]
    intro t ht
    dsimp only
    rw [cartesian_weight e (Icc_subset_Icc (neg_le_neg (m.interior_time h).2.le)
      (p.interior_time h).2.le ht)]
  exact ⟨fun _ => birth_well p m h,left.deriv.symm ▸ neg_lt_neg hu,dv.deriv.symm ▸ hv,
    (flight e p m h).1,eq.symm ▸ flight_bounds e early rates p m h⟩

end PlasmaLean.Design.DommaschkRadialMirrorHeightBand
