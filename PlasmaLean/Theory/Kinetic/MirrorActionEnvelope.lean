/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorHeightAction
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Action bounds for the accessible well containing a launch

On a one-dimensional trace the component below a prescribed field strength is an open
interval. Forbidden endpoints enclose both boundaries. Clipped quadrature over the capped
interval bounds the one-way longitudinal action from above even if the trace has additional
accessible pockets beyond either first hit. Quadrature over an accessible core gives the
lower bound. No derivative at a first hit is required for either estimate. A finite bounce
time involves the reciprocal of the square root of the energy gap and requires further data.
-/

public section
noncomputable section

open Set Real MeasureTheory

namespace PlasmaLean.Kinetic.MirrorActionEnvelope

open MirrorHeightAction

/-- The first level hits on the two sides of an accessible launch. -/
structure LaunchWell (f : ℝ → ℝ) (c h l r : ℝ) : Prop where
  left_lt : l < c
  lt_right : c < r
  left_hit : f l = h
  right_hit : f r = h
  accessible : ∀ x ∈ Ioo l r, f x < h

/-- A continuous trace with a strictly accessible launch between forbidden caps has a
first mirror-height hit on each side, including when a hit is tangent to the level. -/
theorem exists_launchWell {f : ℝ → ℝ} {a c b h : ℝ} (hac : a < c) (hcb : c < b)
    (hf : ContinuousOn f (Icc a b)) (ha : h < f a) (hc : f c < h) (hb : h < f b) :
    ∃ l ∈ Ioo a c, ∃ r ∈ Ioo c b, LaunchWell f c h l r := by
  have hleft := hf.mono (Icc_subset_Icc (le_refl a) hcb.le)
  have hright := hf.mono (Icc_subset_Icc hac.le (le_refl b))
  let L := Icc a c ∩ f ⁻¹' Ici h
  let R := Icc c b ∩ f ⁻¹' Ici h
  have cL : IsClosed L := hleft.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have cR : IsClosed R := hright.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have ml : a ∈ L := ⟨⟨le_rfl, hac.le⟩, ha.le⟩
  have mr : b ∈ R := ⟨⟨hcb.le, le_rfl⟩, hb.le⟩
  obtain ⟨⟨ll,lh⟩,greatest⟩ := cL.isGreatest_csSup ⟨a,ml⟩ ⟨c, fun _ hx => hx.1.2⟩
  obtain ⟨⟨rr,rh⟩,least⟩ := cR.isLeast_csInf ⟨b,mr⟩ ⟨c, fun _ hx => hx.1.1⟩
  change h ≤ f (sSup L) at lh
  change h ≤ f (sInf R) at rh
  have lc : sSup L < c := ll.2.lt_of_ne (fun e => hc.not_ge (e ▸ lh))
  have cr : c < sInf R := rr.1.lt_of_ne (fun e => hc.not_ge (e ▸ rh))
  have left_hit : f (sSup L) = h := by
    apply le_antisymm _ lh
    by_contra! above
    obtain ⟨x,hx,hit⟩ := intermediate_value_Ioo' lc.le
      (hleft.mono (Icc_subset_Icc ll.1 le_rfl)) (show h ∈ Ioo _ _ from ⟨hc,above⟩)
    exact hx.1.not_ge (greatest (show x ∈ L from ⟨⟨ll.1.trans hx.1.le,hx.2.le⟩,hit.ge⟩))
  have right_hit : f (sInf R) = h := by
    apply le_antisymm _ rh
    by_contra! above
    obtain ⟨x,hx,hit⟩ := intermediate_value_Ioo cr.le
      (hright.mono (Icc_subset_Icc le_rfl rr.2)) (show h ∈ Ioo _ _ from ⟨hc,above⟩)
    exact hx.2.not_ge (least (show x ∈ R from ⟨⟨hx.1.le,hx.2.le.trans rr.2⟩,hit.ge⟩))
  have al := ll.1.lt_of_ne (fun e => ha.ne (e ▸ left_hit).symm)
  have rb := rr.2.lt_of_ne (fun e => hb.ne (e ▸ right_hit).symm)
  refine ⟨_,⟨al,lc⟩,_,⟨cr,rb⟩,lc,cr,left_hit,right_hit,?_⟩
  intro x hx
  apply lt_of_not_ge
  intro bad
  rcases le_total x c with hxc | hcx
  · exact hx.1.not_ge (greatest (show x ∈ L from ⟨⟨ll.1.trans hx.1.le,hxc⟩,bad⟩))
  · exact hx.2.not_ge (least (show x ∈ R from ⟨⟨hcx,hx.2.le.trans rr.2⟩,bad⟩))

/-- Any accessible interval that contains the launch lies between the first hits. -/
theorem LaunchWell.contains_core {f : ℝ → ℝ} {c h l r p q : ℝ}
    (well : LaunchWell f c h l r) (hp : p ≤ c) (hq : c ≤ q)
    (core : ∀ x ∈ Ioo p q, f x < h) : l ≤ p ∧ q ≤ r := by
  constructor
  · by_contra! bad
    exact (core l ⟨bad,well.left_lt.trans_le hq⟩).ne well.left_hit
  · by_contra! bad
    exact (core r ⟨hp.trans_lt well.lt_right,bad⟩).ne well.right_hit

/-- Raising the accessible height enlarges the launch component, even across a change
of bounce class at a critical field strength. -/
theorem LaunchWell.nested {f : ℝ → ℝ} {c h H l r L R : ℝ} (small : LaunchWell f c h l r)
    (large : LaunchWell f c H L R) (hh : h ≤ H) : L ≤ l ∧ r ≤ R :=
  large.contains_core small.left_lt.le small.lt_right.le
    (fun x hx => (small.accessible x hx).trans_le hh)

/-- The first hits at a fixed height are unique. -/
theorem LaunchWell.unique {f : ℝ → ℝ} {c h l r L R : ℝ} (well : LaunchWell f c h l r)
    (other : LaunchWell f c h L R) : l = L ∧ r = R := by
  obtain ⟨h₁,h₂⟩ := well.nested other le_rfl
  obtain ⟨h₃,h₄⟩ := other.nested well le_rfl
  exact ⟨le_antisymm h₃ h₁,le_antisymm h₂ h₄⟩

/-- The nonnegative clipped density is monotone under inclusion of ordered trace intervals. -/
theorem action_mono_interval {f w : ℝ → ℝ} {a p q b h : ℝ}
    (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ w t) : action f w p q h ≤ action f w a b h := by
  have hcont : ContinuousOn (fun t => w t * √(2*(h-f t))) (Icc a b) :=
    hw.mul ((continuousOn_const.mul (continuousOn_const.sub hf)).sqrt)
  exact intervalIntegral.integral_mono_interval hap hpq hqb
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
      mul_nonneg (hn t (Ioc_subset_Icc_self ht)) (sqrt_nonneg _))
    (hcont.intervalIntegrable_of_Icc (hap.trans (hpq.trans hqb)))

/-- Integrating over an accessible core bounds the one-way launch-well action from below.
Integrating the clipped density over both full caps bounds it from above. -/
theorem LaunchWell.action_bounds {f w : ℝ → ℝ} {a l p c q r b h : ℝ}
    (well : LaunchWell f c h l r) (hal : a ≤ l) (hrb : r ≤ b) (hp : p ≤ c) (hq : c ≤ q)
    (core : ∀ t ∈ Ioo p q, f t < h) (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hn : ∀ t ∈ Icc a b, 0 ≤ w t) :
    action f w p q h ≤ action f w l r h ∧ action f w l r h ≤ action f w a b h := by
  obtain ⟨hlp,hqr⟩ := well.contains_core hp hq core
  have sub := Icc_subset_Icc hal hrb
  exact ⟨action_mono_interval hlp (hp.trans hq) hqr (hf.mono sub) (hw.mono sub)
    (fun t ht => hn t (sub ht)),action_mono_interval hal (well.left_lt.trans well.lt_right).le
      hrb hf hw hn⟩

/-- Positive arclength density at launch makes the one-way action strictly larger at
a higher height, even when that height has a larger launch-connected component. -/
theorem LaunchWell.action_strictly_increases {f w : ℝ → ℝ} {c h H l r L R : ℝ}
    (small : LaunchWell f c h l r) (large : LaunchWell f c H L R) (hh : h < H)
    (hf : ContinuousOn f (Icc L R)) (hw : ContinuousOn w (Icc L R))
    (hn : ∀ t ∈ Icc L R, 0 ≤ w t) (hc : 0 < w c) :
    action f w l r h < action f w L R H := by
  obtain ⟨hL,hR⟩ := small.nested large hh.le
  have sub := Icc_subset_Icc hL hR
  have hc' : c ∈ Ioo l r := ⟨small.left_lt,small.lt_right⟩
  have hlr := small.left_lt.trans small.lt_right
  have grow := strictMonoOn_action hlr (hf.mono sub) (hw.mono sub) (fun t ht => hn t (sub ht))
    ⟨c,Ioo_subset_Icc_self hc',small.accessible c hc',hc⟩
  exact (grow (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh.le) hh).trans_le
    (action_mono_interval hL hlr.le hR hf hw hn)

/-- A continuous field strength has two forbidden caps and an accessible component with
quadratic vanishing of the gap at its first hit. Its inverse-speed integral diverges on
the half well from the left boundary to launch. -/
theorem forbidden_caps_allow_infinite_bounce_time :
    ∃ f : ℝ → ℝ, Continuous f ∧ 2 < f (-1) ∧ 2 < f 3 ∧ LaunchWell f 1 2 0 2 ∧
      ¬ IntervalIntegrable (fun t => (√(2*(2-f t)))⁻¹) volume 0 1 := by
  let d := fun t : ℝ => min t (2-t)
  let f := fun t : ℝ => 2 - d t * |d t| / 2
  have well : LaunchWell f 1 2 0 2 := by
    refine ⟨by norm_num,by norm_num,by norm_num [f,d],by norm_num [f,d],?_⟩
    intro t ht
    have pos : 0 < d t := lt_min ht.1 (sub_pos.mpr ht.2)
    dsimp [f]
    linarith [mul_pos pos (abs_pos.mpr pos.ne')]
  refine ⟨f,by dsimp [f,d]; fun_prop,by norm_num [f,d],by norm_num [f,d],well,?_⟩
  intro finite
  have reciprocal : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 := by
    apply finite.congr_uIoo
    intro t ht
    rw [uIoo_of_le zero_le_one] at ht
    have val : d t = t := min_eq_left (by linarith [ht.2])
    have rad : 2*(2-f t) = t^2 := by simp only [f,val,abs_of_pos ht.1]; ring
    change (√(2*(2-f t)))⁻¹ = t⁻¹
    rw [rad,Real.sqrt_sq ht.1.le]
  simp at reciprocal

/-- On the double well of strength `||t|-1|`, the launch at `-1` first hits the
central peak at height one. Every higher height admits the entire opposite core
`[1/2,1]`, adding at least half a unit of action. -/
private theorem doubleWell_gap {h l r : ℝ} (high : 1 < h)
    (well : LaunchWell (fun t : ℝ => abs (|t| - 1)) (-1) h l r) :
    action (fun t : ℝ => abs (|t| - 1)) 1 (-2) 0 1 + 1/2 ≤
      action (fun t : ℝ => abs (|t| - 1)) 1 l r h := by
  let f := fun t : ℝ => abs (|t| - 1)
  have cf : Continuous f := by dsimp [f]; fun_prop
  have core : ∀ t ∈ Ioo (-2 : ℝ) 1, f t < h := by
    intro t ht
    apply lt_of_le_of_lt _ high
    apply abs_le.mpr
    constructor
    · linarith [abs_nonneg t]
    · have ht' : |t| ≤ 2 := abs_le.mpr ⟨ht.1.le,by linarith [ht.2]⟩
      linarith
  obtain ⟨hl,hr⟩ := well.contains_core (by norm_num : (-2 : ℝ) ≤ -1)
    (by norm_num : (-1 : ℝ) ≤ 1) core
  let g := fun (H t : ℝ) => (1 : ℝ) * √(2*(H-f t))
  have cg (H : ℝ) : Continuous (g H) := by dsimp [g]; fun_prop
  have grow : action f 1 (-2) 0 1 ≤ action f 1 (-2) 0 h :=
    intervalIntegral.integral_mono_on (by norm_num) ((cg 1).intervalIntegrable _ _)
      ((cg h).intervalIntegrable _ _) fun t _ => by
        dsimp [g]; gcongr
  have add : action f 1 (-2) 0 h + action f 1 0 1 h = action f 1 (-2) 1 h :=
    intervalIntegral.integral_add_adjacent_intervals ((cg h).intervalIntegrable _ _)
      ((cg h).intervalIntegrable _ _)
  have half : (1/2 : ℝ) ≤ action f 1 (1/2) 1 h := by
    calc
      _ = ∫ _ in (1/2 : ℝ)..1, (1 : ℝ) := by norm_num
      _ ≤ _ := intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
        ((cg h).intervalIntegrable _ _) (fun t ht => by
          change 1 ≤ 1 * √(2*(h-abs (|t| - 1)))
          rw [one_mul,one_le_sqrt,abs_of_nonneg (by linarith [ht.1] : 0 ≤ t),
            abs_of_nonpos (sub_nonpos.mpr ht.2)]
          linarith [ht.1])
  have includeCore : action f 1 (1/2) 1 h ≤ action f 1 0 1 h :=
    action_mono_interval (by norm_num) (by norm_num) le_rfl cf.continuousOn
      continuousOn_const (fun _ _ => zero_le_one)
  have includeWell : action f 1 (-2) 1 h ≤ action f 1 l r h :=
    action_mono_interval hl (by norm_num) hr cf.continuousOn
      continuousOn_const (fun _ _ => zero_le_one)
  change action f 1 (-2) 0 1 + 1/2 ≤ action f 1 l r h
  linarith

/-- The action on the launch-connected component can genuinely jump as two wells merge.
The same continuous field and unit arclength density are used for every height. -/
theorem launch_action_can_be_discontinuous :
    ∃ f J : ℝ → ℝ, Continuous f ∧
      (∀ h ∈ Icc (1 : ℝ) 2, ∃ l r, LaunchWell f (-1) h l r ∧ J h = action f 1 l r h) ∧
      ¬ ContinuousWithinAt J (Icc 1 2) 1 := by
  let f := fun t : ℝ => abs (|t| - 1)
  have cf : Continuous f := by dsimp [f]; fun_prop
  have all (h : Icc (1 : ℝ) 2) : ∃ l r, LaunchWell f (-1) h l r := by
    obtain ⟨l,_,r,_,well⟩ := exists_launchWell (a := -4) (b := 4) (c := -1) (h := h.val)
      (by norm_num) (by norm_num) cf.continuousOn
      (by norm_num [f]; linarith [h.2.2]) (by norm_num [f]; linarith [h.2.1])
      (by norm_num [f]; linarith [h.2.2])
    exact ⟨l,r,well⟩
  choose l r well using all
  let J := fun h : ℝ => if hh : h ∈ Icc (1 : ℝ) 2 then action f 1 (l ⟨h,hh⟩) (r ⟨h,hh⟩) h else 0
  have repr (h : ℝ) (hh : h ∈ Icc (1 : ℝ) 2) : J h = action f 1 (l ⟨h,hh⟩) (r ⟨h,hh⟩) h :=
    dite_eq_left hh
  refine ⟨f,J,cf,(fun h hh => ⟨_,_,well ⟨h,hh⟩,repr h hh⟩),?_⟩
  have base : LaunchWell f (-1) 1 (-2) 0 := by
    refine ⟨by norm_num,by norm_num,by norm_num [f],by norm_num [f],?_⟩
    intro x hx
    simp only [f,abs_of_neg hx.2,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  have hh₁ : (1 : ℝ) ∈ Icc 1 2 := by constructor <;> norm_num
  obtain ⟨el,er⟩ := (well ⟨1,hh₁⟩).unique base
  have val₁ := repr 1 hh₁
  rw [el,er] at val₁
  intro cont
  obtain ⟨δ,pos,near⟩ := Metric.continuousWithinAt_iff.mp cont (1/2) (by norm_num)
  let t := min (δ/2) (1/2)
  have tp : 0 < t := lt_min (by positivity) (by norm_num)
  have tm : t ≤ δ/2 := min_le_left _ _
  have ts : t ≤ 1/2 := min_le_right _ _
  have hh : 1+t ∈ Icc (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have gap := doubleWell_gap (by linarith : 1 < 1+t) (well ⟨1+t,hh⟩)
  change action f 1 (-2) 0 1 + 1/2 ≤ action f 1 _ _ (1+t) at gap
  rw [← val₁,← repr (1+t) hh] at gap
  have close := near hh (show dist (1+t) 1 < δ by
    rw [Real.dist_eq,abs_of_nonneg] <;> linarith)
  rw [Real.dist_eq,abs_lt] at close
  linarith [close.2]

end PlasmaLean.Kinetic.MirrorActionEnvelope
