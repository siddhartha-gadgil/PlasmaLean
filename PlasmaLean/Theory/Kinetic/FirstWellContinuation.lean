/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellPersistence
public import PlasmaLean.Theory.Kinetic.MirrorActionComparison
public import PlasmaLean.Theory.Fields.TrajectorySlabObservable
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Continuation of first mirror times and first-well actions across launch parameters -/

@[expose] public section
noncomputable section

namespace PlasmaLean.Kinetic.FirstWellContinuation

open Set Filter Topology MeasureTheory MirrorHeightAction

variable {P : Type*} [TopologicalSpace P] {f w : P → ℝ → ℝ} {h τ : P → ℝ} {b : ℝ}

/-- The first contact on an outward clock, with the birth at zero. -/
structure FirstContact (f : ℝ → ℝ) (h b τ : ℝ) : Prop where
  interior : τ ∈ Ioo 0 b
  hit : f τ = h
  before : ∀ t ∈ Ico 0 τ, f t < h

/-- A strict birth and a strict exterior cap suffice to select the first contact. -/
theorem exists_first {g : ℝ → ℝ} {H B : ℝ} (hb : 0 < B)
    (cont : ContinuousOn g (Icc 0 B)) (birth : g 0 < H) (cap : H < g B) :
    ∃ T, FirstContact g H B T := by
  obtain ⟨T, hT, hit, quiet⟩ := Fields.TrajectorySlabs.first_contact_in_bracket
    (a := 0) (l := 0) le_rfl hb (by simpa using birth) cont cap
  exact ⟨T, hT, hit, quiet⟩

/-- Superlevel points arbitrarily close beyond the first contact. -/
def CrossesOutward (f : ℝ → ℝ) (h b τ : ℝ) : Prop :=
  ∀ v, τ < v → ∃ s ∈ Ioo τ (min v b), h < f s

theorem FirstContact.crosses_of_deriv_pos {g : ℝ → ℝ} {H B T : ℝ}
    (hit : FirstContact g H B T) (d : 0 < deriv g T) : CrossesOutward g H B T := by
  intro v hv
  have near := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (differentiableAt_of_deriv_ne_zero d.ne').hasDerivAt).2.eventually (eventually_gt_nhds d)
  have inside : ∀ᶠ s in 𝓝[>] T, s ∈ Ioo T (min v B) := Ioo_mem_nhdsGT (lt_min hv hit.interior.2)
  obtain ⟨s, hs, slope⟩ := (inside.and near).exists
  exact ⟨s, hs, hit.hit ▸ (slope_pos_iff_of_le hs.1.le).mp slope⟩

/-- If the first contact fails to cross outward, it is a local maximum of the profile. -/
theorem FirstContact.localMax_of_not_crosses {g : ℝ → ℝ} {H B T : ℝ}
    (hit : FirstContact g H B T) (stops : ¬ CrossesOutward g H B T) : IsLocalMax g T := by
  unfold CrossesOutward at stops
  push Not at stops
  obtain ⟨v, hv, quiet⟩ := stops
  have near : ∀ᶠ s in 𝓝 T, s ∈ Ioo 0 (min v B) := Ioo_mem_nhds hit.interior.1
    (lt_min hv hit.interior.2)
  filter_upwards [near] with s hs
  rcases lt_trichotomy s T with before | eq | after
  · exact hit.hit ▸ (hit.before s ⟨hs.1.le, before⟩).le
  · exact le_of_eq (congrArg g eq)
  · exact hit.hit ▸ quiet s ⟨after, hs.2⟩

/-- The first contact varies continuously at any parameter where it crosses outward.
Later contacts and intervening critical points can be arbitrary. -/
theorem continuousAt_time (hf : ContinuousOn (fun z : P × ℝ => f z.1 z.2) (univ ×ˢ Icc 0 b))
    (hh : Continuous h) (first : ∀ p, FirstContact (f p) (h p) b (τ p)) {p : P}
    (outward : CrossesOutward (f p) (h p) b (τ p)) : ContinuousAt τ p := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases neg : a < 0
    · exact Eventually.of_forall fun q => neg.trans (first q).interior.1
    have ab : a ≤ b := ha.le.trans (first p).interior.2.le
    have cf := hf.mono (prod_mono_right (Icc_subset_Icc_right ab))
    have keep := MirrorWellPersistence.isOpen_stays (Y := fun q t => f q t - h q)
      (U := Iio 0) isOpen_Iio (cf.sub (hh.comp continuous_fst).continuousOn)
    have quiet : ∀ t ∈ Icc 0 a, f p t - h p ∈ Iio 0 :=
      fun t ht => sub_neg.mpr ((first p).before t ⟨ht.1, ht.2.trans_lt ha⟩)
    filter_upwards [keep.mem_nhds quiet] with q good
    by_contra! bad
    exact (lt_irrefl (0 : ℝ)) (by
      have atHit := good (τ q) ⟨(first q).interior.1.le, bad⟩
      simpa only [mem_Iio, (first q).hit, sub_self] using atHit)
  · intro a ha
    obtain ⟨s, hs, above⟩ := outward a ha
    have sb := lt_min_iff.mp hs.2
    have time : s ∈ Icc 0 b := ⟨((first p).interior.1.trans hs.1).le, sb.2.le⟩
    have atTime : Continuous fun q => f q s :=
      hf.comp_continuous (continuous_id.prodMk continuous_const) fun q => ⟨mem_univ q, time⟩
    filter_upwards [((isOpen_lt hh atTime).mem_nhds above)] with q forbidden
    apply lt_of_le_of_lt _ sb.1
    by_contra! past
    exact forbidden.not_gt ((first q).before s ⟨time.1, past⟩)

/-- The action from birth to first contact is continuous in the varying birth data and height. -/
theorem continuous_action (hf : ContinuousOn (fun z : P × ℝ => f z.1 z.2) (univ ×ˢ Icc 0 b))
    (hw : ContinuousOn (fun z : P × ℝ => w z.1 z.2) (univ ×ˢ Icc 0 b))
    (hh : Continuous h) (first : ∀ p, FirstContact (f p) (h p) b (τ p))
    (outward : ∀ p, CrossesOutward (f p) (h p) b (τ p)) :
    Continuous fun p => action (f p) (w p) 0 (τ p) (h p) := by
  nontriviality P
  obtain ⟨p⟩ := ‹Nontrivial P›.to_nonempty
  have hb : 0 ≤ b := ((first p).interior.1.trans (first p).interior.2).le
  let clock (t : ℝ) := (projIcc 0 b hb t : ℝ)
  let density := fun (q : P) (t : ℝ) => w q (clock t) * Real.sqrt (2 * (h q - f q (clock t)))
  have ct : Continuous fun z : P × ℝ => (z.1, clock z.2) :=
    continuous_fst.prodMk (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have valid (z : P × ℝ) : (z.1, clock z.2) ∈ univ ×ˢ Icc 0 b :=
    ⟨mem_univ _, (projIcc 0 b hb z.2).property⟩
  have cd : Continuous density.uncurry := (hw.comp_continuous ct valid).mul
    ((continuous_const.mul ((hh.comp continuous_fst).sub (hf.comp_continuous ct valid))).sqrt)
  have times := continuous_iff_continuousAt.mpr fun q => continuousAt_time hf hh first (outward q)
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
    (a₀ := 0) cd times).congr
  intro q
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (first q).interior.1.le] at ht
  have mem : t ∈ Icc 0 b := ⟨ht.1, ht.2.trans (first q).interior.2.le⟩
  simp only [density, clock, projIcc_of_mem hb mem]

/-- One passage, adding the integrals from birth to first contact on each signed clock. -/
def twoSidedAction (F W : Bool → P → ℝ → ℝ) (T : Bool → P → ℝ) (H : P → ℝ) (p : P) : ℝ :=
  action (F false p) (W false p) 0 (T false p) (H p) +
    action (F true p) (W true p) 0 (T true p) (H p)

/-- With a connected parameter space and actions bracketing a target, either one first well
has that action or one of the outward first contacts is a local maximum of its field.
The two directions may have different outer caps and later accessible pockets. -/
theorem target_or_grazing [PreconnectedSpace P] {F W : Bool → P → ℝ → ℝ}
    {B : Bool → ℝ} {T : Bool → P → ℝ} {H : P → ℝ} (height : Continuous H)
    (field : ∀ i, ContinuousOn (fun z : P × ℝ => F i z.1 z.2) (univ ×ˢ Icc 0 (B i)))
    (weight : ∀ i, ContinuousOn (fun z : P × ℝ => W i z.1 z.2) (univ ×ˢ Icc 0 (B i)))
    (first : ∀ i p, FirstContact (F i p) (H p) (B i) (T i p))
    (left right : P) {target : ℝ} (low : twoSidedAction F W T H left < target)
    (high : target < twoSidedAction F W T H right) :
    (∃ p, twoSidedAction F W T H p = target) ∨
      ∃ i p, IsLocalMax (F i p) (T i p) ∧ deriv (F i p) (T i p) = 0 := by
  by_cases crosses : ∀ i p, CrossesOutward (F i p) (H p) (B i) (T i p)
  · have cs (i : Bool) := continuous_action (field i) (weight i) height (first i) (crosses i)
    exact Or.inl (intermediate_value_univ left right ((cs false).add (cs true)) ⟨low.le, high.le⟩)
  · push Not at crosses
    obtain ⟨i, p, stuck⟩ := crosses
    have mx := (first i p).localMax_of_not_crosses stuck
    exact Or.inr ⟨i, p, mx, mx.deriv_eq_zero⟩

/-- Earliest-contact times for a fixed profile agree. -/
theorem FirstContact.unique {g : ℝ → ℝ} {H B C t s : ℝ}
    (x : FirstContact g H B t) (y : FirstContact g H C s) : t = s := by
  apply le_antisymm
  · by_contra! earlier
    exact (x.before s ⟨y.interior.1.le, earlier⟩).ne y.hit
  · by_contra! earlier
    exact (y.before t ⟨x.interior.1.le, earlier⟩).ne x.hit

/-- The sum over signed clocks equals the original one-way action on the physical interval. -/
theorem action_split {g v : ℝ → ℝ} {l r H : ℝ} (hl : l ≤ 0) (hr : 0 ≤ r)
    (field : ContinuousOn g (Icc l r)) (weight : ContinuousOn v (Icc l r)) :
    action (fun t => g (-t)) (fun t => v (-t)) 0 (-l) H + action g v 0 r H =
      action g v l r H := by
  let d := fun t => v t * Real.sqrt (2 * (H - g t))
  have cont : ContinuousOn d (Icc l r) :=
    weight.mul ((continuousOn_const.mul (continuousOn_const.sub field)).sqrt)
  change (∫ t in (0:ℝ)..-l, d (-t)) + (∫ t in (0:ℝ)..r, d t) = ∫ t in l..r, d t
  rw [intervalIntegral.integral_comp_neg, neg_zero, neg_neg]
  apply intervalIntegral.integral_add_adjacent_intervals
  · exact (cont.mono (by rw [uIcc_of_le hl]; exact Icc_subset_Icc_right hr)).intervalIntegrable
  · exact (cont.mono (by rw [uIcc_of_le hr]; exact Icc_subset_Icc_left hl)).intervalIntegrable

/-- A continuous family on a common finite slab. The left and right end caps lie above
the level and the common birth at zero lies below it. -/
structure CappedFamily (f w : P → ℝ → ℝ) (h : P → ℝ) (b : ℝ) : Prop where
  duration : 0 < b
  height : Continuous h
  field : ContinuousOn (fun z : P × ℝ => f z.1 z.2) (univ ×ˢ Icc (-b) b)
  weight : ContinuousOn (fun z : P × ℝ => w z.1 z.2) (univ ×ˢ Icc (-b) b)
  birth : ∀ p, f p 0 < h p
  back : ∀ p, h p < f p (-b)
  forward : ∀ p, h p < f p b

open MirrorActionEnvelope

/-- A target bracketed by two physical well actions is attained somewhere in the connected
family, unless a first contact somewhere is a local maximum of the original field profile. -/
theorem CappedFamily.target_or_localMax [PreconnectedSpace P] (fam : CappedFamily f w h b)
    {x y : P} {l₁ r₁ l₂ r₂ j : ℝ}
    (wx : LaunchWell (f x) 0 (h x) l₁ r₁) (wy : LaunchWell (f y) 0 (h y) l₂ r₂)
    (low : action (f x) (w x) l₁ r₁ (h x) < j)
    (high : j < action (f y) (w y) l₂ r₂ (h y)) :
    (∃ p l r, LaunchWell (f p) 0 (h p) l r ∧ action (f p) (w p) l r (h p) = j) ∨
      ∃ p l r, LaunchWell (f p) 0 (h p) l r ∧
        (IsLocalMax (f p) l ∨ IsLocalMax (f p) r) := by
  let clock (i : Bool) (t : ℝ) := if i then t else -t
  let signed (g : P → ℝ → ℝ) (i : Bool) (p : P) (t : ℝ) := g p (clock i t)
  have joint {g : P → ℝ → ℝ}
      (hg : ContinuousOn (fun z : P × ℝ => g z.1 z.2) (univ ×ˢ Icc (-b) b)) (i : Bool) :
      ContinuousOn (fun z : P × ℝ => signed g i z.1 z.2) (univ ×ˢ Icc 0 b) := by
    apply hg.comp (f := fun z : P × ℝ => (z.1, clock i z.2))
    · cases i <;> simp only [clock, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    · intro z hz
      refine ⟨mem_univ _, ?_⟩
      obtain ⟨h0, hb⟩ := hz.2
      cases i <;> simp only [clock, Bool.false_eq_true, ↓reduceIte, mem_Icc] <;>
        constructor <;> linarith
  have first (i : Bool) (p : P) : ∃ t, FirstContact (signed f i p) (h p) b t := by
    apply exists_first fam.duration
    · exact (joint fam.field i).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun t ht => ⟨mem_univ p, ht⟩)
    · cases i <;> simpa [signed, clock] using fam.birth p
    · cases i
      · exact fam.back p
      · exact fam.forward p
  choose T ht using first
  let L (p : P) := -(T false p)
  let R (p : P) := T true p
  have well (p : P) : LaunchWell (f p) 0 (h p) (L p) (R p) := by
    have back := ht false p
    have fwd := ht true p
    refine ⟨neg_lt_zero.mpr back.interior.1, fwd.interior.1, back.hit, fwd.hit, ?_⟩
    intro t ir
    by_cases zero : 0 ≤ t
    · exact fwd.before t ⟨zero, ir.2⟩
    · have earlier : -t ∈ Ico 0 (T false p) := ⟨by linarith, neg_lt_of_neg_lt ir.1⟩
      simpa [signed, clock] using back.before (-t) earlier
  have mass (p : P) : twoSidedAction (signed f) (signed w) T h p =
      action (f p) (w p) (L p) (R p) (h p) := by
    have sub : Icc (L p) (R p) ⊆ Icc (-b) b :=
      Icc_subset_Icc (neg_le_neg (ht false p).interior.2.le) (ht true p).interior.2.le
    have onArc {g : P → ℝ → ℝ}
        (cg : ContinuousOn (fun z : P × ℝ => g z.1 z.2) (univ ×ˢ Icc (-b) b)) :
        ContinuousOn (g p) (Icc (L p) (R p)) :=
      cg.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hm => ⟨mem_univ p, sub hm⟩
    simpa only [twoSidedAction, signed, clock, L, R, neg_neg, Bool.false_eq_true, ↓reduceIte] using
      action_split (H := h p) (well p).left_lt.le (well p).lt_right.le (onArc fam.field)
        (onArc fam.weight)
  have ends {p : P} {l r : ℝ} (ws : LaunchWell (f p) 0 (h p) l r) : L p = l ∧ R p = r := by
    exact (well p).unique ws
  obtain ⟨exl, exr⟩ := ends wx
  obtain ⟨eyl, eyr⟩ := ends wy
  rcases target_or_grazing fam.height (joint fam.field) (joint fam.weight) ht x y
      (by simpa [mass, exl, exr] using low) (by simpa [mass, eyl, eyr] using high) with
    ⟨p, exactMass⟩ | ⟨i, p, localMax, _⟩
  · exact Or.inl ⟨p, L p, R p, well p, (mass p).symm.trans exactMass⟩
  · right
    refine ⟨p, L p, R p, well p, ?_⟩
    cases i
    · left
      have reflect : Tendsto Neg.neg (𝓝 (L p)) (𝓝 (T false p)) := by
        simpa only [L, neg_neg] using (continuous_neg.continuousAt (x := L p)).tendsto
      change ∀ᶠ t in 𝓝 (L p), f p t ≤ f p (L p)
      filter_upwards [reflect.eventually localMax] with t ht
      simpa [signed, clock, L] using ht
    · exact Or.inr localMax

end PlasmaLean.Kinetic.FirstWellContinuation
