/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellComponent
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Persistence of transverse mirror wells in a family of field profiles -/

public section
noncomputable section
open Set MeasureTheory

namespace PlasmaLean.Kinetic.MirrorWellPersistence

/-- The launch lies below the height, both caps lie above it, and every contact
points out of the well on its respective half of the bracket. -/
def Bracket (f : ℝ → ℝ) (a c b h : ℝ) : Prop :=
  h < f a ∧ f c < h ∧ h < f b ∧
    (∀ t ∈ Icc a c, f t = h → deriv f t < 0) ∧
    (∀ t ∈ Icc c b, f t = h → 0 < deriv f t)

/-- Supply the three strict height tests and oriented derivatives for every contact. -/
theorem Bracket.of_signs {f : ℝ → ℝ} {a c b h : ℝ}
    (left : h < f a) (center : f c < h) (right : h < f b)
    (decreasing : ∀ t ∈ Icc a c, f t = h → deriv f t < 0)
    (increasing : ∀ t ∈ Icc c b, f t = h → 0 < deriv f t) : Bracket f a c b h :=
  ⟨left, center, right, decreasing, increasing⟩

/-- A bracket transfers between profiles that agree in value and oriented slope
on its closed window, including the two caps. -/
theorem Bracket.congrOn {f g : ℝ → ℝ} {a c b h : ℝ} (good : Bracket f a c b h)
    (ac : a ≤ c) (cb : c ≤ b) (values : EqOn f g (Icc a b))
    (slopes : EqOn (deriv f) (deriv g) (Icc a b)) : Bracket g a c b h := by
  obtain ⟨lo, mid, hi, left, right⟩ := good
  refine ⟨values ⟨le_rfl, ac.trans cb⟩ ▸ lo, values ⟨ac, cb⟩ ▸ mid,
    values ⟨ac.trans cb, le_rfl⟩ ▸ hi, ?_, ?_⟩
  · intro t ht hit
    have whole := (Icc_subset_Icc_right cb) ht
    exact slopes whole ▸ left t ht ((values whole).trans hit)
  · intro t ht hit
    have whole := (Icc_subset_Icc_left ac) ht
    exact slopes whole ▸ right t ht ((values whole).trans hit)

private theorem open_forall_compact {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [CompactSpace K] {s : Set (X × K)} (hs : IsOpen s) :
    IsOpen {x : X | ∀ k : K, (x, k) ∈ s} := by
  have eq : {x : X | ∀ k : K, (x, k) ∈ s} = (Prod.fst '' sᶜ)ᶜ := by
    ext x
    simp [Set.mem_image, Prod.exists]
  rw [eq]
  exact (isClosedMap_fst_of_compactSpace _ hs.isClosed_compl).isOpen_compl

/-- Staying in an open spatial region for a compact time window is open in the
initial data of a jointly continuous family. -/
theorem isOpen_stays {P E : Type*} [TopologicalSpace P] [TopologicalSpace E] {a b : ℝ}
    {Y : P → ℝ → E} {U : Set E} (op : IsOpen U)
    (hy : ContinuousOn (fun z : P × ℝ => Y z.1 z.2) (univ ×ˢ Icc a b)) :
    IsOpen {p | ∀ t ∈ Icc a b, Y p t ∈ U} := by
  have joint : Continuous (fun z : P × Icc a b => Y z.1 z.2) :=
    hy.comp_continuous (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      fun z => ⟨mem_univ _, z.2.property⟩
  have keep := open_forall_compact (op.preimage joint)
  convert keep using 1
  ext p
  simp

variable {P : Type*} [TopologicalSpace P] {F : P → ℝ → ℝ} {a c b : ℝ}

/-- Joint continuity on the closed time bracket of strength and its time
derivative makes the set of transverse wells open in parameter and height. -/
theorem isOpen_bracket (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn (fun z : P × ℝ => F z.1 z.2) (univ ×ˢ Icc a b))
    (hd : ContinuousOn (fun z : P × ℝ => deriv (F z.1) z.2) (univ ×ˢ Icc a b)) :
    IsOpen {z : P × ℝ | Bracket (F z.1) a c b z.2} := by
  have atTime (t : ℝ) (ht : t ∈ Icc a b) : Continuous (fun z : P × ℝ => F z.1 t) :=
    hf.comp_continuous (continuous_fst.prodMk continuous_const) fun _ => ⟨mem_univ _, ht⟩
  have onHalf {i j : ℝ} (sub : Icc i j ⊆ Icc a b)
      {G : P → ℝ → ℝ} (hg : ContinuousOn (fun z : P × ℝ => G z.1 z.2) (univ ×ˢ Icc a b)) :
      Continuous (fun z : (P × ℝ) × Icc i j => G z.1.1 z.2) :=
    hg.comp_continuous (continuous_fst.fst.prodMk (continuous_subtype_val.comp continuous_snd))
      fun z => ⟨mem_univ _, sub z.2.property⟩
  have side {i j : ℝ} (sub : Icc i j ⊆ Icc a b) {s : Set ℝ} (hs : IsOpen s) :
      IsOpen {z : P × ℝ | ∀ t ∈ Icc i j, F z.1 t = z.2 → deriv (F z.1) t ∈ s} := by
    have good := (isClosed_eq (onHalf sub hf) continuous_fst.snd).isOpen_compl.union
      (hs.preimage (onHalf sub (G := fun p => deriv (F p)) hd))
    convert open_forall_compact good using 1
    ext z
    simp [Set.mem_union, or_iff_not_imp_left]
  have left := side (Icc_subset_Icc_right hcb : Icc a c ⊆ Icc a b) (s := Iio 0) isOpen_Iio
  have right := side (Icc_subset_Icc_left hac : Icc c b ⊆ Icc a b) (s := Ioi 0) isOpen_Ioi
  exact (isOpen_lt continuous_snd (atTime a ⟨le_rfl, hac.trans hcb⟩)).inter
    ((isOpen_lt (atTime c ⟨hac, hcb⟩) continuous_snd).inter
      ((isOpen_lt continuous_snd (atTime b ⟨hac.trans hcb, le_rfl⟩)).inter (left.inter right)))

/-- For a distribution positive on open sets, one transverse bracket gives a
positive-measure set of parameter-height pairs with transverse brackets. -/
theorem measure_bracket_pos [MeasurableSpace (P × ℝ)] (μ : Measure (P × ℝ))
    [Measure.IsOpenPosMeasure μ] (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn (fun z : P × ℝ => F z.1 z.2) (univ ×ˢ Icc a b))
    (hd : ContinuousOn (fun z : P × ℝ => deriv (F z.1) z.2) (univ ×ˢ Icc a b))
    {p : P} {h : ℝ} (one : Bracket (F p) a c b h) :
    0 < μ {z : P × ℝ | Bracket (F z.1) a c b z.2} :=
  (isOpen_bracket hac hcb hf hd).measure_pos μ ⟨(p, h), one⟩

/-- The bracket selects the accessible component and gives the derivative signs
at its two actual endpoints. -/
theorem Bracket.exists_well {f : ℝ → ℝ} {h : ℝ} (one : Bracket f a c b h)
    (hac : a < c) (hcb : c < b) (hf : ContinuousOn f (Icc a b)) :
    ∃ l ∈ Ioo a c, ∃ r ∈ Ioo c b,
      MirrorActionEnvelope.LaunchWell f c h l r ∧ deriv f l < 0 ∧ 0 < deriv f r := by
  obtain ⟨l, hl, r, hr, el, er, dl, dr, interior, _, _⟩ :=
    MirrorWell.two_simple_mirrors_with_caps hac hcb hf one.1 one.2.1 one.2.2.1
      one.2.2.2.1 one.2.2.2.2
  exact ⟨l, hl, r, hr, ⟨hl.2, hr.1, el, er, interior⟩, dl, dr⟩

/-- A physical time parameter of positive speed lets a transverse profile
bracket at the launch descend to the arclength contract. -/
theorem Bracket.regularBirth {B : Fields.Space → Fields.Space} {X : ℝ → Fields.Space}
    {speed : ℝ → ℝ} {h : ℝ} (one : Bracket (fun t => ‖B (X t)‖) a c b h)
    (hac : a < c) (hcb : c < b) (hf : ContinuousOn (fun t => ‖B (X t)‖) (Icc a b))
    (hs : ContinuousOn speed (Icc a b))
    (line : ∀ t ∈ Icc a b, 0 < speed t ∧ B (X t) ≠ 0 ∧
      HasDerivAt X (speed t • GCLittlejohn.bhat B (X t)) t) :
    Contract.RegularMirrorBirth B (X c) h := by
  obtain ⟨l, hl, r, hr, well, dl, dr⟩ := one.exists_well hac hcb hf
  have sub : Icc l r ⊆ Icc a b := Icc_subset_Icc hl.1.le hr.2.le
  exact well.regular_at (B := B) (X := X) (speed := speed) ⟨hl.2.le, hr.1.le⟩
    (hs.mono sub) (fun t ht => line t (sub ht)) dl dr

/-- In a chart of physical births, a continuous mirror-height assignment can
depend on all the initial data. One transverse test in the chart gives positive
measure to births satisfying the arclength contract. -/
theorem regular_birth_measure_pos [MeasurableSpace P] (μ : Measure P)
    [Measure.IsOpenPosMeasure μ] {B : Fields.Space → Fields.Space}
    {X : P → ℝ → Fields.Space} {speed : P → ℝ → ℝ} {H : P → ℝ}
    (hac : a < c) (hcb : c < b) (he : Continuous H)
    (hf : ContinuousOn (fun z : P × ℝ => ‖B (X z.1 z.2)‖) (univ ×ˢ Icc a b))
    (hd : ContinuousOn (fun z : P × ℝ => deriv (fun t => ‖B (X z.1 t)‖) z.2)
      (univ ×ˢ Icc a b))
    (hs : ∀ p, ContinuousOn (speed p) (Icc a b))
    (line : ∀ p, ∀ t ∈ Icc a b, 0 < speed p t ∧ B (X p t) ≠ 0 ∧
      HasDerivAt (X p) (speed p t • GCLittlejohn.bhat B (X p t)) t)
    {q : P} (witness : Bracket (fun t => ‖B (X q t)‖) a c b (H q)) :
    0 < μ {p | Contract.RegularMirrorBirth B (X p c) (H p)} := by
  let F (p : P) (t : ℝ) := ‖B (X p t)‖
  have op : IsOpen {p : P | Bracket (F p) a c b (H p)} :=
    (isOpen_bracket (F := F) hac.le hcb.le hf hd).preimage (continuous_id.prodMk he)
  have pos := op.measure_pos μ ⟨q, witness⟩
  refine pos.trans_le (measure_mono ?_)
  intro p hp
  have profile : ContinuousOn (F p) (Icc a b) :=
    hf.comp (f := fun t : ℝ => (p, t)) (continuous_const.prodMk continuous_id).continuousOn
      fun _ ht => ⟨mem_univ p, ht⟩
  exact Bracket.regularBirth (B := B) (X := X p) (speed := speed p)
    hp hac hcb profile (hs p) (line p)

/-- A translated parabolic well tests both strict cap inequalities. It is
transverse at every interior mirror height, including arbitrarily near its bottom. -/
theorem quadratic_bracket_iff (p h : ℝ) :
    Bracket (fun t : ℝ => t ^ 2 + p) (-1) 0 1 h ↔ p < h ∧ h < p + 1 := by
  have d (t : ℝ) : deriv (fun x : ℝ => x ^ 2 + p) t = 2 * t := by
    simp
  constructor
  · intro hb
    exact ⟨by simpa using hb.2.1, by linarith [hb.2.2.1]⟩
  · rintro ⟨bot, top⟩
    refine ⟨by linarith, by simpa using bot, by linarith, ?_, ?_⟩
    · intro t ht hit
      rw [d]
      have ne : t ≠ 0 := by rintro rfl; simp at hit; linarith
      linarith [lt_of_le_of_ne ht.2 ne]
    · intro t ht hit
      rw [d]
      have ne : t ≠ 0 := by rintro rfl; simp at hit; linarith
      linarith [lt_of_le_of_ne ht.1 ne.symm]

/-- Uniform strength error alone allows an outward crossing to reverse direction.
For every positive error scale this smooth perturbation fails the same bracket
test as the quadratic profile at height 1/4. -/
theorem uniform_profile_error_counterexample (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, (∀ t, |g t - t ^ 2| ≤ 2 * ε) ∧
      Bracket (fun t : ℝ => t ^ 2) (-1) 0 1 (1 / 4) ∧ ¬Bracket g (-1) 0 1 (1 / 4) := by
  let g (t : ℝ) := t ^ 2 - (2 * ε) * Real.sin ((t - 1 / 2) / ε)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro t
    simp only [g, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos hε,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_of_le_one_right (mul_nonneg (by norm_num) hε.le) (Real.abs_sin_le_one _)
  · simpa using (quadratic_bracket_iff 0 (1 / 4)).mpr (by norm_num)
  · intro hb
    have hit : g (1 / 2) = 1 / 4 := by norm_num [g]
    have pos := hb.2.2.2.2 (1 / 2) (by constructor <;> norm_num) hit
    have inner := ((hasDerivAt_id (1 / 2 : ℝ)).sub_const (1 / 2)).div_const ε
    have d := ((hasDerivAt_pow 2 (1 / 2 : ℝ)).sub (inner.sin.const_mul (2 * ε))).deriv
    change deriv g (1 / 2) = _ at d
    rw [d] at pos
    field_simp [hε.ne'] at pos
    norm_num at pos

end PlasmaLean.Kinetic.MirrorWellPersistence
