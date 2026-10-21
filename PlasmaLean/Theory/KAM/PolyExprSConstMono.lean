/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.PolyExprS

/-!
# Monotonicity of the majorants of `PolyExprS` in the constants

`ConstLe e e'`: the expression `e` has the shape of `e'` with every constant replaced by a constant
of smaller or equal norm (the inverse-square-root nodes keep their centre `c`). Then, at bounds
`a ≥ 0` (and `b ≥ 0`) where `e'` is valid,

* `e` is valid (`ConstLe.valid`),
* `maj a e ≤ maj a e'`, `majD a b e ≤ majD a b e'`, `majD2 a b e ≤ majD2 a b e'`
  (`ConstLe.maj_le`, `ConstLe.majD_le`, `ConstLe.majD2_le`).

This gives majorants uniform over a parameter interval: a parameter entering only through
constants (for example the pitch parameter `λ` of the `μ > 0` passing guiding-centre field) can
be replaced by the end point of largest modulus.

**Sanity.** `constLe_refl`: every expression is `ConstLe` itself.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM.PolyExprS

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*}

/-- `e` has the shape of `e'` with constants of smaller or equal norm. -/
inductive ConstLe : PolyExprS 𝕜 σ → PolyExprS 𝕜 σ → Prop
  /-- Constants of smaller norm. -/
  | const {c c' : 𝕜} : ‖c‖ ≤ ‖c'‖ → ConstLe (.const c) (.const c')
  /-- Variables. -/
  | var (i : σ) : ConstLe (.var i) (.var i)
  /-- Sums. -/
  | add {p q p' q' : PolyExprS 𝕜 σ} : ConstLe p p' → ConstLe q q' → ConstLe (.add p q) (.add p' q')
  /-- Differences. -/
  | sub {p q p' q' : PolyExprS 𝕜 σ} : ConstLe p p' → ConstLe q q' → ConstLe (.sub p q) (.sub p' q')
  /-- Products. -/
  | mul {p q p' q' : PolyExprS 𝕜 σ} : ConstLe p p' → ConstLe q q' → ConstLe (.mul p q) (.mul p' q')
  /-- Nodes with the same centre. -/
  | isqrt (c : ℝ) {d d' : PolyExprS 𝕜 σ} : ConstLe d d' → ConstLe (.isqrt c d) (.isqrt c d')

/-- **Sanity**: `ConstLe` is reflexive. -/
theorem constLe_refl : ∀ e : PolyExprS 𝕜 σ, ConstLe e e
  | .const _ => .const le_rfl
  | .var i => .var i
  | .add p q => .add (constLe_refl p) (constLe_refl q)
  | .sub p q => .sub (constLe_refl p) (constLe_refl q)
  | .mul p q => .mul (constLe_refl p) (constLe_refl q)
  | .isqrt c d => .isqrt c (constLe_refl d)

variable {a b : σ → ℝ} {e e' : PolyExprS 𝕜 σ}

/-- Validity and the majorant bound together (induction). -/
theorem ConstLe.valid_maj (ha : ∀ i, 0 ≤ a i) (h : ConstLe e e') (hv : Valid a e') :
    Valid a e ∧ maj a e ≤ maj a e' := by
  induction h with
  | const hc => exact ⟨trivial, hc⟩
  | var i => exact ⟨trivial, le_rfl⟩
  | add _ _ ihp ihq =>
    obtain ⟨vp, mp⟩ := ihp hv.1
    obtain ⟨vq, mq⟩ := ihq hv.2
    exact ⟨⟨vp, vq⟩, add_le_add mp mq⟩
  | sub _ _ ihp ihq =>
    obtain ⟨vp, mp⟩ := ihp hv.1
    obtain ⟨vq, mq⟩ := ihq hv.2
    exact ⟨⟨vp, vq⟩, add_le_add mp mq⟩
  | mul _ _ ihp ihq =>
    obtain ⟨vp, mp⟩ := ihp hv.1
    obtain ⟨vq, mq⟩ := ihq hv.2
    exact ⟨⟨vp, vq⟩, mul_le_mul mp mq (maj_nonneg ha _) (maj_nonneg ha _)⟩
  | isqrt c _ ih =>
    obtain ⟨vd, md⟩ := ih hv.1
    exact ⟨⟨vd, md.trans_lt hv.2⟩, isqG_mono md hv.2⟩

/-- **`ConstLe` preserves validity.** -/
theorem ConstLe.valid (ha : ∀ i, 0 ≤ a i) (h : ConstLe e e') (hv : Valid a e') : Valid a e :=
  (h.valid_maj ha hv).1

/-- **The majorant is monotone in the constants.** -/
theorem ConstLe.maj_le (ha : ∀ i, 0 ≤ a i) (h : ConstLe e e') (hv : Valid a e') :
    maj a e ≤ maj a e' :=
  (h.valid_maj ha hv).2

/-- **The first-derivative majorant is monotone in the constants.** -/
theorem ConstLe.majD_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (h : ConstLe e e')
    (hv : Valid a e') : majD a b e ≤ majD a b e' := by
  induction h with
  | const _ => exact le_rfl
  | var i => exact le_rfl
  | add _ _ ihp ihq => exact add_le_add (ihp hv.1) (ihq hv.2)
  | sub _ _ ihp ihq => exact add_le_add (ihp hv.1) (ihq hv.2)
  | @mul p q p' q' hp hq ihp ihq =>
    have m1 := hp.maj_le ha hv.1
    have m2 := hq.maj_le ha hv.2
    have e1 := ihp hv.1
    have e2 := ihq hv.2
    have n1 := majD_nonneg ha hb p
    have n2 := majD_nonneg ha hb q
    have n3 := maj_nonneg ha p
    have n4 := maj_nonneg ha q
    have n5 := majD_nonneg ha hb p'
    have n6 := maj_nonneg ha p'
    simp only [majD]
    gcongr
  | @isqrt c d d' hd ih =>
    have md := hd.maj_le ha hv.1
    have hg := isqG_mono md hv.2
    have g0 := isqG_nonneg c (maj a d)
    have g1 := isqG_nonneg c (maj a d')
    have n1 := majD_nonneg ha hb d
    simp only [majD]
    have := ih hv.1
    gcongr

/-- **The second-derivative majorant is monotone in the constants.** -/
theorem ConstLe.majD2_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (h : ConstLe e e')
    (hv : Valid a e') : majD2 a b e ≤ majD2 a b e' := by
  induction h with
  | const _ => exact le_rfl
  | var i => exact le_rfl
  | add _ _ ihp ihq => exact add_le_add (ihp hv.1) (ihq hv.2)
  | sub _ _ ihp ihq => exact add_le_add (ihp hv.1) (ihq hv.2)
  | @mul p q p' q' hp hq ihp ihq =>
    have m1 := hp.maj_le ha hv.1
    have m2 := hq.maj_le ha hv.2
    have d1 := hp.majD_le ha hb hv.1
    have d2 := hq.majD_le ha hb hv.2
    have e1 := ihp hv.1
    have e2 := ihq hv.2
    have n1 := majD2_nonneg ha hb p
    have n2 := majD2_nonneg ha hb q
    have n3 := maj_nonneg ha p
    have n4 := maj_nonneg ha q
    have n5 := majD_nonneg ha hb p
    have n6 := majD_nonneg ha hb q
    have n7 := majD2_nonneg ha hb p'
    have n8 := maj_nonneg ha p'
    have n9 := majD_nonneg ha hb p'
    simp only [majD2]
    gcongr
  | @isqrt c d d' hd ih =>
    have md := hd.maj_le ha hv.1
    have dd := hd.majD_le ha hb hv.1
    have hg := isqG_mono md hv.2
    have g0 := isqG_nonneg c (maj a d)
    have g1 := isqG_nonneg c (maj a d')
    have n1 := majD_nonneg ha hb d
    have n2 := majD2_nonneg ha hb d
    have e1 := ih hv.1
    simp only [majD2]
    gcongr

end PlasmaLean.Theory.KAM.PolyExprS
