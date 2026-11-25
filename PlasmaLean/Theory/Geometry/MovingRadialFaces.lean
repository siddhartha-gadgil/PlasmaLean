/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AnnularLevelSeparator
public import PlasmaLean.Theory.Geometry.ActionFaceBarrier

/-!
# Action levels and first exits between moving radial faces

A pair of continuous angular graphs can follow different radial brackets at different
launch phases. The action only needs to be continuous on the closed region between them.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.MovingRadialFaces

open Set
open scoped unitInterval

/-- The closed physical region between two radial graphs over the phase circle. -/
def strip (lo hi : UnitAddCircle → ℝ) : Set (UnitAddCircle × ℝ) :=
  {p | p.2 ∈ Icc (lo p.1) (hi p.1)}

/-- Opposite strict face signs give an angularly essential connected set of exact
prescribed actions in the physical moving strip, meeting every path joining its faces. -/
theorem separator {lo hi target : UnitAddCircle → ℝ} (cl : Continuous lo) (ch : Continuous hi)
    (width : ∀ x, lo x < hi x) (ct : Continuous target) {J : UnitAddCircle × ℝ → ℝ}
    (cJ : ContinuousOn J (strip lo hi))
    (low : ∀ x, J (x, lo x) < target x) (high : ∀ x, target x < J (x, hi x)) :
    ∃ K : Set (UnitAddCircle × ℝ), IsCompact K ∧ IsConnected K ∧
      (∀ p ∈ K, J p = target p.1 ∧ p.2 ∈ Ioo (lo p.1) (hi p.1)) ∧
      Prod.fst '' K = univ ∧
      (∀ g : C(I, UnitAddCircle × ℝ), (∀ t, g t ∈ strip lo hi) →
        (g 0).2 = lo (g 0).1 → (g 1).2 = hi (g 1).1 → ∃ t, g t ∈ K) ∧
      ¬ ∃ L : C(K, ℝ), ∀ p : K, (L p : UnitAddCircle) = p.val.1 := by
  let lift (p : UnitAddCircle × I) : UnitAddCircle × ℝ :=
    (p.1, lo p.1 + (hi p.1 - lo p.1) * (p.2 : ℝ))
  have cLift : Continuous lift :=
    continuous_fst.prodMk ((cl.comp continuous_fst).add (((ch.comp continuous_fst).sub
      (cl.comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)))
  have inside (p : UnitAddCircle × I) : lift p ∈ strip lo hi := by
    change lo p.1 ≤ _ ∧ _ ≤ hi p.1
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (width _).le) p.2.2.1)
    · have h := mul_le_mul_of_nonneg_left p.2.2.2 (sub_nonneg.mpr (width p.1).le)
      dsimp [lift]
      linarith
  let F (p : UnitAddCircle × I) := J (lift p) - target p.1
  have cF : Continuous F := (cJ.comp_continuous cLift inside).sub (ct.comp continuous_fst)
  obtain ⟨A, compact, connected, level, meets, proj, separates⟩ :=
    AnnularLevelSeparator.annulus_separator F cF (target := 0)
      (fun x => by simpa [F, lift] using sub_neg.mpr (low x))
      (fun x => by simpa [F, lift] using sub_pos.mpr (high x))
  refine ⟨lift '' A, compact.image cLift, connected.image _ cLift.continuousOn, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨eq, h0, h1⟩ := level p hp
    refine ⟨sub_eq_zero.mp eq, ?_, ?_⟩
    · exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr (width _)) h0)
    · have h := mul_lt_mul_of_pos_left (show (p.2 : ℝ) < 1 from h1) (sub_pos.mpr (width p.1))
      dsimp [lift]
      linarith
  · ext x
    constructor
    · exact fun _ => mem_univ _
    · intro _
      obtain ⟨p, hp, rfl⟩ := (eq_univ_iff_forall.mp proj) x
      exact ⟨lift p, mem_image_of_mem _ hp, rfl⟩
  · intro g hg h0 h1
    let s (t : I) := ((g t).2 - lo (g t).1) / (hi (g t).1 - lo (g t).1)
    have pos (t : I) : 0 < hi (g t).1 - lo (g t).1 := sub_pos.mpr (width _)
    have cs : Continuous s := ((continuous_snd.comp g.continuous).sub
      (cl.comp (continuous_fst.comp g.continuous))).div
      ((ch.comp (continuous_fst.comp g.continuous)).sub
        (cl.comp (continuous_fst.comp g.continuous)))
      (fun t => (pos t).ne')
    have hs (t : I) : s t ∈ Icc 0 1 := by
      obtain ⟨l,h⟩ := hg t
      exact ⟨div_nonneg (sub_nonneg.mpr l) (pos t).le,
        (div_le_one (pos t)).mpr (sub_le_sub_right h _)⟩
    let path : AnnularLevelSeparator.Passage UnitAddCircle :=
      ⟨⟨fun t => ((g t).1, ⟨s t, hs t⟩),
        (continuous_fst.comp g.continuous).prodMk (cs.subtype_mk hs)⟩,
        Subtype.ext (by simp [s,h0]), Subtype.ext (by simp [s,h1,(pos 1).ne'])⟩
    obtain ⟨t, ht⟩ := meets path
    refine ⟨t, path.val t, ht, Prod.ext rfl ?_⟩
    change lo (g t).1 + (hi (g t).1 - lo (g t).1) * s t = (g t).2
    dsimp [s]
    field_simp [(pos t).ne']
    ring
  · rintro ⟨L, hL⟩
    let inc : C(A, lift '' A) := ⟨fun a => ⟨lift a.val, mem_image_of_mem _ a.property⟩,
      (cLift.comp continuous_subtype_val).subtype_mk _⟩
    exact AnnularLevelSeparator.no_angular_lift compact separates
      ⟨L.comp inc, fun a => hL (inc a)⟩

/-- A pre-exit action band and two independent boundary observations prevent exit even
when both faces change with time. The phase and height can enter through those observations. -/
theorem stays_between {T inner outer : ℝ} {r lo hi J : ℝ → ℝ}
    (cr : ContinuousOn r (Icc 0 T)) (cl : ContinuousOn lo (Icc 0 T))
    (ch : ContinuousOn hi (Icc 0 T)) (width : ∀ t ∈ Icc 0 T, lo t < hi t)
    (start : r 0 ∈ Ioo (lo 0) (hi 0))
    (band : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, r s ∈ Icc (lo s) (hi s)) →
      J t ∈ Icc inner outer)
    (lower : ∀ t ∈ Icc 0 T, r t = lo t → J t < inner)
    (upper : ∀ t ∈ Icc 0 T, r t = hi t → outer < J t) :
    ∀ t ∈ Icc 0 T, r t ∈ Ioo (lo t) (hi t) := by
  intro t ht
  have zeroT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  let v (s : ℝ) := (r s - lo s) / (hi s - lo s)
  have pos (s : ℝ) (hs : s ∈ Icc 0 T) : 0 < hi s - lo s := sub_pos.mpr (width s hs)
  have cv : ContinuousOn v (Icc 0 T) :=
    (cr.sub cl).div (ch.sub cl) (fun s hs => (pos s hs).ne')
  have open_iff (s : ℝ) (hs : s ∈ Icc 0 T) :
      v s ∈ Ioo 0 1 ↔ r s ∈ Ioo (lo s) (hi s) := by
    change 0 < (r s - lo s) / _ ∧ (r s - lo s) / _ < 1 ↔ _
    rw [div_pos_iff_of_pos_right (pos s hs), div_lt_one (pos s hs), sub_pos, sub_lt_sub_iff_right]
    rfl
  by_contra hout
  obtain ⟨u, hu, face, before⟩ := ActionFaceBarrier.first_hit_of_departure cv
    ((open_iff 0 zeroT).mpr start) ht (fun h => hout ((open_iff t ht).mp h))
  have bounds := band u hu (by
    intro s hs
    have sp := pos s ⟨hs.1, hs.2.trans hu.2⟩
    obtain ⟨a,b⟩ := before s hs
    have l : 0 ≤ r s - lo s := by simpa using (le_div_iff₀ sp).mp a
    have h := (div_le_one sp).mp b
    exact ⟨sub_nonneg.mp l, (sub_le_sub_iff_right _).mp h⟩)
  rcases face with low | high
  · have eq := (div_eq_zero_iff.mp low).resolve_right (pos u hu).ne'
    exact (lower u hu (sub_eq_zero.mp eq)).not_ge bounds.1
  · have eq := (div_eq_one_iff_eq (pos u hu).ne').mp high
    exact (upper u hu (sub_left_inj.mp eq)).not_ge bounds.2

end PlasmaLean.MovingRadialFaces
