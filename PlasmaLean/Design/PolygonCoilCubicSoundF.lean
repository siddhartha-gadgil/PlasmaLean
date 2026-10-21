/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicSoundE

/-!
# Soundness of the cubic checker, part F: rows and faces

* `cellCond_spec`: the geometric conditions checked by `cellOK4`;
* `row_sound`: a row of cells accepted by `cellsRow4` (from sound line records) bounds
  `‖Bseg - hel‖` and the distance to the coil on `[t₁, t₂] × [w₁, w_{n-1}]`;
* `face_sound` (**face bound**): a face accepted by `cellsAll4` (from sound line records) bounds
  them on `[t₁, t_{K-1}] × [w₁, w_{n-1}]`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- The conclusion on a rectangle of a face: error bound and distance to the coil. -/
@[expose] def RectGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind eta : ℕ) (T1 T2 W1 W2 : ℝ) :
    Prop :=
  ∀ t ∈ Icc T1 T2, ∀ w ∈ Icc W1 W2,
    ‖errF fils (ptF kind t w)‖ ≤ (eta : ℝ) / ((two40 : ℕ) : ℝ) ∧
      ∀ z ∈ allSegs fils, ∀ s ∈ Icc (0 : ℝ) 1,
        1 / 5 ≤ ‖ptF kind t w - seg (ptR z.2.1) (ptR z.2.2) s‖

/-- Meaning of the face-range check `inFaceB`. -/
theorem inFaceB_spec (F : Face4) (hwd : 0 < F.wd) {W : ℤ} (h : inFaceB F W = true) :
    (F.kind < 2 → |(W : ℝ) / F.wd| ≤ aF) ∧
      (¬ F.kind < 2 → 161 / 181 ≤ (W : ℝ) / F.wd ∧ (W : ℝ) / F.wd ≤ 199 / 181) := by
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  unfold inFaceB at h
  constructor
  · intro hk
    simp only [hk, ite_true, decide_eq_true_eq] at h
    rw [abs_div, abs_of_pos hwd', div_le_iff₀ hwd', aF]
    have : ((iabs W : ℕ) : ℝ) * 32761 ≤ 3420 * F.wd := by exact_mod_cast h
    rw [iabs_cast] at this
    linarith
  · intro hk
    simp only [hk, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (161 : ℝ) * F.wd ≤ 181 * W := by exact_mod_cast h1
    have h2' : (181 : ℝ) * W ≤ 199 * F.wd := by exact_mod_cast h2
    constructor
    · rw [le_div_iff₀ hwd']; linarith
    · rw [div_le_iff₀ hwd']; linarith

/-- The geometric conditions checked by `cellOK4`. -/
theorem cellCond_spec (F : Face4) (hwd : 0 < F.wd) {M0 M1 M2 M3 W0 W1 W2 W3 : ℤ}
    (h : cellCond F M0 M1 M2 M3 W0 W1 W2 W3 = true) :
    (M0 < M1 ∧ M1 < M2 ∧ M2 < M3) ∧ (W0 < W1 ∧ W1 < W2 ∧ W2 < W3) ∧
      -1 / 2 ≤ (M0 : ℝ) / 4096 ∧ (M3 : ℝ) / 4096 ≤ 1 / 2 ∧
      (F.kind < 2 ∨ 17 / 20 ≤ (W0 : ℝ) / F.wd) ∧
      (∀ w ∈ Icc ((W1 : ℝ) / F.wd) ((W2 : ℝ) / F.wd), 17 / 20 ≤ faceRho F.kind w ∧
        faceRho F.kind w ≤ 23 / 20 ∧ |faceZeta F.kind w| ≤ 3 / 25) ∧
      (F.kind < 2 ∨ 0 < W0) := by
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  unfold cellCond at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hm1, hm2⟩, hm3⟩, ⟨⟨hw1, hw2⟩, hw3⟩⟩, ⟨hlo, hhi⟩, hk, hf1, hf2⟩ := h
  have f1 := inFaceB_spec F hwd hf1
  have f2 := inFaceB_spec F hwd hf2
  refine ⟨⟨hm1, hm2, hm3⟩, ⟨hw1, hw2, hw3⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have : (-2048 : ℝ) ≤ M0 := by exact_mod_cast hlo
    linarith
  · have : (M3 : ℝ) ≤ 2048 := by exact_mod_cast hhi
    linarith
  · rcases hk with hk | hk
    · exact Or.inl hk
    · right; rw [le_div_iff₀ hwd']
      have : (17 : ℝ) * F.wd ≤ 20 * W0 := by exact_mod_cast hk
      linarith
  · intro w hw
    by_cases hk2 : F.kind < 2
    · have a1 := f1.1 hk2
      have a2 := f2.1 hk2
      simp only [faceRho, faceZeta, hk2, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · unfold cylR; split_ifs <;> norm_num
      · unfold cylR; split_ifs <;> norm_num
      · rw [abs_le] at a1 a2 ⊢
        constructor <;> nlinarith [hw.1, hw.2, show aF ≤ 3 / 25 by norm_num [aF]]
    · have a1 := f1.2 hk2
      have a2 := f2.2 hk2
      simp only [faceRho, faceZeta, hk2, ite_false]
      refine ⟨by linarith [hw.1], by linarith [hw.2], ?_⟩
      rw [planeZ_abs]; norm_num [aF]
  · rcases hk with hk | hk
    · exact Or.inl hk
    · right; omega

/-- **One cell from sound line records.** -/
theorem cell_from_lines (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (hF : Face4OK F)
    (eta : ℕ) (M0 M1 M2 M3 W0 W1 W2 W3 : ℤ)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : CRec)
    (va : LVal fils F M0 W0 a0 ∧ LVal fils F M0 W1 a1 ∧ LVal fils F M0 W2 a2 ∧ LVal fils F M0 W3 a3)
    (vb : LVal fils F M1 W0 b0 ∧ LVal fils F M1 W1 b1 ∧ LVal fils F M1 W2 b2 ∧ LVal fils F M1 W3 b3)
    (vc : LVal fils F M2 W0 c0 ∧ LVal fils F M2 W1 c1 ∧ LVal fils F M2 W2 c2 ∧ LVal fils F M2 W3 c3)
    (vd : LVal fils F M3 W0 d0 ∧ LVal fils F M3 W1 d1 ∧ LVal fils F M3 W2 d2 ∧ LVal fils F M3 W3 d3)
    (wa : LW fils F M0 W0 W1 W2 W3 a1) (wb : LW fils F M1 W0 W1 W2 W3 b1)
    (wc : LW fils F M2 W0 W1 W2 W3 c1) (wdd : LW fils F M3 W0 W1 W2 W3 d1)
    (tb : LT fils F M0 M1 M2 M3 W0 W1 W2 W3 b1)
    (hok : cellOK4 F eta M0 M1 M2 M3 W0 W1 W2 W3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 =
      true) :
    RectGood fils F.kind eta ((M1 : ℝ) / 4096) ((M2 : ℝ) / 4096) ((W1 : ℝ) / F.wd)
      ((W2 : ℝ) / F.wd) := by
  have hF' := hF
  obtain ⟨hk4, hwd, -, -, -, -⟩ := hF
  have hok' := hok
  unfold cellOK4 at hok'
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨hcond, ⟨⟨⟨⟨oa0, oa1⟩, oa2, oa3⟩, ⟨⟨ob0, ob1⟩, ob2, ob3⟩⟩, ⟨⟨oc0, oc1⟩, oc2, oc3⟩,
    ⟨⟨od0, od1⟩, od2, od3⟩⟩⟩, -⟩ := hok'
  obtain ⟨⟨hm1, hm2, hm3⟩, ⟨hw1, hw2, hw3⟩, hlo, hhi, hk, hcell, hρ0⟩ := cellCond_spec F hwd hcond
  have hρ : ∀ W : ℤ, W0 ≤ W → F.kind < 2 ∨ 0 < W := by
    intro W hW; rcases hρ0 with h | h
    · exact Or.inl h
    · right; omega
  have hρ1 := hρ W1 hw1.le
  have hρ2 := hρ W2 (hw1.trans hw2).le
  have hρ3 := hρ W3 ((hw1.trans hw2).trans hw3).le
  have hρ00 := hρ W0 le_rfl
  set Rm : Fin 4 → Fin 4 → CRec := ![![a0, a1, a2, a3], ![b0, b1, b2, b3], ![c0, c1, c2, c3],
    ![d0, d1, d2, d3]]
  set M : Fin 4 → ℤ := ![M0, M1, M2, M3]
  set W : Fin 4 → ℤ := ![W0, W1, W2, W3]
  have hcw : CondW F W0 W1 W2 W3 := ⟨hw1, hw2, hw3, hk⟩
  have hct : CondT F M0 M1 M2 M3 W0 W1 W2 W3 := ⟨hm1, hm2, hm3, hcw, hcell, hlo, hhi⟩
  obtain ⟨hTg, hDg⟩ := tb hct ob1
  intro t ht w hw
  refine ⟨?_, hDg w hw t ht⟩
  refine cell_sound4 fils F eta hwd M W Rm ⟨hm1, hm2, hm3⟩ ⟨hw1, hw2, hw3⟩ ?_ ?_ hTg hok ht hw
  · intro i j
    fin_cases i <;> fin_cases j
    · exact va.1 hρ00 oa0
    · exact va.2.1 hρ1 oa1
    · exact va.2.2.1 hρ2 oa2
    · exact va.2.2.2 hρ3 oa3
    · exact vb.1 hρ00 ob0
    · exact vb.2.1 hρ1 ob1
    · exact vb.2.2.1 hρ2 ob2
    · exact vb.2.2.2 hρ3 ob3
    · exact vc.1 hρ00 oc0
    · exact vc.2.1 hρ1 oc1
    · exact vc.2.2.1 hρ2 oc2
    · exact vc.2.2.2 hρ3 oc3
    · exact vd.1 hρ00 od0
    · exact vd.2.1 hρ1 od1
    · exact vd.2.2.1 hρ2 od2
    · exact vd.2.2.2 hρ3 od3
  · intro i
    fin_cases i
    · exact wa hcw oa1
    · exact wb hcw ob1
    · exact wc hcw oc1
    · exact wdd hcw od1

/-- Splitting the first four entries off a `Forall₂`. -/
theorem forall2_four {α β : Type} {P : α → β → Prop} {a b c d : α} {xs : List α} {L : List β}
    (h : List.Forall₂ P (a :: b :: c :: d :: xs) L) :
    ∃ r0 r1 r2 r3 rs, L = r0 :: r1 :: r2 :: r3 :: rs ∧ P a r0 ∧ P b r1 ∧ P c r2 ∧ P d r3 ∧
      List.Forall₂ P xs rs := by
  rcases h with _ | ⟨h0, h⟩
  rcases h with _ | ⟨h1, h⟩
  rcases h with _ | ⟨h2, h⟩
  rcases h with _ | ⟨h3, h⟩
  exact ⟨_, _, _, _, _, rfl, h0, h1, h2, h3, h⟩

/-- Union of two adjacent rectangles in `w`. -/
theorem rect_union {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {kind eta : ℕ} {T1 T2 W1 W2 W3 : ℝ}
    (h1 : RectGood fils kind eta T1 T2 W1 W2) (h2 : RectGood fils kind eta T1 T2 W2 W3) :
    RectGood fils kind eta T1 T2 W1 W3 := by
  intro t ht w hw
  rcases le_total w W2 with h | h
  · exact h1 t ht w ⟨hw.1, h⟩
  · exact h2 t ht w ⟨h, hw.2⟩

/-- Union of two adjacent rectangles in `t`. -/
theorem rect_union_t {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {kind eta : ℕ} {T1 T2 T3 W1 W2 : ℝ}
    (h1 : RectGood fils kind eta T1 T2 W1 W2) (h2 : RectGood fils kind eta T2 T3 W1 W2) :
    RectGood fils kind eta T1 T3 W1 W2 := by
  intro t ht w hw
  rcases le_total t T2 with h | h
  · exact h1 t ⟨ht.1, h⟩ w hw
  · exact h2 t ⟨h, ht.2⟩ w hw

/-- **A row of cells.** -/
theorem row_sound (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (hF : Face4OK F) (eta : ℕ)
    (M0 M1 M2 M3 : ℤ) :
    ∀ (ws : List ℤ) (L0 L1 L2 L3 : List CRec),
      List.Forall₂ (LVal fils F M0) ws L0 → List.Forall₂ (LVal fils F M1) ws L1 →
      List.Forall₂ (LVal fils F M2) ws L2 → List.Forall₂ (LVal fils F M3) ws L3 →
      QuadP (LW fils F M0) ws L0 → QuadP (LW fils F M1) ws L1 → QuadP (LW fils F M2) ws L2 →
      QuadP (LW fils F M3) ws L3 → QuadP (LT fils F M0 M1 M2 M3) ws L1 →
      cellsRow4 F eta M0 M1 M2 M3 L0 L1 L2 L3 ws = true → 4 ≤ ws.length →
      RectGood fils F.kind eta ((M1 : ℝ) / 4096) ((M2 : ℝ) / 4096) ((ws.getD 1 0 : ℝ) / F.wd)
        ((ws.getD (ws.length - 2) 0 : ℝ) / F.wd) := by
  intro ws
  induction ws with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp at h
  | cons W0 ws ih =>
    intro L0 L1 L2 L3 v0 v1 v2 v3 q0 q1 q2 q3 qt hrow hlen
    rcases ws with _ | ⟨W1, _ | ⟨W2, _ | ⟨W3, rest⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    obtain ⟨a0, a1, a2, a3, as, rfl, va0, va1, va2, va3, vas⟩ := forall2_four v0
    obtain ⟨b0, b1, b2, b3, bs, rfl, vb0, vb1, vb2, vb3, vbs⟩ := forall2_four v1
    obtain ⟨c0, c1, c2, c3, cs, rfl, vc0, vc1, vc2, vc3, vcs⟩ := forall2_four v2
    obtain ⟨d0, d1, d2, d3, ds, rfl, vd0, vd1, vd2, vd3, vds⟩ := forall2_four v3
    simp only [cellsRow4, Bool.and_eq_true] at hrow
    obtain ⟨hcell, hrest⟩ := hrow
    simp only [QuadP] at q0 q1 q2 q3 qt
    have hc := cell_from_lines fils F hF eta M0 M1 M2 M3 W0 W1 W2 W3 a0 a1 a2 a3 b0 b1 b2 b3
      c0 c1 c2 c3 d0 d1 d2 d3 ⟨va0, va1, va2, va3⟩ ⟨vb0, vb1, vb2, vb3⟩ ⟨vc0, vc1, vc2, vc3⟩
      ⟨vd0, vd1, vd2, vd3⟩ q0.1 q1.1 q2.1 q3.1 qt.1 hcell
    rcases rest with _ | ⟨W4, rest'⟩
    · simpa using hc
    · have ih' := ih (a1 :: a2 :: a3 :: as) (b1 :: b2 :: b3 :: bs) (c1 :: c2 :: c3 :: cs)
        (d1 :: d2 :: d3 :: ds) (.cons va1 (.cons va2 (.cons va3 vas)))
        (.cons vb1 (.cons vb2 (.cons vb3 vbs))) (.cons vc1 (.cons vc2 (.cons vc3 vcs)))
        (.cons vd1 (.cons vd2 (.cons vd3 vds))) q0.2 q1.2 q2.2 q3.2 qt.2 hrest (by simp)
      have e1 : (W1 :: W2 :: W3 :: W4 :: rest').getD 1 0 = W2 := rfl
      have e2 : (W1 :: W2 :: W3 :: W4 :: rest').getD ((W1 :: W2 :: W3 :: W4 :: rest').length - 2)
          0 =
          (W0 :: W1 :: W2 :: W3 :: W4 :: rest').getD
            ((W0 :: W1 :: W2 :: W3 :: W4 :: rest').length - 2) 0 := by
        simp only [List.length_cons]
        rw [show rest'.length + 1 + 1 + 1 + 1 + 1 - 2 = (rest'.length + 1 + 1 + 1 + 1 - 2) + 1 by
          omega]
        rfl
      rw [e1, e2] at ih'
      exact rect_union hc ih'

/-- The `t`-strip facts of the rows: for every window of four grid lines, the records of the
second line carry `LT` with these neighbours. -/
@[expose] def RowsT (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) :
    List ℤ → List (List CRec) → Prop
  | m0 :: m1 :: m2 :: m3 :: ms, _ :: L1 :: L2 :: L3 :: Ls =>
    QuadP (LT fils F m0 m1 m2 m3) F.wn L1 ∧ RowsT fils F (m1 :: m2 :: m3 :: ms) (L1 :: L2 :: L3 ::
        Ls)
  | _, _ => True

/-- **A face.** -/
theorem face_sound (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (hF : Face4OK F) (eta : ℕ)
    (hwn : 4 ≤ F.wn.length) :
    ∀ (g : List ℤ) (Ls : List (List CRec)),
      List.Forall₂ (fun m L => List.Forall₂ (LVal fils F m) F.wn L ∧ QuadP (LW fils F m) F.wn L)
        g Ls →
      RowsT fils F g Ls → cellsAll4 eta F g Ls = true → 4 ≤ g.length →
      RectGood fils F.kind eta ((g.getD 1 0 : ℝ) / 4096) ((g.getD (g.length - 2) 0 : ℝ) / 4096)
        ((F.wn.getD 1 0 : ℝ) / F.wd) ((F.wn.getD (F.wn.length - 2) 0 : ℝ) / F.wd) := by
  intro g
  induction g with
  | nil => intro _ _ _ _ h; simp at h
  | cons m0 g ih =>
    intro Ls hL hT hall hlen
    rcases g with _ | ⟨m1, _ | ⟨m2, _ | ⟨m3, ms⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · simp at hlen
    obtain ⟨L0, L1, L2, L3, Ls', rfl, ⟨v0, q0⟩, ⟨v1, q1⟩, ⟨v2, q2⟩, ⟨v3, q3⟩, hLs⟩ := forall2_four
        hL
    simp only [cellsAll4, Bool.and_eq_true] at hall
    obtain ⟨hrow, hrest⟩ := hall
    simp only [RowsT] at hT
    have hr := row_sound fils F hF eta m0 m1 m2 m3 F.wn L0 L1 L2 L3 v0 v1 v2 v3 q0 q1 q2 q3 hT.1
      hrow hwn
    rcases ms with _ | ⟨m4, ms'⟩
    · simpa using hr
    · have ih' := ih (L1 :: L2 :: L3 :: Ls') (.cons ⟨v1, q1⟩ (.cons ⟨v2, q2⟩ (.cons ⟨v3, q3⟩ hLs)))
        hT.2 hrest (by simp)
      have e1 : (m1 :: m2 :: m3 :: m4 :: ms').getD 1 0 = m2 := rfl
      have e2 : (m1 :: m2 :: m3 :: m4 :: ms').getD ((m1 :: m2 :: m3 :: m4 :: ms').length - 2) 0 =
          (m0 :: m1 :: m2 :: m3 :: m4 :: ms').getD
            ((m0 :: m1 :: m2 :: m3 :: m4 :: ms').length - 2) 0 := by
        simp only [List.length_cons]
        rw [show ms'.length + 1 + 1 + 1 + 1 + 1 - 2 = (ms'.length + 1 + 1 + 1 + 1 - 2) + 1 by
          omega]
        rfl
      rw [e1, e2] at ih'
      exact rect_union_t hr ih'

end PlasmaLean.Design.PolygonCoil
