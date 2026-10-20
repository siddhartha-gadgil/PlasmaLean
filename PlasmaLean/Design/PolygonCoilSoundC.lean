/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSoundB

/-!
# Soundness of the polygonal-coil checker, part C: cells, lines, chunks

* `corner_bound`: a passing grid corner bounds `‖Bseg - hel‖` there;
* `cell_sound` (**cell bound**): four passing corners with `max e + rem + hterm ≤ η` give
  `‖Bseg - hel‖ ≤ η·2⁻⁴⁰` on the whole cell `[φ_m, φ_{m'}] × [w_j, w_{j+1}]`, and distance
  `≥ 1/5` from every segment there.

Lines and chunks: `Design/PolygonCoilSoundD`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- Validity of the coil data. -/
@[expose] def FilsValid (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) : Prop :=
  (∀ f ∈ fils, f.2 ≠ []) ∧ (∀ f ∈ fils, filOK o f.1 f.2 = true) ∧ (allSegs fils).length ≤ nSeg

/-- Validity of a face including its `hel` constants. -/
@[expose] def FaceOK (F : Face) : Prop :=
  FaceValid F ∧ (F.h1n : ℝ) / F.h1d = helPhiC F.kind ∧ (F.h2n : ℝ) / F.h2d = helWC F.kind ∧
    0 < F.h1d ∧ 0 < F.h2d

/-- **Bound at a grid corner.** -/
theorem corner_bound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceValid F) (m : ℕ) (wn : ℤ) (hw : inFace F.kind ((wn : ℝ) / F.wd))
    (r : RC) (gs : List (List ℕ)) (hxyz : (cornerXYZ F m wn).2 = true)
    (hok : (cornerEval o (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ F m wn).1.1
      (cornerXYZ F m wn).1.2.1 (cornerXYZ F m wn).1.2.2.1 (cornerXYZ F m wn).1.2.2.2
      (helAt (helCoef (faceRZ F wn).1 (faceRZ F wn).2) (trigOf m)) r gs).ok = true) :
    ‖Bseg fils (faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd)) -
        hel (faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd))‖ * ((two40 : ℕ) : ℝ) ≤
      (cornerEval o (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ F m wn).1.1
        (cornerXYZ F m wn).1.2.1 (cornerXYZ F m wn).1.2.2.1 (cornerXYZ F m wn).1.2.2.2
        (helAt (helCoef (faceRZ F wn).1 (faceRZ F wn).2) (trigOf m)) r gs).e := by
  obtain ⟨hne, hfok, hlen⟩ := hfv
  obtain ⟨hc, hD⟩ := cornerR_cornerXYZ F hF.2 m wn hxyz
  obtain ⟨hden, hhel⟩ := helAt_corner F hF m wn hw
  rw [← hc] at hhel ⊢
  exact cornerEval_sound o fils hne hfok hlen _ _ _ _ hD _ hden hhel r gs hok

/-- Real meaning of the cell constants `cellRC`. -/
theorem cellRC_facts (F : Face) (hF : FaceOK F) {m m' : ℕ} (hm : m < m') {wn wn' : ℤ}
    (hwn : wn < wn') (hw0 : inFace F.kind ((wn : ℝ) / F.wd)) (D : ℕ) (hD : 0 < D) :
    let rc := (cellRC F m m' wn wn' D).1
    let ht := (cellRC F m m' wn wn' D).2
    let dφ : ℝ := 2 * ((m' : ℝ) - m) * 4096 / (4096 ^ 2 + (m : ℝ) ^ 2)
    let ρm : ℝ := if F.kind < 2 then (cylR F.kind : ℝ) / 181 else (wn' : ℝ) / F.wd
    let dw : ℝ := (wn' : ℝ) / F.wd - (wn : ℝ) / F.wd
    ∃ Can Cbn Cd : ℝ, 0 < Cd ∧ 0 ≤ Can ∧ 0 ≤ Cbn ∧
      Can / Cd = 6 * dφ ^ 2 * ρm ^ 2 + 6 * dw ^ 2 ∧ Cbn / Cd = 10 * dφ ^ 2 * ρm ∧
      rc.doRem = true ∧ (rc.s0l : ℝ) = D * 1073741824 ∧ 0 < rc.s0l ∧
      (D : ℝ) * S32 * (ρm * dφ + dw) ≤ rc.rBD ∧
      (rc.K1 : ℝ) = (D : ℝ) ^ 2 * ((two40 : ℕ) : ℝ) ∧
      (rc.K2 : ℝ) = Can * (D : ℝ) ^ 2 * ((two64 : ℕ) : ℝ) ∧ (rc.K3 : ℝ) = 8 * Cd ∧
      (rc.Cbn : ℝ) = Cbn ∧ (rc.lam2 : ℝ) = ((D : ℝ) * S32) ^ 2 ∧
      ((two40 : ℕ) : ℝ) * (dφ ^ 2 * helPhiC F.kind + dw ^ 2 * helWC F.kind) / 8 ≤ (ht : ℝ) ∧
      0 ≤ ρm ∧ 0 ≤ dφ ∧ 0 < dw := by
  intro rc ht dφ ρm dw
  obtain ⟨⟨hk, hwd⟩, hh1, hh2, hh1d, hh2d⟩ := hF
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set a1 : ℕ := 2 * (m' - m) * qT
  set b1 : ℕ := qT * qT + m * m
  set a2 : ℕ := if F.kind < 2 then (cylR F.kind).toNat else wn'.toNat
  set b2 : ℕ := if F.kind < 2 then 181 else F.wd
  set a3 : ℕ := (wn' - wn).toNat
  set b3 : ℕ := F.wd
  have hb1 : 0 < b1 := Nat.add_pos_left (Nat.mul_pos (by norm_num [qT]) (by norm_num [qT])) _
  have hb2 : 0 < b2 := by simp only [b2]; split_ifs <;> omega
  have hb3 : 0 < b3 := hwd
  have h1 : (a1 : ℝ) / b1 = dφ := by
    simp only [a1, b1, dφ, qT]; push_cast [Nat.cast_sub hm.le]; ring
  have hwpos : inFace F.kind ((wn : ℝ) / F.wd) → (2 ≤ F.kind → 0 < wn') := by
    intro hw hk2
    unfold inFace at hw
    have hc : ¬ F.kind < 2 := by omega
    simp only [hc, ite_false] at hw
    have : (0 : ℝ) < (wn : ℝ) / F.wd := by linarith [hw.1]
    have : (0 : ℝ) < wn := by rwa [lt_div_iff₀ hwd', zero_mul] at this
    have : (0 : ℤ) < wn := by exact_mod_cast this
    omega
  have h2 : (a2 : ℝ) / b2 = ρm := by
    simp only [a2, b2, ρm]
    split_ifs with hc
    · rw [toNat_cast_real (by unfold cylR; split_ifs <;> norm_num)]; norm_num
    · rw [toNat_cast_real (hwpos hw0 (by omega)).le]
  have h3 : (a3 : ℝ) / b3 = dw := by
    simp only [a3, b3, dw]; rw [toNat_cast_real (by omega)]; push_cast; ring
  have hρm : 0 ≤ ρm := by rw [← h2]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdφ : 0 ≤ dφ := by rw [← h1]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hdw : 0 < dw := by
    simp only [dw]; rw [← sub_div]; apply div_pos _ hwd'
    have : (wn : ℝ) < wn' := by exact_mod_cast hwn
    linarith
  refine ⟨((6 * (a1 * a1 * (a2 * a2) * (b3 * b3) + a3 * a3 * (b1 * b1) * (b2 * b2)) : ℕ) : ℝ),
    ((10 * (a1 * a1) * a2 * b2 * (b3 * b3) : ℕ) : ℝ), ((b1 * b1 * (b2 * b2) * (b3 * b3) : ℕ) : ℝ),
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb1 hb1) (Nat.mul_pos hb2 hb2))
      (Nat.mul_pos hb3 hb3)), Nat.cast_nonneg _, Nat.cast_nonneg _, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hρm, hdφ, hdw⟩
  · rw [← h1, ← h2, ← h3]; push_cast; field_simp
  · rw [← h1, ← h2]; push_cast; field_simp
  · simp only [rc, cellRC]; push_cast [two30]; ring
  · simp only [rc, cellRC]; exact Nat.mul_pos hD (by norm_num [two30])
  · simp only [rc, cellRC]
    change (D : ℝ) * S32 * (ρm * dφ + dw) ≤ ((cdiv ((a2 * a1 * b3 + a3 * b1 * b2) * two32)
      (b1 * b2 * b3) * D : ℕ) : ℝ)
    have hcd := cdiv_ge ((a2 * a1 * b3 + a3 * b1 * b2) * two32) (Nat.mul_pos (Nat.mul_pos hb1 hb2)
        hb3)
    push_cast [two32_cast] at hcd ⊢
    rw [← h1, ← h2, ← h3]
    have e : ((a2 : ℝ) / b2 * ((a1 : ℝ) / b1) + (a3 : ℝ) / b3) =
        ((a2 : ℝ) * a1 * b3 + a3 * b1 * b2) / (b1 * b2 * b3) := by field_simp
    rw [e]
    have : ((a2 : ℝ) * a1 * b3 + a3 * b1 * b2) * S32 / (b1 * b2 * b3) ≤
        (cdiv ((a2 * a1 * b3 + a3 * b1 * b2) * two32) (b1 * b2 * b3) : ℝ) := by
      convert hcd using 1
    have := mul_le_mul_of_nonneg_left this hDr.le
    calc (D : ℝ) * S32 * (((a2 : ℝ) * a1 * b3 + a3 * b1 * b2) / (b1 * b2 * b3)) =
        D * (((a2 : ℝ) * a1 * b3 + a3 * b1 * b2) * S32 / (b1 * b2 * b3)) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · simp only [rc, cellRC]; push_cast; ring
  · simp only [rc, cellRC, a1, b1, a2, b2, a3, b3]; push_cast; ring
  · simp only [rc, cellRC, b1, b2, b3]; push_cast; ring
  · simp only [rc, cellRC, a1, a2, b2, b3]
  · simp only [rc, cellRC]; push_cast [sq_cast, two32_cast]; ring
  · simp only [ht, cellRC]
    change _ ≤ ((cdiv ((a1 * a1 * F.h1n * F.h2d * (b3 * b3) + a3 * a3 * F.h2n * F.h1d * (b1 * b1))
      * two40) (8 * (b1 * b1) * (b3 * b3) * F.h1d * F.h2d) : ℕ) : ℝ)
    have hden : 0 < 8 * (b1 * b1) * (b3 * b3) * F.h1d * F.h2d :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.mul_pos hb1 hb1))
        (Nat.mul_pos hb3 hb3)) hh1d) hh2d
    refine le_trans ?_ (cdiv_ge _ hden)
    have hp : helPhiC F.kind = (F.h1n : ℝ) / F.h1d := hh1.symm
    have hw : helWC F.kind = (F.h2n : ℝ) / F.h2d := hh2.symm
    rw [hp, hw, ← h1, ← h3]
    have : (0 : ℝ) < F.h1d := by exact_mod_cast hh1d
    have : (0 : ℝ) < F.h2d := by exact_mod_cast hh2d
    push_cast
    field_simp
    ring_nf
    exact le_refl _

/-- Every vertex of a valid filament has nonnegative translated coordinates. -/
theorem fil_trOK {o : Offs} {K : ℤ} {xs : List (ℤ × ℤ × ℤ)} (h : filOK o K xs = true) :
    ∀ p ∈ xs, trOK p := by
  intro p hp
  unfold filOK at h
  rw [List.all_eq_true] at h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have hmem : (xs[i], (rot1 xs)[i]'(by simp [rot1_length]; omega)) ∈ List.zip xs (rot1 xs) :=
    List.mem_iff_getElem.mpr ⟨i, by simp [rot1_length]; omega, by simp [List.getElem_zip]⟩
  exact (segOK_spec (h _ hmem)).1

/-- Membership in `rot1`. -/
theorem mem_rot1 {α : Type} {xs : List α} {x : α} (h : x ∈ rot1 xs) : x ∈ xs := by
  cases xs with
  | nil => simp [rot1] at h
  | cons y ys =>
    simp only [rot1, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact List.mem_cons_of_mem _ h
    · exact List.mem_cons_self

/-- The segments of the coil set: endpoints valid and `segOK`. -/
theorem allSegs_valid {o : Offs} {fils : List (ℤ × List (ℤ × ℤ × ℤ))}
    (hfok : ∀ f ∈ fils, filOK o f.1 f.2 = true) :
    ∀ s ∈ allSegs fils, trOK s.2.1 ∧ trOK s.2.2 ∧ segOK o s.1 s.2.1 s.2.2 = true := by
  intro s hs
  simp only [allSegs, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨f, hf, pq, hpq, rfl⟩ := hs
  have hok := hfok f hf
  have htr := fil_trOK hok
  refine ⟨htr _ (List.of_mem_zip hpq).1, htr _ (mem_rot1 (List.of_mem_zip hpq).2), ?_⟩
  unfold filOK at hok; rw [List.all_eq_true] at hok
  exact hok _ hpq

/-- `|κ||q - p| ≤ kv/2⁶⁴`. -/
theorem kvR_le {o : Offs} {K : ℤ} {p q : ℤ × ℤ × ℤ} (h : segOK o K p q = true) :
    kvR (K, p, q) ≤ ((mkSeg o K p q).kv : ℝ) / ((two64 : ℕ) : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hvv⟩ := segOK_spec h
  set vv : ℤ := (q.1 - p.1) * (q.1 - p.1) + (q.2.1 - p.2.1) * (q.2.1 - p.2.1) +
    (q.2.2 - p.2.2) * (q.2.2 - p.2.2)
  have hvv0 : 0 ≤ vv := by
    nlinarith [mul_self_nonneg (q.1 - p.1), mul_self_nonneg (q.2.1 - p.2.1),
      mul_self_nonneg (q.2.2 - p.2.2)]
  have hS := S32_pos
  have hnorm : ‖ptR q - ptR p‖ = Real.sqrt (vv : ℝ) / S32 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_coords]
    simp only [ptR, PiLp.sub_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [show ((q.1 : ℝ) / S32 - p.1 / S32) ^ 2 + ((q.2.1 : ℝ) / S32 - p.2.1 / S32) ^ 2 +
        ((q.2.2 : ℝ) / S32 - p.2.2 / S32) ^ 2 = (vv : ℝ) / S32 ^ 2 by
          simp only [vv]; push_cast; field_simp,
      Real.sqrt_div (by positivity), Real.sqrt_sq hS.le]
  have hup : Real.sqrt (vv : ℝ) ≤ (sqrtUp vv.toNat : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    have := (by exact_mod_cast hvv : (vv : ℝ) ≤ ((sqrtUp vv.toNat : ℤ) : ℝ) * ((sqrtUp vv.toNat :
        ℤ) : ℝ))
    push_cast at this; nlinarith
  unfold kvR
  simp only
  rw [hnorm]
  have hkv : ((mkSeg o K p q).kv : ℝ) = |(K : ℝ)| * (sqrtUp vv.toNat : ℝ) := by
    simp only [mkSeg, Nat.mul_eq]; push_cast [Nat.cast_natAbs, Int.cast_abs]; rfl
  rw [hkv, abs_div, abs_of_pos hS]
  have h64 : ((two64 : ℕ) : ℝ) = S32 ^ 2 := by norm_num [two64, S32]
  rw [h64]
  have : |(K : ℝ)| / S32 * (Real.sqrt (vv : ℝ) / S32) = |(K : ℝ)| * Real.sqrt vv / S32 ^ 2 := by
    field_simp
  rw [this]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left hup (abs_nonneg _)

/-- The real remainder bound of one segment on a cell, from its `remTerm`. -/
theorem seg_cell_term {kvz : ℕ} {kv dφ dφu ρm dw d : ℝ} (hkv : 0 ≤ kv)
    (hkvz : kv ≤ (kvz : ℝ) / ((two64 : ℕ) : ℝ)) (hd : 1 / 5 ≤ d) (hφ : 0 ≤ dφ) (hφu : dφ ≤ dφu)
    (hρ : 0 ≤ ρm) (_hdw : 0 ≤ dw) {Can Cbn Cd : ℝ} (_hCd : 0 < Cd)
    (hCa : Can / Cd = 6 * dφu ^ 2 * ρm ^ 2 + 6 * dw ^ 2) (hCb : Cbn / Cd = 10 * dφu ^ 2 * ρm) :
    kv * (6 * ρm ^ 2 / d ^ 4 + 2 * ρm / d ^ 3) * dφ ^ 2 / 8 + kv * (6 / d ^ 4) * dw ^ 2 / 8 ≤
      ((kvz : ℝ) / ((two64 : ℕ) : ℝ) * ((two40 : ℕ) : ℝ) * (Can / Cd / d ^ 4 + Cbn / Cd / d ^ 2) /
          8) /
        ((two40 : ℕ) : ℝ) := by
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hd0 : 0 < d := by linarith
  rw [hCa, hCb]
  have hφ2 : dφ ^ 2 ≤ dφu ^ 2 := pow_le_pow_left₀ hφ hφu 2
  have h3 : 2 * ρm / d ^ 3 ≤ 10 * ρm / d ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * d ^ 2 ≤ 10 * d ^ 3 := by nlinarith [sq_nonneg d]
    nlinarith [mul_le_mul_of_nonneg_left this hρ]
  have e : ((kvz : ℝ) / ((two64 : ℕ) : ℝ) * ((two40 : ℕ) : ℝ) *
      ((6 * dφu ^ 2 * ρm ^ 2 + 6 * dw ^ 2) / d ^ 4 + 10 * dφu ^ 2 * ρm / d ^ 2) / 8) /
        ((two40 : ℕ) : ℝ) = (kvz : ℝ) / ((two64 : ℕ) : ℝ) *
      ((6 * dφu ^ 2 * ρm ^ 2 + 6 * dw ^ 2) / d ^ 4 + 10 * dφu ^ 2 * ρm / d ^ 2) / 8 := by
    field_simp
  rw [e]
  have hA : kv * (6 * ρm ^ 2 / d ^ 4 + 2 * ρm / d ^ 3) * dφ ^ 2 / 8 + kv * (6 / d ^ 4) * dw ^ 2 / 8
      ≤
      kv * ((6 * dφu ^ 2 * ρm ^ 2 + 6 * dw ^ 2) / d ^ 4 + 10 * dφu ^ 2 * ρm / d ^ 2) / 8 := by
    have h4 : 0 ≤ 6 * ρm ^ 2 / d ^ 4 + 2 * ρm / d ^ 3 := by positivity
    have hX : (6 * ρm ^ 2 / d ^ 4 + 2 * ρm / d ^ 3) * dφ ^ 2 ≤
        (6 * ρm ^ 2 / d ^ 4 + 10 * ρm / d ^ 2) * dφu ^ 2 :=
      mul_le_mul (by linarith) hφ2 (by positivity) (by positivity)
    have e2 : (6 * dφu ^ 2 * ρm ^ 2 + 6 * dw ^ 2) / d ^ 4 + 10 * dφu ^ 2 * ρm / d ^ 2 =
        (6 * ρm ^ 2 / d ^ 4 + 10 * ρm / d ^ 2) * dφu ^ 2 + 6 / d ^ 4 * dw ^ 2 := by
      field_simp; ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hX hkv
    nlinarith
  refine hA.trans ?_
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_right hkvz (by positivity)

theorem one_fifth_le {lam d : ℝ} (hl : 0 < lam) (hd : 0 < d) (h : lam ^ 2 ≤ 25 * (lam ^ 2 * d ^ 2))
    :
    1 / 5 ≤ d := by
  have hl2 : 0 < lam ^ 2 := by positivity
  have h1 : 1 ≤ 25 * d ^ 2 := by
    have : lam ^ 2 * 1 ≤ lam ^ 2 * (25 * d ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hl2
  by_contra hc
  push Not at hc
  have : d ^ 2 < (1 / 5) ^ 2 := pow_lt_pow_left₀ hc hd.le two_ne_zero
  linarith

theorem list_sum_map_div {ι : Type} (L : List ι) (f : ι → ℝ) (c : ℝ) :
    (L.map fun z => f z / c).sum = (L.map f).sum / c := by
  induction L with
  | nil => simp
  | cons z L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem sum_two_le {ι : Type} (L : List ι) (F G T : ι → ℝ) (c1 c2 : ℝ)
    (h : ∀ z ∈ L, F z * c1 / 8 + G z * c2 / 8 ≤ T z) :
    (L.map F).sum * c1 / 8 + (L.map G).sum * c2 / 8 ≤ (L.map T).sum := by
  induction L with
  | nil => simp
  | cons z L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h z (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    linarith

/-- Shorthand for the corner evaluation at the grid corner `(m, wn)` of face `F`. -/
@[expose] def cornerAt (o : Offs) (fs : List Fil) (F : Face) (m : ℕ) (wn : ℤ) (r : RC)
    (gs : List (List ℕ)) : CornerOut :=
  cornerEval o fs (cornerXYZ F m wn).1.1 (cornerXYZ F m wn).1.2.1 (cornerXYZ F m wn).1.2.2.1
    (cornerXYZ F m wn).1.2.2.2 (helAt (helCoef (faceRZ F wn).1 (faceRZ F wn).2) (trigOf m)) r gs

/-- **The cell bound.** Four passing corners `(m, wn)`, `(m', wn)`, `(m, wn')`, `(m', wn')`, the
first carrying the cell remainder, with `max e + rem + hterm ≤ η`, give
`‖Bseg - hel‖ ≤ η 2⁻⁴⁰` on the cell, and every point of the cell is at distance `≥ 1/5` from
every segment. -/
theorem cell_sound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (hfv : FilsValid o fils)
    (F : Face) (hF : FaceOK F) {m m' : ℕ} (hm : m < m') {wn wn' : ℤ} (hwn : wn < wn')
    (hw0 : inFace F.kind ((wn : ℝ) / F.wd)) (hw1 : inFace F.kind ((wn' : ℝ) / F.wd))
    (r10 r01 r11 : RC) (g00 g10 g01 g11 : List (List ℕ))
    (hx00 : (cornerXYZ F m wn).2 = true) (hx10 : (cornerXYZ F m' wn).2 = true)
    (hx01 : (cornerXYZ F m wn').2 = true) (hx11 : (cornerXYZ F m' wn').2 = true)
    (h00 : (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m wn
      (cellRC F m m' wn wn' (cornerXYZ F m wn).1.2.2.2).1 g00).ok = true)
    (h10 : (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m' wn r10 g10).ok = true)
    (h01 : (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m wn' r01 g01).ok = true)
    (h11 : (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m' wn' r11 g11).ok = true)
    (hη : nmax (nmax (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m wn
        (cellRC F m m' wn wn' (cornerXYZ F m wn).1.2.2.2).1 g00).e
        (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m wn' r01 g01).e)
        (nmax (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m' wn r10 g10).e
          (cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m' wn' r11 g11).e) +
        ((cornerAt o (fils.map fun f => mkFil o f.1 f.2) F m wn
          (cellRC F m m' wn wn' (cornerXYZ F m wn).1.2.2.2).1 g00).rem +
          (cellRC F m m' wn wn' (cornerXYZ F m wn).1.2.2.2).2) ≤ etaFp) :
    ∀ φ ∈ Icc (phiM m) (phiM m'), ∀ w ∈ Icc ((wn : ℝ) / F.wd) ((wn' : ℝ) / F.wd),
      ‖Bseg fils (faceSigma F.kind φ w) - hel (faceSigma F.kind φ w)‖ ≤
        (etaFp : ℝ) / ((two40 : ℕ) : ℝ) ∧
      ∀ s ∈ allSegs fils, ∀ t ∈ Icc (0 : ℝ) 1,
        1 / 5 ≤ ‖faceSigma F.kind φ w - seg (ptR s.2.1) (ptR s.2.2) t‖ := by
  intro φ hφ w hw
  set fs := fils.map fun f => mkFil o f.1 f.2
  have hFv := hF.1
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hFv.2
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  set D := (cornerXYZ F m wn).1.2.2.2
  obtain ⟨hyc, hD⟩ := cornerR_cornerXYZ F hFv.2 m wn hx00
  set rc := (cellRC F m m' wn wn' D).1
  set ht := (cellRC F m m' wn wn' D).2
  set c00 := cornerAt o fs F m wn rc g00
  set c10 := cornerAt o fs F m' wn r10 g10
  set c01 := cornerAt o fs F m wn' r01 g01
  set c11 := cornerAt o fs F m' wn' r11 g11
  set emax := nmax (nmax c00.e c01.e) (nmax c10.e c11.e)
  -- corner bounds
  have b00 := corner_bound o fils hfv F hFv m wn hw0 rc g00 hx00 h00
  have b10 := corner_bound o fils hfv F hFv m' wn hw0 r10 g10 hx10 h10
  have b01 := corner_bound o fils hfv F hFv m wn' hw1 r01 g01 hx01 h01
  have b11 := corner_bound o fils hfv F hFv m' wn' hw1 r11 g11 hx11 h11
  have hemax : ∀ x : ℕ, x = c00.e ∨ x = c10.e ∨ x = c01.e ∨ x = c11.e → (x : ℝ) ≤ emax := by
    intro x hx
    have a1 := nmax_ge_left c00.e c01.e
    have a2 := nmax_ge_right c00.e c01.e
    have a3 := nmax_ge_left c10.e c11.e
    have a4 := nmax_ge_right c10.e c11.e
    have a5 := nmax_ge_left (nmax c00.e c01.e) (nmax c10.e c11.e)
    have a6 := nmax_ge_right (nmax c00.e c01.e) (nmax c10.e c11.e)
    rcases hx with rfl | rfl | rfl | rfl <;> exact_mod_cast (by omega)
  have cb : ∀ (x : ℝ) (n : ℕ), x * ((two40 : ℕ) : ℝ) ≤ n → (n : ℝ) ≤ emax → x ≤ (emax : ℝ) /
      ((two40 : ℕ) : ℝ) := by
    intro x n h1 h2
    rw [le_div_iff₀ h40]; linarith
  have e00 := cb _ _ b00 (hemax _ (Or.inl rfl))
  have e10 := cb _ _ b10 (hemax _ (Or.inr (Or.inl rfl)))
  have e01 := cb _ _ b01 (hemax _ (Or.inr (Or.inr (Or.inl rfl))))
  have e11 := cb _ _ b11 (hemax _ (Or.inr (Or.inr (Or.inr rfl))))
  -- cell constants
  obtain ⟨Can, Cbn, Cd, hCd, hCan, hCbn, hCa, hCb, hdoRem, hs0, hs0p, hrBD, hK1, hK2, hK3, hCbnE,
    hlam2, hht, hρm, hdφ, hdw⟩ := cellRC_facts F hF hm hwn hw0 D hD
  set dφu : ℝ := 2 * ((m' : ℝ) - m) * 4096 / (4096 ^ 2 + (m : ℝ) ^ 2)
  set ρm : ℝ := if F.kind < 2 then (cylR F.kind : ℝ) / 181 else (wn' : ℝ) / F.wd
  set dw : ℝ := (wn' : ℝ) / F.wd - (wn : ℝ) / F.wd
  obtain ⟨hne, hfok, hlen⟩ := hfv
  -- the remainder records of the reference corner
  obtain ⟨R, hRsegs, hRall, hrem, -⟩ := cornerEval_rem o fils hne hfok _ _ _ D hD _ rc hdoRem g00
      h00
  set Xt := (cornerXYZ F m wn).1.1
  set Yt := (cornerXYZ F m wn).1.2.1
  set Zt := (cornerXYZ F m wn).1.2.2.1
  set cy := mkCD Xt Yt Zt D
  set y := cornerR Xt Yt Zt D
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set lam : ℝ := (D : ℝ) * S32
  have hlam : 0 < lam := mul_pos hDr S32_pos
  have hsv := allSegs_valid hfok
  set Ls : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → ℕ := fun s => cellL rc (d2Low (vertN cy (mkVt s.2.1))
    (vertN cy (mkVt s.2.2)) (Nat.mul (Nat.mul D D) (mkSeg o s.1 s.2.1 s.2.2).vv))
  set dd : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → ℝ := fun s => Real.sqrt (Ls s) / lam
  have hproj : ∀ z ∈ R, (z.1, z.2.1, z.2.2.1) ∈ allSegs fils := by
    intro z hz; rw [← hRsegs]; exact List.mem_map_of_mem hz
  -- exact vertex distances of the records
  have hneq : ∀ z ∈ R, z.2.2.2.1.n = vertN cy (mkVt z.2.1) ∧ z.2.2.2.2.n = vertN cy (mkVt z.2.2.1)
      := by
    intro z hz
    obtain ⟨ha, hb, -, -⟩ := hRall z hz
    obtain ⟨tp, tq, -⟩ := hsv _ (hproj z hz)
    constructor
    · have := ha.1; rw [← vertN_eq Xt Yt Zt D hD tp] at this; exact_mod_cast this
    · have := hb.1; rw [← vertN_eq Xt Yt Zt D hD tq] at this; exact_mod_cast this
  -- per-record facts
  have hz : ∀ z ∈ R, 0 < Ls (z.1, z.2.1, z.2.2.1) ∧ 1 / 5 ≤ dd (z.1, z.2.1, z.2.2.1) ∧
      (∀ φ' ∈ Icc (phiM m) (phiM m'), ∀ w' ∈ Icc ((wn : ℝ) / F.wd) ((wn' : ℝ) / F.wd),
        ∀ t ∈ Icc (0 : ℝ) 1, dd (z.1, z.2.1, z.2.2.1) ≤
          ‖faceSigma F.kind φ' w' - seg (ptR z.2.1) (ptR z.2.2.1) t‖) ∧
      kvR (z.1, z.2.1, z.2.2.1) * (6 * ρm ^ 2 / dd (z.1, z.2.1, z.2.2.1) ^ 4 +
          2 * ρm / dd (z.1, z.2.1, z.2.2.1) ^ 3) * (phiM m' - phiM m) ^ 2 / 8 +
        kvR (z.1, z.2.1, z.2.2.1) * (6 / dd (z.1, z.2.1, z.2.2.1) ^ 4) * dw ^ 2 / 8 ≤
        ((remTerm rc z.2.2.2.1.n z.2.2.2.2.n (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)
          (mkSeg o z.1 z.2.1 z.2.2.1).kv).1 : ℝ) / ((two40 : ℕ) : ℝ) := by
    intro z hz
    obtain ⟨ha, hb, hs, hrt⟩ := hRall z hz
    obtain ⟨hna, hnb⟩ := hneq z hz
    rw [hna, hnb] at hrt ⊢
    obtain ⟨hLpos, h25, hterm⟩ := remTerm_sound rc _ _ _ _ hrt hDr hCd hK1 hK2 hK3 hCbnE hCan hCbn
      hlam2
    have hLr : (0 : ℝ) < Ls (z.1, z.2.1, z.2.2.1) := by exact_mod_cast hLpos
    have hddpos : 0 < dd (z.1, z.2.1, z.2.2.1) := div_pos (Real.sqrt_pos.mpr hLr) hlam
    have hdd2 : lam ^ 2 * dd (z.1, z.2.1, z.2.2.1) ^ 2 = Ls (z.1, z.2.1, z.2.2.1) := by
      simp only [dd]; rw [div_pow, Real.sq_sqrt hLr.le]; field_simp
    have hd5 : 1 / 5 ≤ dd (z.1, z.2.1, z.2.2.1) :=
      one_fifth_le hlam hddpos (by rw [hdd2]; exact h25)
    refine ⟨hLpos, hd5, ?_, ?_⟩
    · intro φ' hφ' w' hw' t ht
      -- distance from the reference corner
      have hxy : lam * ‖faceSigma F.kind φ' w' - y‖ ≤ rc.rBD := by
        rw [hyc]
        have h1 := faceSigma_phi_dist F.kind (w := w') hφ'.1
        have h2 := faceSigma_w_dist F.kind (φ := phiM m) hw'.1
        have hρw : |(if F.kind < 2 then (cylR F.kind : ℝ) / 181 else w')| ≤ ρm := by
          simp only [ρm]; split_ifs with hk2
          · exact le_of_eq (abs_of_pos (by unfold cylR; split_ifs <;> norm_num))
          · have : 0 ≤ w' := by
              unfold inFace at hw0
              simp only [hk2, ite_false] at hw0
              linarith [hw0.1, hw'.1]
            rw [abs_of_nonneg this]; exact hw'.2
        have hdφu : phiM m' - phiM m ≤ dφu := phiM_sub_le hm.le
        have htri : ‖faceSigma F.kind φ' w' - faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd)‖ ≤
            ρm * dφu + dw := by
          calc _ = ‖(faceSigma F.kind φ' w' - faceSigma F.kind (phiM m) w') +
                (faceSigma F.kind (phiM m) w' - faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd))‖ := by
                congr 1; abel
            _ ≤ _ := norm_add_le _ _
            _ ≤ |(if F.kind < 2 then (cylR F.kind : ℝ) / 181 else w')| * (φ' - phiM m) +
                (w' - (wn : ℝ) / F.wd) := add_le_add h1 h2
            _ ≤ ρm * dφu + dw := by
                apply add_le_add
                · exact mul_le_mul hρw (by linarith [hφ'.2]) (by linarith [hφ'.1]) hρm
                · simp only [dw]; linarith [hw'.2]
        calc lam * ‖faceSigma F.kind φ' w' - faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd)‖ ≤
            lam * (ρm * dφu + dw) := mul_le_mul_of_nonneg_left htri hlam.le
          _ ≤ rc.rBD := hrBD
      -- the scaled endpoints
      set A := lam • (ptR z.2.1 - y)
      set B := lam • (ptR z.2.2.1 - y)
      have hA : ((vertN cy (mkVt z.2.1) : ℕ) : ℝ) = ‖A‖ ^ 2 := by
        rw [vertN_eq Xt Yt Zt D hD (hsv _ (hproj z hz)).1, norm_smul, Real.norm_eq_abs,
          abs_of_pos hlam]; ring
      have hB : ((vertN cy (mkVt z.2.2.1) : ℕ) : ℝ) = ‖B‖ ^ 2 := by
        rw [vertN_eq Xt Yt Zt D hD (hsv _ (hproj z hz)).2.1, norm_smul, Real.norm_eq_abs,
          abs_of_pos hlam]; ring
      have hw := mkSeg_weights hs
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvv⟩ := hw
      have hBA : ((Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv : ℕ) : ℝ) = ‖B - A‖ ^ 2 :=
          by
        rw [lam_diff_norm Xt Yt Zt D hD z.2.1 z.2.2.1]
        push_cast [Nat.mul_eq]; rw [hvv]; push_cast; ring
      have hvvpos : 0 < Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpos, -⟩ := segOK_spec hs
        have : 0 < (mkSeg o z.1 z.2.1 z.2.2.1).vv := by
          simp only [mkSeg]; omega
        exact Nat.mul_pos (Nat.mul_pos hD hD) this
      have hd2 := d2Low_sound hA hB hBA hvvpos ht
      have hseg : A + t • (B - A) = lam • (seg (ptR z.2.1) (ptR z.2.2.1) t - y) := by
        simp only [A, B, seg]; module
      rw [hseg, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, mul_pow, norm_sub_rev] at hd2
      have hrs : rc.rBD ≤ rc.s0l := by
        have hh : (cornerAt o fs F m wn rc g00).ok = true := h00
        simp only [cornerAt, cornerEval, Bool.and_eq_true] at hh
        obtain ⟨-, hr⟩ := hh
        rw [hdoRem] at hr
        simpa using hr
      have hcl := cellL_sound rc hlam hd2 hxy hrs hs0p hLpos
      -- conclude
      have : lam ^ 2 * dd (z.1, z.2.1, z.2.2.1) ^ 2 ≤
          lam ^ 2 * ‖faceSigma F.kind φ' w' - seg (ptR z.2.1) (ptR z.2.2.1) t‖ ^ 2 := by
        rw [hdd2]; exact hcl
      have h2 : dd (z.1, z.2.1, z.2.2.1) ^ 2 ≤
          ‖faceSigma F.kind φ' w' - seg (ptR z.2.1) (ptR z.2.2.1) t‖ ^ 2 :=
        le_of_mul_le_mul_left this (by positivity)
      exact (pow_le_pow_iff_left₀ hddpos.le (norm_nonneg _) two_ne_zero).mp h2
    · have hterm' := hterm (dd (z.1, z.2.1, z.2.2.1)) hddpos (by rw [hdd2])
      have hk := kvR_le hs
      refine (seg_cell_term (kvz := (mkSeg o z.1 z.2.1 z.2.2.1).kv) (by unfold kvR; positivity) hk
          hd5
        (by linarith [phiM_lt hm]) (phiM_sub_le hm.le) hρm hdw.le hCd hCa hCb).trans ?_
      exact div_le_div_of_nonneg_right hterm' h40.le
  -- apply the analytic cell bound
  have hseg_rec : ∀ s ∈ allSegs fils, ∃ z ∈ R, (z.1, z.2.1, z.2.2.1) = s := by
    intro s hs; rw [← hRsegs] at hs; exact List.mem_map.mp hs
  refine ⟨?_, fun s hs t ht => ?_⟩
  swap
  · obtain ⟨z, hz', rfl⟩ := hseg_rec s hs
    obtain ⟨-, h5, hd, -⟩ := hz z hz'
    exact h5.trans (hd φ hφ w hw t ht)
  have hwlt : (wn : ℝ) / F.wd < (wn' : ℝ) / F.wd := by
    apply div_lt_div_of_pos_right _ hwd'; exact_mod_cast hwn
  have hρcell : ∀ w' ∈ Icc ((wn : ℝ) / F.wd) ((wn' : ℝ) / F.wd),
      |(if F.kind < 2 then (cylR F.kind : ℝ) / 181 else w')| ≤ ρm := by
    intro w' hw'
    simp only [ρm]; split_ifs with hk2
    · exact le_of_eq (abs_of_pos (by unfold cylR; split_ifs <;> norm_num))
    · have : 0 ≤ w' := by
        unfold inFace at hw0
        simp only [hk2, ite_false] at hw0
        linarith [hw0.1, hw'.1]
      rw [abs_of_nonneg this]; exact hw'.2
  have hA := cell_analytic hFv.1 (allSegs fils) dd (phiM_lt hm) hwlt hw0 hw1 hρm hρcell
    (fun s hs => by
      obtain ⟨z, hz', rfl⟩ := hseg_rec s hs
      exact lt_of_lt_of_le (by norm_num) (hz z hz').2.1)
    (fun s hs => by
      obtain ⟨z, hz', rfl⟩ := hseg_rec s hs
      exact (hz z hz').2.2.1)
    e00 e10 e01 e11 hφ hw
  rw [Bseg_eq_BL]
  refine hA.trans ?_
  -- the remainder sums
  have hrsum : (c00.rem : ℝ) = (R.map fun z => ((remTerm rc z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv) (mkSeg o z.1 z.2.1 z.2.2.1).kv).1 :
          ℝ)).sum := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hrem
    refine h.trans ?_
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  have hsum : ((allSegs fils).map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum
      *
        (phiM m' - phiM m) ^ 2 / 8 +
      ((allSegs fils).map fun z => kvR z * (6 / dd z ^ 4)).sum * dw ^ 2 / 8 ≤
      (c00.rem : ℝ) / ((two40 : ℕ) : ℝ) := by
    rw [← hRsegs, List.map_map, List.map_map, hrsum, ← list_sum_map_div]
    refine sum_two_le R _ _ _ _ _ fun z hz' => ?_
    have := (hz z hz').2.2.2
    simp only [Function.comp]
    linarith
  have hhel : helPhiC F.kind * (phiM m' - phiM m) ^ 2 / 8 + helWC F.kind * dw ^ 2 / 8 ≤
      (ht : ℝ) / ((two40 : ℕ) : ℝ) := by
    rw [le_div_iff₀ h40]
    have hφ2 : (phiM m' - phiM m) ^ 2 ≤ dφu ^ 2 :=
      pow_le_pow_left₀ (by linarith [phiM_lt hm]) (phiM_sub_le hm.le) 2
    have hHφ : 0 ≤ helPhiC F.kind := by unfold helPhiC; split_ifs <;> norm_num
    have h1 := mul_le_mul_of_nonneg_left hφ2 hHφ
    calc (helPhiC F.kind * (phiM m' - phiM m) ^ 2 / 8 + helWC F.kind * dw ^ 2 / 8) *
          ((two40 : ℕ) : ℝ) ≤ (helPhiC F.kind * dφu ^ 2 / 8 + helWC F.kind * dw ^ 2 / 8) *
          ((two40 : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ h40.le; linarith
      _ = ((two40 : ℕ) : ℝ) * (dφu ^ 2 * helPhiC F.kind + dw ^ 2 * helWC F.kind) / 8 := by ring
      _ ≤ ht := hht
  have hη' : ((emax : ℕ) : ℝ) + ((c00.rem : ℕ) : ℝ) + (ht : ℝ) ≤ etaFp := by
    have := (by exact_mod_cast hη : ((emax + (c00.rem + ht) : ℕ) : ℝ) ≤ (etaFp : ℝ))
    push_cast at this; linarith
  have e1 : (emax : ℝ) / ((two40 : ℕ) : ℝ) +
      (((allSegs fils).map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum +
        helPhiC F.kind) * (phiM m' - phiM m) ^ 2 / 8 +
      (((allSegs fils).map fun z => kvR z * (6 / dd z ^ 4)).sum + helWC F.kind) *
        ((wn' : ℝ) / F.wd - (wn : ℝ) / F.wd) ^ 2 / 8 =
      (emax : ℝ) / ((two40 : ℕ) : ℝ) +
      (((allSegs fils).map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum *
        (phiM m' - phiM m) ^ 2 / 8 +
      ((allSegs fils).map fun z => kvR z * (6 / dd z ^ 4)).sum * dw ^ 2 / 8) +
      (helPhiC F.kind * (phiM m' - phiM m) ^ 2 / 8 + helWC F.kind * dw ^ 2 / 8) := by
    simp only [dw]; ring
  rw [e1]
  calc _ ≤ (emax : ℝ) / ((two40 : ℕ) : ℝ) + (c00.rem : ℝ) / ((two40 : ℕ) : ℝ) +
        (ht : ℝ) / ((two40 : ℕ) : ℝ) := by linarith
    _ = ((emax : ℝ) + c00.rem + ht) / ((two40 : ℕ) : ℝ) := by ring
    _ ≤ (etaFp : ℝ) / ((two40 : ℕ) : ℝ) := div_le_div_of_nonneg_right hη' h40.le

end PlasmaLean.Design.PolygonCoil
