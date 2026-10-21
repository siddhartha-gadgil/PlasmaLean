/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicSoundB

/-!
# Soundness of the cubic checker, part C: the remainders of one corner

* `remP4_facts`: real meaning of the remainder parameters `remP4` (radii, `λ`-powers and kernel
  constants);
* `corner_w_bound`: if a corner with remainder parameters passes, the cubic interpolation error of
  `⟨n, Bseg - hel⟩` along the `w`-line through the corner, on the cell `[w, w⁺]`, is at most
  `rwC/2⁴⁰`;
* `corner_t_bound`: the same along the `t`-direction on the strip `[t, t⁺] × [w, w⁺]`, at most
  `rtC/2⁴⁰`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-! ## Notation -/

/-- The face point at `(t, w)`. -/
@[expose] def ptF (kind : ℕ) (t w : ℝ) : Space := faceSigma kind (phiT t) w

/-- The field error `Bseg - hel`. -/
@[expose] def errF (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) : Space := Bseg fils y - hel y

/-- Validity of the coil data for the cubic checker (segment count bound `nS`). -/
@[expose] def FilsOK4 (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) : Prop :=
  (∀ f ∈ fils, f.2 ≠ []) ∧ (∀ f ∈ fils, filOK o f.1 f.2 = true) ∧ (allSegs fils).length ≤ nS

/-- Validity of a cubic face, including the `hel` constants `HT ≥ 2000`, `HW ≥ 1000`. -/
@[expose] def Face4OK (F : Face4) : Prop :=
  F.kind < 4 ∧ 0 < F.wd ∧ 0 < F.htd ∧ 0 < F.hwd ∧ (2000 : ℝ) ≤ (F.htn : ℝ) / F.htd ∧
    (1000 : ℝ) ≤ (F.hwn : ℝ) / F.hwd

/-! ## Elementary facts -/

theorem iabs_cast (a : ℤ) : ((iabs a : ℕ) : ℝ) = |(a : ℝ)| := by
  simp [iabs, Nat.cast_natAbs, Int.cast_abs]

/-- Cast of `nmax`. -/
theorem nmax_cast (a b : ℕ) : ((nmax a b : ℕ) : ℝ) = max (a : ℝ) b := by
  unfold nmax
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; simp [h]
  · have hb : Nat.ble a b = false := by
      cases hh : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hh) h
    rw [hb]
    have : (b : ℝ) ≤ a := by exact_mod_cast (le_of_lt (not_le.mp h))
    simp [this]

/-- Along `w` the face point moves on a unit-speed line. -/
theorem faceSigma_w_norm (kind : ℕ) (φ w w0 : ℝ) :
    ‖faceSigma kind φ w - faceSigma kind φ w0‖ = |w - w0| := by
  have e : faceSigma kind φ w - faceSigma kind φ w0 = (w - w0) • faceW kind φ := by
    unfold faceSigma faceW
    by_cases hk : kind < 2
    · simp only [hk, ite_true, polarPt_eq]; module
    · simp only [hk, ite_false, polarPt_eq]; module
  rw [e, norm_smul, norm_faceW, mul_one, Real.norm_eq_abs]

/-- The segment of a semantic record. -/
@[expose] def seg3 (z : SRec) : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) := (z.1, z.2.1, z.2.2.1)

/-- The `w`-distance bound of a record: `√L_w/λ`. -/
@[expose] def ddW (D : ℕ) (Q : RemP) (o : Offs) (z : SRec) : ℝ :=
  Real.sqrt (cellL Q.rcW (d2Low z.2.2.2.1.n z.2.2.2.2.n
    (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv))) / ((D : ℝ) * S32)

/-- The `t`-distance bound of a record: `√L_t/λ`. -/
@[expose] def ddT (D : ℕ) (Q : RemP) (o : Offs) (z : SRec) : ℝ :=
  Real.sqrt (cellL Q.rcT (d2Low z.2.2.2.1.n z.2.2.2.2.n
    (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv))) / ((D : ℝ) * S32)

/-- From the record check: distance bound along any curve that stays in the ball of radius
`rBD/λ` around the corner. -/
theorem dd_le {o : Offs} {Xt Yt Zt D : ℕ} (hD : 0 < D) {z : SRec}
    (hva : VRok Xt Yt Zt D z.2.1 z.2.2.2.1) (hvb : VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2)
    (hs : segOK o z.1 z.2.1 z.2.2.1 = true) (rc : RC) (hrs : rc.rBD ≤ rc.s0l) (hs0 : 0 < rc.s0l)
    (hL : 0 < cellL rc (d2Low z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)))
    {x : Space} (hx : (D : ℝ) * S32 * ‖x - cornerR Xt Yt Zt D‖ ≤ rc.rBD) {s : ℝ}
    (hs' : s ∈ Icc (0 : ℝ) 1) :
    Real.sqrt (cellL rc (d2Low z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv))) / ((D : ℝ) * S32) ≤
      ‖x - seg (ptR z.2.1) (ptR z.2.2.1) s‖ := by
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have h := rec_dist hD hva hvb hs rc hrs hs0 hL hx hs'
  rw [div_le_iff₀ hlam, Real.sqrt_le_left (by positivity)]
  nlinarith [h]

/-- **The `w`-line remainder of the coil field from the corner records.** -/
theorem wline_coil (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) {Xt Yt Zt D : ℕ} (hD : 0 < D)
    (n : Space) (hn : ‖n‖ ≤ 1) (R : List SRec) (hR : R.map seg3 = allSegs fils) (Q : RemP)
    (hrec : ∀ z ∈ R, VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
      segOK o z.1 z.2.1 z.2.2.1 = true ∧ remChk (Nat.mul D D) Q (srTriple o z) = true)
    (hrs : Q.rcW.rBD ≤ Q.rcW.s0l) (hs0 : 0 < Q.rcW.s0l)
    (hw6 : 120 * ((D : ℝ) * S32) ^ 6 ≤ Q.w6) (kind : ℕ) (φ : ℝ) {W0 W1 W2 W3 w : ℝ}
    (h01 : W0 < W1) (h12 : W1 < W2) (h23 : W2 < W3) (hw : w ∈ Icc W1 W2)
    (hreach : ∀ v ∈ Icc W0 W3, (D : ℝ) * S32 * ‖faceSigma kind φ v - cornerR Xt Yt Zt D‖ ≤
      Q.rcW.rBD) :
    |⟪n, Bseg fils (faceSigma kind φ w)⟫ - newt W0 W1 W2 W3 ⟪n, Bseg fils (faceSigma kind φ W0)⟫
        ⟪n, Bseg fils (faceSigma kind φ W1)⟫ ⟪n, Bseg fils (faceSigma kind φ W2)⟫
        ⟪n, Bseg fils (faceSigma kind φ W3)⟫ w| ≤
      ((R.map fun z => remTW (Nat.mul D D) Q (srTriple o z)).sum : ℝ) / ((two40 : ℕ) : ℝ) *
        |omega4 W0 W1 W2 W3 w| / 24 := by
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have eB : ∀ v, Bseg fils v = BL (R.map seg3) v := by intro v; rw [hR]; rfl
  simp only [eB]
  have hL : ∀ z ∈ R, 0 < cellL Q.rcW (d2Low z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)) := by
    intro z hz
    have := (hrec z hz).2.2.2
    simp only [remChk, srTriple, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.1
  have hdd : ∀ z ∈ R, 0 < ddW D Q o z := fun z hz => by
    unfold ddW; exact div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hL z hz)) hlam
  have hsep : ∀ z ∈ R, ∀ τ ∈ Icc W0 W3, ∀ s ∈ Icc (0 : ℝ) 1,
      ddW D Q o z ≤ ‖faceSigma kind φ τ - seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s‖ := by
    intro z hz τ hτ s hs
    obtain ⟨hva, hvb, hsg, -⟩ := hrec z hz
    exact dd_le hD hva hvb hsg Q.rcW hrs hs0 (hL z hz) (hreach τ hτ) hs
  have h := BL_cubic n hn seg3 (ddW D Q o) (fun z => 120 / (ddW D Q o z) ^ 6)
    (σ := fun v => faceSigma kind φ v) (σ1 := fun _ => faceW kind φ) (σ2 := fun _ => 0)
    (σ3 := fun _ => 0) (σ4 := fun _ => 0) h01 h12 h23 hw
    (fun τ _ => hasDerivAt_face_w kind φ τ) (fun τ _ => hasDerivAt_const τ _)
    (fun τ _ => hasDerivAt_const τ _) (fun τ _ => hasDerivAt_const τ _) R hdd
    (fun z hz => by have := hdd z hz; positivity) hsep ?_
  · refine h.trans ?_
    have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
    have hsum : (R.map fun z => kvR (seg3 z) * (120 / (ddW D Q o z) ^ 6)).sum ≤
        ((R.map fun z => remTW (Nat.mul D D) Q (srTriple o z)).sum : ℝ) / ((two40 : ℕ) : ℝ) := by
      rw [le_div_iff₀ h40, ← List.sum_map_mul_right, Nat.cast_list_sum, List.map_map]
      apply List.sum_le_sum
      intro z hz
      obtain ⟨-, -, hsg, -⟩ := hrec z hz
      have hk := kv_ge hsg
      have := termW_ge (hL z hz) hlam hk hw6
      simp only [Function.comp_apply, remTW, srTriple]
      unfold ddW seg3
      rw [mul_comm]
      exact this
    have hω := abs_nonneg (omega4 W0 W1 W2 W3 w)
    gcongr
  · intro z hz τ hτ s hs
    have hu := hsep z hz τ hτ s hs
    have hd := hdd z hz
    have hb := abs_kgD4_line (cross n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1))
      (faceSigma kind φ τ - seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s) (faceW kind φ)
      (norm_pos_iff.mp (lt_of_lt_of_le hd hu))
    rw [norm_faceW, one_pow, mul_one] at hb
    refine hb.trans ?_
    have hm := norm_cross_le n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1)
    have h6 : 120 / ‖faceSigma kind φ τ - seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s‖ ^ 6 ≤
        120 / (ddW D Q o z) ^ 6 := div_pow_anti (by norm_num) hd hu 6
    calc ‖cross n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1)‖ *
          (120 / ‖faceSigma kind φ τ - seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s‖ ^ 6)
        ≤ (‖n‖ * ‖ptR (seg3 z).2.2 - ptR (seg3 z).2.1‖) * (120 / (ddW D Q o z) ^ 6) :=
          mul_le_mul hm h6 (by positivity) (by positivity)
      _ = _ := by ring

/-- Monotonicity of the kernel constants in `ρ`, `T`, `t`. -/
theorem kc_mono {ρ ρm Tm tm : ℝ} (hρ : 0 ≤ ρ) (hρm : ρ ≤ ρm) (ht : 0 ≤ tm) :
    kc6 ρ Tm tm ≤ kc6 ρm Tm tm ∧ kc4 ρ Tm tm ≤ kc4 ρm Tm tm ∧ kc2 ρ ≤ kc2 ρm := by
  have p3 : ρ ^ 3 ≤ ρm ^ 3 := pow_le_pow_left₀ hρ hρm 3
  have p4 : ρ ^ 4 ≤ ρm ^ 4 := pow_le_pow_left₀ hρ hρm 4
  have p2 : ρ ^ 2 ≤ ρm ^ 2 := pow_le_pow_left₀ hρ hρm 2
  have hT4 : 0 ≤ Tm ^ 4 := by positivity
  have h5 : kc5 ρ Tm tm ≤ kc5 ρm Tm tm := by
    unfold kc5
    have : 0 ≤ 2304 * tm + 2309 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p3 this) hT4
  refine ⟨?_, ?_, ?_⟩
  · unfold kc6; nlinarith
  · unfold kc4; nlinarith
  · unfold kc2; linarith

/-- **The `t`-strip remainder of the coil field from the corner records.** -/
theorem tline_coil (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ))) {Xt Yt Zt D : ℕ} (hD : 0 < D)
    (n : Space) (hn : ‖n‖ ≤ 1) (R : List SRec) (hR : R.map seg3 = allSegs fils) (Q : RemP)
    (hrec : ∀ z ∈ R, VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
      segOK o z.1 z.2.1 z.2.2.1 = true ∧ remChk (Nat.mul D D) Q (srTriple o z) = true)
    (hrs : Q.rcT.rBD ≤ Q.rcT.s0l) (hs0 : 0 < Q.rcT.s0l) {ρ ρm ζ Tm tm : ℝ} (hρ : 0 < ρ)
    (hρm : ρ ≤ ρm) (hTm1 : Tm ≤ 1) (htm : 0 ≤ tm)
    (h6 : kc6 ρm Tm tm * ((D : ℝ) * S32) ^ 6 ≤ Q.t6)
    (h4 : kc4 ρm Tm tm * ((D : ℝ) * S32) ^ 4 ≤ Q.t4) (h2 : kc2 ρm * ((D : ℝ) * S32) ^ 2 ≤ Q.t2)
    {T0 T1 T2 T3 t : ℝ} (h01 : T0 < T1) (h12 : T1 < T2) (h23 : T2 < T3) (ht : t ∈ Icc T1 T2)
    (hT : ∀ τ ∈ Icc T0 T3, 1 / (1 + τ ^ 2) ≤ Tm ∧ |τ| ≤ tm)
    (hreach : ∀ τ ∈ Icc T0 T3, (D : ℝ) * S32 * ‖circ ρ ζ τ - cornerR Xt Yt Zt D‖ ≤ Q.rcT.rBD) :
    |⟪n, Bseg fils (circ ρ ζ t)⟫ - newt T0 T1 T2 T3 ⟪n, Bseg fils (circ ρ ζ T0)⟫
        ⟪n, Bseg fils (circ ρ ζ T1)⟫ ⟪n, Bseg fils (circ ρ ζ T2)⟫ ⟪n, Bseg fils (circ ρ ζ T3)⟫ t| ≤
      ((R.map fun z => remTT (Nat.mul D D) Q (srTriple o z)).sum : ℝ) / ((two40 : ℕ) : ℝ) *
        |omega4 T0 T1 T2 T3 t| / 24 := by
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have eB : ∀ v, Bseg fils v = BL (R.map seg3) v := by intro v; rw [hR]; rfl
  simp only [eB]
  obtain ⟨m6, m4, m2⟩ := kc_mono (Tm := Tm) hρ.le hρm htm
  have hL : ∀ z ∈ R, 0 < cellL Q.rcT (d2Low z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)) := by
    intro z hz
    have := (hrec z hz).2.2.2
    simp only [remChk, srTriple, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.2
  have hdd : ∀ z ∈ R, 0 < ddT D Q o z := fun z hz => by
    unfold ddT; exact div_pos (Real.sqrt_pos.mpr (by exact_mod_cast hL z hz)) hlam
  have hsep : ∀ z ∈ R, ∀ τ ∈ Icc T0 T3, ∀ s ∈ Icc (0 : ℝ) 1,
      ddT D Q o z ≤ ‖circ ρ ζ τ - seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s‖ := by
    intro z hz τ hτ s hs
    obtain ⟨hva, hvb, hsg, -⟩ := hrec z hz
    exact dd_le hD hva hvb hsg Q.rcT hrs hs0 (hL z hz) (hreach τ hτ) hs
  set Kf : SRec → ℝ := fun z => kc6 ρm Tm tm / (ddT D Q o z) ^ 6 +
    kc4 ρm Tm tm / (ddT D Q o z) ^ 4 + kc2 ρm / (ddT D Q o z) ^ 2
  have k6 : 0 ≤ kc6 ρm Tm tm := by unfold kc6 kc5; have := hρ.le.trans hρm; positivity
  have k4 : 0 ≤ kc4 ρm Tm tm := by unfold kc4 kc5; have := hρ.le.trans hρm; positivity
  have k2 : 0 ≤ kc2 ρm := by unfold kc2; linarith
  have h := BL_cubic n hn seg3 (ddT D Q o) Kf
    (σ := circ ρ ζ) (σ1 := U1 ρ) (σ2 := U2 ρ) (σ3 := U3 ρ) (σ4 := U4 ρ) h01 h12 h23 ht
    (fun τ _ => hasDerivAt_circ ρ ζ τ) (fun τ _ => hasDerivAt_U1 ρ τ)
    (fun τ _ => hasDerivAt_U2 ρ τ) (fun τ _ => hasDerivAt_U3 ρ τ) R hdd
    (fun z hz => by
      have := hdd z hz
      exact add_nonneg (add_nonneg (div_nonneg k6 (by positivity)) (div_nonneg k4 (by positivity)))
        (div_nonneg k2 (by positivity))) hsep ?_
  · refine h.trans ?_
    have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
    have hsum : (R.map fun z => kvR (seg3 z) * Kf z).sum ≤
        ((R.map fun z => remTT (Nat.mul D D) Q (srTriple o z)).sum : ℝ) / ((two40 : ℕ) : ℝ) := by
      rw [le_div_iff₀ h40, ← List.sum_map_mul_right, Nat.cast_list_sum, List.map_map]
      apply List.sum_le_sum
      intro z hz
      obtain ⟨-, -, hsg, -⟩ := hrec z hz
      have hk := kv_ge hsg
      have := term_ge (hL z hz) hlam hk k6 k4 k2 h6 h4 h2
      simp only [Function.comp_apply, remTT, srTriple]
      simp only [Kf]
      unfold ddT seg3
      rw [mul_comm]
      exact this
    have hω := abs_nonneg (omega4 T0 T1 T2 T3 t)
    gcongr
  · intro z hz τ hτ s hs
    have hu := hsep z hz τ hτ s hs
    have hd := hdd z hz
    have hb := kt_bound (cross n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1))
      (seg (ptR (seg3 z).2.1) (ptR (seg3 z).2.2) s) hρ hd hu (hT τ hτ).1 hTm1 (hT τ hτ).2
    refine hb.trans ?_
    have hm := norm_cross_le n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1)
    have hd6 : 0 < (ddT D Q o z) ^ 6 := by positivity
    have hd4 : 0 < (ddT D Q o z) ^ 4 := by positivity
    have hd2 : 0 < (ddT D Q o z) ^ 2 := by positivity
    have hK : kc6 ρ Tm tm / ddT D Q o z ^ 6 + kc4 ρ Tm tm / ddT D Q o z ^ 4 +
        kc2 ρ / ddT D Q o z ^ 2 ≤ Kf z := by
      simp only [Kf]
      gcongr
    have hK0 : 0 ≤ kc6 ρ Tm tm / ddT D Q o z ^ 6 + kc4 ρ Tm tm / ddT D Q o z ^ 4 +
        kc2 ρ / ddT D Q o z ^ 2 := by
      have : 0 ≤ kc6 ρ Tm tm := by unfold kc6 kc5; positivity
      have : 0 ≤ kc4 ρ Tm tm := by unfold kc4 kc5; positivity
      have : 0 ≤ kc2 ρ := by unfold kc2; linarith
      positivity
    calc ‖cross n (ptR (seg3 z).2.2 - ptR (seg3 z).2.1)‖ *
          (kc6 ρ Tm tm / ddT D Q o z ^ 6 + kc4 ρ Tm tm / ddT D Q o z ^ 4 + kc2 ρ / ddT D Q o z ^ 2)
        ≤ (‖n‖ * ‖ptR (seg3 z).2.2 - ptR (seg3 z).2.1‖) * Kf z :=
          mul_le_mul hm hK hK0 (by positivity)
      _ = _ := by ring

/-! ## The remainder parameters -/

theorem cdiv_ge' (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := cdiv_ge a hb

/-- The radius numerator `ρn/ρd` of `remP4`. -/
@[expose] def rhoN (F : Face4) (wn1 : ℤ) : ℕ := if F.kind < 2 then (cylR F.kind).toNat else iabs wn1
/-- The radius denominator of `remP4`. -/
@[expose] def rhoD (F : Face4) : ℕ := if F.kind < 2 then 181 else F.wd

/-- The radius denominator is positive. -/
theorem rhoD_pos (F : Face4) (hwd : 0 < F.wd) : 0 < rhoD F := by
  unfold rhoD; split_ifs <;> omega

/-- The minimal `|m|` on `[mp, mn2]` used by `remP4`. -/
@[expose] def mminP (mp mn2 : ℤ) : ℕ := if mp ≤ 0 ∧ 0 ≤ mn2 then 0 else nmin2 (iabs mp) (iabs mn2)
/-- The maximal `|m|` on `[mp, mn2]`. -/
@[expose] def mmaxP (mp mn2 : ℤ) : ℕ := nmax (iabs mp) (iabs mn2)

/-- The kernel parameters `T_max = q²/(q² + m_min²)`, `t_max = m_max/q`. -/
@[expose] def TmP (mp mn2 : ℤ) : ℝ := (4096 : ℝ) ^ 2 / (4096 ^ 2 + (mminP mp mn2 : ℝ) ^ 2)
/-- `t_max = m_max/q`. -/
@[expose] def tmP (mp mn2 : ℤ) : ℝ := (mmaxP mp mn2 : ℝ) / 4096

/-- The factor `T = q²/(q² + m_min²)` is at most `1`. -/
theorem TmP_le_one (mp mn2 : ℤ) : TmP mp mn2 ≤ 1 := by
  unfold TmP; rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (mminP mp mn2 : ℝ)]

/-- For `τ ∈ [mp/q, mn2/q]`: `1/(1 + τ²) ≤ T_max` and `|τ| ≤ t_max`. -/
theorem Tm_bounds {mp mn2 : ℤ} (hm : mp ≤ mn2) {τ : ℝ}
    (hτ : τ ∈ Icc ((mp : ℝ) / 4096) ((mn2 : ℝ) / 4096)) :
    1 / (1 + τ ^ 2) ≤ TmP mp mn2 ∧ |τ| ≤ tmP mp mn2 := by
  obtain ⟨h1, h2⟩ := hτ
  have hq : (0 : ℝ) < 4096 := by norm_num
  constructor
  · unfold TmP
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- `m_min² ≤ (4096 τ)²`
    have key : (mminP mp mn2 : ℝ) ^ 2 ≤ (4096 * τ) ^ 2 := by
      unfold mminP
      split_ifs with hc
      · simpa using sq_nonneg (4096 * τ)
      · have hmin : ((nmin2 (iabs mp) (iabs mn2) : ℕ) : ℝ) ≤ |4096 * τ| := by
          unfold nmin2
          rcases not_and_or.mp hc with h | h
          · push Not at h
            have hmp : (0 : ℝ) < mp := by exact_mod_cast h
            have : 4096 * τ ≥ mp := by rw [div_le_iff₀ hq] at h1; linarith
            have hpos : 0 ≤ 4096 * τ := by linarith
            rw [abs_of_nonneg hpos]
            cases hb : Nat.ble (iabs mp) (iabs mn2)
            · simp only [Bool.cond_false, iabs_cast]
              have : |(mn2 : ℝ)| = mn2 := abs_of_nonneg (by
                have : (mp : ℝ) ≤ mn2 := by exact_mod_cast hm
                linarith)
              rw [this]
              have hnle : ¬ (iabs mp ≤ iabs mn2) := fun h => by
                rw [Nat.ble_eq_true_of_le h] at hb; cases hb
              have := Nat.lt_of_not_le hnle
              have h' : (iabs mn2 : ℝ) < iabs mp := by exact_mod_cast this
              rw [iabs_cast, iabs_cast, abs_of_pos hmp] at h'
              linarith [abs_le.mp (le_refl |(mn2 : ℝ)|)]
            · simp only [Bool.cond_true, iabs_cast, abs_of_pos hmp]; linarith
          · push Not at h
            have hmn : (mn2 : ℝ) < 0 := by exact_mod_cast h
            have : 4096 * τ ≤ mn2 := by rw [le_div_iff₀ hq] at h2; linarith
            have hneg : 4096 * τ ≤ 0 := by linarith
            rw [abs_of_nonpos hneg]
            cases hb : Nat.ble (iabs mp) (iabs mn2)
            · simp only [Bool.cond_false, iabs_cast, abs_of_neg hmn]; linarith
            · simp only [Bool.cond_true, iabs_cast]
              have hle := Nat.le_of_ble_eq_true hb
              have h' : (iabs mp : ℝ) ≤ iabs mn2 := by exact_mod_cast hle
              rw [iabs_cast, iabs_cast, abs_of_neg hmn] at h'
              linarith
        have h0 : (0 : ℝ) ≤ (nmin2 (iabs mp) (iabs mn2) : ℕ) := Nat.cast_nonneg _
        calc ((nmin2 (iabs mp) (iabs mn2) : ℕ) : ℝ) ^ 2 ≤ |4096 * τ| ^ 2 :=
              pow_le_pow_left₀ h0 hmin 2
          _ = (4096 * τ) ^ 2 := sq_abs _
    nlinarith
  · unfold tmP mmaxP
    rw [nmax_cast, iabs_cast, iabs_cast, le_div_iff₀ hq]
    rw [div_le_iff₀ hq] at h1
    rw [le_div_iff₀ hq] at h2
    rcases le_total 0 τ with h | h
    · rw [abs_of_nonneg h]
      have : τ * 4096 ≤ |(mn2 : ℝ)| := by linarith [le_abs_self (mn2 : ℝ)]
      linarith [le_max_right |(mp : ℝ)| |(mn2 : ℝ)|]
    · rw [abs_of_nonpos h]
      have : -τ * 4096 ≤ |(mp : ℝ)| := by linarith [neg_abs_le (mp : ℝ)]
      linarith [le_max_left |(mp : ℝ)| |(mn2 : ℝ)|]

/-- **Real meaning of the remainder parameters.** -/
theorem remP4_spec (F : Face4) (hwd : 0 < F.wd) (mp m mn2 wp wn wn1 wn2 : ℤ) (D : ℕ) (hD : 0 < D)
    (hρ : 0 < rhoN F wn1) :
    let Q := remP4 F mp m mn2 wp wn wn1 wn2 D
    let lam := (D : ℝ) * S32
    let ρ := (rhoN F wn1 : ℝ) / rhoD F
    0 < Q.rcW.s0l ∧ 0 < Q.rcT.s0l ∧
    lam * (max |(wn : ℝ) - wp| |(wn2 : ℝ) - wn| / F.wd) ≤ Q.rcW.rBD ∧
    lam ^ 2 * (4 * ρ ^ 2 * (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 +
      (|(wn1 : ℝ) - wn| / F.wd) ^ 2) ≤ Q.nt ∧
    120 * lam ^ 6 ≤ Q.w6 ∧ (Q.lam2 : ℝ) = lam ^ 2 ∧
    kc6 ρ (TmP mp mn2) (tmP mp mn2) * lam ^ 6 ≤ Q.t6 ∧
    kc4 ρ (TmP mp mn2) (tmP mp mn2) * lam ^ 4 ≤ Q.t4 ∧ kc2 ρ * lam ^ 2 ≤ Q.t2 := by
  intro Q lam ρ
  have hlamN : ((Nat.mul D two32 : ℕ) : ℝ) = lam := by push_cast [Nat.mul_eq, two32_cast]; rfl
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hρd := rhoD_pos F hwd
  have hρd' : (0 : ℝ) < rhoD F := by exact_mod_cast hρd
  have hq : (0 : ℝ) < 4096 := by norm_num
  have hlam : 0 < lam := mul_pos (by exact_mod_cast hD) S32_pos
  set q : ℕ := qT
  have hqR : (q : ℝ) = 4096 := by simp [q, qT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < Nat.mul D two30; exact Nat.mul_pos hD (by norm_num [two30])
  · change 0 < Nat.mul D two30; exact Nat.mul_pos hD (by norm_num [two30])
  · change lam * (max |(wn : ℝ) - wp| |(wn2 : ℝ) - wn| / F.wd) ≤
      (cdiv (Nat.mul (Nat.mul D two32) (nmax (iabs (wn - wp)) (iabs (wn2 - wn)))) F.wd : ℝ)
    refine le_trans ?_ (cdiv_ge _ hwd)
    push_cast [Nat.mul_eq]
    rw [two32_cast, nmax_cast, iabs_cast, iabs_cast]
    push_cast; rw [mul_div_assoc]
  · change lam ^ 2 * (4 * ρ ^ 2 * (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 +
      (|(wn1 : ℝ) - wn| / F.wd) ^ 2) ≤
      (cdiv (Nat.mul (sq (Nat.mul D two32)) (Nat.add (Nat.mul 4 (Nat.mul (sq (rhoN F wn1))
        (Nat.mul (sq (nmax (iabs (m - mp)) (iabs (mn2 - m)))) (sq F.wd))))
        (Nat.mul (sq (iabs (wn1 - wn))) (Nat.mul (sq (rhoD F)) (sq q)))))
        (Nat.mul (sq (rhoD F)) (Nat.mul (sq q) (sq F.wd))) : ℝ)
    refine le_trans ?_ (cdiv_ge _ (Nat.mul_pos (Nat.mul_pos hρd hρd)
      (Nat.mul_pos (by simp only [q, qT, sq]; norm_num) (Nat.mul_pos hwd hwd))))
    push_cast [Nat.mul_eq, Nat.add_eq, sq_cast]
    rw [two32_cast, nmax_cast, iabs_cast, iabs_cast, iabs_cast, hqR]
    simp only [ρ, lam]
    push_cast
    rw [le_div_iff₀ (by positivity)]
    field_simp
    ring_nf
    exact le_rfl
  · change 120 * lam ^ 6 ≤
      ((Nat.mul 120 (Nat.mul (sq (sq (Nat.mul D two32))) (sq (Nat.mul D two32))) : ℕ) : ℝ)
    push_cast [Nat.mul_eq, sq_cast]; rw [two32_cast]; simp only [lam]; ring_nf; exact le_rfl
  · change ((sq (Nat.mul D two32) : ℕ) : ℝ) = lam ^ 2
    rw [sq_cast, hlamN]
  · have e1 : (if F.kind < 2 then (cylR F.kind).toNat else iabs wn1) = rhoN F wn1 := rfl
    have e2 : (if F.kind < 2 then 181 else F.wd) = rhoD F := rfl
    have e3 : (if mp ≤ 0 ∧ 0 ≤ mn2 then 0 else nmin2 (iabs mp) (iabs mn2)) = mminP mp mn2 := rfl
    have e4 : nmax (iabs mp) (iabs mn2) = mmaxP mp mn2 := rfl
    simp only [Q, remP4, e1, e2, e3, e4]
    refine le_trans ?_ (cdiv_ge _ ?_)
    · push_cast [Nat.mul_eq, Nat.add_eq, sq_cast, two32_cast]
      simp only [ρ, lam, kc6, kc5, TmP, tmP, qT]
      generalize (rhoN F wn1 : ℝ) = rn at *
      generalize (rhoD F : ℝ) = rd at *
      generalize (mminP mp mn2 : ℝ) = a
      generalize (mmaxP mp mn2 : ℝ) = b
      apply le_of_eq
      have h1 : (0 : ℝ) < 4096 ^ 2 + a ^ 2 := by positivity
      push_cast
      field_simp
      ring
    · have p4 : 0 < sq (sq (rhoD F)) := by
        simp only [sq]; exact Nat.mul_pos (Nat.mul_pos hρd hρd) (Nat.mul_pos hρd hρd)
      have pT0 : 0 < Nat.add (sq qT) (sq (mminP mp mn2)) :=
        Nat.lt_of_lt_of_le (by norm_num [sq, qT]) (Nat.le_add_right _ _)
      have pT : 0 < sq (sq (Nat.add (sq qT) (sq (mminP mp mn2)))) := by
        simp only [sq]; exact Nat.mul_pos (Nat.mul_pos pT0 pT0) (Nat.mul_pos pT0 pT0)
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos pT (Nat.mul_pos p4 (by norm_num [qT])))
  · have e1 : (if F.kind < 2 then (cylR F.kind).toNat else iabs wn1) = rhoN F wn1 := rfl
    have e2 : (if F.kind < 2 then 181 else F.wd) = rhoD F := rfl
    have e3 : (if mp ≤ 0 ∧ 0 ≤ mn2 then 0 else nmin2 (iabs mp) (iabs mn2)) = mminP mp mn2 := rfl
    have e4 : nmax (iabs mp) (iabs mn2) = mmaxP mp mn2 := rfl
    simp only [Q, remP4, e1, e2, e3, e4]
    refine le_trans ?_ (cdiv_ge _ ?_)
    · push_cast [Nat.mul_eq, Nat.add_eq, sq_cast, two32_cast]
      simp only [ρ, lam, kc4, kc5, TmP, tmP, qT]
      generalize (rhoN F wn1 : ℝ) = rn at *
      generalize (rhoD F : ℝ) = rd at *
      generalize (mminP mp mn2 : ℝ) = a
      generalize (mmaxP mp mn2 : ℝ) = b
      apply le_of_eq
      have h1 : (0 : ℝ) < 4096 ^ 2 + a ^ 2 := by positivity
      push_cast
      field_simp
      ring
    · have p2 : 0 < sq (rhoD F) := by simp only [sq]; exact Nat.mul_pos hρd hρd
      have pT0 : 0 < Nat.add (sq qT) (sq (mminP mp mn2)) :=
        Nat.lt_of_lt_of_le (by norm_num [sq, qT]) (Nat.le_add_right _ _)
      have pT : 0 < sq (sq (Nat.add (sq qT) (sq (mminP mp mn2)))) := by
        simp only [sq]; exact Nat.mul_pos (Nat.mul_pos pT0 pT0) (Nat.mul_pos pT0 pT0)
      exact Nat.mul_pos (by norm_num) (Nat.mul_pos pT (Nat.mul_pos (by norm_num [qT])
        (Nat.mul_pos p2 hρd)))
  · have e1 : (if F.kind < 2 then (cylR F.kind).toNat else iabs wn1) = rhoN F wn1 := rfl
    have e2 : (if F.kind < 2 then 181 else F.wd) = rhoD F := rfl
    simp only [Q, remP4, e1, e2]
    refine le_trans ?_ (cdiv_ge _ hρd)
    push_cast [Nat.mul_eq, sq_cast, two32_cast]
    simp only [ρ, lam, kc2]
    apply le_of_eq
    field_simp

/-! ## The remainder contributions -/

/-- `rwC` dominates `(R_w/2⁴⁰ + 1000)|ω|/24` for `|ω| ≤ (w₂ - w₁)²(w₂ - w₀)(w₃ - w₁)/4`. -/
theorem rwC_ge (F : Face4) (hF : Face4OK F) {w0 w1 w2 w3 : ℤ} (h01 : w0 < w1) (h12 : w1 < w2)
    (h23 : w2 < w3) (rw : ℕ) {ω : ℝ}
    (hω : |ω| ≤ ((w2 : ℝ) / F.wd - w1 / F.wd) ^ 2 * ((w2 : ℝ) / F.wd - w0 / F.wd) *
      ((w3 : ℝ) / F.wd - w1 / F.wd) / 4) :
    ((rw : ℝ) / ((two40 : ℕ) : ℝ) + 1000) * |ω| / 24 ≤
      (rwC F w0 w1 w2 w3 rw : ℝ) / ((two40 : ℕ) : ℝ) := by
  obtain ⟨-, hwd, -, hhwd, -, hhw⟩ := hF
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hden : 0 < Nat.mul 96 (sq (sq F.wd)) := by
    apply Nat.mul_pos (by norm_num); simp only [sq]
    exact Nat.mul_pos (Nat.mul_pos hwd hwd) (Nat.mul_pos hwd hwd)
  have hc := cdiv_ge (Nat.mul F.hwn two40) hhwd
  unfold rwC
  rw [le_div_iff₀ h40]
  refine le_trans ?_ (cdiv_ge _ hden)
  push_cast [Nat.mul_eq, Nat.add_eq, sq_cast, iabs_cast] at hc ⊢
  have hd1 : (0 : ℝ) < (w1 : ℝ) - w0 := by have : (w0 : ℝ) < w1 := by exact_mod_cast h01
                                           linarith
  have hd2 : (0 : ℝ) < (w2 : ℝ) - w1 := by have : (w1 : ℝ) < w2 := by exact_mod_cast h12
                                           linarith
  have hd3 : (0 : ℝ) < (w3 : ℝ) - w2 := by have : (w2 : ℝ) < w3 := by exact_mod_cast h23
                                           linarith
  rw [abs_of_pos hd2, abs_of_pos (by linarith : (0 : ℝ) < (w2 : ℝ) - w0),
    abs_of_pos (by linarith : (0 : ℝ) < (w3 : ℝ) - w1)]
  have hhw' : 1000 * ((two40 : ℕ) : ℝ) ≤ (F.hwn : ℝ) * ((two40 : ℕ) : ℝ) / F.hwd := by
    have hhwd' : (0 : ℝ) < F.hwd := by exact_mod_cast hhwd
    rw [le_div_iff₀ hhwd']; rw [le_div_iff₀ hhwd'] at hhw; nlinarith
  have eω : ((w2 : ℝ) / F.wd - w1 / F.wd) ^ 2 * ((w2 : ℝ) / F.wd - w0 / F.wd) *
      ((w3 : ℝ) / F.wd - w1 / F.wd) / 4 =
      ((w2 : ℝ) - w1) ^ 2 * ((w2 : ℝ) - w0) * ((w3 : ℝ) - w1) / (4 * (F.wd : ℝ) ^ 4) := by
    field_simp
  rw [eω] at hω
  have hω0 := abs_nonneg ω
  have hΩ : 0 ≤ ((w2 : ℝ) - w1) ^ 2 * (((w2 : ℝ) - w0) * ((w3 : ℝ) - w1)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  calc ((rw : ℝ) / ((two40 : ℕ) : ℝ) + 1000) * |ω| / 24 * ((two40 : ℕ) : ℝ)
      ≤ ((rw : ℝ) / ((two40 : ℕ) : ℝ) + 1000) * (((w2 : ℝ) - w1) ^ 2 * ((w2 : ℝ) - w0) *
          ((w3 : ℝ) - w1) / (4 * (F.wd : ℝ) ^ 4)) / 24 * ((two40 : ℕ) : ℝ) := by gcongr
    _ = ((rw : ℝ) + 1000 * ((two40 : ℕ) : ℝ)) * (((w2 : ℝ) - w1) ^ 2 * (((w2 : ℝ) - w0) *
          ((w3 : ℝ) - w1))) / (96 * (F.wd : ℝ) ^ 4) := by field_simp; ring
    _ ≤ ((rw : ℝ) + (F.hwn : ℝ) * ((two40 : ℕ) : ℝ) / F.hwd) * (((w2 : ℝ) - w1) ^ 2 *
          (((w2 : ℝ) - w0) * ((w3 : ℝ) - w1))) / (96 * (F.wd : ℝ) ^ 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΩ
        linarith
    _ ≤ ((rw : ℝ) + (cdiv (F.hwn * two40) F.hwd : ℝ)) * (((w2 : ℝ) - w1) ^ 2 *
          (((w2 : ℝ) - w0) * ((w3 : ℝ) - w1))) / (96 * (F.wd : ℝ) ^ 4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΩ
        have := hc
        linarith
    _ = _ := by ring

/-- `rtC` dominates `(R_t/2⁴⁰ + 2000)|ω|/24` for `|ω| ≤ (t₂ - t₁)²(t₂ - t₀)(t₃ - t₁)/4`,
`t = m/4096`. -/
theorem rtC_ge (F : Face4) (hF : Face4OK F) {m0 m1 m2 m3 : ℤ} (h01 : m0 < m1) (h12 : m1 < m2)
    (h23 : m2 < m3) (rt : ℕ) {ω : ℝ}
    (hω : |ω| ≤ ((m2 : ℝ) / 4096 - m1 / 4096) ^ 2 * ((m2 : ℝ) / 4096 - m0 / 4096) *
      ((m3 : ℝ) / 4096 - m1 / 4096) / 4) :
    ((rt : ℝ) / ((two40 : ℕ) : ℝ) + 2000) * |ω| / 24 ≤
      (rtC F m0 m1 m2 m3 rt : ℝ) / ((two40 : ℕ) : ℝ) := by
  obtain ⟨-, -, hhtd, -, hht, -⟩ := hF
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hden : 0 < Nat.mul 96 (sq (sq qT)) := by norm_num [sq, qT]
  have hc := cdiv_ge (Nat.mul F.htn two40) hhtd
  unfold rtC
  rw [le_div_iff₀ h40]
  refine le_trans ?_ (cdiv_ge _ hden)
  push_cast [Nat.mul_eq, Nat.add_eq, sq_cast, iabs_cast] at hc ⊢
  have hd2 : (0 : ℝ) < (m2 : ℝ) - m1 := by have : (m1 : ℝ) < m2 := by exact_mod_cast h12
                                           linarith
  have hd1 : (0 : ℝ) < (m1 : ℝ) - m0 := by have : (m0 : ℝ) < m1 := by exact_mod_cast h01
                                           linarith
  have hd3 : (0 : ℝ) < (m3 : ℝ) - m2 := by have : (m2 : ℝ) < m3 := by exact_mod_cast h23
                                           linarith
  rw [abs_of_pos hd2, abs_of_pos (by linarith : (0 : ℝ) < (m2 : ℝ) - m0),
    abs_of_pos (by linarith : (0 : ℝ) < (m3 : ℝ) - m1)]
  have hht' : 2000 * ((two40 : ℕ) : ℝ) ≤ (F.htn : ℝ) * ((two40 : ℕ) : ℝ) / F.htd := by
    have hhtd' : (0 : ℝ) < F.htd := by exact_mod_cast hhtd
    rw [le_div_iff₀ hhtd']; rw [le_div_iff₀ hhtd'] at hht; nlinarith
  have eω : ((m2 : ℝ) / 4096 - m1 / 4096) ^ 2 * ((m2 : ℝ) / 4096 - m0 / 4096) *
      ((m3 : ℝ) / 4096 - m1 / 4096) / 4 =
      ((m2 : ℝ) - m1) ^ 2 * ((m2 : ℝ) - m0) * ((m3 : ℝ) - m1) / (4 * (4096 : ℝ) ^ 4) := by
    field_simp
  rw [eω] at hω
  have hω0 := abs_nonneg ω
  have hΩ : 0 ≤ ((m2 : ℝ) - m1) ^ 2 * (((m2 : ℝ) - m0) * ((m3 : ℝ) - m1)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  simp only [qT]
  push_cast
  calc ((rt : ℝ) / ((two40 : ℕ) : ℝ) + 2000) * |ω| / 24 * ((two40 : ℕ) : ℝ)
      ≤ ((rt : ℝ) / ((two40 : ℕ) : ℝ) + 2000) * (((m2 : ℝ) - m1) ^ 2 * ((m2 : ℝ) - m0) *
          ((m3 : ℝ) - m1) / (4 * (4096 : ℝ) ^ 4)) / 24 * ((two40 : ℕ) : ℝ) := by gcongr
    _ = ((rt : ℝ) + 2000 * ((two40 : ℕ) : ℝ)) * (((m2 : ℝ) - m1) ^ 2 * (((m2 : ℝ) - m0) *
          ((m3 : ℝ) - m1))) / (96 * (4096 * 4096 * (4096 * 4096))) := by field_simp; ring
    _ ≤ ((rt : ℝ) + (F.htn : ℝ) * ((two40 : ℕ) : ℝ) / F.htd) * (((m2 : ℝ) - m1) ^ 2 *
          (((m2 : ℝ) - m0) * ((m3 : ℝ) - m1))) / (96 * (4096 * 4096 * (4096 * 4096))) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΩ
        linarith
    _ ≤ ((rt : ℝ) + (cdiv (F.htn * two40) F.htd : ℝ)) * (((m2 : ℝ) - m1) ^ 2 *
          (((m2 : ℝ) - m0) * ((m3 : ℝ) - m1))) / (96 * (4096 * 4096 * (4096 * 4096))) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΩ
        have := hc
        linarith
    _ = _ := by ring

/-! ## `hel` on the faces -/

theorem ptF_eq (kind : ℕ) (t w : ℝ) : ptF kind t w = circ (faceRho kind w) (faceZeta kind w) t :=
  faceSigma_phiT kind t w

/-- The `w`-interpolation error of `⟨n, hel⟩` on a face. -/
theorem hel_w_face {n : Space} (hn : ‖n‖ ≤ 1) {kind : ℕ} (t : ℝ) {W0 W1 W2 W3 w : ℝ}
    (h01 : W0 < W1) (h12 : W1 < W2) (h23 : W2 < W3) (hw : w ∈ Icc W1 W2)
    (hk : kind < 2 ∨ 17 / 20 ≤ W0) :
    |⟪n, hel (ptF kind t w)⟫ - newt W0 W1 W2 W3 ⟪n, hel (ptF kind t W0)⟫ ⟪n, hel (ptF kind t W1)⟫
      ⟪n, hel (ptF kind t W2)⟫ ⟪n, hel (ptF kind t W3)⟫ w| ≤ 1000 * |omega4 W0 W1 W2 W3 w| /
          24 := by
  simp only [ptF_eq, faceRho, faceZeta]
  by_cases hc : kind < 2
  · simp only [hc, ite_true]
    have : (0 : ℝ) < (cylR kind : ℝ) / 181 := by unfold cylR; split_ifs <;> norm_num
    exact hel_zeta_interp4 n this t h01 h12 h23 hw
  · simp only [hc, ite_false]
    have hz : |planeZ kind| ≤ 3 / 25 := by rw [planeZ_abs]; norm_num [aF]
    exact hel_rho_interp4 hn hz t h01 h12 h23 (hk.resolve_left hc) hw

/-- The `t`-interpolation error of `⟨n, hel⟩` on a face. -/
theorem hel_t_face {n : Space} (hn : ‖n‖ ≤ 1) {kind : ℕ} {w : ℝ}
    (hρ1 : 17 / 20 ≤ faceRho kind w) (hρ2 : faceRho kind w ≤ 23 / 20)
    (hζ : |faceZeta kind w| ≤ 3 / 25) {T0 T1 T2 T3 t : ℝ}
    (h01 : T0 < T1) (h12 : T1 < T2) (h23 : T2 < T3) (hlo : -1 / 2 ≤ T0) (hhi : T3 ≤ 1 / 2)
    (ht : t ∈ Icc T1 T2) :
    |⟪n, hel (ptF kind t w)⟫ - newt T0 T1 T2 T3 ⟪n, hel (ptF kind T0 w)⟫ ⟪n, hel (ptF kind T1 w)⟫
      ⟪n, hel (ptF kind T2 w)⟫ ⟪n, hel (ptF kind T3 w)⟫ t| ≤ 2000 * |omega4 T0 T1 T2 T3 t| /
          24 := by
  simp only [ptF_eq]
  exact hel_t_interp hn hρ1 hρ2 hζ h01 h12 h23 hlo hhi ht

/-! ## The two remainder bounds of a corner -/

theorem div_lt_div_wd {a b : ℤ} {d : ℕ} (hd : 0 < d) (h : a < b) : (a : ℝ) / d < (b : ℝ) / d := by
  have : (a : ℝ) < b := by exact_mod_cast h
  exact div_lt_div_of_pos_right this (by exact_mod_cast hd)

/-- **The `w`-remainder of a passing corner.** -/
theorem corner_w_bound (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hF : Face4OK F) (mp m mn2 wp wn wn1 wn2 : ℤ)
    (h01 : wp < wn) (h12 : wn < wn1) (h23 : wn1 < wn2)
    (hk : F.kind < 2 ∨ 17 / 20 ≤ (wp : ℝ) / F.wd) (gs : List (List ℕ))
    (hxyz : (cornerXYZ4 F m wn).2 = true)
    (hok : (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 (cornerXYZ4 F m wn).1.2.2.2
      (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m))
      (some (remP4 F mp m mn2 wp wn wn1 wn2 (cornerXYZ4 F m wn).1.2.2.2)) gs).ok = true)
    (n : Space) (hn : ‖n‖ ≤ 1) (w : ℝ) (hw : w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd)) :
    |⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) w)⟫ - newt ((wp : ℝ) / F.wd) ((wn : ℝ) / F.wd)
      ((wn1 : ℝ) / F.wd) ((wn2 : ℝ) / F.wd)
      ⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) ((wp : ℝ) / F.wd))⟫
      ⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn : ℝ) / F.wd))⟫
      ⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn1 : ℝ) / F.wd))⟫
      ⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) ((wn2 : ℝ) / F.wd))⟫ w| ≤
      (rwC F wp wn wn1 wn2 (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2)
        (cornerXYZ4 F m wn).1.1 (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1
        (cornerXYZ4 F m wn).1.2.2.2 (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m))
        (some (remP4 F mp m mn2 wp wn wn1 wn2 (cornerXYZ4 F m wn).1.2.2.2)) gs).rw : ℝ) /
        ((two40 : ℕ) : ℝ) := by
  have hF' := hF
  obtain ⟨hk4, hwd, -, -, -, -⟩ := hF
  set D := (cornerXYZ4 F m wn).1.2.2.2
  set Q := remP4 F mp m mn2 wp wn wn1 wn2 D
  obtain ⟨hc, hD⟩ := cornerR_cornerXYZ4 F hwd m wn hxyz
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hwpos : F.kind < 2 ∨ 0 < wn := by
    rcases hk with h | h
    · exact Or.inl h
    · right
      have : (0 : ℝ) < (wp : ℝ) / F.wd := by linarith
      have : (0 : ℝ) < wp := by
        have := (div_pos_iff_of_pos_right hwd').mp this; exact this
      have : (0 : ℤ) < wp := by exact_mod_cast this
      omega
  obtain ⟨hh0, hhv⟩ := helAt_corner4 F ⟨hk4, hwd⟩ m wn hwpos
  rw [← hc] at hhv
  have hs := cornerEval4_sound o nS fils hfv.1 hfv.2.1 hfv.2.2 _ _ _ D hD _ hh0 hhv _ gs hok
  obtain ⟨R, hR, hrec, hrw, -, hW, -, -⟩ := hs.2 Q rfl
  have hρN : 0 < rhoN F wn1 := by
    unfold rhoN
    split_ifs with h2
    · unfold cylR; split_ifs <;> norm_num
    · have := hwpos.resolve_left h2
      simp only [iabs]; omega
  obtain ⟨hs0W, -, hrBW, -, hw6, -⟩ := remP4_spec F hwd mp m mn2 wp wn wn1 wn2 D hD hρN
  have o01 := div_lt_div_wd hwd h01
  have o12 := div_lt_div_wd hwd h12
  have o23 := div_lt_div_wd hwd h23
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hreach : ∀ v ∈ Icc ((wp : ℝ) / F.wd) ((wn2 : ℝ) / F.wd), (D : ℝ) * S32 *
      ‖faceSigma F.kind (phiT ((m : ℝ) / 4096)) v - cornerR (cornerXYZ4 F m wn).1.1
        (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 D‖ ≤ Q.rcW.rBD := by
    intro v hv
    rw [hc, faceSigma_w_norm]
    refine le_trans ?_ hrBW
    apply mul_le_mul_of_nonneg_left _ hlam.le
    rw [le_div_iff₀ hwd']
    have a1 : |(wn : ℝ) - wp| = (wn : ℝ) - wp := abs_of_pos (by
      have : (wp : ℝ) < wn := by exact_mod_cast h01
      linarith)
    have a2 : |(wn2 : ℝ) - wn| = (wn2 : ℝ) - wn := abs_of_pos (by
      have : (wn : ℝ) < wn2 := by exact_mod_cast (h12.trans h23)
      linarith)
    rw [a1, a2]
    obtain ⟨hv1, hv2⟩ := hv
    rw [div_le_iff₀ hwd'] at hv1
    rw [le_div_iff₀ hwd'] at hv2
    rcases le_total v ((wn : ℝ) / F.wd) with h | h
    · rw [abs_of_nonpos (by linarith)]
      rw [le_div_iff₀ hwd'] at h
      have : (wn : ℝ) / F.wd * F.wd = wn := by field_simp
      nlinarith [le_max_left ((wn : ℝ) - wp) ((wn2 : ℝ) - wn)]
    · rw [abs_of_nonneg (by linarith)]
      rw [div_le_iff₀ hwd'] at h
      have : (wn : ℝ) / F.wd * F.wd = wn := by field_simp
      nlinarith [le_max_right ((wn : ℝ) - wp) ((wn2 : ℝ) - wn)]
  have hcoil := wline_coil o fils hD n hn R hR Q hrec hW hs0W hw6 F.kind (phiT ((m : ℝ) / 4096))
    o01 o12 o23 hw hreach
  have hhel := hel_w_face hn (kind := F.kind) ((m : ℝ) / 4096) o01 o12 o23 hw hk
  rw [← hrw] at hcoil
  simp only [errF, inner_sub_right, newt_sub, ptF]
  simp only [ptF] at hhel
  have hω := abs_omega_le o01.le o23.le hw
  refine le_trans ?_ (rwC_ge F hF' h01 h12 h23 _ hω)
  set A := ⟪n, Bseg fils (faceSigma F.kind (phiT ((m : ℝ) / 4096)) w)⟫ - newt ((wp : ℝ) / F.wd)
    ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd) ((wn2 : ℝ) / F.wd)
    ⟪n, Bseg fils (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wp : ℝ) / F.wd))⟫
    ⟪n, Bseg fils (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn : ℝ) / F.wd))⟫
    ⟪n, Bseg fils (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn1 : ℝ) / F.wd))⟫
    ⟪n, Bseg fils (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn2 : ℝ) / F.wd))⟫ w
  set H := ⟪n, hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) w)⟫ - newt ((wp : ℝ) / F.wd)
    ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd) ((wn2 : ℝ) / F.wd)
    ⟪n, hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wp : ℝ) / F.wd))⟫
    ⟪n, hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn : ℝ) / F.wd))⟫
    ⟪n, hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn1 : ℝ) / F.wd))⟫
    ⟪n, hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn2 : ℝ) / F.wd))⟫ w
  have e : ∀ a b c d : ℝ, a - b - (c - d) = (a - c) - (b - d) := fun a b c d => by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have : |A| + |H| ≤ _ := add_le_add hcoil hhel
  refine this.trans (le_of_eq ?_)
  ring

/-- **Distance from a passing corner's `t`-strip to the coil**: `≥ 1/5`. -/
theorem corner_t_dist (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hF : Face4OK F) (mp m mn mn2 wp wn wn1 wn2 : ℤ)
    (hm01 : mp < m) (hm12 : m < mn) (hm23 : mn < mn2)
    (h01 : wp < wn) (h12 : wn < wn1) (_h23 : wn1 < wn2)
    (hk : F.kind < 2 ∨ 17 / 20 ≤ (wp : ℝ) / F.wd)
    (hcell : ∀ w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd), 17 / 20 ≤ faceRho F.kind w ∧
      faceRho F.kind w ≤ 23 / 20 ∧ |faceZeta F.kind w| ≤ 3 / 25)
    (gs : List (List ℕ))
    (hxyz : (cornerXYZ4 F m wn).2 = true)
    (hok : (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 (cornerXYZ4 F m wn).1.2.2.2
      (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m))
      (some (remP4 F mp m mn2 wp wn wn1 wn2 (cornerXYZ4 F m wn).1.2.2.2)) gs).ok = true)
    (w : ℝ) (hw : w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd))
    (t : ℝ) (ht : t ∈ Icc ((mp : ℝ) / 4096) ((mn2 : ℝ) / 4096)) :
    ∀ z ∈ allSegs fils, ∀ s ∈ Icc (0 : ℝ) 1,
      1 / 5 ≤ ‖ptF F.kind t w - seg (ptR z.2.1) (ptR z.2.2) s‖ := by
  have hF' := hF
  obtain ⟨hk4, hwd, -, -, -, -⟩ := hF
  set D := (cornerXYZ4 F m wn).1.2.2.2
  set Q := remP4 F mp m mn2 wp wn wn1 wn2 D
  obtain ⟨hc, hD⟩ := cornerR_cornerXYZ4 F hwd m wn hxyz
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hwn01 : (wn : ℝ) < wn1 := by exact_mod_cast h12
  have hwpos : F.kind < 2 ∨ 0 < wn := by
    rcases hk with h | h
    · exact Or.inl h
    · right
      have : (0 : ℝ) < (wp : ℝ) / F.wd := by linarith
      have : (0 : ℝ) < wp := (div_pos_iff_of_pos_right hwd').mp this
      have : (0 : ℤ) < wp := by exact_mod_cast this
      omega
  obtain ⟨hh0, hhv⟩ := helAt_corner4 F ⟨hk4, hwd⟩ m wn hwpos
  rw [← hc] at hhv
  have hs := cornerEval4_sound o nS fils hfv.1 hfv.2.1 hfv.2.2 _ _ _ D hD _ hh0 hhv _ gs hok
  obtain ⟨R, hR, hrec, -, -, -, hTs, hN⟩ := hs.2 Q rfl
  have hρN : 0 < rhoN F wn1 := by
    unfold rhoN
    split_ifs with h2
    · unfold cylR; split_ifs <;> norm_num
    · have := hwpos.resolve_left h2
      simp only [iabs]; omega
  obtain ⟨-, hs0T, -, hNt, -, hl2, -, -, -⟩ := remP4_spec F hwd mp m mn2 wp wn wn1 wn2 D hD hρN
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hq : (0 : ℝ) < 4096 := by norm_num
  have o01 : (mp : ℝ) / 4096 < (m : ℝ) / 4096 := by
    have : (mp : ℝ) < m := by exact_mod_cast hm01
    linarith [div_lt_div_of_pos_right this hq]
  have o12 : (m : ℝ) / 4096 < (mn : ℝ) / 4096 := by
    have : (m : ℝ) < mn := by exact_mod_cast hm12
    linarith [div_lt_div_of_pos_right this hq]
  have o23 : (mn : ℝ) / 4096 < (mn2 : ℝ) / 4096 := by
    have : (mn : ℝ) < mn2 := by exact_mod_cast hm23
    linarith [div_lt_div_of_pos_right this hq]
  -- the radii
  set ρm := (rhoN F wn1 : ℝ) / rhoD F
  have hρd' : (0 : ℝ) < rhoD F := by exact_mod_cast rhoD_pos F hwd
  obtain ⟨hρ1, hρ2, hζ⟩ := hcell w hw
  have hW1 : (wn : ℝ) / F.wd ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd) :=
    ⟨le_rfl, (div_lt_div_wd hwd h12).le⟩
  obtain ⟨hρ01, -, -⟩ := hcell _ hW1
  have hρle : ∀ v ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd), faceRho F.kind v ≤ ρm := by
    intro v hv
    simp only [faceRho, ρm, rhoN, rhoD]
    split_ifs with h2
    · push_cast; unfold cylR; split_ifs <;> norm_num
    · have hpos := hwpos.resolve_left h2
      have hw1 : (0 : ℝ) < wn1 := by exact_mod_cast (hpos.trans h12)
      simp only [iabs_cast]
      rw [abs_of_pos hw1]
      exact hv.2
  have hρpos : 0 < faceRho F.kind w := by linarith
  have hρ0pos : 0 < faceRho F.kind ((wn : ℝ) / F.wd) := by linarith
  -- the region
  have hreach : ∀ τ ∈ Icc ((mp : ℝ) / 4096) ((mn2 : ℝ) / 4096), (D : ℝ) * S32 *
      ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ - cornerR (cornerXYZ4 F m wn).1.1
        (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 D‖ ≤ Q.rcT.rBD := by
    intro τ hτ
    rw [hc, faceSigma_phiT]
    have hd := circ_dist_sq hρpos.le hρ0pos.le (faceZeta F.kind w) (faceZeta F.kind ((wn : ℝ) /
        F.wd))
      τ ((m : ℝ) / 4096)
    -- `(ρ - ρ₀)² + (ζ - ζ₀)² = (w - w₁)²`
    have hrz : (faceRho F.kind w - faceRho F.kind ((wn : ℝ) / F.wd)) ^ 2 +
        (faceZeta F.kind w - faceZeta F.kind ((wn : ℝ) / F.wd)) ^ 2 = (w - (wn : ℝ) / F.wd) ^
            2 := by
      simp only [faceRho, faceZeta]; split_ifs <;> ring
    have hdw : (w - (wn : ℝ) / F.wd) ^ 2 ≤ (|(wn1 : ℝ) - wn| / F.wd) ^ 2 := by
      have e : |(wn1 : ℝ) - wn| / F.wd = (wn1 : ℝ) / F.wd - (wn : ℝ) / F.wd := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < (wn1 : ℝ) - wn), sub_div]
      rw [e]
      exact pow_le_pow_left₀ (by linarith [hw.1]) (by linarith [hw.2]) 2
    have hdt : (τ - (m : ℝ) / 4096) ^ 2 ≤ (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 := by
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      obtain ⟨hτ1, hτ2⟩ := hτ
      have b1 : ((m : ℝ) - mp) / 4096 ≤ max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096 :=
        div_le_div_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (by norm_num)
      have b2 : ((mn2 : ℝ) - m) / 4096 ≤ max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096 :=
        div_le_div_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) (by norm_num)
      rw [sub_div] at b1 b2
      rw [abs_le]; constructor <;> linarith
    have hρρ : faceRho F.kind w * faceRho F.kind ((wn : ℝ) / F.wd) ≤ ρm ^ 2 := by
      have := hρle w hw
      have := hρle _ hW1
      nlinarith
    have hsq : ((D : ℝ) * S32) ^ 2 * ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ -
        circ (faceRho F.kind ((wn : ℝ) / F.wd)) (faceZeta F.kind ((wn : ℝ) / F.wd))
          ((m : ℝ) / 4096)‖ ^ 2 ≤ (Q.rcT.rBD : ℝ) ^ 2 := by
      have hNt' := hNt
      have hN' : (Q.nt : ℝ) ≤ (Q.rcT.rBD : ℝ) ^ 2 := by
        have := (by exact_mod_cast hN : ((Q.nt : ℕ) : ℝ) ≤ ((sq Q.rcT.rBD : ℕ) : ℝ))
        rwa [sq_cast] at this
      refine le_trans ?_ (hNt'.trans hN')
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 4 * (faceRho F.kind w * faceRho F.kind ((wn : ℝ) / F.wd)) * (τ - (m : ℝ) / 4096) ^ 2 ≤
          4 * ρm ^ 2 * (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 :=
        mul_le_mul (by linarith) hdt (sq_nonneg _) (by positivity)
      linarith
    have h2' : ((D : ℝ) * S32 * ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ -
        circ (faceRho F.kind ((wn : ℝ) / F.wd)) (faceZeta F.kind ((wn : ℝ) / F.wd))
          ((m : ℝ) / 4096)‖) ^ 2 ≤ (Q.rcT.rBD : ℝ) ^ 2 := by rw [mul_pow]; exact hsq
    exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) two_ne_zero).mp h2'
  intro z hz s hs
  have hz' : z ∈ R.map (fun z => (z.1, z.2.1, z.2.2.1)) := by rw [hR]; exact hz
  obtain ⟨zr, hzr, rfl⟩ := List.mem_map.mp hz'
  obtain ⟨hva, hvb, hsg, hchk⟩ := hrec zr hzr
  simp only [remChk, srTriple, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hchk
  obtain ⟨⟨-, hLt⟩, h25⟩ := hchk
  have hx : (D : ℝ) * S32 * ‖ptF F.kind t w - cornerR (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 D‖ ≤ Q.rcT.rBD := by
    rw [ptF_eq]; exact hreach t ht
  have hd := rec_dist hD hva hvb hsg Q.rcT hTs hs0T hLt hx hs
  have h25' : ((Q.lam2 : ℕ) : ℝ) ≤ 25 * (cellL Q.rcT (d2Low zr.2.2.2.1.n zr.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o zr.1 zr.2.1 zr.2.2.1).vv)) : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_eq] using h25)
  rw [hl2] at h25'
  have hLt' : (0 : ℝ) < (cellL Q.rcT (d2Low zr.2.2.2.1.n zr.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o zr.1 zr.2.1 zr.2.2.1).vv)) : ℝ) := by exact_mod_cast hLt
  have hpos : 0 < ‖ptF F.kind t w - seg (ptR zr.2.1) (ptR zr.2.2.1) s‖ := by
    rcases (norm_nonneg (ptF F.kind t w - seg (ptR zr.2.1) (ptR zr.2.2.1) s)).lt_or_eq with h | h
    · exact h
    · have h0 : ((D : ℝ) * S32) ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
      rw [← h, h0] at hd; linarith
  have h25'' : ((D : ℝ) * S32) ^ 2 ≤ 25 * (((D : ℝ) * S32) ^ 2 *
      ‖ptF F.kind t w - seg (ptR zr.2.1) (ptR zr.2.2.1) s‖ ^ 2) :=
    h25'.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  exact one_fifth_le hlam hpos h25''

/-- **The `t`-remainder of a passing corner.** -/
theorem corner_t_bound (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hfv : FilsOK4 o nS fils) (F : Face4) (hF : Face4OK F) (mp m mn mn2 wp wn wn1 wn2 : ℤ)
    (hm01 : mp < m) (hm12 : m < mn) (hm23 : mn < mn2)
    (h01 : wp < wn) (h12 : wn < wn1) (_h23 : wn1 < wn2)
    (hk : F.kind < 2 ∨ 17 / 20 ≤ (wp : ℝ) / F.wd)
    (hcell : ∀ w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd), 17 / 20 ≤ faceRho F.kind w ∧
      faceRho F.kind w ≤ 23 / 20 ∧ |faceZeta F.kind w| ≤ 3 / 25)
    (hlo : -1 / 2 ≤ (mp : ℝ) / 4096) (hhi : (mn2 : ℝ) / 4096 ≤ 1 / 2) (gs : List (List ℕ))
    (hxyz : (cornerXYZ4 F m wn).2 = true)
    (hok : (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) (cornerXYZ4 F m wn).1.1
      (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 (cornerXYZ4 F m wn).1.2.2.2
      (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m))
      (some (remP4 F mp m mn2 wp wn wn1 wn2 (cornerXYZ4 F m wn).1.2.2.2)) gs).ok = true)
    (n : Space) (hn : ‖n‖ ≤ 1) (w : ℝ) (hw : w ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd))
    (t : ℝ) (ht : t ∈ Icc ((m : ℝ) / 4096) ((mn : ℝ) / 4096)) :
    |⟪n, errF fils (ptF F.kind t w)⟫ - newt ((mp : ℝ) / 4096) ((m : ℝ) / 4096)
      ((mn : ℝ) / 4096) ((mn2 : ℝ) / 4096)
      ⟪n, errF fils (ptF F.kind ((mp : ℝ) / 4096) w)⟫
      ⟪n, errF fils (ptF F.kind ((m : ℝ) / 4096) w)⟫
      ⟪n, errF fils (ptF F.kind ((mn : ℝ) / 4096) w)⟫
      ⟪n, errF fils (ptF F.kind ((mn2 : ℝ) / 4096) w)⟫ t| ≤
      (rtC F mp m mn mn2 (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2)
        (cornerXYZ4 F m wn).1.1 (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1
        (cornerXYZ4 F m wn).1.2.2.2 (helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m))
        (some (remP4 F mp m mn2 wp wn wn1 wn2 (cornerXYZ4 F m wn).1.2.2.2)) gs).rt : ℝ) /
        ((two40 : ℕ) : ℝ) := by
  have hF' := hF
  obtain ⟨hk4, hwd, -, -, -, -⟩ := hF
  set D := (cornerXYZ4 F m wn).1.2.2.2
  set Q := remP4 F mp m mn2 wp wn wn1 wn2 D
  obtain ⟨hc, hD⟩ := cornerR_cornerXYZ4 F hwd m wn hxyz
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hwn01 : (wn : ℝ) < wn1 := by exact_mod_cast h12
  have hwpos : F.kind < 2 ∨ 0 < wn := by
    rcases hk with h | h
    · exact Or.inl h
    · right
      have : (0 : ℝ) < (wp : ℝ) / F.wd := by linarith
      have : (0 : ℝ) < wp := (div_pos_iff_of_pos_right hwd').mp this
      have : (0 : ℤ) < wp := by exact_mod_cast this
      omega
  obtain ⟨hh0, hhv⟩ := helAt_corner4 F ⟨hk4, hwd⟩ m wn hwpos
  rw [← hc] at hhv
  have hs := cornerEval4_sound o nS fils hfv.1 hfv.2.1 hfv.2.2 _ _ _ D hD _ hh0 hhv _ gs hok
  obtain ⟨R, hR, hrec, -, hrt, -, hTs, hN⟩ := hs.2 Q rfl
  have hρN : 0 < rhoN F wn1 := by
    unfold rhoN
    split_ifs with h2
    · unfold cylR; split_ifs <;> norm_num
    · have := hwpos.resolve_left h2
      simp only [iabs]; omega
  obtain ⟨-, hs0T, -, hNt, -, -, h6, h4, h2⟩ := remP4_spec F hwd mp m mn2 wp wn wn1 wn2 D hD hρN
  have hlam : 0 < (D : ℝ) * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hq : (0 : ℝ) < 4096 := by norm_num
  have o01 : (mp : ℝ) / 4096 < (m : ℝ) / 4096 := by
    have : (mp : ℝ) < m := by exact_mod_cast hm01
    linarith [div_lt_div_of_pos_right this hq]
  have o12 : (m : ℝ) / 4096 < (mn : ℝ) / 4096 := by
    have : (m : ℝ) < mn := by exact_mod_cast hm12
    linarith [div_lt_div_of_pos_right this hq]
  have o23 : (mn : ℝ) / 4096 < (mn2 : ℝ) / 4096 := by
    have : (mn : ℝ) < mn2 := by exact_mod_cast hm23
    linarith [div_lt_div_of_pos_right this hq]
  -- the radii
  set ρm := (rhoN F wn1 : ℝ) / rhoD F
  have hρd' : (0 : ℝ) < rhoD F := by exact_mod_cast rhoD_pos F hwd
  obtain ⟨hρ1, hρ2, hζ⟩ := hcell w hw
  have hW1 : (wn : ℝ) / F.wd ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd) :=
    ⟨le_rfl, (div_lt_div_wd hwd h12).le⟩
  obtain ⟨hρ01, -, -⟩ := hcell _ hW1
  have hρle : ∀ v ∈ Icc ((wn : ℝ) / F.wd) ((wn1 : ℝ) / F.wd), faceRho F.kind v ≤ ρm := by
    intro v hv
    simp only [faceRho, ρm, rhoN, rhoD]
    split_ifs with h2
    · push_cast; unfold cylR; split_ifs <;> norm_num
    · have hpos := hwpos.resolve_left h2
      have hw1 : (0 : ℝ) < wn1 := by exact_mod_cast (hpos.trans h12)
      simp only [iabs_cast]
      rw [abs_of_pos hw1]
      exact hv.2
  have hρpos : 0 < faceRho F.kind w := by linarith
  have hρ0pos : 0 < faceRho F.kind ((wn : ℝ) / F.wd) := by linarith
  -- the region
  have hreach : ∀ τ ∈ Icc ((mp : ℝ) / 4096) ((mn2 : ℝ) / 4096), (D : ℝ) * S32 *
      ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ - cornerR (cornerXYZ4 F m wn).1.1
        (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1 D‖ ≤ Q.rcT.rBD := by
    intro τ hτ
    rw [hc, faceSigma_phiT]
    have hd := circ_dist_sq hρpos.le hρ0pos.le (faceZeta F.kind w) (faceZeta F.kind ((wn : ℝ) /
        F.wd))
      τ ((m : ℝ) / 4096)
    -- `(ρ - ρ₀)² + (ζ - ζ₀)² = (w - w₁)²`
    have hrz : (faceRho F.kind w - faceRho F.kind ((wn : ℝ) / F.wd)) ^ 2 +
        (faceZeta F.kind w - faceZeta F.kind ((wn : ℝ) / F.wd)) ^ 2 = (w - (wn : ℝ) / F.wd) ^
            2 := by
      simp only [faceRho, faceZeta]; split_ifs <;> ring
    have hdw : (w - (wn : ℝ) / F.wd) ^ 2 ≤ (|(wn1 : ℝ) - wn| / F.wd) ^ 2 := by
      have e : |(wn1 : ℝ) - wn| / F.wd = (wn1 : ℝ) / F.wd - (wn : ℝ) / F.wd := by
        rw [abs_of_pos (by linarith : (0 : ℝ) < (wn1 : ℝ) - wn), sub_div]
      rw [e]
      exact pow_le_pow_left₀ (by linarith [hw.1]) (by linarith [hw.2]) 2
    have hdt : (τ - (m : ℝ) / 4096) ^ 2 ≤ (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 := by
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _)
      obtain ⟨hτ1, hτ2⟩ := hτ
      have b1 : ((m : ℝ) - mp) / 4096 ≤ max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096 :=
        div_le_div_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (by norm_num)
      have b2 : ((mn2 : ℝ) - m) / 4096 ≤ max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096 :=
        div_le_div_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) (by norm_num)
      rw [sub_div] at b1 b2
      rw [abs_le]; constructor <;> linarith
    have hρρ : faceRho F.kind w * faceRho F.kind ((wn : ℝ) / F.wd) ≤ ρm ^ 2 := by
      have := hρle w hw
      have := hρle _ hW1
      nlinarith
    have hsq : ((D : ℝ) * S32) ^ 2 * ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ -
        circ (faceRho F.kind ((wn : ℝ) / F.wd)) (faceZeta F.kind ((wn : ℝ) / F.wd))
          ((m : ℝ) / 4096)‖ ^ 2 ≤ (Q.rcT.rBD : ℝ) ^ 2 := by
      have hNt' := hNt
      have hN' : (Q.nt : ℝ) ≤ (Q.rcT.rBD : ℝ) ^ 2 := by
        have := (by exact_mod_cast hN : ((Q.nt : ℕ) : ℝ) ≤ ((sq Q.rcT.rBD : ℕ) : ℝ))
        rwa [sq_cast] at this
      refine le_trans ?_ (hNt'.trans hN')
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 4 * (faceRho F.kind w * faceRho F.kind ((wn : ℝ) / F.wd)) * (τ - (m : ℝ) / 4096) ^ 2 ≤
          4 * ρm ^ 2 * (max |(m : ℝ) - mp| |(mn2 : ℝ) - m| / 4096) ^ 2 :=
        mul_le_mul (by linarith) hdt (sq_nonneg _) (by positivity)
      linarith
    have h2' : ((D : ℝ) * S32 * ‖circ (faceRho F.kind w) (faceZeta F.kind w) τ -
        circ (faceRho F.kind ((wn : ℝ) / F.wd)) (faceZeta F.kind ((wn : ℝ) / F.wd))
          ((m : ℝ) / 4096)‖) ^ 2 ≤ (Q.rcT.rBD : ℝ) ^ 2 := by rw [mul_pow]; exact hsq
    exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) two_ne_zero).mp h2'
  have hTb := fun τ (hτ : τ ∈ Icc ((mp : ℝ) / 4096) ((mn2 : ℝ) / 4096)) =>
    Tm_bounds (hm01.trans (hm12.trans hm23)).le hτ
  have htm : 0 ≤ tmP mp mn2 := by unfold tmP; positivity
  have hcoil := tline_coil o fils hD n hn R hR Q hrec hTs hs0T hρpos (hρle w hw)
    (TmP_le_one mp mn2) htm h6 h4 h2 o01 o12 o23 ht hTb hreach
  have hhel := hel_t_face hn hρ1 hρ2 hζ o01 o12 o23 hlo hhi ht
  rw [← hrt] at hcoil
  simp only [errF, inner_sub_right, newt_sub, ptF_eq]
  simp only [ptF_eq] at hhel
  have hω := abs_omega_le o01.le o23.le ht
  refine le_trans ?_ (rtC_ge F hF' hm01 hm12 hm23 _ hω)
  set A := ⟪n, Bseg fils (circ (faceRho F.kind w) (faceZeta F.kind w) t)⟫ - newt ((mp : ℝ) / 4096)
    ((m : ℝ) / 4096) ((mn : ℝ) / 4096) ((mn2 : ℝ) / 4096)
    ⟪n, Bseg fils (circ (faceRho F.kind w) (faceZeta F.kind w) ((mp : ℝ) / 4096))⟫
    ⟪n, Bseg fils (circ (faceRho F.kind w) (faceZeta F.kind w) ((m : ℝ) / 4096))⟫
    ⟪n, Bseg fils (circ (faceRho F.kind w) (faceZeta F.kind w) ((mn : ℝ) / 4096))⟫
    ⟪n, Bseg fils (circ (faceRho F.kind w) (faceZeta F.kind w) ((mn2 : ℝ) / 4096))⟫ t
  set H := ⟪n, hel (circ (faceRho F.kind w) (faceZeta F.kind w) t)⟫ - newt ((mp : ℝ) / 4096)
    ((m : ℝ) / 4096) ((mn : ℝ) / 4096) ((mn2 : ℝ) / 4096)
    ⟪n, hel (circ (faceRho F.kind w) (faceZeta F.kind w) ((mp : ℝ) / 4096))⟫
    ⟪n, hel (circ (faceRho F.kind w) (faceZeta F.kind w) ((m : ℝ) / 4096))⟫
    ⟪n, hel (circ (faceRho F.kind w) (faceZeta F.kind w) ((mn : ℝ) / 4096))⟫
    ⟪n, hel (circ (faceRho F.kind w) (faceZeta F.kind w) ((mn2 : ℝ) / 4096))⟫ t
  have e : ∀ a b c d : ℝ, a - b - (c - d) = (a - c) - (b - d) := fun a b c d => by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have : |A| + |H| ≤ _ := add_le_add hcoil hhel
  refine this.trans (le_of_eq ?_)
  ring

end PlasmaLean.Design.PolygonCoil
