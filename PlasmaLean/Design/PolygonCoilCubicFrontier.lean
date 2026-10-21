/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicData
public import PlasmaLean.Design.PolygonCoilCubicSoundF
public import PlasmaLean.Design.PolygonCoilSymm

/-!
# The cubic certificate on the whole frontier of `Ωa`, `a = 3420/32761`

For the coil set `filsC` (`Design/PolygonCoilCubicData`):

* `FrontPtC y`: `y ∈ Ka a` lies on one of the four faces `|s| = a`, `|z| = a`;
* `fund_polarT`: a point of the fundamental piece `y₁ ≥ |y₀|` is
  `(ρ cos φ, ρ sin φ, z)` with `φ = π/2 + 2 arctan t`, `t = -y₀/(ρ + y₁)`, `|t| ≤ √2 - 1`;
* `CoversC`: the four face covers (`RectGood` on rectangles containing `|t| ≤ 1697/4096` and the
  face range), proved by the kernel certificates in `Design/PolygonCoilCubicCellsF`;
* `fund_QC`: on the fundamental piece the face covers apply;
* `frontier_QC` (**frontier bound**): given `CoversC`, at every face point
  `‖Bseg filsC - hel‖ ≤ etaC·2⁻⁴⁰` (`≈ 3.221 × 10⁻⁶`) and the distance to every point of the
  coil is `≥ 1/5`, by the symmetries `Rot_π`, `σ` of `Bseg`, `hel` and the coil.

The module also contains the coil-data validity `filsOK4C` and the small assembly lemmas used by
the certificate modules (`line_facts`, `rowsT_cons`, `cellsAll4_cons`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.RationalStellarator.Confined
  Set Real
open scoped RealInnerProductSpace

/-- The certified error `etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶` of the cubic certificate. -/
@[expose] def etaRC : ℝ := (etaC : ℝ) / ((two40 : ℕ) : ℝ)

/-- The certified error is nonnegative. -/
theorem etaRC_nonneg : 0 ≤ etaRC := by unfold etaRC; positivity

/-- Decimal upper bound on the certified error. -/
theorem etaRC_le : etaRC ≤ 3221 / 1000000000 := by
  norm_num [etaRC, etaC, two40]

/-- A point of a face of `Ωa aF`. -/
@[expose] def FrontPtC (y : Space) : Prop := y ∈ Ka aF ∧ (|sc y| = aF ∨ |y 2| = aF)

/-- The certified property at a point (cubic design). -/
@[expose] def QpC (y : Space) : Prop :=
  ‖Bseg filsC y - hel y‖ ≤ etaRC ∧ ∀ x, coilPt filsC x → 1 / 5 ≤ ‖y - x‖

/-! ## Coil data and certificate assembly -/

/-- Every filament of `filsC` is nonempty and there are at most `nSC` segments. -/
theorem filsC_shape : (filsC.all fun f => !f.2.isEmpty) = true ∧ (allSegs filsC).length ≤ nSC :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The filaments of `filsC` pass `filOK` (one kernel evaluation). -/
theorem filsC_ok : (filsC.all fun f => filOK offsC f.1 f.2) = true := by decide +kernel

/-- **Validity of the coil data of the cubic design.** -/
theorem filsOK4C : FilsOK4 offsC nSC filsC := by
  refine ⟨fun f hf => ?_, fun f hf => List.all_eq_true.mp filsC_ok f hf, filsC_shape.2⟩
  have := List.all_eq_true.mp filsC_shape.1 f hf
  simpa using this

/-- The facts certified by one kernel line check. -/
theorem line_facts {F : Face4} (hF : Face4OK F) {mp m mn mn2 : ℤ} {L : List CRec}
    (h : lineOut4 offsC nSC filsDL F mp m mn mn2 = L) :
    (List.Forall₂ (LVal filsC F m) F.wn L ∧ QuadP (LW filsC F m) F.wn L) ∧
      QuadP (LT filsC F mp m mn mn2) F.wn L := by
  rw [filsDL_eq] at h
  subst h
  have := lineOut4_sound offsC nSC filsC filsOK4C F hF mp m mn mn2
  exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩

/-- One step of `RowsT`. -/
theorem rowsT_cons {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {F : Face4} {m0 m1 m2 m3 : ℤ}
    {ms : List ℤ} {L0 L1 L2 L3 : List CRec} {Ls : List (List CRec)}
    (h1 : QuadP (LT fils F m0 m1 m2 m3) F.wn L1)
    (h2 : RowsT fils F (m1 :: m2 :: m3 :: ms) (L1 :: L2 :: L3 :: Ls)) :
    RowsT fils F (m0 :: m1 :: m2 :: m3 :: ms) (L0 :: L1 :: L2 :: L3 :: Ls) := ⟨h1, h2⟩

/-- The end of `RowsT`. -/
theorem rowsT_end {fils : List (ℤ × List (ℤ × ℤ × ℤ))} {F : Face4} {m0 m1 m2 : ℤ}
    {L0 L1 L2 : List CRec} : RowsT fils F [m0, m1, m2] [L0, L1, L2] := trivial

/-- One step of `cellsAll4` (rows are checked by separate kernel evaluations). -/
theorem cellsAll4_cons {eta : ℕ} {F : Face4} {m0 m1 m2 m3 : ℤ} {ms : List ℤ}
    {L0 L1 L2 L3 : List CRec} {Ls : List (List CRec)}
    (h1 : cellsRow4 F eta m0 m1 m2 m3 L0 L1 L2 L3 F.wn = true)
    (h2 : cellsAll4 eta F (m1 :: m2 :: m3 :: ms) (L1 :: L2 :: L3 :: Ls) = true) :
    cellsAll4 eta F (m0 :: m1 :: m2 :: m3 :: ms) (L0 :: L1 :: L2 :: L3 :: Ls) = true := by
  simp only [cellsAll4, h1, h2, Bool.and_self]

/-- The end of `cellsAll4`. -/
theorem cellsAll4_end {eta : ℕ} {F : Face4} {m0 m1 m2 : ℤ} {L0 L1 L2 : List CRec} :
    cellsAll4 eta F [m0, m1, m2] [L0, L1, L2] = true := rfl

/-- Lower end of the `w`-range of face `k`. -/
@[expose] def faceLoC (k : ℕ) : ℝ := if k < 2 then -aF else 161 / 181

/-- Upper end of the `w`-range of face `k`. -/
@[expose] def faceHiC (k : ℕ) : ℝ := if k < 2 then aF else 199 / 181

/-- A certified cover of face `k`: a rectangle containing `|t| ≤ 1697/4096` and the face range on
which `RectGood` holds. -/
@[expose] def FaceCovC (k : ℕ) : Prop :=
  ∃ T1 T2 W1 W2 : ℝ, RectGood filsC k etaC T1 T2 W1 W2 ∧ T1 ≤ -(1697 / 4096) ∧
    1697 / 4096 ≤ T2 ∧ W1 ≤ faceLoC k ∧ faceHiC k ≤ W2

/-- The four face covers. -/
@[expose] def CoversC : Prop := FaceCovC 0 ∧ FaceCovC 1 ∧ FaceCovC 2 ∧ FaceCovC 3

/-! ## Symmetry reduction -/

theorem filsC_eq : filsC = (List.zip repKC repVC).flatMap (fun kv => orbit kv.1 kv.2) := rfl

/-- The certified property is invariant under `Rot_π`. -/
theorem QpC_rotPi {y : Space} (h : QpC y) : QpC (rotPi y) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [filsC_eq, Bseg_rotPi, hel_rotPi, ← isSym_rotPi.sub, isSym_rotPi.norm, ← filsC_eq]
    exact h.1
  · have hx' := coilPt_rotPi _ (filsC_eq ▸ hx)
    rw [← filsC_eq] at hx'
    have e : rotPi y - x = rotPi (y - rotPi x) := by rw [isSym_rotPi.sub, rotPi_rotPi]
    rw [e, isSym_rotPi.norm]
    exact h.2 _ hx'

/-- The certified property is invariant under the stellarator symmetry `σ`. -/
theorem QpC_σ {y : Space} (h : QpC y) : QpC (σ y) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [filsC_eq, Bseg_σ, hel_σ, ← filsC_eq, show -σ (Bseg filsC y) - -σ (hel y) =
      -(σ (Bseg filsC y) - σ (hel y)) by abel, norm_neg, ← isSym_σ.sub, isSym_σ.norm]
    exact h.1
  · have hx' := coilPt_σ _ (filsC_eq ▸ hx)
    rw [← filsC_eq] at hx'
    have e : σ y - x = σ (y - σ x) := by rw [isSym_σ.sub, σ_σ]
    rw [e, isSym_σ.norm]
    exact h.2 _ hx'

/-- `s` is invariant under `Rot_π`. -/
theorem sc_rotPiC (y : Space) : sc (rotPi y) = sc y := by simp [sc, r2, rotPi]
/-- `s` is invariant under `σ`. -/
theorem sc_σC (y : Space) : sc (σ y) = sc y := by simp [sc, r2, σ]; ring

/-- The faces are invariant under `Rot_π`. -/
theorem FrontPtC_rotPi {y : Space} (h : FrontPtC y) : FrontPtC (rotPi y) := by
  have e : rotPi y 2 = y 2 := by simp [rotPi]
  unfold FrontPtC Ka at *
  simp only [mem_ofPred_eq, sc_rotPiC, e] at *
  exact h

/-- The faces are invariant under `σ`. -/
theorem FrontPtC_σ {y : Space} (h : FrontPtC y) : FrontPtC (σ y) := by
  have e : |σ y 2| = |y 2| := by simp [σ]
  unfold FrontPtC Ka at *
  simp only [mem_ofPred_eq, sc_σC, e] at *
  exact h

/-- Reduction to the fundamental piece `y₁ ≥ |y₀|`. -/
theorem reduce_fundC (hf : ∀ y, FrontPtC y → |y 0| ≤ y 1 → QpC y) {y : Space}
    (hy : FrontPtC y) : QpC y := by
  rcases le_total |y 0| |y 1| with h | h
  · rcases le_total 0 (y 1) with h1 | h1
    · exact hf y hy (by rwa [abs_of_nonneg h1] at h)
    · have := hf (rotPi y) (FrontPtC_rotPi hy) (by
        simp only [rotPi]; simp; rw [abs_of_nonpos h1] at h; linarith)
      simpa [rotPi_rotPi] using QpC_rotPi this
  · rcases le_total 0 (y 0) with h1 | h1
    · have := hf (σ y) (FrontPtC_σ hy) (by
        simp only [σ]; simp; rw [abs_of_nonneg h1] at h; linarith)
      simpa [σ_σ] using QpC_σ this
    · have := hf (rotPi (σ y)) (FrontPtC_rotPi (FrontPtC_σ hy)) (by
        simp only [rotPi, σ]; simp; rw [abs_of_nonpos h1] at h; linarith)
      simpa [rotPi_rotPi, σ_σ] using QpC_σ (QpC_rotPi this)

/-- Polar form of a point of the fundamental piece in the rational parametrisation
`φ = π/2 + 2 arctan t`, `|t| ≤ 1697/4096`. -/
theorem fund_polarT {y : Space} (hr : 0 < r2 y) (hy : |y 0| ≤ y 1) :
    ∃ t, |t| ≤ 1697 / 4096 ∧ y = polarPt (sqrt (r2 y)) (y 2) (phiT t) := by
  set ρ := sqrt (r2 y)
  have hρ2 : ρ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [sq_sqrt hr.le]; rfl
  have hρ0 : 0 ≤ ρ := sqrt_nonneg _
  have ha := abs_nonneg (y 0)
  have hy1 : 0 < y 1 := by
    by_contra hn
    have h1' : y 1 = 0 := by linarith
    have h0 : y 0 = 0 := abs_eq_zero.mp (by linarith)
    have : r2 y = 0 := by simp only [r2]; rw [h0, h1']; ring
    linarith
  have hρpos : 0 < ρ := by nlinarith
  have hpos : 0 < ρ + y 1 := by linarith
  set t := -y 0 / (ρ + y 1)
  refine ⟨t, ?_, ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos hpos, div_le_div_iff₀ hpos (by norm_num)]
    have hsq : |y 0| ^ 2 = y 0 ^ 2 := sq_abs _
    have key : (4096 * |y 0| - 1697 * y 1) ≤ 1697 * ρ := by
      rcases le_total (4096 * |y 0| - 1697 * y 1) 0 with h | h
      · linarith
      · apply le_of_sq_le_sq _ (by positivity)
        have : (1697 * ρ) ^ 2 = 1697 ^ 2 * (|y 0| ^ 2 + y 1 ^ 2) := by rw [hsq, ← hρ2]; ring
        rw [this]
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hy)]
    linarith
  · have hden : 1 + t ^ 2 = 2 * ρ / (ρ + y 1) := by
      simp only [t]
      field_simp
      nlinarith [hρ2]
    have hc : ρ * cos (phiT t) = y 0 := by
      rw [cos_phiT, hden]
      simp only [t]
      field_simp
    have hs : ρ * sin (phiT t) = y 1 := by
      rw [sin_phiT, hden]
      simp only [t]
      field_simp
      nlinarith [hρ2]
    ext k; fin_cases k
    · simp [polarPt, hc]
    · simp [polarPt, hs]
    · simp [polarPt]

/-- `√x = c` from `x = c²`, `c ≥ 0`. -/
theorem sqrt_sq_eqC {c x : ℝ} (hc : 0 ≤ c) (h : x = c ^ 2) : sqrt x = c := by
  rw [h, sqrt_sq hc]

/-- A face cover gives the certified property at its points. -/
theorem toQC {k : ℕ} {T1 T2 W1 W2 t w : ℝ} {y : Space} (hF : RectGood filsC k etaC T1 T2 W1 W2)
    (ht : t ∈ Icc T1 T2) (hw : w ∈ Icc W1 W2) (he : y = ptF k t w) : QpC y := by
  obtain ⟨h1, h2⟩ := hF t ht w hw
  rw [← he] at h1 h2
  exact ⟨h1, fun x ⟨z, hz, s, hs, hx⟩ => by rw [hx]; exact h2 z hz s hs⟩

/-- A face cover gives the certified property at the points of the face. -/
theorem toQC' {k : ℕ} (hc : FaceCovC k) {t w : ℝ} {y : Space} (ht : |t| ≤ 1697 / 4096)
    (hw1 : faceLoC k ≤ w) (hw2 : w ≤ faceHiC k) (he : y = ptF k t w) : QpC y := by
  obtain ⟨T1, T2, W1, W2, hR, h1, h2, h3, h4⟩ := hc
  have ht' := abs_le.mp ht
  exact toQC hR ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ he

/-- **The fundamental piece.** -/
theorem fund_QC (hc : CoversC) {y : Space} (hy : FrontPtC y) (hf : |y 0| ≤ y 1) : QpC y := by
  obtain ⟨⟨hs, hz⟩, hface⟩ := hy
  have hr : 0 < r2 y := Ka_sub_domain (a := aF) (by norm_num [aF]) ⟨hs, hz⟩
  obtain ⟨t, ht, hyp⟩ := fund_polarT hr hf
  have hsc : sc y = (r2 y - 1) / 2 := rfl
  have hz' := abs_le.mp (show |y 2| ≤ aF from hz)
  have hsq : ∀ c : ℝ, 0 ≤ c → r2 y = c ^ 2 → sqrt (r2 y) = c := fun c hc h => sqrt_sq_eqC hc h
  rcases hface with h | h
  · rcases abs_eq (by norm_num [aF] : (0 : ℝ) ≤ aF) |>.mp h with h' | h'
    · -- the outer cylinder
      have hρ : sqrt (r2 y) = 199 / 181 := hsq _ (by norm_num) (by
        rw [hsc, aF] at h'; linarith)
      refine toQC' hc.1 ht (w := y 2) (by simp [faceLoC]; linarith) (by simp [faceHiC]; linarith) ?_
      conv_lhs => rw [hyp, hρ]
      simp [ptF, faceSigma, cylR]
    · have hρ : sqrt (r2 y) = 161 / 181 := hsq _ (by norm_num) (by
        rw [hsc, aF] at h'; linarith)
      refine toQC' hc.2.1 ht (w := y 2) (by simp [faceLoC]; linarith) (by simp [faceHiC]; linarith)
        ?_
      conv_lhs => rw [hyp, hρ]
      simp [ptF, faceSigma, cylR]
  · have hρb : 161 / 181 ≤ sqrt (r2 y) ∧ sqrt (r2 y) ≤ 199 / 181 := by
      have := abs_le.mp hs
      rw [hsc, aF] at this
      constructor
      · rw [le_sqrt (by norm_num) hr.le]; linarith
      · rw [sqrt_le_left (by norm_num)]; linarith
    rcases abs_eq (by norm_num [aF] : (0 : ℝ) ≤ aF) |>.mp h with h' | h'
    · refine toQC' hc.2.2.1 ht (w := sqrt (r2 y)) (by simp [faceLoC]; linarith [hρb.1])
        (by simp [faceHiC]; linarith [hρb.2]) ?_
      conv_lhs => rw [hyp]
      simp [ptF, faceSigma, planeZ, h']
    · refine toQC' hc.2.2.2 ht (w := sqrt (r2 y)) (by simp [faceLoC]; linarith [hρb.1])
        (by simp [faceHiC]; linarith [hρb.2]) ?_
      conv_lhs => rw [hyp]
      simp [ptF, faceSigma, planeZ, h']

/-- **The frontier bound (cubic design).** Given the four face covers, at every point of the four
faces of `Ωa aF`, `‖Bseg filsC - hel‖ ≤ etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶` and every point of the coil is
at distance `≥ 1/5`. -/
theorem frontier_QC (hc : CoversC) {y : Space} (hy : FrontPtC y) : QpC y :=
  reduce_fundC (fun _ hy hf => fund_QC hc hy hf) hy

end PlasmaLean.Design.PolygonCoil
