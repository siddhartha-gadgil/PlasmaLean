/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCover
public import PlasmaLean.Design.PolygonCoilSymm

/-!
# The certified bound on the whole frontier of `Ωa`, `a = 3420/32761`

* `FrontPt y`: `y ∈ Ka a` lies on one of the four faces `|s| = a`, `|z| = a`;
* `fund_Q`: on the fundamental piece `y₁ ≥ |y₀|` the face covers `cover0`–`cover3` apply
  (`y = (ρ cos φ, ρ sin φ, z)` with `φ = 2 arctan(y₁/(ρ + y₀)) ∈ [φ_1696, φ_9889]`);
* `frontier_Q` (**frontier bound**): at every face point, `‖Bseg fils - hel‖ ≤ etaFp·2⁻⁴⁰`
  (`≤ 6.5 × 10⁻⁴`) and the distance to every point of the coil is `≥ 1/5`, by the symmetries
  `Rot_π`, `σ` of `Bseg fils`, `hel` and the coil.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.RationalStellarator.Confined
  Set Real
open scoped RealInnerProductSpace

/-- The certified error `etaFp·2⁻⁴⁰ ≈ 6.4999 × 10⁻⁴`. It sits exactly at the one-transit threshold
`6.5 × 10⁻⁴` (zero margin; `etaFp` is the floor of `6.5 × 10⁻⁴ · 2⁴⁰`) and is `11.6×` above the
10-transit requirement `5.6 × 10⁻⁵`. -/
@[expose] def etaR : ℝ := (etaFp : ℝ) / ((two40 : ℕ) : ℝ)

theorem etaR_nonneg : 0 ≤ etaR := by unfold etaR; positivity

theorem etaR_le : etaR ≤ 65 / 100000 := by norm_num [etaR, etaFp, two40]

/-- A point of a face of `Ωa aF`. -/
@[expose] def FrontPt (y : Space) : Prop := y ∈ Ka aF ∧ (|sc y| = aF ∨ |y 2| = aF)

/-- The certified property at a point. -/
@[expose] def Qp (y : Space) : Prop :=
  ‖Bseg fils y - hel y‖ ≤ etaR ∧ ∀ x, coilPt fils x → 1 / 5 ≤ ‖y - x‖

theorem fils_eq : fils = (List.zip repK repV).flatMap (fun kv => orbit kv.1 kv.2) := rfl

theorem Qp_rotPi {y : Space} (h : Qp y) : Qp (rotPi y) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [fils_eq, Bseg_rotPi, hel_rotPi, ← isSym_rotPi.sub, isSym_rotPi.norm, ← fils_eq]
    exact h.1
  · have hx' := coilPt_rotPi _ (fils_eq ▸ hx)
    rw [← fils_eq] at hx'
    have e : rotPi y - x = rotPi (y - rotPi x) := by rw [isSym_rotPi.sub, rotPi_rotPi]
    rw [e, isSym_rotPi.norm]
    exact h.2 _ hx'

theorem Qp_σ {y : Space} (h : Qp y) : Qp (σ y) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [fils_eq, Bseg_σ, hel_σ, ← fils_eq, show -σ (Bseg fils y) - -σ (hel y) =
      -(σ (Bseg fils y) - σ (hel y)) by abel, norm_neg, ← isSym_σ.sub, isSym_σ.norm]
    exact h.1
  · have hx' := coilPt_σ _ (fils_eq ▸ hx)
    rw [← fils_eq] at hx'
    have e : σ y - x = σ (y - σ x) := by rw [isSym_σ.sub, σ_σ]
    rw [e, isSym_σ.norm]
    exact h.2 _ hx'

theorem sc_rotPi (y : Space) : sc (rotPi y) = sc y := by simp [sc, r2, rotPi]
theorem sc_σ (y : Space) : sc (σ y) = sc y := by simp [sc, r2, σ]; ring

theorem FrontPt_rotPi {y : Space} (h : FrontPt y) : FrontPt (rotPi y) := by
  have e : rotPi y 2 = y 2 := by simp [rotPi]
  unfold FrontPt Ka at *
  simp only [mem_ofPred_eq, sc_rotPi, e] at *
  exact h

theorem FrontPt_σ {y : Space} (h : FrontPt y) : FrontPt (σ y) := by
  have e : |σ y 2| = |y 2| := by simp [σ]
  unfold FrontPt Ka at *
  simp only [mem_ofPred_eq, sc_σ, e] at *
  exact h

/-- Reduction to the fundamental piece `y₁ ≥ |y₀|`. -/
theorem reduce_fund (hf : ∀ y, FrontPt y → |y 0| ≤ y 1 → Qp y) {y : Space} (hy : FrontPt y) :
    Qp y := by
  rcases le_total |y 0| |y 1| with h | h
  · rcases le_total 0 (y 1) with h1 | h1
    · exact hf y hy (by rwa [abs_of_nonneg h1] at h)
    · have := hf (rotPi y) (FrontPt_rotPi hy) (by
        simp only [rotPi]; simp; rw [abs_of_nonpos h1] at h; linarith)
      simpa [rotPi_rotPi] using Qp_rotPi this
  · rcases le_total 0 (y 0) with h1 | h1
    · have := hf (σ y) (FrontPt_σ hy) (by
        simp only [σ]; simp; rw [abs_of_nonneg h1] at h; linarith)
      simpa [σ_σ] using Qp_σ this
    · have := hf (rotPi (σ y)) (FrontPt_rotPi (FrontPt_σ hy)) (by
        simp only [rotPi, σ]; simp; rw [abs_of_nonpos h1] at h; linarith)
      simpa [rotPi_rotPi, σ_σ] using Qp_σ (Qp_rotPi this)

theorem cos_two_arctan (t : ℝ) : cos (2 * arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [cos_two_mul, cos_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  rw [div_pow, one_pow, sq_sqrt h.le]
  field_simp
  ring

theorem sin_two_arctan (t : ℝ) : sin (2 * arctan t) = 2 * t / (1 + t ^ 2) := by
  rw [sin_two_mul, cos_arctan, sin_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  have hs : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2) = 1 + t ^ 2 := mul_self_sqrt h.le
  calc 2 * (t / sqrt (1 + t ^ 2)) * (1 / sqrt (1 + t ^ 2))
      = 2 * t / (sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2)) := by ring
    _ = _ := by rw [hs]

/-- Polar form of a point of the fundamental piece. -/
theorem fund_polar {y : Space} (hr : 0 < r2 y) (hy : |y 0| ≤ y 1) :
    ∃ φ ∈ Icc (phiM 1696) (phiM 9889), y = polarPt (sqrt (r2 y)) (y 2) φ := by
  set ρ := sqrt (r2 y)
  have hρ2 : ρ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by rw [sq_sqrt hr.le]; rfl
  have hρ0 : 0 ≤ ρ := sqrt_nonneg _
  have hy0 := abs_le.mp (le_refl |y 0|)
  have hab := abs_le.mp hy
  have hy1 : 0 < y 1 := by
    by_contra hn
    have h1 : y 1 ≤ 0 := not_lt.mp hn
    have ha := abs_nonneg (y 0)
    have h1' : y 1 = 0 := by linarith
    have h0 : y 0 = 0 := abs_eq_zero.mp (by linarith)
    have : r2 y = 0 := by simp only [r2]; rw [h0, h1']; ring
    linarith
  have hpos : 0 < ρ + y 0 := by
    have : y 0 ^ 2 < ρ ^ 2 := by rw [hρ2]; nlinarith
    nlinarith [abs_lt_of_sq_lt_sq' this hρ0]
  set t := y 1 / (ρ + y 0)
  refine ⟨2 * arctan t, ⟨?_, ?_⟩, ?_⟩
  · unfold phiM
    have : (1696 : ℝ) / 4096 ≤ t := by
      rw [div_le_div_iff₀ (by norm_num) hpos]
      have hρle : ρ ≤ 2400 / 1696 * y 1 := by
        apply le_of_sq_le_sq _ (by positivity)
        rw [hρ2]; nlinarith
      nlinarith
    have := arctan_strictMono.monotone this
    push_cast; linarith
  · unfold phiM
    have : t ≤ (9889 : ℝ) / 4096 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      have hρge : 4096 / 9889 * y 1 - y 0 ≤ ρ := by
        rcases le_total (4096 / 9889 * y 1 - y 0) 0 with h | h
        · linarith
        · apply le_of_sq_le_sq _ hρ0
          rw [hρ2]; nlinarith
      nlinarith
    have := arctan_strictMono.monotone this
    push_cast; linarith
  · have hρpos : 0 < ρ := by nlinarith
    have hden : 0 < 1 + t ^ 2 := by positivity
    have hc : ρ * cos (2 * arctan t) = y 0 := by
      rw [cos_two_arctan]
      simp only [t]
      field_simp
      nlinarith [hρ2]
    have hs : ρ * sin (2 * arctan t) = y 1 := by
      rw [sin_two_arctan]
      simp only [t]
      field_simp
      nlinarith [hρ2]
    ext k; fin_cases k
    · simp [polarPt, hc]
    · simp [polarPt, hs]
    · simp [polarPt]

theorem sqrt_sq_eq' {c x : ℝ} (hc : 0 ≤ c) (h : x = c ^ 2) : sqrt x = c := by
  rw [h, sqrt_sq hc]

/-- **The fundamental piece.** -/
theorem fund_Q {y : Space} (hy : FrontPt y) (hf : |y 0| ≤ y 1) : Qp y := by
  obtain ⟨⟨hs, hz⟩, hface⟩ := hy
  have hr : 0 < r2 y := Ka_sub_domain (a := aF) (by norm_num [aF]) ⟨hs, hz⟩
  obtain ⟨φ, hφ, hyp⟩ := fund_polar hr hf
  have hsc : sc y = (r2 y - 1) / 2 := rfl
  have toQ : ∀ (F : Face) (w : ℝ), FaceGood fils F (phiM 1696) (phiM 9889) →
      inFace F.kind w → y = faceSigma F.kind φ w → Qp y := by
    intro F w hF hw he
    obtain ⟨h1, h2⟩ := hF φ hφ w hw
    rw [← he] at h1 h2
    refine ⟨h1, fun x ⟨z, hz, t, ht, hx⟩ => ?_⟩
    rw [hx]; exact h2 z hz t ht
  have hsq : ∀ c : ℝ, 0 ≤ c → r2 y = c ^ 2 → sqrt (r2 y) = c := fun c hc h => sqrt_sq_eq' hc h
  rcases hface with h | h
  · rcases abs_eq (by norm_num [aF] : (0 : ℝ) ≤ aF) |>.mp h with h' | h'
    · -- the outer cylinder
      have hρ : sqrt (r2 y) = 199 / 181 := hsq _ (by norm_num) (by
        rw [hsc, aF] at h'; linarith)
      refine toQ face0 (y 2) cover0 (by change |y 2| ≤ aF; exact hz) ?_
      conv_lhs => rw [hyp, hρ]
      simp [faceSigma, show face0.kind = 0 from rfl, cylR]
    · have hρ : sqrt (r2 y) = 161 / 181 := hsq _ (by norm_num) (by
        rw [hsc, aF] at h'; linarith)
      refine toQ face1 (y 2) cover1 (by change |y 2| ≤ aF; exact hz) ?_
      conv_lhs => rw [hyp, hρ]
      simp [faceSigma, show face1.kind = 1 from rfl, cylR]
  · have hρb : 161 / 181 ≤ sqrt (r2 y) ∧ sqrt (r2 y) ≤ 199 / 181 := by
      have := abs_le.mp hs
      rw [hsc, aF] at this
      constructor
      · rw [le_sqrt (by norm_num) hr.le]; linarith
      · rw [sqrt_le_left (by norm_num)]; linarith
    rcases abs_eq (by norm_num [aF] : (0 : ℝ) ≤ aF) |>.mp h with h' | h'
    · refine toQ face2 (sqrt (r2 y)) cover2 ?_ ?_
      · change if face2.kind < 2 then _ else _
        simp only [show face2.kind = 2 from rfl]; norm_num; exact hρb
      · conv_lhs => rw [hyp]
        simp [faceSigma, show face2.kind = 2 from rfl, planeZ, h']
    · refine toQ face3 (sqrt (r2 y)) cover3 ?_ ?_
      · change if face3.kind < 2 then _ else _
        simp only [show face3.kind = 3 from rfl]; norm_num; exact hρb
      · conv_lhs => rw [hyp]
        simp [faceSigma, show face3.kind = 3 from rfl, planeZ, h']

/-- **The frontier bound.** At every point of the four faces of `Ωa aF`,
`‖Bseg fils - hel‖ ≤ etaFp·2⁻⁴⁰ ≤ 6.5 × 10⁻⁴` and every point of the coil is at distance
`≥ 1/5`. -/
theorem frontier_Q {y : Space} (hy : FrontPt y) : Qp y :=
  reduce_fund (fun _ hy hf => fund_Q hy hf) hy

end PlasmaLean.Design.PolygonCoil
