/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamTorus

/-!
# The sampled flow-form residual at one grid point

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). `pointAP` is the integer
checker for one grid point `(θ_j, φ_l) = (2πj/N₁, 2πl/L)`:

1. approximants of `R, z, 𝓛R, 𝓛z` (`torusAP`, from the exponential table);
2. the dyadic point `ỹ` nearest to `(R cos φ_l, R sin φ_l, z)` with its distance bound `e_y`
   (checked `e_y ≤ d_N`) and the tube check `ỹ ∈ realTube (w_N/D)` (`tubeOK`);
3. the coil field at `ỹ` (`fieldAP`), widened by `Lip · e_y` (Lipschitz transfer to the true
   torus point; the Lipschitz bound is a hypothesis, proved in `Design/CoilKamLip`);
4. the residuals `E_R = B^φ 𝓛R − R B^R`, `E_z = B^φ 𝓛z − R B^z`.

`pointAP_sound`: if `pointAP … j l = some (s₁, s₂)` then `|E_R(θ_j, φ_l)| ≤ s₁/D` and
`|E_z(θ_j, φ_l)| ≤ s₂/D`.

**Sanity.** `tubeOK_fixture` (the point `(1, 0, 0)` passes), `not_tubeOK_fixture` (the origin
fails).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open PlasmaLean.Fields PlasmaLean.Design.CoilFieldComplex PlasmaLean.Theory.KAM.FourierSumHolo

/-- Boolean `≤` on integers. -/
def ileB (a b : ℤ) : Bool := decide (a ≤ b)

/-- The tube check `(D - w)² ≤ Y₀² + Y₁² ≤ (D + w)²`, `|Y₂| ≤ w`, `w < D`. -/
def tubeOK (D wN : ℕ) (Y0 Y1 Y2 : ℤ) : Bool :=
  Nat.blt wN D && ileB (((D : ℤ) - wN) ^ 2) (Y0 ^ 2 + Y1 ^ 2) &&
    ileB (Y0 ^ 2 + Y1 ^ 2) (((D : ℤ) + wN) ^ 2) && Nat.ble Y2.natAbs wN

theorem tubeOK_sound {D wN : ℕ} (hD : 0 < D) {Y0 Y1 Y2 : ℤ} (h : tubeOK D wN Y0 Y1 Y2 = true) :
    ptD D (Y0, Y1, Y2) ∈ realTube ((wN : ℝ) / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  simp only [tubeOK, ileB, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨hw, h1⟩, h2⟩, h3⟩ := h
  obtain ⟨p0, p1, p2⟩ := ptD_apply D (Y0, Y1, Y2)
  refine ⟨?_, ?_⟩
  · rw [p0, p1]
    simp only
    have e : ((Y0 : ℝ) / D) ^ 2 + ((Y1 : ℝ) / D) ^ 2 = ((Y0 : ℝ) ^ 2 + Y1 ^ 2) / D ^ 2 := by
      field_simp
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hD'.le]
    have h1' : ((D : ℝ) - wN) ^ 2 ≤ (Y0 : ℝ) ^ 2 + Y1 ^ 2 := by exact_mod_cast h1
    have h2' : (Y0 : ℝ) ^ 2 + Y1 ^ 2 ≤ ((D : ℝ) + wN) ^ 2 := by exact_mod_cast h2
    have hw' : (wN : ℝ) < D := by exact_mod_cast hw
    have l1 : (D : ℝ) - wN ≤ Real.sqrt ((Y0 : ℝ) ^ 2 + Y1 ^ 2) :=
      Real.le_sqrt_of_sq_le h1'
    have l2 : Real.sqrt ((Y0 : ℝ) ^ 2 + Y1 ^ 2) ≤ D + wN :=
      Real.sqrt_le_iff.2 ⟨by positivity, h2'⟩
    have e2 : Real.sqrt ((Y0 : ℝ) ^ 2 + Y1 ^ 2) / D - 1 =
        (Real.sqrt ((Y0 : ℝ) ^ 2 + Y1 ^ 2) - D) / D := by field_simp
    rw [e2, abs_div, Nat.abs_cast]
    refine div_le_div_of_nonneg_right ?_ hD'.le
    rw [abs_le]; constructor <;> linarith
  · rw [p2]; simp only
    rw [abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (by rw [← natAbs_cast]; exact_mod_cast h3) hD'.le

/-- Widen the error of an approximant. -/
def apWiden (p : ℤ × ℕ) (e : ℕ) : ℤ × ℕ := (p.1, p.2 + e)

/-- **The grid-point checker**: bounds `(s₁, s₂)` (scale `D = 2³² D₀`) of the two residuals at
`(2πj/N₁, 2πl/L)`, or `none`. -/
def pointAP (D₀ L q E : ℕ) (Iq : ℤ) (tbl : List (ℤ × ℤ)) (recs : List TRec) (wN dN Lip : ℕ)
    (j l : ℕ) : Option (ℕ × ℕ) :=
  let D := 4294967296 * D₀
  let T := torusAP D L q E Iq tbl recs j l
  let cs := tget tbl (((l : ℤ) % L).toNat)
  let cφ : ℤ × ℕ := (cs.1, E)
  let sφ : ℤ × ℕ := (cs.2, E)
  let Y0 := apMul D T.1 cφ
  let Y1 := apMul D T.1 sφ
  let eY := Y0.2 + Y1.2 + T.2.1.2
  match tubeOK D wN Y0.1 Y1.1 T.2.1.1 && Nat.ble eY dN with
  | false => none
  | true =>
    match fieldAP D₀ (Y0.1, Y1.1, T.2.1.1) with
    | none => none
    | some B =>
      let B0 := apWiden B.1 (Lip * eY)
      let B1 := apWiden B.2.1 (Lip * eY)
      let B2 := apWiden B.2.2 (Lip * eY)
      let Bφ := apAdd (apNeg (apMul D sφ B0)) (apMul D cφ B1)
      let BR := apAdd (apMul D cφ B0) (apMul D sφ B1)
      some (apAbs (apSub (apMul D Bφ T.2.2.1) (apMul D T.1 BR)),
        apAbs (apSub (apMul D Bφ T.2.2.2) (apMul D T.1 B2)))

theorem Approx.widen {D : ℕ} {x y : ℝ} {p : ℤ × ℕ} {e : ℕ} (hx : Approx D x p)
    (hxy : |y - x| ≤ (e : ℝ) / D) : Approx D y (apWiden p e) := by
  unfold Approx at *
  simp only [apWiden, Nat.cast_add, add_div]
  calc |y - (p.1 : ℝ) / D| = |(y - x) + (x - (p.1 : ℝ) / D)| := by ring_nf
    _ ≤ |y - x| + |x - (p.1 : ℝ) / D| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Soundness of the grid-point checker.** -/
theorem pointAP_sound {D₀ L q N₁ E : ℕ} (hD₀ : 0 < D₀) (hL : 0 < L) (hq : N₁ * q = L)
    {tbl : List (ℤ × ℤ)}
    (htbl : ∀ t < L, ‖gexp L t - gauss (4294967296 * D₀) (tget tbl t)‖ ≤
      (E : ℝ) / (4294967296 * D₀ : ℕ))
    {ι : ℝ} {Iq : ℤ} (hι : Approx (4294967296 * D₀) ι (Iq, 1)) (recs : List TRec)
    {wN dN Lip : ℕ} (hw : (wN : ℝ) / (4294967296 * D₀ : ℕ) < 7 / 20)
    (hLip : ∀ y y' : Space, y' ∈ realTube ((wN : ℝ) / (4294967296 * D₀ : ℕ)) →
      ‖y - y'‖ ≤ (dN : ℝ) / (4294967296 * D₀ : ℕ) → ∀ i, |Bc y i - Bc y' i| ≤ Lip * ‖y - y'‖)
    {j l : ℕ} {s₁ s₂ : ℕ} (h : pointAP D₀ L q E Iq tbl recs wN dN Lip j l = some (s₁, s₂)) :
    |resR (4294967296 * D₀) ι recs (2 * Real.pi * j / N₁) (2 * Real.pi * l / L)| ≤
        (s₁ : ℝ) / (4294967296 * D₀ : ℕ) ∧
      |resZ (4294967296 * D₀) ι recs (2 * Real.pi * j / N₁) (2 * Real.pi * l / L)| ≤
        (s₂ : ℝ) / (4294967296 * D₀ : ℕ) := by
  set D := 4294967296 * D₀ with hDdef
  have hD : 0 < D := by positivity
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set θ := 2 * Real.pi * j / N₁
  set φ := 2 * Real.pi * l / L
  obtain ⟨hR, hZ, hLR, hLZ⟩ := torusAP_sound hD hL hq htbl hι recs j l
  obtain ⟨hc, hs⟩ := cos_sin_approx htbl hL (l : ℤ)
  have hφ : 2 * Real.pi * ((l : ℤ) : ℝ) / L = φ := by simp [φ]
  rw [hφ] at hc hs
  unfold pointAP at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  rename_i hchk
  simp only [Bool.and_eq_true, Nat.ble_eq] at hchk
  obtain ⟨htube, heY⟩ := hchk
  split at h
  · exact absurd h (by simp)
  rename_i B hB
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set T := torusAP D L q E Iq tbl recs j l
  set cs := tget tbl (((l : ℤ) % L).toNat)
  set Y0 := apMul D T.1 (cs.1, E)
  set Y1 := apMul D T.1 (cs.2, E)
  -- the torus point and its dyadic neighbour
  have hY0 : Approx D (Rr D recs θ φ * Real.cos φ) Y0 := hR.mul hD hc
  have hY1 : Approx D (Rr D recs θ φ * Real.sin φ) Y1 := hR.mul hD hs
  set yt := torusPt D recs θ φ
  set yd := ptD D (Y0.1, Y1.1, T.2.1.1)
  have hyt : yt 0 = Rr D recs θ φ * Real.cos φ ∧ yt 1 = Rr D recs θ φ * Real.sin φ ∧
      yt 2 = Zr D recs θ φ := by simp [yt, torusPt, cylR]
  obtain ⟨d0, d1, d2⟩ := ptD_apply D (Y0.1, Y1.1, T.2.1.1)
  have hdist : ‖yt - yd‖ ≤ ((Y0.2 + Y1.2 + T.2.1.2 : ℕ) : ℝ) / D := by
    refine (norm_le_sum_abs _).trans ?_
    simp only [PiLp.sub_apply, hyt.1, hyt.2.1, hyt.2.2]
    rw [show yd = ptD D (Y0.1, Y1.1, T.2.1.1) from rfl]
    rw [d0, d1, d2]
    push_cast
    rw [add_div, add_div]
    exact add_le_add (add_le_add hY0 hY1) hZ
  have hdN : ‖yt - yd‖ ≤ (dN : ℝ) / D :=
    hdist.trans (div_le_div_of_nonneg_right (by exact_mod_cast heY) hD'.le)
  have hyd : yd ∈ realTube ((wN : ℝ) / D) := tubeOK_sound hD htube
  -- the field at the dyadic point and at the torus point
  obtain ⟨b0, b1, b2⟩ := fieldAP_sound hD₀ hw hyd hB
  have hL' := hLip yt yd hyd hdN
  have widen : ∀ i : Fin 3, ∀ p : ℤ × ℕ, Approx D (Bc yd i) p →
      Approx D (Bc yt i) (apWiden p (Lip * (Y0.2 + Y1.2 + T.2.1.2))) := by
    intro i p hp
    refine hp.widen ((hL' i).trans ?_)
    rw [Nat.cast_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdist (by positivity)
  have B0 := widen 0 _ b0
  have B1 := widen 1 _ b1
  have B2 := widen 2 _ b2
  have hBφ := ((hs.mul hD B0).neg).add (hc.mul hD B1)
  have hBR := (hc.mul hD B0).add (hs.mul hD B1)
  have hE1 := (hBφ.mul hD hLR).sub (hR.mul hD hBR)
  have hE2 := (hBφ.mul hD hLZ).sub (hR.mul hD B2)
  constructor
  · have := hE1.abs_le hD
    convert this using 2
    unfold resR
    simp only [Bc] at *
    ring
  · have := hE2.abs_le hD
    convert this using 2
    unfold resZ
    simp only [Bc] at *
    ring

/-! ## Sanity -/

/-- Accepted fixture: `(1, 0, 0)` lies in the tube of half-width `1/4` (scale `4`). -/
theorem tubeOK_fixture : tubeOK 4 1 4 0 0 = true := by decide +kernel

/-- Rejected fixture: the origin does not. -/
theorem not_tubeOK_fixture : tubeOK 4 1 0 0 0 = false := by decide +kernel

end PlasmaLean.Design.CoilKam
