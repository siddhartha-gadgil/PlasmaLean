/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusOutL
public import PlasmaLean.Design.RationalStellaratorGCTorusMaj
public import PlasmaLean.Design.KamTorusAExact
public import PlasmaLean.Certificates.KernelFact

/-!
# Admissibility of the Newton step near a reference torus (guiding-centre field)

The bounds `AdmBounds` of the Newton step (`Design/KamFlowIterationS`) for the guiding-centre
field `gcFlow (1/256)` at every analytic torus `(u, z)` that is `μ`-close (`Close`) to a reference
torus `(u₀, z₀)` lying within the given distances of the low-resolution torus `K_S`
(`gc_adm_near`): the inputs of the low-resolution ball chain (`inputs_L`), the field bounds and
`u`, `z`-derivatives (`Design/RationalStellaratorGCTorusOutL`), the inverses of `D̃`, `R`, `W₀`
(Neumann series around the means `d₀ ≈ 0.9443`, `w₀ ≈ −0.009364`), the torsion
`T₀ = Y (1 + X)⁻¹` with `Y = R³ P̃ q`, `X = q D̃³ W₀² − 1` (`‖X‖ ≤ 5.02 × 10⁻⁸`,
`‖Y‖ ≤ 37.111`, `⟨Y⟩ ≈ 0.44163`), and the strip validity of the field.

**Sanity.** `d0G_bounds`: `0.944 ≤ d₀ ≤ 0.945`; `cGC_au`: the torus bound is `‖u₀‖ + μ`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-! ## The constants -/

/-- The displacement budget `μ = 10⁻¹²`. -/
def μG : ℝ := 1 / 10 ^ 12
/-- The initial error `e₀ = 3.7 × 10⁻²³`. -/
def e0G : ℝ := 37 / 10 ^ 24
/-- The initial loss `δ₀ = r_A/7`. -/
def δ0G : ℝ := KamTorusA.rA / 7
/-- `‖u‖`. -/
def auG : ℝ := 1929 / 10000 + μG
/-- `‖z‖`. -/
def azG : ℝ := 811 / 5000 + μG
/-- `‖∂_θ u‖`. -/
def aRtG : ℝ := 817 / 5000 + μG
/-- `‖∂_θ z‖`. -/
def aztG : ℝ := 101 / 625 + μG
/-- `‖𝓛 u‖`. -/
def aLRG : ℝ := 1093 / 10000 + μG
/-- `‖𝓛 z‖`. -/
def aLzG : ℝ := 1037 / 10000 + μG
/-- `e^{r_A} ≤ acG`. -/
def acG : ℝ := 74315 / 2 ^ 16
/-- `‖D̃⁻¹‖`. -/
def sDG : ℝ := 16283 / 10000
/-- `‖R⁻¹‖`. -/
def sRG : ℝ := 1 / (1 - auG)
/-- `‖W₀⁻¹‖`. -/
def sWG : ℝ := 17151 / 100
/-- The torsion bound. -/
def tTG : ℝ := 37111 / 1000
/-- The twist bound. -/
def τG : ℝ := 441 / 1000

/-- **The step constants for the guiding-centre torus.** -/
def cGC : SC where
  ρ := KamTorusA.rA
  δ0 := δ0G
  γ := 687 / 10000
  θ := e0G / δ0G ^ 4
  au := auG
  az := azG
  aRt := aRtG
  azt := aztG
  aLR := aLRG
  aLz := aLzG
  ac := acG
  bD := 12751 / 10000
  bDu := 22351 / 10000
  bDz := 20221 / 100000
  bnR := 10061 / 100000
  bnRu := 94501 / 100000
  bnRz := 74441 / 100000
  bnZ := 10451 / 100000
  bnZu := 86841 / 100000
  bnZz := 81671 / 100000
  sD := sDG
  sR := sRG
  sW := sWG
  tT := tTG
  τ := τG
  C2 := (C2Q : ℝ)
  E1 := 2718 / 1000
  cKb := 5310
  cLb := 18200

/-- **Sanity**: the torus bound of `cGC` is `‖u₀‖ + μ`. -/
theorem cGC_au : cGC.au = 1929 / 10000 + 1 / 10 ^ 12 := rfl

/-- The mean of `D̃` on the low-resolution torus. -/
def d0G : ℝ := 2126414735707981 / 2 ^ 51

/-- The mean of `W₀` on the low-resolution torus. -/
def w0G : ℝ := -(5398240620830529 / 2 ^ 59)

/-- **Sanity**: `0.944 ≤ d₀ ≤ 0.945`. -/
theorem d0G_bounds : 944 / 1000 ≤ d0G ∧ d0G ≤ 945 / 1000 := by norm_num [d0G]

/-- The inputs of the low-resolution chain from `μ`-closeness to a reference torus at the given
distances from the low-resolution torus. -/
theorem inputs_L {ρ : ℝ} (hρA : ρ ≤ KamTorusA.rA) {ι μ : ℝ} {u z u₀ z₀ : FA}
    (hC : Close ρ ι u z u₀ z₀ μ) {du dz da db : ℝ}
    (h1 : Bd KamTorusA.rA (u₀ - xL 4) du) (h2 : Bd KamTorusA.rA (z₀ - xL 5) dz)
    (h3 : Bd KamTorusA.rA (dTh u₀ - dTh (xL 4)) da) (h4 : Bd KamTorusA.rA (dTh z₀ - dTh (xL 5)) db)
    (e1 : μ + du ≤ EL 4) (e2 : μ + dz ≤ EL 5) (e3 : μ + da ≤ EL 6) (e4 : μ + db ≤ EL 7) :
    Bd ρ (u - xL 4) (EL 4) ∧ Bd ρ (z - xL 5) (EL 5) ∧ Bd ρ (dTh u - xL 6) (EL 6) ∧
      Bd ρ (dTh z - xL 7) (EL 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hC.du.add (h1.strip hρA)
    rw [sub_add_sub_cancel] at this; exact this.le e1
  · have := hC.dz.add (h2.strip hρA)
    rw [sub_add_sub_cancel] at this; exact this.le e2
  · have := hC.dut.add (h3.strip hρA)
    rw [sub_add_sub_cancel, ← dTh_xL_A] at this; exact this.le e3
  · have := hC.dzt.add (h4.strip hρA)
    rw [sub_add_sub_cancel, ← dTh_xL_B] at this; exact this.le e4

/-- A kernel-checked rational inequality, cast to `ℝ`. -/
theorem qle {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

section Field

variable {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {u z : FA}
  (hU : Bd r (u - xL 4) (EL 4)) (hZ : Bd r (z - xL 5) (EL 5))
  (hA : Bd r (dTh u - xL 6) (EL 6)) (hB : Bd r (dTh z - xL 7) (EL 7))
include hr hq hU hZ hA hB

/-- `‖D̃ − d₀‖ ≤ 0.3302`. -/
theorem Bd_Ddev : Bd r ((gcFlow (1 / 256)).Dof u z - algebraMap ℂ FA (d0G : ℂ))
    (743500000000000 / 2 ^ 51) := by
  have h := normL_Ddev hr hq hU hZ hA hB
  have hk : algebraMap ℂ FA ((2 : ℂ) ^ 51 * ((d0G : ℝ) : ℂ)) = (2126414735707981 : FA) := by
    rw [show ((2 : ℂ) ^ 51 * ((d0G : ℝ) : ℂ)) = (2126414735707981 : ℂ) by
      simp only [d0G]; push_cast; ring]
    exact map_ofNat _ _
  have e : Ex.eval (XL u z) trL_Ddev =
      (2 ^ 51 : ℂ) • ((gcFlow (1 / 256)).Dof u z - algebraMap ℂ FA (d0G : ℂ)) := by
    simp only [trL_Ddev, Ex.eval, XL, FlowFieldS.Dof, gcFlow, KL, Int.cast_ofNat]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, ← map_mul, hk, map_pow, map_ofNat]
    norm_num
  rw [e] at h
  have h2 := h.smul ((2 ^ 51 : ℂ))⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at h2
  refine h2.le (le_of_eq ?_)
  rw [norm_inv, norm_pow, Complex.norm_ofNat]; push_cast; ring

/-- `‖W₀ − w₀‖ ≤ 0.003533`. -/
theorem Bd_Wdev : Bd r (W0of u z - algebraMap ℂ FA (w0G : ℂ)) (2037000000000000 / 2 ^ 59) := by
  have h := normL_Wdev hr hq hU hZ hA hB
  have hk : algebraMap ℂ FA ((2 : ℂ) ^ 59 * ((w0G : ℝ) : ℂ)) = -(5398240620830529 : FA) := by
    rw [show ((2 : ℂ) ^ 59 * ((w0G : ℝ) : ℂ)) = -(5398240620830529 : ℂ) by
      simp only [w0G]; push_cast; ring]
    rw [map_neg, map_ofNat]
  have e : Ex.eval (XL u z) trL_Wdev = (2 ^ 59 : ℂ) • (W0of u z - algebraMap ℂ FA (w0G : ℂ)) := by
    simp only [trL_Wdev, Ex.eval, XL, Int.cast_ofNat]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, ← map_mul, hk, map_pow, map_ofNat]
    norm_num
    ring
  rw [e] at h
  have h2 := h.smul ((2 ^ 59 : ℂ))⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at h2
  refine h2.le (le_of_eq ?_)
  rw [norm_inv, norm_pow, Complex.norm_ofNat]; push_cast; ring

/-- `‖q D̃³ W₀² − 1‖ ≤ 5.02 × 10⁻⁸`. -/
theorem Bd_Xtor : Bd r (xL 112 * (PolyExprS.eval (xB u z) (gcD (1 / 256)) ^ 3 * W0of u z ^ 2) -
    1) (251 / 5000000000) := by
  have h := normL_X hr hq hU hZ hA hB
  have e : Ex.eval (XL u z) trL_X =
      xL 112 * (PolyExprS.eval (xB u z) (gcD (1 / 256)) ^ 3 * W0of u z ^ 2) - 1 := by
    simp only [trL_X, Ex.eval, XL, KL]; ring
  rw [e] at h
  refine h.le (le_of_eq ?_); push_cast; ring

end Field

/-- The average of the torsion centre `Y`. -/
theorem avg_xL_Y : avg (xL 113) = ((509165810821300134 / 2 ^ 60 : ℝ) : ℂ) := by
  have hg : gL 113 16 12 = 509165810821300134 := by kernel_fact
  change coeff (ctr SL NL ML (1, 0, 0) (gridPolyNM NL ML (gL 113))) (0, 0) = _
  rw [coeff_ctr_grid]
  simp only [abs_zero, Nat.cast_nonneg, and_self, ↓reduceIte, zero_add, Int.toNat_natCast,
    pow_zero, mul_one, NL, ML, SL]
  rw [show gL 113 16 12 = 509165810821300134 from hg]
  push_cast
  ring

section Adm

variable {r : ℝ} (hr0 : 0 < r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {u z : FA}
  (hU : Bd r (u - xL 4) (EL 4)) (hZ : Bd r (z - xL 5) (EL 5))
  (hA : Bd r (dTh u - xL 6) (EL 6)) (hB : Bd r (dTh z - xL 7) (EL 7))
include hr0 hq hU hZ hA hB

/-- **`D̃` is invertible**, `‖D̃⁻¹‖ ≤ 1.6283`. -/
theorem adm_Di_gc : IsUnit ((gcFlow (1 / 256)).Dof u z) ∧
    Bd r (Ring.inverse ((gcFlow (1 / 256)).Dof u z)) sDG := by
  have h := Bd_Ddev hr0.le hq hU hZ hA hB
  have hn : ‖((d0G : ℝ) : ℂ)‖ = d0G := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num [d0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [d0G])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [d0G, sDG])⟩

/-- **`W₀` is invertible**, `‖W₀⁻¹‖ ≤ 171.51`. -/
theorem adm_Wi_gc : IsUnit (W0of u z) ∧ Bd r (Ring.inverse (W0of u z)) sWG := by
  have h := Bd_Wdev hr0.le hq hU hZ hA hB
  have hn : ‖((w0G : ℝ) : ℂ)‖ = -w0G := by
    rw [Complex.norm_real, Real.norm_of_nonpos (by norm_num [w0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [w0G])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [w0G, sWG])⟩

/-- **Torsion and twist**: `‖T₀‖ ≤ 37.111`, `|⟨T₀⟩| ≥ 0.441`. -/
theorem adm_T_gc : Bd r ((gcFlow (1 / 256)).Talg u z) tTG ∧
    τG ≤ ‖avg ((gcFlow (1 / 256)).Talg u z)‖ := by
  have hr := hr0.le
  set F := (gcFlow (1 / 256)).Dof u z ^ 3 * W0of u z ^ 2 with hF
  set q := xL 112 with hq_def
  have hX : Bd r (q * F - algebraMap ℂ FA 1) ((251 / 5000000000 : ℚ) : ℝ) := by
    rw [map_one]
    have := Bd_Xtor hr hq hU hZ hA hB
    refine this.le (le_of_eq ?_); push_cast; ring
  obtain ⟨hUq, hInv⟩ := Bd.inverse hr hX (by rw [norm_one]; norm_num)
  rw [norm_one] at hInv
  have hY := valL_le hr hq hU hZ hA hB 113 (by norm_num)
  have hYc := (ballL_all hr hq hU hZ hA hB) 113 (by norm_num)
  have hXe : Bd r (q * F - 1) ((251 / 5000000000 : ℚ) : ℝ) := by rwa [map_one] at hX
  set Y := XL u z 113 with hY_def
  obtain ⟨hDu, -⟩ := adm_Di_gc hr0 hq hU hZ hA hB
  obtain ⟨hWu, -⟩ := adm_Wi_gc hr0 hq hU hZ hA hB
  have hYe : Y = (1 + u) ^ 3 * (gcFlow (1 / 256)).Pof u z * q := rfl
  have hrep : (gcFlow (1 / 256)).Talg u z = Y * Ring.inverse (q * F) := by
    refine ext_eval fun θ ψ => ?_
    have hD := eval_ne_zero_of_unit hDu θ ψ
    have hW := eval_ne_zero_of_unit hWu θ ψ
    have hQ := eval_ne_zero_of_unit hUq θ ψ
    rw [eval_mul, eval_inverse hUq, hYe]
    rw [hF] at hQ ⊢
    simp only [FlowFieldS.Talg, FlowFieldS.Di, Wi, eval_mul, eval_pow', eval_inverse hDu,
      eval_inverse hWu, eval_add', eval_one] at hQ ⊢
    have hq0 : eval q θ ψ ≠ 0 := left_ne_zero_of_mul hQ
    field_simp
  have hX1 : (0 : ℝ) < 1 - ((251 / 5000000000 : ℚ) : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [hrep]
    refine (hY.mul hr hInv).le ?_
    have h1 := qle (show BL 113 + EL 113 ≤ 371101 / 10000 by kernel_fact)
    push_cast at h1 ⊢
    rw [tTG]
    calc ((BL 113 : ℝ) + EL 113) * (1 / (1 - 251 / 5000000000)) ≤
        (371101 / 10000) * (1 / (1 - 251 / 5000000000)) := by gcongr
      _ ≤ 37111 / 1000 := by norm_num
  · have hI : Ring.inverse (q * F) = 1 - (q * F - 1) * Ring.inverse (q * F) := by
      have := Ring.mul_inverse_cancel _ hUq
      linear_combination this
    have e : (gcFlow (1 / 256)).Talg u z = Y - Y * (q * F - 1) * Ring.inverse (q * F) := by
      rw [hrep]; nth_rewrite 1 [hI]; ring
    rw [e, avg_sub]
    have h1 : ‖avg (Y * (q * F - 1) * Ring.inverse (q * F))‖ ≤
        ((BL 113 + EL 113 : ℚ) : ℝ) * ((251 / 5000000000 : ℚ) : ℝ) *
          (1 / (1 - ((251 / 5000000000 : ℚ) : ℝ))) :=
      ((hY.mul hr hXe).mul hr hInv).norm_avg_le hr
    have h2 : ‖avg (Y - xL 113)‖ ≤ ((EL 113 : ℚ) : ℝ) := hYc.norm_avg_le hr
    rw [avg_sub, avg_xL_Y] at h2
    have h3 : (509165810821300134 / 2 ^ 60 : ℝ) - ((EL 113 : ℚ) : ℝ) ≤ ‖avg Y‖ := by
      have := norm_sub_norm_le (((509165810821300134 / 2 ^ 60 : ℝ) : ℂ))
        (((509165810821300134 / 2 ^ 60 : ℝ) : ℂ) - avg Y)
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
        norm_sub_rev] at this
      linarith
    have h5 := norm_sub_norm_le (avg Y) (avg (Y * (q * F - 1) * Ring.inverse (q * F)))
    have hB1 := qle (show BL 113 + EL 113 ≤ 371101 / 10000 by kernel_fact)
    have hE1 := qle (show EL 113 ≤ 1 / 10 ^ 4 by kernel_fact)
    push_cast at h1 hB1 hE1 h3
    have h6 : ((BL 113 : ℝ) + EL 113) * (251 / 5000000000) * (1 / (1 - 251 / 5000000000)) ≤
        (371101 / 10000) * (251 / 5000000000) * (1 / (1 - 251 / 5000000000)) := by gcongr
    rw [τG]
    norm_num at h6 h3 ⊢
    linarith

end Adm

/-- The bounds `(‖u‖, ‖z‖, ‖cos 2φ‖, ‖sin 2φ‖, 0, 0)` of the torus variables. -/
def avG : Fin 6 → ℝ := ![auG, azG, acG, acG, 0, 0]

/-- The torus variable bounds are below the validity bounds `aTQ`. -/
theorem avG_le : (∀ i, 0 ≤ avG i) ∧ ∀ i, avG i ≤ (aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    norm_num [avG, aTQ, auG, azG, acG, μG]

/-- **Admissibility near a reference torus.** Every analytic torus `μ`-close to a reference torus
`(u₀, z₀)` (with the torus bounds of `K₀` and at the given distances from the low-resolution
torus) satisfies the bounds of the Newton step with the constants `cGC`, on every strip
`0 < ρ ≤ r_A`. -/
theorem gc_adm_near {ρ : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ KamTorusA.rA) {u z u₀ z₀ : FA}
    (hu : Ana u) (hz : Ana z) (hC : Close ρ KamTorusA.iota u z u₀ z₀ μG)
    (b1 : Bd KamTorusA.rA u₀ (1929 / 10000)) (b2 : Bd KamTorusA.rA z₀ (811 / 5000))
    (b3 : Bd KamTorusA.rA (dTh u₀) (817 / 5000)) (b4 : Bd KamTorusA.rA (dTh z₀) (101 / 625))
    (b5 : Bd KamTorusA.rA (Lt KamTorusA.iota u₀) (1093 / 10000))
    (b6 : Bd KamTorusA.rA (Lt KamTorusA.iota z₀) (1037 / 10000))
    (h1 : Bd KamTorusA.rA (u₀ - xL 4) ((3179 / 10 ^ 18 : ℚ) : ℝ))
    (h2 : Bd KamTorusA.rA (z₀ - xL 5) ((3068 / 10 ^ 18 : ℚ) : ℝ))
    (h3 : Bd KamTorusA.rA (dTh u₀ - dTh (xL 4)) ((2346 / 10 ^ 17 : ℚ) : ℝ))
    (h4 : Bd KamTorusA.rA (dTh z₀ - dTh (xL 5)) ((2451 / 10 ^ 17 : ℚ) : ℝ)) :
    (gcFlow (1 / 256)).AdmBounds cGC KamTorusA.iota ρ u z := by
  have hq : Real.exp ρ ≤ (74315 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hρA).trans exp_rA_le'
  have e1 := qle (show (1 / 10 ^ 12 + 3179 / 10 ^ 18 : ℚ) ≤ EL 4 by kernel_fact)
  have e2 := qle (show (1 / 10 ^ 12 + 3068 / 10 ^ 18 : ℚ) ≤ EL 5 by kernel_fact)
  have e3 := qle (show (1 / 10 ^ 12 + 2346 / 10 ^ 17 : ℚ) ≤ EL 6 by kernel_fact)
  have e4 := qle (show (1 / 10 ^ 12 + 2451 / 10 ^ 17 : ℚ) ≤ EL 7 by kernel_fact)
  push_cast at e1 e2 e3 e4
  obtain ⟨hU, hZ, hA, hB⟩ := inputs_L hρA hC h1 h2 h3 h4
    (by rw [μG]; push_cast; linarith) (by rw [μG]; push_cast; linarith)
    (by rw [μG]; push_cast; linarith) (by rw [μG]; push_cast; linarith)
  have hρ0 := hρ.le
  -- the torus
  have tu : Bd ρ u auG := by
    have := hC.du.add (b1.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [auG]; linarith)
  have tz : Bd ρ z azG := by
    have := hC.dz.add (b2.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [azG]; linarith)
  have tRt : Bd ρ (dTh u) aRtG := by
    have := hC.dut.add (b3.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aRtG]; linarith)
  have tzt : Bd ρ (dTh z) aztG := by
    have := hC.dzt.add (b4.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aztG]; linarith)
  have tLR : Bd ρ (Lt KamTorusA.iota u) aLRG := by
    have := hC.duL.add (b5.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLRG]; linarith)
  have tLz : Bd ρ (Lt KamTorusA.iota z) aLzG := by
    have := hC.dzL.add (b6.strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLzG]; linarith)
  -- the inverses
  obtain ⟨hDu, hDb⟩ := adm_Di_gc hρ hq hU hZ hA hB
  obtain ⟨hWu, hWb⟩ := adm_Wi_gc hρ hq hU hZ hA hB
  have hR1 : Bd ρ ((1 + u) - algebraMap ℂ FA 1) auG := by
    rw [map_one, add_sub_cancel_left]; exact tu
  obtain ⟨hRu, hRb⟩ := Bd.inverse hρ0 hR1 (by rw [norm_one]; norm_num [auG, μG])
  rw [norm_one] at hRb
  obtain ⟨hT, hτ⟩ := adm_T_gc hρ hq hU hZ hA hB
  -- strip validity
  have hgood : (gcFlow (1 / 256)).Good u z := by
    refine ⟨ρ, hρ, avG, fun i => ?_, (gcFlow_valid _ avG (gc_maj_E_lt avG_le.1 avG_le.2)).1⟩
    have hc : Real.exp ρ ≤ acG := by
      have := hq; push_cast at this; rw [acG]; linarith
    fin_cases i
    · exact tu
    · exact tz
    · exact (Bd_cS ρ).le hc
    · exact (Bd_sS ρ).le hc
    · exact Bd_zero ρ
    · exact Bd_zero ρ
  have fb : ∀ {X : FA} {i : ℕ} {c : ℚ}, Bd ρ X ((BL i + EL i : ℚ) : ℝ) → BL i + EL i ≤ c →
      Bd ρ X (c : ℝ) := fun h hc => h.le (qle hc)
  exact
  { frame := ⟨hu, hz, hDu, hRu, hWu, ⟨ρ, _, hρ, hDb⟩, ⟨ρ, _, hρ, hRb⟩, ⟨ρ, _, hρ, hWb⟩, hgood⟩
    hu := tu
    hz := tz
    hRt := tRt
    hzt := tzt
    hLR := tLR
    hLz := tLz
    hbD := by
      have := fb (gcL_Dt hρ0 hq hU hZ hA hB) (c := 12751 / 10000) (by kernel_fact)
      push_cast at this; exact this
    hbDu := by
      have := fb (gcL_Dtu hρ0 hq hU hZ hA hB) (c := 22351 / 10000) (by kernel_fact)
      push_cast at this; exact this
    hbDz := by
      have := fb (gcL_Dtz hρ0 hq hU hZ hA hB) (c := 20221 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnR := by
      have := fb (gcL_nRt hρ0 hq hU hZ hA hB) (c := 10061 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnRu := by
      have := fb (gcL_nRtu hρ0 hq hU hZ hA hB) (c := 94501 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnRz := by
      have := fb (gcL_nRtz hρ0 hq hU hZ hA hB) (c := 74441 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZ := by
      have := fb (gcL_nZt hρ0 hq hU hZ hA hB) (c := 10451 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZu := by
      have := fb (gcL_nZtu hρ0 hq hU hZ hA hB) (c := 86841 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hbnZz := by
      have := fb (gcL_nZtz hρ0 hq hU hZ hA hB) (c := 81671 / 100000) (by kernel_fact)
      push_cast at this; exact this
    hsD := hDb
    hsR := hRb
    hsW := hWb
    hT := hT
    hτ := hτ }

end PlasmaLean.Design.RationalStellaratorGC
