/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamRows
public import PlasmaLean.Design.CoilKamNum

/-!
# The coarse sampled residual certificate of a rational coil torus

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`): the full pipeline from the
rational torus `ckRecs` (`N = 8`, `M = 16`, 281 records at scale `2¹⁰⁰`, refitted to the coil
field `tfField + polyCoilFieldC` at `ι = ι_A`) to a **certified strip norm of its flow-form
residual** through `PaleyWiener.Bd_of_samples` (in the form `Bd_of_sample_sum`).

Ingredients, all checked here:

* `ck_hyp`: the exponential table (`expTableOK`, kernel) with its base entry from
  `sqrtTwoAddSeries` brackets (`ck_base`), and the enclosure of `ι_A` (`ck_iota`);
* `ck_grid`: the 512 kernel evaluations of `Design/CoilKamPts0`–`7` (rows in
  `Design/CoilKamRows`) give
  `Σ_{j<16} Σ_{l<32} |E_R(θ_j, φ_l)| ≤ ckTotA/D` (and `E_z`);
* the analytic side on the strips `ρ' = 1/20`, `ρ = 1/25`: the mapping hypothesis into
  `coilNbhdP (23/100) (7/100)` (`ck_hmap`, from `torus_hmap`), holomorphy, and the sup bounds
  `|E_R| ≤ ckMR`, `|E_z| ≤ ckMZ` (`ck_supR`, `ck_supZ`, with `Mcoil ≤ 45000`);
* the aliasing tail with `K = (7, 15)`, `e^{1/50} ≤ 50/49`, `e^{-1/50} ≤ 50/51`;
* `iota_diophantine_phi`: the reused Diophantine certificate in the full-period convention
  (`|kι_A − m| ≥ 0.03435/|k|`).

**Main results** (`coilTorus_resR_Bd`, `coilTorus_resZ_Bd`): any `x : FA` whose evaluation is the
real flow-form residual `E_R` (resp. `E_z`) of the torus for the coil field satisfies
`Bd (1/50) x (4.5·10⁹)` (resp. `2.71·10⁹`). The sampled part of the bound is `≈ 2·10⁻⁴`; the
bound is dominated by the aliasing tail `2 M geoZ(q)(tailZ(q,K₁)+tailZ(q,K₂))`, i.e. by the crude
analytic constant `Mcoil` and the narrow strip margin `ρ - r = 1/50` (see the notes for the
extrapolated cost of a useful certificate).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open PlasmaLean.Theory.KAM PlasmaLean.Theory.KAM.PaleyWiener PlasmaLean.Fields
  PlasmaLean.Design.CoilFieldComplex PlasmaLean.Theory.KAM.FourierSumHolo

/-! ## The Diophantine constant in the full-period convention -/

/-- The coil torus is parametrised by the geometric angle `φ` (full period), so the frequency
vector is `(ι, 1)` instead of `(ι/2, 1)`: from the certificate `torusA_period_diophantine` of
`ι/2` with `γ = 0.0687`, `ι_A` itself is `(γ/2, 1)`-Diophantine. -/
theorem iota_diophantine_phi : Diophantine torusAIota (687 / 20000) 1 := by
  intro k m hk
  have h := torusA_period_diophantine (2 * k) m (by omega)
  push_cast at h
  have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
  have e : (2 : ℝ) * k * (torusAIota / 2) - m = k * torusAIota - m := by ring
  rw [e, pow_one, abs_mul, abs_two] at h
  rw [pow_one]
  calc (687 / 20000 : ℝ) / |(k : ℝ)| = 687 / 10000 / (2 * |(k : ℝ)|) := by
        field_simp; ring
    _ ≤ _ := h

/-! ## The analytic inputs of the grid checker -/

theorem ck_tget1 :
    tget ckTbl 1 = (1243293049398167358316279903776, 247306363802463555846379077689) := by
  decide +kernel

theorem ck_two3 : twoAddBr ckD (2 + 1) =
    (2486586098796334716632559807551, 2486586098796334716632559807552) := by decide +kernel

theorem ck_sl : (sqrtBr (2 * ckD) ((2 * ckD - (twoAddBr ckD 2).2) * ckD)).1 =
    494612727604927111692758155377 := by decide +kernel

theorem ck_sh : (sqrtBr (2 * ckD) ((2 * ckD - (twoAddBr ckD 2).1) * ckD)).2 =
    494612727604927111692758155380 := by decide +kernel

theorem ck_two2_le : (twoAddBr ckD 2).2 ≤ 2 * ckD := by decide +kernel

/-- The base entry of the exponential table. -/
theorem ck_base : ‖gexp 32 1 - gauss ckD (tget ckTbl 1)‖ ≤ (ckE1 : ℝ) / ckD := by
  have h := base_exp_approx ckD 2 ckD_pos 1243293049398167358316279903776
    247306363802463555846379077689 1 1 ?_ ?_ ck_two2_le
  · rw [ck_tget1]
    have e : (2 : ℕ) ^ (2 + 3) = 32 := by norm_num
    rw [e] at h
    simpa [ckE1] using h
  · intro x h1 h2
    rw [ck_two3] at h1 h2
    simp only at h1 h2
    rw [abs_le]; push_cast at h1 h2 ⊢
    constructor <;> linarith
  · intro x h1 h2
    rw [ck_sl] at h1; rw [ck_sh] at h2
    rw [abs_le]; push_cast at h1 h2 ⊢
    constructor <;> linarith

/-- The exponential table. -/
theorem ck_tbl : ∀ t < 32, ‖gexp 32 t - gauss ckD (tget ckTbl t)‖ ≤ (ckE : ℝ) / ckD :=
  expTableOK_sound ckD_pos ck_base (by decide +kernel)

/-- The enclosure of `ι_A`. -/
theorem ck_iota : Approx ckD torusAIota (ckIq, 1) :=
  iota_approx ckD_pos (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The analytic inputs hold.** -/
theorem ck_hyp : CkHyp := ⟨ck_tbl, ck_iota⟩

/-! ## The grid sum -/

theorem sum_range_16 (g : ℕ → ℝ) : ∑ j ∈ Finset.range 16, g j =
    g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8 + g 9 + g 10 + g 11 + g 12 + g 13 +
      g 14 + g 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The total of the `E_R` point values. -/
def ckTotA : ℕ := 192080535271609311897390937
/-- The total of the `E_z` point values. -/
def ckTotB : ℕ := 228121633466152530931604479

/-- **The grid sums** (from the 512 kernel evaluations). -/
theorem ck_grid :
    ∑ j ∈ Finset.range 16, ∑ l ∈ Finset.range 32, rowR j l ≤ (ckTotA : ℝ) / ckD ∧
      ∑ j ∈ Finset.range 16, ∑ l ∈ Finset.range 32, rowZ j l ≤ (ckTotB : ℝ) / ckD := by
  have r0 := ck_row_0 ck_hyp
  have r1 := ck_row_1 ck_hyp
  have r2 := ck_row_2 ck_hyp
  have r3 := ck_row_3 ck_hyp
  have r4 := ck_row_4 ck_hyp
  have r5 := ck_row_5 ck_hyp
  have r6 := ck_row_6 ck_hyp
  have r7 := ck_row_7 ck_hyp
  have r8 := ck_row_8 ck_hyp
  have r9 := ck_row_9 ck_hyp
  have r10 := ck_row_10 ck_hyp
  have r11 := ck_row_11 ck_hyp
  have r12 := ck_row_12 ck_hyp
  have r13 := ck_row_13 ck_hyp
  have r14 := ck_row_14 ck_hyp
  have r15 := ck_row_15 ck_hyp
  have hD : (0 : ℝ) < ckD := by exact_mod_cast ckD_pos
  rw [sum_range_16 (fun j => ∑ l ∈ Finset.range 32, rowR j l),
    sum_range_16 (fun j => ∑ l ∈ Finset.range 32, rowZ j l)]
  constructor
  · calc _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add (add_le_add r0.1 r1.1) r2.1) r3.1) r4.1) r5.1) r6.1) r7.1) r8.1) r9.1)
          r10.1) r11.1) r12.1) r13.1) r14.1) r15.1
      _ = (ckTotA : ℝ) / ckD := by
          rw [ckTotA]; push_cast; ring
  · calc _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add (add_le_add r0.2 r1.2) r2.2) r3.2) r4.2) r5.2) r6.2) r7.2) r8.2) r9.2)
          r10.2) r11.2) r12.2) r13.2) r14.2) r15.2
      _ = (ckTotB : ℝ) / ckD := by
          rw [ckTotB]; push_cast; ring

/-! ## The real torus and the tube -/

theorem ckD_eq : (ckD : ℝ) = 2 ^ 100 := by norm_num [ckD, ckD₀]

theorem ck_zero_nz : zeroA ckRecs = 1268299107607331756854126575616 ∧
    zeroB ckRecs = -13793580596804032512 ∧ nzA ckRecs = 243902724395902587519185054985 ∧
    nzB ckRecs = 240799972133483059041953030957 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem ck_s₁ (θ ψ : ℝ) : |Rr ckD ckRecs θ ψ - 1| ≤ 193 / 1000 := by
  refine (abs_Rr_sub_le ckD ckRecs θ ψ 1).trans ?_
  rw [ck_zero_nz.1, ck_zero_nz.2.2.1, ckD_eq]
  norm_num [abs_of_pos]

theorem ck_s₂ (θ ψ : ℝ) : |Zr ckD ckRecs θ ψ| ≤ 19 / 100 := by
  refine (abs_Zr_le ckD ckRecs θ ψ).trans ?_
  rw [ck_zero_nz.2.1, ck_zero_nz.2.2.2, ckD_eq]
  norm_num [abs_of_neg]

theorem ck_tube (θ ψ : ℝ) : torusPt ckD ckRecs θ ψ ∈ realTube (193 / 1000) := by
  have := torusPt_realTube ck_s₁ ck_s₂ (by norm_num) θ ψ
  rwa [max_eq_left (by norm_num)] at this

/-! ## Coefficient sums -/

theorem ck_modeN : ∀ r ∈ ckRecs, modeN r ≤ 24 := by
  have h : ckRecs.all (fun r => decide (modeN r ≤ 24)) = true := by decide +kernel
  intro r hr
  have := List.all_eq_true.1 h r hr
  simpa using this

theorem ck_wsums :
    wsumN 20 19 24 gA ckRecs =
      7507854480863105308515959069155912327075582221632945724686336 ∧
    wsumN 20 19 24 gB ckRecs =
      1277163380115540908147123978059107453315466667129897985267712 ∧
    wsumN 25 24 24 (fun r => 1 * gA r) ckRecs =
      2038280946086395040183813523231181056009454475636954417977142016 ∧
    wsumN 25 24 24 (fun r => modeN r * gA r) ckRecs =
      548013017912280536903127275704751218265914938329892184693056000 ∧
    wsumN 25 24 24 (fun r => modeN r * gB r) ckRecs =
      534637247298250020936230664131225095969025557647868059546013200 ∧
    (ckRecs.map gA).sum = 1512201832003234344373311630601 ∧
    (ckRecs.map gB).sum = 240799972147276639638757063469 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem exp_20 : Real.exp (1 / 20) ≤ ((20 : ℕ) : ℝ) / (19 : ℕ) := by
  have := exp_le_inv_one_sub (x := 1 / 20) (by norm_num) (by norm_num)
  norm_num at this ⊢; linarith

theorem exp_25 : Real.exp (1 / 25) ≤ ((25 : ℕ) : ℝ) / (24 : ℕ) := by
  have := exp_le_inv_one_sub (x := 1 / 25) (by norm_num) (by norm_num)
  norm_num at this ⊢; linarith

/-- The displacement of `R` under complexification on the strip `1/20`. -/
theorem ck_eR (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 20) (hψ : |ψ.im| ≤ 1 / 20) :
    ‖fourierSumC (uR ckD ckRecs) θ ψ - fourierSumC (uR ckD ckRecs) θ.re ψ.re‖ ≤ 1613 / 100000 := by
  have h := norm_fourierSumC_uOfG_sub_re_le hθ hψ (fun _ => 1) (fun _ => 1) ckD
    (fun r => (r.a, r.a')) ckRecs (fun r _ => by simp)
  have h2 := sum_weight_sub_one_le (ρ := 1 / 20) (by norm_num) exp_20 gA ckD ckD_pos ckRecs ck_modeN
  refine (h.trans (le_of_eq ?_)).trans (h2.trans ?_)
  · rfl
  · rw [ck_wsums.1, ck_wsums.2.2.2.2.2.1, ckD_eq]; norm_num

/-- The displacement of `z` under complexification on the strip `1/20`. -/
theorem ck_eZ (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 20) (hψ : |ψ.im| ≤ 1 / 20) :
    ‖fourierSumC (uZ ckD ckRecs) θ ψ - fourierSumC (uZ ckD ckRecs) θ.re ψ.re‖ ≤ 1575 / 100000 := by
  have h := norm_fourierSumC_uOfG_sub_re_le hθ hψ (fun _ => 1) (fun _ => 1) ckD
    (fun r => (r.b, r.b')) ckRecs (fun r _ => by simp)
  have h2 := sum_weight_sub_one_le (ρ := 1 / 20) (by norm_num) exp_20 gB ckD ckD_pos ckRecs ck_modeN
  refine (h.trans (le_of_eq ?_)).trans (h2.trans ?_)
  · rfl
  · rw [ck_wsums.2.1, ck_wsums.2.2.2.2.2.2, ckD_eq]; norm_num

/-- **The mapping hypothesis**: the complexified torus maps the strip `1/20` into
`coilNbhdP (23/100) (7/100)`. -/
theorem ck_hmap : ∀ θ ψ : ℂ, θ ∈ PaleyWiener.stripC (1 / 20) → ψ ∈ PaleyWiener.stripC (1 / 20) →
    torusC ckD ckRecs θ ψ ∈ coilNbhdP (23 / 100) (7 / 100) := by
  have hC : Real.cosh (1 / 20) ≤ 400 / 399 := by
    have := cosh_le_of_exp (x := 1 / 20) (by norm_num) exp_20
    norm_num at this ⊢; linarith
  have hSh : Real.sinh (1 / 20) ≤ 39 / 760 := by
    have := sinh_le_of_exp (x := 1 / 20) exp_20
    norm_num at this ⊢; linarith
  exact torus_hmap ck_s₁ ck_s₂ (by norm_num) ck_eR ck_eZ (by norm_num) hC hSh (by norm_num)
    (by norm_num) (by norm_num)

/-! ## Sup bounds on the strip `1/25` -/

theorem norm_lsym_le (k m : ℤ) : ‖lsym torusAIota (k, m)‖ ≤ ((k.natAbs + m.natAbs : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := torusAIota_bounds
  unfold lsym
  rw [norm_mul, Complex.norm_I, one_mul]
  simp only
  have : ((m : ℂ) + (torusAIota : ℂ) * k) = (((m : ℝ) + torusAIota * k : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < torusAIota), Nat.cast_add, natAbs_cast,
    natAbs_cast]
  have : torusAIota * |(k : ℝ)| ≤ |(k : ℝ)| := by
    have := abs_nonneg (k : ℝ); nlinarith
  linarith

theorem ck_SR (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    ‖fourierSumC (uR ckD ckRecs) θ ψ‖ ≤ 1206 / 1000 := by
  have h := norm_fourierSumC_uOfG_le hθ hψ (fun _ => 1) (fun _ => ((1 : ℕ) : ℝ)) ckD
    (fun r => (r.a, r.a')) ckRecs (fun r _ => by simp)
  have h2 := sum_weight_le (ρ := 1 / 25) (by norm_num) exp_25 (fun _ => 1) gA ckD ckD_pos ckRecs
    ck_modeN
  refine (h.trans (le_of_eq ?_)).trans (h2.trans ?_)
  · rfl
  · rw [ck_wsums.2.2.1, ckD_eq]; norm_num

theorem ck_SL (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    ‖fourierSumC (uLR ckD torusAIota ckRecs) θ ψ‖ ≤ 325 / 1000 := by
  have h := norm_fourierSumC_uOfG_le hθ hψ (lsym torusAIota) (fun r => ((modeN r : ℕ) : ℝ)) ckD
    (fun r => (r.a, r.a')) ckRecs (fun r _ => ⟨norm_lsym_le r.k r.m,
      by have := norm_lsym_le (-r.k) (-r.m); simpa [modeN] using this⟩)
  have h2 := sum_weight_le (ρ := 1 / 25) (by norm_num) exp_25 modeN gA ckD ckD_pos ckRecs
    ck_modeN
  refine (h.trans (le_of_eq ?_)).trans (h2.trans ?_)
  · rfl
  · rw [ck_wsums.2.2.2.1, ckD_eq]; norm_num

theorem ck_SLZ (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    ‖fourierSumC (uLZ ckD torusAIota ckRecs) θ ψ‖ ≤ 317 / 1000 := by
  have h := norm_fourierSumC_uOfG_le hθ hψ (lsym torusAIota) (fun r => ((modeN r : ℕ) : ℝ)) ckD
    (fun r => (r.b, r.b')) ckRecs (fun r _ => ⟨norm_lsym_le r.k r.m,
      by have := norm_lsym_le (-r.k) (-r.m); simpa [modeN] using this⟩)
  have h2 := sum_weight_le (ρ := 1 / 25) (by norm_num) exp_25 modeN gB ckD ckD_pos ckRecs
    ck_modeN
  refine (h.trans (le_of_eq ?_)).trans (h2.trans ?_)
  · rfl
  · rw [ck_wsums.2.2.2.2.1, ckD_eq]; norm_num

theorem ck_cosh {ψ : ℂ} (hψ : |ψ.im| ≤ 1 / 25) : Real.cosh ψ.im ≤ 625 / 624 := by
  have h1 : Real.cosh ψ.im ≤ Real.cosh (1 / 25) :=
    Real.cosh_le_cosh.2 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 25)]; exact hψ)
  have h2 := cosh_le_of_exp (x := 1 / 25) (by norm_num) exp_25
  norm_num at h2 ⊢; linarith

theorem ck_mem {θ ψ : ℂ} (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    torusC ckD ckRecs θ ψ ∈ coilNbhdP (23 / 100) (7 / 100) :=
  ck_hmap θ ψ (show |θ.im| < 1 / 20 by linarith) (show |ψ.im| < 1 / 20 by linarith)

/-- The sup bound of `E_R` on the closed strip `1/25`. -/
def ckMR : ℝ := 2 * (625 / 624) * 45000 * (325 / 1000) + 1206 / 1000 * (2 * (625 / 624) * 45000)

/-- The sup bound of `E_z` on the closed strip `1/25`. -/
def ckMZ : ℝ := 2 * (625 / 624) * 45000 * (317 / 1000) + 1206 / 1000 * 45000

theorem ck_supR (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    ‖resCR ckD torusAIota ckRecs θ ψ‖ ≤ ckMR := by
  have h := norm_resCR_le (d := 12 / 100) (by norm_num) (by norm_num) (by norm_num) (ck_mem hθ hψ)
    (ck_cosh hψ)
    (ck_SL θ ψ hθ hψ) (ck_SR θ ψ hθ hψ)
  have hM := Mcoil_ck_le
  have hM0 : 0 ≤ Mcoil (23 / 100) (12 / 100) (7 / 100) :=
    (norm_nonneg _).trans (norm_coilFieldCC_apply_le (d := 12 / 100) (by norm_num) (by norm_num)
      (by norm_num) (ck_mem hθ hψ) 0)
  refine h.trans ?_
  unfold ckMR
  nlinarith

theorem ck_supZ (θ ψ : ℂ) (hθ : |θ.im| ≤ 1 / 25) (hψ : |ψ.im| ≤ 1 / 25) :
    ‖resCZ ckD torusAIota ckRecs θ ψ‖ ≤ ckMZ := by
  have h := norm_resCZ_le (d := 12 / 100) (by norm_num) (by norm_num) (by norm_num) (ck_mem hθ hψ)
    (ck_cosh hψ)
    (ck_SLZ θ ψ hθ hψ) (ck_SR θ ψ hθ hψ)
  have hM := Mcoil_ck_le
  have hM0 : 0 ≤ Mcoil (23 / 100) (12 / 100) (7 / 100) :=
    (norm_nonneg _).trans (norm_coilFieldCC_apply_le (d := 12 / 100) (by norm_num) (by norm_num)
      (by norm_num) (ck_mem hθ hψ) 0)
  refine h.trans ?_
  unfold ckMZ
  nlinarith

/-! ## The certified strip norms -/

theorem samplePt_eq (N j : ℕ) : samplePt N j = 2 * Real.pi * j / N := rfl

theorem ck_samples_R :
    ∑ j ∈ Finset.range 16, ∑ l ∈ Finset.range 32,
      ‖resCR ckD torusAIota ckRecs (samplePt 16 j) (samplePt 32 l)‖ ≤ (ckTotA : ℝ) / ckD := by
  refine le_of_eq_of_le ?_ ck_grid.1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [resCR_ofReal (w := 193 / 1000) (by norm_num) (ck_tube _ _), Complex.norm_real,
    Real.norm_eq_abs, samplePt_eq, samplePt_eq]
  simp [rowR]

theorem ck_samples_Z :
    ∑ j ∈ Finset.range 16, ∑ l ∈ Finset.range 32,
      ‖resCZ ckD torusAIota ckRecs (samplePt 16 j) (samplePt 32 l)‖ ≤ (ckTotB : ℝ) / ckD := by
  refine le_of_eq_of_le ?_ ck_grid.2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [resCZ_ofReal (w := 193 / 1000) (by norm_num) (ck_tube _ _), Complex.norm_real,
    Real.norm_eq_abs, samplePt_eq, samplePt_eq]
  simp [rowZ]

theorem exp_50 : Real.exp (1 / 50) ≤ 50 / 49 := by
  have := exp_le_inv_one_sub (x := 1 / 50) (by norm_num) (by norm_num)
  norm_num at this ⊢; linarith

theorem expneg_50 : Real.exp (-(1 / 25 - 1 / 50)) ≤ 50 / 51 := by
  have := exp_neg_le (x := 1 / 25 - 1 / 50) (by norm_num)
  norm_num at this ⊢; linarith

/-- **The certified strip norm of the `R`-residual of the coarse coil torus.** Any `x : FA`
whose evaluation is the real flow-form residual `E_R = B^φ 𝓛R − R B^R` of the torus `ckRecs`
for the coil field satisfies `‖x‖_{1/50} ≤ 4.5·10⁹`. -/
theorem coilTorus_resR_Bd (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = (resR ckD torusAIota ckRecs θ ψ : ℂ)) :
    Bd (1 / 50) x (45 * 10 ^ 8) := by
  have hx' : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = resCR ckD torusAIota ckRecs θ ψ := fun θ ψ => by
    rw [hx, resCR_ofReal (w := 193 / 1000) (by norm_num) (ck_tube θ ψ)]
  have hB := Bd_of_sample_sum (ρ' := 1 / 20) (ρ := 1 / 25) (r := 1 / 50) (M := ckMR)
    (S := (ckTotA : ℝ) / ckD) (E := 50 / 49) (Q := 50 / 51) (K₁ := 7) (K₂ := 15) (N₁ := 16)
    (N₂ := 32) x hx' (resCR_add_two_pi_left _ _ _) (resCR_add_two_pi_right _ _ _)
    (resCR_differentiableOn (d := 12 / 100) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ck_hmap)
    (by norm_num) (by norm_num) ck_supR (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ck_samples_R exp_50 expneg_50 (by norm_num)
  refine ⟨hB.1, hB.2.trans ?_⟩
  rw [ckD_eq]
  norm_num [ckMR, ckTotA, geoZ, tailZ]

/-- **The certified strip norm of the `z`-residual of the coarse coil torus**
(`‖x‖_{1/50} ≤ 2.71·10⁹`). -/
theorem coilTorus_resZ_Bd (x : FA)
    (hx : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = (resZ ckD torusAIota ckRecs θ ψ : ℂ)) :
    Bd (1 / 50) x (271 * 10 ^ 7) := by
  have hx' : ∀ θ ψ : ℝ, WEll1Z2.eval x θ ψ = resCZ ckD torusAIota ckRecs θ ψ := fun θ ψ => by
    rw [hx, resCZ_ofReal (w := 193 / 1000) (by norm_num) (ck_tube θ ψ)]
  have hB := Bd_of_sample_sum (ρ' := 1 / 20) (ρ := 1 / 25) (r := 1 / 50) (M := ckMZ)
    (S := (ckTotB : ℝ) / ckD) (E := 50 / 49) (Q := 50 / 51) (K₁ := 7) (K₂ := 15) (N₁ := 16)
    (N₂ := 32) x hx' (resCZ_add_two_pi_left _ _ _) (resCZ_add_two_pi_right _ _ _)
    (resCZ_differentiableOn (d := 12 / 100) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ck_hmap)
    (by norm_num) (by norm_num) ck_supZ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ck_samples_Z exp_50 expneg_50 (by norm_num)
  refine ⟨hB.1, hB.2.trans ?_⟩
  rw [ckD_eq]
  norm_num [ckMZ, ckTotB, geoZ, tailZ]

end PlasmaLean.Design.CoilKam
