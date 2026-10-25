/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCNegTorusAdmL
public import PlasmaLean.Design.RationalStellaratorGCNegTorusOutH
public import PlasmaLean.Certificates.KernelFact

/-!
# The `v∥ < 0` guiding-centre torus `K₀` and admissibility of the KAM step

The approximate invariant torus `K₀ = (1 + u₀G, z₀G)` of the guiding-centre field
`gcFlow (−1/256)` (`ρ_s = −1/256`, rotational transform `ι_B = (161 − √5)/1178`), certified by the
ball pipelines of `Design/RationalStellaratorGCNegTorusOut*`:

* `K₀` is real and analytic (`isReal_u₀G`, `ana_u₀G`, …) with strip bounds at `r_A = 0.1257`
  (`Bd_u₀G`, …, `Bd_Lt_z₀G`);
* **the residual** (`gc_resR_bound`, `gc_resZ_bound`): `‖D̃ 𝓛K₀ − ñ‖_{r_A} ≤ e₀ = 3.5 × 10⁻²⁴`;
* **admissibility** (`gc_adm`): every analytic torus `μ = 10⁻¹²`-close to `K₀` on a strip
  `r_A/7 ≤ ρ ≤ r_A` satisfies the bounds `AdmBounds` of the Newton step with the constants `cGC`
  (field bounds and derivatives from the low-resolution ball chain, `‖D̃⁻¹‖ ≤ 1.4865`,
  `‖W₀⁻¹‖ ≤ 207.47`, torsion `‖T₀‖ ≤ 43.171`, twist `|⟨T₀⟩| ≥ 0.327`).

**Sanity.** `Bd_u₀G` is the torus bound of `cGC` without `μ`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-! ## The torus `K₀` -/

/-- `r_A ≥ 0`. -/
theorem rA_nonneg' : 0 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]

/-- `K₀` is analytic. -/
theorem ana_u₀G : Ana u₀G := ana_ctr_grid SH NH MH _ _

/-- `K₀` is analytic. -/
theorem ana_z₀G : Ana z₀G := ana_ctr_grid SH NH MH _ _

/-- `K₀` is real. -/
theorem isReal_u₀G : IsReal u₀G := isReal_ctr_sym SH NH MH 0 (halfGridR FH NH datH_U)

/-- `K₀` is real. -/
theorem isReal_z₀G : IsReal z₀G := isReal_ctr_sym SH NH MH 1 (halfGridR FH NH datH_Z)

/-- The values of the high-resolution chain at `r_A`. -/
theorem valH_rA (i : ℕ) (hi : i < 70) : Bd KamTorusA.rA (XH i) ((BH i + EH i : ℚ) : ℝ) :=
  valH_le rA_nonneg' exp_rA_le' i hi

/-- `‖u₀‖_{r_A} ≤ 0.2174`. -/
theorem Bd_u₀G : Bd KamTorusA.rA u₀G (1087 / 5000) :=
  (valH_rA 4 (by norm_num)).le (by
    have := qle (show BH 4 + EH 4 ≤ 1087 / 5000 by kernel_fact)
    push_cast at this ⊢; exact this)

/-- `‖z₀‖_{r_A} ≤ 0.1794`. -/
theorem Bd_z₀G : Bd KamTorusA.rA z₀G (897 / 5000) :=
  (valH_rA 5 (by norm_num)).le (by
    have := qle (show BH 5 + EH 5 ≤ 897 / 5000 by kernel_fact)
    push_cast at this ⊢; exact this)

/-- `‖∂_θ u₀‖_{r_A} ≤ 0.1818`. -/
theorem Bd_dTh_u₀G : Bd KamTorusA.rA (dTh u₀G) (909 / 5000) := by
  rw [← dTh_xH_thU]
  refine (normH exp_rA_le' 8 (by norm_num)).le ?_
  have := qle (show BH 8 ≤ 909 / 5000 by kernel_fact); push_cast at this ⊢; exact this

/-- `‖∂_θ z₀‖_{r_A} ≤ 0.1749`. -/
theorem Bd_dTh_z₀G : Bd KamTorusA.rA (dTh z₀G) (1749 / 10000) := by
  rw [← dTh_xH_thZ]
  refine (normH exp_rA_le' 9 (by norm_num)).le ?_
  have := qle (show BH 9 ≤ 1749 / 10000 by kernel_fact); push_cast at this ⊢; exact this

/-- `‖2^{−96} X‖ ≤ 2^{−96} ‖X‖`. -/
theorem Bd_inv_pow96 {r : ℝ} {X : FA} {B : ℝ} (h : Bd r ((2 : ℂ) ^ 96 • X) B) :
    Bd r X (B / 2 ^ 96) := by
  have := h.smul ((2 : ℂ) ^ 96)⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this
  refine this.le (le_of_eq ?_)
  rw [norm_inv, norm_pow, Complex.norm_ofNat]; ring

/-- `‖𝓛 u₀‖_{r_A} ≤ 0.1319`. -/
theorem Bd_Lt_u₀G : Bd KamTorusA.rA (Lt iotaB u₀G) (1319 / 10000) := by
  have h := Bd_inv_pow96 (valH_rA 6 (by norm_num))
  refine h.le ?_
  have := qle (show (BH 6 + EH 6) / 2 ^ 96 ≤ 1319 / 10000 by kernel_fact)
  push_cast at this ⊢; exact this

/-- `‖𝓛 z₀‖_{r_A} ≤ 0.1222`. -/
theorem Bd_Lt_z₀G : Bd KamTorusA.rA (Lt iotaB z₀G) (611 / 5000) := by
  have h := Bd_inv_pow96 (valH_rA 7 (by norm_num))
  refine h.le ?_
  have := qle (show (BH 7 + EH 7) / 2 ^ 96 ≤ 611 / 5000 by kernel_fact)
  push_cast at this ⊢; exact this

/-! ## The residual of `K₀` -/

/-- The `R`-residual node is `2^96` times the flow-form residual. -/
theorem eval_trH_resR :
    Ex.eval XH trH_resR = (2 : ℂ) ^ 96 • (gcFlow (-1 / 256)).resR iotaB u₀G z₀G := by
  rw [FlowFieldS.resR_eq]
  simp only [trH_resR, Ex.eval, XH, FlowFieldS.Dof, gcFlow, KH, Algebra.smul_def, map_pow,
    map_ofNat, Int.cast_ofNat]
  norm_num
  ring

/-- The `z`-residual node is `2^96` times the flow-form residual. -/
theorem eval_trH_resZ :
    Ex.eval XH trH_resZ = (2 : ℂ) ^ 96 • (gcFlow (-1 / 256)).resZ iotaB u₀G z₀G := by
  rw [FlowFieldS.resZ_eq]
  simp only [trH_resZ, Ex.eval, XH, FlowFieldS.Dof, gcFlow, KH, Algebra.smul_def, map_pow,
    map_ofNat, Int.cast_ofNat]
  norm_num
  ring

/-- **The residual of `K₀`** (`R`-component): `‖D̃ 𝓛u₀ − ñ_R‖_{r_A} ≤ 3.5 × 10⁻²⁴`. -/
theorem gc_resR_bound : Bd KamTorusA.rA ((gcFlow (-1 / 256)).resR iotaB u₀G z₀G) e0G := by
  have h := normH_resR rA_nonneg' exp_rA_le'
  rw [eval_trH_resR] at h
  refine (Bd_inv_pow96 h).le ?_
  norm_num [e0G]

/-- **The residual of `K₀`** (`z`-component): `‖D̃ 𝓛z₀ − ñ_z‖_{r_A} ≤ 3.5 × 10⁻²⁴`. -/
theorem gc_resZ_bound : Bd KamTorusA.rA ((gcFlow (-1 / 256)).resZ iotaB u₀G z₀G) e0G := by
  have h := normH_resZ rA_nonneg' exp_rA_le'
  rw [eval_trH_resZ] at h
  refine (Bd_inv_pow96 h).le ?_
  norm_num [e0G]

/-! ## Distances from `K₀` to the low-resolution torus -/

/-- `‖u₀ − u_S‖_{r_A} ≤ 1.562 × 10⁻¹⁴`. -/
theorem dist_u : Bd KamTorusA.rA (u₀G - xL 4) ((1562 / 10 ^ 17 : ℚ) : ℝ) := by
  have h := normH_dU rA_nonneg' exp_rA_le'
  simp only [trH_dU, Ex.eval, XH] at h
  exact h.le (le_of_eq (by norm_num))

/-- `‖z₀ − z_S‖_{r_A} ≤ 6.909 × 10⁻¹⁵`. -/
theorem dist_z : Bd KamTorusA.rA (z₀G - xL 5) ((6909 / 10 ^ 18 : ℚ) : ℝ) := by
  have h := normH_dZ rA_nonneg' exp_rA_le'
  simp only [trH_dZ, Ex.eval, XH] at h
  exact h.le (le_of_eq (by norm_num))

/-- `‖∂_θ u₀ − ∂_θ u_S‖_{r_A} ≤ 8.004 × 10⁻¹⁴`. -/
theorem dist_a : Bd KamTorusA.rA (dTh u₀G - dTh (xL 4)) ((8004 / 10 ^ 17 : ℚ) : ℝ) := by
  have h := normH_dA rA_nonneg' exp_rA_le'
  simp only [trH_dA, Ex.eval, XH] at h
  exact h.le (le_of_eq (by norm_num))

/-- `‖∂_θ z₀ − ∂_θ z_S‖_{r_A} ≤ 4.518 × 10⁻¹⁴`. -/
theorem dist_b : Bd KamTorusA.rA (dTh z₀G - dTh (xL 5)) ((4518 / 10 ^ 17 : ℚ) : ℝ) := by
  have h := normH_dB rA_nonneg' exp_rA_le'
  simp only [trH_dB, Ex.eval, XH] at h
  exact h.le (le_of_eq (by norm_num))

/-! ## Admissibility near `K₀` -/

/-- **Admissibility of every torus `μ`-close to `K₀`** on a strip `0 < ρ ≤ r_A`. -/
theorem gc_adm {ρ : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ KamTorusA.rA) {u z : FA} (hu : Ana u) (hz : Ana z)
    (hC : Close ρ iotaB u z u₀G z₀G μG) :
    (gcFlow (-1 / 256)).AdmBounds cGC iotaB ρ u z :=
  gc_adm_near hρ hρA hu hz hC Bd_u₀G Bd_z₀G Bd_dTh_u₀G Bd_dTh_z₀G Bd_Lt_u₀G Bd_Lt_z₀G dist_u
    dist_z dist_a dist_b

end PlasmaLean.Design.RationalStellaratorGCNeg
