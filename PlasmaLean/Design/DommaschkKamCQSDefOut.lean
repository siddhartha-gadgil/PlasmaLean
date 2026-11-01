/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCQSDefChain
public import PlasmaLean.Design.DommaschkKamCAdm

/-!
# The QA defect of torus C at the surrogate torus (N-34, D4)

The certified values of the QA-defect chain of Dommaschk torus C (`Design/DommaschkKamCQSDefChain`)
expressed through the straight-line program of the QA-defect numerator (N-34 §4,
`Design/DommaschkKamCQSPoly`) at the low-resolution surrogate torus `(xA 4, xA 5)` of the
admissibility chain (oracle angle `ψₒ = 2φ`, `24 × 28`, scale `2^{−64}`), all in the strip norm
`ρ = 0` (`ℓ¹` of the Fourier coefficients, which bounds the supremum).

**The program on a leaf vector** (`qsQ`, …, `qsNg`; `l : Fin 13 → A` in the order of the fields of
`QSLeaves`: `D, D_u, D_z, D_φ, n_R, n_R,u, n_R,z, n_R,φ, n_z, n_z,u, n_z,z, n_z,φ, R`): the same
formulas as `QSLeaves.Q, …, QSLeaves.Ng`, so `(QSLeaves.mk (l 0) … (l 12)).Ng ι u_θ z_θ =
qsNg l ι u_θ z_θ` by `rfl`. (`Design/DommaschkKamCQSPoly` cannot be imported together with the Adm
modules: both declare `DommaschkKamC.Qp`.) `lvO u z` is the leaf vector at a torus in the oracle
frame (`Fo p u z`, `R = R₀ + u`).

**Surrogate bounds** (`lS = lvO (xA 4) (xA 5)`, `ι_q = iotaqC`, `u_θ = xA 6`, `z_θ = xA 7`; the
approximate inverses `qG = xQ 238` of `Q R¹⁷` and `qB = xQ 241` of `R¹⁶`):
* `surr_G`: `‖qG · N_g(lS, ι_q)‖₀ ≤ 0.0430282` (the numerator
  `∂_{φ_B}|B|² · (qG Q R¹⁷)`);
* `surr_eG`: `‖qG Q R¹⁷ − 1‖₀ ≤ 1.97e-06`;
  `surr_GI`: `‖qG (N₁ u_θ + N₂ z_θ)‖₀ ≤ 0.07374`;
* `surr_eB`: `‖qB R¹⁶ − 1‖₀ ≤ 1.87e-10`;
  `surr_bB`: `‖Q qB − c_B‖₀ ≤ e_B` (`c_B = 4948040378/2^32`);
* `surr_dM`: `‖D − c_D‖₀ ≤ e_D` (`c_D = 2738375982/2^32`);
* `surr_F`: `|⟨(qG N_g)² R⁸ qD⟩| ≤ 1.898e-05` (the `L²(J)` integrand,
  `qD` the Adm inverse of `D`).

**Sanity.** `qsNg_iota_zero` (degenerate), `qsNg_instance` (concrete: the instance of
`qs_instance`), `surr_G_ne` (rejected: the surrogate defect numerator is not zero, torus C is not
exactly quasi-axisymmetric: its `(0, 6)` Fourier coefficient is about `0.00117`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam
  PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall
  WEll1Z2 Complex

/-! ## The straight-line program on a leaf vector -/

section Prog

variable {A : Type*} [CommRing A]

/-- `Q = n_R² + R²D² + n_z²` (`QSLeaves.Q`). -/
def qsQ (l : Fin 13 → A) : A := l 4 ^ 2 + l 12 ^ 2 * l 0 ^ 2 + l 8 ^ 2
/-- `Q_u` (`QSLeaves.Qu`). -/
def qsQu (l : Fin 13 → A) : A :=
  2 * (l 4 * l 5 + l 12 * l 0 ^ 2 + l 12 ^ 2 * (l 0 * l 1) + l 8 * l 9)
/-- `Q_z` (`QSLeaves.Qz`). -/
def qsQz (l : Fin 13 → A) : A := 2 * (l 4 * l 6 + l 12 ^ 2 * (l 0 * l 2) + l 8 * l 10)
/-- `Q_φ` (`QSLeaves.Qf`). -/
def qsQf (l : Fin 13 → A) : A := 2 * (l 4 * l 7 + l 12 ^ 2 * (l 0 * l 3) + l 8 * l 11)
/-- `P_L = Q_u n_R + Q_z n_z + D Q_φ` (`QSLeaves.PL`). -/
def qsPL (l : Fin 13 → A) : A := qsQu l * l 4 + qsQz l * l 8 + l 0 * qsQf l
/-- `M_L = R P_L − 16 Q n_R` (`QSLeaves.ML`). -/
def qsML (l : Fin 13 → A) : A := l 12 * qsPL l - 16 * qsQ l * l 4
/-- `N₀ = R⁸ M_L` (`QSLeaves.N0`). -/
def qsN0 (l : Fin 13 → A) : A := l 12 ^ 8 * qsML l
/-- `N₁ = n_R M_L − Q(R Q_u − 16 Q)` (`QSLeaves.N1`). -/
def qsN1 (l : Fin 13 → A) : A := l 4 * qsML l - qsQ l * (l 12 * qsQu l - 16 * qsQ l)
/-- `N₂ = n_z M_L − R Q Q_z` (`QSLeaves.N2`). -/
def qsN2 (l : Fin 13 → A) : A := l 8 * qsML l - l 12 * qsQ l * qsQz l
/-- **The QA-defect numerator** `N_g = N₀ + ι(N₁ u_θ + N₂ z_θ)` (`QSLeaves.Ng`). -/
def qsNg (l : Fin 13 → A) (ι uθ zθ : A) : A := qsN0 l + ι * (qsN1 l * uθ + qsN2 l * zθ)

/-- Ring homomorphisms commute with `Q`. -/
theorem qsQ_map {B : Type*} [CommRing B] (f : A →+* B) (l : Fin 13 → A) :
    f (qsQ l) = qsQ (fun i => f (l i)) := by
  simp [qsQ]

/-- Ring homomorphisms commute with `N₁`. -/
theorem qsN1_map {B : Type*} [CommRing B] (f : A →+* B) (l : Fin 13 → A) :
    f (qsN1 l) = qsN1 (fun i => f (l i)) := by
  simp [qsN1, qsML, qsPL, qsQ, qsQu, qsQz, qsQf, map_ofNat]

/-- Ring homomorphisms commute with `N₂`. -/
theorem qsN2_map {B : Type*} [CommRing B] (f : A →+* B) (l : Fin 13 → A) :
    f (qsN2 l) = qsN2 (fun i => f (l i)) := by
  simp [qsN2, qsML, qsPL, qsQ, qsQu, qsQz, qsQf, map_ofNat]

/-- **Ring homomorphisms commute with the numerator.** -/
theorem qsNg_map {B : Type*} [CommRing B] (f : A →+* B) (l : Fin 13 → A) (ι uθ zθ : A) :
    f (qsNg l ι uθ zθ) = qsNg (fun i => f (l i)) (f ι) (f uθ) (f zθ) := by
  simp [qsNg, qsN0, qsN1, qsN2, qsML, qsPL, qsQ, qsQu, qsQz, qsQf, map_ofNat]

/-- **Sanity (degenerate)**: for `ι = 0` the numerator is `N₀ = R⁸ M_L`. -/
theorem qsNg_iota_zero (l : Fin 13 → A) (uθ zθ : A) : qsNg l 0 uθ zθ = qsN0 l := by
  simp [qsNg]

end Prog

/-- **Sanity (concrete)**: the instance of `qs_instance` (`R = D = n_R = 1`, all other leaves `0`,
`ι = 1/2`, `u_θ = z_θ = 0`): `N_g = −30`. -/
theorem qsNg_instance :
    qsNg (![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1] : Fin 13 → ℚ) (1 / 2) 0 0 = -30 := by
  norm_num [qsNg, qsN0, qsN1, qsN2, qsML, qsPL, qsQ, qsQu, qsQz, qsQf]

/-! ## The leaves at a torus (oracle frame) -/

/-- The leaf vector at a torus `(u, z)` in the oracle frame: the field polynomials `D, n_R, n_z`,
their `∂_u`, `∂_z`, the `φ`-derivatives `dDf, dnRf, dnZf` (`Design/DommaschkKamCQSData`), and
`R = R₀ + u`. -/
def lvO (u z : FA) : Fin 13 → FA :=
  ![Fo dD u z, Fo (DkPoly.dU dD) u z, Fo (DkPoly.dZ dD) u z, Fo dDf u z, Fo dnR u z,
    Fo (DkPoly.dU dnR) u z, Fo (DkPoly.dZ dnR) u z, Fo dnRf u z, Fo dnZ u z,
    Fo (DkPoly.dU dnZ) u z, Fo (DkPoly.dZ dnZ) u z, Fo dnZf u z, RofG dkR0 u]

/-- The R-form `∂_φD` becomes the `u`-form one (kernel check). -/
theorem qsd_substR_Df : substR dDRf = dDf := by kernel_fact
/-- The R-form `∂_φn_R` becomes the `u`-form one (kernel check). -/
theorem qsd_substR_nRf : substR (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRhf) = dnRf := by kernel_fact
/-- The R-form `∂_φn_z` becomes the `u`-form one (kernel check). -/
theorem qsd_substR_nZf : substR dnZRf = dnZf := by kernel_fact

/-- A new leaf at the surrogate is the R-form chain value `fQ k`. -/
theorem Fo_surrQ {k : ℕ} {pu : DkPoly.SP} (h : substR (polyQ k) = pu) :
    Fo pu (xA 4) (xA 5) = fQ k := by
  rw [Fo, ← h, ev_substR_A, xRo_eq]; rfl

/-- The surrogate leaf vector. -/
abbrev lS : Fin 13 → FA := lvO (xA 4) (xA 5)

/-- The surrogate leaf `D`. -/
theorem lS0 : lS 0 = XA 106 := Fo_surr (k := 0) subst_D
/-- The surrogate leaf `D_u`. -/
theorem lS1 : lS 1 = XA 115 := Fo_surr (k := 1) subst_Du
/-- The surrogate leaf `D_z`. -/
theorem lS2 : lS 2 = XA 123 := Fo_surr (k := 2) subst_Dz
/-- The surrogate leaf `D_φ`. -/
theorem lS3 : lS 3 = fQ 0 := Fo_surrQ (k := 0) qsd_substR_Df
/-- The surrogate leaf `n_R`. -/
theorem lS4 : lS 4 = XA 133 := Fo_surr (k := 3) subst_nR
/-- The surrogate leaf `n_R,u`. -/
theorem lS5 : lS 5 = XA 143 := Fo_surr (k := 4) subst_nRu
/-- The surrogate leaf `n_R,z`. -/
theorem lS6 : lS 6 = XA 151 := Fo_surr (k := 5) subst_nRz
/-- The surrogate leaf `n_R,φ`. -/
theorem lS7 : lS 7 = fQ 1 := Fo_surrQ (k := 1) qsd_substR_nRf
/-- The surrogate leaf `n_z`. -/
theorem lS8 : lS 8 = XA 159 := Fo_surr (k := 6) subst_nZ
/-- The surrogate leaf `n_z,u`. -/
theorem lS9 : lS 9 = XA 167 := Fo_surr (k := 7) subst_nZu
/-- The surrogate leaf `n_z,z`. -/
theorem lS10 : lS 10 = XA 173 := Fo_surr (k := 8) subst_nZz
/-- The surrogate leaf `n_z,φ`. -/
theorem lS11 : lS 11 = fQ 2 := Fo_surrQ (k := 2) qsd_substR_nZf
/-- The surrogate leaf `R`. -/
theorem lS12 : lS 12 = XA 10 := R_surr

/-! ## The chain values as the program at the surrogate -/

/-- The chain variable `R²`. -/
theorem XA_R2 : XA 11 = XA 10 ^ 2 := by
  rw [show XA 11 = RvA ^ 2 * zvA ^ 0 from rfl, show XA 10 = RvA from rfl, pow_zero, mul_one]
/-- The chain variable `R⁸`. -/
theorem XA_R8 : XA 17 = XA 10 ^ 8 := by
  rw [show XA 17 = RvA ^ 8 * zvA ^ 0 from rfl, show XA 10 = RvA from rfl, pow_zero, mul_one]
/-- The chain variable `R¹⁶`. -/
theorem XA_R16 : XA 25 = XA 10 ^ 16 := by
  rw [show XA 25 = RvA ^ 16 * zvA ^ 0 from rfl, show XA 10 = RvA from rfl, pow_zero, mul_one]
/-- The chain variable `R¹⁷`. -/
theorem XA_R17 : XA 26 = XA 10 ^ 17 := by
  rw [show XA 26 = RvA ^ 17 * zvA ^ 0 from rfl, show XA 10 = RvA from rfl, pow_zero, mul_one]
/-- The chain variable `D²`. -/
theorem XA_DD : XA 179 = XA 106 * XA 106 := rfl

/-- The surrogate leaves rewritten to chain values. -/
theorem lS_vals : lS 0 = XA 106 ∧ lS 1 = XA 115 ∧ lS 2 = XA 123 ∧ lS 3 = fQ 0 ∧ lS 4 = XA 133 ∧
    lS 5 = XA 143 ∧ lS 6 = XA 151 ∧ lS 7 = fQ 1 ∧ lS 8 = XA 159 ∧ lS 9 = XA 167 ∧
    lS 10 = XA 173 ∧ lS 11 = fQ 2 ∧ lS 12 = XA 10 :=
  ⟨lS0, lS1, lS2, lS3, lS4, lS5, lS6, lS7, lS8, lS9, lS10, lS11, lS12⟩

/-- The node `Q` is `qsQ` at the surrogate. -/
theorem Qnq_eq : Qnq = qsQ lS := by
  obtain ⟨h0, -, -, -, h4, -, -, -, h8, -, -, -, h12⟩ := lS_vals
  rw [qsQ, h0, h4, h8, h12, Qnq, XA_R2, XA_DD]; ring

/-- The node `Q_u/2`. -/
theorem Qu2q_eq : 2 * Qu2q = qsQu lS := by
  obtain ⟨h0, h1, -, -, h4, h5, -, -, h8, h9, -, -, h12⟩ := lS_vals
  rw [qsQu, h0, h1, h4, h5, h8, h9, h12, Qu2q, DDuq, XA_R2, XA_DD]; ring

/-- The node `Q_z/2`. -/
theorem Qz2q_eq : 2 * Qz2q = qsQz lS := by
  obtain ⟨h0, -, h2, -, h4, -, h6, -, h8, -, h10, -, h12⟩ := lS_vals
  rw [qsQz, h0, h2, h4, h6, h8, h10, h12, Qz2q, DDzq, XA_R2]

/-- The node `Q_φ/2`. -/
theorem Qf2q_eq : 2 * Qf2q = qsQf lS := by
  obtain ⟨h0, -, -, h3, h4, -, -, h7, h8, -, -, h11, h12⟩ := lS_vals
  rw [qsQf, h0, h3, h4, h7, h8, h11, h12, Qf2q, DDfq, XA_R2]

/-- The node `P_L/2`. -/
theorem PL2q_eq : 2 * PL2q = qsPL lS := by
  obtain ⟨h0, -, -, -, h4, -, -, -, h8, -, -, -, -⟩ := lS_vals
  rw [qsPL, ← Qu2q_eq, ← Qz2q_eq, ← Qf2q_eq, h0, h4, h8, PL2q]; ring

/-- The node `M_L`. -/
theorem MLq_eq : MLq = qsML lS := by
  obtain ⟨-, -, -, -, h4, -, -, -, -, -, -, -, h12⟩ := lS_vals
  rw [qsML, ← PL2q_eq, ← Qnq_eq, h4, h12, MLq]; push_cast; ring

/-- The node `N₁`. -/
theorem N1q_eq : N1q = qsN1 lS := by
  obtain ⟨-, -, -, -, h4, -, -, -, -, -, -, -, h12⟩ := lS_vals
  rw [qsN1, ← MLq_eq, ← Qnq_eq, ← Qu2q_eq, h4, h12, N1q, RQu2q]; push_cast; ring

/-- The node `N₂`. -/
theorem N2q_eq : N2q = qsN2 lS := by
  obtain ⟨-, -, -, -, -, -, -, -, h8, -, -, -, h12⟩ := lS_vals
  rw [qsN2, ← MLq_eq, ← Qnq_eq, ← Qz2q_eq, h8, h12, N2q, RQq]; push_cast; ring

/-- The node `N₁ u_θ + N₂ z_θ`. -/
theorem N12q_eq : N12q = qsN1 lS * xA 6 + qsN2 lS * xA 7 := by
  rw [N12q, N1q_eq, N2q_eq]; rfl

/-- The node `Q R¹⁷`. -/
theorem QR17q_eq : QR17q = qsQ lS * lS 12 ^ 17 := by
  rw [QR17q, Qnq_eq, lS12, XA_R17]

/-- The surrogate iota `ι_q = −Iqc/2^128` in the strip algebra. -/
def iotaqF : FA := algebraMap ℂ FA ((iotaqC : ℝ) : ℂ)

set_option linter.style.longLine false in
/-- **The node `G` is `qG · N_g` at the surrogate** (with `ι_q`). -/
theorem Gq_eq : Gq = xQ 238 * qsNg lS iotaqF (xA 6) (xA 7) := by
  have e8 : qG8q * MLq = xQ 238 * qsN0 lS := by
    rw [qG8q, MLq_eq, qsN0, lS12, XA_R8]; ring
  have e12 := N12q_eq
  rw [Gq, e8, e12, qsNg, iotaqF, iotaqC]
  simp only [Algebra.smul_def, ← map_intCast (algebraMap ℂ FA)]
  have h2 : algebraMap ℂ FA ((2 : ℂ) ^ 128)⁻¹ * algebraMap ℂ FA ((340282366920938463463374607431768211456 : ℤ) : ℂ) = 1 := by
    rw [← map_mul]; norm_num
  have hi : algebraMap ℂ FA (((-((Iqc : ℝ) / 2 ^ Qc)) : ℝ) : ℂ) =
      -(algebraMap ℂ FA ((2 : ℂ) ^ 128)⁻¹ * algebraMap ℂ FA ((82229627956397544609921576118836816763 : ℤ) : ℂ)) := by
    rw [← map_mul, ← map_neg]; congr 1; simp [Iqc, Qc]; ring
  rw [hi]
  linear_combination (xQ 238 * qsN0 lS) * h2

/-- The node `F` is the `L²(J)` integrand at the surrogate. -/
theorem Fq_eq : Fq = (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 * (lS 12 ^ 8 * xA 186) := by
  rw [Fq, GGq, H8q, Gq_eq, lS12, XA_R8]; rw [show XA 186 = xA 186 from rfl]; ring

/-! ## The surrogate bounds -/

/-- A bound of `2^k • y` gives a bound of `y`. -/
theorem Bd_of_smul2 {ρ b : ℝ} {y : FA} (k : ℕ) (h : Bd ρ (((2 : ℂ) ^ k) • y) b) :
    Bd ρ y (b / 2 ^ k) := by
  have h2 := h.smul ((2 : ℂ) ^ k)⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by simp), one_smul, norm_inv, norm_pow, Complex.norm_ofNat] at h2
  exact h2.le (le_of_eq (by ring))

set_option linter.style.longLine false in
/-- **The defect numerator at the surrogate**: `‖qG · N_g(lS, ι_q, xA 6, xA 7)‖₀ ≤ B + E`. -/
theorem surr_G : Bd 0 (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) (((4302821 / 10 ^ 8 : ℚ) : ℚ) : ℝ) := by
  have h := valQ_le 240 (by norm_num)
  rw [show XQ 240 = Gq from rfl, Gq_eq] at h
  exact h.le (by exact_mod_cast (show BQ 240 + EQ 240 ≤ (4302821 / 10 ^ 8 : ℚ) by kernel_fact))

set_option linter.style.longLine false in
/-- **The approximate inverse of `Q R¹⁷` at the surrogate.** -/
theorem surr_eG : Bd 0 (xQ 238 * (qsQ lS * lS 12 ^ 17) - 1) (((982911 / 500000000000 : ℚ) : ℚ) : ℝ) := by
  have h := nQ_eG
  rw [show Ex.eval XQ trQ_eG = xQ 238 * QR17q - 1 * 1 from rfl, mul_one, QR17q_eq] at h
  exact h

set_option linter.style.longLine false in
/-- The `ι`-coefficient of the numerator at the surrogate. -/
theorem surr_GI : Bd 0 (xQ 238 * (qsN1 lS * xA 6 + qsN2 lS * xA 7)) (((368683 / 5000000 : ℚ) : ℚ) : ℝ) := by
  have h := nQ_GI
  rw [show Ex.eval XQ trQ_GI = xQ 238 * N12q from rfl, N12q_eq] at h
  exact h

/-- **The approximate inverse of `R¹⁶` at the surrogate.** -/
theorem surr_eB : Bd 0 (xQ 241 * lS 12 ^ 16 - 1) (((1868661 / 10 ^ 16 : ℚ) : ℚ) : ℝ) := by
  have h := nQ_eB
  rw [show Ex.eval XQ trQ_eB = xQ 241 * XA 25 - 1 * 1 from rfl, mul_one, XA_R16, ← lS12] at h
  exact h

/-- The constant `c_B ≈ ⟨|B|²⟩` of the `|B|²` node. -/
def cBF : FA := algebraMap ℂ FA (((4948040378 / 2 ^ 32 : ℚ) : ℚ) : ℂ)

/-- The constant `c_D ≈ ⟨D⟩` of the `D_min` node. -/
def cDF : FA := algebraMap ℂ FA (((2738375982 / 2 ^ 32 : ℚ) : ℚ) : ℂ)

/-- **`|B|²` at the surrogate**: `‖Q qB − c_B‖₀ ≤ e_B`. -/
theorem surr_bB : Bd 0 (qsQ lS * xQ 241 - cBF) ((((279394800 : ℚ) : ℚ) : ℝ) / 2 ^ 32) := by
  have h := nQ_bB
  have e : Ex.eval XQ trQ_bB = ((2 : ℂ) ^ 32) • (qsQ lS * xQ 241 - cBF) := by
    have h1 : algebraMap ℂ FA ((2 : ℂ) ^ 32) = ((4294967296 : ℤ) : FA) := by
      rw [← map_intCast (algebraMap ℂ FA)]; norm_num
    have h2 : algebraMap ℂ FA ((2 : ℂ) ^ 32) * cBF = ((4948040378 : ℤ) : FA) := by
      rw [cBF, ← map_mul, ← map_intCast (algebraMap ℂ FA)]; congr 1; push_cast; ring
    rw [show Ex.eval XQ trQ_bB = ((4294967296 : ℤ) : FA) * (Qnq * xQ 241) -
      ((4948040378 : ℤ) : FA) * (1 * 1) from rfl, Qnq_eq, Algebra.smul_def, mul_sub, h2, h1]
    ring
  rw [e] at h
  exact Bd_of_smul2 32 h

set_option linter.style.longLine false in
/-- **`D` at the surrogate**: `‖D − c_D‖₀ ≤ e_D`. -/
theorem surr_dM : Bd 0 (lS 0 - cDF) ((((2060210000 : ℚ) : ℚ) : ℝ) / 2 ^ 32) := by
  have h := nQ_dM
  have e : Ex.eval XQ trQ_dM = ((2 : ℂ) ^ 32) • (lS 0 - cDF) := by
    have h1 : algebraMap ℂ FA ((2 : ℂ) ^ 32) = ((4294967296 : ℤ) : FA) := by
      rw [← map_intCast (algebraMap ℂ FA)]; norm_num
    have h2 : algebraMap ℂ FA ((2 : ℂ) ^ 32) * cDF = ((2738375982 : ℤ) : FA) := by
      rw [cDF, ← map_mul, ← map_intCast (algebraMap ℂ FA)]; congr 1; push_cast; ring
    rw [show Ex.eval XQ trQ_dM = ((4294967296 : ℤ) : FA) * XA 106 - ((2738375982 : ℤ) : FA) * 1 from rfl,
      lS0, Algebra.smul_def, mul_sub, h2, h1]
    ring
  rw [e] at h
  exact Bd_of_smul2 32 h

set_option maxRecDepth 100000 in
/-- The centre grid of `F` at the origin. -/
theorem gQ_F_centre : gQ 244 NA MA = -330129809667532 := by kernel_fact

/-- The mean of the centre of `F`. -/
theorem avg_xQ_F : avg (xQ 244) = (((((82532452416883 / 2 ^ 62 : ℚ) : ℚ) : ℚ) : ℂ)) := by
  change coeff (ctr SA NA MA (1, 0, 2) (gridPolyNM NA MA (gQ 244))) (0, 0) = _
  rw [coeff_ctr_grid]
  simp only [abs_zero, Nat.cast_nonneg, and_self, ↓reduceIte, zero_add, Int.toNat_natCast, NA, MA,
    SA]
  rw [show gQ 244 24 28 = -330129809667532 from gQ_F_centre]
  push_cast
  simp [Complex.I_sq]; ring

set_option linter.style.longLine false in
/-- **The `L²(J)` integrand at the surrogate**: `|⟨(qG N_g)² R⁸ qD⟩| ≤ m_F`. -/
theorem surr_F : ‖avg ((xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 * (lS 12 ^ 8 * xA 186))‖ ≤
    (((1483 / 78125000 : ℚ) : ℚ) : ℝ) := by
  rw [← Fq_eq, show Fq = XQ 244 from rfl]
  have h1 : ‖avg (XQ 244 - xQ 244)‖ ≤ EQ 244 := (ballQ_all 244 (by norm_num)).norm_avg_le le_rfl
  have h2 : avg (XQ 244) = avg (xQ 244) + avg (XQ 244 - xQ 244) := by rw [avg_sub]; ring
  rw [h2, avg_xQ_F]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_ratCast]
  have := qleA (show |((82532452416883 / 2 ^ 62 : ℚ) : ℚ)| + EQ 244 ≤ (1483 / 78125000 : ℚ) by kernel_fact)
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
/-- **Sanity (rejected fixture)**: the surrogate defect numerator is not zero: torus C is not
exactly quasi-axisymmetric (the `(0, 6)` Fourier coefficient of the centre of `G` is about
`0.00117`, larger than the radius `1.2e-05`). -/
theorem surr_G_ne : xQ 238 * qsNg lS iotaqF (xA 6) (xA 7) ≠ 0 := by
  intro h0
  have h := ballQ_all 240 (by norm_num)
  rw [show XQ 240 = Gq from rfl, Gq_eq, h0, zero_sub] at h
  have hc := h.norm_coeff_le le_rfl (0, 6)
  rw [coeff_neg, norm_neg, show xQ 240 = ctr SA NA MA (1, 0, 1) (gridPolyNM NA MA (gQ 240)) from rfl,
    coeff_ctr_grid, ite_eq_left (by norm_num [NA, MA])] at hc
  rw [show gQ 240 ((0 : ℤ) + NA).toNat ((6 : ℤ) + MA).toNat = 21539338154933775 by norm_num [NA, MA]; kernel_fact] at hc
  rw [norm_mul, norm_inv, norm_mul, norm_pow, Complex.norm_ofNat, norm_pow, Complex.norm_I, one_pow,
    mul_one, Complex.norm_intCast] at hc
  have h2 := (Rat.cast_lt (K := ℝ)).2 (show EQ 240 < |(21539338154933775 : ℚ)| / 2 ^ 64 by kernel_fact)
  rw [inv_mul_eq_div] at hc
  norm_num [SA] at hc h2
  linarith

end PlasmaLean.Design.DommaschkKamC
