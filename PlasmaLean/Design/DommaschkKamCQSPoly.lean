/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCQSData
public import PlasmaLean.Design.DommaschkKamIdentCheck
public import PlasmaLean.Design.DommaschkKamCTorus

/-!
# The polynomial form of the QA defect of the Dommaschk field on an invariant torus (N-34, D3)

N-34 (`notes/theory/dommaschk-qs-defect.md` §4) certifies the per-torus quasi-axisymmetry defect
`torusQADefect = ∂_{φ_B}|B|`, `∂_{φ_B} = [(1 + ι B·∂_θK)𝓛 − ι J ∂_θ]/J`, `J = B·𝓛K = |B|²/B^φ`,
on torus C of the Dommaschk certification field `dkFieldTC` through a polynomial formula in the
flow-form data `D = R⁷B_φ`, `n_R = R⁸B_R`, `n_z = R⁸B_z` (`Dp`, `nRp`, `nZp`; `Dp_ident`, …).
This file provides the formula and everything that makes it correct, except the link to the actual
defect function on the exact torus (module D6).

**The straight-line program** (`QSLeaves`; leaves: the values of `D, n_R, n_z`, their `∂_u`,
`∂_z`, `∂_φ`, and `R`):

    Q   = n_R² + R²D² + n_z²                                   (R¹⁶|B|² = Q)
    Q_u = 2(n_R n_{R,u} + R D² + R² D D_u + n_z n_{z,u}),
    Q_z = 2(n_R n_{R,z} + R² D D_z + n_z n_{z,z}),
    Q_φ = 2(n_R n_{R,φ} + R² D D_φ + n_z n_{z,φ}),
    P_L = Q_u n_R + Q_z n_z + D Q_φ,      M_L = R P_L − 16 Q n_R,
    N₀ = R⁸ M_L,   N₁ = n_R M_L − Q(R Q_u − 16 Q),   N₂ = n_z M_L − R Q Q_z,
    N_g = N₀ + ι (N₁ u_θ + N₂ z_θ).

**Results.**
* `qsDefectSq_eq` (field identity): on an invariant torus (`D 𝓛u = n_R`, `D 𝓛z = n_z`) with
  `a = (n_R u_θ + n_z z_θ)/R⁸`, `J = Q/(R⁸D)` and the chain-rule values of `𝓛(Q/R¹⁶)` and
  `∂_θ(Q/R¹⁶)`, `[(1 + ιa)𝓛|B|² − ιJ∂_θ|B|²]/J = N_g/(Q R¹⁷)`.
* `qsDefect_eq_of_sq`: the same for `|B|` (any `b` with `b² = Q/R¹⁶`, `2b𝓛b = 𝓛|B|²`,
  `2b∂_θb = ∂_θ|B|²`): `N_g/(2bQR¹⁷)`; `qsDefect_eq_real`: with `b = √Q/R⁸` (`R, Q > 0`),
  `torusQADefect = N_g/(2Q√Q R⁹)`.
* `normSq_flow`, `boozerJ_flow`, `boozerA_flow`: `|B|² = Q/R¹⁶`, `B·𝓛K = Q/(R⁸D)`,
  `B·∂_θK = (n_R u_θ + n_z z_θ)/R⁸` from the flow-form relations.
* The polynomial leaves: `Qp` (the polynomial expression of `Q` in `(u, z, c, s)`) with
  `eval_Qp`, `pd_Qp_U`, `pd_Qp_Z`, `phiD_Qp` (`∂_u Q = Q_u`, `∂_z Q = Q_z`, `∂_φQ = Q_φ` at the
  leaves `leavesAt x`), the leaf identities `pd_Dp_U`, …, `phiD_Dp`, …, and `dkFieldTC_polys`
  (the field polynomials of `dkFieldTC` are `Dp, nRp, nZp`).
* Kernel checks (`kernel_fact`) of the generated `φ`-derivative data of `DommaschkKamCQSData`:
  `dDf_eq` (`phiS dD = dDf`), `dnRf_eq`, `dnZf_eq`, the `R`-form `dDRf_eq`, `dnRhf_eq`,
  `dnZRf_eq`, and the substitution `R = R₀ + u` between the two forms: `substR_dDRf`,
  `substR_dnRhf`, `substR_dnZRf`.

The expanded polynomials are not used: `N₁, N₂` have about 44 000 terms in `(u, z, c, s)`
(17 000 in `(R, z, c, s)`), degree 72 in `u`, with 550-bit denominators
(`scripts/dommaschk_kam/emit_qs.py`, which also derives the formula with sympy, checks it exactly at
rational points against the expanded `Q`, and validates it on torus C against `qs_defect.py`).

**Sanity.** `Ng_toroidal` (degenerate: for `B = ∇φ`, `D = R⁶`, `n = 0`, the numerator vanishes
when `ι = 0` or `u_θ = z_θ = 0`), `qs_instance`, `qs_instance_lhs` (a concrete instance of
`qsDefectSq_eq`),
`qsDefectSq_needs_invariance` (rejected: without invariance the identity fails), `dDf_ne`.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.DommaschkKam DkPoly
open PlasmaLean.Design.KamNewton (pd phiD)

/-! ## Kernel checks of the `φ`-derivative data -/

/-- `∂_φD = dDf` (kernel check). -/
theorem dDf_eq : phiS dD = dDf := by kernel_fact
/-- `∂_φn_R = dnRf` (kernel check). -/
theorem dnRf_eq : phiS dnR = dnRf := by kernel_fact
/-- `∂_φn_z = dnZf` (kernel check). -/
theorem dnZf_eq : phiS dnZ = dnZf := by kernel_fact
/-- `R`-form: `∂_φD = dDRf` (kernel check). -/
theorem dDRf_eq : phiS dDR = dDRf := by kernel_fact
/-- `R`-form: `∂_φ(n_R/R) = dnRhf` (kernel check). -/
theorem dnRhf_eq : phiS dnRh = dnRhf := by kernel_fact
/-- `R`-form: `∂_φn_z = dnZRf` (kernel check). -/
theorem dnZRf_eq : phiS dnZR = dnZRf := by kernel_fact
/-- The `R`-form `∂_φD` becomes the `u`-form one under `R = R₀ + u` (kernel check). -/
theorem substR_dDRf : substR dDRf = dDf := by kernel_fact
/-- The `R`-form `∂_φn_R = R ∂_φ(n_R/R)` becomes the `u`-form one (kernel check). -/
theorem substR_dnRhf : substR (mulMono ⟨1, 1, 0, 0, 0⟩ dnRhf) = dnRf := by kernel_fact
/-- The `R`-form `∂_φn_z` becomes the `u`-form one (kernel check). -/
theorem substR_dnZRf : substR dnZRf = dnZf := by kernel_fact

/-- **Sanity (rejected fixture)**: `∂_φD` is not the empty sum (the field is not axisymmetric). -/
theorem dDf_ne : dDf ≠ [] := by
  have h : dDf.length = 337 := by kernel_fact
  intro h0
  rw [h0] at h
  simp at h

/-- The field polynomials of `dkFieldTC` are `Dp`, `nRp`, `nZp`. -/
theorem dkFieldTC_polys : dkFieldTC.Dp = Dp ∧ dkFieldTC.nRp = nRp ∧ dkFieldTC.nZp = nZp :=
  ⟨rfl, rfl, rfl⟩

/-! ## The straight-line program -/

/-- The leaves of the QA-defect numerator: the values of `D, n_R, n_z`, their partial derivatives
`∂_u, ∂_z`, their `φ`-derivatives, and `R`. -/
structure QSLeaves (A : Type*) where
  /-- `D = R⁷B_φ`. -/
  D : A
  /-- `∂_u D`. -/
  Du : A
  /-- `∂_z D`. -/
  Dz : A
  /-- `∂_φ D`. -/
  Df : A
  /-- `n_R = R⁸B_R`. -/
  nR : A
  /-- `∂_u n_R`. -/
  nRu : A
  /-- `∂_z n_R`. -/
  nRz : A
  /-- `∂_φ n_R`. -/
  nRf : A
  /-- `n_z = R⁸B_z`. -/
  nZ : A
  /-- `∂_u n_z`. -/
  nZu : A
  /-- `∂_z n_z`. -/
  nZz : A
  /-- `∂_φ n_z`. -/
  nZf : A
  /-- `R = R₀ + u`. -/
  R : A

namespace QSLeaves

variable {A : Type*} [CommRing A] (l : QSLeaves A)

/-- `Q = n_R² + R²D² + n_z²` (`= R¹⁶|B|²`). -/
def Q : A := l.nR ^ 2 + l.R ^ 2 * l.D ^ 2 + l.nZ ^ 2
/-- `Q_u = ∂_u Q` by the product rule (`∂_u R = 1`). -/
def Qu : A := 2 * (l.nR * l.nRu + l.R * l.D ^ 2 + l.R ^ 2 * (l.D * l.Du) + l.nZ * l.nZu)
/-- `Q_z = ∂_z Q`. -/
def Qz : A := 2 * (l.nR * l.nRz + l.R ^ 2 * (l.D * l.Dz) + l.nZ * l.nZz)
/-- `Q_φ = ∂_φ Q`. -/
def Qf : A := 2 * (l.nR * l.nRf + l.R ^ 2 * (l.D * l.Df) + l.nZ * l.nZf)
/-- `P_L = Q_u n_R + Q_z n_z + D Q_φ` (`= D 𝓛Q` on an invariant torus). -/
def PL : A := l.Qu * l.nR + l.Qz * l.nZ + l.D * l.Qf
/-- `M_L = R P_L − 16 Q n_R` (`= R¹⁷ D 𝓛|B|²` on an invariant torus). -/
def ML : A := l.R * l.PL - 16 * l.Q * l.nR
/-- `N₀ = R⁸ M_L`. -/
def N0 : A := l.R ^ 8 * l.ML
/-- `N₁ = n_R M_L − Q(R Q_u − 16 Q)` (the coefficient of `ι u_θ`). -/
def N1 : A := l.nR * l.ML - l.Q * (l.R * l.Qu - 16 * l.Q)
/-- `N₂ = n_z M_L − R Q Q_z` (the coefficient of `ι z_θ`). -/
def N2 : A := l.nZ * l.ML - l.R * l.Q * l.Qz
/-- **The QA-defect numerator** `N_g = N₀ + ι(N₁ u_θ + N₂ z_θ)`: `∂_{φ_B}|B|² = N_g/(Q R¹⁷)`. -/
def Ng (ι uθ zθ : A) : A := l.N0 + ι * (l.N1 * uθ + l.N2 * zθ)

end QSLeaves

/-! ## The algebraic identities -/

section Field

variable {K : Type*} [Field K]

/-- **`|B|²` in flow form**: with `n_R = R⁸B_R`, `D = R⁷B_φ`, `n_z = R⁸B_z`, `|B|² = Q/R¹⁶`. -/
theorem normSq_flow (l : QSLeaves K) (BR BP BZ : K) (hR : l.R ≠ 0) (hnR : l.nR = l.R ^ 8 * BR)
    (hD : l.D = l.R ^ 7 * BP) (hnZ : l.nZ = l.R ^ 8 * BZ) :
    BR ^ 2 + BP ^ 2 + BZ ^ 2 = l.Q / l.R ^ 16 := by
  rw [QSLeaves.Q, hnR, hD, hnZ]
  field_simp

/-- **The Boozer Jacobian in flow form**: with `𝓛K = 𝓛u e_R + R e_φ + 𝓛z e_z` and invariance
`D 𝓛u = n_R`, `D 𝓛z = n_z`, `J = B·𝓛K = Q/(R⁸D)`. -/
theorem boozerJ_flow (l : QSLeaves K) (BR BP BZ Lu Lz : K) (hR : l.R ≠ 0) (hD0 : l.D ≠ 0)
    (hnR : l.nR = l.R ^ 8 * BR) (hD : l.D = l.R ^ 7 * BP) (hnZ : l.nZ = l.R ^ 8 * BZ)
    (hLu : l.D * Lu = l.nR) (hLz : l.D * Lz = l.nZ) :
    BR * Lu + BP * l.R + BZ * Lz = l.Q / (l.R ^ 8 * l.D) := by
  have hLu' : Lu = l.nR / l.D := by field_simp; linear_combination hLu
  have hLz' : Lz = l.nZ / l.D := by field_simp; linear_combination hLz
  have hBR : BR = l.nR / l.R ^ 8 := by field_simp; linear_combination -hnR
  have hBP : BP = l.D / l.R ^ 7 := by field_simp; linear_combination -hD
  have hBZ : BZ = l.nZ / l.R ^ 8 := by field_simp; linear_combination -hnZ
  rw [hLu', hLz', hBR, hBP, hBZ, QSLeaves.Q]
  field_simp

/-- **The covariant `θ`-component in flow form**: `a = B·∂_θK = (n_R u_θ + n_z z_θ)/R⁸`
(`∂_θK = u_θ e_R + z_θ e_z`). -/
theorem boozerA_flow (l : QSLeaves K) (BR BZ uθ zθ : K) (hR : l.R ≠ 0)
    (hnR : l.nR = l.R ^ 8 * BR) (hnZ : l.nZ = l.R ^ 8 * BZ) :
    BR * uθ + BZ * zθ = (l.nR * uθ + l.nZ * zθ) / l.R ^ 8 := by
  rw [hnR, hnZ]
  field_simp

/-- **The QA-defect identity for `|B|²`** (the algebraic core of N-34 §4). On an invariant torus
(`D 𝓛u = n_R`, `D 𝓛z = n_z`), with `a = (n_R u_θ + n_z z_θ)/R⁸`, `J = Q/(R⁸D)`, and the
chain-rule values `𝓛(Q/R¹⁶) = (Q_u 𝓛u + Q_z 𝓛z + Q_φ)/R¹⁶ − 16Q𝓛u/R¹⁷`,
`∂_θ(Q/R¹⁶) = (Q_u u_θ + Q_z z_θ)/R¹⁶ − 16Q u_θ/R¹⁷`:
`[(1 + ιa)𝓛|B|² − ιJ∂_θ|B|²]/J = N_g/(Q R¹⁷)`. -/
theorem qsDefectSq_eq (l : QSLeaves K) (ι uθ zθ Lu Lz : K) (hR : l.R ≠ 0) (hD : l.D ≠ 0)
    (hQ : l.Q ≠ 0) (hLu : l.D * Lu = l.nR) (hLz : l.D * Lz = l.nZ) :
    ((1 + ι * ((l.nR * uθ + l.nZ * zθ) / l.R ^ 8)) *
          ((l.Qu * Lu + l.Qz * Lz + l.Qf) / l.R ^ 16 - 16 * l.Q * Lu / l.R ^ 17) -
        ι * (l.Q / (l.R ^ 8 * l.D)) *
          ((l.Qu * uθ + l.Qz * zθ) / l.R ^ 16 - 16 * l.Q * uθ / l.R ^ 17)) /
        (l.Q / (l.R ^ 8 * l.D)) =
      l.Ng ι uθ zθ / (l.Q * l.R ^ 17) := by
  have hLu' : Lu = l.nR / l.D := by field_simp; linear_combination hLu
  have hLz' : Lz = l.nZ / l.D := by field_simp; linear_combination hLz
  rw [hLu', hLz']
  simp only [QSLeaves.Ng, QSLeaves.N0, QSLeaves.N1, QSLeaves.N2, QSLeaves.ML, QSLeaves.PL]
  field_simp
  ring

/-- **The QA-defect identity for `|B|`** (the definition `torusQADefect` of N-34 §2): for any `b`
with `b² = Q/R¹⁶`, `b ≠ 0`, and derivatives `Lb`, `tb` with `2b·Lb = 𝓛|B|²`, `2b·tb = ∂_θ|B|²`
(the chain-rule values above), `[(1 + ιa)Lb − ιJ·tb]/J = N_g/(2bQR¹⁷)`. -/
theorem qsDefect_eq_of_sq [CharZero K] (l : QSLeaves K) (ι uθ zθ Lu Lz b Lb tb : K) (hR : l.R ≠ 0)
    (hD : l.D ≠ 0) (hQ : l.Q ≠ 0) (hb : b ≠ 0) (hLu : l.D * Lu = l.nR) (hLz : l.D * Lz = l.nZ)
    (hLb : 2 * b * Lb = (l.Qu * Lu + l.Qz * Lz + l.Qf) / l.R ^ 16 - 16 * l.Q * Lu / l.R ^ 17)
    (htb : 2 * b * tb = (l.Qu * uθ + l.Qz * zθ) / l.R ^ 16 - 16 * l.Q * uθ / l.R ^ 17) :
    ((1 + ι * ((l.nR * uθ + l.nZ * zθ) / l.R ^ 8)) * Lb -
        ι * (l.Q / (l.R ^ 8 * l.D)) * tb) / (l.Q / (l.R ^ 8 * l.D)) =
      l.Ng ι uθ zθ / (2 * b * l.Q * l.R ^ 17) := by
  have h := qsDefectSq_eq l ι uθ zθ Lu Lz hR hD hQ hLu hLz
  rw [← hLb, ← htb] at h
  have h2 : (2 : K) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hJ : l.Q / (l.R ^ 8 * l.D) ≠ 0 := div_ne_zero hQ (mul_ne_zero (pow_ne_zero _ hR) hD)
  rw [show l.Ng ι uθ zθ / (2 * b * l.Q * l.R ^ 17) =
      l.Ng ι uθ zθ / (l.Q * l.R ^ 17) / (2 * b) by field_simp, ← h]
  field_simp

/-- **The real form**: with `R, Q > 0` and `|B| = √Q/R⁸`,
`torusQADefect = N_g/(2Q√Q R⁹)`. -/
theorem qsDefect_eq_real (l : QSLeaves ℝ) (ι uθ zθ Lu Lz Lb tb : ℝ) (hR : 0 < l.R)
    (hD : l.D ≠ 0) (hQ : 0 < l.Q) (hLu : l.D * Lu = l.nR) (hLz : l.D * Lz = l.nZ)
    (hLb : 2 * (Real.sqrt l.Q / l.R ^ 8) * Lb =
      (l.Qu * Lu + l.Qz * Lz + l.Qf) / l.R ^ 16 - 16 * l.Q * Lu / l.R ^ 17)
    (htb : 2 * (Real.sqrt l.Q / l.R ^ 8) * tb =
      (l.Qu * uθ + l.Qz * zθ) / l.R ^ 16 - 16 * l.Q * uθ / l.R ^ 17) :
    ((1 + ι * ((l.nR * uθ + l.nZ * zθ) / l.R ^ 8)) * Lb -
        ι * (l.Q / (l.R ^ 8 * l.D)) * tb) / (l.Q / (l.R ^ 8 * l.D)) =
      l.Ng ι uθ zθ / (2 * l.Q * Real.sqrt l.Q * l.R ^ 9) := by
  have hs : 0 < Real.sqrt l.Q := Real.sqrt_pos.2 hQ
  have hb : Real.sqrt l.Q / l.R ^ 8 ≠ 0 := (div_pos hs (pow_pos hR 8)).ne'
  rw [qsDefect_eq_of_sq l ι uθ zθ Lu Lz _ Lb tb hR.ne' hD hQ.ne' hb hLu hLz hLb htb]
  have : l.R ≠ 0 := hR.ne'
  field_simp

/-- `|B| = √Q/R⁸` satisfies `b² = Q/R¹⁶`. -/
theorem sqrtQ_sq (Q R : ℝ) (hQ : 0 ≤ Q) :
    (Real.sqrt Q / R ^ 8) ^ 2 = Q / R ^ 16 := by
  rw [div_pow, Real.sq_sqrt hQ, ← pow_mul]

end Field

/-! ## The polynomial leaves -/

section Leaves

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- The leaves at a point `x` of `(u, z, c, s, ·, ·)`: the sparse polynomials `D, n_R, n_z`, their
formal `∂_u`, `∂_z`, the generated `φ`-derivatives `dDf, dnRf, dnZf`, and `R = R₀ + u`. -/
noncomputable def leavesAt (x : Fin 6 → A) : QSLeaves A where
  D := ev x dD
  Du := ev x (dU dD)
  Dz := ev x (dZ dD)
  Df := ev x dDf
  nR := ev x dnR
  nRu := ev x (dU dnR)
  nRz := ev x (dZ dnR)
  nRf := ev x dnRf
  nZ := ev x dnZ
  nZu := ev x (dU dnZ)
  nZz := ev x (dZ dnZ)
  nZf := ev x dnZf
  R := ev x Rl

/-- `R = R₀ + u` as a polynomial expression. -/
noncomputable def Rp : PolyExpr ℂ (Fin 6) := toPE Rl

/-- `Q = n_R² + R²D² + n_z²` as a polynomial expression in `(u, z, c, s)` (not expanded). -/
noncomputable def Qp : PolyExpr ℂ (Fin 6) :=
  .add (.add (.mul nRp nRp) (.mul (.mul Rp Rp) (.mul Dp Dp))) (.mul nZp nZp)

/-- `∂_u D` at the leaves. -/
theorem pd_Dp_U (x : Fin 6 → A) : pd x 0 Dp = (leavesAt x).Du := pd_toPE_U x dD
/-- `∂_z D` at the leaves. -/
theorem pd_Dp_Z (x : Fin 6 → A) : pd x 1 Dp = (leavesAt x).Dz := pd_toPE_Z x dD
/-- `∂_φ D` at the leaves (through the kernel check `dDf_eq`). -/
theorem phiD_Dp (x : Fin 6 → A) : phiD x Dp = (leavesAt x).Df := by
  rw [Dp, phiD_toPE, dDf_eq]; rfl
/-- `∂_u n_R` at the leaves. -/
theorem pd_nRp_U (x : Fin 6 → A) : pd x 0 nRp = (leavesAt x).nRu := pd_toPE_U x dnR
/-- `∂_z n_R` at the leaves. -/
theorem pd_nRp_Z (x : Fin 6 → A) : pd x 1 nRp = (leavesAt x).nRz := pd_toPE_Z x dnR
/-- `∂_φ n_R` at the leaves (through `dnRf_eq`). -/
theorem phiD_nRp (x : Fin 6 → A) : phiD x nRp = (leavesAt x).nRf := by
  rw [nRp, phiD_toPE, dnRf_eq]; rfl
/-- `∂_u n_z` at the leaves. -/
theorem pd_nZp_U (x : Fin 6 → A) : pd x 0 nZp = (leavesAt x).nZu := pd_toPE_U x dnZ
/-- `∂_z n_z` at the leaves. -/
theorem pd_nZp_Z (x : Fin 6 → A) : pd x 1 nZp = (leavesAt x).nZz := pd_toPE_Z x dnZ
/-- `∂_φ n_z` at the leaves (through `dnZf_eq`). -/
theorem phiD_nZp (x : Fin 6 → A) : phiD x nZp = (leavesAt x).nZf := by
  rw [nZp, phiD_toPE, dnZf_eq]; rfl

/-- The values of `D, n_R, n_z, R` at the leaves. -/
theorem eval_leaves (x : Fin 6 → A) :
    PolyExpr.eval x Dp = (leavesAt x).D ∧ PolyExpr.eval x nRp = (leavesAt x).nR ∧
      PolyExpr.eval x nZp = (leavesAt x).nZ ∧ PolyExpr.eval x Rp = (leavesAt x).R :=
  ⟨eval_toPE x dD, eval_toPE x dnR, eval_toPE x dnZ, eval_toPE x Rl⟩

/-- `∂_u R = 1`. -/
theorem pd_Rp_U (x : Fin 6 → A) : pd x 0 Rp = 1 := by
  rw [Rp, pd_toPE_U]; simp [Rl, dU, Tm.dU, Tm.ev]

/-- `∂_z R = 0`. -/
theorem pd_Rp_Z (x : Fin 6 → A) : pd x 1 Rp = 0 := by
  rw [Rp, pd_toPE_Z]; simp [Rl, dZ, Tm.dZ]

/-- `∂_φ R = 0`. -/
theorem phiD_Rp (x : Fin 6 → A) : phiD x Rp = 0 := by
  rw [Rp, phiD_toPE]; simp [Rl, phiS, dC, DkPoly.dS, Tm.dC, Tm.dS, merge, mergeF, mulMono]

/-- The partial derivative of a product. -/
theorem pd_mul (x : Fin 6 → A) (i : Fin 6) (p q : PolyExpr ℂ (Fin 6)) :
    pd x i (.mul p q) = pd x i p * PolyExpr.eval x q + PolyExpr.eval x p * pd x i q := rfl

/-- The partial derivative of a sum. -/
theorem pd_add (x : Fin 6 → A) (i : Fin 6) (p q : PolyExpr ℂ (Fin 6)) :
    pd x i (.add p q) = pd x i p + pd x i q := rfl

/-- **`Q` at the leaves.** -/
theorem eval_Qp (x : Fin 6 → A) : PolyExpr.eval x Qp = (leavesAt x).Q := by
  obtain ⟨h1, h2, h3, h4⟩ := eval_leaves x
  simp only [Qp, PolyExpr.eval, h1, h2, h3, h4, QSLeaves.Q]
  ring

/-- **`∂_u Q = Q_u`** at the leaves (the product rule of the straight-line program). -/
theorem pd_Qp_U (x : Fin 6 → A) : pd x 0 Qp = (leavesAt x).Qu := by
  obtain ⟨h1, h2, h3, h4⟩ := eval_leaves x
  simp only [Qp, pd_add, pd_mul, PolyExpr.eval, h1, h2, h3, h4,
    pd_Dp_U, pd_nRp_U, pd_nZp_U, pd_Rp_U,
    QSLeaves.Qu]
  ring

/-- **`∂_z Q = Q_z`** at the leaves. -/
theorem pd_Qp_Z (x : Fin 6 → A) : pd x 1 Qp = (leavesAt x).Qz := by
  obtain ⟨h1, h2, h3, h4⟩ := eval_leaves x
  simp only [Qp, pd_add, pd_mul, PolyExpr.eval, h1, h2, h3, h4,
    pd_Dp_Z, pd_nRp_Z, pd_nZp_Z, pd_Rp_Z,
    QSLeaves.Qz]
  ring

/-- `phiD` of a product. -/
theorem phiD_mul (x : Fin 6 → A) (p q : PolyExpr ℂ (Fin 6)) :
    phiD x (.mul p q) = phiD x p * PolyExpr.eval x q + PolyExpr.eval x p * phiD x q := by
  simp only [phiD, pd_mul]; ring

/-- `phiD` of a sum. -/
theorem phiD_add (x : Fin 6 → A) (p q : PolyExpr ℂ (Fin 6)) :
    phiD x (.add p q) = phiD x p + phiD x q := by
  simp only [phiD, pd_add]; ring

/-- **`∂_φQ = Q_φ`** at the leaves. -/
theorem phiD_Qp (x : Fin 6 → A) : phiD x Qp = (leavesAt x).Qf := by
  obtain ⟨h1, h2, h3, h4⟩ := eval_leaves x
  simp only [Qp, phiD_add, phiD_mul, PolyExpr.eval, h1, h2, h3, h4,
    phiD_Dp, phiD_nRp, phiD_nZp, phiD_Rp,
    QSLeaves.Qf]
  ring

end Leaves

/-! ## Sanity -/

/-- **Sanity (degenerate case)**: for the vacuum field `B = ∇φ` (`D = R⁶`, `n_R = n_z = 0`, no
`φ`-dependence) the numerator is `N_g = ι·2R²⁸u_θ`; it vanishes for `ι = 0` and for
`u_θ = z_θ = 0` (`|B| = 1/R` is constant on circles `R = const`). -/
theorem Ng_toroidal {A : Type*} [CommRing A] (R ι uθ zθ : A) :
    (QSLeaves.mk (R ^ 6) (6 * R ^ 5) 0 0 0 0 0 0 0 0 0 0 R).Ng ι uθ zθ =
      ι * (2 * R ^ 28 * uθ) := by
  simp only [QSLeaves.Ng, QSLeaves.N0, QSLeaves.N1, QSLeaves.N2, QSLeaves.ML, QSLeaves.PL,
    QSLeaves.Q, QSLeaves.Qu, QSLeaves.Qz, QSLeaves.Qf]
  ring

/-- **Sanity (concrete instance)** of `qsDefectSq_eq`: `R = 1`, `D = 1`, `n_R = 1`, `n_z = 0`, all
derivatives `0`, `𝓛u = 1`, `u_θ = z_θ = 0`, `ι = 1/2`: both sides are `−15`
(`Q = 2`, `Q_u = 2`, `P_L = 2`, `M_L = −30`, `N_g = −30`). -/
theorem qs_instance :
    (QSLeaves.mk (1 : ℚ) 0 0 0 1 0 0 0 0 0 0 0 1).Ng (1 / 2) 0 0 /
        ((QSLeaves.mk (1 : ℚ) 0 0 0 1 0 0 0 0 0 0 0 1).Q * 1 ^ 17) = -15 := by
  norm_num [QSLeaves.Ng, QSLeaves.N0, QSLeaves.N1, QSLeaves.N2, QSLeaves.ML, QSLeaves.PL,
    QSLeaves.Q, QSLeaves.Qu, QSLeaves.Qz, QSLeaves.Qf]

/-- **Sanity (accepted instance)**: the left side of `qsDefectSq_eq` at the leaves of
`qs_instance` with the invariant `𝓛u = 1` is `−15`, through the identity. -/
theorem qs_instance_lhs :
    let l : QSLeaves ℚ := QSLeaves.mk 1 0 0 0 1 0 0 0 0 0 0 0 1
    ((1 + (1 / 2) * ((l.nR * 0 + l.nZ * 0) / l.R ^ 8)) *
          ((l.Qu * 1 + l.Qz * 0 + l.Qf) / l.R ^ 16 - 16 * l.Q * 1 / l.R ^ 17) -
        (1 / 2) * (l.Q / (l.R ^ 8 * l.D)) *
          ((l.Qu * 0 + l.Qz * 0) / l.R ^ 16 - 16 * l.Q * 0 / l.R ^ 17)) /
        (l.Q / (l.R ^ 8 * l.D)) = -15 := by
  intro l
  rw [qsDefectSq_eq l (1 / 2) 0 0 1 0 (by norm_num [l]) (by norm_num [l])
    (by norm_num [l, QSLeaves.Q]) (by norm_num [l]) (by norm_num [l])]
  exact qs_instance

/-- **Sanity (rejected fixture)**: the invariance hypothesis is needed. With the leaves of
`qs_instance` but `𝓛u = 0` (so `D 𝓛u ≠ n_R`), the left side of `qsDefectSq_eq` is `0`, not `−15`. -/
theorem qsDefectSq_needs_invariance :
    let l : QSLeaves ℚ := QSLeaves.mk 1 0 0 0 1 0 0 0 0 0 0 0 1
    ((1 + (1 / 2) * ((l.nR * 0 + l.nZ * 0) / l.R ^ 8)) *
          ((l.Qu * 0 + l.Qz * 0 + l.Qf) / l.R ^ 16 - 16 * l.Q * 0 / l.R ^ 17) -
        (1 / 2) * (l.Q / (l.R ^ 8 * l.D)) *
          ((l.Qu * 0 + l.Qz * 0) / l.R ^ 16 - 16 * l.Q * 0 / l.R ^ 17)) /
        (l.Q / (l.R ^ 8 * l.D)) ≠ l.Ng (1 / 2) 0 0 / (l.Q * l.R ^ 17) := by
  norm_num [QSLeaves.Ng, QSLeaves.N0, QSLeaves.N1, QSLeaves.N2, QSLeaves.ML, QSLeaves.PL,
    QSLeaves.Q, QSLeaves.Qu, QSLeaves.Qz, QSLeaves.Qf]

end PlasmaLean.Design.DommaschkKamC
