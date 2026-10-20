/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.StripEval

/-!
# The field of the rational stellarator in the strip algebra (KAM route, K3d)

The flow form of the field-line equations of `field (1/4)` (`Design/KamTorusA`) for a torus
`K = (R, z) = (1 + u, z)` is `D(K, φ)·𝓛K = n(K, φ)` with `𝓛 = ∂_φ + ι∂_θ` and polynomials
`D, n_R, n_z` in `u, z, c = cos 2φ, s = sin 2φ`. This file sets these objects up in the strip
algebra `𝔸` (`Theory/KAM/StripAlgebra`):

* the trigonometric elements `cS = cos 2φ = −sin ψ`, `sS = sin 2φ = cos ψ` (`ψ = 2φ − π/2`) with
  `dS a b sS = b cS`, `dS a b cS = −b sS`, and the operators `dTh = ∂_θ`, `dPh = ∂_φ = 2∂_ψ`,
  `Lt ι = 𝓛 = ι∂_θ + ∂_φ`;
* the polynomials in **monomial form in `u = R − 1`** (so that the majorants see the
  cancellations near the magnetic axis): `Dp` (`D = R²(1 + ε∂_φh)`), `nRp = 2εR·Ps`,
  `nZp = εR²·Pz`, the residuals `resRp = D w_R − n_R`, `resZp = D w_z − n_z`, the flux primitive
  numerators `Pap`, `Pbp`, and the torsion numerator `Pp`;
* the **polynomial identities** on which the Newton step rests, proved pointwise in `ℂ` and
  transported to `𝔸` by uniqueness of Fourier coefficients (`ext_eval`):
  - `divFree`: `R ∂_φD − 3 n_R + R ∂_u n_R + R ∂_z n_z = 0` (the flux form `(D/R³) dR∧dz` is
    invariant: `div B = 0`);
  - `flux_a`, `flux_b`, `flux_c`: the 1-form `α = a dR + b dz`, `a = P_a/R`, `b = P_b/R²`, is a
    primitive of the flux 2-form `β = w (dR − X_R dφ) ∧ (dz − X_z dφ)`, `w = D/R³`;
  - `torsion_poly`: `P = (n_R D − D ∇n_R·V₀ + n_R ∇D·V₀) z − (n_z D − D ∇n_z·V₀ + n_z ∇D·V₀) u`.

**Sanity.** `eval_sS`, `eval_cS` (the elements are the trigonometric functions), `Dp_axis`
(`D = 1` on the magnetic axis `u = z = 0`), `nRp_axis` (`X = 0` on the axis).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PolyExpr Complex WEll1Z2

/-! ## Operators and the trigonometric elements -/

/-- `∂_θ`. -/
def dTh (x : FA) : FA := dS 1 0 x

/-- `∂_φ = 2 ∂_ψ` (`ψ = 2φ − π/2`). -/
def dPh (x : FA) : FA := dS 0 2 x

/-- The transport `𝓛 = ∂_φ + ι ∂_θ` of the flow form. -/
def Lt (ι : ℝ) (x : FA) : FA := dS ι 2 x

/-- `𝓛 = ι ∂_θ + ∂_φ` on analytic elements. -/
theorem Lt_eq (ι : ℝ) {x : FA} (hx : Ana x) : Lt ι x = (ι : ℂ) • dTh x + dPh x := by
  have h1 := dS_add_symbol (ι : ℂ) 0 0 2 hx
  simp only [add_zero, zero_add] at h1
  rw [Lt, h1, dTh, dPh]
  congr 1
  have := dS_smul_symbol 1 0 (ι : ℂ) hx
  simpa using this

/-- `𝓛 = 2 (∂_ψ + (ι/2) ∂_θ)`. -/
theorem Lt_eq_two (ι : ℝ) {x : FA} (hx : Ana x) : Lt ι x = (2 : ℂ) • dS ((ι / 2 : ℝ)) 1 x := by
  rw [Lt, ← dS_smul_symbol _ _ _ hx]; congr 1 <;> push_cast <;> ring

/-- A mode is analytic, with `‖e^{i(kθ+mψ)}‖_ρ = e^{ρ(|k|+|m|)}`. -/
theorem Bd_mode (ρ : ℝ) (km : ℤ × ℤ) : Bd ρ (mode 0 km) (weight ρ km) := by
  refine ⟨?_, ?_⟩
  · unfold InWeighted
    exact summable_of_ne_finset_zero (s := {km}) fun n hn => by
      simp [Finset.mem_singleton.not.1 hn]
  · rw [wnorm, tsum_eq_single km (fun n hn => by simp [hn])]; simp

/-- Modes are analytic. -/
theorem ana_mode (km : ℤ × ℤ) : Ana (mode 0 km) := ⟨1, _, one_pos, Bd_mode 1 km⟩

/-- `dS a b` on a mode: multiplication by `i (a k + b m)`. -/
theorem dS_mode' (a b : ℂ) (km : ℤ × ℤ) :
    dS a b (mode 0 km) = (I * (a * km.1 + b * km.2)) • mode 0 km :=
  ext_coeff fun n => by
    rw [(ana_mode km).coeff_dS, coeff_smul]
    by_cases h : n = km
    · subst h; simp [dsym]
    · simp [dsym, h]

/-- `sin 2φ = cos ψ` as an element of `𝔸`. -/
def sS : FA := (1 / 2 : ℂ) • (mode 0 (0, 1) + mode 0 (0, -1))

/-- `cos 2φ = −sin ψ` as an element of `𝔸`. -/
def cS : FA := (I / 2) • (mode 0 (0, 1) - mode 0 (0, -1))

/-- `sS` is analytic. -/
theorem ana_sS : Ana sS := ((ana_mode _).add (ana_mode _)).smul _

/-- `cS` is analytic. -/
theorem ana_cS : Ana cS := ((ana_mode _).sub (ana_mode _)).smul _

/-- `‖sS‖_ρ ≤ e^ρ`. -/
theorem Bd_sS (ρ : ℝ) : Bd ρ sS (Real.exp ρ) := by
  have h := ((Bd_mode ρ (0, 1)).add (Bd_mode ρ (0, -1))).smul (1 / 2 : ℂ)
  refine h.le (le_of_eq ?_)
  simp [weight, modeSize]; ring

/-- `‖cS‖_ρ ≤ e^ρ`. -/
theorem Bd_cS (ρ : ℝ) : Bd ρ cS (Real.exp ρ) := by
  have h := ((Bd_mode ρ (0, 1)).sub (Bd_mode ρ (0, -1))).smul (I / 2)
  refine h.le (le_of_eq ?_)
  simp [weight, modeSize]; ring

/-- `dS a b sS = b cS`. -/
theorem dS_sS (a b : ℂ) : dS a b sS = b • cS := by
  rw [sS, dS_smul _ _ _ ((ana_mode _).add (ana_mode _)), dS_add _ _ (ana_mode _) (ana_mode _),
    dS_mode', dS_mode', cS]
  simp only [smul_add, smul_sub, smul_smul]
  push_cast
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2 <;> ring

/-- `dS a b cS = −b sS`. -/
theorem dS_cS (a b : ℂ) : dS a b cS = -(b • sS) := by
  rw [cS, dS_smul _ _ _ ((ana_mode _).sub (ana_mode _)), dS_sub _ _ (ana_mode _) (ana_mode _),
    dS_mode', dS_mode', sS]
  simp only [smul_add, smul_sub, smul_smul]
  push_cast
  rw [sub_eq_add_neg, ← neg_smul, neg_add, ← neg_smul, ← neg_smul]
  congr 2
  · ring_nf; rw [I_sq]; ring
  · ring_nf; rw [I_sq]; ring

/-- Sanity: `sS` is the function `cos ψ`. -/
theorem eval_sS (θ ψ : ℝ) : eval sS θ ψ = Real.cos ψ := by
  rw [sS, eval_smul', eval_add', eval_mode, eval_mode]
  simp only [fourierMode, Complex.ofReal_cos]
  rw [Complex.cos]
  push_cast; ring_nf

/-- Sanity: `cS` is the function `−sin ψ`. -/
theorem eval_cS (θ ψ : ℝ) : eval cS θ ψ = -Real.sin ψ := by
  rw [cS, eval_smul', eval_sub', eval_mode, eval_mode]
  simp only [fourierMode, Complex.ofReal_sin]
  rw [Complex.sin]
  push_cast; ring_nf

/-- `sS` is real. -/
theorem isReal_sS : IsReal sS :=
  (isReal_iff_eval _).2 fun θ ψ => by rw [eval_sS, Complex.conj_ofReal]

/-- `cS` is real. -/
theorem isReal_cS : IsReal cS :=
  (isReal_iff_eval _).2 fun θ ψ => by
    rw [eval_cS, map_neg, Complex.conj_ofReal]

/-- `∂_θ` kills `sS`. -/
theorem dTh_sS : dTh sS = 0 := by rw [dTh, dS_sS]; simp
/-- `∂_θ` kills `cS`. -/
theorem dTh_cS : dTh cS = 0 := by rw [dTh, dS_cS]; simp
/-- `∂_φ sin 2φ = 2 cos 2φ`. -/
theorem dPh_sS : dPh sS = (2 : ℂ) • cS := by rw [dPh, dS_sS]
/-- `∂_φ cos 2φ = −2 sin 2φ`. -/
theorem dPh_cS : dPh cS = -((2 : ℂ) • sS) := by rw [dPh, dS_cS]
/-- `𝓛 sin 2φ = 2 cos 2φ`. -/
theorem Lt_sS (ι : ℝ) : Lt ι sS = (2 : ℂ) • cS := by rw [Lt, dS_sS]
/-- `𝓛 cos 2φ = −2 sin 2φ`. -/
theorem Lt_cS (ι : ℝ) : Lt ι cS = -((2 : ℂ) • sS) := by rw [Lt, dS_cS]

/-! ## The polynomials (monomial form in `u = R − 1, z, c, s`; variables `w_R, w_z` are `4, 5`) -/

/-- Sum of a list of expressions. -/
def sumE {σ : Type*} : List (PolyExpr ℂ σ) → PolyExpr ℂ σ
  | [] => const 0
  | e :: es => add e (sumE es)

/-- The monomial `c ∏ x_i^{k_i}`. -/
def monoE {σ : Type*} (c : ℂ) : List (σ × ℕ) → PolyExpr ℂ σ
  | [] => const c
  | (i, k) :: l => mul (monoE c l) (npow (var i) k)

/-- `D = R²(1 + ε∂_φh)` in monomial form in `u = R − 1, z, c = cos 2φ, s = sin 2φ`. -/
def Dp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/8) [(0, 4), (1, 1), (2, 1)],
    monoE (-1/8) [(0, 4), (3, 1)],
    monoE (-1/2) [(0, 3), (1, 1), (2, 1)],
    monoE (-1/2) [(0, 3), (3, 1)],
    monoE (-1/2) [(0, 2), (3, 1)],
    monoE (1) [(0, 2)],
    monoE (1) [(0, 1), (1, 1), (2, 1)],
    monoE (2) [(0, 1)],
    monoE (1/2) [(1, 3), (2, 1)],
    monoE (1/2) [(1, 2), (3, 1)],
    monoE (1) []]

/-- The numerator `2εR Ps` of `X_R`, monomial form in `u, z, c, s`. -/
def nRp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/8) [(0, 5), (1, 1), (3, 1)],
    monoE (1/8) [(0, 5), (2, 1)],
    monoE (-5/8) [(0, 4), (1, 1), (3, 1)],
    monoE (5/8) [(0, 4), (2, 1)],
    monoE (-5/4) [(0, 3), (1, 1), (3, 1)],
    monoE (5/4) [(0, 3), (2, 1)],
    monoE (-5/4) [(0, 2), (1, 1), (3, 1)],
    monoE (5/4) [(0, 2), (2, 1)],
    monoE (-1/2) [(0, 1), (1, 3), (3, 1)],
    monoE (1/2) [(0, 1), (1, 2), (2, 1)],
    monoE (1/2) [(0, 1), (2, 1)],
    monoE (-1/2) [(1, 3), (3, 1)],
    monoE (1/2) [(1, 2), (2, 1)],
    monoE (1/2) [(1, 1), (3, 1)]]

/-- The numerator `εR² Pz` of `X_z`, monomial form in `u, z, c, s`. -/
def nZp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/16) [(0, 6), (3, 1)],
    monoE (-3/8) [(0, 5), (3, 1)],
    monoE (-9/16) [(0, 4), (3, 1)],
    monoE (1/4) [(0, 3), (3, 1)],
    monoE (3/4) [(0, 2), (1, 2), (3, 1)],
    monoE (-1/2) [(0, 2), (1, 1), (2, 1)],
    monoE (1) [(0, 2), (3, 1)],
    monoE (3/2) [(0, 1), (1, 2), (3, 1)],
    monoE (-1) [(0, 1), (1, 1), (2, 1)],
    monoE (1/2) [(0, 1), (3, 1)],
    monoE (3/4) [(1, 2), (3, 1)],
    monoE (-1/2) [(1, 1), (2, 1)]]

/-- Numerator `R·a` of the `dR`-coefficient `a` of the flux primitive. -/
def Pap : PolyExpr ℂ (Fin 6) := sumE [
    monoE (1/32) [(0, 4), (2, 1)],
    monoE (1/8) [(0, 3), (2, 1)],
    monoE (-1/4) [(0, 1), (2, 1)],
    monoE (-3/8) [(1, 2), (2, 1)],
    monoE (-1/4) [(1, 1), (3, 1)],
    monoE (-1) [(1, 1)]]

/-- Numerator `R²·b` of the `dz`-coefficient `b` of the flux primitive. -/
def Pbp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (-1/16) [(0, 4), (1, 1), (2, 1)],
    monoE (-1/16) [(0, 4), (3, 1)],
    monoE (-1/4) [(0, 3), (1, 1), (2, 1)],
    monoE (-1/4) [(0, 3), (3, 1)],
    monoE (-3/8) [(0, 2), (1, 1), (2, 1)],
    monoE (-3/8) [(0, 2), (3, 1)],
    monoE (-1/4) [(0, 1), (1, 1), (2, 1)],
    monoE (-1/4) [(0, 1), (3, 1)],
    monoE (-1/4) [(1, 3), (2, 1)],
    monoE (-1/4) [(1, 2), (3, 1)],
    monoE (1/4) [(1, 1), (2, 1)]]

/-- The torsion numerator `P = (D² (X − DX·V₀)) × V₀` (`V₀ = (u, z)`), monomial form; the torsion
density is `T₀ = R³ P / (D³ W₀²)`. -/
def Pp : PolyExpr ℂ (Fin 6) := sumE [
    monoE (1/128) [(0, 11), (3, 2)],
    monoE (-1/64) [(0, 10), (1, 1), (2, 1), (3, 1)],
    monoE (1/16) [(0, 10), (3, 2)],
    monoE (-1/64) [(0, 9), (1, 2), (2, 2)],
    monoE (-1/64) [(0, 9), (1, 2), (3, 2)],
    monoE (-9/64) [(0, 9), (1, 1), (2, 1), (3, 1)],
    monoE (27/128) [(0, 9), (3, 2)],
    monoE (-3/16) [(0, 9), (3, 1)],
    monoE (1/64) [(0, 8), (1, 3), (2, 1), (3, 1)],
    monoE (-5/32) [(0, 8), (1, 2), (2, 2)],
    monoE (-1/8) [(0, 8), (1, 2), (3, 2)],
    monoE (-25/64) [(0, 8), (1, 1), (2, 1), (3, 1)],
    monoE (7/16) [(0, 8), (3, 2)],
    monoE (-5/4) [(0, 8), (3, 1)],
    monoE (7/16) [(0, 7), (1, 3), (2, 1), (3, 1)],
    monoE (-31/32) [(0, 7), (1, 2), (2, 2)],
    monoE (-11/32) [(0, 7), (1, 2), (3, 2)],
    monoE (3/8) [(0, 7), (1, 2), (3, 1)],
    monoE (-5/16) [(0, 7), (1, 1), (2, 1), (3, 1)],
    monoE (-1/4) [(0, 7), (1, 1), (2, 1)],
    monoE (25/32) [(0, 7), (3, 2)],
    monoE (-25/8) [(0, 7), (3, 1)],
    monoE (71/32) [(0, 6), (1, 3), (2, 1), (3, 1)],
    monoE (-25/8) [(0, 6), (1, 2), (2, 2)],
    monoE (-5/16) [(0, 6), (1, 2), (3, 2)],
    monoE (9/4) [(0, 6), (1, 2), (3, 1)],
    monoE (-5/32) [(0, 6), (1, 1), (2, 1), (3, 1)],
    monoE (-11/8) [(0, 6), (1, 1), (2, 1)],
    monoE (5/4) [(0, 6), (3, 2)],
    monoE (-15/4) [(0, 6), (3, 1)],
    monoE (1/4) [(0, 5), (1, 5), (2, 1), (3, 1)],
    monoE (-1/4) [(0, 5), (1, 4), (2, 2)],
    monoE (1/4) [(0, 5), (1, 4), (3, 2)],
    monoE (33/8) [(0, 5), (1, 3), (2, 1), (3, 1)],
    monoE (-37/8) [(0, 5), (1, 2), (2, 2)],
    monoE (3/8) [(0, 5), (1, 2), (3, 2)],
    monoE (51/8) [(0, 5), (1, 2), (3, 1)],
    monoE (-7/4) [(0, 5), (1, 1), (2, 1), (3, 1)],
    monoE (-3) [(0, 5), (1, 1), (2, 1)],
    monoE (5/4) [(0, 5), (3, 2)],
    monoE (-35/16) [(0, 5), (3, 1)],
    monoE (3/4) [(0, 4), (1, 5), (2, 1), (3, 1)],
    monoE (-3/4) [(0, 4), (1, 4), (2, 2)],
    monoE (3/4) [(0, 4), (1, 4), (3, 2)],
    monoE (31/16) [(0, 4), (1, 3), (2, 1), (3, 1)],
    monoE (-2) [(0, 4), (1, 2), (2, 2)],
    monoE (1/2) [(0, 4), (1, 2), (3, 2)],
    monoE (21/2) [(0, 4), (1, 2), (3, 1)],
    monoE (-29/8) [(0, 4), (1, 1), (2, 1), (3, 1)],
    monoE (-25/8) [(0, 4), (1, 1), (2, 1)],
    monoE (1/2) [(0, 4), (3, 2)],
    monoE (-1/2) [(0, 4), (3, 1)],
    monoE (1/2) [(0, 3), (1, 5), (2, 1), (3, 1)],
    monoE (1/8) [(0, 3), (1, 4), (2, 2)],
    monoE (1) [(0, 3), (1, 4), (3, 2)],
    monoE (1/2) [(0, 3), (1, 4), (3, 1)],
    monoE (-5/2) [(0, 3), (1, 3), (2, 1), (3, 1)],
    monoE (9/4) [(0, 3), (1, 2), (2, 2)],
    monoE (-7/8) [(0, 3), (1, 2), (3, 2)],
    monoE (43/4) [(0, 3), (1, 2), (3, 1)],
    monoE (-2) [(0, 3), (1, 1), (2, 1), (3, 1)],
    monoE (-3/2) [(0, 3), (1, 1), (2, 1)],
    monoE (-7/8) [(0, 2), (1, 5), (2, 1), (3, 1)],
    monoE (9/4) [(0, 2), (1, 4), (2, 2)],
    monoE (2) [(0, 2), (1, 4), (3, 1)],
    monoE (-5/8) [(0, 2), (1, 3), (2, 1), (3, 1)],
    monoE (-1/2) [(0, 2), (1, 3), (2, 1)],
    monoE (2) [(0, 2), (1, 2), (2, 2)],
    monoE (-1) [(0, 2), (1, 2), (3, 2)],
    monoE (13/2) [(0, 2), (1, 2), (3, 1)],
    monoE (-1/4) [(0, 2), (1, 1), (2, 1)],
    monoE (1/4) [(0, 1), (1, 6), (2, 2)],
    monoE (1/4) [(0, 1), (1, 6), (3, 2)],
    monoE (-3/4) [(0, 1), (1, 5), (2, 1), (3, 1)],
    monoE (2) [(0, 1), (1, 4), (2, 2)],
    monoE (-3/8) [(0, 1), (1, 4), (3, 2)],
    monoE (5/2) [(0, 1), (1, 4), (3, 1)],
    monoE (2) [(0, 1), (1, 3), (2, 1), (3, 1)],
    monoE (-1) [(0, 1), (1, 3), (2, 1)],
    monoE (7/4) [(0, 1), (1, 2), (3, 1)],
    monoE (-1/4) [(1, 7), (2, 1), (3, 1)],
    monoE (1/2) [(1, 6), (2, 2)],
    monoE (1) [(1, 5), (2, 1), (3, 1)],
    monoE (1/2) [(1, 4), (3, 2)],
    monoE (1) [(1, 4), (3, 1)],
    monoE (-1/2) [(1, 3), (2, 1)]]

/-- The flow-form residual `D w_R − n_R` (variables `u, z, c, s, w_R, w_z`). -/
def resRp : PolyExpr ℂ (Fin 6) := sub (mul Dp (var 4)) nRp

/-- The flow-form residual `D w_z − n_z`. -/
def resZp : PolyExpr ℂ (Fin 6) := sub (mul Dp (var 5)) nZp

/-! ## Partial derivatives -/

section Partials

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- The partial derivative `∂_i P(x)` (directional derivative along the `i`-th unit vector). -/
def pd (x : Fin 6 → A) (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) : A :=
  PolyExpr.deriv x (Pi.single i 1) e

/-- The directional derivative is the sum of partial derivatives. -/
theorem deriv_eq_sum (x h : Fin 6 → A) :
    ∀ e : PolyExpr ℂ (Fin 6), PolyExpr.deriv x h e = ∑ i, h i * pd x i e
  | .const c => by simp [PolyExpr.deriv, pd]
  | .var j => by
    simp only [PolyExpr.deriv, pd]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi])
      (by simp)]
    simp
  | .add p q => by
    simp only [PolyExpr.deriv, pd, deriv_eq_sum x h p, deriv_eq_sum x h q,
      ← Finset.sum_add_distrib, mul_add]
  | .sub p q => by
    simp only [PolyExpr.deriv, pd, deriv_eq_sum x h p, deriv_eq_sum x h q,
      ← Finset.sum_sub_distrib, mul_sub]
  | .mul p q => by
    simp only [PolyExpr.deriv, pd, deriv_eq_sum x h p, deriv_eq_sum x h q, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by
      rw [deriv_eq_sum x (Pi.single i 1) p, deriv_eq_sum x (Pi.single i 1) q]
      ring_nf

/-- Variables with index `≥ 4` (the velocities `w_R, w_z`) do not occur. -/
def NoW : PolyExpr ℂ (Fin 6) → Prop
  | .const _ => True
  | .var i => i.val < 4
  | .add p q => NoW p ∧ NoW q
  | .sub p q => NoW p ∧ NoW q
  | .mul p q => NoW p ∧ NoW q

/-- Evaluation only depends on the variables that occur. -/
theorem eval_congr_noW {x y : Fin 6 → A} (hxy : ∀ i : Fin 6, i.val < 4 → x i = y i) :
    ∀ e : PolyExpr ℂ (Fin 6), NoW e → PolyExpr.eval x e = PolyExpr.eval y e
  | .const _, _ => rfl
  | .var i, h => hxy i h
  | .add p q, h => by
    simp only [PolyExpr.eval, eval_congr_noW hxy p h.1, eval_congr_noW hxy q h.2]
  | .sub p q, h => by
    simp only [PolyExpr.eval, eval_congr_noW hxy p h.1, eval_congr_noW hxy q h.2]
  | .mul p q, h => by
    simp only [PolyExpr.eval, eval_congr_noW hxy p h.1, eval_congr_noW hxy q h.2]

/-- Derivatives only depend on the variables that occur. -/
theorem deriv_congr_noW {x y h h' : Fin 6 → A} (hxy : ∀ i : Fin 6, i.val < 4 → x i = y i)
    (hhh : ∀ i : Fin 6, i.val < 4 → h i = h' i) :
    ∀ e : PolyExpr ℂ (Fin 6), NoW e → PolyExpr.deriv x h e = PolyExpr.deriv y h' e
  | .const _, _ => rfl
  | .var i, hi => hhh i hi
  | .add p q, hn => by
    simp only [PolyExpr.deriv, deriv_congr_noW hxy hhh p hn.1, deriv_congr_noW hxy hhh q hn.2]
  | .sub p q, hn => by
    simp only [PolyExpr.deriv, deriv_congr_noW hxy hhh p hn.1, deriv_congr_noW hxy hhh q hn.2]
  | .mul p q, hn => by
    simp only [PolyExpr.deriv, deriv_congr_noW hxy hhh p hn.1, deriv_congr_noW hxy hhh q hn.2,
      eval_congr_noW hxy p hn.1, eval_congr_noW hxy q hn.2]

/-- The partial derivative in a velocity variable vanishes. -/
theorem pd_noW {x : Fin 6 → A} {i : Fin 6} (hi : 4 ≤ i.val) :
    ∀ e : PolyExpr ℂ (Fin 6), NoW e → pd x i e = 0
  | .const _, _ => by simp [pd, PolyExpr.deriv]
  | .var j, hj => by
    simp only [pd, PolyExpr.deriv]
    have : j ≠ i := fun h => by subst h; simp [NoW] at hj; omega
    simp [this]
  | .add p q, hn => by
    have h1 := pd_noW (x := x) hi p hn.1; have h2 := pd_noW (x := x) hi q hn.2
    simp only [pd, PolyExpr.deriv] at *; rw [h1, h2, add_zero]
  | .sub p q, hn => by
    have h1 := pd_noW (x := x) hi p hn.1; have h2 := pd_noW (x := x) hi q hn.2
    simp only [pd, PolyExpr.deriv] at *; rw [h1, h2, sub_zero]
  | .mul p q, hn => by
    have h1 := pd_noW (x := x) hi p hn.1; have h2 := pd_noW (x := x) hi q hn.2
    simp only [pd, PolyExpr.deriv] at *; rw [h1, h2, zero_mul, mul_zero, add_zero]

end Partials

/-- `D` does not involve the velocities. -/
theorem noW_Dp : NoW Dp := by simp [NoW, Dp, sumE, monoE, npow]
/-- `n_R` does not involve the velocities. -/
theorem noW_nRp : NoW nRp := by simp [NoW, nRp, sumE, monoE, npow]
/-- `n_z` does not involve the velocities. -/
theorem noW_nZp : NoW nZp := by simp [NoW, nZp, sumE, monoE, npow]
/-- `P_a` does not involve the velocities. -/
theorem noW_Pap : NoW Pap := by simp [NoW, Pap, sumE, monoE, npow]
/-- `P_b` does not involve the velocities. -/
theorem noW_Pbp : NoW Pbp := by simp [NoW, Pbp, sumE, monoE, npow]
/-- `P` does not involve the velocities. -/
theorem noW_Pp : NoW Pp := by simp [NoW, Pp, sumE, monoE, npow]

/-- Evaluation of directional derivatives at a point of the torus. -/
theorem eval_deriv (x h : Fin 6 → FA) (θ ψ : ℝ) :
    ∀ e : PolyExpr ℂ (Fin 6), eval (PolyExpr.deriv x h e) θ ψ =
      PolyExpr.deriv (A := ℂ) (fun i => eval (x i) θ ψ) (fun i => eval (h i) θ ψ) e
  | .const c => by simp [PolyExpr.deriv, eval_zero']
  | .var i => rfl
  | .add p q => by
    simp only [PolyExpr.deriv, eval_add', eval_deriv x h θ ψ p, eval_deriv x h θ ψ q]
  | .sub p q => by
    simp only [PolyExpr.deriv, eval_sub', eval_deriv x h θ ψ p, eval_deriv x h θ ψ q]
  | .mul p q => by
    simp only [PolyExpr.deriv, eval_add', eval_mul, eval_deriv x h θ ψ p, eval_deriv x h θ ψ q,
      eval_polyExpr]

/-- Evaluation of partial derivatives. -/
theorem eval_pd (x : Fin 6 → FA) (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) (θ ψ : ℝ) :
    eval (pd x i e) θ ψ = pd (fun j => eval (x j) θ ψ) i e := by
  rw [pd, eval_deriv, pd]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp [eval_one]
  · simp [h, eval_zero']

/-! ## The polynomial identities -/

/-- The `φ`-derivative of a polynomial in `(u, z, c, s)`: `∂_c P·(−2s) + ∂_s P·(2c)`. -/
def phiD {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] (x : Fin 6 → A)
    (e : PolyExpr ℂ (Fin 6)) : A :=
  pd x 2 e * (-2 * x 3) + pd x 3 e * (2 * x 2)

/-- Unfolding set for the concrete polynomials. -/
macro "poly_simp" : tactic =>
  `(tactic| simp only [phiD, pd, PolyExpr.deriv, PolyExpr.eval, Dp, nRp, nZp, Pap, Pbp, Pp,
    sumE, monoE, npow, Pi.single_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Fin.isValue, eval_npow])

/-- Evaluation of `phiD`. -/
theorem eval_phiD (x : Fin 6 → FA) (e : PolyExpr ℂ (Fin 6)) (θ ψ : ℝ) :
    eval (phiD x e) θ ψ = phiD (fun j => eval (x j) θ ψ) e := by
  simp only [phiD, eval_add', eval_mul, eval_pd, eval_neg', eval_ofNat']

/-- Pointwise transfer set. -/
macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_add', eval_sub', eval_mul, eval_neg', eval_pow', eval_pd, eval_phiD,
    eval_polyExpr, eval_one, eval_ofNat', eval_zero'])

/-- **Divergence-free identity** in `𝔸`. -/
theorem divFree (x : Fin 6 → FA) :
    (1 + x 0) * phiD x Dp - 3 * PolyExpr.eval x nRp + (1 + x 0) * pd x 0 nRp +
      (1 + x 0) * pd x 1 nZp = 0 := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (a) in `𝔸`. -/
theorem flux_a (x : Fin 6 → FA) :
    (1 + x 0) * pd x 0 Pbp - 2 * PolyExpr.eval x Pbp - (1 + x 0) ^ 2 * pd x 1 Pap =
      PolyExpr.eval x Dp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (b) in `𝔸`. -/
theorem flux_b (x : Fin 6 → FA) :
    (1 + x 0) ^ 2 * phiD x Pap = PolyExpr.eval x nZp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **Flux primitive identity** (c) in `𝔸`. -/
theorem flux_c (x : Fin 6 → FA) :
    (1 + x 0) * phiD x Pbp = -PolyExpr.eval x nRp := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-- **The torsion numerator** in `𝔸`. -/
theorem torsion_poly (x : Fin 6 → FA) :
    PolyExpr.eval x Pp =
      (PolyExpr.eval x nRp * PolyExpr.eval x Dp -
          PolyExpr.eval x Dp * (pd x 0 nRp * x 0 + pd x 1 nRp * x 1) +
          PolyExpr.eval x nRp * (pd x 0 Dp * x 0 + pd x 1 Dp * x 1)) * x 1 -
        (PolyExpr.eval x nZp * PolyExpr.eval x Dp -
          PolyExpr.eval x Dp * (pd x 0 nZp * x 0 + pd x 1 nZp * x 1) +
          PolyExpr.eval x nZp * (pd x 0 Dp * x 0 + pd x 1 Dp * x 1)) * x 0 := by
  refine ext_eval fun θ ψ => ?_
  eval_simp
  poly_simp; simp; ring

/-! ## The torus point and the derived quantities -/

/-- The variables `(u, z, c, s, 𝓛u, 𝓛z)` of the residual at a torus `K = (1 + u, z)`. -/
def xK (ι : ℝ) (u z : FA) : Fin 6 → FA := ![u, z, cS, sS, Lt ι u, Lt ι z]

/-- The variables `(u, z, c, s)` (velocities `0`), for polynomials without velocities. -/
def xB (u z : FA) : Fin 6 → FA := ![u, z, cS, sS, 0, 0]

/-- Polynomials without velocities see only `(u, z, c, s)`. -/
theorem eval_xK_xB (ι : ℝ) (u z : FA) {e : PolyExpr ℂ (Fin 6)} (he : NoW e) :
    PolyExpr.eval (xK ι u z) e = PolyExpr.eval (xB u z) e :=
  eval_congr_noW (fun i hi => by fin_cases i <;> simp_all [xK, xB]) e he

/-- Partial derivatives of polynomials without velocities see only `(u, z, c, s)`. -/
theorem pd_xK_xB (ι : ℝ) (u z : FA) (i : Fin 6) {e : PolyExpr ℂ (Fin 6)} (he : NoW e) :
    pd (xK ι u z) i e = pd (xB u z) i e :=
  deriv_congr_noW (fun i hi => by fin_cases i <;> simp_all [xK, xB]) (fun _ _ => rfl) e he

/-- `D(K)`. -/
def Dof (u z : FA) : FA := PolyExpr.eval (xB u z) Dp

/-- The torsion numerator `P(K)`. -/
def Pof (u z : FA) : FA := PolyExpr.eval (xB u z) Pp

/-- `W₀ = ∂_θK × V₀ = ∂_θR · z − ∂_θz · u` (minus the winding rate). -/
def W0of (u z : FA) : FA := dTh u * z - dTh z * u

/-- The `R`-residual `D 𝓛R − n_R`. -/
def resR (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) resRp

/-- The `z`-residual `D 𝓛z − n_z`. -/
def resZ (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) resZp

/-- `resR = D 𝓛u − n_R`. -/
theorem resR_eq (ι : ℝ) (u z : FA) :
    resR ι u z = Dof u z * Lt ι u - PolyExpr.eval (xB u z) nRp := by
  rw [resR, resRp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z noW_Dp, eval_xK_xB ι u z noW_nRp]
  rfl

/-- `resZ = D 𝓛z − n_z`. -/
theorem resZ_eq (ι : ℝ) (u z : FA) :
    resZ ι u z = Dof u z * Lt ι z - PolyExpr.eval (xB u z) nZp := by
  rw [resZ, resZp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z noW_Dp, eval_xK_xB ι u z noW_nZp]
  rfl

end PlasmaLean.Design.KamNewton
