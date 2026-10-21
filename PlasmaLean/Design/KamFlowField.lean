/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.StripEval

/-!
# Fields in flow form: the abstract interface of the KAM step (`FlowField`)

The flow form of the field-line equations of a magnetic field `B` for a torus
`K = (R, z) = (1 + u, z)` is `D(K, φ)·𝓛K = n(K, φ)` with `𝓛 = ∂_φ + ι∂_θ` and polynomials
`D, n_R, n_z` in `u, z, c = cos 2φ, s = sin 2φ` (`D = R³B^φ`, `n = R³(B^R, B^z)` after clearing
denominators). This file collects the **field-independent** part of the KAM Newton step in the
strip algebra `𝔸` (`Theory/KAM/StripAlgebra`) and the **interface** `FlowField` that the Newton
step (`Design/KamFlowFrame`, `Design/KamFlowStep`) and the iteration (`Design/KamFlowIteration`)
need from a field:

* the trigonometric elements `cS = cos 2φ = −sin ψ`, `sS = sin 2φ = cos ψ` (`ψ = 2φ − π/2`) with
  `dS a b sS = b cS`, `dS a b cS = −b sS`, and the operators `dTh = ∂_θ`, `dPh = ∂_φ = 2∂_ψ`,
  `Lt ι = 𝓛 = ι∂_θ + ∂_φ`;
* polynomial expressions in the six variables `(u, z, c, s, w_R, w_z)` (`sumE`, `monoE`), their
  partial derivatives `pd`, the `φ`-derivative `phiD`, and the torus points `xK` (with
  velocities `𝓛K`) and `xB` (velocities `0`);
* `FlowField`: the polynomials `D, n_R, n_z`, the flux-primitive numerators `P_a, P_b` and the
  torsion numerator `P`, with real coefficients, free of the velocity variables, satisfying at
  every torus point `xB u z` the **divergence-free identity** `divFree`, the **flux primitive
  identities** `flux_a`, `flux_b`, `flux_c` and the **torsion identity** `torsion_poly`.
  The derived objects are `F.Dof` (`D(K)`), `F.Pof` (`P(K)`), `F.resRp`, `F.resZp` (the residual
  polynomials `D w − n`) and `F.resR`, `F.resZ` (the residuals `D 𝓛K − n` at a torus).

The instance for the rational stellarator `field (1/4)` is `field14` (`Design/KamNewtonField`).

**Sanity.** `eval_sS`, `eval_cS` (the elements are the trigonometric functions),
`FlowField.not_noW_resRp` (the residuals do involve the velocities), and the degenerate instance
`FlowField.toroidal` (`D = 1`, `n = 0`) with `FlowField.toroidal_resR` (`resR = 𝓛u`).
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

/-! ## Polynomial expressions (variables `u = R − 1, z, c, s, w_R, w_z` are `0, …, 5`) -/

/-- Sum of a list of expressions. -/
def sumE {σ : Type*} : List (PolyExpr ℂ σ) → PolyExpr ℂ σ
  | [] => const 0
  | e :: es => add e (sumE es)

/-- The monomial `c ∏ x_i^{k_i}`. -/
def monoE {σ : Type*} (c : ℂ) : List (σ × ℕ) → PolyExpr ℂ σ
  | [] => const c
  | (i, k) :: l => mul (monoE c l) (npow (var i) k)

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

/-- The `φ`-derivative of a polynomial in `(u, z, c, s)`: `∂_c P·(−2s) + ∂_s P·(2c)`. -/
def phiD {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] (x : Fin 6 → A)
    (e : PolyExpr ℂ (Fin 6)) : A :=
  pd x 2 e * (-2 * x 3) + pd x 3 e * (2 * x 2)

/-- Evaluation of `phiD`. -/
theorem eval_phiD (x : Fin 6 → FA) (e : PolyExpr ℂ (Fin 6)) (θ ψ : ℝ) :
    eval (phiD x e) θ ψ = phiD (fun j => eval (x j) θ ψ) e := by
  simp only [phiD, eval_add', eval_mul, eval_pd, eval_neg', eval_ofNat']

/-- Pointwise transfer set. -/
macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_add', eval_sub', eval_mul, eval_neg', eval_pow', eval_pd, eval_phiD,
    eval_polyExpr, eval_one, eval_ofNat', eval_zero'])

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

/-- `W₀ = ∂_θK × V₀ = ∂_θR · z − ∂_θz · u` (minus the winding rate). -/
def W0of (u z : FA) : FA := dTh u * z - dTh z * u


/-! ## The interface -/

/-- **A field in flow form**: the data of a magnetic field that the KAM Newton step uses.

The polynomials are in the variables `(u, z, c, s, w_R, w_z)` (`u = R − 1`, `c = cos 2φ`,
`s = sin 2φ`; the velocities `w_R, w_z` only enter the residuals):
* `Dp = D` (`R³B^φ` up to a common factor), `nRp = n_R`, `nZp = n_z` (so `X = n/D` is the
  field-line vector field `dK/dφ`);
* `Pap`, `Pbp`: the numerators of the primitive `α = (P_a/R) dR + (P_b/R²) dz` of the flux
  2-form `β = w (dR − X_R dφ) ∧ (dz − X_z dφ)`, `w = D/R³`;
* `Pp`: the torsion numerator.

The identities are required at every torus point `xB u z` of the strip algebra (this is all the
Newton step uses, and it allows fields whose identities only hold modulo algebraic relations
satisfied along tori). -/
structure FlowField where
  /-- `D` (the `φ`-component of the field, times `R³`). -/
  Dp : PolyExpr ℂ (Fin 6)
  /-- `n_R` (the `R`-component of the field, times `R³`). -/
  nRp : PolyExpr ℂ (Fin 6)
  /-- `n_z` (the `z`-component of the field, times `R³`). -/
  nZp : PolyExpr ℂ (Fin 6)
  /-- Numerator `R·a` of the `dR`-coefficient of the flux primitive. -/
  Pap : PolyExpr ℂ (Fin 6)
  /-- Numerator `R²·b` of the `dz`-coefficient of the flux primitive. -/
  Pbp : PolyExpr ℂ (Fin 6)
  /-- The torsion numerator `P = (D² (X − DX·V₀)) × V₀` (`V₀ = (u, z)`). -/
  Pp : PolyExpr ℂ (Fin 6)
  /-- `D` does not involve the velocities. -/
  noW_Dp : NoW Dp
  /-- `n_R` does not involve the velocities. -/
  noW_nRp : NoW nRp
  /-- `n_z` does not involve the velocities. -/
  noW_nZp : NoW nZp
  /-- `D` has real coefficients. -/
  real_Dp : Dp.RealConsts
  /-- `n_R` has real coefficients. -/
  real_nRp : nRp.RealConsts
  /-- `n_z` has real coefficients. -/
  real_nZp : nZp.RealConsts
  /-- `P` has real coefficients. -/
  real_Pp : Pp.RealConsts
  /-- **Divergence-free identity** `R ∂_φD − 3 n_R + R ∂_u n_R + R ∂_z n_z = 0` (the flux form
  `(D/R³) dR∧dz` is invariant). -/
  divFree : ∀ u z : FA,
    (1 + u) * phiD (xB u z) Dp - 3 * PolyExpr.eval (xB u z) nRp + (1 + u) * pd (xB u z) 0 nRp +
      (1 + u) * pd (xB u z) 1 nZp = 0
  /-- **Flux primitive identity** (a): `dα` has `dR∧dz`-coefficient `w`. -/
  flux_a : ∀ u z : FA,
    (1 + u) * pd (xB u z) 0 Pbp - 2 * PolyExpr.eval (xB u z) Pbp -
      (1 + u) ^ 2 * pd (xB u z) 1 Pap = PolyExpr.eval (xB u z) Dp
  /-- **Flux primitive identity** (b): the `dz∧dφ`-coefficient. -/
  flux_b : ∀ u z : FA, (1 + u) ^ 2 * phiD (xB u z) Pap = PolyExpr.eval (xB u z) nZp
  /-- **Flux primitive identity** (c): the `dR∧dφ`-coefficient. -/
  flux_c : ∀ u z : FA, (1 + u) * phiD (xB u z) Pbp = -PolyExpr.eval (xB u z) nRp
  /-- **The torsion numerator**
  `P = (n_R D − D ∇n_R·V₀ + n_R ∇D·V₀) z − (n_z D − D ∇n_z·V₀ + n_z ∇D·V₀) u`. -/
  torsion_poly : ∀ u z : FA,
    PolyExpr.eval (xB u z) Pp =
      (PolyExpr.eval (xB u z) nRp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp * (pd (xB u z) 0 nRp * u + pd (xB u z) 1 nRp * z) +
          PolyExpr.eval (xB u z) nRp * (pd (xB u z) 0 Dp * u + pd (xB u z) 1 Dp * z)) * z -
        (PolyExpr.eval (xB u z) nZp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp * (pd (xB u z) 0 nZp * u + pd (xB u z) 1 nZp * z) +
          PolyExpr.eval (xB u z) nZp * (pd (xB u z) 0 Dp * u + pd (xB u z) 1 Dp * z)) * u

namespace FlowField

variable (F : FlowField)

/-- The flow-form residual polynomial `D w_R − n_R` (variables `u, z, c, s, w_R, w_z`). -/
def resRp : PolyExpr ℂ (Fin 6) := sub (mul F.Dp (var 4)) F.nRp

/-- The flow-form residual polynomial `D w_z − n_z`. -/
def resZp : PolyExpr ℂ (Fin 6) := sub (mul F.Dp (var 5)) F.nZp

/-- `D(K)`. -/
def Dof (u z : FA) : FA := PolyExpr.eval (xB u z) F.Dp

/-- The torsion numerator `P(K)`. -/
def Pof (u z : FA) : FA := PolyExpr.eval (xB u z) F.Pp

/-- The `R`-residual `D 𝓛R − n_R` of a torus `K = (1 + u, z)`. -/
def resR (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) F.resRp

/-- The `z`-residual `D 𝓛z − n_z`. -/
def resZ (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) F.resZp

/-- `resR = D 𝓛u − n_R`. -/
theorem resR_eq (ι : ℝ) (u z : FA) :
    F.resR ι u z = F.Dof u z * Lt ι u - PolyExpr.eval (xB u z) F.nRp := by
  rw [resR, resRp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z F.noW_Dp, eval_xK_xB ι u z F.noW_nRp]
  rfl

/-- `resZ = D 𝓛z − n_z`. -/
theorem resZ_eq (ι : ℝ) (u z : FA) :
    F.resZ ι u z = F.Dof u z * Lt ι z - PolyExpr.eval (xB u z) F.nZp := by
  rw [resZ, resZp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z F.noW_Dp, eval_xK_xB ι u z F.noW_nZp]
  rfl

/-- **Sanity**: the residual polynomials do involve the velocities (the Newton step perturbs
them through `𝓛ΔK`). -/
theorem not_noW_resRp : ¬ NoW F.resRp := by
  simp [resRp, NoW]

/-- **Sanity: the purely toroidal flow field** `D = 1`, `n = 0` (field lines are the circles
`R, z = const`), with flux primitive `α = −dz/(2R²)` and torsion `0`; it satisfies the interface,
so the identities are consistent. -/
def toroidal : FlowField where
  Dp := const 1
  nRp := const 0
  nZp := const 0
  Pap := const 0
  Pbp := const (-1 / 2)
  Pp := const 0
  noW_Dp := by simp [NoW]
  noW_nRp := by simp [NoW]
  noW_nZp := by simp [NoW]
  real_Dp := by simp [PolyExpr.RealConsts]
  real_nRp := by simp [PolyExpr.RealConsts]
  real_nZp := by simp [PolyExpr.RealConsts]
  real_Pp := by simp [PolyExpr.RealConsts]
  divFree := fun u z => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  flux_a := fun u z => by
    simp only [pd, PolyExpr.deriv, PolyExpr.eval, mul_zero, sub_zero]
    rw [← map_ofNat (algebraMap ℂ FA) 2, ← map_mul]
    norm_num
  flux_b := fun u z => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  flux_c := fun u z => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  torsion_poly := fun u z => by simp [pd, PolyExpr.deriv, PolyExpr.eval]

/-- **Sanity**: the residual of the toroidal field is `𝓛u` (the torus must be invariant under the
`φ`-rotation). -/
theorem toroidal_resR (ι : ℝ) (u z : FA) : toroidal.resR ι u z = Lt ι u := by
  rw [resR_eq]
  simp [toroidal, Dof, PolyExpr.eval]

end FlowField

end PlasmaLean.Design.KamNewton
