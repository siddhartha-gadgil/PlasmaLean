/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.Composition
public import PlasmaLean.Design.KamTorusA

/-!
# Composition bounds for the flow form of torus A (K3 plan, lemma 4, design part)

The flow form of the invariance equation of `Design/KamTorusA` is
`resR = D·w_R − 2εR·Ps`, `resZ = D·w_z − εR²·Pz`, with `w = ∂_φK + ι∂_θK`, and
`D = R²(1 + ε∂_φh)`, `Ps`, `Pz` polynomials in `(R, z, cos 2φ, sin 2φ)` (`Dfun`, `Psfun`,
`Pzfun`). Here these are written as polynomial expressions (`PolyExpr ℂ (Fin 6)`, variables
`R, z, c = cos 2φ, s = sin 2φ, w_R, w_z`), mirroring the definitions of `Design/KamTorusA`
term by term:

* `DE`, `PsE`, `PzE`, the flow numerators `XRnumE = 2εR·Ps`, `XZnumE = εR²·Pz`, and the
  residuals `resRE`, `resZE`;
* `eval_DE`, `eval_PsE`, `eval_PzE`, `eval_resRE`, `eval_resZE`: evaluated at real points they
  are exactly `Dfun`, `Psfun`, `Pzfun`, and `resRw ι θ φ`, `resZw ι θ φ` (the residuals of
  `KamTorusA`) at the torus point.

**Composition with a torus in `ℓ¹_r(ℤ²)`.** For `R, z, w_R, w_z ∈ WEll1Z2 r` (`r ≥ 0`) and the
trigonometric elements `c2 r = cos 2φ = −sin ψ`, `s2 r = sin 2φ = cos ψ` (`ψ = 2φ − π/2`;
`eval_c2`, `eval_s2`; `norm_c2_le`, `norm_s2_le`: `‖·‖_r ≤ e^r`):
* `norm_D_le`, `norm_XRnum_le`, `norm_XZnum_le`, `norm_resR_le`, `norm_resZ_le`: value bounds
  `‖P(K)‖_r ≤ P̂(‖R‖_r, ‖z‖_r, e^r, e^r, ‖w_R‖_r, ‖w_z‖_r)`, with the closed forms `Dmaj`,
  `Psmaj`, `Pzmaj` (`maj_DE`, `maj_PsE`, `maj_PzE`);
* `taylor_resR`, `taylor_resZ`: for a perturbation `ΔK = (ΔR, Δz, 0, 0, Δw_R, Δw_z)` (the angle
  variables are not perturbed), `‖res(K + ΔK) − res(K) − Dres(K)ΔK‖_r ≤ ½ r̂es''(a + b)[b, b]`,
  and `deriv_resR_le` / `deriv_resZ_le`: `‖Dres(K)ΔK‖_r ≤ r̂es'(a)·b` — this is the
  `(H-field)` hypothesis of the K3 plan in polynomial (cleared) form;
* `inv_D_bound`, `norm_XR_le`, `norm_XZ_le`: if `‖D(K) − D̄‖_r < |D̄|` then `D(K)` is invertible
  and the field-line vector field `X = (2εR Ps, εR² Pz)/D` composed with `K` satisfies
  `‖X_R(K)‖_r ≤ P̂s-majorant / (|D̄| − ‖D(K) − D̄‖_r)`.

**Not included (recorded).** Lemma 6 of the plan (`flux_average`, `⟨η₂⟩ = O(‖E‖²)`, or a
translation counterterm `λ` with `λ = 0` a posteriori) is not cheap: it needs the normal `N`
and the frame `M = (∂_θK, N)` with their inverses (lemma 5 data), the identity
`∮ K^*(ι_X Ω) = 0` for the exact flux form `Ω = R B^φ dR ∧ dz` (div B = 0) pulled back by the
torus, and the averaging of `η₂ = (M⁻¹E)₂` against it. None of this is a polynomial
composition estimate, so it is left to the frame stage.

**Sanity.** `maj_DE_axis`: at the magnetic-axis values `‖R‖ = 1`, `‖z‖ = 0`, `e^r = 1`
(the degenerate strip `r = 0`) the majorant of `D` is `1 + 1/4·(2·(4/4)·1) = 3/2`; `eval_DE_axis`:
`D(1, 0, c, s) = 1` exactly (the axis is unperturbed); the rejected fixture `not_maj_DE_le_one`
(the majorant does not reproduce the cancellation, `D̂ > 1` on the axis — which is why `1/D` is
bounded by the Neumann series around `D̄`, not from `D̂`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open PlasmaLean.Theory.KAM PlasmaLean.Theory.KAM.PolyExpr

/-! ## The polynomial expressions -/

/-- Expressions in `R, z, c = cos 2φ, s = sin 2φ, w_R, w_z`. -/
abbrev FExpr : Type := PolyExpr ℂ (Fin 6)

/-- The variable `R`. -/
def vR : FExpr := var 0
/-- The variable `z`. -/
def vz : FExpr := var 1
/-- The variable `c = cos 2φ`. -/
def vc : FExpr := var 2
/-- The variable `s = sin 2φ`. -/
def vs : FExpr := var 3
/-- The variable `w_R = ∂_φR + ι∂_θR`. -/
def vwR : FExpr := var 4
/-- The variable `w_z = ∂_φz + ι∂_θz`. -/
def vwZ : FExpr := var 5

/-- `sfun = ((R² − 1)² − 4z²)/4`. -/
def sfunE : FExpr :=
  mul (const (1 / 4)) (sub (npow (sub (npow vR 2) (const 1)) 2) (mul (const 4) (npow vz 2)))

/-- `sgfun = −z((R² − 1)(R² − 5) − 4z²)/4`. -/
def sgfunE : FExpr :=
  mul (const (-1 / 4)) (mul vz (sub (mul (sub (npow vR 2) (const 1)) (sub (npow vR 2) (const 5)))
    (mul (const 4) (npow vz 2))))

/-- `s2fs = (R⁴ − 1 + 4z²)/4`. -/
def s2fsE : FExpr :=
  mul (const (1 / 4)) (add (sub (npow vR 4) (const 1)) (mul (const 4) (npow vz 2)))

/-- `s2gs = −z(R⁴ − 5 + 4z²)/4`. -/
def s2gsE : FExpr :=
  mul (const (-1 / 4)) (mul vz (add (sub (npow vR 4) (const 5)) (mul (const 4) (npow vz 2))))

/-- `sgz = −((R² − 1)(R² − 5) − 12z²)/4`. -/
def sgzE : FExpr :=
  mul (const (-1 / 4)) (sub (mul (sub (npow vR 2) (const 1)) (sub (npow vR 2) (const 5)))
    (mul (const 12) (npow vz 2)))

/-- `D = R² + ε(−2 sfun·s + 2 sgfun·c)` (`Dfun`). -/
def DE : FExpr :=
  add (npow vR 2) (mul (const (1 / 4))
    (add (mul (mul (const (-2)) sfunE) vs) (mul (mul (const 2) sgfunE) vc)))

/-- `Ps = s2fs·c + s2gs·s` (`Psfun`). -/
def PsE : FExpr := add (mul s2fsE vc) (mul s2gsE vs)

/-- `Pz = −2z·c + sgz·s` (`Pzfun`). -/
def PzE : FExpr := add (mul (mul (const (-2)) vz) vc) (mul sgzE vs)

/-- The numerator `2εR·Ps` of `X_R`. -/
def XRnumE : FExpr := mul (mul (mul (const 2) (const (1 / 4))) vR) PsE

/-- The numerator `εR²·Pz` of `X_z`. -/
def XZnumE : FExpr := mul (mul (const (1 / 4)) (npow vR 2)) PzE

/-- The flow-form residual `D·w_R − 2εR·Ps`. -/
def resRE : FExpr := sub (mul DE vwR) XRnumE

/-- The flow-form residual `D·w_z − εR²·Pz`. -/
def resZE : FExpr := sub (mul DE vwZ) XZnumE

/-! ## Agreement with `Design/KamTorusA` -/

/-- The real point `(R, z, c, s, w_R, w_z)` in `ℂ⁶`. -/
def realPt (R z c s wR wZ : ℝ) : Fin 6 → ℂ := ![R, z, c, s, wR, wZ]

/-- `DE` evaluates to `Dfun`. -/
theorem eval_DE (R z c s wR wZ : ℝ) :
    eval (realPt R z c s wR wZ) DE = (Dfun R z c s : ℂ) := by
  simp only [eval, DE, sfunE, sgfunE, vR, vz, vc, vs, eval_npow, realPt, Matrix.cons_val,
    Algebra.algebraMap_self, RingHom.id_apply, Dfun, sfun, sgfun, eps]
  push_cast; ring

/-- `PsE` evaluates to `Psfun`. -/
theorem eval_PsE (R z c s wR wZ : ℝ) :
    eval (realPt R z c s wR wZ) PsE = (Psfun R z c s : ℂ) := by
  simp only [eval, PsE, s2fsE, s2gsE, vR, vz, vc, vs, eval_npow, realPt, Matrix.cons_val,
    Algebra.algebraMap_self, RingHom.id_apply, Psfun, s2fs, s2gs]
  push_cast; ring

/-- `PzE` evaluates to `Pzfun`. -/
theorem eval_PzE (R z c s wR wZ : ℝ) :
    eval (realPt R z c s wR wZ) PzE = (Pzfun R z c s : ℂ) := by
  simp only [eval, PzE, sgzE, vR, vz, vc, vs, eval_npow, realPt, Matrix.cons_val,
    Algebra.algebraMap_self, RingHom.id_apply, Pzfun, sgz]
  push_cast; ring

/-- `resRE` evaluates to `D w_R − 2εR Ps`. -/
theorem eval_resRE (R z c s wR wZ : ℝ) :
    eval (realPt R z c s wR wZ) resRE =
      ((Dfun R z c s * wR - 2 * eps * R * Psfun R z c s : ℝ) : ℂ) := by
  simp only [resRE, XRnumE, eval]
  rw [eval_DE, eval_PsE]
  simp only [vR, vwR, eval, realPt, Matrix.cons_val, Algebra.algebraMap_self, RingHom.id_apply,
    eps]
  push_cast; ring

/-- `resZE` evaluates to `D w_z − εR² Pz`. -/
theorem eval_resZE (R z c s wR wZ : ℝ) :
    eval (realPt R z c s wR wZ) resZE =
      ((Dfun R z c s * wZ - eps * R ^ 2 * Pzfun R z c s : ℝ) : ℂ) := by
  simp only [resZE, XZnumE, eval]
  rw [eval_DE, eval_PzE]
  simp only [vR, vwZ, eval, eval_npow, realPt, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply,
    eps]
  push_cast; ring

/-- The torus point of `KamTorusA` at angles `(θ, φ)` with transform `ι`. -/
def torusPt (ι θ φ : ℝ) : Fin 6 → ℂ :=
  realPt (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))
    (torusRφ θ φ + ι * torusRθ θ φ) (torusZφ θ φ + ι * torusZθ θ φ)

/-- The expression `resRE` at the torus point is the residual `resRw` of `KamTorusA`. -/
theorem eval_resRE_torus (ι θ φ : ℝ) : eval (torusPt ι θ φ) resRE = (resRw ι θ φ : ℂ) := by
  rw [torusPt, eval_resRE, resRw]

/-- The expression `resZE` at the torus point is the residual `resZw` of `KamTorusA`. -/
theorem eval_resZE_torus (ι θ φ : ℝ) : eval (torusPt ι θ φ) resZE = (resZw ι θ φ : ℂ) := by
  rw [torusPt, eval_resZE, resZw]

/-! ## Closed forms of the majorants -/

/-- The majorant of `sfun`: `((a² + 1)² + 4b²)/4`. -/
def sfunMaj (a b : ℝ) : ℝ := ((a ^ 2 + 1) ^ 2 + 4 * b ^ 2) / 4
/-- The majorant of `sgfun`: `b((a² + 1)(a² + 5) + 4b²)/4`. -/
def sgfunMaj (a b : ℝ) : ℝ := b * ((a ^ 2 + 1) * (a ^ 2 + 5) + 4 * b ^ 2) / 4
/-- The majorant of `D`: `a² + (2 sfunMaj·s + 2 sgfunMaj·c)/4`. -/
def Dmaj (a b c s : ℝ) : ℝ := a ^ 2 + (2 * sfunMaj a b * s + 2 * sgfunMaj a b * c) / 4
/-- The majorant of `Ps`: `(a⁴ + 1 + 4b²)c/4 + b(a⁴ + 5 + 4b²)s/4`. -/
def Psmaj (a b c s : ℝ) : ℝ :=
  (a ^ 4 + 1 + 4 * b ^ 2) / 4 * c + b * (a ^ 4 + 5 + 4 * b ^ 2) / 4 * s
/-- The majorant of `Pz`: `2bc + ((a² + 1)(a² + 5) + 12b²)s/4`. -/
def Pzmaj (a b c s : ℝ) : ℝ := 2 * b * c + ((a ^ 2 + 1) * (a ^ 2 + 5) + 12 * b ^ 2) / 4 * s

/-- The majorant point `(a_R, a_z, a_c, a_s, a_{w_R}, a_{w_z})`. -/
def majPt (aR az ac as awR awZ : ℝ) : Fin 6 → ℝ := ![aR, az, ac, as, awR, awZ]

/-- Closed form of `D̂`. -/
theorem maj_DE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) DE = Dmaj aR az ac as := by
  simp only [maj, DE, sfunE, sgfunE, vR, vz, vc, vs, maj_npow, majPt, Matrix.cons_val, norm_div,
    norm_neg, norm_one, Complex.norm_ofNat, Dmaj, sfunMaj, sgfunMaj]
  ring

/-- Closed form of `P̂s`. -/
theorem maj_PsE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) PsE = Psmaj aR az ac as := by
  simp only [maj, PsE, s2fsE, s2gsE, vR, vz, vc, vs, maj_npow, majPt, Matrix.cons_val, norm_div,
    norm_neg, norm_one, Complex.norm_ofNat, Psmaj]
  ring

/-- Closed form of `P̂z`. -/
theorem maj_PzE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) PzE = Pzmaj aR az ac as := by
  simp only [maj, PzE, sgzE, vR, vz, vc, vs, maj_npow, majPt, Matrix.cons_val, norm_div, norm_neg,
    norm_one, Complex.norm_ofNat, Pzmaj]
  ring

/-- Closed form of the majorant of `2εR·Ps`. -/
theorem maj_XRnumE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) XRnumE = aR / 2 * Psmaj aR az ac as := by
  rw [XRnumE, maj, maj_PsE]
  simp only [maj, vR, majPt, Matrix.cons_val, norm_div, norm_one, Complex.norm_ofNat]
  ring

/-- Closed form of the majorant of `εR²·Pz`. -/
theorem maj_XZnumE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) XZnumE = aR ^ 2 / 4 * Pzmaj aR az ac as := by
  rw [XZnumE, maj, maj_PzE]
  simp only [maj, vR, maj_npow, majPt, Matrix.cons_val, norm_div, norm_one, Complex.norm_ofNat]
  ring

/-- Closed form of the majorant of `resR`. -/
theorem maj_resRE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) resRE =
      Dmaj aR az ac as * awR + aR / 2 * Psmaj aR az ac as := by
  rw [resRE, maj, maj, maj_DE, maj_XRnumE]
  simp only [maj, vwR, majPt, Matrix.cons_val]

/-- Closed form of the majorant of `resZ`. -/
theorem maj_resZE (aR az ac as awR awZ : ℝ) :
    maj (majPt aR az ac as awR awZ) resZE =
      Dmaj aR az ac as * awZ + aR ^ 2 / 4 * Pzmaj aR az ac as := by
  rw [resZE, maj, maj, maj_DE, maj_XZnumE]
  simp only [maj, vwZ, majPt, Matrix.cons_val]

/-! ## The trigonometric elements of `ℓ¹_r(ℤ²)` -/

namespace Torus

variable {r : ℝ}

/-- `cos 2φ = −sin ψ = (i/2)(e^{iψ} − e^{−iψ})` as an element of `ℓ¹_r(ℤ²)`. -/
def c2 (r : ℝ) : WEll1Z2 r := (Complex.I / 2) • (WEll1Z2.mode r (0, 1) - WEll1Z2.mode r (0, -1))

/-- `sin 2φ = cos ψ = (e^{iψ} + e^{−iψ})/2` as an element of `ℓ¹_r(ℤ²)`. -/
def s2 (r : ℝ) : WEll1Z2 r := (1 / 2 : ℂ) • (WEll1Z2.mode r (0, 1) + WEll1Z2.mode r (0, -1))

/-- The weight of the modes `(0, ±1)` is `e^r`. -/
theorem weight_zero_pm_one (m : ℤ) (hm : m = 1 ∨ m = -1) : weight r (0, m) = Real.exp r := by
  rcases hm with rfl | rfl <;> simp [weight, modeSize]

/-- `‖cos 2φ‖_r ≤ e^r`. -/
theorem norm_c2_le : ‖c2 r‖ ≤ Real.exp r := by
  rw [c2, norm_smul]
  have h := norm_sub_le (WEll1Z2.mode r (0, 1)) (WEll1Z2.mode r (0, -1))
  rw [WEll1Z2.norm_mode, WEll1Z2.norm_mode, weight_zero_pm_one 1 (Or.inl rfl),
    weight_zero_pm_one (-1) (Or.inr rfl)] at h
  have hI : ‖Complex.I / 2‖ = 1 / 2 := by simp
  rw [hI]; linarith

/-- `‖sin 2φ‖_r ≤ e^r`. -/
theorem norm_s2_le : ‖s2 r‖ ≤ Real.exp r := by
  rw [s2, norm_smul]
  have h := norm_add_le (WEll1Z2.mode r (0, 1)) (WEll1Z2.mode r (0, -1))
  rw [WEll1Z2.norm_mode, WEll1Z2.norm_mode, weight_zero_pm_one 1 (Or.inl rfl),
    weight_zero_pm_one (-1) (Or.inr rfl)] at h
  have hI : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hI]; linarith

/-- The Fourier sum of a combination of the modes `(0, ±1)`. -/
theorem fourierSum_pm (α β : ℂ) (θ ψ : ℝ) :
    fourierSum (fun n => α * (Pi.single (0, 1) (1 : ℂ) : ℤ × ℤ → ℂ) n +
        β * (Pi.single (0, -1) (1 : ℂ) : ℤ × ℤ → ℂ) n) θ ψ =
      α * Complex.exp (ψ * Complex.I) + β * Complex.exp (-ψ * Complex.I) := by
  rw [fourierSum, tsum_eq_sum (s := {(0, 1), (0, -1)}) (fun n hn => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [hn.1, hn.2])]
  rw [Finset.sum_pair (by simp)]
  simp [fourierMode]

/-- Sanity: `c2 r` evaluates to `cos 2φ` at `ψ = 2φ − π/2`. -/
theorem eval_c2 (θ φ : ℝ) : WEll1Z2.eval (c2 r) θ (psi φ) = (Real.cos (2 * φ) : ℂ) := by
  have hc : WEll1Z2.coeff (c2 r) = fun n => Complex.I / 2 * (Pi.single (0, 1) (1 : ℂ) :
      ℤ × ℤ → ℂ) n + (-(Complex.I / 2)) * (Pi.single (0, -1) (1 : ℂ) : ℤ × ℤ → ℂ) n := by
    funext n; simp [c2]; ring
  rw [WEll1Z2.eval, hc, fourierSum_pm, cos_two_mul_eq, Complex.ofReal_neg, Complex.ofReal_sin,
    Complex.sin]
  ring_nf

/-- Sanity: `s2 r` evaluates to `sin 2φ` at `ψ = 2φ − π/2`. -/
theorem eval_s2 (θ φ : ℝ) : WEll1Z2.eval (s2 r) θ (psi φ) = (Real.sin (2 * φ) : ℂ) := by
  have hc : WEll1Z2.coeff (s2 r) = fun n => (1 / 2 : ℂ) * (Pi.single (0, 1) (1 : ℂ) :
      ℤ × ℤ → ℂ) n + (1 / 2 : ℂ) * (Pi.single (0, -1) (1 : ℂ) : ℤ × ℤ → ℂ) n := by
    funext n; simp [s2]
  rw [WEll1Z2.eval, hc, fourierSum_pm, sin_two_mul_eq, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-! ## Composition with a torus in `ℓ¹_r(ℤ²)` -/

variable [Fact (0 ≤ r)]

/-- The torus data `(R, z, cos 2φ, sin 2φ, w_R, w_z)` in `ℓ¹_r(ℤ²)`. -/
def pt (R z wR wZ : WEll1Z2 r) : Fin 6 → WEll1Z2 r := ![R, z, c2 r, s2 r, wR, wZ]

/-- The norm bounds of the torus data. -/
def bd (R z wR wZ : WEll1Z2 r) : Fin 6 → ℝ :=
  majPt ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) ‖wR‖ ‖wZ‖

/-- The torus data are bounded by `bd`. -/
theorem norm_pt_le (R z wR wZ : WEll1Z2 r) : ∀ i, ‖pt R z wR wZ i‖ ≤ bd R z wR wZ i := by
  intro i
  fin_cases i <;> simp [pt, bd, majPt, norm_c2_le, norm_s2_le]

/-- `‖D(K)‖_r ≤ D̂(‖R‖_r, ‖z‖_r, e^r, e^r)`. -/
theorem norm_D_le (R z wR wZ : WEll1Z2 r) :
    ‖eval (pt R z wR wZ) DE‖ ≤ Dmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) := by
  have := norm_eval_le (norm_pt_le R z wR wZ) DE
  rwa [bd, maj_DE] at this

/-- `‖2εR Ps(K)‖_r ≤ (‖R‖_r/2)·P̂s(‖R‖_r, ‖z‖_r, e^r, e^r)`. -/
theorem norm_XRnum_le (R z wR wZ : WEll1Z2 r) :
    ‖eval (pt R z wR wZ) XRnumE‖ ≤ ‖R‖ / 2 * Psmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) := by
  have := norm_eval_le (norm_pt_le R z wR wZ) XRnumE
  rwa [bd, maj_XRnumE] at this

/-- `‖εR² Pz(K)‖_r ≤ (‖R‖_r²/4)·P̂z(‖R‖_r, ‖z‖_r, e^r, e^r)`. -/
theorem norm_XZnum_le (R z wR wZ : WEll1Z2 r) :
    ‖eval (pt R z wR wZ) XZnumE‖ ≤ ‖R‖ ^ 2 / 4 * Pzmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) := by
  have := norm_eval_le (norm_pt_le R z wR wZ) XZnumE
  rwa [bd, maj_XZnumE] at this

/-- Value bound for the `R`-residual of the flow form. -/
theorem norm_resR_le (R z wR wZ : WEll1Z2 r) :
    ‖eval (pt R z wR wZ) resRE‖ ≤
      Dmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) * ‖wR‖ +
        ‖R‖ / 2 * Psmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) := by
  have := norm_eval_le (norm_pt_le R z wR wZ) resRE
  rwa [bd, maj_resRE] at this

/-- Value bound for the `z`-residual of the flow form. -/
theorem norm_resZ_le (R z wR wZ : WEll1Z2 r) :
    ‖eval (pt R z wR wZ) resZE‖ ≤
      Dmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) * ‖wZ‖ +
        ‖R‖ ^ 2 / 4 * Pzmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) := by
  have := norm_eval_le (norm_pt_le R z wR wZ) resZE
  rwa [bd, maj_resZE] at this

/-- A torus perturbation `ΔK = (ΔR, Δz, 0, 0, Δw_R, Δw_z)` (angles are not perturbed). -/
def dpt (dR dz dwR dwZ : WEll1Z2 r) : Fin 6 → WEll1Z2 r := ![dR, dz, 0, 0, dwR, dwZ]

/-- The norm bounds of a perturbation. -/
def dbd (dR dz dwR dwZ : WEll1Z2 r) : Fin 6 → ℝ := majPt ‖dR‖ ‖dz‖ 0 0 ‖dwR‖ ‖dwZ‖

/-- The perturbation is bounded by `dbd`. -/
theorem norm_dpt_le (dR dz dwR dwZ : WEll1Z2 r) :
    ∀ i, ‖dpt dR dz dwR dwZ i‖ ≤ dbd dR dz dwR dwZ i := by
  intro i
  fin_cases i <;> simp [dpt, dbd, majPt]

/-- `pt + dpt` is the perturbed torus. -/
theorem pt_add_dpt (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    pt R z wR wZ + dpt dR dz dwR dwZ = pt (R + dR) (z + dz) (wR + dwR) (wZ + dwZ) := by
  funext i
  fin_cases i <;> simp [pt, dpt]

/-- **Derivative bound** for the `R`-residual: `‖Dres_R(K)ΔK‖_r ≤ r̂es_R'(a)·b`. -/
theorem deriv_resR_le (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    ‖deriv (pt R z wR wZ) (dpt dR dz dwR dwZ) resRE‖ ≤
      majD (bd R z wR wZ) (dbd dR dz dwR dwZ) resRE :=
  norm_deriv_le (norm_pt_le R z wR wZ) (norm_dpt_le dR dz dwR dwZ) resRE

/-- **Derivative bound** for the `z`-residual. -/
theorem deriv_resZ_le (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    ‖deriv (pt R z wR wZ) (dpt dR dz dwR dwZ) resZE‖ ≤
      majD (bd R z wR wZ) (dbd dR dz dwR dwZ) resZE :=
  norm_deriv_le (norm_pt_le R z wR wZ) (norm_dpt_le dR dz dwR dwZ) resZE

/-- **Taylor bound** for the `R`-residual (the `(H-field)` estimate in cleared form):
`‖res_R(K + ΔK) − res_R(K) − Dres_R(K)ΔK‖_r ≤ ½ r̂es_R''(a + b)[b, b]`. -/
theorem taylor_resR (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    ‖eval (pt (R + dR) (z + dz) (wR + dwR) (wZ + dwZ)) resRE - eval (pt R z wR wZ) resRE -
        deriv (pt R z wR wZ) (dpt dR dz dwR dwZ) resRE‖ ≤
      majD2 (bd R z wR wZ + dbd dR dz dwR dwZ) (dbd dR dz dwR dwZ) resRE / 2 := by
  rw [← pt_add_dpt]
  exact norm_taylor_le (norm_pt_le R z wR wZ) (norm_dpt_le dR dz dwR dwZ) resRE

/-- **Taylor bound** for the `z`-residual. -/
theorem taylor_resZ (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    ‖eval (pt (R + dR) (z + dz) (wR + dwR) (wZ + dwZ)) resZE - eval (pt R z wR wZ) resZE -
        deriv (pt R z wR wZ) (dpt dR dz dwR dwZ) resZE‖ ≤
      majD2 (bd R z wR wZ + dbd dR dz dwR dwZ) (dbd dR dz dwR dwZ) resZE / 2 := by
  rw [← pt_add_dpt]
  exact norm_taylor_le (norm_pt_le R z wR wZ) (norm_dpt_le dR dz dwR dwZ) resZE

/-- **Lipschitz bound** for `D`: `‖D(K + ΔK) − D(K)‖_r ≤ D̂'(a + b)·b`. -/
theorem lipschitz_D (R z wR wZ dR dz dwR dwZ : WEll1Z2 r) :
    ‖eval (pt (R + dR) (z + dz) (wR + dwR) (wZ + dwZ)) DE - eval (pt R z wR wZ) DE‖ ≤
      majD (bd R z wR wZ + dbd dR dz dwR dwZ) (dbd dR dz dwR dwZ) DE := by
  rw [← pt_add_dpt]
  exact norm_eval_add_sub_le (norm_pt_le R z wR wZ) (norm_dpt_le dR dz dwR dwZ) DE

/-- **`1/D` by the Neumann series**: if `‖D(K) − D̄‖_r < |D̄|` then `D(K)` is invertible in
`ℓ¹_r(ℤ²)` with `‖D(K)⁻¹‖_r ≤ 1/(|D̄| − ‖D(K) − D̄‖_r)`. -/
theorem inv_D_bound (R z wR wZ : WEll1Z2 r) (Dbar : ℂ)
    (h : ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖ < ‖Dbar‖) :
    IsUnit (eval (pt R z wR wZ) DE) ∧
      ‖Ring.inverse (eval (pt R z wR wZ) DE)‖ ≤
        1 / (‖Dbar‖ - ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖) :=
  WEll1Z2.inverse_bound _ Dbar h

/-- The field-line vector field `X_R(K) = 2εR Ps(K)/D(K)`:
`‖X_R(K)‖_r ≤ (‖R‖/2)P̂s / (|D̄| − ‖D(K) − D̄‖_r)`. -/
theorem norm_XR_le (R z wR wZ : WEll1Z2 r) (Dbar : ℂ)
    (h : ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖ < ‖Dbar‖) :
    ‖eval (pt R z wR wZ) XRnumE * Ring.inverse (eval (pt R z wR wZ) DE)‖ ≤
      ‖R‖ / 2 * Psmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) /
        (‖Dbar‖ - ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖) := by
  have hi := (inv_D_bound R z wR wZ Dbar h).2
  have hn := norm_XRnum_le R z wR wZ
  rw [div_eq_mul_one_div]
  exact (norm_mul_le _ _).trans
    (mul_le_mul hn hi (norm_nonneg _) ((norm_nonneg _).trans hn))

/-- The field-line vector field `X_z(K) = εR² Pz(K)/D(K)`:
`‖X_z(K)‖_r ≤ (‖R‖²/4)P̂z / (|D̄| − ‖D(K) − D̄‖_r)`. -/
theorem norm_XZ_le (R z wR wZ : WEll1Z2 r) (Dbar : ℂ)
    (h : ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖ < ‖Dbar‖) :
    ‖eval (pt R z wR wZ) XZnumE * Ring.inverse (eval (pt R z wR wZ) DE)‖ ≤
      ‖R‖ ^ 2 / 4 * Pzmaj ‖R‖ ‖z‖ (Real.exp r) (Real.exp r) /
        (‖Dbar‖ - ‖eval (pt R z wR wZ) DE - algebraMap ℂ _ Dbar‖) := by
  have hi := (inv_D_bound R z wR wZ Dbar h).2
  have hn := norm_XZnum_le R z wR wZ
  rw [div_eq_mul_one_div]
  exact (norm_mul_le _ _).trans
    (mul_le_mul hn hi (norm_nonneg _) ((norm_nonneg _).trans hn))

end Torus

/-! ## Sanity checks -/

/-- Sanity (special case): on the axis `R = 1`, `z = 0`, `D = 1` for every `c, s`. -/
theorem eval_DE_axis (c s wR wZ : ℝ) : eval (realPt 1 0 c s wR wZ) DE = 1 := by
  rw [eval_DE]; simp [Dfun, sfun, sgfun]

/-- Sanity (degenerate strip): the majorant of `D` at `‖R‖ = 1`, `‖z‖ = 0`, `e^0 = 1` is `3/2`. -/
theorem maj_DE_axis : maj (majPt 1 0 1 1 0 0) DE = 3 / 2 := by
  rw [maj_DE]; norm_num [Dmaj, sfunMaj, sgfunMaj]

/-- Rejected fixture: the majorant does not see the cancellation `D = 1` on the axis
(`D̂ = 3/2 > 1`), so `1/D` must be bounded by the Neumann series around a constant `D̄`. -/
theorem not_maj_DE_le_one : ¬ maj (majPt 1 0 1 1 0 0) DE ≤ 1 := by
  rw [maj_DE_axis]; norm_num

end PlasmaLean.Design.KamTorusA
