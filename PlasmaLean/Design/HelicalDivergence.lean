/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalStellarator
public import PlasmaLean.Theory.Fields.ClebschDivergence

/-!
# Actual derivatives and `∇ · B = 0` for a helically symmetric field family

Unit-pitch helical symmetry `K = (-x₁, x₀, 1)`, `D = |K|² = 1 + r²`. With
`C = cos 2z`, `S = sin 2z`, `P = (x₀² - x₁²) C + 2 x₀ x₁ S` (`= r² cos 2χ`), the flux family
`ψ = r² + (a + b r²) P` is helically invariant for all parameters `a, b`. The field is
`B = D⁻¹ (∇ψ × K + F(ψ) K)` with `F(ψ) = F₀ + F₁ ψ`.

Derivatives are computed in forward mode: every scalar layer (`C`, `S`, `P`, `ψ`, the
gradient coordinates `G k`, the numerators `N k`, …) has an explicit derivative operator
proved with Mathlib's calculus rules. Results:

* `field_hasFDerivAt`: the actual Fréchet derivative of `B` at every point (`D ≥ 1`);
* `field_divergence_free`: `∇ · B = 0` everywhere, for all `a, b, F₀, F₁`;
* `field_symmetric`, `field_firstIntegral`: helical symmetry of the force and flux surfaces;
* `stellarator_field_eq`, `stellarator_divergence_free`: the field of
  `HelicalStellarator` is the case `a = ε, b = 0, F₀ = F, F₁ = 0`, hence divergence free.

No coil origin is claimed.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.HelicalFamily
open PlasmaLean.Fields PlasmaLean.Kinetic WithLp

/-- Coordinate functional. -/
abbrev pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- `cos 2z`. -/
@[expose] def C (y : Space) : ℝ := Real.cos (2 * y 2)
/-- `sin 2z`. -/
@[expose] def S (y : Space) : ℝ := Real.sin (2 * y 2)
/-- Squared distance from the axis. -/
@[expose] def r2 (y : Space) : ℝ := y 0 ^ 2 + y 1 ^ 2
/-- `D = 1 + r² = |K|²`. -/
@[expose] def D (y : Space) : ℝ := 1 + r2 y
/-- `1 / D`. -/
@[expose] def Dinv (y : Space) : ℝ := (D y)⁻¹
/-- Second helical harmonic `r² cos 2χ`. -/
@[expose] def P (y : Space) : ℝ := (y 0 ^ 2 - y 1 ^ 2) * C y + 2 * y 0 * y 1 * S y
/-- Conjugate harmonic `r² sin 2χ`. -/
@[expose] def Q (y : Space) : ℝ := -(y 0 ^ 2 - y 1 ^ 2) * S y + 2 * y 0 * y 1 * C y
/-- `∂P/∂x₀`. -/
@[expose] def P0 (y : Space) : ℝ := 2 * y 0 * C y + 2 * y 1 * S y
/-- `∂P/∂x₁`. -/
@[expose] def P1 (y : Space) : ℝ := -2 * y 1 * C y + 2 * y 0 * S y
/-- Radial amplitude `a + b r²`. -/
@[expose] def amp (a b : ℝ) (y : Space) : ℝ := a + b * r2 y
/-- Flux family `ψ = r² + (a + b r²) P`. -/
@[expose] def psi (a b : ℝ) (y : Space) : ℝ := r2 y + amp a b y * P y
/-- `∂ψ/∂x₀`. -/
@[expose] def G0 (a b : ℝ) (y : Space) : ℝ := 2 * y 0 + 2 * b * y 0 * P y + amp a b y * P0 y
/-- `∂ψ/∂x₁`. -/
@[expose] def G1 (a b : ℝ) (y : Space) : ℝ := 2 * y 1 + 2 * b * y 1 * P y + amp a b y * P1 y
/-- `∂ψ/∂z`. -/
@[expose] def G2 (a b : ℝ) (y : Space) : ℝ := 2 * (amp a b y * Q y)
/-- Gradient of `ψ`. -/
@[expose] def gPsi (a b : ℝ) (y : Space) : Space := toLp 2 ![G0 a b y, G1 a b y, G2 a b y]
/-- Flux function of the axial field, `F(ψ) = F₀ + F₁ ψ`. -/
@[expose] def Fv (a b F0 F1 : ℝ) (y : Space) : ℝ := F0 + F1 * psi a b y
/-- Numerator of `B₀`. -/
@[expose] def N0 (a b F0 F1 : ℝ) (y : Space) : ℝ :=
  G1 a b y - y 0 * G2 a b y - Fv a b F0 F1 y * y 1
/-- Numerator of `B₁`. -/
@[expose] def N1 (a b F0 F1 : ℝ) (y : Space) : ℝ :=
  -(y 1 * G2 a b y) - G0 a b y + Fv a b F0 F1 y * y 0
/-- Numerator of `B₂`. -/
@[expose] def N2 (a b F0 F1 : ℝ) (y : Space) : ℝ :=
  y 0 * G0 a b y + y 1 * G1 a b y + Fv a b F0 F1 y

/-- The helically symmetric field `B = D⁻¹ (∇ψ × K + F(ψ) K)`, in coordinates. -/
@[expose] def field (a b F0 F1 : ℝ) (y : Space) : Space :=
  toLp 2 ![Dinv y * N0 a b F0 F1 y, Dinv y * N1 a b F0 F1 y, Dinv y * N2 a b F0 F1 y]

/-! ## Forward-mode derivative operators -/

/-- Derivative of `C`. -/
@[expose] def dC (x : Space) : Space →L[ℝ] ℝ := (-2 * S x) • pr 2
/-- Derivative of `S`. -/
@[expose] def dS (x : Space) : Space →L[ℝ] ℝ := (2 * C x) • pr 2
/-- Derivative of `r²`. -/
@[expose] def dR (x : Space) : Space →L[ℝ] ℝ := (2 * x 0) • pr 0 + (2 * x 1) • pr 1
/-- Derivative of `1/D`. -/
@[expose] def dDinv (x : Space) : Space →L[ℝ] ℝ := (-(D x ^ 2)⁻¹) • dR x
/-- Derivative of `P`. -/
@[expose] def dP (x : Space) : Space →L[ℝ] ℝ :=
  (x 0 ^ 2 - x 1 ^ 2) • dC x + C x • ((2 * x 0) • pr 0 - (2 * x 1) • pr 1) +
    (2 * x 0 * x 1) • dS x + S x • ((2 * x 1) • pr 0 + (2 * x 0) • pr 1)
/-- Derivative of `Q`. -/
@[expose] def dQ (x : Space) : Space →L[ℝ] ℝ :=
  (-(x 0 ^ 2 - x 1 ^ 2)) • dS x - S x • ((2 * x 0) • pr 0 - (2 * x 1) • pr 1) +
    (2 * x 0 * x 1) • dC x + C x • ((2 * x 1) • pr 0 + (2 * x 0) • pr 1)
/-- Derivative of `P0`. -/
@[expose] def dP0 (x : Space) : Space →L[ℝ] ℝ :=
  (2 * x 0) • dC x + C x • ((2 : ℝ) • pr 0) + (2 * x 1) • dS x + S x • ((2 : ℝ) • pr 1)
/-- Derivative of `P1`. -/
@[expose] def dP1 (x : Space) : Space →L[ℝ] ℝ :=
  (-2 * x 1) • dC x + C x • ((-2 : ℝ) • pr 1) + (2 * x 0) • dS x + S x • ((2 : ℝ) • pr 0)
/-- Derivative of `amp`. -/
@[expose] def dA (b : ℝ) (x : Space) : Space →L[ℝ] ℝ := b • dR x
/-- Derivative of `ψ`. -/
@[expose] def dPsi (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  dR x + amp a b x • dP x + P x • dA b x
/-- Derivative of `G0`. -/
@[expose] def dG0 (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 : ℝ) • pr 0 + (2 * b) • (x 0 • dP x + P x • pr 0) + amp a b x • dP0 x + P0 x • dA b x
/-- Derivative of `G1`. -/
@[expose] def dG1 (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 : ℝ) • pr 1 + (2 * b) • (x 1 • dP x + P x • pr 1) + amp a b x • dP1 x + P1 x • dA b x
/-- Derivative of `G2`. -/
@[expose] def dG2 (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 : ℝ) • (amp a b x • dQ x + Q x • dA b x)
/-- Derivative of `F(ψ)`. -/
@[expose] def dF (a b F1 : ℝ) (x : Space) : Space →L[ℝ] ℝ := F1 • dPsi a b x
/-- Derivative of `N0`. -/
@[expose] def dN0 (a b F0 F1 : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  dG1 a b x - (x 0 • dG2 a b x + G2 a b x • pr 0) -
    (Fv a b F0 F1 x • pr 1 + x 1 • dF a b F1 x)
/-- Derivative of `N1`. -/
@[expose] def dN1 (a b F0 F1 : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  -(x 1 • dG2 a b x + G2 a b x • pr 1) - dG0 a b x +
    (Fv a b F0 F1 x • pr 0 + x 0 • dF a b F1 x)
/-- Derivative of `N2`. -/
@[expose] def dN2 (a b _F0 F1 : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (x 0 • dG0 a b x + G0 a b x • pr 0) + (x 1 • dG1 a b x + G1 a b x • pr 1) + dF a b F1 x

/-- Derivative of a field coordinate `D⁻¹ N`. -/
@[expose] def dB (x : Space) (N : ℝ) (dN : Space →L[ℝ] ℝ) : Space →L[ℝ] ℝ :=
  Dinv x • dN + N • dDinv x

/-- The derivative of the field, assembled from its coordinates. -/
@[expose] def fieldDeriv (a b F0 F1 : ℝ) (x : Space) : Space →L[ℝ] Space :=
  (dB x (N0 a b F0 F1 x) (dN0 a b F0 F1 x)).smulRight (basis 0) +
  (dB x (N1 a b F0 F1 x) (dN1 a b F0 F1 x)).smulRight (basis 1) +
  (dB x (N2 a b F0 F1 x) (dN2 a b F0 F1 x)).smulRight (basis 2)

/-! ## Layered derivative proofs -/

section Derivs
variable (a b F0 F1 : ℝ) (x : Space)

/-- Transfer a derivative along a pointwise function identity and an operator identity. -/
theorem hfd {f g : Space → ℝ} {L L' : Space →L[ℝ] ℝ} {x : Space} (h : HasFDerivAt g L x)
    (hf : ∀ y, f y = g y) (hL : L = L') : HasFDerivAt f L' x := by
  rw [show f = g from funext hf, ← hL]; exact h

theorem hasFDerivAt_pr (i : Fin 3) : HasFDerivAt (fun y : Space => y i) (pr i) x :=
  (pr i).hasFDerivAt

theorem hasFDerivAt_C : HasFDerivAt C (dC x) x := by
  have := ((hasFDerivAt_pr x 2).const_mul 2).cos
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dC, S]; ring

theorem hasFDerivAt_S : HasFDerivAt S (dS x) x := by
  have := ((hasFDerivAt_pr x 2).const_mul 2).sin
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dS, C]; ring

theorem hasFDerivAt_r2 : HasFDerivAt r2 (dR x) x := by
  have := ((hasFDerivAt_pr x 0).pow 2).add ((hasFDerivAt_pr x 1).pow 2)
  refine hfd this (fun y => by simp [r2]) ?_
  ext v; simp [dR]

theorem D_pos (y : Space) : 0 < D y := by unfold D r2; positivity

theorem hasFDerivAt_Dinv : HasFDerivAt Dinv (dDinv x) x := by
  have hD : HasFDerivAt D (dR x) x := hfd ((hasFDerivAt_r2 x).const_add 1) (fun y => rfl) rfl
  have := (hasDerivAt_inv (D_pos x).ne').hasFDerivAt.comp x hD
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dDinv]; ring

theorem hasFDerivAt_P : HasFDerivAt P (dP x) x := by
  have h0 := hasFDerivAt_pr x 0
  have h1 := hasFDerivAt_pr x 1
  have := (((h0.pow 2).sub (h1.pow 2)).mul (hasFDerivAt_C x)).add
    (((h0.mul h1).const_mul 2).mul (hasFDerivAt_S x))
  refine hfd this (fun y => by simp only [P, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]; ring) ?_
  ext v; simp [dP]; ring

theorem hasFDerivAt_Q : HasFDerivAt Q (dQ x) x := by
  have h0 := hasFDerivAt_pr x 0
  have h1 := hasFDerivAt_pr x 1
  have := (((h0.pow 2).sub (h1.pow 2)).neg.mul (hasFDerivAt_S x)).add
    (((h0.mul h1).const_mul 2).mul (hasFDerivAt_C x))
  refine hfd this (fun y => by
    simp only [Q, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]; ring) ?_
  ext v; simp [dQ]; ring

theorem hasFDerivAt_P0 : HasFDerivAt P0 (dP0 x) x := by
  have := (((hasFDerivAt_pr x 0).const_mul 2).mul (hasFDerivAt_C x)).add
    (((hasFDerivAt_pr x 1).const_mul 2).mul (hasFDerivAt_S x))
  refine hfd this (fun y => by simp [P0]) ?_
  ext v; simp [dP0]; ring

theorem hasFDerivAt_P1 : HasFDerivAt P1 (dP1 x) x := by
  have := (((hasFDerivAt_pr x 1).const_mul (-2)).mul (hasFDerivAt_C x)).add
    (((hasFDerivAt_pr x 0).const_mul 2).mul (hasFDerivAt_S x))
  refine hfd this (fun y => by simp [P1]) ?_
  ext v; simp [dP1]; ring

theorem hasFDerivAt_amp : HasFDerivAt (amp a b) (dA b x) x := by
  have := ((hasFDerivAt_r2 x).const_mul b).const_add a
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dA]

theorem hasFDerivAt_psi : HasFDerivAt (psi a b) (dPsi a b x) x := by
  have := (hasFDerivAt_r2 x).add ((hasFDerivAt_amp a b x).mul (hasFDerivAt_P x))
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dPsi]; ring

theorem hasFDerivAt_G0 : HasFDerivAt (G0 a b) (dG0 a b x) x := by
  have h0 := hasFDerivAt_pr x 0
  have := ((h0.const_mul 2).add (((h0.mul (hasFDerivAt_P x)).const_mul (2 * b)))).add
    ((hasFDerivAt_amp a b x).mul (hasFDerivAt_P0 x))
  refine hfd this (fun y => by simp [G0]; ring) ?_
  ext v; simp [dG0]; ring

theorem hasFDerivAt_G1 : HasFDerivAt (G1 a b) (dG1 a b x) x := by
  have h1 := hasFDerivAt_pr x 1
  have := ((h1.const_mul 2).add (((h1.mul (hasFDerivAt_P x)).const_mul (2 * b)))).add
    ((hasFDerivAt_amp a b x).mul (hasFDerivAt_P1 x))
  refine hfd this (fun y => by simp [G1]; ring) ?_
  ext v; simp [dG1]; ring

theorem hasFDerivAt_G2 : HasFDerivAt (G2 a b) (dG2 a b x) x := by
  have := ((hasFDerivAt_amp a b x).mul (hasFDerivAt_Q x)).const_mul 2
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dG2]

theorem hasFDerivAt_Fv : HasFDerivAt (Fv a b F0 F1) (dF a b F1 x) x := by
  have := ((hasFDerivAt_psi a b x).const_mul F1).const_add F0
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dF]

theorem hasFDerivAt_N0 : HasFDerivAt (N0 a b F0 F1) (dN0 a b F0 F1 x) x := by
  have := ((hasFDerivAt_G1 a b x).sub ((hasFDerivAt_pr x 0).mul (hasFDerivAt_G2 a b x))).sub
    ((hasFDerivAt_Fv a b F0 F1 x).mul (hasFDerivAt_pr x 1))
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dN0]

theorem hasFDerivAt_N1 : HasFDerivAt (N1 a b F0 F1) (dN1 a b F0 F1 x) x := by
  have := (((hasFDerivAt_pr x 1).mul (hasFDerivAt_G2 a b x)).neg.sub
    (hasFDerivAt_G0 a b x)).add ((hasFDerivAt_Fv a b F0 F1 x).mul (hasFDerivAt_pr x 0))
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dN1]

theorem hasFDerivAt_N2 : HasFDerivAt (N2 a b F0 F1) (dN2 a b F0 F1 x) x := by
  have := (((hasFDerivAt_pr x 0).mul (hasFDerivAt_G0 a b x)).add
    ((hasFDerivAt_pr x 1).mul (hasFDerivAt_G1 a b x))).add (hasFDerivAt_Fv a b F0 F1 x)
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dN2]

/-- The actual Fréchet derivative of the helical field, at every point. -/
theorem field_hasFDerivAt : HasFDerivAt (field a b F0 F1) (fieldDeriv a b F0 F1 x) x := by
  have hc (N : Space → ℝ) (dN : Space →L[ℝ] ℝ) (h : HasFDerivAt N dN x) :
      HasFDerivAt (fun y => Dinv y * N y) (dB x (N x) dN) x := by
    exact (hasFDerivAt_Dinv x).mul h
  have hB := hasFDerivAt_of_coords (B := field a b F0 F1)
    (L := ![dB x (N0 a b F0 F1 x) (dN0 a b F0 F1 x), dB x (N1 a b F0 F1 x) (dN1 a b F0 F1 x),
      dB x (N2 a b F0 F1 x) (dN2 a b F0 F1 x)]) (x := x) (fun k => by
        fin_cases k
        · exact hc _ _ (hasFDerivAt_N0 a b F0 F1 x)
        · exact hc _ _ (hasFDerivAt_N1 a b F0 F1 x)
        · exact hc _ _ (hasFDerivAt_N2 a b F0 F1 x))
  refine hB.congr_fderiv ?_
  simp [fieldDeriv, Fin.sum_univ_three]

end Derivs

/-- Entries of the derivative operator: `(DB eᵢ)ₖ` from the coordinate derivatives. -/
theorem fieldDeriv_apply (a b F0 F1 : ℝ) (x v : Space) :
    fieldDeriv a b F0 F1 x v 0 = dB x (N0 a b F0 F1 x) (dN0 a b F0 F1 x) v ∧
    fieldDeriv a b F0 F1 x v 1 = dB x (N1 a b F0 F1 x) (dN1 a b F0 F1 x) v ∧
    fieldDeriv a b F0 F1 x v 2 = dB x (N2 a b F0 F1 x) (dN2 a b F0 F1 x) v := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldDeriv, basis]

/-- `∇ · B = 0` at every point, for every member of the family. -/
theorem field_divergence_free (a b F0 F1 : ℝ) (x : Space) :
    divergence (fderiv ℝ (field a b F0 F1) x) = 0 := by
  rw [(field_hasFDerivAt a b F0 F1 x).fderiv, divergence_apply]
  obtain ⟨e0, -, -⟩ := fieldDeriv_apply a b F0 F1 x (basis 0)
  obtain ⟨-, e1, -⟩ := fieldDeriv_apply a b F0 F1 x (basis 1)
  obtain ⟨-, -, e2⟩ := fieldDeriv_apply a b F0 F1 x (basis 2)
  rw [e0, e1, e2]
  have hD := (D_pos x).ne'
  simp only [Fin.isValue, dB, Dinv, dN0, dG1, dP, dC, neg_mul, dS, smul_add, P, amp, dP1, P1,
    dA, dR, dG2, dQ, neg_sub, Q, G2, Fv, psi, dF, dPsi, N0, G1, dDinv, neg_smul, smul_neg,
    basis, add_apply, smul_apply,
    sub_apply, PiLp.proj_apply, ne_eq, one_ne_zero, not_false_eq_true,
    PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, Fin.reduceEq, PiLp.single_eq_same, mul_one,
    sub_zero, zero_add, add_zero, zero_sub, mul_neg, neg_apply, neg_zero,
    dN1, neg_add_rev, dG0, dP0, P0, N1, G0, zero_ne_one, sub_neg_eq_add, dN2, N2, sub_self,
    neg_neg]
  unfold D r2 at hD ⊢
  field_simp
  ring

/-! ## Vector form, helical symmetry and the earlier example -/

open PlasmaLean.Design.HelicalStellarator (K K_norm_sq)

/-- The gradient formula for `ψ`. -/
theorem psi_hasFDerivAt (a b : ℝ) (x : Space) :
    HasFDerivAt (psi a b) (innerSL ℝ (gPsi a b x)) x := by
  refine (hasFDerivAt_psi a b x).congr_fderiv ?_
  ext v
  simp [dPsi, dR, dP, dA, dC, dS, gPsi, G0, G1, G2, P0, P1, P, Q, amp,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- `ψ` is helically invariant: `⟪K, ∇ψ⟫ = 0`. -/
theorem psi_invariant (a b : ℝ) (x : Space) : ⟪K x, gPsi a b x⟫ = 0 := by
  simp [K, helicalK_apply, gPsi, G0, G1, G2, P0, P1, P, Q, amp, r2,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- `1/D = 1/|K|²`. -/
theorem Dinv_eq (y : Space) : Dinv y = (‖K y‖ ^ 2)⁻¹ := by
  rw [K_norm_sq, Dinv, D, r2, HelicalStellarator.r2]; ring

/-- Vector form of the field: `B = |K|⁻² (∇ψ × K + F(ψ) K)`. -/
theorem field_eq_cross (a b F0 F1 : ℝ) (y : Space) :
    field a b F0 F1 y =
      (‖K y‖ ^ 2)⁻¹ • (cross (gPsi a b y) (K y) + Fv a b F0 F1 y • K y) := by
  rw [← Dinv_eq]
  ext i
  fin_cases i <;>
    simp [field, cross, crossProduct, K, helicalK_apply, gPsi, N0, N1, N2] <;> ring

/-- Helical symmetry of the magnetic force, for every member of the family. -/
theorem field_symmetric (a b F0 F1 : ℝ) : SymmetricFlux (field a b F0 F1) (gPsi a b) K := by
  intro x v
  rw [field_eq_cross]
  have hK : ‖K x‖ ^ 2 ≠ 0 := by
    rw [K_norm_sq]; unfold HelicalStellarator.r2; positivity
  exact symmetricFlux_of_cross (K x) (gPsi a b x) v _ (psi_invariant a b x) hK

/-- `ψ` is an exact field-line first integral. -/
theorem field_firstIntegral (a b F0 F1 : ℝ) :
    FirstIntegralOn (field a b F0 F1) (psi a b) Set.univ :=
  (field_symmetric a b F0 F1).firstIntegral (psi_hasFDerivAt a b)

/-- The field of `HelicalStellarator` is the member `a = ε, b = 0, F₀ = F, F₁ = 0`. -/
theorem stellarator_field_eq (ε F : ℝ) :
    HelicalStellarator.field ε F = field ε 0 F 0 := by
  funext y
  rw [field_eq_cross, HelicalStellarator.field]
  have hg : HelicalStellarator.psiGrad ε y = gPsi ε 0 y := by
    ext i
    fin_cases i
    · simp [HelicalStellarator.psiGrad, gPsi, G0, P0, P, amp, C, S]
    · simp [HelicalStellarator.psiGrad, gPsi, G1, P1, P, amp, C, S]
    · simp [HelicalStellarator.psiGrad, gPsi, G2, Q, amp, C, S]; ring
  rw [hg]
  simp [Fv]

/-- The helical stellarator field of `HelicalStellarator` is divergence free. -/
theorem stellarator_divergence_free (ε F : ℝ) (x : Space) :
    divergence (fderiv ℝ (HelicalStellarator.field ε F) x) = 0 := by
  rw [stellarator_field_eq]
  exact field_divergence_free ε 0 F 0 x

end PlasmaLean.Design.HelicalFamily
