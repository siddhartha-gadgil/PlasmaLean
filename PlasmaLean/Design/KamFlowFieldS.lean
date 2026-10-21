/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowField
public import PlasmaLean.Theory.KAM.PolyExprSStrip

/-!
# Fields in flow form with an inverse-square-root node (`FlowFieldS`)

The interface `FlowField` of `Design/KamFlowField` takes polynomial field components. The
guiding-centre field `B̃ = B + ρ_s ∇×b` (`notes/theory/after-kam.md` §1) is polynomial in
`(u, z, c, s)` and **one** algebraic variable `W = q^{−1/2}` (`q = R⁸|B|²`), so its flow form is a
`PolyExprS` (`Theory/KAM/PolyExprS`): polynomial expressions with the node
`isqrt c d = (c + d)^{−1/2}`. This file is the interface for such fields; the Newton step and the
KAM iteration for it are `Design/KamFlowFrameS`, `Design/KamFlowStepS`, `Design/KamFlowIterationS`
(the same proofs as for `FlowField`, with the validity of the node carried along).

Differences from `FlowField`:
* the expressions are `PolyExprS ℂ (Fin 6)`; partial derivatives `pdS` and the `φ`-derivative
  `phiDS` are the directional derivatives of `PolyExprS` (for the node:
  `D(c + d)^{−1/2} = −½ ((c + d)^{−1/2})³ Dd`);
* the identities are required only at tori where all six expressions are **strip valid**
  (`FlowFieldS.Good`: some strip `ρ > 0` and bounds on `(u, z, cos 2φ, sin 2φ)` at which every
  node has deviation majorant below its centre);
* the flux primitive may have a `dφ`-component: `α = (P_a/R) dR + (P_b/R²) dz + P_c dφ`. The
  guiding-centre primitive is `α̃ = α − ρ_s b♭` and `b♭` has the `dφ`-component `R b_φ`, which
  is not removable by a polynomial gauge. The flux identities become
  `R ∂_u P_b − 2P_b − R² ∂_z P_a = D`, `R² ∂_φ P_a − R³ ∂_u P_c = n_z`,
  `R ∂_φ P_b − R³ ∂_z P_c = −n_R`;
* the torsion numerator is *defined* by its formula (`FlowFieldS.Pof`) rather than supplied.

**Sanity.** `FlowField.toS` embeds every polynomial flow field (with `P_c = 0`), so the old
instance `field14` is an instance of the new interface (`FlowField.toS_resR`: the residuals agree).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM Complex WEll1Z2

open PolyExprS (SValid RealConstsS)

/-! ## Partial derivatives of expressions with the node -/

section Partials

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- The partial derivative `∂_i P(x)` of an expression with the node. -/
def pdS (x : Fin 6 → A) (i : Fin 6) (e : PolyExprS ℂ (Fin 6)) : A :=
  PolyExprS.deriv x (Pi.single i 1) e

/-- The `φ`-derivative `∂_c P·(−2s) + ∂_s P·(2c)`. -/
def phiDS (x : Fin 6 → A) (e : PolyExprS ℂ (Fin 6)) : A :=
  pdS x 2 e * (-2 * x 3) + pdS x 3 e * (2 * x 2)

/-- Variables with index `≥ 4` (the velocities) do not occur. -/
def NoWS : PolyExprS ℂ (Fin 6) → Prop
  | .const _ => True
  | .var i => i.val < 4
  | .add p q => NoWS p ∧ NoWS q
  | .sub p q => NoWS p ∧ NoWS q
  | .mul p q => NoWS p ∧ NoWS q
  | .isqrt _ d => NoWS d

/-- Evaluation only depends on the variables that occur. -/
theorem eval_congr_noWS {x y : Fin 6 → A} (hxy : ∀ i : Fin 6, i.val < 4 → x i = y i)
    (e : PolyExprS ℂ (Fin 6)) (he : NoWS e) : PolyExprS.eval x e = PolyExprS.eval y e := by
  induction e with
  | const _ => rfl
  | var i => exact hxy i he
  | add p q hp hq => simp only [PolyExprS.eval, hp he.1, hq he.2]
  | sub p q hp hq => simp only [PolyExprS.eval, hp he.1, hq he.2]
  | mul p q hp hq => simp only [PolyExprS.eval, hp he.1, hq he.2]
  | isqrt c d hd => simp only [PolyExprS.eval, hd he]

/-- Derivatives only depend on the variables that occur. -/
theorem deriv_congr_noWS {x y h h' : Fin 6 → A} (hxy : ∀ i : Fin 6, i.val < 4 → x i = y i)
    (hhh : ∀ i : Fin 6, i.val < 4 → h i = h' i) (e : PolyExprS ℂ (Fin 6)) (he : NoWS e) :
    PolyExprS.deriv x h e = PolyExprS.deriv y h' e := by
  induction e with
  | const _ => rfl
  | var i => exact hhh i he
  | add p q hp hq => simp only [PolyExprS.deriv, hp he.1, hq he.2]
  | sub p q hp hq => simp only [PolyExprS.deriv, hp he.1, hq he.2]
  | mul p q hp hq =>
    simp only [PolyExprS.deriv, hp he.1, hq he.2, eval_congr_noWS hxy p he.1,
      eval_congr_noWS hxy q he.2]
  | isqrt c d hd =>
    simp only [PolyExprS.deriv, hd he]
    rw [eval_congr_noWS hxy (.isqrt c d) he]

/-- The partial derivative in a velocity variable vanishes. -/
theorem pdS_noW {x : Fin 6 → A} {i : Fin 6} (hi : 4 ≤ i.val) (e : PolyExprS ℂ (Fin 6))
    (he : NoWS e) : pdS x i e = 0 := by
  induction e with
  | const _ => simp [pdS, PolyExprS.deriv]
  | var j =>
    simp only [pdS, PolyExprS.deriv]
    have : j ≠ i := fun h => by subst h; simp [NoWS] at he; omega
    simp [this]
  | add p q hp hq =>
    simp only [pdS, PolyExprS.deriv] at *; rw [hp he.1, hq he.2, add_zero]
  | sub p q hp hq =>
    simp only [pdS, PolyExprS.deriv] at *; rw [hp he.1, hq he.2, sub_zero]
  | mul p q hp hq =>
    simp only [pdS, PolyExprS.deriv] at *; rw [hp he.1, hq he.2, zero_mul, mul_zero, add_zero]
  | isqrt c d hd =>
    simp only [pdS, PolyExprS.deriv] at *; rw [hd he, mul_zero]

/-- The embedding of polynomial expressions keeps the absence of velocities. -/
theorem noWS_ofPoly : ∀ e : PolyExpr ℂ (Fin 6), NoW e → NoWS (PolyExprS.ofPoly e)
  | .const _, _ => trivial
  | .var _, h => h
  | .add p q, h => ⟨noWS_ofPoly p h.1, noWS_ofPoly q h.2⟩
  | .sub p q, h => ⟨noWS_ofPoly p h.1, noWS_ofPoly q h.2⟩
  | .mul p q, h => ⟨noWS_ofPoly p h.1, noWS_ofPoly q h.2⟩

/-- `pdS` of an embedded polynomial is `pd`. -/
theorem pdS_ofPoly (x : Fin 6 → A) (i : Fin 6) (e : PolyExpr ℂ (Fin 6)) :
    pdS x i (PolyExprS.ofPoly e) = pd x i e := PolyExprS.deriv_ofPoly _ _ _

/-- `phiDS` of an embedded polynomial is `phiD`. -/
theorem phiDS_ofPoly (x : Fin 6 → A) (e : PolyExpr ℂ (Fin 6)) :
    phiDS x (PolyExprS.ofPoly e) = phiD x e := by
  simp only [phiDS, phiD, pdS_ofPoly]

/-- The directional derivative is the sum of the partial derivatives `pdS`. -/
theorem deriv_eq_sum_pdS (x h : Fin 6 → A) (e : PolyExprS ℂ (Fin 6)) :
    PolyExprS.deriv x h e = ∑ i, h i * pdS x i e := PolyExprS.deriv_eq_sumS x h e

end Partials

/-- Expressions without velocities see only `(u, z, c, s)`. -/
theorem eval_xK_xB_S (ι : ℝ) (u z : FA) {e : PolyExprS ℂ (Fin 6)} (he : NoWS e) :
    PolyExprS.eval (xK ι u z) e = PolyExprS.eval (xB u z) e :=
  eval_congr_noWS (fun i hi => by fin_cases i <;> simp_all [xK, xB]) e he

/-- Partial derivatives of expressions without velocities see only `(u, z, c, s)`. -/
theorem pdS_xK_xB (ι : ℝ) (u z : FA) (i : Fin 6) {e : PolyExprS ℂ (Fin 6)} (he : NoWS e) :
    pdS (xK ι u z) i e = pdS (xB u z) i e :=
  deriv_congr_noWS (fun i hi => by fin_cases i <;> simp_all [xK, xB]) (fun _ _ => rfl) e he

/-! ## The interface -/

/-- **A field in flow form with one inverse-square-root node.** As `FlowField`, with expressions
`PolyExprS`, a `dφ`-component `P_c` of the flux primitive, and identities required only at tori
where the six expressions are strip valid (`Good`). -/
structure FlowFieldS where
  /-- `D = R³ B_φ`. -/
  Dp : PolyExprS ℂ (Fin 6)
  /-- `n_R = R⁴ B^R`. -/
  nRp : PolyExprS ℂ (Fin 6)
  /-- `n_z = R⁴ B^z`. -/
  nZp : PolyExprS ℂ (Fin 6)
  /-- Numerator `R·a` of the `dR`-coefficient of the flux primitive. -/
  Pap : PolyExprS ℂ (Fin 6)
  /-- Numerator `R²·b` of the `dz`-coefficient of the flux primitive. -/
  Pbp : PolyExprS ℂ (Fin 6)
  /-- The `dφ`-coefficient `c` of the flux primitive. -/
  Pcp : PolyExprS ℂ (Fin 6)
  /-- `D` does not involve the velocities. -/
  noW_Dp : NoWS Dp
  /-- `n_R` does not involve the velocities. -/
  noW_nRp : NoWS nRp
  /-- `n_z` does not involve the velocities. -/
  noW_nZp : NoWS nZp
  /-- `D` has real coefficients. -/
  real_Dp : RealConstsS Dp
  /-- `n_R` has real coefficients. -/
  real_nRp : RealConstsS nRp
  /-- `n_z` has real coefficients. -/
  real_nZp : RealConstsS nZp
  /-- **Divergence-free identity** at valid tori. -/
  divFree : ∀ u z : FA, (∃ ρ : ℝ, 0 < ρ ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd ρ (xB u z i) (a i)) ∧
      PolyExprS.Valid a Dp ∧ PolyExprS.Valid a nRp ∧ PolyExprS.Valid a nZp ∧
      PolyExprS.Valid a Pap ∧ PolyExprS.Valid a Pbp ∧ PolyExprS.Valid a Pcp) →
    (1 + u) * phiDS (xB u z) Dp - 3 * PolyExprS.eval (xB u z) nRp +
      (1 + u) * pdS (xB u z) 0 nRp + (1 + u) * pdS (xB u z) 1 nZp = 0
  /-- **Flux primitive identity** (a) at valid tori. -/
  flux_a : ∀ u z : FA, (∃ ρ : ℝ, 0 < ρ ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd ρ (xB u z i) (a i)) ∧
      PolyExprS.Valid a Dp ∧ PolyExprS.Valid a nRp ∧ PolyExprS.Valid a nZp ∧
      PolyExprS.Valid a Pap ∧ PolyExprS.Valid a Pbp ∧ PolyExprS.Valid a Pcp) →
    (1 + u) * pdS (xB u z) 0 Pbp - 2 * PolyExprS.eval (xB u z) Pbp -
      (1 + u) ^ 2 * pdS (xB u z) 1 Pap = PolyExprS.eval (xB u z) Dp
  /-- **Flux primitive identity** (b) at valid tori. -/
  flux_b : ∀ u z : FA, (∃ ρ : ℝ, 0 < ρ ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd ρ (xB u z i) (a i)) ∧
      PolyExprS.Valid a Dp ∧ PolyExprS.Valid a nRp ∧ PolyExprS.Valid a nZp ∧
      PolyExprS.Valid a Pap ∧ PolyExprS.Valid a Pbp ∧ PolyExprS.Valid a Pcp) →
    (1 + u) ^ 2 * phiDS (xB u z) Pap - (1 + u) ^ 3 * pdS (xB u z) 0 Pcp =
      PolyExprS.eval (xB u z) nZp
  /-- **Flux primitive identity** (c) at valid tori. -/
  flux_c : ∀ u z : FA, (∃ ρ : ℝ, 0 < ρ ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd ρ (xB u z i) (a i)) ∧
      PolyExprS.Valid a Dp ∧ PolyExprS.Valid a nRp ∧ PolyExprS.Valid a nZp ∧
      PolyExprS.Valid a Pap ∧ PolyExprS.Valid a Pbp ∧ PolyExprS.Valid a Pcp) →
    (1 + u) * phiDS (xB u z) Pbp - (1 + u) ^ 3 * pdS (xB u z) 1 Pcp =
      -PolyExprS.eval (xB u z) nRp

namespace FlowFieldS

variable (F : FlowFieldS)

/-- Validity of the six expressions at the bounds `a`. -/
def Valid6 (a : Fin 6 → ℝ) : Prop :=
  PolyExprS.Valid a F.Dp ∧ PolyExprS.Valid a F.nRp ∧ PolyExprS.Valid a F.nZp ∧
    PolyExprS.Valid a F.Pap ∧ PolyExprS.Valid a F.Pbp ∧ PolyExprS.Valid a F.Pcp

/-- **Strip validity at a torus**: a strip `ρ > 0` and bounds `a` on the torus variables at
which the six expressions are valid. -/
def Good (u z : FA) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : Fin 6 → ℝ, (∀ i, Bd ρ (xB u z i) (a i)) ∧ F.Valid6 a

/-- The flow-form residual expression `D w_R − n_R`. -/
def resRp : PolyExprS ℂ (Fin 6) := .sub (.mul F.Dp (.var 4)) F.nRp

/-- The flow-form residual expression `D w_z − n_z`. -/
def resZp : PolyExprS ℂ (Fin 6) := .sub (.mul F.Dp (.var 5)) F.nZp

/-- `D(K)`. -/
def Dof (u z : FA) : FA := PolyExprS.eval (xB u z) F.Dp

/-- The `R`-residual `D 𝓛R − n_R`. -/
def resR (ι : ℝ) (u z : FA) : FA := PolyExprS.eval (xK ι u z) F.resRp

/-- The `z`-residual `D 𝓛z − n_z`. -/
def resZ (ι : ℝ) (u z : FA) : FA := PolyExprS.eval (xK ι u z) F.resZp

/-- The torsion numerator
`P = (n_R D − D ∇n_R·V₀ + n_R ∇D·V₀) z − (n_z D − D ∇n_z·V₀ + n_z ∇D·V₀) u`, by definition. -/
def Pof (u z : FA) : FA :=
  (PolyExprS.eval (xB u z) F.nRp * F.Dof u z -
      F.Dof u z * (pdS (xB u z) 0 F.nRp * u + pdS (xB u z) 1 F.nRp * z) +
      PolyExprS.eval (xB u z) F.nRp * (pdS (xB u z) 0 F.Dp * u + pdS (xB u z) 1 F.Dp * z)) * z -
    (PolyExprS.eval (xB u z) F.nZp * F.Dof u z -
      F.Dof u z * (pdS (xB u z) 0 F.nZp * u + pdS (xB u z) 1 F.nZp * z) +
      PolyExprS.eval (xB u z) F.nZp * (pdS (xB u z) 0 F.Dp * u + pdS (xB u z) 1 F.Dp * z)) * u

/-- `resR = D 𝓛u − n_R`. -/
theorem resR_eq (ι : ℝ) (u z : FA) :
    F.resR ι u z = F.Dof u z * Lt ι u - PolyExprS.eval (xB u z) F.nRp := by
  rw [resR, resRp, Dof]
  simp only [PolyExprS.eval, eval_xK_xB_S ι u z F.noW_Dp, eval_xK_xB_S ι u z F.noW_nRp]
  rfl

/-- `resZ = D 𝓛z − n_z`. -/
theorem resZ_eq (ι : ℝ) (u z : FA) :
    F.resZ ι u z = F.Dof u z * Lt ι z - PolyExprS.eval (xB u z) F.nZp := by
  rw [resZ, resZp, Dof]
  simp only [PolyExprS.eval, eval_xK_xB_S ι u z F.noW_Dp, eval_xK_xB_S ι u z F.noW_nZp]
  rfl

end FlowFieldS

/-! ## Polynomial flow fields are instances -/

namespace FlowField

variable (F : FlowField)

/-- **Every polynomial flow field is a flow field with node** (no node, `P_c = 0`); this keeps
the instance `field14` of `Design/KamNewtonField` available for the new interface. -/
def toS : FlowFieldS where
  Dp := PolyExprS.ofPoly F.Dp
  nRp := PolyExprS.ofPoly F.nRp
  nZp := PolyExprS.ofPoly F.nZp
  Pap := PolyExprS.ofPoly F.Pap
  Pbp := PolyExprS.ofPoly F.Pbp
  Pcp := .const 0
  noW_Dp := noWS_ofPoly _ F.noW_Dp
  noW_nRp := noWS_ofPoly _ F.noW_nRp
  noW_nZp := noWS_ofPoly _ F.noW_nZp
  real_Dp := PolyExprS.realConstsS_ofPoly _ F.real_Dp
  real_nRp := PolyExprS.realConstsS_ofPoly _ F.real_nRp
  real_nZp := PolyExprS.realConstsS_ofPoly _ F.real_nZp
  divFree := fun u z _ => by
    simp only [phiDS_ofPoly, pdS_ofPoly, PolyExprS.eval_ofPoly]; exact F.divFree u z
  flux_a := fun u z _ => by
    simp only [pdS_ofPoly, PolyExprS.eval_ofPoly]; exact F.flux_a u z
  flux_b := fun u z _ => by
    simp only [phiDS_ofPoly, PolyExprS.eval_ofPoly]
    rw [show pdS (xB u z) 0 (.const 0 : PolyExprS ℂ (Fin 6)) = 0 by simp [pdS, PolyExprS.deriv],
      mul_zero, sub_zero]
    exact F.flux_b u z
  flux_c := fun u z _ => by
    simp only [phiDS_ofPoly, PolyExprS.eval_ofPoly]
    rw [show pdS (xB u z) 1 (.const 0 : PolyExprS ℂ (Fin 6)) = 0 by simp [pdS, PolyExprS.deriv],
      mul_zero, sub_zero]
    exact F.flux_c u z

/-- **Sanity**: the embedded field has the same residuals. -/
theorem toS_resR (ι : ℝ) (u z : FA) : F.toS.resR ι u z = F.resR ι u z := by
  rw [FlowFieldS.resR_eq, resR_eq]
  simp [FlowFieldS.Dof, Dof, toS, PolyExprS.eval_ofPoly]

/-- **Sanity**: the embedded field has the same torsion numerator. -/
theorem toS_Pof (u z : FA) : F.toS.Pof u z = F.Pof u z := by
  rw [FlowFieldS.Pof, Pof, F.torsion_poly]
  simp [FlowFieldS.Dof, toS, PolyExprS.eval_ofPoly, pdS_ofPoly]

end FlowField

end PlasmaLean.Design.KamNewton
