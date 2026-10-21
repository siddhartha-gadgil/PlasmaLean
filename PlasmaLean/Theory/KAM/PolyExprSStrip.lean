/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.PolyExprS
public import PlasmaLean.Theory.KAM.StripEval

/-!
# Expressions with an inverse-square-root node in the strip algebra

The KAM step for a field with one algebraic variable `w = |B|⁻¹` (the guiding-centre field
`B̃ = B + ρ_s ∇×b`, `notes/theory/after-kam.md` §1.4) evaluates expressions `PolyExprS`
(`Theory/KAM/PolyExprS`) at tori in the strip algebra `𝔸 = FA`. Polynomial expressions
(`PolyExpr`) can be evaluated anywhere; the node `isqrt c d = (c + d)^{−1/2}` only makes sense
where the deviation `d` is smaller than `c`. This file supplies the strip-algebra facts that the
KAM step needs, all under the **strip validity** hypothesis `SValid x e`: there are a strip
`ρ > 0` and bounds `‖x i‖_ρ ≤ a i` with `Valid a e`.

* `SValid.ana`, `SValid.ana_deriv`: values and directional derivatives are analytic.
* `dS_evalS`: the **chain rule** `dS (P(x)) = DP(x)·(dS x)` for every Fourier multiplier
  `dS α β` of order one (`∂_θ`, `∂_φ`, `𝓛`). For the node this is the identity
  `dS (c + d)^{−1/2} = −½ ((c + d)^{−1/2})³ dS d`, derived from `w² (c + d) = 1`
  (`eval_isqrt_sq`) by the Leibniz rule.
* `IsReal.evalS`, `IsReal.derivS`: expressions with real constants (`RealConstsS`) map real
  elements to real elements; for the node the value at every point is the positive real number
  `1/√(c + r)`.
* `deriv_eq_sumS`: the directional derivative is the sum of the partial derivatives.

**Sanity.** `realConstsS_ofPoly` (polynomial expressions keep their reality condition) and
`sValid_ofPoly` (polynomial expressions are valid at every analytic point).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

open Complex WEll1Z2

namespace PolyExprS

variable {σ : Type*}

/-! ## Strip validity -/

/-- **Strip validity** of `e` at `x`: some strip `ρ > 0` and bounds `‖x i‖_ρ ≤ a i` with
`Valid a e` (every node `isqrt c d` has `maj a d < c`). -/
def SValid (x : σ → FA) (e : PolyExprS ℂ σ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : σ → ℝ, (∀ i, Bd ρ (x i) (a i)) ∧ Valid a e

/-- Validity of a polynomial expression at analytic points. -/
theorem sValid_ofPoly [Finite σ] {x : σ → FA} (hx : ∀ i, Ana (x i)) (e : PolyExpr ℂ σ) :
    SValid x (ofPoly e) := by
  classical
  have := Fintype.ofFinite σ
  choose ρf Bf hρf hBf using hx
  let S : Finset ℝ := insert 1 (Finset.univ.image ρf)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, Bf, fun i => (hBf i).strip ?_, valid_ofPoly _ e⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h; exact hρf i
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))

/-- The FA-norm is bounded by every strip norm. -/
theorem norm_le_of_Bd {ρ B : ℝ} (hρ : 0 ≤ ρ) {x : FA} (h : Bd ρ x B) : ‖x‖ ≤ B := by
  rw [norm_eq_wnorm]
  exact (h.mono hρ le_rfl).2

/-- **The defining identity of the node in `𝔸`**: `w² (c + d) = 1` for `w = (c + d)^{−1/2}`,
on a valid node. -/
theorem eval_isqrt_sq {ρ : ℝ} (hρ : 0 ≤ ρ) {x : σ → FA} {a : σ → ℝ}
    (hx : ∀ i, Bd ρ (x i) (a i)) {c : ℝ} {d : PolyExprS ℂ σ} (hv : Valid a (isqrt c d)) :
    eval x (isqrt c d) ^ 2 * (algebraMap ℂ FA (c : ℂ) + eval x d) = 1 := by
  have hb := Bd.evalS hρ hx hv.1
  have hn : ‖algebraMap ℂ FA (c : ℂ) + eval x d - algebraMap ℂ FA (c : ℂ)‖ < c := by
    rw [add_sub_cancel_left]; exact (norm_le_of_Bd hρ hb).trans_lt hv.2
  exact invSqrt_sq_mul hn

/-- Validity of the parts of a sum. -/
theorem SValid.add {x : σ → FA} {p q : PolyExprS ℂ σ} (h : SValid x (add p q)) :
    SValid x p ∧ SValid x q := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := h
  exact ⟨⟨ρ, hρ, a, hx, hv.1⟩, ⟨ρ, hρ, a, hx, hv.2⟩⟩

/-- **Analyticity of values**. -/
theorem SValid.ana {x : σ → FA} {e : PolyExprS ℂ σ} (h : SValid x e) : Ana (eval x e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := h
  exact ⟨ρ, _, hρ, Bd.evalS hρ.le hx hv⟩

/-- A finite family of analytic elements has a common strip. -/
theorem exists_common_strip [Finite σ] {h : σ → FA} (hh : ∀ i, Ana (h i)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ b : σ → ℝ, ∀ i, Bd ρ (h i) (b i) := by
  classical
  have := Fintype.ofFinite σ
  choose ρf Bf hρf hBf using hh
  let S : Finset ℝ := insert 1 (Finset.univ.image ρf)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, Bf, fun i => (hBf i).strip ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; exact one_pos
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h; exact hρf i
  · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))

/-- **Analyticity of directional derivatives** in analytic directions. -/
theorem SValid.ana_deriv [Finite σ] {x h : σ → FA} {e : PolyExprS ℂ σ} (hs : SValid x e)
    (hh : ∀ i, Ana (h i)) : Ana (deriv x h e) := by
  obtain ⟨ρ, hρ, a, hx, hv⟩ := hs
  obtain ⟨ρ', hρ', b, hb⟩ := exists_common_strip hh
  refine ⟨min ρ ρ', _, lt_min hρ hρ', Bd.derivS (lt_min hρ hρ').le
    (fun i => (hx i).strip (min_le_left _ _)) (fun i => (hb i).strip (min_le_right _ _)) hv⟩

/-! ## The chain rule -/

/-- **Chain rule** for expressions with the node: `dS (P(x)) = DP(x)·(dS x)` on a valid strip. -/
theorem dS_evalS (α β : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {x : σ → FA} {a : σ → ℝ}
    (hx : ∀ i, Bd ρ (x i) (a i)) {e : PolyExprS ℂ σ} (hv : Valid a e) :
    dS α β (eval x e) = deriv x (fun i => dS α β (x i)) e := by
  have ana : ∀ {e' : PolyExprS ℂ σ}, Valid a e' → Ana (eval x e') :=
    fun hv' => ⟨ρ, _, hρ, Bd.evalS hρ.le hx hv'⟩
  induction e with
  | const c => simp [eval, deriv, dS_algebraMap]
  | var i => rfl
  | add p q hp hq =>
    simp only [eval, deriv]
    rw [dS_add α β (ana hv.1) (ana hv.2), hp hv.1, hq hv.2]
  | sub p q hp hq =>
    simp only [eval, deriv]
    rw [dS_sub α β (ana hv.1) (ana hv.2), hp hv.1, hq hv.2]
  | mul p q hp hq =>
    simp only [eval, deriv]
    rw [dS_mul α β (ana hv.1) (ana hv.2), hp hv.1, hq hv.2]
  | isqrt c d hd =>
    have hw : Ana (eval x (isqrt c d)) := ana hv
    have hy : Ana (algebraMap ℂ FA (c : ℂ) + eval x d) := (Ana.algebraMap _).add (ana hv.1)
    have hsq := eval_isqrt_sq hρ.le hx hv
    set w := eval x (isqrt c d) with hw_def
    set y := algebraMap ℂ FA (c : ℂ) + eval x d
    have h0 : dS α β (w ^ 2 * y) = 0 := by rw [hsq, dS_one]
    rw [dS_mul α β (hw.pow 2) hy, dS_pow α β hw 1] at h0
    have hdy : dS α β y = deriv x (fun i => dS α β (x i)) d := by
      simp only [y]
      rw [dS_add α β (Ana.algebraMap _) (ana hv.1), dS_algebraMap, zero_add, hd hv.1]
    rw [hdy] at h0
    simp only [deriv]
    rw [← hw_def]
    push_cast at h0
    have key : (2 : FA) * dS α β w + w ^ 3 * deriv x (fun i => dS α β (x i)) d = 0 := by
      linear_combination w * h0 - 2 * dS α β w * hsq
    have h2 : algebraMap ℂ FA (-(1 / 2)) * 2 + 1 = 0 := by
      rw [← map_ofNat (algebraMap ℂ FA) 2, ← map_mul, ← map_one (algebraMap ℂ FA), ← map_add]
      norm_num
    rw [Algebra.smul_def]
    linear_combination (-algebraMap ℂ FA (-(1 / 2))) * key + dS α β w * h2

/-! ## Reality -/

/-- Expressions with real constants (the node's centre is real by construction). -/
def RealConstsS : PolyExprS ℂ σ → Prop
  | const c => (starRingEnd ℂ) c = c
  | var _ => True
  | add p q => RealConstsS p ∧ RealConstsS q
  | sub p q => RealConstsS p ∧ RealConstsS q
  | mul p q => RealConstsS p ∧ RealConstsS q
  | isqrt _ d => RealConstsS d

/-- Sanity: polynomial expressions keep their reality condition. -/
theorem realConstsS_ofPoly (e : PolyExpr ℂ σ) (h : e.RealConsts) : RealConstsS (ofPoly e) := by
  induction e with
  | const c => exact h
  | var i => trivial
  | add p q hp hq => exact ⟨hp h.1, hq h.2⟩
  | sub p q hp hq => exact ⟨hp h.1, hq h.2⟩
  | mul p q hp hq => exact ⟨hp h.1, hq h.2⟩

/-- Evaluation at a point as an algebra homomorphism `𝔸 → ℂ`. -/
def evalAlg (θ ψ : ℝ) : FA →ₐ[ℂ] ℂ :=
  { evalHom θ ψ with commutes' := fun c => eval_algebraMap c θ ψ }

/-- `evalAlg` is evaluation. -/
@[simp] theorem evalAlg_apply (θ ψ : ℝ) (x : FA) : evalAlg θ ψ x = WEll1Z2.eval x θ ψ := rfl

/-- The node maps real elements to real elements. -/
theorem isReal_invSqrt {c : ℝ} {y : FA} (hy : IsReal y)
    (hn : ‖y - algebraMap ℂ FA (c : ℂ)‖ < c) : IsReal (invSqrt ℂ c y) := by
  refine (isReal_iff_eval _).2 fun θ ψ => ?_
  have hr : evalAlg θ ψ y = (((WEll1Z2.eval y θ ψ).re : ℝ) : ℂ) := by
    rw [evalAlg_apply]
    apply Complex.ext <;> simp [hy.eval_im θ ψ]
  obtain ⟨-, hval⟩ := algHom_invSqrt hn (evalAlg θ ψ) hr
  rw [evalAlg_apply] at hval
  rw [hval]; exact RCLike.conj_ofReal _

/-- **Reality of values**: real constants and real inputs give real values (valid strip). -/
theorem IsReal.evalS {ρ : ℝ} (hρ : 0 ≤ ρ) {x : σ → FA} {a : σ → ℝ}
    (hx : ∀ i, Bd ρ (x i) (a i)) (hr : ∀ i, IsReal (x i)) {e : PolyExprS ℂ σ}
    (hv : Valid a e) (he : RealConstsS e) : IsReal (eval x e) := by
  induction e with
  | const c =>
    have hc : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
      have := congrArg Complex.im he
      simp at this; linarith
    simp only [eval]; rw [hc]; exact IsReal.algebraMap _
  | var i => exact hr i
  | add p q hp hq => exact (hp hv.1 he.1).add (hq hv.2 he.2)
  | sub p q hp hq => exact (hp hv.1 he.1).sub (hq hv.2 he.2)
  | mul p q hp hq => exact (hp hv.1 he.1).mul (hq hv.2 he.2)
  | isqrt c d hd =>
    simp only [eval]
    refine isReal_invSqrt ((IsReal.algebraMap c).add (hd hv.1 he)) ?_
    convert (norm_le_of_Bd hρ (Bd.evalS hρ hx hv.1)).trans_lt hv.2 using 2
    exact add_sub_cancel_left _ _

/-- **Reality of directional derivatives** (real inputs and directions). -/
theorem IsReal.derivS {ρ : ℝ} (hρ : 0 ≤ ρ) {x h : σ → FA} {a : σ → ℝ}
    (hx : ∀ i, Bd ρ (x i) (a i)) (hr : ∀ i, IsReal (x i)) (hh : ∀ i, IsReal (h i))
    {e : PolyExprS ℂ σ} (hv : Valid a e) (he : RealConstsS e) : IsReal (deriv x h e) := by
  induction e with
  | const c => simp only [deriv]; exact map_zero cjHom
  | var i => exact hh i
  | add p q hp hq => exact (hp hv.1 he.1).add (hq hv.2 he.2)
  | sub p q hp hq => exact (hp hv.1 he.1).sub (hq hv.2 he.2)
  | mul p q hp hq =>
    exact ((hp hv.1 he.1).mul (IsReal.evalS hρ hx hr hv.2 he.2)).add
      ((IsReal.evalS hρ hx hr hv.1 he.1).mul (hq hv.2 he.2))
  | isqrt c d hd =>
    simp only [deriv]
    have hw := IsReal.evalS hρ hx hr hv he
    have e2 : ((-(1 / 2) : ℂ) • eval x (isqrt c d) ^ 3) =
        (((-(1 / 2) : ℝ) : ℂ) • eval x (isqrt c d) ^ 3) := by push_cast; rfl
    rw [e2]
    exact ((hw.pow 3).smul _).mul (hd hv.1 he)

/-! ## Partial derivatives -/

section Partials

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- The directional derivative is the sum of the partial derivatives. -/
theorem deriv_eq_sumS [Fintype σ] [DecidableEq σ] (x h : σ → A) (e : PolyExprS ℂ σ) :
    deriv x h e = ∑ i, h i * deriv x (Pi.single i 1) e := by
  induction e with
  | const c => simp [deriv]
  | var j =>
    simp only [deriv]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  | add p q hp hq =>
    simp only [deriv, hp, hq, ← Finset.sum_add_distrib, mul_add]
  | sub p q hp hq =>
    simp only [deriv, hp, hq, ← Finset.sum_sub_distrib, mul_sub]
  | mul p q hp hq =>
    simp only [deriv, hp, hq, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  | isqrt c d hd =>
    simp only [deriv, hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

end Partials

end PolyExprS

end PlasmaLean.Theory.KAM
