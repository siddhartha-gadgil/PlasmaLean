/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.InvSqrt

/-!
# Polynomial expressions with an inverse-square-root node

`PolyExprS 𝕜 σ` extends the polynomial expressions `PolyExpr 𝕜 σ` of `Theory/KAM/Composition`
by one node `isqrt c d`, read as `(c + d)^{−1/2}` for a real `c` and an expression `d` (the
*deviation* from the constant `c`). It evaluates in any complete normed commutative `𝕜`-algebra
(`𝕜 = ℝ` or `ℂ`) through `invSqrt` of `Theory/KAM/InvSqrt`. This is what the guiding-centre
field `B̃ = B + ρ_s ∇ × b` needs: `w = |B|⁻¹` with `w² |B|² = 1`
(`notes/theory/after-kam.md`, §1.4, module 2).

**Majorants.** With `g_c(t) = (c − t)^{−1/2}` (`isqG`):
* `maj a (isqrt c d) = g_c(maj a d)`;
* `majD a b (isqrt c d) = ½ g_c(maj a d)³ · majD a b d` (chain rule, `g' = ½ g³`);
* `majD2 a b (isqrt c d) = ¾ g_c(maj a d)⁵ (majD a b d)² + ½ g_c(maj a d)³ majD2 a b d`
  (`g'' = ¾ g⁵`).
The node is only meaningful when `maj a d < c`; `Valid a e` records this for every node of `e`.
Majorants are monotone on valid expressions (`maj_mono`, `majD_mono`, `majD2_mono`,
`Valid.mono`).

**Estimates** (same form as for `PolyExpr`; `‖x i‖ ≤ a i`, `‖h i‖ ≤ b i`):
* `norm_eval_le` (`Valid a e`): `‖P(x)‖ ≤ P̂(a)`;
* `norm_deriv_le` (`Valid a e`): `‖DP(x)h‖ ≤ P̂'(a)·b`, where the derivative of the node is
  `D(c + d)^{−1/2} h = −½ ((c + d)^{−1/2})³ Dd h`;
* `norm_eval_add_sub_le` (`Valid (a + b) e`): `‖P(x + h) − P(x)‖ ≤ P̂'(a + b)·b`;
* `norm_taylor_le` (`Valid (a + b) e`): `‖P(x + h) − P(x) − DP(x)h‖ ≤ ½ P̂''(a + b)[b, b]`.

**Strip algebra.** `eval_algHom`/`deriv_algHom` (continuous algebra homomorphisms commute with
evaluation on valid inputs) give the strip versions `Bd.evalS`, `Bd.derivS`, `Bd.eval_add_subS`,
`Bd.taylorS` in `𝔸 = FA`, the algebra used by the KAM step.

**Compatibility and sanity.** `ofPoly` embeds `PolyExpr` with the same evaluation, derivative and
majorants (`eval_ofPoly`, `maj_ofPoly`, …). `eval_isqrt_point`: at a real point (an algebra
homomorphism `φ : A → 𝕜`), the node evaluates to `1/√(c + φ(d))`. The fixture `isqrt_quarter`
evaluates `(1 + (−3/4))^{−1/2} = 2`, and `not_valid_isqrt` shows that the node is rejected when
the deviation majorant reaches `c`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

/-- Polynomial expressions with an inverse-square-root node `isqrt c d = (c + d)^{−1/2}`. -/
inductive PolyExprS (𝕜 : Type*) (σ : Type*) where
  /-- A constant. -/
  | const (c : 𝕜)
  /-- A variable. -/
  | var (i : σ)
  /-- Sum. -/
  | add (p q : PolyExprS 𝕜 σ)
  /-- Difference. -/
  | sub (p q : PolyExprS 𝕜 σ)
  /-- Product. -/
  | mul (p q : PolyExprS 𝕜 σ)
  /-- Inverse square root `(c + d)^{−1/2}` of a real constant `c` plus a deviation `d`. -/
  | isqrt (c : ℝ) (d : PolyExprS 𝕜 σ)

namespace PolyExprS

variable {𝕜 : Type*} [RCLike 𝕜] {σ : Type*}

/-- The embedding of polynomial expressions. -/
def ofPoly : PolyExpr 𝕜 σ → PolyExprS 𝕜 σ
  | .const c => const c
  | .var i => var i
  | .add p q => add (ofPoly p) (ofPoly q)
  | .sub p q => sub (ofPoly p) (ofPoly q)
  | .mul p q => mul (ofPoly p) (ofPoly q)

section Majorants

/-- The majorant `P̂(a)`; the node `isqrt c d` gives `(c − maj a d)^{−1/2}`. -/
def maj (a : σ → ℝ) : PolyExprS 𝕜 σ → ℝ
  | const c => ‖c‖
  | var i => a i
  | add p q => maj a p + maj a q
  | sub p q => maj a p + maj a q
  | mul p q => maj a p * maj a q
  | isqrt c d => isqG c (maj a d)

/-- The first-derivative majorant `P̂'(a)·b` (product and chain rules). -/
def majD (a b : σ → ℝ) : PolyExprS 𝕜 σ → ℝ
  | const _ => 0
  | var i => b i
  | add p q => majD a b p + majD a b q
  | sub p q => majD a b p + majD a b q
  | mul p q => majD a b p * maj a q + maj a p * majD a b q
  | isqrt c d => isqG c (maj a d) ^ 3 / 2 * majD a b d

/-- The second-derivative majorant `P̂''(a)[b, b]`. -/
def majD2 (a b : σ → ℝ) : PolyExprS 𝕜 σ → ℝ
  | const _ => 0
  | var _ => 0
  | add p q => majD2 a b p + majD2 a b q
  | sub p q => majD2 a b p + majD2 a b q
  | mul p q => majD2 a b p * maj a q + 2 * (majD a b p * majD a b q) + maj a p * majD2 a b q
  | isqrt c d => 3 * isqG c (maj a d) ^ 5 / 4 * majD a b d ^ 2 +
      isqG c (maj a d) ^ 3 / 2 * majD2 a b d

/-- Validity at `a`: every node `isqrt c d` has `maj a d < c`. -/
def Valid (a : σ → ℝ) : PolyExprS 𝕜 σ → Prop
  | const _ => True
  | var _ => True
  | add p q => Valid a p ∧ Valid a q
  | sub p q => Valid a p ∧ Valid a q
  | mul p q => Valid a p ∧ Valid a q
  | isqrt c d => Valid a d ∧ maj a d < c

variable {a a' b b' : σ → ℝ}

omit [RCLike 𝕜] in
/-- `g_c(t)^k / n ≥ 0`. -/
theorem isqG_pow_div_nonneg (c t : ℝ) (k n : ℕ) : 0 ≤ isqG c t ^ k / n :=
  div_nonneg (pow_nonneg (isqG_nonneg c t) k) (Nat.cast_nonneg n)

omit [RCLike 𝕜] in
/-- `3 g_c(t)⁵ / 4 ≥ 0`. -/
theorem isqG_three_pow_div_nonneg (c t : ℝ) : 0 ≤ 3 * isqG c t ^ 5 / 4 :=
  div_nonneg (mul_nonneg zero_le_three (pow_nonneg (isqG_nonneg c t) 5)) zero_le_four

/-- `P̂(a) ≥ 0` for `a ≥ 0`. -/
theorem maj_nonneg (ha : ∀ i, 0 ≤ a i) (e : PolyExprS 𝕜 σ) : 0 ≤ maj a e := by
  induction e with
  | const c => exact norm_nonneg c
  | var i => exact ha i
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq
  | isqrt c d _ => exact isqG_nonneg _ _

/-- `P̂'(a)·b ≥ 0` for `a, b ≥ 0`. -/
theorem majD_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (e : PolyExprS 𝕜 σ) :
    0 ≤ majD a b e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact hb i
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    exact add_nonneg (mul_nonneg hp (maj_nonneg ha q)) (mul_nonneg (maj_nonneg ha p) hq)
  | isqrt c d hd => exact mul_nonneg (isqG_pow_div_nonneg c _ 3 2) hd

/-- `P̂''(a)[b, b] ≥ 0` for `a, b ≥ 0`. -/
theorem majD2_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (e : PolyExprS 𝕜 σ) :
    0 ≤ majD2 a b e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact le_rfl
  | add p q hp hq => exact add_nonneg hp hq
  | sub p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    have := majD_nonneg ha hb p
    have := majD_nonneg ha hb q
    have := maj_nonneg ha p
    have := maj_nonneg ha q
    exact add_nonneg (add_nonneg (mul_nonneg hp (maj_nonneg ha q)) (by positivity))
      (mul_nonneg (maj_nonneg ha p) hq)
  | isqrt c d hd =>
    exact add_nonneg (mul_nonneg (isqG_three_pow_div_nonneg c _) (sq_nonneg _))
      (mul_nonneg (isqG_pow_div_nonneg c _ 3 2) hd)

/-- The majorant is monotone on valid expressions. -/
theorem maj_mono (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ a' i) {e : PolyExprS 𝕜 σ}
    (hv : Valid a' e) : maj a e ≤ maj a' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact haa i
  | add p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | sub p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | mul p q hp hq =>
    exact mul_le_mul (hp hv.1) (hq hv.2) (maj_nonneg ha q) ((maj_nonneg ha p).trans (hp hv.1))
  | isqrt c d hd => exact isqG_mono (hd hv.1) hv.2

/-- Validity is inherited by smaller arguments. -/
theorem Valid.mono (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ a' i) {e : PolyExprS 𝕜 σ}
    (hv : Valid a' e) : Valid a e := by
  induction e with
  | const c => trivial
  | var i => trivial
  | add p q hp hq => exact ⟨hp hv.1, hq hv.2⟩
  | sub p q hp hq => exact ⟨hp hv.1, hq hv.2⟩
  | mul p q hp hq => exact ⟨hp hv.1, hq hv.2⟩
  | isqrt c d hd => exact ⟨hd hv.1, (maj_mono ha haa hv.1).trans_lt hv.2⟩

/-- `P̂'` is monotone in both arguments on valid expressions. -/
theorem majD_mono (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (haa : ∀ i, a i ≤ a' i)
    (hbb : ∀ i, b i ≤ b' i) {e : PolyExprS 𝕜 σ} (hv : Valid a' e) :
    majD a b e ≤ majD a' b' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact hbb i
  | add p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | sub p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | mul p q hp hq =>
    exact add_le_add
      (mul_le_mul (hp hv.1) (maj_mono ha haa hv.2) (maj_nonneg ha q)
        ((majD_nonneg ha hb p).trans (hp hv.1)))
      (mul_le_mul (maj_mono ha haa hv.1) (hq hv.2) (majD_nonneg ha hb q)
        ((maj_nonneg ha p).trans (maj_mono ha haa hv.1)))
  | isqrt c d hd =>
    have hg := isqG_mono (maj_mono ha haa hv.1) hv.2
    have hg0 := isqG_nonneg c (maj a d)
    have h3 : isqG c (maj a d) ^ 3 / 2 ≤ isqG c (maj a' d) ^ 3 / 2 := by gcongr
    exact mul_le_mul h3 (hd hv.1) (majD_nonneg ha hb d) (isqG_pow_div_nonneg c _ 3 2)

/-- `P̂''` is monotone in both arguments on valid expressions. -/
theorem majD2_mono (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (haa : ∀ i, a i ≤ a' i)
    (hbb : ∀ i, b i ≤ b' i) {e : PolyExprS 𝕜 σ} (hv : Valid a' e) :
    majD2 a b e ≤ majD2 a' b' e := by
  induction e with
  | const c => exact le_rfl
  | var i => exact le_rfl
  | add p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | sub p q hp hq => exact add_le_add (hp hv.1) (hq hv.2)
  | mul p q hp hq =>
    have m1 := maj_mono ha haa hv.1
    have m2 := maj_mono ha haa hv.2
    have d1 := majD_mono ha hb haa hbb hv.1
    have d2 := majD_mono ha hb haa hbb hv.2
    have n1 := maj_nonneg ha p
    have n2 := maj_nonneg ha q
    have e1 := majD_nonneg ha hb p
    have e2 := majD_nonneg ha hb q
    have f1 := majD2_nonneg ha hb p
    have f2 := majD2_nonneg ha hb q
    simp only [majD2]
    have k1 := mul_le_mul (hp hv.1) m2 n2 (f1.trans (hp hv.1))
    have k2 := mul_le_mul d1 d2 e2 (e1.trans d1)
    have k3 := mul_le_mul m1 (hq hv.2) f2 (n1.trans m1)
    linarith
  | isqrt c d hd =>
    have hg := isqG_mono (maj_mono ha haa hv.1) hv.2
    have hg0 := isqG_nonneg c (maj a d)
    have d1 := majD_mono ha hb haa hbb hv.1
    have e1 := majD_nonneg ha hb d
    have f1 := majD2_nonneg ha hb d
    have f2 := hd hv.1
    simp only [majD2]
    have h5 : 3 * isqG c (maj a d) ^ 5 / 4 ≤ 3 * isqG c (maj a' d) ^ 5 / 4 := by gcongr
    have h3 : isqG c (maj a d) ^ 3 / 2 ≤ isqG c (maj a' d) ^ 3 / 2 := by gcongr
    have hD : majD a b d ^ 2 ≤ majD a' b' d ^ 2 := by gcongr
    have k1 := mul_le_mul h5 hD (sq_nonneg _) (isqG_three_pow_div_nonneg c _)
    have k2 := mul_le_mul h3 f2 f1 (isqG_pow_div_nonneg c _ 3 2)
    linarith

end Majorants

section Eval

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

/-- Evaluation; the node is `invSqrt` centred at `c`: `(c + d)^{−1/2}`. -/
def eval (x : σ → A) : PolyExprS 𝕜 σ → A
  | const c => algebraMap 𝕜 A c
  | var i => x i
  | add p q => eval x p + eval x q
  | sub p q => eval x p - eval x q
  | mul p q => eval x p * eval x q
  | isqrt c d => invSqrt 𝕜 c (algebraMap 𝕜 A (c : 𝕜) + eval x d)

/-- The directional derivative `DP(x)h`; for the node, `−½ ((c + d)^{−1/2})³ Dd h`. -/
def deriv (x h : σ → A) : PolyExprS 𝕜 σ → A
  | const _ => 0
  | var i => h i
  | add p q => deriv x h p + deriv x h q
  | sub p q => deriv x h p - deriv x h q
  | mul p q => deriv x h p * eval x q + eval x p * deriv x h q
  | isqrt c d => (-(1 / 2) : 𝕜) • eval x (isqrt c d) ^ 3 * deriv x h d

/-- `DP(x)` is additive in the direction. -/
theorem deriv_add (x h h' : σ → A) (e : PolyExprS 𝕜 σ) :
    deriv x (h + h') e = deriv x h e + deriv x h' e := by
  induction e with
  | const c => simp [deriv]
  | var i => simp [deriv]
  | add p q hp hq => simp only [deriv, hp, hq]; abel
  | sub p q hp hq => simp only [deriv, hp, hq]; abel
  | mul p q hp hq => simp only [deriv, hp, hq]; ring
  | isqrt c d hd => simp only [deriv, hd]; ring

/-- The embedding `ofPoly` preserves evaluation. -/
theorem eval_ofPoly (x : σ → A) (e : PolyExpr 𝕜 σ) : eval x (ofPoly e) = PolyExpr.eval x e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [ofPoly, eval, PolyExpr.eval, hp, hq]
  | sub p q hp hq => simp only [ofPoly, eval, PolyExpr.eval, hp, hq]
  | mul p q hp hq => simp only [ofPoly, eval, PolyExpr.eval, hp, hq]

/-- The embedding `ofPoly` preserves derivatives. -/
theorem deriv_ofPoly (x h : σ → A) (e : PolyExpr 𝕜 σ) :
    deriv x h (ofPoly e) = PolyExpr.deriv x h e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [ofPoly, deriv, PolyExpr.deriv, hp, hq]
  | sub p q hp hq => simp only [ofPoly, deriv, PolyExpr.deriv, hp, hq]
  | mul p q hp hq => simp only [ofPoly, deriv, PolyExpr.deriv, hp, hq, eval_ofPoly]

/-- The embedding `ofPoly` preserves the majorant. -/
theorem maj_ofPoly (a : σ → ℝ) (e : PolyExpr 𝕜 σ) : maj a (ofPoly e) = PolyExpr.maj a e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [ofPoly, maj, PolyExpr.maj, hp, hq]
  | sub p q hp hq => simp only [ofPoly, maj, PolyExpr.maj, hp, hq]
  | mul p q hp hq => simp only [ofPoly, maj, PolyExpr.maj, hp, hq]

/-- The embedding `ofPoly` preserves the first-derivative majorant. -/
theorem majD_ofPoly (a b : σ → ℝ) (e : PolyExpr 𝕜 σ) :
    majD a b (ofPoly e) = PolyExpr.majD a b e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [ofPoly, majD, PolyExpr.majD, hp, hq]
  | sub p q hp hq => simp only [ofPoly, majD, PolyExpr.majD, hp, hq]
  | mul p q hp hq => simp only [ofPoly, majD, PolyExpr.majD, hp, hq, maj_ofPoly]

/-- The embedding `ofPoly` preserves the second-derivative majorant. -/
theorem majD2_ofPoly (a b : σ → ℝ) (e : PolyExpr 𝕜 σ) :
    majD2 a b (ofPoly e) = PolyExpr.majD2 a b e := by
  induction e with
  | const c => rfl
  | var i => rfl
  | add p q hp hq => simp only [ofPoly, majD2, PolyExpr.majD2, hp, hq]
  | sub p q hp hq => simp only [ofPoly, majD2, PolyExpr.majD2, hp, hq]
  | mul p q hp hq =>
    simp only [ofPoly, majD2, PolyExpr.majD2, hp, hq, maj_ofPoly, majD_ofPoly]

/-- Polynomial expressions are always valid. -/
theorem valid_ofPoly (a : σ → ℝ) (e : PolyExpr 𝕜 σ) : Valid a (ofPoly e) := by
  induction e with
  | const c => trivial
  | var i => trivial
  | add p q hp hq => exact ⟨hp, hq⟩
  | sub p q hp hq => exact ⟨hp, hq⟩
  | mul p q hp hq => exact ⟨hp, hq⟩

/-! ### Norm estimates -/

variable [NormOneClass A] [CompleteSpace A] {a b : σ → ℝ} {x h : σ → A}

omit [NormOneClass A] [CompleteSpace A] in
/-- The node's argument minus the centre is the deviation. -/
theorem isqrt_arg_sub (c : ℝ) (y : A) :
    algebraMap 𝕜 A (c : 𝕜) + y - algebraMap 𝕜 A (c : 𝕜) = y := add_sub_cancel_left _ _

omit [CompleteSpace A] in
/-- **Majorant bound** `‖P(x)‖ ≤ P̂(a)` on valid expressions. -/
theorem norm_eval_le (hx : ∀ i, ‖x i‖ ≤ a i) {e : PolyExprS 𝕜 σ} (hv : Valid a e) :
    ‖eval x e‖ ≤ maj a e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  induction e with
  | const c => simp [eval, maj, norm_algebraMap']
  | var i => exact hx i
  | add p q hp hq => exact (norm_add_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | sub p q hp hq => exact (norm_sub_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | mul p q hp hq =>
    exact (norm_mul_le _ _).trans
      (mul_le_mul (hp hv.1) (hq hv.2) (norm_nonneg _) (maj_nonneg ha p))
  | isqrt c d hd =>
    simp only [eval, maj]
    exact norm_invSqrt_le (by rw [isqrt_arg_sub]; exact hd hv.1) hv.2

omit [CompleteSpace A] in
/-- **Derivative bound** `‖DP(x)h‖ ≤ P̂'(a)·b` on valid expressions. -/
theorem norm_deriv_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) {e : PolyExprS 𝕜 σ}
    (hv : Valid a e) : ‖deriv x h e‖ ≤ majD a b e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  induction e with
  | const c => simp [deriv, majD]
  | var i => exact hh i
  | add p q hp hq => exact (norm_add_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | sub p q hp hq => exact (norm_sub_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | mul p q hp hq =>
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul (hp hv.1) (norm_eval_le hx hv.2) (norm_nonneg _) (majD_nonneg ha hb p))
    · exact (norm_mul_le _ _).trans
        (mul_le_mul (norm_eval_le hx hv.1) (hq hv.2) (norm_nonneg _) (maj_nonneg ha p))
  | isqrt c d hd =>
    simp only [deriv, majD, eval]
    have h1 := norm_invSqrt_deriv_le (𝕜 := 𝕜) (A := A)
      (by rw [isqrt_arg_sub]; exact norm_eval_le hx hv.1) hv.2
    exact (norm_mul_le _ _).trans (mul_le_mul h1 (hd hv.1) (norm_nonneg _)
      (isqG_pow_div_nonneg c _ 3 2))

omit [NormOneClass A] [CompleteSpace A] in
/-- Bound on the perturbed point: `‖x i + h i‖ ≤ a i + b i`. -/
theorem norm_add_le_add (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) :
    ∀ i, ‖(x + h) i‖ ≤ (a + b) i := fun i =>
  (norm_add_le _ _).trans (add_le_add (hx i) (hh i))

/-- **Lipschitz bound** `‖P(x + h) − P(x)‖ ≤ P̂'(a + b)·b` on expressions valid at `a + b`. -/
theorem norm_eval_add_sub_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i)
    {e : PolyExprS 𝕜 σ} (hv : Valid (a + b) e) :
    ‖eval (x + h) e - eval x e‖ ≤ majD (a + b) b e := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  have hle : ∀ i, a i ≤ (a + b) i := fun i => le_add_of_nonneg_right (hb i)
  have hxh := norm_add_le_add hx hh
  induction e with
  | const c => simp [eval, majD]
  | var i => simpa [eval, majD] using hh i
  | add p q hp hq =>
    simp only [eval, majD]
    rw [add_sub_add_comm]; exact (norm_add_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | sub p q hp hq =>
    simp only [eval, majD]
    rw [sub_sub_sub_comm]; exact (norm_sub_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | mul p q hp hq =>
    simp only [eval, majD]
    have hid : eval (x + h) p * eval (x + h) q - eval x p * eval x q =
        (eval (x + h) p - eval x p) * eval (x + h) q +
          eval x p * (eval (x + h) q - eval x q) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans
        (mul_le_mul (hp hv.1) (norm_eval_le hxh hv.2) (norm_nonneg _) (majD_nonneg hab hb p))
    · exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_eval_le hx (hv.1.mono ha hle)).trans (maj_mono ha hle hv.1))
        (hq hv.2) (norm_nonneg _) (maj_nonneg hab p))
  | isqrt c d hd =>
    simp only [eval, majD]
    have h1 : ‖algebraMap 𝕜 A (c : 𝕜) + eval (x + h) d - algebraMap 𝕜 A (c : 𝕜)‖ ≤
        maj (a + b) d := by rw [isqrt_arg_sub]; exact norm_eval_le hxh hv.1
    have h0 : ‖algebraMap 𝕜 A (c : 𝕜) + eval x d - algebraMap 𝕜 A (c : 𝕜)‖ ≤
        maj (a + b) d := by
      rw [isqrt_arg_sub]
      exact (norm_eval_le hx (hv.1.mono ha hle)).trans (maj_mono ha hle hv.1)
    refine (norm_invSqrt_sub_le h1 h0 hv.2).trans ?_
    rw [add_sub_add_left_eq_sub]
    exact mul_le_mul_of_nonneg_left (hd hv.1) (isqG_pow_div_nonneg c _ 3 2)

/-- **Taylor bound** `‖P(x + h) − P(x) − DP(x)h‖ ≤ ½ P̂''(a + b)[b, b]` on expressions valid at
`a + b`. -/
theorem norm_taylor_le (hx : ∀ i, ‖x i‖ ≤ a i) (hh : ∀ i, ‖h i‖ ≤ b i) {e : PolyExprS 𝕜 σ}
    (hv : Valid (a + b) e) :
    ‖eval (x + h) e - eval x e - deriv x h e‖ ≤ majD2 (a + b) b e / 2 := by
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hx i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hh i)
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  have hle : ∀ i, a i ≤ (a + b) i := fun i => le_add_of_nonneg_right (hb i)
  have hxh := norm_add_le_add hx hh
  induction e with
  | const c => simp [eval, deriv, majD2]
  | var i => simp [eval, deriv, majD2]
  | add p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p + eval (x + h) q - (eval x p + eval x q) -
        (deriv x h p + deriv x h q) = (eval (x + h) p - eval x p - deriv x h p) +
          (eval (x + h) q - eval x q - deriv x h q) := by abel
    rw [hid, add_div]; exact (norm_add_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | sub p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p - eval (x + h) q - (eval x p - eval x q) -
        (deriv x h p - deriv x h q) = (eval (x + h) p - eval x p - deriv x h p) -
          (eval (x + h) q - eval x q - deriv x h q) := by abel
    rw [hid, add_div]; exact (norm_sub_le _ _).trans (add_le_add (hp hv.1) (hq hv.2))
  | mul p q hp hq =>
    simp only [eval, deriv, majD2]
    have hid : eval (x + h) p * eval (x + h) q - eval x p * eval x q -
        (deriv x h p * eval x q + eval x p * deriv x h q) =
        deriv x h p * (eval (x + h) q - eval x q) +
          (eval (x + h) p - eval x p - deriv x h p) * eval (x + h) q +
          eval x p * (eval (x + h) q - eval x q - deriv x h q) := by ring
    rw [hid]
    have t1 : ‖deriv x h p * (eval (x + h) q - eval x q)‖ ≤
        majD (a + b) b p * majD (a + b) b q :=
      (norm_mul_le _ _).trans (mul_le_mul
        ((norm_deriv_le hx hh (hv.1.mono ha hle)).trans
          (majD_mono ha hb hle (fun i => le_rfl) hv.1))
        (norm_eval_add_sub_le hx hh hv.2) (norm_nonneg _) (majD_nonneg hab hb p))
    have t2 : ‖(eval (x + h) p - eval x p - deriv x h p) * eval (x + h) q‖ ≤
        majD2 (a + b) b p / 2 * maj (a + b) q :=
      (norm_mul_le _ _).trans (mul_le_mul (hp hv.1) (norm_eval_le hxh hv.2) (norm_nonneg _)
        (div_nonneg (majD2_nonneg hab hb p) zero_le_two))
    have t3 : ‖eval x p * (eval (x + h) q - eval x q - deriv x h q)‖ ≤
        maj (a + b) p * (majD2 (a + b) b q / 2) :=
      (norm_mul_le _ _).trans (mul_le_mul
        ((norm_eval_le hx (hv.1.mono ha hle)).trans (maj_mono ha hle hv.1)) (hq hv.2)
        (norm_nonneg _) (maj_nonneg hab p))
    calc _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ majD (a + b) b p * majD (a + b) b q + majD2 (a + b) b p / 2 * maj (a + b) q +
          maj (a + b) p * (majD2 (a + b) b q / 2) := add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring
  | isqrt c d hd =>
    simp only [eval, deriv, majD2]
    set M := maj (a + b) d
    set cA := algebraMap 𝕜 A (c : 𝕜)
    set y0 := invSqrt 𝕜 c (cA + eval x d)
    set y1 := invSqrt 𝕜 c (cA + eval (x + h) d)
    have h1 : ‖cA + eval (x + h) d - cA‖ ≤ M := by
      rw [isqrt_arg_sub]; exact norm_eval_le hxh hv.1
    have h0 : ‖cA + eval x d - cA‖ ≤ M := by
      rw [isqrt_arg_sub]
      exact (norm_eval_le hx (hv.1.mono ha hle)).trans (maj_mono ha hle hv.1)
    have hk : ‖eval (x + h) d - eval x d‖ ≤ majD (a + b) b d := norm_eval_add_sub_le hx hh hv.1
    have hg := isqG_nonneg c M
    have T1 := norm_invSqrt_taylor_le h0 h1 hv.2
    rw [add_sub_add_left_eq_sub] at T1
    have T2 := norm_invSqrt_deriv_le (𝕜 := 𝕜) h0 hv.2
    have hid : y1 - y0 - (-(1 / 2) : 𝕜) • y0 ^ 3 * deriv x h d =
        (y1 - y0 - (-(1 / 2) : 𝕜) • y0 ^ 3 * (eval (x + h) d - eval x d)) +
          (-(1 / 2) : 𝕜) • y0 ^ 3 * (eval (x + h) d - eval x d - deriv x h d) := by ring
    rw [hid]
    have t1 : ‖y1 - y0 - (-(1 / 2) : 𝕜) • y0 ^ 3 * (eval (x + h) d - eval x d)‖ ≤
        3 * isqG c M ^ 5 / 4 * majD (a + b) b d ^ 2 / 2 := by
      refine T1.trans ?_
      have := norm_nonneg (eval (x + h) d - eval x d)
      gcongr
    have t2 : ‖(-(1 / 2) : 𝕜) • y0 ^ 3 * (eval (x + h) d - eval x d - deriv x h d)‖ ≤
        isqG c M ^ 3 / 2 * (majD2 (a + b) b d / 2) :=
      (norm_mul_le _ _).trans (mul_le_mul T2 (hd hv.1) (norm_nonneg _)
        (isqG_pow_div_nonneg c _ 3 2))
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 3 * isqG c M ^ 5 / 4 * majD (a + b) b d ^ 2 / 2 +
          isqG c M ^ 3 / 2 * (majD2 (a + b) b d / 2) := add_le_add t1 t2
      _ = _ := by ring

end Eval

/-! ## Algebra homomorphisms, points, and the strip algebra -/

section Hom

variable {A B : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A] [NormOneClass A] [CompleteSpace A]
  [NormedCommRing B] [NormedAlgebra 𝕜 B] {a : σ → ℝ} {x h : σ → A}

/-- Continuous algebra homomorphisms commute with evaluation on valid inputs. -/
theorem eval_algHom (f : A →ₐ[𝕜] B) (hf : Continuous f) (hx : ∀ i, ‖x i‖ ≤ a i)
    {e : PolyExprS 𝕜 σ} (hv : Valid a e) : f (eval x e) = eval (fun i => f (x i)) e := by
  induction e with
  | const c => simp [eval]
  | var i => rfl
  | add p q hp hq => simp [eval, hp hv.1, hq hv.2]
  | sub p q hp hq => simp [eval, hp hv.1, hq hv.2]
  | mul p q hp hq => simp [eval, hp hv.1, hq hv.2]
  | isqrt c d hd =>
    simp only [eval]
    rw [map_invSqrt f hf (by rw [isqrt_arg_sub]; exact (norm_eval_le hx hv.1).trans_lt hv.2),
      map_add, AlgHom.commutes, hd hv.1]

/-- Continuous algebra homomorphisms commute with directional derivatives on valid inputs. -/
theorem deriv_algHom (f : A →ₐ[𝕜] B) (hf : Continuous f) (hx : ∀ i, ‖x i‖ ≤ a i)
    {e : PolyExprS 𝕜 σ} (hv : Valid a e) :
    f (deriv x h e) = deriv (fun i => f (x i)) (fun i => f (h i)) e := by
  induction e with
  | const c => simp [deriv]
  | var i => rfl
  | add p q hp hq => simp [deriv, hp hv.1, hq hv.2]
  | sub p q hp hq => simp [deriv, hp hv.1, hq hv.2]
  | mul p q hp hq =>
    simp [deriv, hp hv.1, hq hv.2, eval_algHom f hf hx hv.1, eval_algHom f hf hx hv.2]
  | isqrt c d hd =>
    simp only [deriv]
    rw [map_mul, map_smul, map_pow, eval_algHom f hf hx hv, hd hv.1]

/-- **Evaluation at a point**: if `φ : A → 𝕜` is an algebra homomorphism (e.g. evaluation of
a Fourier series at a point) and `φ(d(x)) = r` is real, then the node evaluates to the positive
inverse square root `1/√(c + r)`. -/
theorem eval_isqrt_point (φ : A →ₐ[𝕜] 𝕜) (hx : ∀ i, ‖x i‖ ≤ a i) {c : ℝ} {d : PolyExprS 𝕜 σ}
    (hv : Valid a (isqrt c d)) {r : ℝ} (hr : φ (eval x d) = r) :
    0 < c + r ∧ φ (eval x (isqrt c d)) = (((Real.sqrt (c + r))⁻¹ : ℝ) : 𝕜) := by
  simp only [eval]
  refine algHom_invSqrt (by rw [isqrt_arg_sub]; exact (norm_eval_le hx hv.1).trans_lt hv.2) φ ?_
  rw [map_add, AlgHom.commutes, hr, Algebra.algebraMap_self, RingHom.id_apply,
    RCLike.ofReal_add]

end Hom

section Strip

open WEll1Z2

variable {σ : Type*} {ρ : ℝ} {x h : σ → FA} {a b : σ → ℝ}

/-- **Strip majorant bound** `‖P(x)‖_ρ ≤ P̂(a)` for valid `P` (`ρ ≥ 0`). -/
theorem Bd.evalS (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) {e : PolyExprS ℂ σ}
    (hv : Valid a e) : Bd ρ (eval x e) (maj a e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have e1 : eval x e = toFA hρ (eval xl e) := by
    rw [eval_algHom (toFA hρ) (continuous_toFA hρ) hxl hv]
    congr 1; funext i; exact (toFA_liftS hρ _ _).symm
  rw [e1]
  exact (Bd_toFA hρ _).le (norm_eval_le hxl hv)

/-- **Strip derivative bound** `‖DP(x)h‖_ρ ≤ P̂'(a)·b` for valid `P`. -/
theorem Bd.derivS (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (hh : ∀ i, Bd ρ (h i) (b i))
    {e : PolyExprS ℂ σ} (hv : Valid a e) : Bd ρ (deriv x h e) (majD a b e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have e1 : deriv x h e = toFA hρ (deriv xl hl e) := by
    rw [deriv_algHom (toFA hρ) (continuous_toFA hρ) hxl hv]
    congr 1 <;> funext i <;> exact (toFA_liftS hρ _ _).symm
  rw [e1]
  exact (Bd_toFA hρ _).le (norm_deriv_le hxl hhl hv)

/-- **Strip Lipschitz bound** `‖P(x + h) − P(x)‖_ρ ≤ P̂'(a + b)·b` for `P` valid at `a + b`. -/
theorem Bd.eval_add_subS (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i))
    (hh : ∀ i, Bd ρ (h i) (b i)) {e : PolyExprS ℂ σ} (hv : Valid (a + b) e) :
    Bd ρ (eval (x + h) e - eval x e) (majD (a + b) b e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hxl i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hhl i)
  have hva : Valid a e := hv.mono ha fun i => le_add_of_nonneg_right (hb i)
  have e1 : eval (x + h) e - eval x e = toFA hρ (eval (xl + hl) e - eval xl e) := by
    rw [map_sub, eval_algHom (toFA hρ) (continuous_toFA hρ) (norm_add_le_add hxl hhl) hv,
      eval_algHom (toFA hρ) (continuous_toFA hρ) hxl hva]
    congr 2 <;> funext i <;> simp [xl, hl, liftF, toFA_liftS]
  rw [e1]
  exact (Bd_toFA hρ _).le (norm_eval_add_sub_le hxl hhl hv)

/-- **Strip Taylor bound** `‖P(x + h) − P(x) − DP(x)h‖_ρ ≤ ½ P̂''(a + b)[b, b]` for `P` valid
at `a + b`. -/
theorem Bd.taylorS (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (hh : ∀ i, Bd ρ (h i) (b i))
    {e : PolyExprS ℂ σ} (hv : Valid (a + b) e) :
    Bd ρ (eval (x + h) e - eval x e - deriv x h e) (majD2 (a + b) b e / 2) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have ha : ∀ i, 0 ≤ a i := fun i => (norm_nonneg _).trans (hxl i)
  have hb : ∀ i, 0 ≤ b i := fun i => (norm_nonneg _).trans (hhl i)
  have hva : Valid a e := hv.mono ha fun i => le_add_of_nonneg_right (hb i)
  have e1 : eval (x + h) e - eval x e - deriv x h e =
      toFA hρ (eval (xl + hl) e - eval xl e - deriv xl hl e) := by
    rw [map_sub, map_sub, eval_algHom (toFA hρ) (continuous_toFA hρ) (norm_add_le_add hxl hhl) hv,
      eval_algHom (toFA hρ) (continuous_toFA hρ) hxl hva,
      deriv_algHom (toFA hρ) (continuous_toFA hρ) hxl hva]
    congr 2 <;> try congr 1
    all_goals funext i; simp [xl, hl, liftF, toFA_liftS]
  rw [e1]
  exact (Bd_toFA hρ _).le (norm_taylor_le hxl hhl hv)

end Strip

/-! ## Sanity checks -/

/-- The expression `(1 + (−3/4))^{−1/2}`. -/
def isqrtQuarter : PolyExprS ℝ Unit := isqrt 1 (const (-(3 / 4)))

/-- Sanity (accepted fixture): `isqrtQuarter` is valid and evaluates to `(1/4)^{−1/2} = 2`. -/
theorem isqrt_quarter :
    Valid (fun _ => 0) isqrtQuarter ∧ eval (fun _ : Unit => (0 : ℝ)) isqrtQuarter = 2 := by
  refine ⟨⟨trivial, by norm_num [maj]⟩, ?_⟩
  simp only [isqrtQuarter, eval, Algebra.algebraMap_self, RingHom.id_apply,
    RCLike.ofReal_real_eq_id, id]
  have e : (1 : ℝ) + -(3 / 4) = 1 / 4 := by norm_num
  rw [e]
  exact invSqrt_quarter

/-- Sanity: the majorant of `isqrtQuarter` is sharp, `g_1(3/4) = (1/4)^{−1/2} = 2`. -/
theorem maj_isqrtQuarter : maj (fun _ => 0) isqrtQuarter = 2 := by
  simp only [isqrtQuarter, maj, isqG, norm_neg]
  rw [show (1 : ℝ) - ‖(3 / 4 : ℝ)‖ = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- Sanity: the derivative of `(1 + x)^{−1/2}` at `x = 0` in direction `h` is `−h/2`. -/
theorem deriv_isqrt_zero (h : ℝ) :
    deriv (fun _ : Unit => (0 : ℝ)) (fun _ => h) (isqrt 1 (var ()) : PolyExprS ℝ Unit) =
      -(h / 2) := by
  simp only [deriv, eval, Algebra.algebraMap_self, RingHom.id_apply, add_zero,
    RCLike.ofReal_real_eq_id, id]
  rw [invSqrt_real (by norm_num)]
  simp only [Real.sqrt_one, inv_one, one_pow, smul_eq_mul]
  ring

/-- Rejected fixture: when the deviation majorant reaches the centre the node is not valid, and
indeed at `1 + (−1) = 0` there is no inverse square root (`y² · 0 ≠ 1`). -/
theorem not_valid_isqrt :
    ¬ Valid (fun _ => 0) (isqrt 1 (const (-1)) : PolyExprS ℝ Unit) ∧
      ∀ y : ℝ,
        y ^ 2 * (1 + eval (fun _ : Unit => (0 : ℝ)) (const (-1) : PolyExprS ℝ Unit)) ≠ 1 := by
  refine ⟨fun hv => ?_, fun y => ?_⟩
  · have := hv.2
    simp [maj] at this
  · simp [eval]

end PolyExprS

end PlasmaLean.Theory.KAM
