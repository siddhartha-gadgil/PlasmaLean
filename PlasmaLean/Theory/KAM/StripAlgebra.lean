/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.Composition
public import PlasmaLean.Certificates.Kronecker2DWeighted

/-!
# The strip algebra: double Fourier series with bounds on several strips (KAM route, K3d)

The Newton step of the K3 plan (`notes/theory/kam-k3-plan.md` §2) loses analyticity: every
small-divisor solve and every derivative is estimated from a strip of width `ρ` to a narrower
strip `ρ − δ`. Rather than moving between the spaces `WEll1Z2 ρ` (whose ring structures depend on
`ρ`), all objects here live in **one** commutative ring, the algebra
`𝔸 = ℓ¹(ℤ²)` (`FA = WEll1Z2 0`) of absolutely convergent double Fourier series, and the strip
norms are recorded by a predicate:

* `Bd ρ x B`: the Fourier coefficients of `x` satisfy `∑ |x_{k,m}| e^{ρ(|k|+|m|)} ≤ B` (and the
  sum converges). It is monotone in `ρ` and `B` (`Bd.mono`), closed under the ring operations with
  the Banach-algebra estimate (`Bd.add`, `Bd.mul`, `Bd.pow`, …), and gives Neumann inverses
  (`Bd.inverse`).
* **Polynomial majorants** (`Bd.eval`, `Bd.deriv`, `Bd.taylor`, `Bd.eval_add_sub`): the estimates
  of `Theory/KAM/Composition` hold for `Bd ρ`, by lifting to `WEll1Z2 ρ` through the algebra
  homomorphism `toFA : WEll1Z2 ρ →ₐ[ℂ] 𝔸` (restriction of the strip).
* **Fourier multipliers of order one** `dS a b` with symbol `i (a k + b m)`: `∂_θ = dS 1 0`,
  `∂_ψ = dS 0 1`, and the transport `𝓛 = ι ∂_θ + 2 ∂_ψ = dS ι 2` of the flow form. On *analytic*
  elements (`Ana x`: `Bd ρ x B` for some `ρ > 0`) they are derivations (`dS_mul`), kill
  constants, commute with each other (`dS_dS_comm`), satisfy the inverse rule (`dS_inverse`) and
  the chain rule for polynomial expressions (`dS_eval`); the Cauchy estimate is `Bd.dS`.
* the **zero-mean solution** `coh ω x` of `(∂_ψ + ω ∂_θ) u = x` (`dS_coh`) with the Rüssmann
  estimate `Bd.coh`, and the **average** `avg x = x_{0,0}` (`avg_dS`: derivatives have mean zero).
* **reality**: `IsReal x` (conjugation symmetry `x_{−n} = conj x_n`, i.e. a real-valued
  function) is preserved by all of the above with real parameters.

**Sanity.** `Bd_one`, `dS_one` (constants are killed), `avg_one`, the mode fixture `dS_mode`
(`dS a b` multiplies the mode `(k, m)` by `i (a k + b m)`), and the rejected fixture
`not_Bd_neg` (a strict bound below the norm of `1` fails).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

open Complex WEll1Z2 PlasmaLean.Certificates.Kron2

/-- `0 ≤ 0`, so `ℓ¹_0(ℤ²)` carries its Banach-algebra structure. -/
instance fact_zero_le_zero : Fact ((0 : ℝ) ≤ 0) := ⟨le_rfl⟩

/-- The algebra `𝔸 = ℓ¹(ℤ²)` of absolutely convergent double Fourier series (convolution of
coefficients). -/
abbrev FA : Type := WEll1Z2 0

/-! ## Strip bounds -/

/-- `Bd ρ x B`: the coefficients of `x` have finite weighted norm `‖x‖_ρ ≤ B` on the strip of
width `ρ`. -/
def Bd (ρ : ℝ) (x : FA) (B : ℝ) : Prop := InWeighted ρ (coeff x) ∧ wnorm ρ (coeff x) ≤ B

/-- `x` is analytic: it has a finite weighted norm on some strip of positive width. -/
def Ana (x : FA) : Prop := ∃ ρ B, 0 < ρ ∧ Bd ρ x B

namespace Bd

variable {ρ ρ' B B' : ℝ} {x y : FA}

/-- A bound is nonnegative. -/
theorem nonneg (h : Bd ρ x B) : 0 ≤ B := (wnorm_nonneg _ _).trans h.2

/-- Monotonicity in the strip width and in the bound. -/
theorem mono (h : Bd ρ x B) (hρ : ρ' ≤ ρ) (hB : B ≤ B') : Bd ρ' x B' :=
  ⟨h.1.mono hρ, (wnorm_mono h.1 hρ).trans (h.2.trans hB)⟩

/-- Monotonicity in the bound. -/
theorem le (h : Bd ρ x B) (hB : B ≤ B') : Bd ρ x B' := h.mono le_rfl hB

/-- Monotonicity in the strip width. -/
theorem strip (h : Bd ρ x B) (hρ : ρ' ≤ ρ) : Bd ρ' x B := h.mono hρ le_rfl

/-- A coefficient is bounded by the norm (`ρ ≥ 0`). -/
theorem norm_coeff_le (h : Bd ρ x B) (hρ : 0 ≤ ρ) (n : ℤ × ℤ) : ‖coeff x n‖ ≤ B := by
  have h1 := norm_mul_weight_le_wnorm h.1 n
  have h2 : 1 ≤ weight ρ n := one_le_weight hρ n
  calc ‖coeff x n‖ ≤ ‖coeff x n‖ * weight ρ n := le_mul_of_one_le_right (norm_nonneg _) h2
    _ ≤ B := h1.trans h.2

/-- Sums. -/
theorem add (hx : Bd ρ x B) (hy : Bd ρ y B') : Bd ρ (x + y) (B + B') := by
  have e : coeff (x + y) = fun n => coeff x n + coeff y n := funext fun n => coeff_add x y n
  refine ⟨e ▸ inWeighted_add hx.1 hy.1, ?_⟩
  rw [e]; exact (wnorm_add_le hx.1 hy.1).trans (add_le_add hx.2 hy.2)

/-- Scalar multiples. -/
theorem smul (hx : Bd ρ x B) (c : ℂ) : Bd ρ (c • x) (‖c‖ * B) := by
  have e : coeff (c • x) = fun n => c * coeff x n := funext fun n => coeff_smul c x n
  refine ⟨e ▸ inWeighted_smul hx.1 c, ?_⟩
  rw [e, wnorm_smul]; exact mul_le_mul_of_nonneg_left hx.2 (norm_nonneg _)

/-- Negation. -/
theorem neg (hx : Bd ρ x B) : Bd ρ (-x) B := by
  have h := hx.smul (-1)
  simpa using h

/-- Differences. -/
theorem sub (hx : Bd ρ x B) (hy : Bd ρ y B') : Bd ρ (x - y) (B + B') := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- **Banach-algebra estimate** (`ρ ≥ 0`). -/
theorem mul (hρ : 0 ≤ ρ) (hx : Bd ρ x B) (hy : Bd ρ y B') : Bd ρ (x * y) (B * B') := by
  rw [Bd, coeff_mul']
  refine ⟨inWeighted_cconv hρ hx.1 hy.1, ?_⟩
  exact (wnorm_cconv_le hρ hx.1 hy.1).trans
    (mul_le_mul hx.2 hy.2 (wnorm_nonneg _ _) hx.nonneg)

end Bd

/-- The zero element. -/
theorem Bd_zero (ρ : ℝ) : Bd ρ 0 0 := by
  have e : coeff (0 : FA) = 0 := funext fun n => coeff_zero n
  refine ⟨?_, ?_⟩
  · rw [e]; unfold InWeighted; simp
  · rw [e, wnorm_zero]

/-- Coefficients of the unit. -/
theorem coeff_one_FA : coeff (1 : FA) = delta2 := funext coeff_one

/-- `wnorm ρ δ₀ = 1` for every `ρ`. -/
theorem wnorm_delta2 (ρ : ℝ) : wnorm ρ delta2 = 1 := by
  rw [wnorm, tsum_eq_single 0 (fun n hn => by simp [delta2, hn])]
  simp [delta2, weight, modeSize]

/-- The unit: `‖1‖_ρ = 1`. -/
theorem Bd_one (ρ : ℝ) : Bd ρ 1 1 := by
  refine ⟨?_, ?_⟩
  · rw [coeff_one_FA]; unfold InWeighted
    exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp [delta2, Finset.mem_singleton.not.1 hn]
  · rw [coeff_one_FA, wnorm_delta2]

/-- Constants: `‖c‖_ρ = |c|`. -/
theorem Bd_algebraMap (ρ : ℝ) (c : ℂ) : Bd ρ (algebraMap ℂ FA c) ‖c‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  simpa using (Bd_one ρ).smul c

/-- Powers. -/
theorem Bd.pow {ρ B : ℝ} {x : FA} (hρ : 0 ≤ ρ) (hx : Bd ρ x B) : ∀ n : ℕ, Bd ρ (x ^ n) (B ^ n)
  | 0 => by simpa using Bd_one ρ
  | n + 1 => by rw [pow_succ, pow_succ]; exact (Bd.pow hρ hx n).mul hρ hx

/-- Rejected fixture: the bound must dominate the norm (`‖1‖_ρ = 1`, so `Bd ρ 1 (1/2)` fails). -/
theorem not_Bd_one_half (ρ : ℝ) : ¬ Bd ρ 1 (1 / 2) := by
  rintro ⟨-, h⟩
  rw [coeff_one_FA, wnorm_delta2] at h
  norm_num at h

/-! ## Lifting to a strip and polynomial majorants -/

/-- The algebra homomorphism `ℓ¹_ρ(ℤ²) → 𝔸` (forgetting the strip; same coefficients). -/
def toFA {ρ : ℝ} (hρ : 0 ≤ ρ) : @AlgHom ℂ (WEll1Z2 ρ) FA _
    (@CommSemiring.toSemiring _ (@CommRing.toCommSemiring _ (@instCommRing ρ ⟨hρ⟩))) _
    (@instAlgebra ρ ⟨hρ⟩) _ :=
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  { toFun := restrict hρ
    map_one' := ext_coeff fun n => by simp
    map_mul' := fun x y => restrict_mul hρ x y
    map_zero' := ext_coeff fun n => by simp
    map_add' := fun x y => restrict_add hρ x y
    commutes' := fun c => ext_coeff fun n => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp }

/-- `toFA` keeps the coefficients. -/
@[simp] theorem coeff_toFA {ρ : ℝ} (hρ : 0 ≤ ρ) (x : WEll1Z2 ρ) (n : ℤ × ℤ) :
    coeff (toFA hρ x) n = coeff x n := coeff_restrict hρ x n

/-- An element of a strip space is bounded by its norm. -/
theorem Bd_toFA {ρ : ℝ} (hρ : 0 ≤ ρ) (x : WEll1Z2 ρ) : Bd ρ (toFA hρ x) ‖x‖ := by
  have e : coeff (toFA hρ x) = coeff x := funext (coeff_toFA hρ x)
  refine ⟨e ▸ inWeighted_coeff x, ?_⟩
  rw [e, norm_eq_wnorm]

/-- The lift of `x ∈ 𝔸` with `Bd ρ x B` to `ℓ¹_ρ(ℤ²)`. -/
def liftS {ρ : ℝ} (x : FA) (h : InWeighted ρ (coeff x)) : WEll1Z2 ρ := ofCoeff (coeff x) h

/-- `toFA ∘ liftS = id`. -/
theorem toFA_liftS {ρ : ℝ} (hρ : 0 ≤ ρ) (x : FA) (h : InWeighted ρ (coeff x)) :
    toFA hρ (liftS x h) = x := ext_coeff fun n => by simp [liftS]

/-- The norm of the lift is the strip norm. -/
theorem norm_liftS {ρ : ℝ} (x : FA) (h : InWeighted ρ (coeff x)) :
    ‖liftS x h‖ = wnorm ρ (coeff x) := norm_ofCoeff _ _

/-- Evaluation of polynomial expressions commutes with algebra homomorphisms. -/
theorem PolyExpr.eval_algHom {A B : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    [NormedCommRing B] [NormedAlgebra ℂ B] (f : A →ₐ[ℂ] B) {σ : Type*} (x : σ → A) :
    ∀ e : PolyExpr ℂ σ, f (PolyExpr.eval x e) = PolyExpr.eval (fun i => f (x i)) e
  | .const c => by simp [PolyExpr.eval]
  | .var i => rfl
  | .add p q => by simp [PolyExpr.eval, eval_algHom f x p, eval_algHom f x q]
  | .sub p q => by simp [PolyExpr.eval, eval_algHom f x p, eval_algHom f x q]
  | .mul p q => by simp [PolyExpr.eval, eval_algHom f x p, eval_algHom f x q]

/-- Directional derivatives of polynomial expressions commute with algebra homomorphisms. -/
theorem PolyExpr.deriv_algHom {A B : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    [NormedCommRing B] [NormedAlgebra ℂ B] (f : A →ₐ[ℂ] B) {σ : Type*} (x h : σ → A) :
    ∀ e : PolyExpr ℂ σ, f (PolyExpr.deriv x h e) =
      PolyExpr.deriv (fun i => f (x i)) (fun i => f (h i)) e
  | .const c => by simp [PolyExpr.deriv]
  | .var i => rfl
  | .add p q => by simp [PolyExpr.deriv, deriv_algHom f x h p, deriv_algHom f x h q]
  | .sub p q => by simp [PolyExpr.deriv, deriv_algHom f x h p, deriv_algHom f x h q]
  | .mul p q => by
    simp [PolyExpr.deriv, deriv_algHom f x h p, deriv_algHom f x h q, eval_algHom]


section Majorants

variable {σ : Type*} {ρ : ℝ} {x h : σ → FA} {a b : σ → ℝ}

/-- Lift of a family with strip bounds. -/
def liftF (x : σ → FA) (hx : ∀ i, InWeighted ρ (coeff (x i))) : σ → WEll1Z2 ρ :=
  fun i => liftS (x i) (hx i)

/-- **Majorant bound** `‖P(x)‖_ρ ≤ P̂(a)` from `‖x i‖_ρ ≤ a i` (`ρ ≥ 0`). -/
theorem Bd.eval (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (e : PolyExpr ℂ σ) :
    Bd ρ (PolyExpr.eval x e) (PolyExpr.maj a e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have e1 : PolyExpr.eval x e = toFA hρ (PolyExpr.eval xl e) := by
    rw [PolyExpr.eval_algHom]; congr 1; funext i; exact (toFA_liftS hρ _ _).symm
  rw [e1]
  exact (Bd_toFA hρ _).le (PolyExpr.norm_eval_le hxl e)

/-- **Derivative bound** `‖DP(x)h‖_ρ ≤ P̂'(a)·b`. -/
theorem Bd.deriv (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (hh : ∀ i, Bd ρ (h i) (b i))
    (e : PolyExpr ℂ σ) : Bd ρ (PolyExpr.deriv x h e) (PolyExpr.majD a b e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have e1 : PolyExpr.deriv x h e = toFA hρ (PolyExpr.deriv xl hl e) := by
    rw [PolyExpr.deriv_algHom]; congr 1 <;> funext i <;> exact (toFA_liftS hρ _ _).symm
  rw [e1]
  exact (Bd_toFA hρ _).le (PolyExpr.norm_deriv_le hxl hhl e)

/-- **Lipschitz bound** `‖P(x + h) − P(x)‖_ρ ≤ P̂'(a + b)·b`. -/
theorem Bd.eval_add_sub (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (hh : ∀ i, Bd ρ (h i) (b i))
    (e : PolyExpr ℂ σ) :
    Bd ρ (PolyExpr.eval (x + h) e - PolyExpr.eval x e) (PolyExpr.majD (a + b) b e) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have e1 : PolyExpr.eval (x + h) e - PolyExpr.eval x e =
      toFA hρ (PolyExpr.eval (xl + hl) e - PolyExpr.eval xl e) := by
    rw [map_sub, PolyExpr.eval_algHom, PolyExpr.eval_algHom]
    congr 2 <;> funext i <;> simp [xl, hl, liftF, toFA_liftS]
  rw [e1]
  exact (Bd_toFA hρ _).le (PolyExpr.norm_eval_add_sub_le hxl hhl e)

/-- **Taylor bound** `‖P(x + h) − P(x) − DP(x)h‖_ρ ≤ ½ P̂''(a + b)[b, b]`. -/
theorem Bd.taylor (hρ : 0 ≤ ρ) (hx : ∀ i, Bd ρ (x i) (a i)) (hh : ∀ i, Bd ρ (h i) (b i))
    (e : PolyExpr ℂ σ) :
    Bd ρ (PolyExpr.eval (x + h) e - PolyExpr.eval x e - PolyExpr.deriv x h e)
      (PolyExpr.majD2 (a + b) b e / 2) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  set xl := liftF x (fun i => (hx i).1)
  set hl := liftF h (fun i => (hh i).1)
  have hxl : ∀ i, ‖xl i‖ ≤ a i := fun i => by
    simp only [xl, liftF]; rw [norm_liftS]; exact (hx i).2
  have hhl : ∀ i, ‖hl i‖ ≤ b i := fun i => by
    simp only [hl, liftF]; rw [norm_liftS]; exact (hh i).2
  have e1 : PolyExpr.eval (x + h) e - PolyExpr.eval x e - PolyExpr.deriv x h e =
      toFA hρ (PolyExpr.eval (xl + hl) e - PolyExpr.eval xl e - PolyExpr.deriv xl hl e) := by
    rw [map_sub, map_sub, PolyExpr.eval_algHom, PolyExpr.eval_algHom, PolyExpr.deriv_algHom]
    congr 2 <;> try congr 1
    all_goals funext i; simp [xl, hl, liftF, toFA_liftS]
  rw [e1]
  exact (Bd_toFA hρ _).le (PolyExpr.norm_taylor_le hxl hhl e)

end Majorants

/-! ## Neumann inverses -/

/-- Ring homomorphisms commute with `Ring.inverse` on units. -/
theorem map_ringInverse {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {x : R} (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  have hfx : IsUnit (f x) := hx.map f
  have h1 : (1 : S) = f x * f (Ring.inverse x) := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hx, map_one]
  have := (Ring.inverse_mul_eq_iff_eq_mul (f x) 1 (f (Ring.inverse x)) hfx).2 h1
  rw [mul_one] at this
  exact this.symm

/-- **Neumann bound** on a strip: if `‖x − c‖_ρ ≤ β < |c|` then `x` is a unit of `𝔸` and
`‖x⁻¹‖_ρ ≤ 1/(|c| − β)`. -/
theorem Bd.inverse {ρ β : ℝ} {x : FA} {c : ℂ} (hρ : 0 ≤ ρ)
    (hx : Bd ρ (x - algebraMap ℂ FA c) β) (hβ : β < ‖c‖) :
    IsUnit x ∧ Bd ρ (Ring.inverse x) (1 / (‖c‖ - β)) := by
  have : Fact (0 ≤ ρ) := ⟨hρ⟩
  have hw : InWeighted ρ (coeff x) := by
    have h1 := (hx.add (Bd_algebraMap ρ c)).1
    simpa using h1
  set xl : WEll1Z2 ρ := liftS x hw
  have hsub : ‖xl - algebraMap ℂ (WEll1Z2 ρ) c‖ ≤ β := by
    have e : xl - algebraMap ℂ (WEll1Z2 ρ) c = liftS (x - algebraMap ℂ FA c) hx.1 :=
      ext_coeff fun n => by
        simp only [xl, liftS, coeff_sub, coeff_ofCoeff]
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        simp
    rw [e, norm_liftS]; exact hx.2
  obtain ⟨hu, hinv⟩ := WEll1Z2.inverse_bound xl c (hsub.trans_lt hβ)
  have hmap : toFA hρ xl = x := toFA_liftS hρ x hw
  have hux : IsUnit x := hmap ▸ hu.map (toFA hρ)
  refine ⟨hux, ?_⟩
  have hi : toFA hρ (Ring.inverse xl) = Ring.inverse x := by
    rw [← hmap]; exact map_ringInverse (toFA hρ) hu
  rw [← hi]
  refine (Bd_toFA hρ _).le (hinv.trans ?_)
  have : 0 < ‖c‖ - β := by linarith
  have : 0 < ‖c‖ - ‖xl - algebraMap ℂ (WEll1Z2 ρ) c‖ := by linarith
  gcongr


/-! ## Analytic elements -/

namespace Ana

variable {x y : FA}

/-- Analytic elements are absolutely summable on some strip `ρ > 0`. -/
theorem of_Bd {ρ B : ℝ} (hρ : 0 < ρ) (h : Bd ρ x B) : Ana x := ⟨ρ, B, hρ, h⟩

/-- Sums. -/
theorem add (hx : Ana x) (hy : Ana y) : Ana (x + y) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  obtain ⟨ρ', B', hρ', h'⟩ := hy
  exact ⟨min ρ ρ', B + B', lt_min hρ hρ',
    (h.strip (min_le_left _ _)).add (h'.strip (min_le_right _ _))⟩

/-- Products. -/
theorem mul (hx : Ana x) (hy : Ana y) : Ana (x * y) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  obtain ⟨ρ', B', hρ', h'⟩ := hy
  exact ⟨min ρ ρ', B * B', lt_min hρ hρ',
    (h.strip (min_le_left _ _)).mul (le_min hρ.le hρ'.le) (h'.strip (min_le_right _ _))⟩

/-- Scalar multiples. -/
theorem smul (hx : Ana x) (c : ℂ) : Ana (c • x) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx; exact ⟨ρ, _, hρ, h.smul c⟩

/-- Negation. -/
theorem neg (hx : Ana x) : Ana (-x) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx; exact ⟨ρ, _, hρ, h.neg⟩

/-- Differences. -/
theorem sub (hx : Ana x) (hy : Ana y) : Ana (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- Constants. -/
theorem algebraMap (c : ℂ) : Ana (algebraMap ℂ FA c) := ⟨1, _, one_pos, Bd_algebraMap 1 c⟩

/-- The unit. -/
theorem one : Ana (1 : FA) := ⟨1, _, one_pos, Bd_one 1⟩

/-- Zero. -/
theorem zero : Ana (0 : FA) := ⟨1, _, one_pos, Bd_zero 1⟩

/-- Powers. -/
theorem pow (hx : Ana x) : ∀ n : ℕ, Ana (x ^ n)
  | 0 => by simpa using one
  | n + 1 => by rw [pow_succ]; exact (pow hx n).mul hx

/-- Polynomial expressions of analytic elements are analytic. -/
theorem eval {σ : Type*} {z : σ → FA} (hz : ∀ i, Ana (z i)) :
    ∀ e : PolyExpr ℂ σ, Ana (PolyExpr.eval z e)
  | .const c => algebraMap c
  | .var i => hz i
  | .add p q => (eval hz p).add (eval hz q)
  | .sub p q => (eval hz p).sub (eval hz q)
  | .mul p q => (eval hz p).mul (eval hz q)

end Ana

/-- Analytic elements have absolutely summable coefficients. -/
theorem Ana.summable {x : FA} (hx : Ana x) : Summable fun n => ‖coeff x n‖ := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  exact summable_norm_of_inWeighted hρ.le h.1

/-! ## Fourier multipliers of order one -/

/-- The symbol `i (a k + b m)` acting on coefficients. -/
def dsym (a b : ℂ) (u : ℤ × ℤ → ℂ) (n : ℤ × ℤ) : ℂ := I * (a * n.1 + b * n.2) * u n

/-- The multiplier with symbol `i (a k + b m)` on `𝔸` (`0` if the result is not summable):
`∂_θ = dS 1 0`, `∂_ψ = dS 0 1`, `𝓛 = ι ∂_θ + 2 ∂_ψ = dS ι 2`. -/
def dS (a b : ℂ) (x : FA) : FA :=
  open Classical in if h : InWeighted 0 (dsym a b (coeff x)) then ofCoeff _ h else 0

/-- Coefficients of `dS a b x` when the symbol series is summable. -/
theorem coeff_dS {a b : ℂ} {x : FA} (h : InWeighted 0 (dsym a b (coeff x))) :
    coeff (dS a b x) = dsym a b (coeff x) := by
  funext n; simp [dS, h]

/-- `|a k + b m| ≤ max(|a|, |b|) (|k| + |m|)`. -/
theorem norm_symbol_le (a b : ℂ) (n : ℤ × ℤ) :
    ‖a * n.1 + b * n.2‖ ≤ max ‖a‖ ‖b‖ * modeSize n := by
  have h1 : ‖a * (n.1 : ℂ)‖ ≤ max ‖a‖ ‖b‖ * |(n.1 : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have h2 : ‖b * (n.2 : ℂ)‖ ≤ max ‖a‖ ‖b‖ * |(n.2 : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  calc _ ≤ ‖a * (n.1 : ℂ)‖ + ‖b * (n.2 : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by rw [modeSize, mul_add]; exact add_le_add h1 h2

/-- **Cauchy estimate** for `dsym`: `‖dsym u‖_{ρ−δ} ≤ max(|a|,|b|)/(eδ) ‖u‖_ρ`. -/
theorem dsym_estimate {ρ δ : ℝ} (hδ : 0 < δ) (a b : ℂ) {u : ℤ × ℤ → ℂ} (hu : InWeighted ρ u) :
    InWeighted (ρ - δ) (dsym a b u) ∧
      wnorm (ρ - δ) (dsym a b u) ≤ max ‖a‖ ‖b‖ / (Real.exp 1 * δ) * wnorm ρ u := by
  refine wnorm_le_of_termwise hu fun n => ?_
  have hsup := pow_mul_exp_neg_le (modeSize_nonneg n) hδ 1
  simp only [pow_one, Nat.cast_one] at hsup
  rw [weight_sub]
  have hn : ‖dsym a b u n‖ ≤ max ‖a‖ ‖b‖ * modeSize n * ‖u n‖ := by
    simp only [dsym, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_right (norm_symbol_le a b n) (norm_nonneg _)
  have hC : 0 ≤ max ‖a‖ ‖b‖ := (norm_nonneg a).trans (le_max_left _ _)
  calc ‖dsym a b u n‖ * (weight ρ n * Real.exp (-δ * modeSize n))
      ≤ max ‖a‖ ‖b‖ * modeSize n * ‖u n‖ * (weight ρ n * Real.exp (-δ * modeSize n)) :=
        mul_le_mul_of_nonneg_right hn (by have := weight_pos ρ n; positivity)
    _ = max ‖a‖ ‖b‖ * (modeSize n * Real.exp (-δ * modeSize n)) * (‖u n‖ * weight ρ n) := by
        ring
    _ ≤ max ‖a‖ ‖b‖ * (1 / (Real.exp 1 * δ)) * (‖u n‖ * weight ρ n) := by
        gcongr
        · exact mul_nonneg (norm_nonneg _) (weight_pos ρ n).le
    _ = _ := by ring

/-- **Cauchy estimate** on `𝔸`: `‖dS a b x‖_{ρ−δ} ≤ max(|a|,|b|)/(eδ) ‖x‖_ρ` for `0 < δ ≤ ρ`. -/
theorem Bd.dS {ρ δ B : ℝ} {x : FA} (hx : Bd ρ x B) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (a b : ℂ) :
    Bd (ρ - δ) (dS a b x) (max ‖a‖ ‖b‖ / (Real.exp 1 * δ) * B) := by
  obtain ⟨h1, h2⟩ := dsym_estimate hδ a b hx.1
  have h0 : InWeighted 0 (dsym a b (coeff x)) := h1.mono (by linarith)
  rw [Bd, coeff_dS h0]
  refine ⟨h1, h2.trans ?_⟩
  have : 0 ≤ max ‖a‖ ‖b‖ / (Real.exp 1 * δ) := by
    have := (norm_nonneg a).trans (le_max_left ‖a‖ ‖b‖); positivity
  exact mul_le_mul_of_nonneg_left hx.2 this

/-- For analytic `x`, the symbol series is summable. -/
theorem Ana.inW_dsym {x : FA} (hx : Ana x) (a b : ℂ) : InWeighted 0 (dsym a b (coeff x)) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  have := (dsym_estimate hρ a b h.1).1
  rwa [sub_self] at this

/-- `dS` of an analytic element is analytic. -/
theorem Ana.d {x : FA} (hx : Ana x) (a b : ℂ) : Ana (KAM.dS a b x) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  refine ⟨ρ / 2, max ‖a‖ ‖b‖ / (Real.exp 1 * (ρ / 2)) * B, by positivity, ?_⟩
  have := h.dS (δ := ρ / 2) (by positivity) (by linarith) a b
  rwa [show ρ - ρ / 2 = ρ / 2 by ring] at this

/-- Coefficients of `dS` of an analytic element. -/
theorem Ana.coeff_dS {x : FA} (hx : Ana x) (a b : ℂ) :
    coeff (KAM.dS a b x) = dsym a b (coeff x) := KAM.coeff_dS (hx.inW_dsym a b)

/-- **Leibniz rule** for coefficient functions. -/
theorem dsym_cconv (a b : ℂ) {f g : ℤ × ℤ → ℂ} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) (hdf : Summable fun n => ‖dsym a b f n‖)
    (hdg : Summable fun n => ‖dsym a b g n‖) :
    dsym a b (cconv f g) = cconv (dsym a b f) g + cconv f (dsym a b g) := by
  funext n
  change dsym a b (cconv f g) n =
    (∑' c, dsym a b f c * g (n - c)) + ∑' c, f c * dsym a b g (n - c)
  rw [← (summable_conv_summand hdf hg n).tsum_add (summable_conv_summand hf hdg n)]
  simp only [dsym, cconv]
  rw [← tsum_mul_left]
  refine tsum_congr fun c => ?_
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  ring

/-- **Leibniz rule**: `dS` is a derivation on analytic elements. -/
theorem dS_mul (a b : ℂ) {x y : FA} (hx : Ana x) (hy : Ana y) :
    dS a b (x * y) = dS a b x * y + x * dS a b y := by
  refine ext_coeff fun n => ?_
  rw [(hx.mul hy).coeff_dS, coeff_add, coeff_mul, coeff_mul, coeff_mul', hx.coeff_dS,
    hy.coeff_dS, dsym_cconv a b hx.summable hy.summable
      ((inWeighted_zero_iff _).1 (hx.inW_dsym a b)) ((inWeighted_zero_iff _).1 (hy.inW_dsym a b))]
  rfl

/-- `dS` is additive on analytic elements. -/
theorem dS_add (a b : ℂ) {x y : FA} (hx : Ana x) (hy : Ana y) :
    dS a b (x + y) = dS a b x + dS a b y := by
  refine ext_coeff fun n => ?_
  rw [(hx.add hy).coeff_dS, coeff_add, hx.coeff_dS, hy.coeff_dS]
  simp [dsym, coeff_add, mul_add]

/-- `dS` commutes with scalars on analytic elements. -/
theorem dS_smul (a b c : ℂ) {x : FA} (hx : Ana x) : dS a b (c • x) = c • dS a b x := by
  refine ext_coeff fun n => ?_
  rw [(hx.smul c).coeff_dS, coeff_smul, hx.coeff_dS]
  simp only [dsym, coeff_smul]; ring

/-- `dS` commutes with negation on analytic elements. -/
theorem dS_neg (a b : ℂ) {x : FA} (hx : Ana x) : dS a b (-x) = -dS a b x := by
  have := dS_smul a b (-1) hx; simpa using this

/-- `dS` commutes with differences on analytic elements. -/
theorem dS_sub (a b : ℂ) {x y : FA} (hx : Ana x) (hy : Ana y) :
    dS a b (x - y) = dS a b x - dS a b y := by
  rw [sub_eq_add_neg, dS_add a b hx hy.neg, dS_neg a b hy, ← sub_eq_add_neg]

/-- `dS` kills constants. -/
theorem dS_algebraMap (a b c : ℂ) : dS a b (algebraMap ℂ FA c) = 0 := by
  have hc : coeff (algebraMap ℂ FA c) = fun n => c * delta2 n := by
    funext n; rw [Algebra.algebraMap_eq_smul_one, coeff_smul, coeff_one]
  have hz : dsym a b (coeff (algebraMap ℂ FA c)) = 0 := by
    funext n; rw [hc]
    by_cases h : n = 0
    · subst h; simp [dsym]
    · simp [dsym, delta2, h]
  refine ext_coeff fun n => ?_
  rw [KAM.coeff_dS (by rw [hz]; unfold InWeighted; simp), hz]
  simp

/-- Sanity: `dS` kills `1`. -/
@[simp] theorem dS_one (a b : ℂ) : dS a b 1 = 0 := by
  have := dS_algebraMap a b 1; simpa using this

/-- `dS` is linear in the symbol (on analytic elements). -/
theorem dS_add_symbol (a b a' b' : ℂ) {x : FA} (hx : Ana x) :
    dS (a + a') (b + b') x = dS a b x + dS a' b' x := by
  refine ext_coeff fun n => ?_
  rw [hx.coeff_dS, coeff_add, hx.coeff_dS, hx.coeff_dS]
  simp only [dsym]; ring

/-- `dS` is homogeneous in the symbol (on analytic elements). -/
theorem dS_smul_symbol (a b c : ℂ) {x : FA} (hx : Ana x) :
    dS (c * a) (c * b) x = c • dS a b x := by
  refine ext_coeff fun n => ?_
  rw [hx.coeff_dS, coeff_smul, hx.coeff_dS]
  simp only [dsym]; ring

/-- Multipliers commute (on analytic elements). -/
theorem dS_dS_comm (a b a' b' : ℂ) {x : FA} (hx : Ana x) :
    dS a b (dS a' b' x) = dS a' b' (dS a b x) := by
  refine ext_coeff fun n => ?_
  rw [(hx.d a' b').coeff_dS, (hx.d a b).coeff_dS, hx.coeff_dS, hx.coeff_dS]
  simp only [dsym]; ring

/-- Powers: `dS (x^n) = n x^{n−1} dS x`. -/
theorem dS_pow (a b : ℂ) {x : FA} (hx : Ana x) :
    ∀ n : ℕ, dS a b (x ^ (n + 1)) = ((n + 1 : ℕ) : FA) * x ^ n * dS a b x
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, dS_mul a b (hx.pow _) hx, dS_pow a b hx n]
    push_cast; ring

/-- **Inverse rule**: `dS (x⁻¹) = −x⁻² dS x` for an analytic unit with analytic inverse. -/
theorem dS_inverse (a b : ℂ) {x : FA} (hx : Ana x) (hu : IsUnit x) (hi : Ana (Ring.inverse x)) :
    dS a b (Ring.inverse x) = -(Ring.inverse x ^ 2 * dS a b x) := by
  have h1 : dS a b (x * Ring.inverse x) = 0 := by rw [Ring.mul_inverse_cancel _ hu, dS_one]
  rw [dS_mul a b hx hi] at h1
  have h2 : Ring.inverse x * x = 1 := Ring.inverse_mul_cancel _ hu
  linear_combination Ring.inverse x * h1 - dS a b (Ring.inverse x) * h2

/-- **Chain rule** for polynomial expressions: `dS (P(x)) = DP(x)·(dS x)`. -/
theorem dS_eval (a b : ℂ) {σ : Type*} {z : σ → FA} (hz : ∀ i, Ana (z i)) :
    ∀ e : PolyExpr ℂ σ, dS a b (PolyExpr.eval z e) =
      PolyExpr.deriv z (fun i => dS a b (z i)) e
  | .const c => by simp [PolyExpr.eval, PolyExpr.deriv, dS_algebraMap]
  | .var i => rfl
  | .add p q => by
    simp only [PolyExpr.eval, PolyExpr.deriv]
    rw [dS_add a b (Ana.eval hz p) (Ana.eval hz q), dS_eval a b hz p, dS_eval a b hz q]
  | .sub p q => by
    simp only [PolyExpr.eval, PolyExpr.deriv]
    rw [dS_sub a b (Ana.eval hz p) (Ana.eval hz q), dS_eval a b hz p, dS_eval a b hz q]
  | .mul p q => by
    simp only [PolyExpr.eval, PolyExpr.deriv]
    rw [dS_mul a b (Ana.eval hz p) (Ana.eval hz q), dS_eval a b hz p, dS_eval a b hz q]

/-- Sanity (mode fixture): `dS a b` multiplies the mode `(k, m)` by `i (a k + b m)`. -/
theorem dS_mode (a b : ℂ) (km : ℤ × ℤ) :
    coeff (dS a b (mode 0 km)) km = I * (a * km.1 + b * km.2) := by
  have h : Ana (mode 0 km) := ⟨1, weight 1 km, one_pos, by
    refine ⟨?_, ?_⟩
    · unfold InWeighted
      exact summable_of_ne_finset_zero (s := {km}) fun n hn => by
        simp [Finset.mem_singleton.not.1 hn]
    · rw [wnorm, tsum_eq_single km (fun n hn => by simp [hn])]; simp⟩
  rw [h.coeff_dS]; simp [dsym]


/-! ## The average and the cohomological solver -/

/-- The average (zero Fourier coefficient). -/
def avg (x : FA) : ℂ := coeff x (0, 0)

/-- The average is bounded by any strip norm (`ρ ≥ 0`). -/
theorem Bd.norm_avg_le {ρ B : ℝ} {x : FA} (h : Bd ρ x B) (hρ : 0 ≤ ρ) : ‖avg x‖ ≤ B :=
  h.norm_coeff_le hρ _

/-- The average is additive. -/
@[simp] theorem avg_add (x y : FA) : avg (x + y) = avg x + avg y := coeff_add x y _

/-- The average of a difference. -/
@[simp] theorem avg_sub (x y : FA) : avg (x - y) = avg x - avg y := coeff_sub x y _

/-- The average of a negation. -/
@[simp] theorem avg_neg (x : FA) : avg (-x) = -avg x := coeff_neg x _

/-- The average commutes with scalars. -/
@[simp] theorem avg_smul (c : ℂ) (x : FA) : avg (c • x) = c * avg x := coeff_smul c x _

/-- The average of a constant. -/
@[simp] theorem avg_algebraMap (c : ℂ) : avg (algebraMap ℂ FA c) = c := by
  rw [avg, Algebra.algebraMap_eq_smul_one, coeff_smul, coeff_one]; simp [delta2]

/-- Sanity: `avg 1 = 1`. -/
@[simp] theorem avg_one : avg (1 : FA) = 1 := by rw [avg, coeff_one]; simp [delta2]

/-- **Derivatives have mean zero.** -/
@[simp] theorem avg_dS (a b : ℂ) (x : FA) : avg (dS a b x) = 0 := by
  unfold avg dS
  split_ifs with h
  · simp [dsym]
  · simp

/-- The zero-mean solution of `(∂_ψ + ω ∂_θ) u = x` (`0` if not summable). -/
def coh (ω : ℝ) (x : FA) : FA :=
  open Classical in
  if h : InWeighted 0 (cohSol ω (coeff x)) then ofCoeff _ h else 0

/-- The solver output has mean zero. -/
@[simp] theorem avg_coh (ω : ℝ) (x : FA) : avg (coh ω x) = 0 := by
  unfold avg coh
  split_ifs with h
  · simp
  · simp

/-- **Rüssmann estimate** on `𝔸`: `‖coh ω x‖_{ρ−δ} ≤ ‖x‖_ρ/(eγδ)` for `0 < δ ≤ ρ`,
`δ ≤ 2/e`, `ω` `(γ, 1)`-Diophantine. -/
theorem Bd.coh {ω γ ρ δ B : ℝ} {x : FA} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ) (hδ2 : δ ≤ 2 / Real.exp 1) (hx : Bd ρ x B) :
    Bd (ρ - δ) (KAM.coh ω x) (B / (Real.exp 1 * γ * δ)) := by
  obtain ⟨h1, h2⟩ := cohSol_estimate_one hD hγ hδ hδ2 hx.1
  have h0 : InWeighted 0 (cohSol ω (coeff x)) := h1.mono (by linarith)
  have hc : coeff (KAM.coh ω x) = cohSol ω (coeff x) := by
    funext n; simp [KAM.coh, h0]
  rw [Bd, hc]
  refine ⟨h1, h2.trans ?_⟩
  gcongr
  exact hx.2

/-- The solver output of an analytic element is analytic, with the expected coefficients. -/
theorem Ana.coh {ω γ : ℝ} {x : FA} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hx : Ana x) :
    Ana (KAM.coh ω x) ∧ coeff (KAM.coh ω x) = cohSol ω (coeff x) := by
  obtain ⟨ρ, B, hρ, h⟩ := hx
  set δ := min (ρ / 2) (2 / Real.exp 1)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδρ : δ ≤ ρ / 2 := min_le_left _ _
  have hb := h.coh hD hγ hδ (by linarith) (min_le_right _ _)
  have h0 : InWeighted 0 (cohSol ω (coeff x)) :=
    (cohSol_estimate_one hD hγ hδ (min_le_right _ _) h.1).1.mono (by linarith)
  exact ⟨⟨ρ - δ, _, by linarith, hb⟩, by funext n; simp [KAM.coh, h0]⟩

/-- **The solver solves the cohomological equation:** `(∂_ψ + ω ∂_θ) (coh ω x) = x` for analytic
zero-mean `x`. -/
theorem dS_coh {ω γ : ℝ} {x : FA} (hD : Diophantine ω γ 1) (hγ : 0 < γ) (hx : Ana x)
    (h0 : avg x = 0) : dS ω 1 (KAM.coh ω x) = x := by
  obtain ⟨ha, hc⟩ := hx.coh hD hγ
  refine ext_coeff fun n => ?_
  rw [ha.coeff_dS, hc]
  have := cohSol_spec hD hγ (f := coeff x) h0 n
  rw [← this, cohOp_eq]
  simp only [dsym, cohSol, divisor]
  push_cast; ring


/-! ## Reality -/

/-- Conjugate-reflected coefficients `n ↦ conj f(−n)` (the coefficients of the complex
conjugate function). -/
def cjFun (f : ℤ × ℤ → ℂ) (n : ℤ × ℤ) : ℂ := (starRingEnd ℂ) (f (-n))

/-- `modeSize (−n) = modeSize n`. -/
theorem modeSize_neg (n : ℤ × ℤ) : modeSize (-n) = modeSize n := by
  simp [modeSize, abs_neg]

/-- The weight is even. -/
theorem weight_neg (ρ : ℝ) (n : ℤ × ℤ) : weight ρ (-n) = weight ρ n := by
  simp [weight, modeSize_neg]

/-- Conjugate reflection preserves the weighted norm. -/
theorem inWeighted_cjFun {ρ : ℝ} {f : ℤ × ℤ → ℂ} (hf : InWeighted ρ f) :
    InWeighted ρ (cjFun f) ∧ wnorm ρ (cjFun f) = wnorm ρ f := by
  have e : (fun n => ‖cjFun f n‖ * weight ρ n) =
      (fun n => ‖f n‖ * weight ρ n) ∘ (Equiv.neg _) := by
    funext n; simp [cjFun, weight_neg]
  refine ⟨?_, ?_⟩
  · unfold InWeighted; rw [e]; exact (Equiv.summable_iff _).2 hf
  · unfold wnorm; rw [e]; exact (Equiv.neg (ℤ × ℤ)).tsum_eq (fun n => ‖f n‖ * weight ρ n)

/-- Complex conjugation of the represented function. -/
def cj (x : FA) : FA := ofCoeff (cjFun (coeff x)) (inWeighted_cjFun (inWeighted_coeff x)).1

/-- Coefficients of `cj x`. -/
@[simp] theorem coeff_cj (x : FA) (n : ℤ × ℤ) :
    coeff (cj x) n = (starRingEnd ℂ) (coeff x (-n)) := by
  simp [cj, cjFun]

/-- Convolution commutes with conjugate reflection. -/
theorem cconv_cjFun {f g : ℤ × ℤ → ℂ} :
    cconv (cjFun f) (cjFun g) = cjFun (cconv f g) := by
  funext n
  simp only [cconv, cjFun, Complex.conj_tsum, map_mul]
  rw [← (Equiv.neg (ℤ × ℤ)).tsum_eq]
  refine tsum_congr fun a => ?_
  simp only [Equiv.neg_apply, neg_neg]
  congr 3
  abel

/-- `cj` as a ring homomorphism. -/
def cjHom : FA →+* FA where
  toFun := cj
  map_one' := ext_coeff fun n => by
    rw [coeff_cj, coeff_one, coeff_one]
    by_cases h : n = 0
    · subst h; simp [delta2]
    · simp [delta2, h]
  map_mul' := fun x y => ext_coeff fun n => by
    rw [coeff_mul, coeff_cj, coeff_mul]
    have : cconv (coeff (cj x)) (coeff (cj y)) = cjFun (cconv (coeff x) (coeff y)) := by
      rw [← cconv_cjFun]; congr 1 <;> funext m <;> simp [cjFun]
    rw [this]; rfl
  map_zero' := ext_coeff fun n => by simp
  map_add' := fun x y => ext_coeff fun n => by simp

/-- `cj` is conjugate-linear. -/
theorem cj_smul (c : ℂ) (x : FA) : cj (c • x) = (starRingEnd ℂ) c • cj x :=
  ext_coeff fun n => by simp

/-- `x` represents a real-valued function: `x_{−n} = conj x_n`. -/
def IsReal (x : FA) : Prop := cj x = x

namespace IsReal

variable {x y : FA}

/-- Coefficient form of reality. -/
theorem coeff_neg (h : IsReal x) (n : ℤ × ℤ) :
    coeff x (-n) = (starRingEnd ℂ) (coeff x n) := by
  have := congrArg (fun z => coeff z (-n)) h
  simp only [coeff_cj, neg_neg] at this
  rw [← this]

/-- Reality from the coefficient form. -/
theorem of_coeff (h : ∀ n, coeff x (-n) = (starRingEnd ℂ) (coeff x n)) : IsReal x :=
  ext_coeff fun n => by
    rw [coeff_cj, h]; simp

/-- Sums. -/
theorem add (hx : IsReal x) (hy : IsReal y) : IsReal (x + y) := by
  unfold IsReal at *
  rw [show cj (x + y) = cjHom (x + y) from rfl, map_add]
  exact congrArg₂ (· + ·) hx hy

/-- Products. -/
theorem mul (hx : IsReal x) (hy : IsReal y) : IsReal (x * y) := by
  unfold IsReal at *
  rw [show cj (x * y) = cjHom (x * y) from rfl, map_mul]
  exact congrArg₂ (· * ·) hx hy

/-- Real scalar multiples. -/
theorem smul (hx : IsReal x) (c : ℝ) : IsReal ((c : ℂ) • x) := by
  unfold IsReal at *; rw [cj_smul, Complex.conj_ofReal, hx]

/-- Negation. -/
theorem neg (hx : IsReal x) : IsReal (-x) := by
  have := hx.smul (-1); simpa using this

/-- Differences. -/
theorem sub (hx : IsReal x) (hy : IsReal y) : IsReal (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- The unit. -/
theorem one : IsReal (1 : FA) := map_one cjHom

/-- Real constants. -/
theorem algebraMap (c : ℝ) : IsReal (algebraMap ℂ FA c) := by
  rw [Algebra.algebraMap_eq_smul_one]; exact one.smul c

/-- Powers. -/
theorem pow (hx : IsReal x) : ∀ n : ℕ, IsReal (x ^ n)
  | 0 => by simpa using one
  | n + 1 => by rw [pow_succ]; exact (pow hx n).mul hx

/-- Inverses of real units are real. -/
theorem inverse (hx : IsReal x) (hu : IsUnit x) : IsReal (Ring.inverse x) := by
  unfold IsReal at *
  have := map_ringInverse cjHom hu
  rw [show cjHom x = cj x from rfl, hx] at this
  exact this

/-- Real multipliers preserve reality. -/
theorem dS (hx : IsReal x) (a b : ℝ) : IsReal (KAM.dS a b x) := by
  unfold KAM.dS
  split_ifs with h
  · refine of_coeff fun n => ?_
    simp only [coeff_ofCoeff, dsym, hx.coeff_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_add, map_intCast, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    ring
  · exact map_zero cjHom

/-- The solver preserves reality (real `ω`). -/
theorem coh (hx : IsReal x) (ω : ℝ) : IsReal (KAM.coh ω x) := by
  unfold KAM.coh
  split_ifs with h
  · refine of_coeff fun n => ?_
    simp only [coeff_ofCoeff, cohSol, divisor, hx.coeff_neg, map_div₀, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    push_cast
    rw [show -(n.2 : ℂ) + -(n.1 : ℂ) * ω = -((n.2 : ℂ) + n.1 * ω) by ring]
    rw [mul_neg, div_neg, neg_mul, div_neg]
  · exact map_zero cjHom

/-- The average of a real element is real. -/
theorem conj_avg (hx : IsReal x) : (starRingEnd ℂ) (avg x) = avg x := by
  have := hx.coeff_neg (0, 0)
  simp only [Prod.neg_mk, neg_zero] at this
  exact this.symm

end IsReal

/-- Polynomial expressions with real constants. -/
def PolyExpr.RealConsts {σ : Type*} : PolyExpr ℂ σ → Prop
  | .const c => (starRingEnd ℂ) c = c
  | .var _ => True
  | .add p q => p.RealConsts ∧ q.RealConsts
  | .sub p q => p.RealConsts ∧ q.RealConsts
  | .mul p q => p.RealConsts ∧ q.RealConsts

/-- A polynomial expression with real constants maps real elements to real elements. -/
theorem IsReal.eval {σ : Type*} {z : σ → FA} (hz : ∀ i, IsReal (z i)) :
    ∀ e : PolyExpr ℂ σ, e.RealConsts → IsReal (PolyExpr.eval z e)
  | .const c, h => by
    have hc : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
      have := congrArg Complex.im h
      simp at this; linarith
    simp only [PolyExpr.eval]; rw [hc]; exact IsReal.algebraMap _
  | .var i, _ => hz i
  | .add p q, h => (IsReal.eval hz p h.1).add (IsReal.eval hz q h.2)
  | .sub p q, h => (IsReal.eval hz p h.1).sub (IsReal.eval hz q h.2)
  | .mul p q, h => (IsReal.eval hz p h.1).mul (IsReal.eval hz q h.2)

end PlasmaLean.Theory.KAM
