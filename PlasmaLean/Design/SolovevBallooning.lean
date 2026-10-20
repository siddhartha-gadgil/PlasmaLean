/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.BallooningReduction
public import PlasmaLean.Design.SolovevMercierCertified

/-!
# Ideal-ballooning stability of the reactor Solov'ev equilibrium on chosen flux surfaces

We prove, for the reactor Solov'ev equilibrium of `SolovevAlpha` (`A = 7/4 T`, `L = 10 m`,
`F = 50 T m`, `ψ̃ = R²z²/2 + (R² − L²)²/4`) and the flux surfaces `ψ̃ = s²`, `s = 1, 2, 3, 4`:

  `reactor_ballooning_s1 … s4 : ∀ c, (reactorLine … c).Stable`,

i.e. for EVERY eikonal family (shift `c`, equivalently every `θ_k`) the ballooning line
operator along the exact field line `SolovevMercier.lineS` has nonnegative energy
`∫ (P X'² + Q X²) dt` for every compactly supported `C¹` mode `X`, where `P, Q` are given by the
SUPPLIED ballooning reduction of `BallooningReduction` (`ballooningP`, `ballooningQ`;
Connor–Hastie–Taylor 1978, Dewar–Glasser 1983).

## What is computed from the actual equilibrium (proved)

* `reactorLine`: line element `ℓ = |λ|` of the exact field line (`lnEll_eq_abs_lam`), the actual
  field `B` (`B_line`), the actual `μ₀∇p` (`lnGp_eq_pressure`), the actual curvature
  `b·∇b` computed from the actual field derivative `fieldDeriv` (`DBB_line`), and the
  covering-space eikonal gradient `k = k₀ − (σ(t) − c) ∇√ψ̃` (with `B · k = 0`,
  `lnB_inner_lnEik`), where `∇√ψ̃` is the actual
  gradient (`psiTGrad_line`), `k₀ = ∇φ − ∂ₜΦ ∇t` (`lnK0_eq`, `hasDerivAt_phiS`), `∇√ψ̃, ∇t` are the
  dual basis of the meridian coordinates (`meridian_dual`, with the derivatives of
  `jacobian_eq`) and `σ' = ∂ₛ∂ₜΦ = 3 rate sin t/R⁵` (`hasDerivAt_lnSig`, `lnD_eq_mixed`).
* `P_geom`, `Q_geom`: along the line, exactly `P = p₀ + σ p₁ + σ² p₂`, `Q = q₀ + σ q₁`, with
  explicit coefficient trees in `(cos t, sin t, R, √2, 1/R, 1/|B|²)`.
* Two exact identities (`Bk0gp_eq`: `B × k₀ · μ₀∇p = 3c|B|²`; `B2_deriv_eq`) give
  `hasDerivAt_a`: the secular (geodesic-curvature) drive is an exact derivative,
  `q₁ = d/dt a` with `a = a₀ − (75/s)/|B|²`. This is the structure behind the averaged
  (Mercier) tail and is what makes a global certificate possible.

## The certificate (two-variable Riccati, uniform in `θ_k`)

`BallooningReduction.riccati2D_energy_nonneg` reduces stability of all lines/`θ_k` to one
inequality on the `(t, σ)` plane: `∂ₜF + d ∂_σF + F²/P ≤ Q`. We take

  `F = σ a(t) + f₀(t) + f₁(t) w²/(w² + σ²) + f₂(t) wσ/(w² + σ²)`,

`f₀ = x A₀(y)`, `f₁ = x A₁(y)`, `f₂ = A₂(y)` quadratics in `y = sin t` (`x = cos t`), with
rational data `Cert` proposed by an UNTRUSTED oracle (a convex SOCP maximizing the margin of
the inequality on a grid, rounded to multiples of `2⁻¹⁶`; numerical margin `≈ 7·10⁻⁴`).
The defect equals `N(t, σ)/(P W²)` with `N = Σ_{k ≤ 6} eₖ(t) σᵏ` (`Npoly_eq`,
`riccati_of_N`). Positivity of `N` is checked rigorously:

* the half circle `x ≥ 0` is parametrized by `τ ∈ [−1, 1]` (`xc`, `wy`), cut into `n = 128`
  cells; on each cell the coefficients `eₖ` are enclosed by a mean-value form: value at the
  centre plus `[−2/n, 2/n]` times the derivative over the cell, both by outward-rounded
  fixed-point interval arithmetic (`FIv`) on expression trees (`Tm`, forward-mode derivative
  `Tm.idual`; soundness `Tm.ieval_mem`, `Tm.idual_mem`, `mem_mvt`);
* positivity in `σ ∈ ℝ` is then a Pólya test on the integer lower coefficient lists for
  `σ ≥ 0` and `σ ≤ 0` (`polyaOK`, `Npoly_pos_of_bounds`); `cellOK_sound`, `allOK_sound`;
* the half `x < 0` follows from up–down symmetry (`baseT_negx`, `Npoly_negx`);
* every cell is kernel-checked (`decide +kernel`, eight chunks per surface: `cert1_cells` …).

`noProfile_rejected`: without the oscillating profiles the outboard cell fails (the shearless
periodic problem is not stable by itself; the stabilization comes from the coupling to the
local shear through `d ∂_σF`).

## Scope and trust

* The ballooning reduction (high-`n` eikonal `δW` ↦ line energy, and "all lines and `θ_k`
  stable ⇒ ideal ballooning stable") is the SUPPLIED interface of `BallooningReduction`; the
  curvature enters only through `B × k · κ`, so only its normal part matters
  (`inner_cross_curvature`). `σ = ∂ₛΦ + const` uses the standard commutation of `∂ₛ` with
  `∫ dt`; since all shifts `c` are covered, the constant is irrelevant.
* Only the surfaces `s = 1, 2, 3, 4` (`ψ̃ ≤ 16` of the plasma `ψ̃ ≤ 625`, the near-axis
  region) are certified. The checks are fully rigorous (standard axioms only); the oracle is
  not part of the trusted base.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set PlasmaLean.Fields PlasmaLean.Certificates.ValidatedQuadrature
open PlasmaLean.Stability.BallooningInfinite PlasmaLean.Stability.BallooningReduction
open PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevMercier PlasmaLean.Design.SolovevAlpha
open scoped RealInnerProductSpace

/-! ## Expression trees with real, derivative and interval semantics -/

/-- Polynomial expression trees over numbered real variables, with rational constants `p/q`.
(Reciprocals such as `1/R` are passed in as separate variables.) -/
inductive Tm where
  /-- The constant `p / q`. -/
  | c (p q : ℤ)
  /-- Variable number `i`. -/
  | v (i : ℕ)
  /-- Sum. -/
  | add (a b : Tm)
  /-- Product. -/
  | mul (a b : Tm)
  /-- Negation. -/
  | neg (a : Tm)

namespace Tm

/-- Real value of a tree at the variable assignment `ρ`. -/
@[expose] def eval (ρ : ℕ → ℝ) : Tm → ℝ
  | c p q => (p : ℝ) / q
  | v i => ρ i
  | add a b => a.eval ρ + b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ
  | neg a => -(a.eval ρ)

/-- Forward-mode derivative of a tree, given the derivatives `ρ'` of the variables. -/
@[expose] def deriv (ρ ρ' : ℕ → ℝ) : Tm → ℝ
  | c _ _ => 0
  | v i => ρ' i
  | add a b => a.deriv ρ ρ' + b.deriv ρ ρ'
  | mul a b => a.deriv ρ ρ' * b.eval ρ + a.eval ρ * b.deriv ρ ρ'
  | neg a => -(a.deriv ρ ρ')

/-- **Chain rule for trees.** If every variable is differentiable along `t`, so is the
value of the tree, with derivative `deriv`. -/
theorem hasDerivAt (e : Tm) {ρ ρ' : ℝ → ℕ → ℝ} {t : ℝ}
    (hρ : ∀ i, HasDerivAt (fun t => ρ t i) (ρ' t i) t) :
    HasDerivAt (fun t => e.eval (ρ t)) (e.deriv (ρ t) (ρ' t)) t := by
  induction e with
  | c p q => simpa [eval, deriv] using hasDerivAt_const t ((p : ℝ) / q)
  | v i => simpa [eval, deriv] using hρ i
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb
  | neg a iha => exact iha.neg

/-- The derivative is linear in the variable derivatives. -/
theorem deriv_smul (e : Tm) (ρ ρ' : ℕ → ℝ) (κ : ℝ) :
    e.deriv ρ (fun i => κ * ρ' i) = κ * e.deriv ρ ρ' := by
  induction e with
  | c p q => simp [deriv]
  | v i => simp [deriv]
  | add a b iha ihb => simp only [deriv, iha, ihb]; ring
  | mul a b iha ihb => simp only [deriv, iha, ihb]; ring
  | neg a iha => simp only [deriv, iha]; ring

/-- Continuity of a tree along continuous variables. -/
theorem continuous_eval (e : Tm) {ρ : ℝ → ℕ → ℝ} (hρ : ∀ i, Continuous fun t => ρ t i) :
    Continuous fun t => e.eval (ρ t) := by
  induction e with
  | c p q => exact continuous_const
  | v i => exact hρ i
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb
  | neg a iha => exact iha.neg

/-- The zero enclosure. -/
@[expose] def zeroIv : FIv := ⟨0, 0, true⟩

/-- `zeroIv` encloses `0`. -/
theorem mem_zeroIv : zeroIv.Mem 0 := by
  intro _; simp [zeroIv, fxVal]

/-- Interval value of a tree. -/
@[expose] def ieval (I : ℕ → FIv) : Tm → FIv
  | c p q => FIv.ofFrac p q
  | v i => I i
  | add a b => (a.ieval I).add (b.ieval I)
  | mul a b => (a.ieval I).mul (b.ieval I)
  | neg a => (a.ieval I).neg

/-- Dual-number sum. -/
@[expose] def dAdd (A B : FIv × FIv) : FIv × FIv := (A.1.add B.1, A.2.add B.2)
/-- Dual-number product. -/
@[expose] def dMul (A B : FIv × FIv) : FIv × FIv :=
  (A.1.mul B.1, (A.2.mul B.1).add (A.1.mul B.2))
/-- Dual-number negation. -/
@[expose] def dNeg (A : FIv × FIv) : FIv × FIv := (A.1.neg, A.2.neg)

/-- Interval value and derivative of a tree (forward mode). -/
@[expose] def idual (I I' : ℕ → FIv) : Tm → FIv × FIv
  | c p q => (FIv.ofFrac p q, zeroIv)
  | v i => (I i, I' i)
  | add a b => dAdd (a.idual I I') (b.idual I I')
  | mul a b => dMul (a.idual I I') (b.idual I I')
  | neg a => dNeg (a.idual I I')

/-- **Soundness of interval evaluation.** -/
theorem ieval_mem (e : Tm) {I : ℕ → FIv} {ρ : ℕ → ℝ} (hI : ∀ i, (I i).Mem (ρ i)) :
    (e.ieval I).Mem (e.eval ρ) := by
  induction e with
  | c p q => exact FIv.mem_ofFrac p q
  | v i => exact hI i
  | add a b iha ihb => exact FIv.mem_add iha ihb
  | mul a b iha ihb => exact FIv.mem_mul iha ihb
  | neg a iha => exact FIv.mem_neg iha

/-- **Soundness of dual evaluation**: value and derivative enclosures. -/
theorem idual_mem (e : Tm) {I I' : ℕ → FIv} {ρ ρ' : ℕ → ℝ} (hI : ∀ i, (I i).Mem (ρ i))
    (hI' : ∀ i, (I' i).Mem (ρ' i)) :
    (e.idual I I').1.Mem (e.eval ρ) ∧ (e.idual I I').2.Mem (e.deriv ρ ρ') := by
  induction e with
  | c p q => exact ⟨FIv.mem_ofFrac p q, mem_zeroIv⟩
  | v i => exact ⟨hI i, hI' i⟩
  | add a b iha ihb => exact ⟨FIv.mem_add iha.1 ihb.1, FIv.mem_add iha.2 ihb.2⟩
  | mul a b iha ihb =>
    exact ⟨FIv.mem_mul iha.1 ihb.1,
      FIv.mem_add (FIv.mem_mul iha.2 ihb.1) (FIv.mem_mul iha.1 ihb.2)⟩
  | neg a iha => exact ⟨FIv.mem_neg iha.1, FIv.mem_neg iha.2⟩

/-- Symbolic derivative tree, given derivative trees `dv i` of the variables. -/
@[expose] def diff (dv : ℕ → Tm) : Tm → Tm
  | c _ _ => c 0 1
  | v i => dv i
  | add a b => add (diff dv a) (diff dv b)
  | mul a b => add (mul (diff dv a) b) (mul a (diff dv b))
  | neg a => neg (diff dv a)

/-- The symbolic derivative evaluates to the forward derivative. -/
theorem eval_diff (dv : ℕ → Tm) (e : Tm) (ρ : ℕ → ℝ) :
    (diff dv e).eval ρ = e.deriv ρ (fun i => (dv i).eval ρ) := by
  induction e with
  | c p q => simp [diff, eval, deriv]
  | v i => simp [diff, deriv]
  | add a b iha ihb => simp only [diff, eval, deriv, iha, ihb]
  | mul a b iha ihb => simp only [diff, eval, deriv, iha, ihb]
  | neg a iha => simp only [diff, eval, deriv, iha]

end Tm

/-! ## Integer polynomials and the Pólya positivity test -/

/-- Value of the integer polynomial `Σ cₖ uᵏ` (coefficients from degree `0`). -/
@[expose] def zpoly : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, u => (a : ℝ) + u * zpoly p u

/-- Multiplication by `1 + u`. -/
@[expose] def mulOnePlus : List ℤ → List ℤ
  | [] => []
  | a :: p => a :: addShift a p
where
  /-- Helper: `(a :: p) ↦ coefficients of p + u·(a :: p)` shifted. -/
  addShift : ℤ → List ℤ → List ℤ
  | b, [] => [b]
  | b, c :: q => (c + b) :: addShift c q

/-- Value of the shifted sum used by `mulOnePlus`. -/
theorem zpoly_addShift (b : ℤ) (p : List ℤ) (u : ℝ) :
    zpoly (mulOnePlus.addShift b p) u = zpoly p u + b + u * zpoly p u := by
  induction p generalizing b with
  | nil => simp [mulOnePlus.addShift, zpoly]
  | cons c q ih => simp only [mulOnePlus.addShift, zpoly, ih]; push_cast; ring

/-- `mulOnePlus` multiplies the polynomial by `1 + u`. -/
theorem zpoly_mulOnePlus (p : List ℤ) (u : ℝ) : zpoly (mulOnePlus p) u = (1 + u) * zpoly p u := by
  cases p with
  | nil => simp [mulOnePlus, zpoly]
  | cons a q => simp only [mulOnePlus, zpoly, zpoly_addShift]; ring

/-- All coefficients are positive (and the list is nonempty). -/
@[expose] def allPos : List ℤ → Bool
  | [] => false
  | [a] => decide (0 < a)
  | a :: b :: p => decide (0 < a) && allPos (b :: p)

/-- A polynomial with positive coefficients is positive on `[0, ∞)`. -/
theorem zpoly_pos_of_allPos {p : List ℤ} (hp : allPos p = true) {u : ℝ} (hu : 0 ≤ u) :
    0 < zpoly p u := by
  induction p with
  | nil => simp [allPos] at hp
  | cons a q ih =>
    cases q with
    | nil =>
      simp only [allPos, decide_eq_true_eq] at hp
      simp only [zpoly, mul_zero, add_zero]; exact_mod_cast hp
    | cons b r =>
      simp only [allPos, Bool.and_eq_true, decide_eq_true_eq] at hp
      have h1 : (0 : ℝ) < a := by exact_mod_cast hp.1
      have h2 := ih hp.2
      simp only [zpoly] at h2 ⊢
      nlinarith

/-- **Pólya test**: some `(1 + u)ᵐ p` (`m ≤ M`) has positive coefficients. -/
@[expose] def polyaOK : ℕ → List ℤ → Bool
  | 0, p => allPos p
  | M + 1, p => allPos p || polyaOK M (mulOnePlus p)

/-- The Pólya test proves positivity on `[0, ∞)`. -/
theorem zpoly_pos_of_polyaOK {M : ℕ} {p : List ℤ} (h : polyaOK M p = true) {u : ℝ}
    (hu : 0 ≤ u) : 0 < zpoly p u := by
  induction M generalizing p with
  | zero => exact zpoly_pos_of_allPos h hu
  | succ M ih =>
    simp only [polyaOK, Bool.or_eq_true] at h
    rcases h with h | h
    · exact zpoly_pos_of_allPos h hu
    · have := ih h
      rw [zpoly_mulOnePlus] at this
      have h1 : 0 < 1 + u := by linarith
      exact pos_of_mul_pos_right this h1.le

/-! ## Cylindrical vectors -/

/-- The vector with cylindrical components `(a, b, c)` (radial, toroidal, vertical) at
toroidal angle `φ`. -/
@[expose] def cyl (φ a b c : ℝ) : Space :=
  WithLp.toLp 2 ![a * Real.cos φ - b * Real.sin φ, a * Real.sin φ + b * Real.cos φ, c]

/-- Inner product in cylindrical components. -/
theorem inner_cyl (φ a b c a' b' c' : ℝ) :
    ⟪cyl φ a b c, cyl φ a' b' c'⟫ = a * a' + b * b' + c * c' := by
  simp only [cyl, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (a * a' + b * b') * Real.sin_sq_add_cos_sq φ

/-- Squared norm in cylindrical components. -/
theorem norm_sq_cyl (φ a b c : ℝ) : ‖cyl φ a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cyl]; ring

/-- Cross product in cylindrical components (right-handed frame `e_R, e_φ, e_z`). -/
theorem cross_cyl (φ a b c a' b' c' : ℝ) :
    cross (cyl φ a b c) (cyl φ a' b' c') =
      cyl φ (b * c' - c * b') (c * a' - a * c') (a * b' - b * a') := by
  apply space_ext <;> simp [cross, cross_apply, cyl]
  · ring
  · ring
  · linear_combination (a * b' - b * a') * Real.sin_sq_add_cos_sq φ

/-- Difference of cylindrical vectors. -/
theorem cyl_sub (φ a b c a' b' c' : ℝ) :
    cyl φ a b c - cyl φ a' b' c' = cyl φ (a - a') (b - b') (c - c') := by
  apply space_ext <;> simp [cyl] <;> ring

/-- Scalar multiple of a cylindrical vector. -/
theorem smul_cyl (φ k a b c : ℝ) : k • cyl φ a b c = cyl φ (k * a) (k * b) (k * c) := by
  apply space_ext <;> simp [cyl] <;> ring

/-- A cylindrical vector with nonzero toroidal component is nonzero. -/
theorem cyl_ne_zero {φ a b c : ℝ} (hb : b ≠ 0) : cyl φ a b c ≠ 0 := by
  intro h
  have := congrArg (fun v => ‖v‖ ^ 2) h
  simp only [norm_sq_cyl, norm_zero] at this
  have : 0 < b ^ 2 := by positivity
  nlinarith [sq_nonneg a, sq_nonneg c]

/-- Continuity of a cylindrical vector field along continuous components. -/
theorem continuous_cyl {φ a b c : ℝ → ℝ} (hφ : Continuous φ) (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) : Continuous fun t => cyl (φ t) (a t) (b t) (c t) := by
  unfold cyl
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop

/-! ## Variables along the line and the coefficient trees

Variables: `0 ↦ x = cos t`, `1 ↦ y = sin t`, `2 ↦ R = R(t)`, `3 ↦ r = √2`, `4 ↦ 1/R`,
`5 ↦ 1/|B|²`. All trees use the
reactor constants `A = 7/4`, `L = 10`, `F = 50` (`c = A/L² = 7/400`). -/

/-- An assignment of the six variables `(x, y, R, r, 1/R, 1/|B|²)`. -/
@[expose] def envOf (x y R r iR iB : ℝ) : ℕ → ℝ
  | 0 => x
  | 1 => y
  | 2 => R
  | 3 => r
  | 4 => iR
  | _ => iB

namespace Tm
/-- Difference. -/
@[expose] def sub (a b : Tm) : Tm := add a (neg b)
/-- Square. -/
@[expose] def sq (a : Tm) : Tm := mul a a
end Tm

open Tm

/-- `x = cos t`. -/ @[expose] def tX : Tm := v 0
/-- `y = sin t`. -/ @[expose] def tY : Tm := v 1
/-- `R`. -/ @[expose] def tR : Tm := v 2
/-- `r = √2`. -/ @[expose] def tr : Tm := v 3
/-- `1/R`. -/ @[expose] def tiR : Tm := v 4
/-- `1/|B|²`. -/ @[expose] def tiB2 : Tm := v 5

section trees
variable (s : ℕ)
/-- Height `z = √2 s x / R`. -/
@[expose] def tz : Tm := mul (mul tr (c s 1)) (mul tX tiR)
/-- `W = z² + R² − L²`. -/
@[expose] def tW : Tm := add (add (sq (tz s)) (sq tR)) (c (-100) 1)
/-- Radial field `B_R = −c R z`. -/
@[expose] def tBR : Tm := neg (mul (c 7 400) (mul tR (tz s)))
/-- Toroidal field `B_φ = F/R`. -/
@[expose] def tBP : Tm := mul (c 50 1) tiR
/-- Vertical field `B_z = c W`. -/
@[expose] def tBZ : Tm := mul (c 7 400) (tW s)
/-- `(∇√ψ̃)_R = R W/(2s)`. -/
@[expose] def tgsR : Tm := mul (c 1 (2 * s)) (mul tR (tW s))
/-- `(∇√ψ̃)_z = R² z/(2s)`. -/
@[expose] def tgsZ : Tm := mul (c 1 (2 * s)) (mul (sq tR) (tz s))
/-- `(∇t)_R = x (L² + s y)/(s R)`. -/
@[expose] def tgtR : Tm := mul (c 1 s) (mul (mul tX (add (c 100 1) (mul (c s 1) tY))) tiR)
/-- `(∇t)_z = −R y/(√2 s)`. -/
@[expose] def tgtZ : Tm := neg (mul (c 1 (2 * s)) (mul (mul tR tY) tr))
/-- Winding rate `F L²/(√2 A) = 10000 √2/7`. -/
@[expose] def trate : Tm := mul (c 10000 7) tr
/-- `∂ₜΦ = −rate/R³`. -/
@[expose] def tPhit : Tm := neg (mul trate (mul tiR (sq tiR)))
/-- `k₀ = ∇φ − ∂ₜΦ ∇t`, radial. -/
@[expose] def tkR : Tm := neg (mul tPhit (tgtR s))
/-- `k₀`, toroidal (`1/R`). -/
@[expose] def tkP : Tm := tiR
/-- `k₀`, vertical. -/
@[expose] def tkZ : Tm := neg (mul tPhit (tgtZ s))
/-- `ℓ = |λ| = 200 √2/(7 R)`. -/
@[expose] def tell : Tm := mul (c 200 7) (mul tr tiR)
/-- `μ₀ ∂_R p = −3 c² R W`. -/
@[expose] def tgpR : Tm := mul (c (-147) 160000) (mul tR (tW s))
/-- `μ₀ ∂_z p = −3 c² R² z`. -/
@[expose] def tgpZ : Tm := mul (c (-147) 160000) (mul (sq tR) (tz s))
/-- `(DB · B)_R = c² R z² − F²/R³ − c² R W`. -/
@[expose] def tGR : Tm :=
  sub (sub (mul (c 49 160000) (mul tR (sq (tz s)))) (mul (c 2500 1) (mul tiR (sq tiR))))
    (mul (c 49 160000) (mul tR (tW s)))
/-- `(DB · B)_z = 2 c² z (W − R²)`. -/
@[expose] def tGZ : Tm := mul (c 49 80000) (mul (tz s) (sub (tW s) (sq tR)))
/-- `|B|²`. -/
@[expose] def tB2 : Tm := add (add (sq (tBR s)) (sq tBP)) (sq (tBZ s))
/-- `1/(ℓ |B|²) = 7 √2 R/(400 |B|²)`. -/
@[expose] def tden : Tm := mul (c 7 400) (mul (mul tr tR) tiB2)
/-- `p₀ = |k₀|²/(ℓ|B|²)`. -/
@[expose] def tp0 : Tm := mul (add (add (sq (tkR s)) (sq tkP)) (sq (tkZ s))) tden
/-- `p₁ = −2 k₀·∇√ψ̃/(ℓ|B|²)`. -/
@[expose] def tp1 : Tm :=
  mul (mul (c (-2) 1) (add (mul (tkR s) (tgsR s)) (mul (tkZ s) (tgsZ s)))) tden
/-- `p₂ = |∇√ψ̃|²/(ℓ|B|²)`. -/
@[expose] def tp2 : Tm := mul (add (sq (tgsR s)) (sq (tgsZ s))) tden
/-- `(B × b)·g` for `b = (bR, bP, bZ)` and a meridional `g = (gR, 0, gZ)`. -/
@[expose] def tcrossDot (bR bP bZ gR gZ : Tm) : Tm :=
  add (mul (sub (mul tBP bZ) (mul (tBZ s) bP)) gR) (mul (sub (mul (tBR s) bP) (mul tBP bR)) gZ)
/-- `B × k₀ · μ₀∇p`. -/
@[expose] def tBk0gp : Tm := tcrossDot s (tkR s) tkP (tkZ s) (tgpR s) (tgpZ s)
/-- `B × k₀ · (DB B)`. -/
@[expose] def tBk0G : Tm := tcrossDot s (tkR s) tkP (tkZ s) (tGR s) (tGZ s)
/-- `B × ∇√ψ̃ · (DB B)`. -/
@[expose] def tBgsG : Tm := tcrossDot s (tgsR s) (c 0 1) (tgsZ s) (tGR s) (tGZ s)
/-- `q₀ = −2ℓ (B×k₀·μ₀∇p)(B×k₀·DB B)/|B|⁶`. -/
@[expose] def tq0 : Tm :=
  neg (mul (mul (mul (c 2 1) tell) (mul (tBk0gp s) (tBk0G s))) (mul tiB2 (sq tiB2)))
/-- `q₁ = 2ℓ (B×k₀·μ₀∇p)(B×∇√ψ̃·DB B)/|B|⁶`. -/
@[expose] def tq1 : Tm :=
  mul (mul (mul (c 2 1) tell) (mul (tBk0gp s) (tBgsG s))) (mul tiB2 (sq tiB2))
end trees

/-- Secular rate `d = ∂ₛ∂ₜΦ = 3 rate y/R⁵`. -/
@[expose] def td : Tm := mul (mul (mul (c 3 1) trate) tY) (mul tiR (sq (sq tiR)))

/-- The variables along the line with the `1/|B|²` slot set to `0`. -/
@[expose] def env0 (s : ℕ) (t : ℝ) : ℕ → ℝ :=
  envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0

/-- `|B|²` along the line (the tree `tB2` does not use the slot `5`). -/
@[expose] def B2v (s : ℕ) (t : ℝ) : ℝ := (tB2 s).eval (env0 s t)

/-- The variables along the field line on the surface `ψ̃ = s²`:
`(cos t, sin t, R(t), √2, 1/R(t), 1/|B|²)`. -/
@[expose] def env (s : ℕ) (t : ℝ) : ℕ → ℝ :=
  envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ (B2v s t)⁻¹

/-! ## The field-line geometry of the reactor surface `ψ̃ = s²` -/

/-- `R > 0` on the reactor surfaces `s ≤ 25`. -/
theorem RS_pos_nat {s : ℕ} (hs : s ≤ 25) (t : ℝ) : 0 < RS 10 s t :=
  RS_pos (by positivity) (by norm_num; exact_mod_cast (by omega : 2 * s < 100)) t

/-- `R² = x₀² + x₁²` along the field line. -/
theorem R2_line (s : ℕ) (t : ℝ) : R2 (lineS (7 / 4) 10 50 s t) = RS 10 s t ^ 2 := by
  simp only [R2, lineS, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination RS 10 s t ^ 2 * Real.sin_sq_add_cos_sq (phiS (7 / 4) 10 50 s t)

/-- **The actual field along the line** in cylindrical components:
`B = (−c R z, F/R, c W)` at toroidal angle `φ(t)`. -/
theorem B_line {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    reactorField (lineS (7 / 4) 10 50 s t) = cyl (phiS (7 / 4) 10 50 s t)
      ((tBR s).eval (env s t)) (tBP.eval (env s t)) ((tBZ s).eval (env s t)) := by
  have hR := RS_pos_nat hs t
  have h2 := R2_line s t
  apply space_ext
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBR, tBP, tz, tX, tR, tr, tiR, zS]
    field_simp
    ring
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBR, tBP, tz, tX, tR, tr, tiR, zS]
    field_simp
    ring
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBZ, tW, tz, tX, tR, tr, tiR, zS, Tm.sq]
    ring

/-- Coordinates of the field derivative applied to a vector. -/
theorem fieldDeriv_coord (A L F : ℝ) (x w : Space) (j : Fin 3) :
    fieldDeriv A L F x w j =
      jac A L F x j 0 * w 0 + jac A L F x j 1 * w 1 + jac A L F x j 2 * w 2 := by
  rw [fieldDeriv, PlasmaLean.Fields.coords_apply]
  simp [row, Fin.sum_univ_three]

/-- **The derivative of the actual field along itself**, `(DB) B`, along the line:
`(c² R z² − F²/R³ − c² R W, 0, 2 c² z (W − R²))`. -/
theorem DBB_line {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (reactorField (lineS (7 / 4) 10 50 s t)) =
      cyl (phiS (7 / 4) 10 50 s t) ((tGR s).eval (env s t)) 0 ((tGZ s).eval (env s t)) := by
  have hR := RS_pos_nat hs t
  have h2 := R2_line s t
  have hc := Real.sin_sq_add_cos_sq (phiS (7 / 4) 10 50 s t)
  rw [B_line hs t]
  apply space_ext
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBR, tBP, tBZ, tW, tGR, tz, tX, tR, tr, tiR, zS,
      Tm.sq, Tm.sub]
    field_simp
    linear_combination (-((√2 * (s:ℝ) * Real.cos t * RS 10 (↑s) t * 22400000000) *
      Real.sin (phiS (7 / 4) 10 50 (↑s) t) +
      (64000000000000:ℝ) * Real.cos (phiS (7 / 4) 10 50 (↑s) t))) * hc
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBR, tBP, tBZ, tW, tGR, tz, tX, tR, tr, tiR, zS,
      Tm.sq, Tm.sub]
    field_simp
    linear_combination ((√2 * (s:ℝ) * Real.cos t * RS 10 (↑s) t * 22400000000) *
      Real.cos (phiS (7 / 4) 10 50 (↑s) t) -
      (64000000000000:ℝ) * Real.sin (phiS (7 / 4) 10 50 (↑s) t)) * hc
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tBR, tBP, tBZ, tW, tGZ, tz, tX, tR, tr, tiR, zS,
      Tm.sq, Tm.sub]
    field_simp
    linear_combination (-(RS 10 (↑s) t ^ 4 * √2 * (s:ℝ) * Real.cos t * 7840000)) * hc

/-- The actual gradient of `ψ̃` along the line is `2s ∇√ψ̃` with
`∇√ψ̃ = (R W/(2s), 0, R² z/(2s))`. -/
theorem psiTGrad_line {s : ℕ} (hs1 : 1 ≤ s) (t : ℝ) :
    psiTGrad 10 (lineS (7 / 4) 10 50 s t) = (2 * (s:ℝ)) •
      cyl (phiS (7 / 4) 10 50 s t) ((tgsR s).eval (env s t)) 0 ((tgsZ s).eval (env s t)) := by
  have h2 := R2_line s t
  have hs : (s:ℝ) ≠ 0 := by positivity
  rw [smul_cyl]
  apply space_ext
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tgsR, tW, tz, tX, tR, tr, tiR, zS, Tm.sq]
    field_simp
    ring
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tgsR, tW, tz, tX, tR, tr, tiR, zS, Tm.sq]
    field_simp
    ring
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tgsZ, tz, tX, tR, tr, tiR, zS, Tm.sq]
    field_simp

/-- The actual `∇φ` along the line is `(0, 1/R, 0)`. -/
theorem phiGrad_line {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    phiGrad (lineS (7 / 4) 10 50 s t) = cyl (phiS (7 / 4) 10 50 s t) 0 (tkP.eval (env s t)) 0 := by
  have hR := RS_pos_nat hs t
  have h2 := R2_line s t
  apply space_ext
  · simp only [phiGrad, PiLp.smul_apply, smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tkP, tiR]
    field_simp
  · simp only [phiGrad, PiLp.smul_apply, smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, env, envOf, tkP, tiR]
    field_simp
  · simp [phiGrad, cyl]

/-! ## Two exact identities (geodesic-curvature structure) -/

/-- `B × k₀ · μ₀∇p = 3 c |B|²`, `c = 7/400` (for any point of the surface relations
`x² + y² = 1`, `R² = L² + 2 s y`, `r² = 2`). -/
theorem Bk0gp_eq (s : ℕ) {x y R r : ℝ} (iB : ℝ) (hx : x ^ 2 + y ^ 2 = 1)
    (hR : R ^ 2 = 100 + 2 * s * y) (hr : r ^ 2 = 2) (hRne : R ≠ 0) (hs : (s : ℝ) ≠ 0) :
    (tBk0gp s).eval (envOf x y R r R⁻¹ iB) =
      3 * (7 / 400) * (tB2 s).eval (envOf x y R r R⁻¹ iB) := by
  simp [Tm.eval, envOf, tBk0gp, tcrossDot, tB2, tBR, tBP, tBZ, tkR, tkP, tkZ, tgpR, tgpZ, tPhit,
    trate, tgtR, tgtZ, tz, tW, tX, tY, tR, tr, tiR, Tm.sq, Tm.sub]
  field_simp
  linear_combination (4704000000000000*r^4*(s:ℝ)^2*y + 9408000000000000*r^2*(s:ℝ)^2*y
    + 940800000000000000*r^2*(s:ℝ)) * hx + (4704000000000000*R^2*r^2*y
    + 9408000000000000*r^2*(s:ℝ)*y^2 - 18816000000000000*(s:ℝ)) * hR
    + (-4704000000000000*r^2*(s:ℝ)^2*y^3 + 4704000000000000*r^2*(s:ℝ)^2*y
    + 18816000000000000*(s:ℝ)^2*y + 940800000000000000*(s:ℝ)) * hr

/-- `(75/s) ∂ₜ|B|² = 6 c ℓ (B × ∇√ψ̃ · DB B)`: the secular drive is an exact `t`-derivative. -/
theorem B2_deriv_eq (s : ℕ) {x y R r : ℝ} (iB diB : ℝ) (hx : x ^ 2 + y ^ 2 = 1)
    (hR : R ^ 2 = 100 + 2 * s * y) (hr : r ^ 2 = 2) (hRne : R ≠ 0) (hs : (s : ℝ) ≠ 0) :
    75 / (s:ℝ) * (tB2 s).deriv (envOf x y R r R⁻¹ iB)
        (envOf (-y) x (s * x * R⁻¹) 0 (-(s * x * R⁻¹) * R⁻¹ * R⁻¹) diB) =
      6 * (7 / 400) * tell.eval (envOf x y R r R⁻¹ iB) * (tBgsG s).eval (envOf x y R r R⁻¹ iB) := by
  simp [Tm.eval, Tm.deriv, envOf, tBgsG, tcrossDot, tB2, tBR, tBP, tBZ, tgsR, tgsZ, tGR,
    tGZ, tell, tz, tW, tX, tR, tr, tiR, Tm.sq, Tm.sub]
  field_simp
  linear_combination (188160000000000*R^4*r^4*(s:ℝ)^2*x - 376320000000000*R^2*r^4*(s:ℝ)^3*x*y
    - 37632000000000000*R^2*r^4*(s:ℝ)^2*x + 37632000000000000*R^2*r^2*(s:ℝ)^2*x
    + 188160000000000*r^6*(s:ℝ)^4*x^3 - 188160000000000*r^6*(s:ℝ)^4*x*y^2
    + 188160000000000*r^6*(s:ℝ)^4*x - 376320000000000*r^4*(s:ℝ)^4*x^3
    + 376320000000000*r^4*(s:ℝ)^4*x*y^2 - 376320000000000*r^4*(s:ℝ)^4*x) * hx
    + (94080000000000*R^6*r^2*x + 376320000000000*R^6*x - 376320000000000*R^4*r^2*(s:ℝ)*x*y
    - 18816000000000000*R^4*r^2*x + 752640000000000*R^4*(s:ℝ)*x*y
    - 188160000000000*R^2*r^4*(s:ℝ)^2*x*y^2 + 188160000000000*R^2*r^4*(s:ℝ)^2*x
    - 752640000000000*R^2*r^2*(s:ℝ)^2*x*y^2 - 37632000000000000*R^2*r^2*(s:ℝ)*x*y
    + 1505280000000000*R^2*(s:ℝ)^2*x*y^2 + 75264000000000000*R^2*(s:ℝ)*x*y
    + 18816000000000000*r^4*(s:ℝ)^2*x*y^2 - 18816000000000000*r^4*(s:ℝ)^2*x
    - 1505280000000000*r^2*(s:ℝ)^3*x*y^3 - 188160000000000000*r^2*(s:ℝ)^2*x*y^2
    + 37632000000000000*r^2*(s:ℝ)^2*x - 3763200000000000000*r^2*(s:ℝ)*x*y
    + 768000000000000000000*r^2*x + 3010560000000000*(s:ℝ)^3*x*y^3
    + 301056000000000000*(s:ℝ)^2*x*y^2 + 7526400000000000000*(s:ℝ)*x*y
    - 1536000000000000000000*x) * hR + (188160000000000*r^4*(s:ℝ)^4*x*y^4
    - 376320000000000*r^4*(s:ℝ)^4*x*y^2 + 188160000000000*r^4*(s:ℝ)^4*x
    + 37632000000000000*r^2*(s:ℝ)^3*x*y^3 - 37632000000000000*r^2*(s:ℝ)^3*x*y
    + 1881600000000000000*r^2*(s:ℝ)^2*x*y^2 - 1881600000000000000*r^2*(s:ℝ)^2*x
    - 3010560000000000*(s:ℝ)^4*x*y^4 - 451584000000000000*(s:ℝ)^3*x*y^3
    - 22579200000000000000*(s:ℝ)^2*x*y^2 + 1159680000000000000000*(s:ℝ)*x*y
    + 76800000000000000000000*x) * hr

/-! ## Derivatives and continuity of the variables along the line -/

/-- `t`-derivatives of the first five variables (slot `5` set to `0`). -/
@[expose] def denv0 (s : ℕ) (t : ℝ) : ℕ → ℝ :=
  envOf (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
    (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹) 0

/-- `t`-derivatives of all six variables along the line. -/
@[expose] def denv (s : ℕ) (t : ℝ) : ℕ → ℝ :=
  envOf (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
    (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹)
    (-((tB2 s).deriv (env0 s t) (denv0 s t) * ((B2v s t)⁻¹) ^ 2))

/-- `R(t)` is differentiable with `R' = s cos t / R`. -/
theorem hasDerivAt_RS_nat {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (RS 10 s) (s * Real.cos t * (RS 10 s t)⁻¹) t := by
  have h := PlasmaLean.Design.SolovevMercierCertified.hasDerivAt_RS_t (s := s)
    (by exact_mod_cast hs1) (by exact_mod_cast hs) t
  simpa [div_eq_mul_inv] using h

/-- Derivatives of the first five variables. -/
theorem hasDerivAt_env0 {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) (i : ℕ) :
    HasDerivAt (fun t => env0 s t i) (denv0 s t i) t := by
  have hR := RS_pos_nat hs t
  have hd := hasDerivAt_RS_nat hs1 hs t
  rcases i with _ | _ | _ | _ | _ | i
  · simpa [env0, denv0, envOf] using Real.hasDerivAt_cos t
  · simpa [env0, denv0, envOf] using Real.hasDerivAt_sin t
  · simpa [env0, denv0, envOf] using hd
  · simpa [env0, denv0, envOf] using hasDerivAt_const t (√2)
  · have := hd.inv hR.ne'
    simp only [env0, denv0, envOf]
    convert this using 1
    field_simp
  · simpa [env0, denv0, envOf] using hasDerivAt_const t (0 : ℝ)

/-- `|B|² = B_R² + B_φ² + B_z²` along the line. -/
theorem B2v_eq (s : ℕ) (t : ℝ) : B2v s t = (tBR s).eval (env s t) ^ 2 +
    tBP.eval (env s t) ^ 2 + (tBZ s).eval (env s t) ^ 2 := by
  simp [B2v, Tm.eval, tB2, tBR, tBP, tBZ, tW, tz, Tm.sq, tX, tR, tr, tiR, env, env0, envOf]
  ring

/-- `|B|² > 0` along the line (the toroidal field never vanishes). -/
theorem B2v_pos {s : ℕ} (hs : s ≤ 25) (t : ℝ) : 0 < B2v s t := by
  have hR := RS_pos_nat hs t
  rw [B2v_eq]
  have : 0 < tBP.eval (env s t) := by
    simp only [Tm.eval, tBP, tiR, env, envOf]; push_cast; positivity
  positivity

/-- `tB2` does not see the slot `5`: its value along the line is `B2v`. -/
theorem tB2_env (s : ℕ) (t : ℝ) : (tB2 s).eval (env s t) = B2v s t := by
  simp [B2v, Tm.eval, tB2, tBR, tBP, tBZ, tW, tz, Tm.sq, tX, tR, tr, tiR, env, env0, envOf]

/-- `|B|²` is differentiable along the line. -/
theorem hasDerivAt_B2v {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (B2v s) ((tB2 s).deriv (env0 s t) (denv0 s t)) t :=
  (tB2 s).hasDerivAt (ρ := env0 s) (ρ' := denv0 s) (hasDerivAt_env0 hs1 hs t)

/-- **Derivatives of all six variables along the line.** -/
theorem hasDerivAt_env {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) (i : ℕ) :
    HasDerivAt (fun t => env s t i) (denv s t i) t := by
  rcases i with _ | _ | _ | _ | _ | i
  · simpa [env, denv, env0, denv0, envOf] using hasDerivAt_env0 hs1 hs t 0
  · simpa [env, denv, env0, denv0, envOf] using hasDerivAt_env0 hs1 hs t 1
  · simpa [env, denv, env0, denv0, envOf] using hasDerivAt_env0 hs1 hs t 2
  · simpa [env, denv, env0, denv0, envOf] using hasDerivAt_env0 hs1 hs t 3
  · simpa [env, denv, env0, denv0, envOf] using hasDerivAt_env0 hs1 hs t 4
  · have h := (hasDerivAt_B2v hs1 hs t).inv (B2v_pos hs t).ne'
    simp only [env, denv, envOf]
    convert h using 1
    field_simp

/-- Continuity of the variables along the line. -/
theorem continuous_env {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (i : ℕ) :
    Continuous fun t => env s t i :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_env hs1 hs t i).continuousAt

/-- Continuity of any tree along the line. -/
theorem continuous_tree {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (e : Tm) :
    Continuous fun t => e.eval (env s t) :=
  e.continuous_eval (continuous_env hs1 hs)

/-- Differentiability of any tree along the line. -/
theorem hasDerivAt_tree {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (e : Tm) (t : ℝ) :
    HasDerivAt (fun t => e.eval (env s t)) (e.deriv (env s t) (denv s t)) t :=
  e.hasDerivAt (hasDerivAt_env hs1 hs t)

/-- The toroidal angle of the line is continuous. -/
theorem continuous_phiS (s : ℕ) (hs : s ≤ 25) : Continuous (phiS (7 / 4) 10 50 s) := by
  have hc := continuous_invCube (L := 10) (s := (s:ℝ)) (by positivity)
    (by norm_num; exact_mod_cast (by omega : 2 * s < 100))
  unfold phiS
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul _).neg.continuousAt

/-! ## The secular drive is an exact derivative: `a' = q₁` -/

/-- The coefficient `a = a₀ − (75/s)/|B|²` of the secular part of the flux function. -/
@[expose] def ta (a0 : ℤ × ℤ) (s : ℕ) : Tm := sub (c a0.1 a0.2) (mul (c 75 s) tiB2)

/-- Surface relations along the line: `cos² + sin² = 1`, `R² = L² + 2 s sin t`, `√2² = 2`. -/
theorem line_relations {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    Real.cos t ^ 2 + Real.sin t ^ 2 = 1 ∧ RS 10 s t ^ 2 = 100 + 2 * s * Real.sin t ∧
      √2 ^ 2 = 2 ∧ RS 10 s t ≠ 0 := by
  refine ⟨by linarith [Real.sin_sq_add_cos_sq t], ?_, Real.sq_sqrt (by norm_num),
    (RS_pos_nat hs t).ne'⟩
  rw [RS_sq (by positivity) (by norm_num; exact_mod_cast (by omega : 2 * s < 100))]
  simp [uS]; ring

/-- **`a' = q₁` along the line.** The `t`-derivative of `a = a₀ − (75/s)/|B|²` is exactly the
coefficient `q₁` of the secular (geodesic-curvature) part of the ballooning drive. This is
what makes the two-variable certificate possible (the `σ³` terms cancel identically). -/
theorem hasDerivAt_a (a0 : ℤ × ℤ) {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (fun t => (ta a0 s).eval (env s t)) ((tq1 s).eval (env s t)) t := by
  have h := hasDerivAt_tree hs1 hs (ta a0 s) t
  refine h.congr_deriv ?_
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs t
  have hsne : (s:ℝ) ≠ 0 := by positivity
  have hB := (B2v_pos hs t).ne'
  have hI1 := Bk0gp_eq s ((B2v s t)⁻¹) hx hR hr hRne hsne
  have hI2 := B2_deriv_eq s 0 0 hx hR hr hRne hsne
  have e1 : (tB2 s).eval (envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹
      (B2v s t)⁻¹) = B2v s t := tB2_env s t
  have e2 : (tB2 s).deriv (envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0)
      (envOf (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
        (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹) 0) =
      (tB2 s).deriv (env0 s t) (denv0 s t) := rfl
  have e3 : tell.eval (envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0) =
      tell.eval (env s t) := by simp [Tm.eval, tell, tr, tiR, env, envOf]
  have e4 : (tBgsG s).eval (envOf (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0) =
      (tBgsG s).eval (env s t) := by
    simp [Tm.eval, tBgsG, tcrossDot, tBR, tBP, tBZ, tgsR, tgsZ, tGR, tGZ, tz, tW, tX, tR, tr,
      tiR, Tm.sq, Tm.sub, env, envOf]
  rw [e1] at hI1
  rw [e2, e3, e4] at hI2
  have hq : (tq1 s).eval (env s t) = 2 * tell.eval (env s t) * ((tBk0gp s).eval (env s t) *
      (tBgsG s).eval (env s t)) * ((B2v s t)⁻¹ * ((B2v s t)⁻¹ * (B2v s t)⁻¹)) := by
    simp [Tm.eval, tq1, Tm.sq, tiB2, env, envOf]
  have hd : (ta a0 s).deriv (env s t) (denv s t) =
      75 / (s:ℝ) * (tB2 s).deriv (env0 s t) (denv0 s t) * ((B2v s t)⁻¹) ^ 2 := by
    simp [Tm.deriv, Tm.eval, ta, tiB2, Tm.sub, denv, envOf]
    ring
  have hk : (tBk0gp s).eval (env s t) = 3 * (7 / 400) * B2v s t := hI1
  rw [hq, hd, hk, hI2]
  field_simp
  ring

/-! ## The ballooning line data of the reactor surfaces -/

section line
variable (s : ℕ)

/-- The secular rate `d(t) = ∂ₛ∂ₜΦ = 3 rate sin t / R⁵` along the line. -/
@[expose] def lnD (t : ℝ) : ℝ := td.eval (env s t)

/-- The secular coefficient `σ(t) = ∫_{π/2}^t d`, i.e. `∂ₛΦ(s, t)` up to a constant. -/
@[expose] def lnSig (t : ℝ) : ℝ := ∫ τ in (π / 2)..t, lnD s τ

/-- `∇√ψ̃` along the line (the secular direction `k₁`). -/
@[expose] def lnGs (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) ((tgsR s).eval (env s t)) 0 ((tgsZ s).eval (env s t))

/-- `∇t` along the line (gradient of the poloidal coordinate). -/
@[expose] def lnGt (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) ((tgtR s).eval (env s t)) 0 ((tgtZ s).eval (env s t))

/-- The periodic part `k₀ = ∇φ − ∂ₜΦ ∇t` of the eikonal gradient. -/
@[expose] def lnK0 (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) ((tkR s).eval (env s t)) (tkP.eval (env s t))
    ((tkZ s).eval (env s t))

/-- The covering-space eikonal gradient of the ballooning family with shift `c`:
`k = ∇(φ − Φ(s, t)) = k₀ − (σ(t) − c) ∇√ψ̃`. -/
@[expose] def lnEik (c t : ℝ) : Space := lnK0 s t - (lnSig s t - c) • lnGs s t

/-- The line element `ℓ = |λ|`, `dl/|B| = ℓ dt`. -/
@[expose] def lnEll (t : ℝ) : ℝ := tell.eval (env s t)

/-- `μ₀ ∇p` along the line (actual Solov'ev pressure). -/
@[expose] def lnGp (t : ℝ) : Space :=
  (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2)) • psiTGrad 10 (lineS (7 / 4) 10 50 s t)

/-- The actual field along the line. -/
@[expose] def lnB (t : ℝ) : Space := reactorField (lineS (7 / 4) 10 50 s t)

/-- The actual field-line curvature `b · ∇b`, from the actual field derivative. -/
@[expose] def lnKappa (t : ℝ) : Space :=
  fieldLineCurvature (lnB s t) (fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t))

end line

/-- `σ' = d`. -/
theorem hasDerivAt_lnSig {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (lnSig s) (lnD s t) t :=
  ((continuous_tree hs1 hs td).integral_hasStrictDerivAt (π / 2) t).hasDerivAt

/-- `μ₀ ∇p` is the actual pressure gradient (times `μ₀`) of the reactor pressure. -/
theorem lnGp_eq_pressure (s : ℕ) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (t : ℝ) :
    lnGp s t = μ₀ • pressureGrad μ₀ (7 / 4) 10 (lineS (7 / 4) 10 50 s t) := by
  rw [lnGp, pressureGrad, smul_smul]
  congr 1
  field_simp

/-- `ℓ = |λ|` for the reparametrization `X' = λ B` of `lineS_fieldLine`. -/
theorem lnEll_eq_abs_lam {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    lnEll s t = |lamS (7 / 4) 10 s t| := by
  have hR := RS_pos_nat hs t
  have h2 : (0:ℝ) < √2 := by positivity
  rw [lamS, abs_neg, abs_of_pos (by positivity)]
  simp [lnEll, Tm.eval, tell, tr, tiR, env, envOf]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- `μ₀∇p = μ ∇√ψ̃` with `μ = −6 c² s`. -/
theorem lnGp_eq {s : ℕ} (hs1 : 1 ≤ s) (t : ℝ) :
    lnGp s t = (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s)) • lnGs s t := by
  rw [lnGp, psiTGrad_line hs1, smul_smul, lnGs]

/-- The eikonal gradient in cylindrical components. -/
theorem lnEik_eq (s : ℕ) (c t : ℝ) : lnEik s c t = cyl (phiS (7 / 4) 10 50 s t)
    ((tkR s).eval (env s t) - (lnSig s t - c) * (tgsR s).eval (env s t)) (tkP.eval (env s t))
    ((tkZ s).eval (env s t) - (lnSig s t - c) * (tgsZ s).eval (env s t)) := by
  rw [lnEik, lnK0, lnGs, smul_cyl, cyl_sub]
  ring_nf

/-! ## Identification of the ballooning coefficients -/

/-- The bending coefficient as a polynomial in the secular variable:
`P(t, σ) = p₀ + σ p₁ + σ² p₂`. -/
@[expose] def Pc (s : ℕ) (t σ : ℝ) : ℝ :=
  (tp0 s).eval (env s t) + σ * (tp1 s).eval (env s t) + σ ^ 2 * (tp2 s).eval (env s t)

/-- The drive as an affine function of the secular variable: `Q(t, σ) = q₀ + σ q₁`. -/
@[expose] def Qc (s : ℕ) (t σ : ℝ) : ℝ := (tq0 s).eval (env s t) + σ * (tq1 s).eval (env s t)

/-- `|B|² = B2v` along the line. -/
theorem norm_sq_lnB {s : ℕ} (hs : s ≤ 25) (t : ℝ) : ‖lnB s t‖ ^ 2 = B2v s t := by
  rw [lnB, B_line hs, norm_sq_cyl, B2v_eq]

/-- `1/(ℓ |B|²)` equals the tree `tden`. -/
theorem tden_eq {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    tden.eval (env s t) = (lnEll s t * B2v s t)⁻¹ := by
  have hR := RS_pos_nat hs t
  have hB := B2v_pos hs t
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (0:ℝ) < √2 := by positivity
  simp only [tden, lnEll, Tm.eval, tell, tr, tR, tiR, tiB2, env, envOf]
  field_simp
  rw [hr]
  ring

/-- **Bending coefficient along the line**: for every secular value `σ`,
`ballooningP ℓ B (k₀ − σ ∇√ψ̃) = P(t, σ)`. -/
theorem P_geom {s : ℕ} (hs : s ≤ 25) (t σ : ℝ) :
    ballooningP (lnEll s t) (lnB s t) (lnK0 s t - σ • lnGs s t) = Pc s t σ := by
  rw [ballooningP_secular, norm_sq_lnB hs, lnK0, lnGs, inner_cyl, norm_sq_cyl, norm_sq_cyl]
  have hd := tden_eq hs t
  simp only [Pc, tp0, tp1, tp2, Tm.eval, Tm.sq, hd]
  ring

/-- **Drive along the line**: for every secular value `σ`,
`ballooningQ ℓ B (k₀ − σ ∇√ψ̃) (μ₀∇p) κ = Q(t, σ)`, with the actual curvature. -/
theorem Q_geom {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t σ : ℝ) :
    ballooningQ (lnEll s t) (lnB s t) (lnK0 s t - σ • lnGs s t) (lnGp s t) (lnKappa s t) =
      Qc s t σ := by
  have hB := B2v_pos hs t
  have hsne : (s:ℝ) ≠ 0 := by positivity
  rw [lnGp_eq hs1, ballooningQ_secular, lnKappa, inner_cross_curvature, inner_cross_curvature,
    show ‖lnB s t‖ ^ 4 = (‖lnB s t‖ ^ 2) ^ 2 by ring, norm_sq_lnB hs]
  simp only [lnB]
  rw [DBB_line hs, B_line hs, lnK0, lnGs, smul_cyl, cross_cyl, cross_cyl, inner_cyl,
    inner_cyl, inner_cyl]
  have gR : (tgpR s).eval (env s t) =
      -(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s) * (tgsR s).eval (env s t) := by
    simp only [tgpR, tgsR, Tm.eval]; push_cast; field_simp; ring
  have gZ : (tgpZ s).eval (env s t) =
      -(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s) * (tgsZ s).eval (env s t) := by
    simp only [tgpZ, tgsZ, Tm.eval]; push_cast; field_simp; ring
  have hiB : tiB2.eval (env s t) = (B2v s t)⁻¹ := by simp [Tm.eval, tiB2, env, envOf]
  simp only [Qc, tq0, tq1, tBk0gp, tBk0G, tBgsG, tcrossDot, Tm.sub, Tm.sq, Tm.eval, gR, gZ, hiB,
    lnEll]
  push_cast
  field_simp
  ring

/-- **The eikonal is a field-line label gradient: `B · k = 0`** along the line, for every
shift `c` (`∂ₜΦ ∇t·B` cancels `∇φ·B`, and `∇√ψ̃ · B = 0`). -/
theorem lnB_inner_lnEik {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (c t : ℝ) :
    ⟪lnB s t, lnEik s c t⟫ = 0 := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs t
  have hsne : (s : ℝ) ≠ 0 := by positivity
  rw [lnB, B_line hs, lnEik_eq, inner_cyl]
  simp only [tBR, tBP, tBZ, tkR, tkP, tkZ, tgsR, tgsZ, tPhit, trate, tgtR, tgtZ, tW, tz, Tm.sq,
    tX, tY, tR, tr, tiR, Tm.eval, env, envOf]
  push_cast
  field_simp
  linear_combination (-10000*√2^4*(s : ℝ)^2*Real.sin t - 20000*√2^2*(s : ℝ)^2*Real.sin t -
      2000000*√2^2*(s : ℝ)) * hx
    + (-10000*RS 10 (s : ℝ) t^2*√2^2*Real.sin t -
      20000*√2^2*(s : ℝ)*Real.sin t^2 + 40000*(s : ℝ)) * hR
    + (10000*√2^2*(s : ℝ)^2*Real.sin t^3 -
      10000*√2^2*(s : ℝ)^2*Real.sin t - 40000*(s : ℝ)^2*Real.sin t - 2000000*(s : ℝ)) * hr

/-- `∇√ψ̃` along the line is continuous. -/
theorem continuous_lnGs {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) : Continuous (lnGs s) :=
  continuous_cyl (continuous_phiS s hs) (continuous_tree hs1 hs _) continuous_const
    (continuous_tree hs1 hs _)

/-- The actual field along the line is continuous. -/
theorem continuous_lnB {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) : Continuous (lnB s) := by
  have : lnB s = fun t => cyl (phiS (7 / 4) 10 50 s t) ((tBR s).eval (env s t))
      (tBP.eval (env s t)) ((tBZ s).eval (env s t)) := funext fun t => B_line hs t
  rw [this]
  exact continuous_cyl (continuous_phiS s hs) (continuous_tree hs1 hs _)
    (continuous_tree hs1 hs _) (continuous_tree hs1 hs _)

/-- The field derivative along the line is continuous. -/
theorem continuous_lnDBB {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) :
    Continuous fun t => fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t) := by
  have : (fun t => fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t)) =
      fun t => cyl (phiS (7 / 4) 10 50 s t) ((tGR s).eval (env s t)) 0
        ((tGZ s).eval (env s t)) := funext fun t => DBB_line hs t
  rw [this]
  exact continuous_cyl (continuous_phiS s hs) (continuous_tree hs1 hs _) continuous_const
    (continuous_tree hs1 hs _)

/-- The field never vanishes along the line. -/
theorem lnB_ne {s : ℕ} (hs : s ≤ 25) (t : ℝ) : lnB s t ≠ 0 := by
  rw [lnB, B_line hs]
  apply cyl_ne_zero
  have hR := RS_pos_nat hs t
  simp only [Tm.eval, tBP, tiR, env, envOf]
  exact mul_ne_zero (by norm_num) (inv_ne_zero hR.ne')

/-- **The ballooning line data of the reactor surface `ψ̃ = s²`** (`1 ≤ s ≤ 25`) for the
eikonal family with shift `c` (`θ_k`): the exact field line `lineS`, the actual field,
pressure gradient and curvature, and the covering-space eikonal gradient
`k = ∇(φ − Φ(s, t)) = k₀ − (σ(t) − c) ∇√ψ̃`. -/
@[expose] def reactorLine {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (c : ℝ) : LineData where
  ℓ := lnEll s
  B := lnB s
  k := lnEik s c
  gp := lnGp s
  κ := lnKappa s
  ℓ_pos t := by
    have hR := RS_pos_nat hs t
    simp only [lnEll, Tm.eval, tell, tr, tiR, env, envOf]
    push_cast
    positivity
  B_ne t := lnB_ne hs t
  k_ne t := by
    rw [lnEik_eq]
    apply cyl_ne_zero
    have hR := RS_pos_nat hs t
    simp only [Tm.eval, tkP, tiR, env, envOf]
    exact inv_ne_zero hR.ne'
  ℓ_cont := continuous_tree hs1 hs tell
  B_cont := continuous_lnB hs1 hs
  k_cont := by
    have hσ : Continuous (lnSig s) := continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_lnSig hs1 hs t).continuousAt
    have : lnEik s c = fun t => lnK0 s t - (lnSig s t - c) • lnGs s t := rfl
    rw [this]
    refine Continuous.sub ?_ ((hσ.sub continuous_const).smul (continuous_lnGs hs1 hs))
    exact continuous_cyl (continuous_phiS s hs) (continuous_tree hs1 hs _)
      (continuous_tree hs1 hs _) (continuous_tree hs1 hs _)
  gp_cont := by
    have : lnGp s = fun t => (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s)) • lnGs s t :=
      funext fun t => lnGp_eq hs1 t
    rw [this]
    exact (continuous_lnGs hs1 hs).const_smul (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * (s:ℝ)))
  κ_cont := by
    have hB := continuous_lnB hs1 hs
    have hD := continuous_lnDBB hs1 hs
    have hn : ∀ t, ‖lnB s t‖ ^ 2 ≠ 0 := fun t => by
      have := norm_pos_iff.mpr (lnB_ne hs t); positivity
    have h1 : Continuous fun t => (⟪lnB s t, fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t)
        (lnB s t)⟫ / ‖lnB s t‖ ^ 2 : ℝ) :=
      Continuous.div (continuous_inner.comp (hB.prodMk hD)) (hB.norm.pow 2) hn
    have h0 : Continuous fun t => ((‖lnB s t‖ ^ 2)⁻¹ : ℝ) := (hB.norm.pow 2).inv₀ hn
    unfold lnKappa fieldLineCurvature
    exact h0.smul (hD.sub (h1.smul hB))

/-- The bending coefficient of the reactor line is `P(t, σ(t) − c)`. -/
theorem reactorLine_P {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (c t : ℝ) :
    (reactorLine hs1 hs c).P t = Pc s t (lnSig s t - c) := by
  simp only [LineData.P, reactorLine, lnEik]
  exact P_geom hs t _

/-- The drive of the reactor line is `Q(t, σ(t) − c)`. -/
theorem reactorLine_Q {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (c t : ℝ) :
    (reactorLine hs1 hs c).Q t = Qc s t (lnSig s t - c) := by
  simp only [LineData.Q, reactorLine, lnEik]
  exact Q_geom hs1 hs t _

/-! ## The certificate flux function -/

namespace Tm

/-- All variables of the tree have index `< k`. -/
@[expose] def UsesBelow (k : ℕ) : Tm → Prop
  | c _ _ => True
  | v i => i < k
  | add a b => a.UsesBelow k ∧ b.UsesBelow k
  | mul a b => a.UsesBelow k ∧ b.UsesBelow k
  | neg a => a.UsesBelow k

/-- The value only depends on the variables actually used. -/
theorem eval_congr {k : ℕ} (e : Tm) (he : e.UsesBelow k) {ρ₁ ρ₂ : ℕ → ℝ}
    (h : ∀ i < k, ρ₁ i = ρ₂ i) : e.eval ρ₁ = e.eval ρ₂ := by
  induction e with
  | c p q => rfl
  | v i => exact h i he
  | add a b iha ihb => simp only [eval, iha he.1, ihb he.2]
  | mul a b iha ihb => simp only [eval, iha he.1, ihb he.2]
  | neg a iha => simp only [eval, iha he]

/-- The derivative only depends on the variables actually used. -/
theorem deriv_congr {k : ℕ} (e : Tm) (he : e.UsesBelow k) {ρ₁ ρ₂ ρ₁' ρ₂' : ℕ → ℝ}
    (h : ∀ i < k, ρ₁ i = ρ₂ i) (h' : ∀ i < k, ρ₁' i = ρ₂' i) :
    e.deriv ρ₁ ρ₁' = e.deriv ρ₂ ρ₂' := by
  induction e with
  | c p q => rfl
  | v i => exact h' i he
  | add a b iha ihb => simp only [deriv, iha he.1, ihb he.2]
  | mul a b iha ihb =>
    simp only [deriv, iha he.1, ihb he.2, eval_congr a he.1 h, eval_congr b he.2 h]
  | neg a iha => simp only [deriv, iha he]

end Tm

/-- Horner tree `Σ (pₖ/qₖ) yᵏ` of a coefficient list. -/
@[expose] def ptree : List (ℤ × ℤ) → Tm → Tm
  | [], _ => c 0 1
  | pq :: l, y => add (c pq.1 pq.2) (mul y (ptree l y))

/-- `tB2` only uses the variables `0, …, 4`. -/
theorem usesBelow_tB2 (s : ℕ) : (tB2 s).UsesBelow 5 := by
  simp [Tm.UsesBelow, tB2, tBR, tBP, tBZ, tW, tz, Tm.sq, tX, tR, tr, tiR]

/-- Horner trees in `y` only use `y`. -/
theorem usesBelow_ptree (l : List (ℤ × ℤ)) : (ptree l tY).UsesBelow 2 := by
  induction l with
  | nil => simp [ptree, Tm.UsesBelow]
  | cons pq l ih => exact ⟨trivial, show (1 : ℕ) < 2 by norm_num, ih⟩

/-- Certificate data for one surface `ψ̃ = s²`: the scale `w = wn/wd` of the `σ`-profiles,
the constant `a₀`, the polynomial profiles `f₀ = x A₀(y)`, `f₁ = x A₁(y)`, `f₂ = A₂(y)`, the
Pólya degree bound `M` and the number `n` of cells of the chart parameter. -/
structure Cert where
  /-- Surface label (`ψ̃ = s²`). -/
  s : ℕ
  /-- Numerator of `w`. -/
  wn : ℤ
  /-- Denominator of `w`. -/
  wd : ℤ
  /-- The constant part of `a`. -/
  a0 : ℤ × ℤ
  /-- Coefficients of `A₀`. -/
  A0 : List (ℤ × ℤ)
  /-- Coefficients of `A₁`. -/
  A1 : List (ℤ × ℤ)
  /-- Coefficients of `A₂`. -/
  A2 : List (ℤ × ℤ)
  /-- Pólya degree bound. -/
  M : ℕ
  /-- Number of chart cells. -/
  n : ℕ

/-- `f₀ = x A₀(y)`. -/ @[expose] def tf0 (C : Cert) : Tm := mul tX (ptree C.A0 tY)
/-- `f₁ = x A₁(y)`. -/ @[expose] def tf1 (C : Cert) : Tm := mul tX (ptree C.A1 tY)
/-- `f₂ = A₂(y)`. -/ @[expose] def tf2 (C : Cert) : Tm := ptree C.A2 tY

/-- Derivative trees of `x, y` along `t` (`x' = −y`, `y' = x`). -/
@[expose] def dvT : ℕ → Tm
  | 0 => neg tY
  | 1 => tX
  | _ => c 0 1

/-- The eleven base coefficient trees: `p₀, p₁, p₂, A = q₀ − f₀', f₁', f₂', d, a, f₀, f₁, f₂`. -/
@[expose] def baseT (C : Cert) : ℕ → Tm
  | 0 => tp0 C.s
  | 1 => tp1 C.s
  | 2 => tp2 C.s
  | 3 => sub (tq0 C.s) (diff dvT (tf0 C))
  | 4 => diff dvT (tf1 C)
  | 5 => diff dvT (tf2 C)
  | 6 => td
  | 7 => ta C.a0 C.s
  | 8 => tf0 C
  | 9 => tf1 C
  | 10 => tf2 C
  | _ => c 0 1

/-! ### The numerator polynomial in `σ`

With `W = w² + σ²`, `ρ = w²/W`, `ν = wσ/W` and the flux
`F = σ a + f₀ + f₁ ρ + f₂ ν`, the Riccati defect `Q − ∂ₜF − d ∂_σF − F²/P` equals
`N(σ)/(P W²)` with `N = Σ_{k ≤ 6} eₖ σᵏ`; the trees `eₖ` are over the base variables
`0 p₀, 1 p₁, 2 p₂, 3 A, 4 g₁ = f₁', 5 g₂ = f₂', 6 d, 7 a, 8 f₀, 9 f₁, 10 f₂`. -/

section etrees
variable (wn wd : ℤ)
/-- `w`. -/ @[expose] def tw : Tm := c wn wd
/-- `h₀ = A − a d`. -/ @[expose] def th0 : Tm := sub (v 3) (mul (v 7) (v 6))
/-- `u₄ = w³ (w (h₀ − g₁) − d f₂)`. -/
@[expose] def tu4 : Tm :=
  mul (mul (tw wn wd) (sq (tw wn wd))) (sub (mul (tw wn wd) (sub th0 (v 4))) (mul (v 6) (v 10)))
/-- `u₂ = w (2 w h₀ + d f₂ − g₁ w)`. -/
@[expose] def tu2 : Tm :=
  mul (tw wn wd) (sub (add (mul (mul (c 2 1) (tw wn wd)) th0) (mul (v 6) (v 10)))
    (mul (v 4) (tw wn wd)))
/-- `v₁ = w² (2 d f₁ − g₂ w)`. -/
@[expose] def tv1 : Tm :=
  mul (sq (tw wn wd)) (sub (mul (c 2 1) (mul (v 6) (v 9))) (mul (v 5) (tw wn wd)))
/-- `S = f₀ + f₁`. -/ @[expose] def tS : Tm := add (v 8) (v 9)
/-- The coefficient trees `e₀, …, e₆`. -/
@[expose] def etree : ℕ → Tm
  | 0 => add (neg (mul (sq (sq (tw wn wd))) (sq tS))) (mul (v 0) (tu4 wn wd))
  | 1 => add (add (neg (mul (mul (c 2 1) (sq (sq (tw wn wd)))) (mul (v 7) tS)))
      (neg (mul (mul (c 2 1) (mul (tw wn wd) (sq (tw wn wd)))) (mul (v 10) tS))))
      (add (mul (v 0) (tv1 wn wd)) (mul (v 1) (tu4 wn wd)))
  | 2 => add (add (add (neg (mul (sq (sq (tw wn wd))) (sq (v 7))))
      (neg (mul (mul (c 2 1) (mul (tw wn wd) (sq (tw wn wd)))) (mul (v 7) (v 10)))))
      (add (neg (mul (mul (c 2 1) (sq (tw wn wd))) (mul (v 8) tS)))
        (neg (mul (sq (tw wn wd)) (sq (v 10))))))
      (add (add (mul (v 0) (tu2 wn wd)) (mul (v 1) (tv1 wn wd))) (mul (v 2) (tu4 wn wd)))
  | 3 => add (add (neg (mul (mul (c 4 1) (sq (tw wn wd))) (mul (v 7) (v 8))))
      (neg (mul (mul (c 2 1) (sq (tw wn wd))) (mul (v 7) (v 9)))))
      (add (add (neg (mul (mul (c 2 1) (tw wn wd)) (mul (v 8) (v 10))))
        (neg (mul (tw wn wd) (mul (v 5) (v 0)))))
        (add (mul (v 1) (tu2 wn wd)) (mul (v 2) (tv1 wn wd))))
  | 4 => add (add (neg (mul (mul (c 2 1) (sq (tw wn wd))) (sq (v 7))))
      (neg (mul (mul (c 2 1) (tw wn wd)) (mul (v 7) (v 10)))))
      (add (add (neg (sq (v 8))) (neg (mul (tw wn wd) (mul (v 5) (v 1)))))
        (add (mul (v 0) th0) (mul (v 2) (tu2 wn wd))))
  | 5 => add (add (neg (mul (c 2 1) (mul (v 7) (v 8)))) (neg (mul (tw wn wd) (mul (v 5) (v 2)))))
      (mul (v 1) th0)
  | 6 => add (neg (sq (v 7))) (mul (v 2) th0)
  | _ => c 0 1
end etrees

/-- The numerator `N(σ) = Σ_{k ≤ 6} eₖ σᵏ` at base values `b`. -/
@[expose] def Npoly (wn wd : ℤ) (b : ℕ → ℝ) (σ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 7, (etree wn wd k).eval b * σ ^ k

/-- **The numerator identity.** With `W = w² + σ²`,
`N = P (A W² − (g₁ w² + g₂ w σ) W − d (a W² − 2 w² σ f₁ + w (w² − σ²) f₂))
  − ((σ a + f₀) W + w² f₁ + w σ f₂)²`. -/
theorem Npoly_eq (wn wd : ℤ) (b : ℕ → ℝ) (σ : ℝ) :
    Npoly wn wd b σ =
      (b 0 + σ * b 1 + σ ^ 2 * b 2) *
        (b 3 * ((wn / wd : ℝ) ^ 2 + σ ^ 2) ^ 2 -
          (b 4 * (wn / wd : ℝ) ^ 2 + b 5 * (wn / wd : ℝ) * σ) * ((wn / wd : ℝ) ^ 2 + σ ^ 2) -
          b 6 * (b 7 * ((wn / wd : ℝ) ^ 2 + σ ^ 2) ^ 2 - 2 * (wn / wd : ℝ) ^ 2 * σ * b 9 +
            (wn / wd : ℝ) * ((wn / wd : ℝ) ^ 2 - σ ^ 2) * b 10)) -
        ((σ * b 7 + b 8) * ((wn / wd : ℝ) ^ 2 + σ ^ 2) + (wn / wd : ℝ) ^ 2 * b 9 +
          (wn / wd : ℝ) * σ * b 10) ^ 2 := by
  simp only [Npoly, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, etree, tw, th0,
    tu4, tu2, tv1, tS, Tm.eval, Tm.sub, Tm.sq]
  push_cast
  ring

/-! ## The chart `τ ↦ ((1 − τ²)/(1 + τ²), 2τ/(1 + τ²))` of the half circle `x ≥ 0` -/

/-- `x(τ) = (1 − τ²)/(1 + τ²)`. -/
@[expose] def xc (τ : ℝ) : ℝ := (1 - τ ^ 2) / (1 + τ ^ 2)

/-- `R` along the chart, `√(L² + 2 s y(τ))`. -/
@[expose] def Rc (s : ℕ) (τ : ℝ) : ℝ := √(100 + 2 * s * wy τ)

/-- The chart variables with the `1/|B|²` slot set to `0`. -/
@[expose] def env0c (s : ℕ) (τ : ℝ) : ℕ → ℝ := envOf (xc τ) (wy τ) (Rc s τ) √2 (Rc s τ)⁻¹ 0

/-- `|B|²` along the chart. -/
@[expose] def B2c (s : ℕ) (τ : ℝ) : ℝ := (tB2 s).eval (env0c s τ)

/-- The six variables along the chart. -/
@[expose] def envc (s : ℕ) (τ : ℝ) : ℕ → ℝ :=
  envOf (xc τ) (wy τ) (Rc s τ) √2 (Rc s τ)⁻¹ (B2c s τ)⁻¹

/-- The `t`-derivative of the first five variables at a general assignment `ρ`. -/
@[expose] def denvAt0 (s : ℕ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  envOf (-ρ 1) (ρ 0) (s * ρ 0 * ρ 4) 0 (-(s * ρ 0 * ρ 4) * ρ 4 * ρ 4) 0

/-- The `t`-derivative of the six variables at a general assignment `ρ`. -/
@[expose] def denvAt (s : ℕ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  envOf (-ρ 1) (ρ 0) (s * ρ 0 * ρ 4) 0 (-(s * ρ 0 * ρ 4) * ρ 4 * ρ 4)
    (-((tB2 s).deriv ρ (denvAt0 s ρ) * ρ 5 ^ 2))

/-- `dt/dτ = 2/(1 + τ²)`. -/
@[expose] def kap (τ : ℝ) : ℝ := 2 / (1 + τ ^ 2)

/-- `x(τ)² + y(τ)² = 1`. -/
theorem xc_sq_add (τ : ℝ) : xc τ ^ 2 + wy τ ^ 2 = 1 := by
  unfold xc wy
  have : 0 < 1 + τ ^ 2 := by positivity
  field_simp
  ring

/-- The radicand of `Rc` is at least `50` on the plasma surfaces. -/
theorem radicand_pos {s : ℕ} (hs : s ≤ 25) (τ : ℝ) : 50 ≤ 100 + 2 * (s:ℝ) * wy τ := by
  have h := wy_mem τ
  have hs' : (s:ℝ) ≤ 25 := by exact_mod_cast hs
  nlinarith [h.1, h.2, (Nat.cast_nonneg s : (0:ℝ) ≤ s)]

/-- `R > 0` along the chart. -/
theorem Rc_pos {s : ℕ} (hs : s ≤ 25) (τ : ℝ) : 0 < Rc s τ :=
  Real.sqrt_pos.mpr (by linarith [radicand_pos hs τ])

/-- `R² = L² + 2 s y` along the chart. -/
theorem Rc_sq {s : ℕ} (hs : s ≤ 25) (τ : ℝ) : Rc s τ ^ 2 = 100 + 2 * s * wy τ :=
  Real.sq_sqrt (by linarith [radicand_pos hs τ])

/-- Derivative of `x(τ)`: `κ · (−y)`. -/
theorem hasDerivAt_xc (τ : ℝ) : HasDerivAt xc (kap τ * -wy τ) τ := by
  have h1 : 0 < 1 + τ ^ 2 := by positivity
  have hn : HasDerivAt (fun τ => 1 - τ ^ 2) (-(2 * τ)) τ := by
    simpa using ((hasDerivAt_id τ).pow 2).const_sub 1
  have hd : HasDerivAt (fun τ => 1 + τ ^ 2) (2 * τ) τ := by
    simpa using ((hasDerivAt_id τ).pow 2).const_add 1
  have := hn.div hd h1.ne'
  unfold xc
  convert this using 1
  unfold kap wy
  field_simp
  ring

/-- Derivative of `y(τ)`: `κ · x`. -/
theorem hasDerivAt_wy (τ : ℝ) : HasDerivAt wy (kap τ * xc τ) τ := by
  have h1 : 0 < 1 + τ ^ 2 := by positivity
  have hn : HasDerivAt (fun τ => 2 * τ) 2 τ := by simpa using (hasDerivAt_id τ).const_mul 2
  have hd : HasDerivAt (fun τ => 1 + τ ^ 2) (2 * τ) τ := by
    simpa using ((hasDerivAt_id τ).pow 2).const_add 1
  have := hn.div hd h1.ne'
  unfold wy
  convert this using 1
  unfold kap xc
  field_simp
  ring

/-- Derivative of `R(τ)`: `κ · s x/R`. -/
theorem hasDerivAt_Rc {s : ℕ} (hs : s ≤ 25) (τ : ℝ) :
    HasDerivAt (Rc s) (kap τ * (s * xc τ * (Rc s τ)⁻¹)) τ := by
  have hp := radicand_pos hs τ
  have hu : HasDerivAt (fun τ => 100 + 2 * (s:ℝ) * wy τ) (2 * s * (kap τ * xc τ)) τ := by
    simpa using ((hasDerivAt_wy τ).const_mul (2 * (s:ℝ))).const_add 100
  have := hu.sqrt (by linarith)
  unfold Rc
  convert this using 1
  have hR : 0 < √(100 + 2 * (s:ℝ) * wy τ) := Real.sqrt_pos.mpr (by linarith)
  field_simp

/-- Derivatives of the first five chart variables: `κ · denvAt0`. -/
theorem hasDerivAt_env0c {s : ℕ} (hs : s ≤ 25) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun τ => env0c s τ i) (kap τ * denvAt0 s (env0c s τ) i) τ := by
  have hR := Rc_pos hs τ
  rcases i with _ | _ | _ | _ | _ | i
  · simpa [env0c, denvAt0, envOf] using hasDerivAt_xc τ
  · simpa [env0c, denvAt0, envOf] using hasDerivAt_wy τ
  · simpa [env0c, denvAt0, envOf, mul_assoc] using hasDerivAt_Rc hs τ
  · simpa [env0c, denvAt0, envOf] using hasDerivAt_const τ (√2)
  · have := (hasDerivAt_Rc hs τ).inv hR.ne'
    simp only [env0c, denvAt0, envOf]
    convert this using 1
    field_simp
  · simpa [env0c, denvAt0, envOf] using hasDerivAt_const τ (0 : ℝ)

/-- `|B|² > 0` along the chart. -/
theorem B2c_pos {s : ℕ} (hs : s ≤ 25) (τ : ℝ) : 0 < B2c s τ := by
  have hR := Rc_pos hs τ
  have hBP : 0 < tBP.eval (env0c s τ) := by
    simp only [Tm.eval, tBP, tiR, env0c, envOf]; push_cast; positivity
  have : B2c s τ = (tBR s).eval (env0c s τ) ^ 2 + tBP.eval (env0c s τ) ^ 2 +
      (tBZ s).eval (env0c s τ) ^ 2 := by
    simp only [B2c, tB2, Tm.eval, Tm.sq]; ring
  rw [this]
  positivity

/-- **Derivatives of the six chart variables**: `d/dτ envc = κ · denvAt (envc)`. -/
theorem hasDerivAt_envc {s : ℕ} (hs : s ≤ 25) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun τ => envc s τ i) (kap τ * denvAt s (envc s τ) i) τ := by
  rcases i with _ | _ | _ | _ | _ | i
  · simpa [envc, denvAt, env0c, denvAt0, envOf] using hasDerivAt_env0c hs τ 0
  · simpa [envc, denvAt, env0c, denvAt0, envOf] using hasDerivAt_env0c hs τ 1
  · simpa [envc, denvAt, env0c, denvAt0, envOf] using hasDerivAt_env0c hs τ 2
  · simpa [envc, denvAt, env0c, denvAt0, envOf] using hasDerivAt_env0c hs τ 3
  · simpa [envc, denvAt, env0c, denvAt0, envOf] using hasDerivAt_env0c hs τ 4
  · have hB := (tB2 s).hasDerivAt (ρ := env0c s)
      (ρ' := fun τ i => kap τ * denvAt0 s (env0c s τ) i) (t := τ) (hasDerivAt_env0c hs τ)
    have h := hB.inv (B2c_pos hs τ).ne'
    have e : (tB2 s).deriv (env0c s τ) (fun i => kap τ * denvAt0 s (env0c s τ) i) =
        kap τ * (tB2 s).deriv (envc s τ) (denvAt0 s (envc s τ)) := by
      rw [Tm.deriv_smul]
      congr 1
    rw [e] at h
    change HasDerivAt (fun τ => (B2c s τ)⁻¹)
      (kap τ * -((tB2 s).deriv (envc s τ) (denvAt0 s (envc s τ)) * ((B2c s τ)⁻¹) ^ 2)) τ
    refine h.congr_deriv ?_
    have := (B2c_pos hs τ).ne'
    change _ = kap τ * -((tB2 s).deriv (envc s τ) (denvAt0 s (envc s τ)) * ((B2c s τ)⁻¹) ^ 2)
    unfold B2c at this ⊢
    field_simp

/-! ## The per-cell checker -/

/-- Interval assignment of the six variables. -/
@[expose] def envOfI (a b c d e f : FIv) : ℕ → FIv
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _ => f

/-- The enclosure `[p₀/q, p₁/q]` (outward rounded). -/
@[expose] def ivHull (p0 p1 q : ℤ) : FIv :=
  ⟨(FIv.ofFrac p0 q).lo, (FIv.ofFrac p1 q).hi, decide (0 < q)⟩

/-- Enclosure of `1`. -/ @[expose] def oneI : FIv := FIv.ofInt 1
/-- Enclosure of `√2`. -/ @[expose] def sqrt2I : FIv := (FIv.ofInt 2).sqrt

section cells
variable (C : Cert) (i : ℕ)
/-- Chart interval of cell `i`: `[(2i − n)/n, (2i + 2 − n)/n]`. -/
@[expose] def cT : FIv := ivHull (2 * i - C.n) (2 * i + 2 - C.n) C.n
/-- `x` over the cell. -/
@[expose] def cX : FIv := (oneI.sub (cT C i).sq).mul (oneI.add (cT C i).sq).inv
/-- `y` over the cell. -/
@[expose] def cY : FIv := ((FIv.ofInt 2).mul (cT C i)).mul (oneI.add (cT C i).sq).inv
/-- `R` over the cell. -/
@[expose] def cR : FIv := ((FIv.ofInt 100).add ((FIv.ofInt (2 * C.s)).mul (cY C i))).sqrt
/-- The first five variables over the cell. -/
@[expose] def cI0 : ℕ → FIv := envOfI (cX C i) (cY C i) (cR C i) sqrt2I (cR C i).inv Tm.zeroIv
/-- `|B|²` over the cell. -/
@[expose] def cB2 : FIv := (tB2 C.s).ieval (cI0 C i)
/-- The six variables over the cell. -/
@[expose] def cI : ℕ → FIv :=
  envOfI (cX C i) (cY C i) (cR C i) sqrt2I (cR C i).inv (cB2 C i).inv
/-- `R' = s x/R` over the cell. -/
@[expose] def cdR : FIv := ((FIv.ofInt C.s).mul (cX C i)).mul (cR C i).inv
/-- `(1/R)' = −R'/R²` over the cell. -/
@[expose] def cdiR : FIv := ((cdR C i).neg.mul (cR C i).inv).mul (cR C i).inv
/-- `t`-derivatives of the first five variables over the cell. -/
@[expose] def cD0 : ℕ → FIv :=
  envOfI (cY C i).neg (cX C i) (cdR C i) Tm.zeroIv (cdiR C i) Tm.zeroIv
/-- `t`-derivatives of the six variables over the cell. -/
@[expose] def cD : ℕ → FIv :=
  envOfI (cY C i).neg (cX C i) (cdR C i) Tm.zeroIv (cdiR C i)
    (((tB2 C.s).idual (cI C i) (cD0 C i)).2.mul (cB2 C i).inv.sq).neg
/-- Numerator of the cell centre `τ_c = m/n`. -/
@[expose] def cm : ℤ := 2 * i + 1 - C.n
/-- `x` at the centre. -/
@[expose] def cXc : FIv :=
  FIv.ofFrac ((C.n : ℤ) * C.n - cm C i * cm C i) ((C.n : ℤ) * C.n + cm C i * cm C i)
/-- `y` at the centre. -/
@[expose] def cYc : FIv := FIv.ofFrac (2 * cm C i * C.n) ((C.n : ℤ) * C.n + cm C i * cm C i)
/-- `R` at the centre. -/
@[expose] def cRc : FIv := ((FIv.ofInt 100).add ((FIv.ofInt (2 * C.s)).mul (cYc C i))).sqrt
/-- The first five variables at the centre. -/
@[expose] def cIc0 : ℕ → FIv := envOfI (cXc C i) (cYc C i) (cRc C i) sqrt2I (cRc C i).inv Tm.zeroIv
/-- The six variables at the centre. -/
@[expose] def cIc : ℕ → FIv :=
  envOfI (cXc C i) (cYc C i) (cRc C i) sqrt2I (cRc C i).inv ((tB2 C.s).ieval (cIc0 C i)).inv
/-- Base coefficients at the centre. -/
@[expose] def cBC (k : ℕ) : FIv := (baseT C k).ieval (cIc C i)
/-- Base coefficients and their `t`-derivatives over the cell. -/
@[expose] def cBD (k : ℕ) : FIv × FIv := (baseT C k).idual (cI C i) (cD C i)
/-- `eₖ` at the centre. -/
@[expose] def cEC (k : ℕ) : FIv := (etree C.wn C.wd k).ieval (cBC C i)
/-- `∂ₜ eₖ` over the cell. -/
@[expose] def cED (k : ℕ) : FIv :=
  ((etree C.wn C.wd k).idual (fun j => (cBD C i j).1) (fun j => (cBD C i j).2)).2
/-- The mean-value factor `[−2/n, 2/n]` (`|t − t_c| ≤ 2|τ − τ_c|`). -/
@[expose] def cH : FIv := ivHull (-2) 2 C.n
/-- Enclosure of `eₖ` over the whole cell (mean-value form). -/
@[expose] def cEH (k : ℕ) : FIv := (cEC C i k).add ((cED C i k).mul (cH C))
/-- Lower coefficients for `σ ≥ 0`. -/
@[expose] def cLp : List ℤ := (List.range 7).map fun k => (cEH C i k).lo
/-- Lower coefficients for `σ ≤ 0` (in `u = −σ`). -/
@[expose] def cLm : List ℤ :=
  (List.range 7).map fun k => if k % 2 = 0 then (cEH C i k).lo else -(cEH C i k).hi
/-- **The per-cell check**: valid enclosures and the Pólya test on both half-lines. -/
@[expose] def cellOK : Bool :=
  ((List.range 7).all fun k => (cEH C i k).ok) && polyaOK C.M (cLp C i) &&
    polyaOK C.M (cLm C i)
end cells

/-- All cells of the chart pass. -/
@[expose] def allOK (C : Cert) : Bool := (List.range C.n).all (cellOK C)

/-- Chunk `k` of `m` consecutive cells (`m k, …, m k + m − 1`) passes. -/
@[expose] def chunkOK (C : Cert) (m k : ℕ) : Bool :=
  (List.range m).all fun j => cellOK C (m * k + j)

/-- `allOK` gives every cell. -/
theorem cells_of_allOK {C : Cert} (h : allOK C = true) : ∀ i < C.n, cellOK C i = true :=
  fun i hi => List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- Chunks of `m` cells cover the cells `0, …, m K − 1`. -/
theorem cells_of_chunks {C : Cert} {m K : ℕ} (h : ∀ k < K, chunkOK C m k = true) :
    ∀ i < m * K, cellOK C i = true := by
  intro i hi
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0] at hi
    · exact h0
  have hk : i / m < K := by
    rw [Nat.div_lt_iff_lt_mul hm]; linarith [Nat.mul_comm m K]
  have hc := List.all_eq_true.mp (h (i / m) hk) (i % m) (List.mem_range.mpr (Nat.mod_lt i hm))
  rwa [Nat.div_add_mod] at hc

/-! ## Soundness of the per-cell checker -/

/-- Soundness of `ivHull`. -/
theorem mem_ivHull {p0 p1 q : ℤ} (hq : 0 < q) {x : ℝ} (h0 : (p0 : ℝ) / q ≤ x)
    (h1 : x ≤ (p1 : ℝ) / q) : (ivHull p0 p1 q).Mem x := by
  have a0 := FIv.mem_ofFrac p0 q
  have a1 := FIv.mem_ofFrac p1 q
  rw [FIv.mem_iff] at a0 a1 ⊢
  have hS := fxScale_pos
  intro _
  have hok : decide (0 < q) = true := by simpa using hq
  obtain ⟨l0, -⟩ := a0 (by simpa [FIv.ofFrac] using hok)
  obtain ⟨-, u1⟩ := a1 (by simpa [FIv.ofFrac] using hok)
  exact ⟨le_trans l0 (by gcongr), le_trans (by gcongr) u1⟩

/-- Membership transports along equality of the real number. -/
theorem mem_of_eq {I : FIv} {x y : ℝ} (h : I.Mem x) (e : x = y) : I.Mem y := e ▸ h

/-- Soundness of integer constants (rewritten form). -/
theorem mem_ofInt' (n : ℤ) {x : ℝ} (h : x = n) : (FIv.ofInt n).Mem x := h ▸ FIv.mem_ofInt n

/-- `√2` enclosure. -/
theorem mem_sqrt2I : sqrt2I.Mem √2 :=
  mem_of_eq (FIv.mem_sqrt (FIv.mem_ofInt 2)) (by norm_num)

/-- Soundness of an interval assignment. -/
theorem mem_envOfI {a b c d e f : FIv} {x y R r iR iB : ℝ} (ha : a.Mem x) (hb : b.Mem y)
    (hc : c.Mem R) (hd : d.Mem r) (he : e.Mem iR) (hf : f.Mem iB) :
    ∀ j, (envOfI a b c d e f j).Mem (envOf x y R r iR iB j) := by
  intro j
  rcases j with _ | _ | _ | _ | _ | j
  exacts [ha, hb, hc, hd, he, hf]

/-- The chart variable lies in its cell interval. -/
theorem mem_cT (C : Cert) (hn : 0 < C.n) (i : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))
      (((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))) : (cT C i).Mem τ :=
  mem_ivHull (by exact_mod_cast hn) hτ.1 hτ.2

section cellsound
variable {C : Cert} {i : ℕ} {τ : ℝ}

/-- `x` over the cell. -/
theorem mem_cX (hT : (cT C i).Mem τ) : (cX C i).Mem (xc τ) := by
  have h1 : oneI.Mem 1 := mem_of_eq (FIv.mem_ofInt 1) (by norm_num)
  have hden := FIv.mem_inv (FIv.mem_add h1 (FIv.mem_sq hT))
  exact mem_of_eq (FIv.mem_mul (FIv.mem_sub h1 (FIv.mem_sq hT)) hden) (by rw [xc, div_eq_mul_inv])

/-- `y` over the cell. -/
theorem mem_cY (hT : (cT C i).Mem τ) : (cY C i).Mem (wy τ) := by
  have h1 : oneI.Mem 1 := mem_of_eq (FIv.mem_ofInt 1) (by norm_num)
  have hden := FIv.mem_inv (FIv.mem_add h1 (FIv.mem_sq hT))
  exact mem_of_eq (FIv.mem_mul (FIv.mem_mul (FIv.mem_ofInt 2) hT) hden)
    (by rw [wy, div_eq_mul_inv]; push_cast; ring)

/-- `R` over the cell. -/
theorem mem_cR (hT : (cT C i).Mem τ) : (cR C i).Mem (Rc C.s τ) :=
  mem_of_eq (FIv.mem_sqrt (FIv.mem_add (FIv.mem_ofInt 100)
    (FIv.mem_mul (FIv.mem_ofInt (2 * C.s)) (mem_cY hT)))) (by rw [Rc]; push_cast; ring_nf)

/-- The first five variables over the cell. -/
theorem mem_cI0 (hT : (cT C i).Mem τ) : ∀ j, (cI0 C i j).Mem (env0c C.s τ j) := by
  unfold cI0 env0c
  exact mem_envOfI (mem_cX hT) (mem_cY hT) (mem_cR hT) mem_sqrt2I (FIv.mem_inv (mem_cR hT))
    Tm.mem_zeroIv

/-- `1/|B|²` over the cell. -/
theorem mem_cB2inv (hT : (cT C i).Mem τ) : (cB2 C i).inv.Mem (B2c C.s τ)⁻¹ := by
  unfold cB2 B2c
  exact FIv.mem_inv ((tB2 C.s).ieval_mem (mem_cI0 hT))

/-- The six variables over the cell. -/
theorem mem_cI (hT : (cT C i).Mem τ) : ∀ j, (cI C i j).Mem (envc C.s τ j) := by
  unfold cI envc
  exact mem_envOfI (mem_cX hT) (mem_cY hT) (mem_cR hT) mem_sqrt2I (FIv.mem_inv (mem_cR hT))
    (mem_cB2inv hT)

/-- `R'` over the cell. -/
theorem mem_cdR (hT : (cT C i).Mem τ) : (cdR C i).Mem (C.s * xc τ * (Rc C.s τ)⁻¹) := by
  unfold cdR
  exact mem_of_eq (FIv.mem_mul (FIv.mem_mul (FIv.mem_ofInt C.s) (mem_cX hT))
    (FIv.mem_inv (mem_cR hT))) (by push_cast; ring)

/-- `(1/R)'` over the cell. -/
theorem mem_cdiR (hT : (cT C i).Mem τ) :
    (cdiR C i).Mem (-(C.s * xc τ * (Rc C.s τ)⁻¹) * (Rc C.s τ)⁻¹ * (Rc C.s τ)⁻¹) := by
  unfold cdiR
  exact FIv.mem_mul (FIv.mem_mul (FIv.mem_neg (mem_cdR hT)) (FIv.mem_inv (mem_cR hT)))
    (FIv.mem_inv (mem_cR hT))

/-- The `t`-derivatives of the first five variables over the cell. -/
theorem mem_cD0 (hT : (cT C i).Mem τ) :
    ∀ j, (cD0 C i j).Mem (denvAt0 C.s (envc C.s τ) j) := by
  unfold cD0 denvAt0
  exact mem_envOfI (FIv.mem_neg (mem_cY hT)) (mem_cX hT) (mem_cdR hT) Tm.mem_zeroIv
    (mem_cdiR hT) Tm.mem_zeroIv

/-- The `t`-derivatives of the six variables over the cell. -/
theorem mem_cD (hT : (cT C i).Mem τ) :
    ∀ j, (cD C i j).Mem (denvAt C.s (envc C.s τ) j) := by
  have h5 : ((((tB2 C.s).idual (cI C i) (cD0 C i)).2.mul (cB2 C i).inv.sq).neg).Mem
      (-((tB2 C.s).deriv (envc C.s τ) (denvAt0 C.s (envc C.s τ)) * envc C.s τ 5 ^ 2)) :=
    FIv.mem_neg (FIv.mem_mul ((tB2 C.s).idual_mem (mem_cI hT) (mem_cD0 hT)).2
      (FIv.mem_sq (mem_cB2inv hT)))
  unfold cD denvAt
  exact mem_envOfI (FIv.mem_neg (mem_cY hT)) (mem_cX hT) (mem_cdR hT) Tm.mem_zeroIv
    (mem_cdiR hT) h5

end cellsound

/-- Value of the chart at the cell centre `τ = m/n`. -/
theorem xc_frac {m n : ℤ} (hn : n ≠ 0) :
    xc ((m : ℝ) / n) = ((n * n - m * m : ℤ) : ℝ) / ((n * n + m * m : ℤ) : ℝ) := by
  unfold xc
  have : (0:ℝ) < n ^ 2 := by positivity
  push_cast
  field_simp

/-- Value of `y` at the cell centre `τ = m/n`. -/
theorem wy_frac {m n : ℤ} (hn : n ≠ 0) :
    wy ((m : ℝ) / n) = ((2 * m * n : ℤ) : ℝ) / ((n * n + m * m : ℤ) : ℝ) := by
  unfold wy
  have : (0:ℝ) < n ^ 2 := by positivity
  push_cast
  field_simp

section centre
variable (C : Cert) (i : ℕ)

/-- The centre `τ_c = m/n` of cell `i`. -/
@[expose] def tc : ℝ := ((cm C i : ℤ) : ℝ) / ((C.n : ℤ) : ℝ)

/-- `x` at the centre. -/
theorem mem_cXc (hn : 0 < C.n) : (cXc C i).Mem (xc (tc C i)) := by
  have hn' : (C.n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold tc cXc
  rw [xc_frac hn']
  exact FIv.mem_ofFrac _ _

/-- `y` at the centre. -/
theorem mem_cYc (hn : 0 < C.n) : (cYc C i).Mem (wy (tc C i)) := by
  have hn' : (C.n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold tc cYc
  rw [wy_frac hn']
  exact FIv.mem_ofFrac _ _

/-- `R` at the centre. -/
theorem mem_cRc (hn : 0 < C.n) : (cRc C i).Mem (Rc C.s (tc C i)) :=
  mem_of_eq (FIv.mem_sqrt (FIv.mem_add (FIv.mem_ofInt 100)
    (FIv.mem_mul (FIv.mem_ofInt (2 * C.s)) (mem_cYc C i hn)))) (by rw [Rc]; push_cast; ring_nf)

/-- The six variables at the cell centre. -/
theorem mem_cIc (hn : 0 < C.n) : ∀ j, (cIc C i j).Mem (envc C.s (tc C i) j) := by
  have h0 : ∀ j, (cIc0 C i j).Mem (env0c C.s (tc C i) j) := by
    unfold cIc0 env0c
    exact mem_envOfI (mem_cXc C i hn) (mem_cYc C i hn) (mem_cRc C i hn) mem_sqrt2I
      (FIv.mem_inv (mem_cRc C i hn)) Tm.mem_zeroIv
  have h5 : ((tB2 C.s).ieval (cIc0 C i)).inv.Mem (B2c C.s (tc C i))⁻¹ :=
    FIv.mem_inv ((tB2 C.s).ieval_mem h0)
  unfold cIc envc
  exact mem_envOfI (mem_cXc C i hn) (mem_cYc C i hn) (mem_cRc C i hn) mem_sqrt2I
    (FIv.mem_inv (mem_cRc C i hn)) h5

end centre
/-! ### Mean value enclosure along the chart -/

/-- Base values along the chart. -/
@[expose] def bc (C : Cert) (τ : ℝ) : ℕ → ℝ := fun j => (baseT C j).eval (envc C.s τ)

/-- The `t`-derivative of `eₖ` along the chart. -/
@[expose] def Dk (C : Cert) (k : ℕ) (τ : ℝ) : ℝ :=
  (etree C.wn C.wd k).deriv (bc C τ)
    (fun j => (baseT C j).deriv (envc C.s τ) (denvAt C.s (envc C.s τ)))

/-- `d/dτ eₖ = κ(τ) · Dₖ(τ)` along the chart. -/
theorem hasDerivAt_ec (C : Cert) (hs : C.s ≤ 25) (k : ℕ) (τ : ℝ) :
    HasDerivAt (fun τ => (etree C.wn C.wd k).eval (bc C τ)) (kap τ * Dk C k τ) τ := by
  have hb : ∀ j, HasDerivAt (fun τ => bc C τ j)
      (kap τ * (baseT C j).deriv (envc C.s τ) (denvAt C.s (envc C.s τ))) τ := by
    intro j
    have := (baseT C j).hasDerivAt (ρ := envc C.s)
      (ρ' := fun τ i => kap τ * denvAt C.s (envc C.s τ) i) (t := τ) (hasDerivAt_envc hs τ)
    rwa [Tm.deriv_smul] at this
  have := (etree C.wn C.wd k).hasDerivAt (ρ := bc C)
    (ρ' := fun τ j => kap τ * (baseT C j).deriv (envc C.s τ) (denvAt C.s (envc C.s τ)))
    (t := τ) hb
  rwa [Tm.deriv_smul] at this

/-- **Mean-value enclosure.** If `g' = κ D` on `[a, b]`, `E ∋ g(τ_c)`, `D_I ∋ D(ξ)` and
`H ∋ κ(ξ)(τ − τ_c)` for all `ξ ∈ [a, b]`, then `E + D_I H ∋ g(τ)`. -/
theorem mem_mvt {g D : ℝ → ℝ} {a b τc τ : ℝ} (hg : ∀ ξ ∈ Icc a b, HasDerivAt g (kap ξ * D ξ) ξ)
    (hc : τc ∈ Icc a b) (hτ : τ ∈ Icc a b) {E Dv H : FIv} (hE : E.Mem (g τc))
    (hD : ∀ ξ ∈ Icc a b, Dv.Mem (D ξ)) (hH : ∀ ξ ∈ Icc a b, H.Mem (kap ξ * (τ - τc))) :
    (E.add (Dv.mul H)).Mem (g τ) := by
  have hcont : ∀ {u v : ℝ}, u ∈ Icc a b → v ∈ Icc a b → ContinuousOn g (Icc u v) :=
    fun hu hv x hx =>
      (hg x ⟨le_trans hu.1 hx.1, le_trans hx.2 hv.2⟩).continuousAt.continuousWithinAt
  rcases lt_trichotomy τc τ with h | h | h
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g (fun ξ => kap ξ * D ξ) h (hcont hc hτ)
      (fun x hx => hg x ⟨le_trans hc.1 hx.1.le, le_trans hx.2.le hτ.2⟩)
    have hξab : ξ ∈ Icc a b := ⟨le_trans hc.1 hξ.1.le, le_trans hξ.2.le hτ.2⟩
    have e : g τ = g τc + D ξ * (kap ξ * (τ - τc)) := by
      have hne : τ - τc ≠ 0 := by linarith
      rw [eq_div_iff hne] at hξe
      linarith
    rw [e]; exact FIv.mem_add hE (FIv.mem_mul (hD ξ hξab) (hH ξ hξab))
  · subst h
    have e : g τc = g τc + D τc * (kap τc * (τc - τc)) := by ring
    rw [e]; exact FIv.mem_add hE (FIv.mem_mul (hD τc hc) (hH τc hc))
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g (fun ξ => kap ξ * D ξ) h (hcont hτ hc)
      (fun x hx => hg x ⟨le_trans hτ.1 hx.1.le, le_trans hx.2.le hc.2⟩)
    have hξab : ξ ∈ Icc a b := ⟨le_trans hτ.1 hξ.1.le, le_trans hξ.2.le hc.2⟩
    have e : g τ = g τc + D ξ * (kap ξ * (τ - τc)) := by
      have hne : τc - τ ≠ 0 := by linarith
      rw [eq_div_iff hne] at hξe
      linarith
    rw [e]; exact FIv.mem_add hE (FIv.mem_mul (hD ξ hξab) (hH ξ hξab))

/-- `0 < κ ≤ 2`. -/
theorem kap_bounds (τ : ℝ) : 0 < kap τ ∧ kap τ ≤ 2 := by
  unfold kap
  have h : 0 < 1 + τ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h]; nlinarith [sq_nonneg τ]

/-! ### From coefficient enclosures to positivity of `N` (Pólya) -/

/-- `zpoly` of seven mapped coefficients is the corresponding sum. -/
theorem zpoly_range7 (f : ℕ → ℤ) (u : ℝ) :
    zpoly ((List.range 7).map f) u = ∑ k ∈ Finset.range 7, (f k : ℝ) * u ^ k := by
  simp [List.range_succ, zpoly, Finset.sum_range_succ]
  ring

/-- **Positivity of `N` from interval coefficients.** If `EHₖ ∋ eₖ(b)` are valid and both Pólya
tests pass, then `N(σ) > 0` for every real `σ`. -/
theorem Npoly_pos_of_bounds {wn wd : ℤ} {b : ℕ → ℝ} {EH : ℕ → FIv} {M : ℕ}
    (hmem : ∀ k, (EH k).Mem ((etree wn wd k).eval b)) (hok : ∀ k < 7, (EH k).ok = true)
    (hp : polyaOK M ((List.range 7).map fun k => (EH k).lo) = true)
    (hm : polyaOK M ((List.range 7).map fun k =>
      if k % 2 = 0 then (EH k).lo else -(EH k).hi) = true) (σ : ℝ) :
    0 < Npoly wn wd b σ := by
  have hS := fxScale_pos
  have hb : ∀ k < 7, ((EH k).lo : ℝ) / fxScale ≤ (etree wn wd k).eval b ∧
      (etree wn wd k).eval b ≤ ((EH k).hi : ℝ) / fxScale := fun k hk => (hmem k) (hok k hk)
  rcases le_or_gt 0 σ with hσ | hσ
  · have hz := zpoly_pos_of_polyaOK hp hσ
    rw [zpoly_range7] at hz
    have key : ∑ k ∈ Finset.range 7, ((EH k).lo : ℝ) / fxScale * σ ^ k ≤ Npoly wn wd b σ := by
      unfold Npoly
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hb k (Finset.mem_range.mp hk)).1 (pow_nonneg hσ k)
    have e : ∑ k ∈ Finset.range 7, ((EH k).lo : ℝ) / fxScale * σ ^ k =
        (∑ k ∈ Finset.range 7, ((EH k).lo : ℝ) * σ ^ k) / fxScale := by
      rw [Finset.sum_div]; congr 1; funext k; ring
    rw [e] at key
    exact lt_of_lt_of_le (div_pos hz hS) key
  · have hu : 0 ≤ -σ := by linarith
    have hz := zpoly_pos_of_polyaOK hm hu
    rw [zpoly_range7] at hz
    have key : ∑ k ∈ Finset.range 7, ((if k % 2 = 0 then (EH k).lo else -(EH k).hi : ℤ) : ℝ) /
        fxScale * (-σ) ^ k ≤ Npoly wn wd b σ := by
      unfold Npoly
      apply Finset.sum_le_sum
      intro k hk
      have hk7 := Finset.mem_range.mp hk
      obtain ⟨h1, h2⟩ := hb k hk7
      rcases Nat.even_or_odd k with he | ho
      · have hk2 : k % 2 = 0 := Nat.even_iff.mp he
        simp only [hk2, ite_true, he.neg_pow]
        exact mul_le_mul_of_nonneg_right h1 (he.pow_nonneg σ)
      · have hk2 : ¬ k % 2 = 0 := by rw [Nat.odd_iff] at ho; omega
        simp only [hk2, ite_false, ho.neg_pow]
        calc ((-(EH k).hi : ℤ) : ℝ) / fxScale * -σ ^ k = ((EH k).hi : ℝ) / fxScale * σ ^ k := by
              push_cast; ring
          _ ≤ (etree wn wd k).eval b * σ ^ k :=
              mul_le_mul_of_nonpos_right h2 (ho.pow_neg hσ).le
    have e : ∑ k ∈ Finset.range 7, ((if k % 2 = 0 then (EH k).lo else -(EH k).hi : ℤ) : ℝ) /
        fxScale * (-σ) ^ k = (∑ k ∈ Finset.range 7,
          ((if k % 2 = 0 then (EH k).lo else -(EH k).hi : ℤ) : ℝ) * (-σ) ^ k) / fxScale := by
      rw [Finset.sum_div]; congr 1; funext k; ring
    rw [e] at key
    exact lt_of_lt_of_le (div_pos hz hS) key

/-! ### Soundness of one cell and of the cover -/

/-- The mean-value factor encloses `κ(ξ)(τ − τ_c)` on the cell. -/
theorem mem_cH (C : Cert) (hn : 0 < C.n) (i : ℕ) {τ ξ : ℝ}
    (hτ : τ ∈ Icc (((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))
      (((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))) :
    (cH C).Mem (kap ξ * (τ - tc C i)) := by
  have hn' : (0 : ℝ) < (C.n : ℤ) := by exact_mod_cast hn
  obtain ⟨k0, k2⟩ := kap_bounds ξ
  have hd : |τ - tc C i| ≤ 1 / ((C.n : ℤ) : ℝ) := by
    obtain ⟨h1, h2⟩ := hτ
    have e1 : (((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ)) = tc C i - 1 / ((C.n : ℤ) : ℝ) := by
      unfold tc cm; push_cast; field_simp; ring
    have e2 : (((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ)) =
        tc C i + 1 / ((C.n : ℤ) : ℝ) := by
      unfold tc cm; push_cast; field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    rw [abs_le]
    constructor <;> linarith
  have hb : |kap ξ * (τ - tc C i)| ≤ 2 / ((C.n : ℤ) : ℝ) := by
    rw [abs_mul, abs_of_pos k0]
    calc kap ξ * |τ - tc C i| ≤ 2 * (1 / ((C.n : ℤ) : ℝ)) :=
          mul_le_mul k2 hd (abs_nonneg _) (by norm_num)
      _ = 2 / ((C.n : ℤ) : ℝ) := by ring
  rw [abs_le] at hb
  push_cast at hb
  unfold cH
  exact mem_ivHull (by exact_mod_cast hn) (by push_cast; rw [neg_div]; linarith [hb.1])
    (by push_cast; linarith [hb.2])

/-- The cell centre lies in the cell. -/
theorem tc_mem (C : Cert) (hn : 0 < C.n) (i : ℕ) :
    tc C i ∈ Icc (((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))
      (((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ)) := by
  have hn' : (0 : ℝ) < (C.n : ℤ) := by exact_mod_cast hn
  unfold tc cm
  constructor <;> (rw [div_le_div_iff_of_pos_right hn']; push_cast; linarith)

/-- **Soundness of one cell**: if `cellOK C i` then `N(σ) > 0` for every chart point `τ` of
cell `i` and every real `σ`. -/
theorem cellOK_sound (C : Cert) (hs : C.s ≤ 25) (hn : 0 < C.n) (i : ℕ) (h : cellOK C i = true)
    {τ : ℝ} (hτ : τ ∈ Icc (((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))
      (((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))) (σ : ℝ) :
    0 < Npoly C.wn C.wd (bc C τ) σ := by
  simp only [cellOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hok, hp⟩, hm⟩ := h
  have hmem : ∀ k, (cEH C i k).Mem ((etree C.wn C.wd k).eval (bc C τ)) := by
    intro k
    have hcen : ∀ j, (cBC C i j).Mem (bc C (tc C i) j) :=
      fun j => (baseT C j).ieval_mem (mem_cIc C i hn)
    refine mem_mvt (a := ((2 * i - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ))
      (b := ((2 * i + 2 - C.n : ℤ) : ℝ) / ((C.n : ℤ) : ℝ)) (D := Dk C k)
      (fun ξ _ => hasDerivAt_ec C hs k ξ) (tc_mem C hn i) hτ
      ((etree C.wn C.wd k).ieval_mem hcen) (fun ξ hξ => ?_) (fun ξ _ => mem_cH C hn i hτ)
    have hT := mem_cT C hn i hξ
    have hB : ∀ j, (cBD C i j).1.Mem (bc C ξ j) ∧
        (cBD C i j).2.Mem ((baseT C j).deriv (envc C.s ξ) (denvAt C.s (envc C.s ξ))) :=
      fun j => (baseT C j).idual_mem (mem_cI hT) (mem_cD hT)
    exact ((etree C.wn C.wd k).idual_mem (fun j => (hB j).1) (fun j => (hB j).2)).2
  exact Npoly_pos_of_bounds hmem (fun k hk => hok k hk) hp hm σ

/-- **Soundness of the cover**: if all cells pass, `N > 0` on the whole half circle `x ≥ 0`
(every `τ ∈ [−1, 1]`) for every `σ`. -/
theorem allOK_sound (C : Cert) (hs : C.s ≤ 25) (hn : 0 < C.n)
    (h : ∀ i < C.n, cellOK C i = true) {τ : ℝ}
    (hτ : τ ∈ Icc (-1 : ℝ) 1) (σ : ℝ) : 0 < Npoly C.wn C.wd (bc C τ) σ := by
  have hn' : (0 : ℝ) < C.n := by exact_mod_cast hn
  set k := ⌊(τ + 1) * C.n / 2⌋₊ with hk
  have hk0 : 0 ≤ (τ + 1) * C.n / 2 := by nlinarith [hτ.1]
  have hk1 := Nat.floor_le hk0
  have hk2 := Nat.lt_floor_add_one ((τ + 1) * C.n / 2)
  rw [← hk] at hk1 hk2
  set i := min (C.n - 1) k with hi
  have hin : i < C.n := by omega
  have hcell := h i hin
  refine cellOK_sound C hs hn i hcell ?_ σ
  have hi1 : (i : ℝ) ≤ k := by exact_mod_cast min_le_right _ _
  constructor
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    push_cast
    nlinarith
  · rw [le_div_iff₀ (by exact_mod_cast hn)]
    push_cast
    rcases le_or_gt k (C.n - 1) with hkn | hkn
    · have : i = k := by omega
      rw [this]
      nlinarith
    · have : i = C.n - 1 := by omega
      have hn1 : ((C.n - 1 : ℕ) : ℝ) = C.n - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, hn1]
      nlinarith [hτ.2]

/-! ### Up–down symmetry: the half circle `x < 0` -/

/-- Signs of the base coefficients under `x ↦ −x` (`p₁, f₂', f₀, f₁` are odd). -/
@[expose] def sgnB : ℕ → ℝ
  | 1 => -1
  | 5 => -1
  | 8 => -1
  | 9 => -1
  | _ => 1

/-- Value of `x` in an assignment. -/
theorem eval_tX (x y R r iR iB : ℝ) : tX.eval (envOf x y R r iR iB) = x := rfl
/-- Value of `y` in an assignment. -/
theorem eval_tY (x y R r iR iB : ℝ) : tY.eval (envOf x y R r iR iB) = y := rfl

/-- `x' = −y`. -/
theorem diff_tX : diff dvT tX = neg tY := rfl
/-- `y' = x`. -/
theorem diff_tY : diff dvT tY = tX := rfl

/-- Horner trees in `y` are even in `x`. -/
theorem ptree_negx (l : List (ℤ × ℤ)) (x y R r iR iB : ℝ) :
    (ptree l tY).eval (envOf (-x) y R r iR iB) = (ptree l tY).eval (envOf x y R r iR iB) := by
  induction l with
  | nil => rfl
  | cons pq l ih => simp only [ptree, Tm.eval, ih]; rfl

/-- The `t`-derivative of a Horner tree in `y` is odd in `x`. -/
theorem diff_ptree_negx (l : List (ℤ × ℤ)) (x y R r iR iB : ℝ) :
    (diff dvT (ptree l tY)).eval (envOf (-x) y R r iR iB) =
      -(diff dvT (ptree l tY)).eval (envOf x y R r iR iB) := by
  induction l with
  | nil => simp [ptree, diff, Tm.eval]
  | cons pq l ih =>
    simp only [ptree, diff, Tm.eval, ih, ptree_negx, diff_tY, eval_tX, eval_tY]
    ring

/-- `|B|²` is even in `x`. -/
theorem tB2_negx (s : ℕ) (x y R r iR iB : ℝ) :
    (tB2 s).eval (envOf (-x) y R r iR iB) = (tB2 s).eval (envOf x y R r iR iB) := by
  simp only [tB2, tBR, tBP, tBZ, tW, tz, Tm.sq, tX, tR, tr, tiR, Tm.eval, envOf]
  ring

/-- **Parity of the base coefficients** under `x ↦ −x`. -/
theorem baseT_negx (C : Cert) (j : ℕ) (x y R r iR iB : ℝ) :
    (baseT C j).eval (envOf (-x) y R r iR iB) =
      sgnB j * (baseT C j).eval (envOf x y R r iR iB) := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp only [baseT, sgnB, tp0, tden, tkR, tkP, tkZ, tPhit, trate, tgtR, tgtZ,
      Tm.sq, tX, tY, tR, tr, tiR, tiB2, Tm.eval, envOf]
    ring
  · simp only [baseT, sgnB, tp1, tden, tkR, tkZ, tPhit, trate, tgtR, tgtZ, tgsR, tgsZ, tW, tz,
      Tm.sq, tX, tY, tR, tr, tiR, tiB2, Tm.eval, envOf]
    ring
  · simp only [baseT, sgnB, tp2, tden, tgsR, tgsZ, tW, tz, Tm.sq, tX, tR, tr, tiR, tiB2,
      Tm.eval, envOf]
    ring
  · have h0 : (diff dvT (tf0 C)).eval (envOf (-x) y R r iR iB) =
        (diff dvT (tf0 C)).eval (envOf x y R r iR iB) := by
      simp only [tf0, diff, Tm.eval, diff_ptree_negx, ptree_negx, diff_tX, eval_tX, eval_tY]
      ring
    have hq : (tq0 C.s).eval (envOf (-x) y R r iR iB) = (tq0 C.s).eval (envOf x y R r iR iB) := by
      simp only [tq0, tell, tBk0gp, tBk0G, tcrossDot, tkR, tkP, tkZ, tPhit, trate, tgtR, tgtZ, tgpR,
        tgpZ, tGR, tGZ, tBR, tBP, tBZ, tW, tz, Tm.sq, Tm.sub, tX, tY, tR, tr, tiR, tiB2, Tm.eval,
        envOf]
      ring
    simp only [baseT, sgnB, Tm.sub, Tm.eval, h0, hq]
    ring
  · simp only [baseT, sgnB, tf1, diff, Tm.eval, diff_ptree_negx, ptree_negx, diff_tX,
      eval_tX, eval_tY]
    ring
  · simp only [baseT, sgnB, tf2, diff_ptree_negx]
    ring
  · simp only [baseT, sgnB, td, trate, Tm.sq, tY, tr, tiR, Tm.eval, envOf]
    ring
  · simp only [baseT, sgnB, ta, Tm.sub, tiB2, Tm.eval, envOf]
    ring
  · simp only [baseT, sgnB, tf0, Tm.eval, ptree_negx, eval_tX]
    ring
  · simp only [baseT, sgnB, tf1, Tm.eval, ptree_negx, eval_tX]
    ring
  · simp only [baseT, sgnB, tf2, ptree_negx]
    ring
  · simp [baseT, sgnB, Tm.eval]

/-- **Parity of `N`**: flipping the signs of the odd base coefficients and `σ` leaves
`N` unchanged. -/
theorem Npoly_negx (wn wd : ℤ) (b : ℕ → ℝ) (σ : ℝ) :
    Npoly wn wd (fun j => sgnB j * b j) (-σ) = Npoly wn wd b σ := by
  simp only [Npoly, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, etree, tw, th0,
    tu4, tu2, tv1, tS, Tm.eval, Tm.sub, Tm.sq, sgnB]
  ring

/-! ### Positivity of `N` along the actual field line -/

/-- Base coefficients along the line. -/
@[expose] def bline (C : Cert) (t : ℝ) : ℕ → ℝ := fun j => (baseT C j).eval (env C.s t)

/-- `R(t) = √(L² + 2 s sin t)`. -/
theorem RS_eq_sqrt (s : ℕ) (t : ℝ) : RS 10 s t = √(100 + 2 * s * Real.sin t) := by
  unfold RS uS; norm_num

/-- **`N(t, σ) > 0` for every `t` and `σ`** (both halves of the circle; the half `x < 0` by
up–down symmetry). -/
theorem Npoly_line_pos (C : Cert) (hs : C.s ≤ 25) (hn : 0 < C.n)
    (h : ∀ i < C.n, cellOK C i = true) (t σ : ℝ) : 0 < Npoly C.wn C.wd (bline C t) σ := by
  have hc2 := Real.sin_sq_add_cos_sq t
  have hsin := Real.abs_sin_le_one t
  rcases le_or_gt 0 (Real.cos t) with hc | hc
  · have h1 : 0 < 1 + Real.cos t := by linarith
    set τ := Real.sin t / (1 + Real.cos t) with hτdef
    have hx : xc τ = Real.cos t := by
      unfold xc; rw [hτdef, div_pow]; field_simp; linear_combination (-1 - Real.cos t) * hc2
    have hy : wy τ = Real.sin t := by
      unfold wy; rw [hτdef, div_pow]; field_simp; linear_combination (-Real.sin t) * hc2
    have hτ : τ ∈ Icc (-1 : ℝ) 1 := by
      rw [hτdef]
      constructor
      · rw [le_div_iff₀ h1]; linarith [neg_abs_le (Real.sin t)]
      · rw [div_le_iff₀ h1]; linarith [le_abs_self (Real.sin t)]
    have hR : Rc C.s τ = RS 10 C.s t := by rw [Rc, hy, RS_eq_sqrt]
    have hB : B2c C.s τ = B2v C.s t := by
      unfold B2c B2v env0c env0; rw [hx, hy, hR]
    have he : envc C.s τ = env C.s t := by unfold envc env; rw [hx, hy, hR, hB]
    have := allOK_sound C hs hn h hτ σ
    have hb : bc C τ = bline C t := by unfold bc bline; rw [he]
    rwa [hb] at this
  · have h1 : 0 < 1 - Real.cos t := by linarith
    set τ := Real.sin t / (1 - Real.cos t) with hτdef
    have hx : xc τ = -Real.cos t := by
      unfold xc; rw [hτdef, div_pow]; field_simp; linear_combination (-1 + Real.cos t) * hc2
    have hy : wy τ = Real.sin t := by
      unfold wy; rw [hτdef, div_pow]; field_simp; linear_combination (-Real.sin t) * hc2
    have hτ : τ ∈ Icc (-1 : ℝ) 1 := by
      rw [hτdef]
      constructor
      · rw [le_div_iff₀ h1]; linarith [neg_abs_le (Real.sin t)]
      · rw [div_le_iff₀ h1]; linarith [le_abs_self (Real.sin t)]
    have hR : Rc C.s τ = RS 10 C.s t := by rw [Rc, hy, RS_eq_sqrt]
    have hB : B2c C.s τ = B2v C.s t := by
      unfold B2c B2v env0c env0; rw [hx, hy, hR, tB2_negx]
    have he : envc C.s τ = envOf (-Real.cos t) (Real.sin t) (RS 10 C.s t) √2 (RS 10 C.s t)⁻¹
        (B2v C.s t)⁻¹ := by unfold envc; rw [hx, hy, hR, hB]
    have hb : bc C τ = fun j => sgnB j * bline C t j := by
      funext j; unfold bc bline env; rw [he, baseT_negx]
    have := allOK_sound C hs hn h hτ (-σ)
    rwa [hb, Npoly_negx] at this

/-! ## The two-variable Riccati certificate and the stability theorem -/

/-- Product rule on the `(t, σ)` plane. -/
theorem hasFDerivAt_prod {g h : ℝ → ℝ} {g' h' t σ : ℝ} (hg : HasDerivAt g g' t)
    (hh : HasDerivAt h h' σ) :
    HasFDerivAt (fun p : ℝ × ℝ => g p.1 * h p.2)
      ((h σ * g') • ContinuousLinearMap.fst ℝ ℝ ℝ + (g t * h') • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, σ) := by
  have h1 := hg.hasFDerivAt.comp (t, σ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, σ)))
  have h2 := hh.hasFDerivAt.comp (t, σ) (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, σ)))
  refine (h1.mul h2).congr_fderiv ?_
  ext <;> simp

/-- Derivative of a tree in `x, y` only (the profiles `f₀, f₁, f₂`). -/
theorem hasDerivAt_xy {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (e : Tm) (he : e.UsesBelow 2) (t : ℝ) :
    HasDerivAt (fun t => e.eval (env s t)) ((diff dvT e).eval (env s t)) t := by
  have h := hasDerivAt_tree hs1 hs e t
  refine h.congr_deriv ?_
  rw [Tm.eval_diff]
  apply Tm.deriv_congr e he (fun _ _ => rfl)
  intro i hi
  interval_cases i <;> rfl

section riccati
variable (C : Cert)

/-- `w` as a real number. -/
@[expose] def wR : ℝ := (C.wn : ℝ) / C.wd
/-- `ρ(σ) = w²/(w² + σ²)`. -/
@[expose] def rhoF (σ : ℝ) : ℝ := wR C ^ 2 / (wR C ^ 2 + σ ^ 2)
/-- `ν(σ) = wσ/(w² + σ²)`. -/
@[expose] def nuF (σ : ℝ) : ℝ := wR C * σ / (wR C ^ 2 + σ ^ 2)
/-- `ρ'(σ)`. -/
@[expose] def drhoF (σ : ℝ) : ℝ := -(2 * wR C ^ 2 * σ) / (wR C ^ 2 + σ ^ 2) ^ 2
/-- `ν'(σ)`. -/
@[expose] def dnuF (σ : ℝ) : ℝ := wR C * (wR C ^ 2 - σ ^ 2) / (wR C ^ 2 + σ ^ 2) ^ 2

/-- **The certificate flux** `F(t, σ) = σ a(t) + f₀(t) + f₁(t) ρ(σ) + f₂(t) ν(σ)`. -/
@[expose] def Fc (t σ : ℝ) : ℝ :=
  σ * bline C t 7 + bline C t 8 + bline C t 9 * rhoF C σ + bline C t 10 * nuF C σ

/-- `∂ₜF = σ q₁ + f₀' + f₁' ρ + f₂' ν` (using `a' = q₁`). -/
@[expose] def Fct (t σ : ℝ) : ℝ :=
  σ * (tq1 C.s).eval (env C.s t) + (diff dvT (tf0 C)).eval (env C.s t) +
    bline C t 4 * rhoF C σ + bline C t 5 * nuF C σ

/-- `∂_σF = a + f₁ ρ' + f₂ ν'`. -/
@[expose] def Fcs (t σ : ℝ) : ℝ := bline C t 7 + bline C t 9 * drhoF C σ + bline C t 10 * dnuF C σ

end riccati

/-- `w² + σ² > 0`. -/
theorem wden_pos {C : Cert} (hw : C.wn ≠ 0) (hwd : 0 < C.wd) (σ : ℝ) : 0 < wR C ^ 2 + σ ^ 2 := by
  have : wR C ≠ 0 := by
    unfold wR; exact div_ne_zero (by exact_mod_cast hw) (by exact_mod_cast hwd.ne')
  positivity

/-- Derivative of `ρ`. -/
theorem hasDerivAt_rhoF {C : Cert} (hw : C.wn ≠ 0) (hwd : 0 < C.wd) (σ : ℝ) :
    HasDerivAt (rhoF C) (drhoF C σ) σ := by
  have hpos := wden_pos hw hwd σ
  have hd : HasDerivAt (fun σ => wR C ^ 2 + σ ^ 2) (2 * σ) σ := by
    simpa using ((hasDerivAt_id σ).pow 2).const_add (wR C ^ 2)
  have := (hasDerivAt_const σ (wR C ^ 2)).div hd hpos.ne'
  unfold rhoF drhoF
  convert this using 1
  ring

/-- Derivative of `ν`. -/
theorem hasDerivAt_nuF {C : Cert} (hw : C.wn ≠ 0) (hwd : 0 < C.wd) (σ : ℝ) :
    HasDerivAt (nuF C) (dnuF C σ) σ := by
  have hpos := wden_pos hw hwd σ
  have hd : HasDerivAt (fun σ => wR C ^ 2 + σ ^ 2) (2 * σ) σ := by
    simpa using ((hasDerivAt_id σ).pow 2).const_add (wR C ^ 2)
  have hn : HasDerivAt (fun σ => wR C * σ) (wR C) σ := by
    simpa using (hasDerivAt_id σ).const_mul (wR C)
  have := hn.div hd hpos.ne'
  unfold nuF dnuF
  convert this using 1
  ring

/-- Continuity of `ρ, ν, ρ', ν'`. -/
theorem continuous_profiles {C : Cert} (hw : C.wn ≠ 0) (hwd : 0 < C.wd) :
    Continuous (rhoF C) ∧ Continuous (nuF C) ∧ Continuous (drhoF C) ∧ Continuous (dnuF C) := by
  have h1 : ∀ σ, wR C ^ 2 + σ ^ 2 ≠ 0 := fun σ => (wden_pos hw hwd σ).ne'
  have h2 : ∀ σ, (wR C ^ 2 + σ ^ 2) ^ 2 ≠ 0 := fun σ => pow_ne_zero 2 (h1 σ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Continuous.div (by fun_prop) (by fun_prop) h1
  · exact Continuous.div (by fun_prop) (by fun_prop) h1
  · exact Continuous.div (by fun_prop) (by fun_prop) h2
  · exact Continuous.div (by fun_prop) (by fun_prop) h2

/-- The bending coefficient `P(t, σ)` is positive for every `(t, σ)`. -/
theorem Pc_pos {s : ℕ} (hs : s ≤ 25) (t σ : ℝ) : 0 < Pc s t σ := by
  rw [← P_geom hs t σ, ballooningP]
  have hR := RS_pos_nat hs t
  have hk : lnK0 s t - σ • lnGs s t ≠ 0 := by
    rw [lnK0, lnGs, smul_cyl, cyl_sub]
    apply cyl_ne_zero
    simp only [Tm.eval, tkP, tiR, env, envOf, mul_zero, sub_zero]
    exact inv_ne_zero hR.ne'
  have hl : 0 < lnEll s t := by
    simp only [lnEll, Tm.eval, tell, tr, tiR, env, envOf]; push_cast; positivity
  have hB : 0 < ‖lnB s t‖ := norm_pos_iff.mpr (lnB_ne hs t)
  have hk' : 0 < ‖lnK0 s t - σ • lnGs s t‖ := norm_pos_iff.mpr hk
  positivity

/-- **The Riccati defect from the numerator.** If `P > 0`, `w ≠ 0` and `N > 0`, then
`∂ₜF + d ∂_σF + F²/P ≤ Q`. -/
theorem riccati_of_N {p0 p1 p2 q0 q1 g0 g1 g2 d a f0 f1 f2 w σ : ℝ} (hW : 0 < w ^ 2 + σ ^ 2)
    (hP : 0 < p0 + σ * p1 + σ ^ 2 * p2)
    (hN : 0 < (p0 + σ * p1 + σ ^ 2 * p2) *
        ((q0 - g0) * (w ^ 2 + σ ^ 2) ^ 2 - (g1 * w ^ 2 + g2 * w * σ) * (w ^ 2 + σ ^ 2) -
          d * (a * (w ^ 2 + σ ^ 2) ^ 2 - 2 * w ^ 2 * σ * f1 + w * (w ^ 2 - σ ^ 2) * f2)) -
        ((σ * a + f0) * (w ^ 2 + σ ^ 2) + w ^ 2 * f1 + w * σ * f2) ^ 2) :
    σ * q1 + g0 + g1 * (w ^ 2 / (w ^ 2 + σ ^ 2)) + g2 * (w * σ / (w ^ 2 + σ ^ 2)) +
        d * (a + f1 * (-(2 * w ^ 2 * σ) / (w ^ 2 + σ ^ 2) ^ 2) +
          f2 * (w * (w ^ 2 - σ ^ 2) / (w ^ 2 + σ ^ 2) ^ 2)) +
        (σ * a + f0 + f1 * (w ^ 2 / (w ^ 2 + σ ^ 2)) + f2 * (w * σ / (w ^ 2 + σ ^ 2))) ^ 2 /
          (p0 + σ * p1 + σ ^ 2 * p2) ≤ q0 + σ * q1 := by
  set P := p0 + σ * p1 + σ ^ 2 * p2 with hPdef
  set W := w ^ 2 + σ ^ 2 with hWdef
  rw [← sub_nonneg]
  have key : q0 + σ * q1 - (σ * q1 + g0 + g1 * (w ^ 2 / W) + g2 * (w * σ / W) +
      d * (a + f1 * (-(2 * w ^ 2 * σ) / W ^ 2) + f2 * (w * (w ^ 2 - σ ^ 2) / W ^ 2)) +
      (σ * a + f0 + f1 * (w ^ 2 / W) + f2 * (w * σ / W)) ^ 2 / P) =
      (P * ((q0 - g0) * W ^ 2 - (g1 * w ^ 2 + g2 * w * σ) * W -
          d * (a * W ^ 2 - 2 * w ^ 2 * σ * f1 + w * (w ^ 2 - σ ^ 2) * f2)) -
        ((σ * a + f0) * W + w ^ 2 * f1 + w * σ * f2) ^ 2) / (P * W ^ 2) := by
    field_simp
    ring
  rw [key]
  positivity

/-- **The two-variable certificate of a surface** (assuming the cover check `allOK C`). -/
@[expose] def riccatiCert (C : Cert) (hs1 : 1 ≤ C.s) (hs : C.s ≤ 25) (hn : 0 < C.n)
    (hw : C.wn ≠ 0) (hwd : 0 < C.wd) (h : ∀ i < C.n, cellOK C i = true) :
    Riccati2D (Pc C.s) (Qc C.s) (lnD C.s) where
  F := Fc C
  Ft := Fct C
  Fs := Fcs C
  hasFDeriv t σ := by
    have ha := hasDerivAt_a C.a0 hs1 hs t
    have hf0 := hasDerivAt_xy hs1 hs (tf0 C) ⟨show (0:ℕ) < 2 by norm_num, usesBelow_ptree _⟩ t
    have hf1 := hasDerivAt_xy hs1 hs (tf1 C) ⟨show (0:ℕ) < 2 by norm_num, usesBelow_ptree _⟩ t
    have hf2 := hasDerivAt_xy hs1 hs (tf2 C) (usesBelow_ptree _) t
    have T1 := hasFDerivAt_prod ha (hasDerivAt_id σ)
    have T2 := hasFDerivAt_prod hf0 (hasDerivAt_const σ (1 : ℝ))
    have T3 := hasFDerivAt_prod hf1 (hasDerivAt_rhoF hw hwd σ)
    have T4 := hasFDerivAt_prod hf2 (hasDerivAt_nuF hw hwd σ)
    have hsum := ((T1.add T2).add T3).add T4
    refine (hsum.congr_fderiv ?_).congr_of_eventuallyEq ?_
    · ext <;> simp [Fct, Fcs, bline, baseT]; ring
    · exact Filter.Eventually.of_forall fun p => by simp [Fc, bline, baseT]; ring
  Ft_cont := by
    obtain ⟨hρ, hν, -, -⟩ := continuous_profiles hw hwd
    have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    have c1 := (continuous_tree hs1 hs (tq1 C.s)).comp hf
    have c2 := (continuous_tree hs1 hs (diff dvT (tf0 C))).comp hf
    have c4 := (continuous_tree hs1 hs (baseT C 4)).comp hf
    have c5 := (continuous_tree hs1 hs (baseT C 5)).comp hf
    exact ((hs'.mul c1).add c2 |>.add (c4.mul (hρ.comp hs'))).add (c5.mul (hν.comp hs'))
  Fs_cont := by
    obtain ⟨-, -, hρ', hν'⟩ := continuous_profiles hw hwd
    have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    have c7 := (continuous_tree hs1 hs (baseT C 7)).comp hf
    have c9 := (continuous_tree hs1 hs (baseT C 9)).comp hf
    have c10 := (continuous_tree hs1 hs (baseT C 10)).comp hf
    exact (c7.add (c9.mul (hρ'.comp hs'))).add (c10.mul (hν'.comp hs'))
  P_pos t σ := Pc_pos hs t σ
  ineq t σ := by
    have hN := Npoly_line_pos C hs hn h t σ
    rw [Npoly_eq] at hN
    have e3 : bline C t 3 = (tq0 C.s).eval (env C.s t) - (diff dvT (tf0 C)).eval (env C.s t) := by
      simp only [bline, baseT, Tm.sub, Tm.eval]; ring
    rw [e3] at hN
    have hP : 0 < bline C t 0 + σ * bline C t 1 + σ ^ 2 * bline C t 2 := Pc_pos hs t σ
    have := riccati_of_N (q1 := (tq1 C.s).eval (env C.s t)) (w := wR C)
      (wden_pos hw hwd σ) hP hN
    exact this

/-- **Ideal-ballooning stability of a reactor flux surface (all field lines, all `θ_k`).**
If every cell check `cellOK C i` (`i < C.n`) passes for the surface `ψ̃ = C.s²`, then for
every shift `c`
(eikonal family) the ballooning line of `reactorLine` is stable: every compactly supported
`C¹` mode has nonnegative energy `∫ (P X'² + Q X²) dt`. -/
theorem reactorLine_stable (C : Cert) (hs1 : 1 ≤ C.s) (hs : C.s ≤ 25) (hn : 0 < C.n)
    (hw : C.wn ≠ 0) (hwd : 0 < C.wd) (h : ∀ i < C.n, cellOK C i = true) (c : ℝ) :
    (reactorLine hs1 hs c).Stable := by
  intro ξ ξ' a b hA
  have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
  have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
  have hPc : Continuous fun p : ℝ × ℝ => Pc C.s p.1 p.2 := by
    have c0 := (continuous_tree hs1 hs (tp0 C.s)).comp hf
    have c1 := (continuous_tree hs1 hs (tp1 C.s)).comp hf
    have c2 := (continuous_tree hs1 hs (tp2 C.s)).comp hf
    exact (c0.add (hs'.mul c1)).add ((hs'.pow 2).mul c2)
  have hQc : Continuous fun p : ℝ × ℝ => Qc C.s p.1 p.2 := by
    have c0 := (continuous_tree hs1 hs (tq0 C.s)).comp hf
    have c1 := (continuous_tree hs1 hs (tq1 C.s)).comp hf
    exact c0.add (hs'.mul c1)
  have := riccati2D_energy_nonneg (riccatiCert C hs1 hs hn hw hwd h) hPc hQc
    (hasDerivAt_lnSig hs1 hs) (continuous_tree hs1 hs td) c hA
  have eP : (reactorLine hs1 hs c).P = fun t => Pc C.s t (lnSig C.s t - c) :=
    funext fun t => reactorLine_P hs1 hs c t
  have eQ : (reactorLine hs1 hs c).Q = fun t => Qc C.s t (lnSig C.s t - c) :=
    funext fun t => reactorLine_Q hs1 hs c t
  rw [eP, eQ]
  exact this

/-! ## The eikonal is the covering-space gradient of the field-line label -/

/-- **`∇√ψ̃` and `∇t` are the dual basis of the meridian coordinates `(s, t) ↦ (R, z)`**:
with the actual partial derivatives `∂ₛR, ∂ₜR, ∂ₛz, ∂ₜz` of `jacobian_eq`
(`SolovevMercierCertified`), `∇√ψ̃ · ∂ₛX = 1`, `∇√ψ̃ · ∂ₜX = 0`, `∇t · ∂ₛX = 0`, `∇t · ∂ₜX = 1`.
By the chain rule these are the gradients of the coordinate functions `√ψ̃` and `t`, so
`lnEik = ∇(φ − Φ(√ψ̃, t)) + c ∇√ψ̃` with `∂ₜΦ = −rate/R³` (`hasDerivAt_phiS`) and
`∂ₛ∂ₜΦ = σ'` (`lnD_eq_mixed`). -/
theorem meridian_dual {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    (tgsR s).eval (env s t) * (Real.sin t / RS 10 s t) + (tgsZ s).eval (env s t) *
        ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
          RS 10 s t ^ 2) = 1 ∧
    (tgsR s).eval (env s t) * (s * Real.cos t / RS 10 s t) + (tgsZ s).eval (env s t) *
        ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
          RS 10 s t ^ 2) = 0 ∧
    (tgtR s).eval (env s t) * (Real.sin t / RS 10 s t) + (tgtZ s).eval (env s t) *
        ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
          RS 10 s t ^ 2) = 0 ∧
    (tgtR s).eval (env s t) * (s * Real.cos t / RS 10 s t) + (tgtZ s).eval (env s t) *
        ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
          RS 10 s t ^ 2) = 1 := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs t
  have hsne : (s:ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [tgsR, tgsZ, tW, tz, Tm.sq, tX, tR, tr, tiR, Tm.eval, env, envOf]
    push_cast
    field_simp
    linear_combination (RS 10 (s:ℝ) t^2*√2^2*(s:ℝ)) * hx + (RS 10 (s:ℝ) t^2*Real.sin t
      - √2^2*(s:ℝ)*Real.sin t^2 + √2^2*(s:ℝ) + 2*(s:ℝ)*Real.sin t^2 - 2*(s:ℝ)) * hR
      + (-2*(s:ℝ)^2*Real.sin t^3 + 2*(s:ℝ)^2*Real.sin t - 100*(s:ℝ)*Real.sin t^2 + 100*(s:ℝ)) * hr
  · simp only [tgsR, tgsZ, tW, tz, Tm.sq, tX, tR, tr, tiR, Tm.eval, env, envOf]
    push_cast
    field_simp
    linear_combination (RS 10 (s:ℝ) t^2*Real.cos t - √2^2*(s:ℝ)*Real.cos t*Real.sin t
      + 2*(s:ℝ)*Real.cos t*Real.sin t) * hR + (-2*(s:ℝ)^2*Real.cos t*Real.sin t^2
      - 100*(s:ℝ)*Real.cos t*Real.sin t) * hr
  · simp only [tgtR, tgtZ, tX, tY, tR, tr, tiR, Tm.eval, env, envOf]
    push_cast
    field_simp
    linear_combination (-√2^2*Real.cos t*Real.sin t) * hR + (-(s:ℝ)*Real.cos t*Real.sin t^2
      - 100*Real.cos t*Real.sin t) * hr
  · simp only [tgtR, tgtZ, tX, tY, tR, tr, tiR, Tm.eval, env, envOf]
    push_cast
    field_simp
    linear_combination (√2^2*(s:ℝ)*Real.sin t + 2*(s:ℝ)*Real.sin t + 200) * hx
      + (√2^2*Real.sin t^2 - 2) * hR + ((s:ℝ)*Real.sin t^3 + (s:ℝ)*Real.sin t
      + 100*Real.sin t^2) * hr

/-- The winding rate: `F L²/(√2 A) = 10000 √2/7`. -/
theorem rateS_eq : rateS (7 / 4) 10 50 = 10000 * √2 / 7 := by
  have h2 : (0:ℝ) < √2 := by positivity
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold rateS
  field_simp
  rw [hr]
  norm_num

/-- `∂ₜΦ = −rate/R³` along the line (the toroidal winding of the exact field line). -/
theorem hasDerivAt_phiS {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (phiS (7 / 4) 10 50 s) (tPhit.eval (env s t)) t := by
  have hc := continuous_invCube (L := 10) (s := (s:ℝ)) (by positivity)
    (by norm_num; exact_mod_cast (by omega : 2 * s < 100))
  have h := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul (rateS (7 / 4) 10 50)).neg
  unfold phiS
  refine h.congr_deriv ?_
  rw [rateS_eq]
  simp only [tPhit, trate, Tm.sq, tr, tiR, Tm.eval, env, envOf]
  push_cast
  ring

/-- `k₀ = ∇φ − ∂ₜΦ ∇t` with the actual `∇φ` and `∂ₜΦ`. -/
theorem lnK0_eq {s : ℕ} (hs : s ≤ 25) (t : ℝ) :
    lnK0 s t = phiGrad (lineS (7 / 4) 10 50 s t) - tPhit.eval (env s t) • lnGt s t := by
  rw [phiGrad_line hs, lnGt, smul_cyl, cyl_sub, lnK0]
  simp only [tkR, tkZ, Tm.eval]
  ring_nf

/-- **`σ' = ∂ₛ∂ₜΦ`**: the secular rate is the derivative in the surface label of the winding
rate `∂ₜΦ = −rate R⁻³` (so `σ(t) = ∂ₛΦ(s, t) + const` by Fubini/FTC, standard). -/
theorem lnD_eq_mixed {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (fun σ : ℝ => -(rateS (7 / 4) 10 50 * (RS 10 σ t ^ 3)⁻¹)) (lnD s t) s := by
  have hsI : (s:ℝ) ∈ Ioo (-45 : ℝ) 45 :=
    ⟨by have : (0:ℝ) ≤ s := by positivity
        linarith, by have : (s:ℝ) ≤ 25 := by exact_mod_cast hs
                     linarith⟩
  have h := ((PlasmaLean.Design.SolovevMercierCertified.hasDerivAt_invRS3 hsI t).const_mul
    (rateS (7 / 4) 10 50)).neg
  refine h.congr_deriv ?_
  have hR := RS_pos_nat hs t
  rw [rateS_eq]
  simp only [lnD, td, trate, Tm.sq, tY, tr, tiR, Tm.eval, env, envOf]
  push_cast
  field_simp

/-! ## The certified surfaces `ψ̃ = s²`, `s = 1, 2, 3, 4` -/

/-- Certificate data for the surface `ψ̃ = 1` (`s = 1`), proposed by an untrusted
SOCP oracle and checked below. -/
@[expose] def cert1 : Cert := ⟨1, 2, 1, (196597, 65536),
  [(7947, 65536), (-143, 65536), (1, 8192)], [(-1, 65536), (-213, 65536), (0, 1)],
  [(-51, 32768), (1, 65536), (213, 65536)], 12, 128⟩

/-- Certificate data for the surface `ψ̃ = 4` (`s = 2`), proposed by an untrusted
SOCP oracle and checked below. -/
@[expose] def cert2 : Cert := ⟨2, 1, 1, (24571, 16384),
  [(3977, 65536), (-143, 65536), (1, 4096)], [(0, 1), (-53, 16384), (1, 65536)],
  [(-91, 65536), (-1, 65536), (53, 16384)], 12, 128⟩

/-- Certificate data for the surface `ψ̃ = 9` (`s = 3`), proposed by an untrusted
SOCP oracle and checked below. -/
@[expose] def cert3 : Cert := ⟨3, 7, 10, (8189, 8192),
  [(83, 2048), (-35, 16384), (3, 8192)], [(-1, 65536), (-209, 65536), (1, 65536)],
  [(-89, 65536), (-1, 16384), (13, 4096)], 12, 128⟩

/-- Certificate data for the surface `ψ̃ = 16` (`s = 4`), proposed by an untrusted
SOCP oracle and checked below. -/
@[expose] def cert4 : Cert := ⟨4, 1, 2, (49103, 65536),
  [(1995, 65536), (-73, 32768), (31, 65536)], [(-1, 65536), (-13, 4096), (1, 32768)],
  [(-43, 32768), (-1, 16384), (207, 65536)], 12, 128⟩

/-- Kernel check of cells `0`–`15` of the surface `s = 1`. -/
theorem cert1_chunk0 : chunkOK cert1 16 0 = true := by decide +kernel

/-- Kernel check of cells `16`–`31` of the surface `s = 1`. -/
theorem cert1_chunk1 : chunkOK cert1 16 1 = true := by decide +kernel

/-- Kernel check of cells `32`–`47` of the surface `s = 1`. -/
theorem cert1_chunk2 : chunkOK cert1 16 2 = true := by decide +kernel

/-- Kernel check of cells `48`–`63` of the surface `s = 1`. -/
theorem cert1_chunk3 : chunkOK cert1 16 3 = true := by decide +kernel

/-- Kernel check of cells `64`–`79` of the surface `s = 1`. -/
theorem cert1_chunk4 : chunkOK cert1 16 4 = true := by decide +kernel

/-- Kernel check of cells `80`–`95` of the surface `s = 1`. -/
theorem cert1_chunk5 : chunkOK cert1 16 5 = true := by decide +kernel

/-- Kernel check of cells `96`–`111` of the surface `s = 1`. -/
theorem cert1_chunk6 : chunkOK cert1 16 6 = true := by decide +kernel

/-- Kernel check of cells `112`–`127` of the surface `s = 1`. -/
theorem cert1_chunk7 : chunkOK cert1 16 7 = true := by decide +kernel

/-- All 128 cells of the surface `s = 1` pass. -/
theorem cert1_cells : ∀ i < cert1.n, cellOK cert1 i = true :=
  cells_of_chunks (m := 16) (K := 8) fun k hk => by
    interval_cases k
    exacts [cert1_chunk0, cert1_chunk1, cert1_chunk2, cert1_chunk3, cert1_chunk4,
      cert1_chunk5, cert1_chunk6, cert1_chunk7]

/-- Kernel check of cells `0`–`15` of the surface `s = 2`. -/
theorem cert2_chunk0 : chunkOK cert2 16 0 = true := by decide +kernel

/-- Kernel check of cells `16`–`31` of the surface `s = 2`. -/
theorem cert2_chunk1 : chunkOK cert2 16 1 = true := by decide +kernel

/-- Kernel check of cells `32`–`47` of the surface `s = 2`. -/
theorem cert2_chunk2 : chunkOK cert2 16 2 = true := by decide +kernel

/-- Kernel check of cells `48`–`63` of the surface `s = 2`. -/
theorem cert2_chunk3 : chunkOK cert2 16 3 = true := by decide +kernel

/-- Kernel check of cells `64`–`79` of the surface `s = 2`. -/
theorem cert2_chunk4 : chunkOK cert2 16 4 = true := by decide +kernel

/-- Kernel check of cells `80`–`95` of the surface `s = 2`. -/
theorem cert2_chunk5 : chunkOK cert2 16 5 = true := by decide +kernel

/-- Kernel check of cells `96`–`111` of the surface `s = 2`. -/
theorem cert2_chunk6 : chunkOK cert2 16 6 = true := by decide +kernel

/-- Kernel check of cells `112`–`127` of the surface `s = 2`. -/
theorem cert2_chunk7 : chunkOK cert2 16 7 = true := by decide +kernel

/-- All 128 cells of the surface `s = 2` pass. -/
theorem cert2_cells : ∀ i < cert2.n, cellOK cert2 i = true :=
  cells_of_chunks (m := 16) (K := 8) fun k hk => by
    interval_cases k
    exacts [cert2_chunk0, cert2_chunk1, cert2_chunk2, cert2_chunk3, cert2_chunk4,
      cert2_chunk5, cert2_chunk6, cert2_chunk7]

/-- Kernel check of cells `0`–`15` of the surface `s = 3`. -/
theorem cert3_chunk0 : chunkOK cert3 16 0 = true := by decide +kernel

/-- Kernel check of cells `16`–`31` of the surface `s = 3`. -/
theorem cert3_chunk1 : chunkOK cert3 16 1 = true := by decide +kernel

/-- Kernel check of cells `32`–`47` of the surface `s = 3`. -/
theorem cert3_chunk2 : chunkOK cert3 16 2 = true := by decide +kernel

/-- Kernel check of cells `48`–`63` of the surface `s = 3`. -/
theorem cert3_chunk3 : chunkOK cert3 16 3 = true := by decide +kernel

/-- Kernel check of cells `64`–`79` of the surface `s = 3`. -/
theorem cert3_chunk4 : chunkOK cert3 16 4 = true := by decide +kernel

/-- Kernel check of cells `80`–`95` of the surface `s = 3`. -/
theorem cert3_chunk5 : chunkOK cert3 16 5 = true := by decide +kernel

/-- Kernel check of cells `96`–`111` of the surface `s = 3`. -/
theorem cert3_chunk6 : chunkOK cert3 16 6 = true := by decide +kernel

/-- Kernel check of cells `112`–`127` of the surface `s = 3`. -/
theorem cert3_chunk7 : chunkOK cert3 16 7 = true := by decide +kernel

/-- All 128 cells of the surface `s = 3` pass. -/
theorem cert3_cells : ∀ i < cert3.n, cellOK cert3 i = true :=
  cells_of_chunks (m := 16) (K := 8) fun k hk => by
    interval_cases k
    exacts [cert3_chunk0, cert3_chunk1, cert3_chunk2, cert3_chunk3, cert3_chunk4,
      cert3_chunk5, cert3_chunk6, cert3_chunk7]

/-- Kernel check of cells `0`–`15` of the surface `s = 4`. -/
theorem cert4_chunk0 : chunkOK cert4 16 0 = true := by decide +kernel

/-- Kernel check of cells `16`–`31` of the surface `s = 4`. -/
theorem cert4_chunk1 : chunkOK cert4 16 1 = true := by decide +kernel

/-- Kernel check of cells `32`–`47` of the surface `s = 4`. -/
theorem cert4_chunk2 : chunkOK cert4 16 2 = true := by decide +kernel

/-- Kernel check of cells `48`–`63` of the surface `s = 4`. -/
theorem cert4_chunk3 : chunkOK cert4 16 3 = true := by decide +kernel

/-- Kernel check of cells `64`–`79` of the surface `s = 4`. -/
theorem cert4_chunk4 : chunkOK cert4 16 4 = true := by decide +kernel

/-- Kernel check of cells `80`–`95` of the surface `s = 4`. -/
theorem cert4_chunk5 : chunkOK cert4 16 5 = true := by decide +kernel

/-- Kernel check of cells `96`–`111` of the surface `s = 4`. -/
theorem cert4_chunk6 : chunkOK cert4 16 6 = true := by decide +kernel

/-- Kernel check of cells `112`–`127` of the surface `s = 4`. -/
theorem cert4_chunk7 : chunkOK cert4 16 7 = true := by decide +kernel

/-- All 128 cells of the surface `s = 4` pass. -/
theorem cert4_cells : ∀ i < cert4.n, cellOK cert4 i = true :=
  cells_of_chunks (m := 16) (K := 8) fun k hk => by
    interval_cases k
    exacts [cert4_chunk0, cert4_chunk1, cert4_chunk2, cert4_chunk3, cert4_chunk4,
      cert4_chunk5, cert4_chunk6, cert4_chunk7]

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 1`** (`s = 1`): for every
eikonal family (shift `c`, i.e. every `θ_k`) the ballooning line of the exact field line
`lineS` has nonnegative energy for every compactly supported `C¹` mode. -/
theorem reactor_ballooning_s1 (c : ℝ) : (reactorLine (s := 1) le_rfl (by norm_num) c).Stable :=
  reactorLine_stable cert1 le_rfl (by norm_num [cert1]) (by norm_num [cert1]) (by norm_num [cert1])
    (by norm_num [cert1]) cert1_cells c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 4`** (`s = 2`). -/
theorem reactor_ballooning_s2 (c : ℝ) :
    (reactorLine (s := 2) (by norm_num) (by norm_num) c).Stable :=
  reactorLine_stable cert2 (by norm_num [cert2]) (by norm_num [cert2]) (by norm_num [cert2])
    (by norm_num [cert2]) (by norm_num [cert2]) cert2_cells c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 9`** (`s = 3`). -/
theorem reactor_ballooning_s3 (c : ℝ) :
    (reactorLine (s := 3) (by norm_num) (by norm_num) c).Stable :=
  reactorLine_stable cert3 (by norm_num [cert3]) (by norm_num [cert3]) (by norm_num [cert3])
    (by norm_num [cert3]) (by norm_num [cert3]) cert3_cells c

/-- **Ideal-ballooning stability of the reactor surface `ψ̃ = 16`** (`s = 4`). -/
theorem reactor_ballooning_s4 (c : ℝ) :
    (reactorLine (s := 4) (by norm_num) (by norm_num) c).Stable :=
  reactorLine_stable cert4 (by norm_num [cert4]) (by norm_num [cert4]) (by norm_num [cert4])
    (by norm_num [cert4]) (by norm_num [cert4]) cert4_cells c

/-! ## Sanity checks -/

/-- Rejected fixture: without the oscillating profiles (`f₀ = f₁ = f₂ = 0`, same `a₀`, `w`) the
outboard-midplane cell (`τ ≈ 1`, bad curvature) fails, so the profiles are essential and the
checker is not vacuous. -/
theorem noProfile_rejected :
    cellOK ⟨1, 2, 1, (196597, 65536), [], [], [], 12, 128⟩ 127 = false := by decide +kernel

/-- The certificate of `s = 1` uses the reactor surface label and `128` cells. -/
theorem cert1_shape : cert1.s = 1 ∧ cert1.n = 128 := ⟨rfl, rfl⟩

end PlasmaLean.Design.SolovevBallooning
