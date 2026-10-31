/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellarator
public import PlasmaLean.Theory.Fields.QSLinearSystem
public import PlasmaLean.Certificates.KernelFact

/-!
# A certified jet obstruction to strong quasisymmetry for the rational stellarator field

Research question Q-25 (c); note N-32 (`notes/theory/holomorphic-qs-brief.md`, §3). The
pointwise jet obstruction `strongQS_jet_obstruction` (`Theory/Fields/QSLinearSystem`) is applied
to the exact vacuum field `RationalStellarator.field (1/4)` (`B = ∇φ + (1/4)∇h`, the certified
`ε`) at the point `p₀ = (1, 0, 1/4)` (cylindrical `R = 1`, `φ = 0`, `z = 1/4`: a quarter unit
above the exact magnetic axis, off the rank-deficient loci).

## The jet at `p₀` (exact rationals; `scripts/quasisymmetry/rational_stellarator_jet.py`)

* `B(p₀) = (1/32, 129/128, -1/8)`, `Q = |B|² = 16913/16384`, `h = B · ∇Q = 7085/262144`,
  `k = B · ∇h = -39250397/67108864`;
* `Y = B × ∇Q = (90915/262144, 775/4096, 1690515/1048576)`,
  `Z = [B, Y] = (203703/4194304, 167461/1048576, 5451543/4194304)`;
* `det(B, Y, Z) = -214774797888495/562949953421312 ≈ -0.3815` (normalized by the three lengths:
  `≈ -0.173`);
* `η(p₀) = (-106520713099/40636158768, 497802473/3386346564, 5383052747/10159039692)`;
* `Dη(p₀) = S` (`St`), with `dη(p₀) = curl S ≈ (-4.665, 38.689, -32.935)`; the certified
  component is `(curl S)_y = 2495555802823774390291/64503804664769659290 ≈ 38.69`.

## Method

The field is rational with denominators powers of `r₂ = x² + y²`. Its coordinates are written as
polynomials in `(x, y, z, w)` with `w = 1/r₂` (`Pb0`, `Pb1`, `Pb2`; `field_coord`). This class is
closed under differentiation: `∂ᵢ w = -2 cᵢ w²`, `c = (x, y, 0)`, so the formal derivative `p4D`
is an actual derivative off the `z`-axis (`p4Eval_hasPartials`). The partial derivatives of `B`
up to order three are therefore explicit functions on the whole domain (`bR`, `JR`, `KR`, `LR`).
The fields of the obstruction are polynomial expressions in this jet (`gqF` = `∇Q`, `YF`, `hF`,
`ZF`, `kF`, and their derivatives `YdF`, `ZdF`, …, all built from `dot3` and `crossF` over any
commutative ring), and the product rule for `HasPartials` gives their actual derivatives at
every point of the domain. At `p₀` the jet is a table of rationals (`bt`, `Jt`, `Kt`, `Lt`,
checked against the formal derivatives by `kernel_fact`), and the linear system of the jet
obstruction is checked over `ℚ` by `kernel_fact` (`jetCheck_true`) and transferred to `ℝ` by
casting.

## Main results

* `strongQS_obstruction`: if `field (1/4)` is strongly quasisymmetric (`StrongQSAt`: `B × u = ∇Ψ`,
  `B · u = C`, `div u = 0`) at every point of a neighbourhood `U` of `p₀`, with any generator `u`
  and any potential `Ψ` of class `C²` at `p₀`, then `C = 0` and `∇Ψ = 0` near `p₀`;
* `not_strongQS_of_ne_zero`: so no strong quasisymmetry with `C ≠ 0` holds on any neighbourhood
  of `p₀`.

Scope. This is a **local** statement at one point of the plasma region. It complements
`RationalStellaratorQAObstruction` (first order in the distance to the axis, all helicities,
along the whole axis) by an exact statement off the axis; it is **not** a global non-existence
theorem (no solid torus, no periods), and it does not exclude approximate quasisymmetry.
-/

open scoped RealInnerProductSpace Topology
open InnerProductSpace Filter

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorJetObstruction
open PlasmaLean.Fields PlasmaLean.Fields.QSLinear PlasmaLean.Vacuum
open PlasmaLean.Design.RationalStellarator

/-! ## Polynomials in `(x, y, z, w)` with `w = 1/r₂` -/

/-- A monomial `c x^a y^b z^d w^e`, `w = 1/(x² + y²)`, stored as `(c, a, b, d, e)`. -/
abbrev Mono4 := ℚ × ℕ × ℕ × ℕ × ℕ

/-- Evaluation of a monomial (with Lean's total `winv = r₂⁻¹`). -/
@[expose] def m4Eval (m : Mono4) (y : Space) : ℝ :=
  (m.1 : ℝ) * y 0 ^ m.2.1 * y 1 ^ m.2.2.1 * y 2 ^ m.2.2.2.1 * winv y ^ m.2.2.2.2

/-- Evaluation of a polynomial (a list of monomials). -/
@[expose] def p4Eval (P : List Mono4) (y : Space) : ℝ := (P.map fun m => m4Eval m y).sum

/-- Formal partial derivative `∂ₗ` of a monomial, using `∂ₗ w = -2 cₗ w²`, `c = (x, y, 0)`. -/
@[expose] def m4D (l : Fin 3) (m : Mono4) : List Mono4 :=
  ![[(m.1 * m.2.1, m.2.1 - 1, m.2.2.1, m.2.2.2.1, m.2.2.2.2),
      (-2 * m.1 * m.2.2.2.2, m.2.1 + 1, m.2.2.1, m.2.2.2.1, m.2.2.2.2 + 1)],
    [(m.1 * m.2.2.1, m.2.1, m.2.2.1 - 1, m.2.2.2.1, m.2.2.2.2),
      (-2 * m.1 * m.2.2.2.2, m.2.1, m.2.2.1 + 1, m.2.2.2.1, m.2.2.2.2 + 1)],
    [(m.1 * m.2.2.2.1, m.2.1, m.2.2.1, m.2.2.2.1 - 1, m.2.2.2.2)]] l

/-- Formal partial derivative `∂ₗ` of a polynomial. -/
@[expose] def p4D (l : Fin 3) (P : List Mono4) : List Mono4 := P.flatMap (m4D l)

/-- Exact rational evaluation of a polynomial at `(x, y, z, w) = (a, b, c, w)`. -/
@[expose] def p4EvalQ (P : List Mono4) (a b c w : ℚ) : ℚ :=
  (P.map fun m => m.1 * a ^ m.2.1 * b ^ m.2.2.1 * c ^ m.2.2.2.1 * w ^ m.2.2.2.2).sum

/-- Sanity check: `∂_z (z² w) = 2 z w` and `∂ₓ w = -2 x w²` formally. -/
example : p4D 2 [(1, 0, 0, 2, 1)] = [(2, 0, 0, 1, 1)] ∧
    p4D 0 [(1, 0, 0, 0, 1)] = [(0, 0, 0, 0, 1), (-2, 1, 0, 0, 2)] := by
  simp [p4D, m4D]

/-! ## Partial derivatives -/

/-- `f` has partial derivatives `d 0`, `d 1`, `d 2` at `y` (as a Fréchet derivative). -/
@[expose] def HasPartials (f : Space → ℝ) (d : Fin 3 → ℝ) (y : Space) : Prop :=
  HasFDerivAt f (lin (d 0) (d 1) (d 2)) y

namespace HasPartials

variable {f g : Space → ℝ} {d e : Fin 3 → ℝ} {y : Space}

/-- The underlying Fréchet derivative. -/
theorem hasFDerivAt (h : HasPartials f d y) : HasFDerivAt f (lin (d 0) (d 1) (d 2)) y := h

/-- Change the partials along a pointwise identity. -/
theorem congr_d (h : HasPartials f d y) {d' : Fin 3 → ℝ} (hd : ∀ l, d l = d' l) :
    HasPartials f d' y := by
  unfold HasPartials at *
  rwa [← hd 0, ← hd 1, ← hd 2]

/-- Change the function along a pointwise identity. -/
theorem congr_fun (h : HasPartials g d y) (hf : ∀ z, f z = g z) : HasPartials f d y := by
  rwa [show f = g from funext hf]

/-- Sum rule. -/
theorem add (hf : HasPartials f d y) (hg : HasPartials g e y) :
    HasPartials (fun z => f z + g z) (fun l => d l + e l) y :=
  (HasFDerivAt.add hf hg).congr_fderiv (by
    ext v; simp [lin_apply]; ring)

/-- Difference rule. -/
theorem sub (hf : HasPartials f d y) (hg : HasPartials g e y) :
    HasPartials (fun z => f z - g z) (fun l => d l - e l) y :=
  (HasFDerivAt.sub hf hg).congr_fderiv (by
    ext v; simp [lin_apply]; ring)

/-- Product rule. -/
theorem mul (hf : HasPartials f d y) (hg : HasPartials g e y) :
    HasPartials (fun z => f z * g z) (fun l => d l * g y + f y * e l) y :=
  (HasFDerivAt.mul hf hg).congr_fderiv (by
    ext v; simp [lin_apply]; ring)

/-- Constant multiple. -/
theorem const_mul (c : ℝ) (hf : HasPartials f d y) :
    HasPartials (fun z => c * f z) (fun l => c * d l) y :=
  (HasFDerivAt.const_mul hf c).congr_fderiv (by
    ext v; simp [lin_apply]; ring)

end HasPartials

/-- Derivative of a monomial off the `z`-axis. -/
theorem m4Eval_hasPartials (m : Mono4) {y : Space} (hy : r2 y ≠ 0) :
    HasPartials (m4Eval m) (fun l => p4Eval (m4D l m) y) y := by
  obtain ⟨c, a, b, d, e⟩ := m
  have hw := hasFDerivAt_winv y hy
  have h := (((((hasFDerivAt_const (c : ℝ) y).mul ((hasFDerivAt_coord y 0).pow a)).mul
    ((hasFDerivAt_coord y 1).pow b)).mul ((hasFDerivAt_coord y 2).pow d)).mul (hw.pow e))
  unfold HasPartials
  refine h.congr_fderiv ?_
  ext v
  rcases e with _ | e <;>
    simp [m4D, p4Eval, m4Eval, lin_apply, wd, cv] <;> ring

/-- **Formal derivatives are derivatives** off the `z`-axis. -/
theorem p4Eval_hasPartials (P : List Mono4) {y : Space} (hy : r2 y ≠ 0) :
    HasPartials (p4Eval P) (fun l => p4Eval (p4D l P) y) y := by
  induction P with
  | nil =>
    refine (show HasPartials (fun _ => (0 : ℝ)) (fun _ => 0) y from ?_).congr_fun
      (fun z => by simp [p4Eval]) |>.congr_d (fun l => by simp [p4Eval, p4D])
    exact (hasFDerivAt_const (0 : ℝ) y).congr_fderiv (by ext v; simp [lin_apply])
  | cons m P ih =>
    refine ((m4Eval_hasPartials m hy).add ih).congr_fun (fun z => by simp [p4Eval]) |>.congr_d
      (fun l => by simp [p4Eval, p4D])

/-- Rational evaluation agrees with real evaluation at a rational point. -/
theorem p4Eval_cast (P : List Mono4) {y : Space} {a b c w : ℚ} (ha : y 0 = a) (hb : y 1 = b)
    (hc : y 2 = c) (hw : winv y = w) : p4Eval P y = (p4EvalQ P a b c w : ℝ) := by
  induction P with
  | nil => simp [p4Eval, p4EvalQ]
  | cons m P ih =>
    simp only [p4Eval, p4EvalQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [m4Eval, ha, hb, hc, hw]

/-! ## Jet formulas over a commutative ring -/

section Formulas

variable {R : Type*} [CommRing R]

/-- Dot product of coordinate triples. -/
@[expose] def dot3 (u v : Fin 3 → R) : R := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross product of coordinate triples. -/
@[expose] def crossF (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

variable (b : Fin 3 → R) (J : Fin 3 → Fin 3 → R) (K : Fin 3 → Fin 3 → Fin 3 → R)
  (L : Fin 3 → Fin 3 → Fin 3 → Fin 3 → R)

/-- `∂ⱼQ = 2 ∑ᵢ bᵢ ∂ⱼbᵢ` (`Jᵢⱼ = ∂ⱼbᵢ`). -/
@[expose] def gqF (j : Fin 3) : R := 2 * dot3 b (fun i => J i j)

/-- `∂ₗ∂ⱼQ` (`Kᵢⱼₗ = ∂ₗ∂ⱼbᵢ`). -/
@[expose] def gqdF (j l : Fin 3) : R :=
  2 * (dot3 (fun i => J i l) (fun i => J i j) + dot3 b (fun i => K i j l))

/-- `∂ₘ∂ₗ∂ⱼQ` (`Lᵢⱼₗₘ = ∂ₘ∂ₗ∂ⱼbᵢ`). -/
@[expose] def gqddF (j l m : Fin 3) : R :=
  2 * ((dot3 (fun i => K i l m) (fun i => J i j) + dot3 (fun i => J i l) (fun i => K i j m)) +
    (dot3 (fun i => J i m) (fun i => K i j l) + dot3 b (fun i => L i j l m)))

/-- `Y = B × ∇Q`. -/
@[expose] def YF : Fin 3 → R := crossF b (gqF b J)

/-- `∂ₗY` (component `i`). -/
@[expose] def YdF (l : Fin 3) : Fin 3 → R := fun i =>
  crossF (fun a => J a l) (gqF b J) i + crossF b (fun a => gqdF b J K a l) i

/-- `∂ₘ∂ₗY` (component `i`). -/
@[expose] def YddF (l m : Fin 3) : Fin 3 → R := fun i =>
  (crossF (fun a => K a l m) (gqF b J) i +
      crossF (fun a => J a l) (fun a => gqdF b J K a m) i) +
    (crossF (fun a => J a m) (fun a => gqdF b J K a l) i +
      crossF b (fun a => gqddF b J K L a l m) i)

/-- `h = B · ∇Q`. -/
@[expose] def hF : R := dot3 b (gqF b J)

/-- `∂ₗh`. -/
@[expose] def hdF (l : Fin 3) : R :=
  dot3 (fun a => J a l) (gqF b J) + dot3 b (fun a => gqdF b J K a l)

/-- `∂ₘ∂ₗh`. -/
@[expose] def hddF (l m : Fin 3) : R :=
  (dot3 (fun a => K a l m) (gqF b J) + dot3 (fun a => J a l) (fun a => gqdF b J K a m)) +
    (dot3 (fun a => J a m) (fun a => gqdF b J K a l) + dot3 b (fun a => gqddF b J K L a l m))

/-- `Z = [B, Y] = (DY) B - (DB) Y` (component `i`). -/
@[expose] def ZF (i : Fin 3) : R := dot3 (fun l => YdF b J K l i) b - dot3 (fun l => J i l) (YF b J)

/-- `∂ₘZ` (component `i`). -/
@[expose] def ZdF (i m : Fin 3) : R :=
  (dot3 (fun l => YddF b J K L l m i) b + dot3 (fun l => YdF b J K l i) (fun l => J l m)) -
    (dot3 (fun l => K i l m) (YF b J) + dot3 (fun l => J i l) (YdF b J K m))

/-- `k = B · ∇h`. -/
@[expose] def kF : R := dot3 (hdF b J K) b

/-- `∂ₘk`. -/
@[expose] def kdF (m : Fin 3) : R :=
  dot3 (fun l => hddF b J K L l m) b + dot3 (hdF b J K) (fun l => J l m)

end Formulas

/-- Sanity check: `e_x × e_y = e_z` and `e_x · e_y = 0` for the formulas. -/
example : crossF (R := ℚ) ![1, 0, 0] ![0, 1, 0] 2 = 1 ∧
    dot3 (R := ℚ) ![1, 0, 0] ![0, 1, 0] = 0 := by
  simp [crossF, dot3]

/-- Product rule for `dot3`. -/
theorem HasPartials.dot {u v : Fin 3 → Space → ℝ} {du dv : Fin 3 → Fin 3 → ℝ} {y : Space}
    (hu : ∀ a, HasPartials (u a) (du a) y) (hv : ∀ a, HasPartials (v a) (dv a) y) :
    HasPartials (fun z => dot3 (fun a => u a z) (fun a => v a z))
      (fun l => dot3 (fun a => du a l) (fun a => v a y) +
        dot3 (fun a => u a y) (fun a => dv a l)) y :=
  (((((hu 0).mul (hv 0)).add ((hu 1).mul (hv 1))).add ((hu 2).mul (hv 2))).congr_fun
    (fun z => rfl)).congr_d (fun l => by simp only [dot3]; ring)

/-- Product rule for `crossF`. -/
theorem HasPartials.cross {u v : Fin 3 → Space → ℝ} {du dv : Fin 3 → Fin 3 → ℝ} {y : Space}
    (hu : ∀ a, HasPartials (u a) (du a) y) (hv : ∀ a, HasPartials (v a) (dv a) y) (i : Fin 3) :
    HasPartials (fun z => crossF (fun a => u a z) (fun a => v a z) i)
      (fun l => crossF (fun a => du a l) (fun a => v a y) i +
        crossF (fun a => u a y) (fun a => dv a l) i) y := by
  fin_cases i
  · exact (((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1))).congr_fun (fun z => by simp [crossF])
      |>.congr_d (fun l => by simp [crossF]; ring)
  · exact (((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2))).congr_fun (fun z => by simp [crossF])
      |>.congr_d (fun l => by simp [crossF]; ring)
  · exact (((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))).congr_fun (fun z => by simp [crossF])
      |>.congr_d (fun l => by simp [crossF]; ring)

/-! ## The field as a polynomial in `(x, y, z, w)` -/

/-- `B₀` for `ε = 1/4`, as a polynomial in `(x, y, z, w)`. -/
@[expose] def Pb0 : List Mono4 :=
  [((-1/4), 7, 0, 0, 3), ((1/2), 6, 1, 1, 3), ((-1/4), 5, 2, 0, 3), ((1/2), 5, 0, 0, 3),
    ((3/8), 5, 0, 0, 2), (1, 4, 3, 1, 3), ((-3), 4, 1, 1, 3), ((-5/8), 4, 1, 1, 2),
    ((1/4), 3, 4, 0, 3), ((1/4), 3, 2, 0, 2), (1, 3, 0, 2, 3), ((-1/4), 3, 0, 0, 3),
    ((-1/2), 3, 0, 0, 2), ((1/2), 2, 5, 1, 3), ((-3), 2, 3, 1, 3), ((-3/4), 2, 3, 1, 2),
    ((-2), 2, 1, 3, 3), ((5/2), 2, 1, 1, 3), ((9/4), 2, 1, 1, 2), ((1/4), 1, 6, 0, 3),
    ((-1/2), 1, 4, 0, 3), ((-1/8), 1, 4, 0, 2), ((-1), 1, 2, 2, 3), ((1/4), 1, 2, 0, 3),
    ((-1/2), 1, 0, 2, 2), ((1/8), 1, 0, 0, 2), ((-1/8), 0, 5, 1, 2), ((3/4), 0, 3, 1, 2),
    ((1/2), 0, 1, 3, 2), ((-5/8), 0, 1, 1, 2), ((-1), 0, 1, 0, 1)]

/-- `B₁` for `ε = 1/4`, as a polynomial in `(x, y, z, w)`. -/
@[expose] def Pb1 : List Mono4 :=
  [((-1/4), 6, 1, 0, 3), ((1/2), 5, 2, 1, 3), ((-1/8), 5, 0, 1, 2), ((-1/4), 4, 3, 0, 3),
    ((1/2), 4, 1, 0, 3), ((1/8), 4, 1, 0, 2), (1, 3, 4, 1, 3), ((-3), 3, 2, 1, 3),
    ((-3/4), 3, 2, 1, 2), ((3/4), 3, 0, 1, 2), ((1/4), 2, 5, 0, 3), ((-1/4), 2, 3, 0, 2),
    (1, 2, 1, 2, 3), ((-1/4), 2, 1, 0, 3), ((1/2), 1, 6, 1, 3), ((-3), 1, 4, 1, 3),
    ((-5/8), 1, 4, 1, 2), ((-2), 1, 2, 3, 3), ((5/2), 1, 2, 1, 3), ((9/4), 1, 2, 1, 2),
    ((1/2), 1, 0, 3, 2), ((-5/8), 1, 0, 1, 2), (1, 1, 0, 0, 1), ((1/4), 0, 7, 0, 3),
    ((-1/2), 0, 5, 0, 3), ((-3/8), 0, 5, 0, 2), ((-1), 0, 3, 2, 3), ((1/4), 0, 3, 0, 3),
    ((1/2), 0, 3, 0, 2), ((1/2), 0, 1, 2, 2), ((-1/8), 0, 1, 0, 2)]

/-- `B₂` for `ε = 1/4`, as a polynomial in `(x, y, z, w)`. -/
@[expose] def Pb2 : List Mono4 :=
  [((-1/8), 5, 1, 0, 2), ((-1/4), 3, 3, 0, 2), ((3/4), 3, 1, 0, 2), ((-1/2), 2, 0, 1, 2),
    ((-1/8), 1, 5, 0, 2), ((3/4), 1, 3, 0, 2), ((3/2), 1, 1, 2, 2), ((-5/8), 1, 1, 0, 2),
    ((1/2), 0, 2, 1, 2)]

/-- The coordinate polynomials. -/
@[expose] def Pb (i : Fin 3) : List Mono4 := ![Pb0, Pb1, Pb2] i

/-- `bᵢ = Bᵢ`. -/
@[expose] def bR (i : Fin 3) (y : Space) : ℝ := p4Eval (Pb i) y
/-- `∂ⱼBᵢ`. -/
@[expose] def JR (i j : Fin 3) (y : Space) : ℝ := p4Eval (p4D j (Pb i)) y
/-- `∂ₗ∂ⱼBᵢ`. -/
@[expose] def KR (i j l : Fin 3) (y : Space) : ℝ := p4Eval (p4D l (p4D j (Pb i))) y
/-- `∂ₘ∂ₗ∂ⱼBᵢ`. -/
@[expose] def LR (i j l m : Fin 3) (y : Space) : ℝ := p4Eval (p4D m (p4D l (p4D j (Pb i)))) y

/-- The values of `B` at `y`. -/
@[expose] def bY (y : Space) : Fin 3 → ℝ := fun i => bR i y
/-- The first derivatives of `B` at `y`. -/
@[expose] def JY (y : Space) : Fin 3 → Fin 3 → ℝ := fun i j => JR i j y
/-- The second derivatives of `B` at `y`. -/
@[expose] def KY (y : Space) : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j l => KR i j l y
/-- The third derivatives of `B` at `y`. -/
@[expose] def LY (y : Space) : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j l m => LR i j l m y

/-- **The field coordinates are the polynomials `Pb`** (with `w = winv`), everywhere. -/
theorem field_coord (y : Space) (i : Fin 3) : field (1 / 4) y i = bR i y := by
  fin_cases i <;>
    simp [field, toroidal, gradH, G, Hd, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, r2, cv, bR, Pb, Pb0,
      Pb1, Pb2, p4Eval, m4Eval] <;> ring

/-- `field_coord` in `simp` normal form (`1/4 = 4⁻¹`). -/
theorem field_coord' (y : Space) (i : Fin 3) : field 4⁻¹ y i = bR i y := by
  rw [inv_eq_one_div]; exact field_coord y i

/-! ## Derivatives of the jet fields on the domain -/

section Jets

variable {y : Space} (hy : r2 y ≠ 0)
include hy

/-- `∂ₗBₐ = Jₐₗ`. -/
theorem hasPartials_b (a : Fin 3) : HasPartials (bR a) (fun l => JR a l y) y :=
  p4Eval_hasPartials (Pb a) hy

/-- `∂ₗJₐⱼ = Kₐⱼₗ`. -/
theorem hasPartials_J (a j : Fin 3) : HasPartials (JR a j) (fun l => KR a j l y) y :=
  p4Eval_hasPartials _ hy

/-- `∂ₘKₐⱼₗ = Lₐⱼₗₘ`. -/
theorem hasPartials_K (a j l : Fin 3) : HasPartials (KR a j l) (fun m => LR a j l m y) y :=
  p4Eval_hasPartials _ hy

/-- Derivative of `∇Q`. -/
theorem hasPartials_gq (j : Fin 3) :
    HasPartials (fun z => gqF (bY z) (JY z) j) (fun l => gqdF (bY y) (JY y) (KY y) j l) y :=
  (HasPartials.dot (hasPartials_b hy) (fun a => hasPartials_J hy a j)).const_mul 2

/-- Derivative of `∂ₗ∇Q`. -/
theorem hasPartials_gqd (j l : Fin 3) :
    HasPartials (fun z => gqdF (bY z) (JY z) (KY z) j l)
      (fun m => gqddF (bY y) (JY y) (KY y) (LY y) j l m) y :=
  ((HasPartials.dot (fun a => hasPartials_J hy a l) (fun a => hasPartials_J hy a j)).add
    (HasPartials.dot (hasPartials_b hy) (fun a => hasPartials_K hy a j l))).const_mul 2

/-- Derivative of `Y`. -/
theorem hasPartials_Y (i : Fin 3) :
    HasPartials (fun z => YF (bY z) (JY z) i) (fun l => YdF (bY y) (JY y) (KY y) l i) y :=
  HasPartials.cross (hasPartials_b hy) (hasPartials_gq hy) i

/-- Derivative of `∂ₗY`. -/
theorem hasPartials_Yd (l i : Fin 3) :
    HasPartials (fun z => YdF (bY z) (JY z) (KY z) l i)
      (fun m => YddF (bY y) (JY y) (KY y) (LY y) l m i) y :=
  (HasPartials.cross (fun a => hasPartials_J hy a l) (hasPartials_gq hy) i).add
    (HasPartials.cross (hasPartials_b hy) (fun a => hasPartials_gqd hy a l) i)

/-- Derivative of `h`. -/
theorem hasPartials_h :
    HasPartials (fun z => hF (bY z) (JY z)) (fun l => hdF (bY y) (JY y) (KY y) l) y :=
  HasPartials.dot (hasPartials_b hy) (hasPartials_gq hy)

/-- Derivative of `∂ₗh`. -/
theorem hasPartials_hd (l : Fin 3) :
    HasPartials (fun z => hdF (bY z) (JY z) (KY z) l)
      (fun m => hddF (bY y) (JY y) (KY y) (LY y) l m) y :=
  (HasPartials.dot (fun a => hasPartials_J hy a l) (hasPartials_gq hy)).add
    (HasPartials.dot (hasPartials_b hy) (fun a => hasPartials_gqd hy a l))

/-- Derivative of `Z`. -/
theorem hasPartials_Z (i : Fin 3) :
    HasPartials (fun z => ZF (bY z) (JY z) (KY z) i)
      (fun m => ZdF (bY y) (JY y) (KY y) (LY y) i m) y :=
  (HasPartials.dot (fun l => hasPartials_Yd hy l i) (hasPartials_b hy)).sub
    (HasPartials.dot (fun l => hasPartials_J hy i l) (hasPartials_Y hy))

/-- Derivative of `k`. -/
theorem hasPartials_k :
    HasPartials (fun z => kF (bY z) (JY z) (KY z)) (fun m => kdF (bY y) (JY y) (KY y) (LY y) m)
      y :=
  HasPartials.dot (hasPartials_hd hy) (hasPartials_b hy)

end Jets

/-! ## Vector fields -/

/-- The linear map with matrix `M` (`(M v)ᵢ = ∑ⱼ Mᵢⱼ vⱼ`). -/
@[expose] def coordCLM (M : Fin 3 → Fin 3 → ℝ) : Space →L[ℝ] Space :=
  ∑ k, (lin (M k 0) (M k 1) (M k 2)).smulRight (basis k)

/-- Coordinates of `coordCLM`. -/
theorem coordCLM_apply (M : Fin 3 → Fin 3 → ℝ) (v : Space) (i : Fin 3) :
    coordCLM M v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  rw [coordCLM, coords_apply, lin_apply]

/-- A vector from a coordinate triple. -/
@[expose] def vecF (u : Fin 3 → ℝ) : Space := vec3 (u 0) (u 1) (u 2)

/-- Coordinates of `vecF`. -/
@[simp] theorem vecF_apply (u : Fin 3 → ℝ) (i : Fin 3) : vecF u i = u i := by
  fin_cases i <;> rfl

/-- Derivative of a vector field from the partials of its coordinates. -/
theorem hasFDerivAt_vecF {F : Space → Fin 3 → ℝ} {M : Fin 3 → Fin 3 → ℝ} {y : Space}
    (h : ∀ k, HasPartials (fun z => F z k) (M k) y) :
    HasFDerivAt (fun z => vecF (F z)) (coordCLM M) y :=
  hasFDerivAt_of_coords fun k => (h k).hasFDerivAt.congr_of_eventuallyEq
    (Eventually.of_forall fun _ => vecF_apply _ k)

/-- Triple product in coordinates. -/
theorem inner_cross_vecF (u v w : Fin 3 → ℝ) :
    ⟪vecF u, cross (vecF v) (vecF w)⟫ = dot3 u (crossF v w) := by
  simp [inner_coords, dot3, crossF]

/-- `field (1/4) = vecF (bY ·)`. -/
theorem field_eq : field (1 / 4) = fun z => vecF (bY z) := by
  funext z
  apply space_ext <;> simp [field_coord', bY]

/-- **The actual derivative of the field** off the `z`-axis, with the matrix `JY`. -/
theorem hasFDerivAt_field {y : Space} (hy : r2 y ≠ 0) :
    HasFDerivAt (field (1 / 4)) (coordCLM (JY y)) y := by
  rw [field_eq]
  exact hasFDerivAt_vecF fun k => hasPartials_b hy k

/-- `∇Q` on the domain. -/
theorem gradient_fieldQ_eq {y : Space} (hy : r2 y ≠ 0) :
    gradient (fieldQ (field (1 / 4))) y = vecF (gqF (bY y) (JY y)) := by
  have hB := hasFDerivAt_field hy
  have key : ∀ i, gradient (fieldQ (field (1 / 4))) y i =
      2 * ⟪field (1 / 4) y, coordCLM (JY y) (basis i)⟫ := fun i => by
    rw [← inner_gradient_fieldQ hB (basis i), EuclideanSpace.inner_single_right]
    simp
  apply space_ext <;> rw [key] <;>
    simp [inner_coords, coordCLM_apply, gqF, dot3, field_coord', bY, JY]

/-- `Y = B × ∇Q` on the domain. -/
theorem fieldY_eq {y : Space} (hy : r2 y ≠ 0) :
    fieldY (field (1 / 4)) y = vecF (YF (bY y) (JY y)) := by
  rw [fieldY, gradient_fieldQ_eq hy]
  apply space_ext <;> simp [YF, crossF, field_coord', bY]

/-- `h = B · ∇Q` on the domain. -/
theorem fieldH_eq {y : Space} (hy : r2 y ≠ 0) :
    fieldH (field (1 / 4)) y = hF (bY y) (JY y) := by
  rw [fieldH, gradient_fieldQ_eq hy, inner_coords]
  simp [hF, dot3, field_coord', bY]

/-- `Y` near a point of the domain. -/
theorem fieldY_eventuallyEq {y : Space} (hy : y ∈ domain) :
    fieldY (field (1 / 4)) =ᶠ[𝓝 y] fun z => vecF (YF (bY z) (JY z)) :=
  Filter.eventuallyEq_of_mem (isOpen_domain.mem_nhds hy) fun _ hz => fieldY_eq (ne_of_gt hz)

/-- `h` near a point of the domain. -/
theorem fieldH_eventuallyEq {y : Space} (hy : y ∈ domain) :
    fieldH (field (1 / 4)) =ᶠ[𝓝 y] fun z => hF (bY z) (JY z) :=
  Filter.eventuallyEq_of_mem (isOpen_domain.mem_nhds hy) fun _ hz => fieldH_eq (ne_of_gt hz)

/-- The derivative of `Y` on the domain. -/
theorem hasFDerivAt_fieldY {y : Space} (hy : y ∈ domain) :
    HasFDerivAt (fieldY (field (1 / 4))) (coordCLM fun i l => YdF (bY y) (JY y) (KY y) l i) y :=
  (hasFDerivAt_vecF fun k => hasPartials_Y (ne_of_gt hy) k).congr_of_eventuallyEq
    (fieldY_eventuallyEq hy)

/-- The derivative of `h` on the domain. -/
theorem hasPartials_fieldH {y : Space} (hy : y ∈ domain) :
    HasPartials (fieldH (field (1 / 4))) (fun l => hdF (bY y) (JY y) (KY y) l) y :=
  (hasPartials_h (ne_of_gt hy)).hasFDerivAt.congr_of_eventuallyEq (fieldH_eventuallyEq hy)

/-- **The bracket field** `Z = [B, Y]`, written through the jet of `B`. -/
@[expose] def ZV (z : Space) : Space := vecF fun i => ZF (bY z) (JY z) (KY z) i

/-- **The function** `k = B · ∇h`, written through the jet of `B`. -/
@[expose] def kV (z : Space) : ℝ := kF (bY z) (JY z) (KY z)

/-- `Z = [B, Y]` on the domain. -/
theorem ZV_eq {z : Space} (hz : z ∈ domain) :
    ZV z = VectorField.lieBracket ℝ (field (1 / 4)) (fieldY (field (1 / 4))) z := by
  rw [VectorField.lieBracket, (hasFDerivAt_fieldY hz).fderiv,
    (hasFDerivAt_field (ne_of_gt hz)).fderiv, fieldY_eq (ne_of_gt hz)]
  apply space_ext <;>
    simp only [ZV, ZF, vecF_apply, PiLp.sub_apply, coordCLM_apply, field_coord, dot3, bY, JY]

/-- `k = B · ∇h` on the domain. -/
theorem kV_eq {z : Space} (hz : z ∈ domain) :
    kV z = fderiv ℝ (fieldH (field (1 / 4))) z (field (1 / 4) z) := by
  rw [(hasPartials_fieldH hz).hasFDerivAt.fderiv, lin_apply]
  simp only [kV, kF, dot3, field_coord, bY]

/-- The derivative of `Z` on the domain. -/
theorem hasFDerivAt_ZV {y : Space} (hy : r2 y ≠ 0) :
    HasFDerivAt ZV (coordCLM fun i m => ZdF (bY y) (JY y) (KY y) (LY y) i m) y :=
  hasFDerivAt_vecF fun k => hasPartials_Z hy k

/-! ## Coordinates of the linear data -/

/-- **The linear system of the jet obstruction in coordinates.** -/
theorem jetSolution_of_coords {X Y Z : Space → Space} {h k : Space → ℝ} {p : Space}
    {x yv zv w : Fin 3 → ℝ} {hv kv : ℝ} {MX MY MZ MS : Fin 3 → Fin 3 → ℝ} {dh dk : Fin 3 → ℝ}
    (hX : X p = vecF x) (hY : Y p = vecF yv) (hZ : Z p = vecF zv) (hh : h p = hv)
    (hk : k p = kv) (e1 : dot3 x w = 0) (e2 : dot3 yv w = -hv) (e3 : dot3 zv w = -kv)
    (e4 : ∀ j, dot3 x (fun i => MS i j) = -dot3 (fun i => MX i j) w)
    (e5 : ∀ j, dot3 yv (fun i => MS i j) = -dh j - dot3 (fun i => MY i j) w)
    (e6 : ∀ j, dot3 zv (fun i => MS i j) = -dk j - dot3 (fun i => MZ i j) w) :
    JetSolution X Y Z h k p (coordCLM MX) (coordCLM MY) (coordCLM MZ) (lin (dh 0) (dh 1) (dh 2))
      (lin (dk 0) (dk 1) (dk 2)) (vecF w) (coordCLM MS) := by
  simp only [dot3] at e1 e2 e3 e4 e5 e6
  refine ⟨?_, ?_, ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [hX, inner_coords]; simpa using e1
  · rw [hY, inner_coords, hh]; simpa using e2
  · rw [hZ, inner_coords, hk]; simpa using e3
  · rw [hX, inner_coords, inner_coords]
    simp only [vecF_apply, coordCLM_apply]
    linear_combination v 0 * e4 0 + v 1 * e4 1 + v 2 * e4 2
  · rw [hY, inner_coords, inner_coords]
    simp only [vecF_apply, coordCLM_apply, lin_apply]
    linear_combination v 0 * e5 0 + v 1 * e5 1 + v 2 * e5 2
  · rw [hZ, inner_coords, inner_coords]
    simp only [vecF_apply, coordCLM_apply, lin_apply]
    linear_combination v 0 * e6 0 + v 1 * e6 1 + v 2 * e6 2

/-! ## Casting the formulas from `ℚ` to `ℝ` -/

section Cast

variable (b : Fin 3 → ℚ) (J : Fin 3 → Fin 3 → ℚ) (K : Fin 3 → Fin 3 → Fin 3 → ℚ)
  (L : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℚ)

/-- Cast of `dot3`. -/
theorem cast_dot3 (u v : Fin 3 → ℚ) :
    ((dot3 u v : ℚ) : ℝ) = dot3 (fun a => (u a : ℝ)) (fun a => (v a : ℝ)) := by
  simp [dot3]

/-- Cast of `crossF`. -/
theorem cast_crossF (u v : Fin 3 → ℚ) (i : Fin 3) :
    ((crossF u v i : ℚ) : ℝ) = crossF (fun a => (u a : ℝ)) (fun a => (v a : ℝ)) i := by
  fin_cases i <;> simp [crossF]

/-- Cast of `gqF`. -/
theorem cast_gqF (j : Fin 3) :
    ((gqF b J j : ℚ) : ℝ) = gqF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) j := by
  simp only [gqF, Rat.cast_mul, Rat.cast_ofNat, cast_dot3]

/-- Cast of `gqdF`. -/
theorem cast_gqdF (j l : Fin 3) :
    ((gqdF b J K j l : ℚ) : ℝ) =
      gqdF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ)) j l := by
  simp only [gqdF, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, cast_dot3]

/-- Cast of `gqddF`. -/
theorem cast_gqddF (j l m : Fin 3) :
    ((gqddF b J K L j l m : ℚ) : ℝ) =
      gqddF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ))
        (fun a c e f => (L a c e f : ℝ)) j l m := by
  simp only [gqddF, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, cast_dot3]

/-- Cast of `YF`. -/
theorem cast_YF (i : Fin 3) :
    ((YF b J i : ℚ) : ℝ) = YF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) i := by
  simp only [YF, cast_crossF, cast_gqF]

/-- Cast of `YdF`. -/
theorem cast_YdF (l i : Fin 3) :
    ((YdF b J K l i : ℚ) : ℝ) =
      YdF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ)) l i := by
  simp only [YdF, Rat.cast_add, cast_crossF, cast_gqF, cast_gqdF]

/-- Cast of `YddF`. -/
theorem cast_YddF (l m i : Fin 3) :
    ((YddF b J K L l m i : ℚ) : ℝ) =
      YddF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ))
        (fun a c e f => (L a c e f : ℝ)) l m i := by
  simp only [YddF, Rat.cast_add, cast_crossF, cast_gqF, cast_gqdF, cast_gqddF]

/-- Cast of `hF`. -/
theorem cast_hF : ((hF b J : ℚ) : ℝ) = hF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) := by
  simp only [hF, cast_dot3, cast_gqF]

/-- Cast of `hdF`. -/
theorem cast_hdF (l : Fin 3) :
    ((hdF b J K l : ℚ) : ℝ) =
      hdF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ)) l := by
  simp only [hdF, Rat.cast_add, cast_dot3, cast_gqF, cast_gqdF]

/-- Cast of `hddF`. -/
theorem cast_hddF (l m : Fin 3) :
    ((hddF b J K L l m : ℚ) : ℝ) =
      hddF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ))
        (fun a c e f => (L a c e f : ℝ)) l m := by
  simp only [hddF, Rat.cast_add, cast_dot3, cast_gqF, cast_gqdF, cast_gqddF]

/-- Cast of `ZF`. -/
theorem cast_ZF (i : Fin 3) :
    ((ZF b J K i : ℚ) : ℝ) =
      ZF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ)) i := by
  simp only [ZF, Rat.cast_sub, cast_dot3, cast_YF, cast_YdF]

/-- Cast of `ZdF`. -/
theorem cast_ZdF (i m : Fin 3) :
    ((ZdF b J K L i m : ℚ) : ℝ) =
      ZdF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ))
        (fun a c e f => (L a c e f : ℝ)) i m := by
  simp only [ZdF, Rat.cast_add, Rat.cast_sub, cast_dot3, cast_YF, cast_YdF, cast_YddF]

/-- Cast of `kF`. -/
theorem cast_kF :
    ((kF b J K : ℚ) : ℝ) =
      kF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ)) := by
  simp only [kF, cast_dot3, cast_hdF]

/-- Cast of `kdF`. -/
theorem cast_kdF (m : Fin 3) :
    ((kdF b J K L m : ℚ) : ℝ) =
      kdF (fun a => (b a : ℝ)) (fun a c => (J a c : ℝ)) (fun a c e => (K a c e : ℝ))
        (fun a c e f => (L a c e f : ℝ)) m := by
  simp only [kdF, Rat.cast_add, cast_dot3, cast_hdF, cast_hddF]

end Cast

/-! ## The jet at `p₀ = (1, 0, 1/4)` -/

/-- The point `p₀ = (1, 0, 1/4)`: `R = 1`, `φ = 0`, `z = 1/4`. -/
@[expose] def p₀ : Space := vec3 1 0 (1 / 4)

/-- `p₀` lies in the current-free domain (`r₂ = 1`). -/
theorem p₀_mem_domain : p₀ ∈ domain := by
  simp [domain, r2, p₀]

/-- `1/r₂ = 1` at `p₀`. -/
theorem winv_p₀ : winv p₀ = ((1 : ℚ) : ℝ) := by
  simp [winv, r2, p₀]

/-- `B(p₀)`. -/
@[expose] def bt : Fin 3 → ℚ :=
  ![(1/32), (129/128), (-1/8)]

/-- `DB(p₀)`: `Jt i j = ∂ⱼBᵢ(p₀)`. -/
@[expose] def Jt : Fin 3 → Fin 3 → ℚ :=
  ![![(13/32), (-99/128), (1/4)], ![(-99/128), (3/32), (3/32)], ![(1/4), (3/32), (-1/2)]]

/-- `D²B(p₀)`: `Kt i j l = ∂ₗ∂ⱼBᵢ(p₀)`. -/
@[expose] def Kt : Fin 3 → Fin 3 → Fin 3 → ℚ :=
  ![![![(-9/8), (19/32), (-3/4)], ![(19/32), (1/8), (23/32)], ![(-3/4), (23/32), 1]], ![![
    (19/32), (1/8), (23/32)], ![(1/8), (-43/32), (3/4)], ![(23/32), (3/4), (3/4)]], ![![(-3/4),
    (23/32), 1], ![(23/32), (3/4), (3/4)], ![1, (3/4), 0]]]

/-- `D³B(p₀)`: `Lt i j l m = ∂ₘ∂ₗ∂ⱼBᵢ(p₀)`. -/
@[expose] def Lt : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℚ :=
  ![![![![(45/8), (57/32), 3], ![(57/32), (-21/8), (-39/8)], ![3, (-39/8), (-3)]], ![![(57/32),
    (-21/8), (-39/8)], ![(-21/8), (15/32), (-3)], ![(-39/8), (-3), (-9/4)]], ![![3, (-39/8), (-3)],
    ![(-39/8), (-3), (-9/4)], ![(-3), (-9/4), 0]]], ![![![(57/32), (-21/8), (-39/8)], ![(-21/8),
    (15/32), (-3)], ![(-39/8), (-3), (-9/4)]], ![![(-21/8), (15/32), (-3)], ![(15/32), (-3/8),
    (15/8)], ![(-3), (15/8), 3]], ![![(-39/8), (-3), (-9/4)], ![(-3), (15/8), 3], ![(-9/4), 3, 3]]],
    ![![![3, (-39/8), (-3)], ![(-39/8), (-3), (-9/4)], ![(-3), (-9/4), 0]], ![![(-39/8), (-3),
    (-9/4)], ![(-3), (15/8), 3], ![(-9/4), 3, 3]], ![![(-3), (-9/4), 0], ![(-9/4), 3, 3], ![0, 3,
    0]]]]

/-- `η(p₀)` (computed in sympy, verified in `jetCheck_true`). -/
@[expose] def wt : Fin 3 → ℚ :=
  ![(-106520713099/40636158768), (497802473/3386346564), (5383052747/10159039692)]

/-- `Dη(p₀)`: `St i j = ∂ⱼηᵢ(p₀)` (computed in sympy, verified in `jetCheck_true`). -/
@[expose] def St : Fin 3 → Fin 3 → ℚ :=
  ![![(1142778405401412979547/34402029154543818288),
    (33508965078846830699059/1032060874636314548640),
    (2248397696156518409011/64503804664769659290)], ![(-446500729522768067/955611920959550508),
    (-128453060924506420811/34402029154543818288), (-1279288638875774501/2150126822158988643)], ![
    (-8238603555575199376/2150126822158988643), (-1357231717706114040851/258015218659078637160),
    (-107552374414971675163/32251902332384829645)]]

/-- `det(B, Y, Z)` at `p₀`. -/
@[expose] def detq : ℚ := (-214774797888495/562949953421312)

/-- The table of `B(p₀)` is the evaluation of the polynomials. -/
theorem tab_b : ∀ i : Fin 3, p4EvalQ (Pb i) 1 0 (1 / 4) 1 = bt i := by kernel_fact

/-- The table of `DB(p₀)` is the evaluation of the formal derivatives. -/
theorem tab_J : ∀ i j : Fin 3, p4EvalQ (p4D j (Pb i)) 1 0 (1 / 4) 1 = Jt i j := by kernel_fact

/-- The table of `D²B(p₀)` is the evaluation of the formal derivatives. -/
theorem tab_K : ∀ i j l : Fin 3, p4EvalQ (p4D l (p4D j (Pb i))) 1 0 (1 / 4) 1 = Kt i j l := by
  kernel_fact

/-- The table of `D³B(p₀)` is the evaluation of the formal derivatives. -/
theorem tab_L : ∀ i j l m : Fin 3,
    p4EvalQ (p4D m (p4D l (p4D j (Pb i)))) 1 0 (1 / 4) 1 = Lt i j l m := by
  kernel_fact

/-- Real evaluation at `p₀` is the rational evaluation. -/
theorem p4Eval_p₀ (P : List Mono4) : p4Eval P p₀ = (p4EvalQ P 1 0 (1 / 4) 1 : ℝ) :=
  p4Eval_cast P (by simp [p₀]) (by simp [p₀]) (by simp [p₀]) winv_p₀

/-- `B(p₀) = bt`. -/
theorem bY_p₀ : bY p₀ = fun i => (bt i : ℝ) := by
  funext i; rw [bY, bR, p4Eval_p₀, tab_b]

/-- `DB(p₀) = Jt`. -/
theorem JY_p₀ : JY p₀ = fun i j => (Jt i j : ℝ) := by
  funext i j; rw [JY, JR, p4Eval_p₀, tab_J]

/-- `D²B(p₀) = Kt`. -/
theorem KY_p₀ : KY p₀ = fun i j l => (Kt i j l : ℝ) := by
  funext i j l; rw [KY, KR, p4Eval_p₀, tab_K]

/-- `D³B(p₀) = Lt`. -/
theorem LY_p₀ : LY p₀ = fun i j l m => (Lt i j l m : ℝ) := by
  funext i j l m; rw [LY, LR, p4Eval_p₀, tab_L]

/-- **The exact linear data at `p₀`, over `ℚ`**: `η(p₀) = wt` and `Dη(p₀) = St` solve the
linear system of the jet obstruction, and `det(B, Y, Z) = detq`. -/
@[expose] def jetCheck : Prop :=
  dot3 bt wt = 0 ∧ dot3 (YF bt Jt) wt = -hF bt Jt ∧ dot3 (ZF bt Jt Kt) wt = -kF bt Jt Kt ∧
    (∀ j : Fin 3, dot3 bt (fun i => St i j) = -dot3 (fun i => Jt i j) wt) ∧
    (∀ j : Fin 3, dot3 (YF bt Jt) (fun i => St i j) =
      -hdF bt Jt Kt j - dot3 (fun i => YdF bt Jt Kt j i) wt) ∧
    (∀ j : Fin 3, dot3 (ZF bt Jt Kt) (fun i => St i j) =
      -kdF bt Jt Kt Lt j - dot3 (fun i => ZdF bt Jt Kt Lt i j) wt) ∧
    dot3 bt (crossF (YF bt Jt) (ZF bt Jt Kt)) = detq

/-- The rational checks hold (each equation is a kernel-evaluated rational identity). -/
theorem jetCheck_true : jetCheck := by kernel_fact

/-- Rejected fixture: a perturbed `η(p₀)` fails the first equation of the system
(`⟪B, η⟫ = 0`). -/
example : dot3 bt (fun i => wt i + 1) ≠ 0 := by
  have h := jetCheck_true.1
  simp only [dot3] at h ⊢
  intro h'
  have : bt 0 + bt 1 + bt 2 = 0 := by linear_combination h' - h
  norm_num [bt] at this

/-- The curl of `S` (its `y` component). -/
theorem curl_St : St 0 2 - St 2 0 = (2495555802823774390291/64503804664769659290) := by
  norm_num [St]

/-! ## The obstruction -/

/-- `B(p₀) ≠ 0`. -/
theorem field_p₀_ne_zero : field (1 / 4) p₀ ≠ 0 := by
  intro h
  have h1 := congrArg (fun v : Space => v 1) h
  simp only [field_coord, PiLp.zero_apply] at h1
  rw [bR, p4Eval_p₀, tab_b] at h1
  norm_num [bt] at h1

/-- **No strong QS near `p₀ = (1, 0, 1/4)` with `C ≠ 0`, and `C = 0` forces `∇Ψ = 0`.** If the
rational stellarator field `B = field (1/4)` is strongly quasisymmetric (`B × u = ∇Ψ`,
`B · u = C`, `div u = 0`) at every point of a neighbourhood `U` of `p₀`, with `Ψ` of class `C²`
at `p₀` (no regularity of `u` is assumed), then `C = 0` and `∇Ψ` vanishes near `p₀`. Local
statement only: it complements the first-order near-axis obstruction
`RationalStellaratorQAObstruction` and is not a global non-existence theorem. -/
theorem strongQS_obstruction {u : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {U : Set Space}
    (hU : U ∈ 𝓝 p₀) (hΨ : ContDiffAt ℝ 2 Ψ p₀)
    (h : ∀ y ∈ U, StrongQSAt (field (1 / 4)) u Ψ C y) :
    C = 0 ∧ ∀ᶠ y in 𝓝 p₀, gradient Ψ y = 0 := by
  have hp := p₀_mem_domain
  have hp' : r2 p₀ ≠ 0 := ne_of_gt hp
  have hΩ : domain ∈ 𝓝 p₀ := isOpen_domain.mem_nhds hp
  have jc := jetCheck_true
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := jc
  have hS : JetSolution (field (1 / 4)) (fieldY (field (1 / 4))) ZV (fieldH (field (1 / 4))) kV
      p₀ (coordCLM (JY p₀)) (coordCLM fun i l => YdF (bY p₀) (JY p₀) (KY p₀) l i)
      (coordCLM fun i m => ZdF (bY p₀) (JY p₀) (KY p₀) (LY p₀) i m)
      (lin (hdF (bY p₀) (JY p₀) (KY p₀) 0) (hdF (bY p₀) (JY p₀) (KY p₀) 1)
        (hdF (bY p₀) (JY p₀) (KY p₀) 2))
      (lin (kdF (bY p₀) (JY p₀) (KY p₀) (LY p₀) 0) (kdF (bY p₀) (JY p₀) (KY p₀) (LY p₀) 1)
        (kdF (bY p₀) (JY p₀) (KY p₀) (LY p₀) 2))
      (vecF fun i => (wt i : ℝ)) (coordCLM fun i j => (St i j : ℝ)) := by
    refine jetSolution_of_coords (congrFun field_eq p₀) (fieldY_eq hp') rfl (fieldH_eq hp') rfl
      ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [kV, bY_p₀, JY_p₀, KY_p₀, LY_p₀]
    · have := congrArg (Rat.cast : ℚ → ℝ) c1
      simpa only [cast_dot3, Rat.cast_zero] using this
    · have := congrArg (Rat.cast : ℚ → ℝ) c2
      simpa only [cast_dot3, cast_YF, cast_hF, Rat.cast_neg] using this
    · have := congrArg (Rat.cast : ℚ → ℝ) c3
      simpa only [cast_dot3, cast_ZF, cast_kF, Rat.cast_neg] using this
    · intro j
      have := congrArg (Rat.cast : ℚ → ℝ) (c4 j)
      simpa only [cast_dot3, Rat.cast_neg] using this
    · intro j
      have := congrArg (Rat.cast : ℚ → ℝ) (c5 j)
      simpa only [cast_dot3, cast_YF, cast_YdF, cast_hdF, Rat.cast_neg, Rat.cast_sub] using this
    · intro j
      have := congrArg (Rat.cast : ℚ → ℝ) (c6 j)
      simpa only [cast_dot3, cast_ZF, cast_ZdF, cast_kdF, Rat.cast_neg, Rat.cast_sub] using this
  have hdet : ⟪field (1 / 4) p₀, cross (fieldY (field (1 / 4)) p₀) (ZV p₀)⟫ ≠ 0 := by
    rw [congrFun field_eq p₀, fieldY_eq hp', ZV, inner_cross_vecF]
    simp only [bY_p₀, JY_p₀, KY_p₀]
    have := congrArg (Rat.cast : ℚ → ℝ) c7
    simp only [cast_dot3, cast_crossF, cast_YF, cast_ZF] at this
    rw [this, detq]
    norm_num
  have hcurl : curlOp (coordCLM fun i j => (St i j : ℝ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : Space => v 1) h0
    simp only [curlOp, PiLp.toLp_apply, Matrix.cons_val_one, coordCLM_apply,
      PiLp.zero_apply] at h1
    have h2 : ((St 0 2 - St 2 0 : ℚ) : ℝ) = 0 := by
      rw [Rat.cast_sub]; simpa using h1
    rw [curl_St] at h2
    norm_num at h2
  exact strongQS_jet_obstruction (field_vacuum (1 / 4)) hp field_p₀_ne_zero hU hΨ h
    (Filter.mem_of_superset hΩ fun _ hz => (hasFDerivAt_field (ne_of_gt hz)).differentiableAt)
    (Filter.mem_of_superset hΩ fun _ hz => (hasFDerivAt_fieldY hz).differentiableAt)
    (Filter.mem_of_superset hΩ fun _ hz => (hasPartials_fieldH hz).hasFDerivAt.differentiableAt)
    (hasFDerivAt_field hp') (hasFDerivAt_fieldY hp) (hasFDerivAt_ZV hp')
    (hasPartials_fieldH hp).hasFDerivAt (hasPartials_k hp').hasFDerivAt
    (Filter.mem_of_superset hΩ fun _ hz => ZV_eq hz)
    (Filter.mem_of_superset hΩ fun _ hz => kV_eq hz) hdet hS hcurl

/-- **No strong QS with `C ≠ 0` on any neighbourhood of `p₀ = (1, 0, 1/4)`** for the rational
stellarator field `field (1/4)`. -/
theorem not_strongQS_of_ne_zero {u : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {U : Set Space}
    (hU : U ∈ 𝓝 p₀) (hΨ : ContDiffAt ℝ 2 Ψ p₀) (hC : C ≠ 0) :
    ¬ ∀ y ∈ U, StrongQSAt (field (1 / 4)) u Ψ C y :=
  fun h => hC (strongQS_obstruction hU hΨ h).1

end PlasmaLean.Design.RationalStellaratorJetObstruction
