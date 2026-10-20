/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.AveragedTrapping
public meta import Lean

/-!
# Exact Taylor-shift covers of the cube for dense integer polynomials

A certificate checker for polynomial inequalities on the cube `[-1, 1]³`, used by
`Design/RationalStellaratorConfined` for the field-line defect of the rational stellarator.

**Representation.** A dense polynomial in three variables `(σ, ζ, τ)` is a list (in `σ`) of
lists (in `ζ`) of lists (in `τ`) of integers (`D3`); ragged lists are allowed and missing
coefficients are zero. `ev3 A σ ζ τ` is its real value.

**Subdivision without rounding.** Bisecting the cube in one variable and rescaling the half to
`[-1, 1]` is the substitution `σ ↦ (σ' ± 1)/2`. Multiplying by `2^d` (`d` ≥ the degree in that
variable) keeps all coefficients integral: `shiftAx ax pos d A` has value
`2^d · A(…, (σ' + c)/2, …)`, `c = ±1` (`ev3_shift0`, `ev3_shift1`, `ev3_shift2`). It is computed
by a rescaling followed by a Taylor shift by `c` (repeated synthetic division, additions only).
Since the polynomial is re-expanded around the centre of every cell, cancellation between
monomials is resolved exactly, and the elementary enclosure `|A| ≤ ∑ |coefficients|` on the cube
becomes sharp on small cells.

**Truncation.** `trunc3 cap 0 A` drops all monomials of total degree `> cap`; the dropped part
is bounded on the cube by the sum of the absolute values of its coefficients (`ev3_trunc3`).

**Certificates.** A `Plan` is a binary tree of splits (`S`, `Z`, `T` for the three variables),
truncations (`D n`), leaves (`L`) and external nodes (`E i`, whose claims are proved separately;
used to split large certificates into several kernel checks). `check absMode dd lits p A D r` is
a Boolean function evaluated by the kernel (`decide +kernel`). Soundness (`check_sound`): if it
returns `true` and the external claims `lits` hold, then on the whole cube `|A| + r ≤ D`
(absolute mode) or `A + r ≤ D` (upper mode). Plans are found by an untrusted search (Python) and
elaborated from strings by the `meta` parser `plan%`; literal polynomials by `d3%`.

**Charts.** `chartD d sg p` turns a sparse integer polynomial `p(s, z, C, S)` into the dense
polynomial `(1 + t²)^d p(s, z, C(t), S(t))` with the rational parametrisation
`C = sg (1 - t²)/(1 + t²)`, `S = sg 2t/(1 + t²)` of the unit circle (`ev3_chartD`).

All arithmetic is exact (`ℤ`), so no floating point is trusted.
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellarator.Cover
open PlasmaLean.Kinetic.LiePoly

/-! ## Dense polynomials -/

/-- Univariate dense polynomial (coefficients from degree `0`). -/
abbrev D1 := List ℤ
/-- Bivariate dense polynomial. -/
abbrev D2 := List D1
/-- Trivariate dense polynomial. -/
abbrev D3 := List D2

/-- Value of a list of coefficients (each with value `e a`) at `x` (Horner). -/
@[expose] def evL {α : Type} (e : α → ℝ) : List α → ℝ → ℝ
  | [], _ => 0
  | a :: l, x => e a + x * evL e l x

/-- Value of a univariate polynomial. -/
@[expose] def ev1 (f : D1) (τ : ℝ) : ℝ := evL (fun c : ℤ => (c : ℝ)) f τ
/-- Value of a bivariate polynomial. -/
@[expose] def ev2 (B : D2) (ζ τ : ℝ) : ℝ := evL (fun f => ev1 f τ) B ζ
/-- Value of a trivariate polynomial. -/
@[expose] def ev3 (A : D3) (σ ζ τ : ℝ) : ℝ := evL (fun B => ev2 B ζ τ) A σ

/-- Padded pointwise combination of lists. -/
@[expose] def zipL {α : Type} (f : α → α → α) : List α → List α → List α
  | [], b => b
  | a :: as, [] => a :: as
  | x :: a, y :: b => f x y :: zipL f a b

/-- Sum of univariate polynomials. -/
@[expose] def add1 : D1 → D1 → D1 := zipL Int.add
/-- Sum of bivariate polynomials. -/
@[expose] def add2 : D2 → D2 → D2 := zipL add1
/-- Sum of trivariate polynomials. -/
@[expose] def add3 : D3 → D3 → D3 := zipL add2

/-- Negation. -/
@[expose] def neg1 : D1 → D1 := List.map Int.neg
/-- Negation. -/
@[expose] def neg2 : D2 → D2 := List.map neg1
/-- Negation. -/
@[expose] def neg3 : D3 → D3 := List.map neg2

/-- Scalar multiple. -/
@[expose] def smul1 (k : ℤ) : D1 → D1 := List.map (Int.mul k)
/-- Scalar multiple. -/
@[expose] def smul2 (k : ℤ) : D2 → D2 := List.map (smul1 k)

/-- Difference `a - b`. -/
@[expose] def sub1 (a b : D1) : D1 := add1 a (neg1 b)
/-- Difference `a - b`. -/
@[expose] def sub2 (a b : D2) : D2 := add2 a (neg2 b)

/-- Product of univariate polynomials. -/
@[expose] def mul1 : D1 → D1 → D1
  | [], _ => []
  | x :: a, b => add1 (smul1 x b) (0 :: mul1 a b)
/-- Product of bivariate polynomials. -/
@[expose] def mul2 : D2 → D2 → D2
  | [], _ => []
  | f :: a, b => add2 (b.map (mul1 f)) ([] :: mul2 a b)
/-- Product of trivariate polynomials. -/
@[expose] def mul3 : D3 → D3 → D3
  | [], _ => []
  | B :: a, b => add3 (b.map (mul2 B)) ([] :: mul3 a b)

/-! ## Taylor shift by `±1` and rescaling -/

/-- One pass of synthetic division by `y - c`, from the top: `b_j = a_j + c b_{j+1}`
(`op a b = a + c b`). The head of the result is the value at `c`, the tail the quotient. -/
@[expose] def passL {α : Type} (op : α → α → α) : List α → List α
  | [] => []
  | a :: rest =>
    match passL op rest with
    | [] => [a]
    | b :: bs => op a b :: b :: bs

/-- Taylor shift `q(y) ↦ q(y + c)` by repeated synthetic division (`n` = fuel ≥ length). -/
@[expose] def taylorL {α : Type} (op : α → α → α) : ℕ → List α → List α
  | 0, l => l
  | n + 1, l =>
    match passL op l with
    | [] => []
    | b :: bs => b :: taylorL op n bs

/-- Rescaling `q(y) = Q^d p(y/Q)`: coefficient `j` is multiplied by `Q^(d-j)`. -/
@[expose] def scaleL {α : Type} (Q : ℕ) (sm : ℤ → α → α) : ℕ → List α → List α
  | _, [] => []
  | d, a :: l => sm ((Q ^ d : ℕ) : ℤ) a :: scaleL Q sm (d - 1) l

/-- `2^d p((y + c)/2)` for a list of coefficients (`c = 1` if `pos`, else `-1`). -/
@[expose] def shiftL {α : Type} (sm : ℤ → α → α) (opP opN : α → α → α) (pos : Bool) (d : ℕ)
    (l : List α) : List α :=
  taylorL (if pos then opP else opN) l.length (scaleL 2 sm d l)

/-- Shift in the first variable `σ`. -/
@[expose] def shift0 (pos : Bool) (d : ℕ) (A : D3) : D3 := shiftL smul2 add2 sub2 pos d A
/-- Shift in the second variable `ζ`. -/
@[expose] def shift1 (pos : Bool) (d : ℕ) (A : D3) : D3 :=
  A.map (shiftL smul1 add1 sub1 pos d)
/-- Shift in the third variable `τ`. -/
@[expose] def shift2 (pos : Bool) (d : ℕ) (A : D3) : D3 :=
  A.map (List.map (shiftL Int.mul Int.add Int.sub pos d))

/-- Shift along axis `ax` (`0, 1, 2`). -/
@[expose] def shiftAx (ax : ℕ) (pos : Bool) (d : ℕ) (A : D3) : D3 :=
  match ax with
  | 0 => shift0 pos d A
  | 1 => shift1 pos d A
  | _ => shift2 pos d A

/-- All lists along axis `ax` have length `≤ d + 1`. -/
@[expose] def lenOK (ax : ℕ) (d : ℕ) (A : D3) : Bool :=
  match ax with
  | 0 => decide (A.length ≤ d + 1)
  | 1 => A.all fun B => decide (B.length ≤ d + 1)
  | _ => A.all fun B => B.all fun f => decide (f.length ≤ d + 1)

/-- Rescaling of the first variable: value `Q^d A(σ/Q, ζ, τ)`. -/
@[expose] def scale0 (Q d : ℕ) (A : D3) : D3 := scaleL Q smul2 d A
/-- Rescaling of the second variable: value `Q^d A(σ, ζ/Q, τ)`. -/
@[expose] def scale1 (Q d : ℕ) (A : D3) : D3 := A.map (scaleL Q smul1 d)

/-- Restriction `σ = ±1`, as a polynomial not depending on `σ`. -/
@[expose] def restrict0 (pos : Bool) (A : D3) : D3 :=
  [A.foldr (fun B acc => if pos then add2 B acc else sub2 B acc) []]
/-- Restriction `ζ = ±1`, as a polynomial not depending on `ζ`. -/
@[expose] def restrict1 (pos : Bool) (A : D3) : D3 :=
  A.map fun B => [B.foldr (fun f acc => if pos then add1 f acc else sub1 f acc) []]

/-! ## Truncation and elementary bounds -/

/-- Sum of absolute values. -/
@[expose] def asum1 : D1 → ℕ
  | [] => 0
  | c :: f => c.natAbs + asum1 f
/-- Sum of absolute values. -/
@[expose] def asum2 : D2 → ℕ
  | [] => 0
  | f :: B => asum1 f + asum2 B
/-- Sum of absolute values. -/
@[expose] def asum3 : D3 → ℕ
  | [] => 0
  | B :: A => asum2 B + asum3 A

/-- Keep the monomials `ζ^k τ^m` with `k + m ≤ cap` (`k` counted from `k₀`); also return the
absolute sum of the dropped coefficients. -/
@[expose] def trunc2 (cap : ℕ) : ℕ → D2 → D2 × ℕ
  | _, [] => ([], 0)
  | k, f :: B =>
    let r := trunc2 cap (k + 1) B
    (f.take (cap + 1 - k) :: r.1, asum1 (f.drop (cap + 1 - k)) + r.2)

/-- Keep the monomials of total degree `≤ cap` (`σ`-degree counted from `j₀`). -/
@[expose] def trunc3 (cap : ℕ) : ℕ → D3 → D3 × ℕ
  | _, [] => ([], 0)
  | j, B :: A =>
    let r := trunc3 cap (j + 1) A
    if j ≤ cap then
      let b := trunc2 (cap - j) 0 B
      (b.1 :: r.1, b.2 + r.2)
    else ([] :: r.1, asum2 B + r.2)

/-- Constant coefficient. -/
@[expose] def const3 (A : D3) : ℤ := ((A.headD []).headD []).headD 0

/-- Leaf test. Absolute mode: `∑|A| + r ≤ D₀ - (∑|D| - |D₀|)`; upper mode:
`A₀ + (∑|A| - |A₀|) + r ≤ D₀ - (∑|D| - |D₀|)`. -/
@[expose] def leafOK (absMode : Bool) (A D : D3) (r : ℕ) : Bool :=
  if absMode then
    decide ((asum3 A : ℤ) + r ≤ const3 D - ((asum3 D : ℤ) - (const3 D).natAbs))
  else
    decide (const3 A + ((asum3 A : ℤ) - (const3 A).natAbs) + r ≤
      const3 D - ((asum3 D : ℤ) - (const3 D).natAbs))

/-! ## Equality up to zero padding -/

/-- All coefficients vanish. -/
@[expose] def zero1 (f : D1) : Bool := f.all (· == 0)
/-- All coefficients vanish. -/
@[expose] def zero2 (B : D2) : Bool := B.all zero1
/-- All coefficients vanish. -/
@[expose] def zero3 (A : D3) : Bool := A.all zero2

/-- Equality of coefficients up to zero padding. -/
@[expose] def beq1 : D1 → D1 → Bool
  | [], b => zero1 b
  | a :: as, [] => zero1 (a :: as)
  | x :: a, y :: b => (x == y) && beq1 a b
/-- Equality of coefficients up to zero padding. -/
@[expose] def beq2 : D2 → D2 → Bool
  | [], b => zero2 b
  | a :: as, [] => zero2 (a :: as)
  | x :: a, y :: b => beq1 x y && beq2 a b
/-- Equality of coefficients up to zero padding. -/
@[expose] def beq3 : D3 → D3 → Bool
  | [], b => zero3 b
  | a :: as, [] => zero3 (a :: as)
  | x :: a, y :: b => beq2 x y && beq3 a b

/-! ## Plans and the checker -/

/-- A subdivision plan. -/
inductive Plan where
  /-- leaf: elementary bound -/
  | leaf : Plan
  /-- truncate to total degree `cap` -/
  | trunc (cap : ℕ) (p : Plan) : Plan
  /-- bisect along axis `ax` (lower half first) -/
  | split (ax : ℕ) (l r : Plan) : Plan
  /-- external node: the claim `lits[i]` is proved separately -/
  | ext (i : ℕ) : Plan

/-- Degree bounds along the three axes. -/
@[expose] def degAx (dd : ℕ × ℕ × ℕ) (ax : ℕ) : ℕ :=
  match ax with
  | 0 => dd.1
  | 1 => dd.2.1
  | _ => dd.2.2

/-- **The checker.** `lits` lists the external claims `(A', D', r')`. -/
@[expose] def check (absMode : Bool) (dd : ℕ × ℕ × ℕ) (lits : List (D3 × D3 × ℕ)) :
    Plan → D3 → D3 → ℕ → Bool
  | .leaf, A, D, r => leafOK absMode A D r
  | .trunc cap p, A, D, r =>
    let t := trunc3 cap 0 A
    check absMode dd lits p t.1 D (r + t.2)
  | .split ax l rt, A, D, r =>
    lenOK ax (degAx dd ax) A && lenOK ax (degAx dd ax) D &&
      check absMode dd lits l (shiftAx ax false (degAx dd ax) A)
        (shiftAx ax false (degAx dd ax) D) (r * 2 ^ degAx dd ax) &&
      check absMode dd lits rt (shiftAx ax true (degAx dd ax) A)
        (shiftAx ax true (degAx dd ax) D) (r * 2 ^ degAx dd ax)
  | .ext i, A, D, r =>
    match lits[i]? with
    | some x => beq3 A x.1 && beq3 D x.2.1 && decide (r ≤ x.2.2)
    | none => false

/-- The claim certified by a plan: on the cube, `|A| + r ≤ D` (absolute mode) or
`A + r ≤ D` (upper mode). -/
@[expose] def Good (absMode : Bool) (A D : D3) (r : ℕ) : Prop :=
  ∀ σ ζ τ : ℝ, |σ| ≤ 1 → |ζ| ≤ 1 → |τ| ≤ 1 →
    (if absMode then |ev3 A σ ζ τ| else ev3 A σ ζ τ) + r ≤ ev3 D σ ζ τ

/-! ## Charts: sparse polynomials on the unit circle -/

/-- `(1 - t²)^a (2t)^b (1 + t²)^(d - a - b)`. -/
@[expose] def tbasis (a b d : ℕ) : D1 :=
  (List.replicate (d - a - b) [1, 0, 1] ++ List.replicate b [0, 2] ++
    List.replicate a [1, 0, -1]).foldr mul1 [1]

/-- Table of `tbasis a b d` for `a + b ≤ d`. -/
@[expose] def tblD (d : ℕ) : List (List D1) :=
  (List.range (d + 1)).map fun a => (List.range (d + 1 - a)).map fun b => tbasis a b d

/-- The monomial `σ^j ζ^k f(τ)`. -/
@[expose] def place (j k : ℕ) (f : D1) : D3 :=
  List.replicate j [] ++ [List.replicate k [] ++ [f]]

/-- Chart of a sparse integer polynomial `p(s, z, C, S)` (exponent lists `[j, k, a, b]`):
the dense polynomial `(1 + t²)^d p(s, z, sg (1 - t²)/(1 + t²), sg 2t/(1 + t²))`. -/
@[expose] def chartD (d : ℕ) (sg : ℤ) (p : FPoly) : D3 :=
  let T := tblD d
  p.foldr (fun t acc =>
    add3 (place (t.2.getD 0 0) (t.2.getD 1 0)
      (smul1 (t.1 * sg ^ (t.2.getD 2 0 + t.2.getD 3 0))
        ((T.getD (t.2.getD 2 0) []).getD (t.2.getD 3 0) []))) acc) []

/-- Admissibility of a sparse polynomial for `chartD d`: exponent lists of length `≤ 4` and
`a + b ≤ d`. -/
@[expose] def chartOK (d : ℕ) (p : FPoly) : Bool :=
  p.all fun t => decide (t.2.length ≤ 4) && decide (t.2.getD 2 0 + t.2.getD 3 0 ≤ d)

/-- Rational coefficients. -/
@[expose] def toQ (p : FPoly) : Poly := p.map fun t => ((t.1 : ℚ), t.2)

/-- Integer partial derivative (mirrors `LiePoly.pderiv`). -/
@[expose] def pderivZ (p : FPoly) (i : ℕ) : FPoly :=
  p.filterMap fun t => if t.2.getD i 0 = 0 then none else some (t.1 * (t.2.getD i 0), decAt t.2 i)

/-- `(1 + t²)^d`. -/
@[expose] def onePlusSq : ℕ → D1
  | 0 => [1]
  | n + 1 => mul1 [1, 0, 1] (onePlusSq n)

/-! ## Evaluation lemmas -/

/-- Value of the empty list. -/
@[simp] theorem evL_nil {α : Type} (e : α → ℝ) (x : ℝ) : evL e [] x = 0 := rfl
/-- Horner step. -/
@[simp] theorem evL_cons {α : Type} (e : α → ℝ) (a : α) (l : List α) (x : ℝ) :
    evL e (a :: l) x = e a + x * evL e l x := rfl

/-- Values add under padded pointwise combination. -/
theorem evL_zipL {α : Type} (e : α → ℝ) (f : α → α → α) (hf : ∀ a b, e (f a b) = e a + e b) :
    ∀ (a b : List α) (x : ℝ), evL e (zipL f a b) x = evL e a x + evL e b x
  | [], b, x => by simp [zipL]
  | a :: as, [], x => by simp [zipL]
  | a :: as, b :: bs, x => by
    simp only [zipL, evL_cons, hf, evL_zipL e f hf as bs x]; ring

/-- Value of a mapped list. -/
theorem evL_map {α β : Type} (e : β → ℝ) (g : α → β) (l : List α) (x : ℝ) :
    evL e (l.map g) x = evL (fun a => e (g a)) l x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Values depend only on the values of the entries. -/
theorem evL_congr {α : Type} (e e' : α → ℝ) (l : List α) (h : ∀ a ∈ l, e a = e' a) (x : ℝ) :
    evL e l x = evL e' l x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [evL_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Scaling the entry values. -/
theorem evL_smul {α : Type} (e : α → ℝ) (k : ℝ) (l : List α) (x : ℝ) :
    evL (fun a => k * e a) l x = k * evL e l x := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-- Value of a concatenation. -/
theorem evL_append {α : Type} (e : α → ℝ) (l₁ l₂ : List α) (x : ℝ) :
    evL e (l₁ ++ l₂) x = evL e l₁ x + x ^ l₁.length * evL e l₂ x := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, pow_succ]; ring

/-- Entries of value `0` give value `0`. -/
theorem evL_zero_of_all {α : Type} (e : α → ℝ) (l : List α) (h : ∀ a ∈ l, e a = 0) (x : ℝ) :
    evL e l x = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [evL_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]; ring

/-- A repeated zero entry has value `0`. -/
theorem evL_replicate_zero {α : Type} (e : α → ℝ) (a : α) (ha : e a = 0) (n : ℕ) (x : ℝ) :
    evL e (List.replicate n a) x = 0 :=
  evL_zero_of_all e _ (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact ha) x

/-! ### Arithmetic -/

/-- Value of a sum. -/
theorem ev1_add1 (a b : D1) (τ : ℝ) : ev1 (add1 a b) τ = ev1 a τ + ev1 b τ :=
  evL_zipL _ _ (fun x y => by simp [Int.add_def]) a b τ

/-- Value of a sum. -/
theorem ev2_add2 (a b : D2) (ζ τ : ℝ) : ev2 (add2 a b) ζ τ = ev2 a ζ τ + ev2 b ζ τ :=
  evL_zipL _ _ (fun x y => ev1_add1 x y τ) a b ζ

/-- Value of a sum. -/
theorem ev3_add3 (a b : D3) (σ ζ τ : ℝ) : ev3 (add3 a b) σ ζ τ = ev3 a σ ζ τ + ev3 b σ ζ τ :=
  evL_zipL _ _ (fun x y => ev2_add2 x y ζ τ) a b σ

/-- Value of a negation. -/
theorem ev1_neg1 (a : D1) (τ : ℝ) : ev1 (neg1 a) τ = -ev1 a τ := by
  unfold ev1 neg1; rw [evL_map]
  have := evL_smul (fun c : ℤ => (c : ℝ)) (-1) a τ
  simp only [neg_one_mul] at this
  rw [← this]; congr 1; funext c; simp [show Int.neg c = -c from rfl]

/-- Value of a negation. -/
theorem ev2_neg2 (a : D2) (ζ τ : ℝ) : ev2 (neg2 a) ζ τ = -ev2 a ζ τ := by
  unfold ev2 neg2; rw [evL_map]
  have := evL_smul (fun f => ev1 f τ) (-1) a ζ
  simp only [neg_one_mul] at this
  rw [← this]; congr 1; funext f; exact ev1_neg1 f τ

/-- Value of a negation. -/
theorem ev3_neg3 (a : D3) (σ ζ τ : ℝ) : ev3 (neg3 a) σ ζ τ = -ev3 a σ ζ τ := by
  unfold ev3 neg3; rw [evL_map]
  have := evL_smul (fun B => ev2 B ζ τ) (-1) a σ
  simp only [neg_one_mul] at this
  rw [← this]; congr 1; funext B; exact ev2_neg2 B ζ τ

/-- Value of a scalar multiple. -/
theorem ev1_smul1 (k : ℤ) (a : D1) (τ : ℝ) : ev1 (smul1 k a) τ = k * ev1 a τ := by
  unfold ev1 smul1; rw [evL_map, ← evL_smul]; congr 1; funext c; simp [Int.mul_def]

/-- Value of a scalar multiple. -/
theorem ev2_smul2 (k : ℤ) (a : D2) (ζ τ : ℝ) : ev2 (smul2 k a) ζ τ = k * ev2 a ζ τ := by
  unfold ev2 smul2; rw [evL_map, ← evL_smul]; congr 1; funext f; exact ev1_smul1 k f τ

/-- Value of a difference. -/
theorem ev1_sub1 (a b : D1) (τ : ℝ) : ev1 (sub1 a b) τ = ev1 a τ - ev1 b τ := by
  simp [sub1, ev1_add1, ev1_neg1]; ring

/-- Value of a difference. -/
theorem ev2_sub2 (a b : D2) (ζ τ : ℝ) : ev2 (sub2 a b) ζ τ = ev2 a ζ τ - ev2 b ζ τ := by
  simp [sub2, ev2_add2, ev2_neg2]; ring

/-- Value of a product. -/
theorem ev1_mul1 (a b : D1) (τ : ℝ) : ev1 (mul1 a b) τ = ev1 a τ * ev1 b τ := by
  induction a with
  | nil => simp [mul1, ev1]
  | cons x a ih =>
    simp only [mul1, ev1_add1, ev1_smul1]
    simp only [ev1, evL_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Multiplying all fibres by a univariate polynomial. -/
theorem ev2_map_mul1 (f : D1) (b : D2) (ζ τ : ℝ) :
    ev2 (b.map (mul1 f)) ζ τ = ev1 f τ * ev2 b ζ τ := by
  unfold ev2; rw [evL_map, ← evL_smul]; congr 1; funext g; exact ev1_mul1 f g τ

/-- Value of a product. -/
theorem ev2_mul2 (a b : D2) (ζ τ : ℝ) : ev2 (mul2 a b) ζ τ = ev2 a ζ τ * ev2 b ζ τ := by
  induction a with
  | nil => simp [mul2, ev2]
  | cons f a ih =>
    simp only [mul2, ev2_add2, ev2_map_mul1]
    simp only [ev2, evL_cons] at ih ⊢
    rw [ih]; simp [ev1]; ring

/-- Multiplying all slices by a bivariate polynomial. -/
theorem ev3_map_mul2 (B : D2) (b : D3) (σ ζ τ : ℝ) :
    ev3 (b.map (mul2 B)) σ ζ τ = ev2 B ζ τ * ev3 b σ ζ τ := by
  unfold ev3; rw [evL_map, ← evL_smul]; congr 1; funext g; exact ev2_mul2 B g ζ τ

/-- Value of a product. -/
theorem ev3_mul3 (a b : D3) (σ ζ τ : ℝ) : ev3 (mul3 a b) σ ζ τ = ev3 a σ ζ τ * ev3 b σ ζ τ := by
  induction a with
  | nil => simp [mul3, ev3]
  | cons B a ih =>
    simp only [mul3, ev3_add3, ev3_map_mul2]
    simp only [ev3, evL_cons] at ih ⊢
    rw [ih]; simp [ev2]; ring


/-! ### Taylor shift -/

section Shift
variable {α : Type} (e : α → ℝ)

/-- Synthetic division: `p(y) = p(c) + (y - c) q(y)`, with the length of the quotient. -/
theorem passL_spec (op : α → α → α) (c : ℝ) (hop : ∀ a b, e (op a b) = e a + c * e b) (y : ℝ) :
    ∀ l : List α, (passL op l = [] → l = []) ∧
      ∀ b bs, passL op l = b :: bs → evL e l y = e b + (y - c) * evL e bs y ∧
        bs.length + 1 = l.length
  | [] => by simp [passL]
  | a :: rest => by
    obtain ⟨ih1, ih2⟩ := passL_spec op c hop y rest
    rcases h : passL op rest with _ | ⟨b', bs'⟩
    · have hr := ih1 h
      subst hr
      refine ⟨by simp [passL], fun b bs hb => ?_⟩
      simp only [passL, List.cons.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      simp
    · obtain ⟨hv, hl⟩ := ih2 b' bs' h
      refine ⟨by simp [passL, h], fun b bs hb => ?_⟩
      simp only [passL, h, List.cons.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨?_, by simp [hl]⟩
      simp only [evL_cons, hop, hv]; ring

/-- **Taylor shift**: `taylorL` computes `q(y + c)`. -/
theorem taylorL_spec (op : α → α → α) (c : ℝ) (hop : ∀ a b, e (op a b) = e a + c * e b) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ x, evL e (taylorL op n l) x = evL e l (x + c)
  | 0, l, hl, x => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [taylorL]
  | n + 1, l, hl, x => by
    obtain ⟨h1, h2⟩ := passL_spec e op c hop (x + c) l
    rcases h : passL op l with _ | ⟨b, bs⟩
    · have := h1 h; subst this; simp [taylorL, passL]
    · obtain ⟨hv, hlen⟩ := h2 b bs h
      simp only [taylorL, h, evL_cons]
      rw [taylorL_spec op c hop n bs (by omega) x, hv]; ring

/-- Rescaling preserves the length. -/
theorem length_scaleL (Q : ℕ) (sm : ℤ → α → α) :
    ∀ (d : ℕ) (l : List α), (scaleL Q sm d l).length = l.length
  | _, [] => rfl
  | d, a :: l => by simp [scaleL, length_scaleL Q sm (d - 1) l]

/-- Rescaling: value `Q^d p(y/Q)` (if the degree is at most `d`). -/
theorem scaleL_spec (Q : ℕ) (hQ : 0 < Q) (sm : ℤ → α → α) (hsm : ∀ k a, e (sm k a) = k * e a) :
    ∀ (l : List α) (d : ℕ), l.length ≤ d + 1 → ∀ y,
      evL e (scaleL Q sm d l) y = (Q : ℝ) ^ d * evL e l (y / Q)
  | [], d, _, y => by simp [scaleL]
  | a :: l, 0, hl, y => by
    have : l.length = 0 := by simp only [List.length_cons] at hl; omega
    rw [List.length_eq_zero_iff] at this
    subst this; simp [scaleL, hsm]
  | a :: l, d + 1, hl, y => by
    simp only [scaleL, evL_cons, hsm, Nat.add_sub_cancel]
    rw [scaleL_spec Q hQ sm hsm l d (by simp only [List.length_cons] at hl; omega) y]
    have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    push_cast
    field_simp
    ring

/-- **Shift**: value `2^d p((y + c)/2)`. -/
theorem shiftL_spec (sm : ℤ → α → α) (hsm : ∀ k a, e (sm k a) = k * e a)
    (opP opN : α → α → α) (hP : ∀ a b, e (opP a b) = e a + e b)
    (hN : ∀ a b, e (opN a b) = e a - e b) (pos : Bool) (d : ℕ) (l : List α)
    (hl : l.length ≤ d + 1) (y : ℝ) :
    evL e (shiftL sm opP opN pos d l) y =
      2 ^ d * evL e l ((y + (if pos then 1 else -1)) / 2) := by
  unfold shiftL
  have hop : ∀ a b, e ((if pos then opP else opN) a b) = e a + (if pos then 1 else -1) * e b := by
    intro a b; cases pos <;> simp [hP, hN]; ring
  rw [taylorL_spec e _ _ hop l.length _ (by rw [length_scaleL]) y,
    scaleL_spec e 2 (by norm_num) sm hsm l d hl]
  norm_num

end Shift

/-- Value of the shift in `σ`. -/
theorem ev3_shift0 (pos : Bool) (d : ℕ) (A : D3) (hA : A.length ≤ d + 1) (σ ζ τ : ℝ) :
    ev3 (shift0 pos d A) σ ζ τ = 2 ^ d * ev3 A ((σ + (if pos then 1 else -1)) / 2) ζ τ :=
  shiftL_spec (fun B => ev2 B ζ τ) smul2 (fun k a => ev2_smul2 k a ζ τ) add2 sub2
    (fun a b => ev2_add2 a b ζ τ) (fun a b => ev2_sub2 a b ζ τ) pos d A hA σ

/-- Value of the shift in `ζ`. -/
theorem ev3_shift1 (pos : Bool) (d : ℕ) (A : D3) (hA : ∀ B ∈ A, B.length ≤ d + 1)
    (σ ζ τ : ℝ) :
    ev3 (shift1 pos d A) σ ζ τ = 2 ^ d * ev3 A σ ((ζ + (if pos then 1 else -1)) / 2) τ := by
  unfold ev3 shift1
  rw [evL_map, ← evL_smul]
  refine evL_congr _ _ A (fun B hB => ?_) σ
  exact shiftL_spec (fun f => ev1 f τ) smul1 (fun k a => ev1_smul1 k a τ) add1 sub1
    (fun a b => ev1_add1 a b τ) (fun a b => ev1_sub1 a b τ) pos d B (hA B hB) ζ

/-- Value of the shift in `τ`. -/
theorem ev3_shift2 (pos : Bool) (d : ℕ) (A : D3) (hA : ∀ B ∈ A, ∀ f ∈ B, f.length ≤ d + 1)
    (σ ζ τ : ℝ) :
    ev3 (shift2 pos d A) σ ζ τ = 2 ^ d * ev3 A σ ζ ((τ + (if pos then 1 else -1)) / 2) := by
  unfold ev3 shift2
  rw [evL_map, ← evL_smul]
  refine evL_congr _ _ A (fun B hB => ?_) σ
  unfold ev2
  rw [evL_map, ← evL_smul]
  refine evL_congr _ _ B (fun f hf => ?_) ζ
  exact shiftL_spec (fun c : ℤ => (c : ℝ)) Int.mul (fun k a => by simp [Int.mul_def])
    Int.add Int.sub (fun a b => by simp [Int.add_def])
    (fun a b => by simp [show Int.sub a b = a - b from rfl])
    pos d f (hA B hB f hf) τ


/-! ### Elementary bounds on the cube -/

/-- Elementary bound on `[-1, 1]`. -/
theorem abs_ev1_le (f : D1) {τ : ℝ} (hτ : |τ| ≤ 1) : |ev1 f τ| ≤ asum1 f := by
  induction f with
  | nil => simp [ev1, asum1]
  | cons c f ih =>
    simp only [ev1, evL_cons, asum1] at ih ⊢
    push_cast
    calc |(c : ℝ) + τ * evL (fun c : ℤ => (c : ℝ)) f τ|
        ≤ |(c : ℝ)| + |τ| * |evL (fun c : ℤ => (c : ℝ)) f τ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + 1 * (asum1 f : ℝ) := by
          gcongr
      _ = _ := by rw [Nat.cast_natAbs, Int.cast_abs]; ring

/-- Elementary bound on `[-1, 1]²`. -/
theorem abs_ev2_le (B : D2) {ζ τ : ℝ} (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    |ev2 B ζ τ| ≤ asum2 B := by
  induction B with
  | nil => simp [ev2, asum2]
  | cons f B ih =>
    simp only [ev2, evL_cons, asum2] at ih ⊢
    push_cast
    calc |ev1 f τ + ζ * evL (fun f => ev1 f τ) B ζ|
        ≤ |ev1 f τ| + |ζ| * |evL (fun f => ev1 f τ) B ζ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ asum1 f + 1 * (asum2 B : ℝ) := by
          gcongr
          · exact abs_ev1_le f hτ
      _ = _ := by ring

/-- Elementary bound on the cube. -/
theorem abs_ev3_le (A : D3) {σ ζ τ : ℝ} (hσ : |σ| ≤ 1) (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    |ev3 A σ ζ τ| ≤ asum3 A := by
  induction A with
  | nil => simp [ev3, asum3]
  | cons B A ih =>
    simp only [ev3, evL_cons, asum3] at ih ⊢
    push_cast
    calc |ev2 B ζ τ + σ * evL (fun B => ev2 B ζ τ) A σ|
        ≤ |ev2 B ζ τ| + |σ| * |evL (fun B => ev2 B ζ τ) A σ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ asum2 B + 1 * (asum3 A : ℝ) := by
          gcongr
          · exact abs_ev2_le B hζ hτ
      _ = _ := by ring

/-- Deviation from the constant coefficient on `[-1, 1]`. -/
theorem ev1_sub_const (f : D1) {τ : ℝ} (hτ : |τ| ≤ 1) :
    |ev1 f τ - (f.headD 0 : ℤ)| ≤ (asum1 f : ℝ) - |((f.headD 0 : ℤ) : ℝ)| := by
  cases f with
  | nil => simp [ev1]
  | cons c f =>
    simp only [ev1, evL_cons, List.headD_cons, asum1]
    push_cast
    have h := abs_ev1_le f hτ
    simp only [ev1] at h
    rw [Nat.cast_natAbs, Int.cast_abs, add_sub_cancel_left, abs_mul]
    nlinarith [abs_nonneg τ, abs_nonneg (evL (fun c : ℤ => (c : ℝ)) f τ)]

/-- Deviation from the constant coefficient on `[-1, 1]²`. -/
theorem ev2_sub_const (B : D2) {ζ τ : ℝ} (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    |ev2 B ζ τ - ((B.headD []).headD 0 : ℤ)| ≤
      (asum2 B : ℝ) - |(((B.headD []).headD 0 : ℤ) : ℝ)| := by
  cases B with
  | nil => simp [ev2]
  | cons f B =>
    simp only [ev2, evL_cons, List.headD_cons, asum2]
    push_cast
    have h1 := ev1_sub_const f hτ
    have h2 := abs_ev2_le B hζ hτ
    simp only [ev2] at h2
    calc |ev1 f τ + ζ * evL (fun f => ev1 f τ) B ζ - ((f.headD 0 : ℤ) : ℝ)|
        ≤ |ev1 f τ - ((f.headD 0 : ℤ) : ℝ)| + |ζ| * |evL (fun f => ev1 f τ) B ζ| := by
          rw [← abs_mul]
          calc _ = |(ev1 f τ - ((f.headD 0 : ℤ) : ℝ)) + ζ * evL (fun f => ev1 f τ) B ζ| := by
                ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ ((asum1 f : ℝ) - |((f.headD 0 : ℤ) : ℝ)|) + 1 * (asum2 B : ℝ) := by
          gcongr
      _ = _ := by ring

/-- Deviation from the constant coefficient on the cube. -/
theorem ev3_sub_const (A : D3) {σ ζ τ : ℝ} (hσ : |σ| ≤ 1) (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    |ev3 A σ ζ τ - (const3 A : ℝ)| ≤ (asum3 A : ℝ) - |(const3 A : ℝ)| := by
  cases A with
  | nil => simp [ev3, const3]
  | cons B A =>
    simp only [ev3, evL_cons, const3, List.headD_cons, asum3]
    push_cast
    have h1 := ev2_sub_const B hζ hτ
    have h2 := abs_ev3_le A hσ hζ hτ
    simp only [ev3] at h2
    calc |ev2 B ζ τ + σ * evL (fun B => ev2 B ζ τ) A σ - (((B.headD []).headD 0 : ℤ) : ℝ)|
        ≤ |ev2 B ζ τ - (((B.headD []).headD 0 : ℤ) : ℝ)| +
            |σ| * |evL (fun B => ev2 B ζ τ) A σ| := by
          rw [← abs_mul]
          calc _ = |(ev2 B ζ τ - (((B.headD []).headD 0 : ℤ) : ℝ)) +
                  σ * evL (fun B => ev2 B ζ τ) A σ| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ ≤ ((asum2 B : ℝ) - |(((B.headD []).headD 0 : ℤ) : ℝ)|) + 1 * (asum3 A : ℝ) := by
          gcongr
      _ = _ := by ring

/-! ### Truncation -/

/-- Splitting a univariate polynomial into low and high degrees. -/
theorem ev1_take_drop (f : D1) (n : ℕ) (τ : ℝ) :
    ev1 f τ = ev1 (f.take n) τ + τ ^ n * ev1 (f.drop n) τ := by
  induction f generalizing n with
  | nil => simp [ev1]
  | cons c f ih =>
    cases n with
    | zero => simp [ev1]
    | succ n =>
      simp only [List.take_succ_cons, List.drop_succ_cons]
      simp only [ev1, evL_cons] at ih ⊢
      rw [ih n]; ring

/-- Error of dropping the high degrees on `[-1, 1]`. -/
theorem ev1_take (f : D1) (n : ℕ) {τ : ℝ} (hτ : |τ| ≤ 1) :
    |ev1 f τ - ev1 (f.take n) τ| ≤ asum1 (f.drop n) := by
  rw [ev1_take_drop f n τ, add_sub_cancel_left, abs_mul, abs_pow]
  calc |τ| ^ n * |ev1 (f.drop n) τ| ≤ 1 * asum1 (f.drop n) := by
        gcongr
        · exact pow_le_one₀ (abs_nonneg _) hτ
        · exact abs_ev1_le _ hτ
    _ = _ := one_mul _

/-- Error of the truncation on `[-1, 1]²`. -/
theorem ev2_trunc2 (cap : ℕ) {ζ τ : ℝ} (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    ∀ (k : ℕ) (B : D2), |ev2 B ζ τ - ev2 (trunc2 cap k B).1 ζ τ| ≤ (trunc2 cap k B).2
  | _, [] => by simp [trunc2, ev2]
  | k, f :: B => by
    have ih := ev2_trunc2 cap hζ hτ (k + 1) B
    simp only [trunc2, ev2, evL_cons] at ih ⊢
    push_cast
    calc |ev1 f τ + ζ * evL (fun f => ev1 f τ) B ζ -
          (ev1 (f.take (cap + 1 - k)) τ + ζ * evL (fun f => ev1 f τ) (trunc2 cap (k + 1) B).1 ζ)|
        = |(ev1 f τ - ev1 (f.take (cap + 1 - k)) τ) +
            ζ * (evL (fun f => ev1 f τ) B ζ -
              evL (fun f => ev1 f τ) (trunc2 cap (k + 1) B).1 ζ)| := by ring_nf
      _ ≤ |ev1 f τ - ev1 (f.take (cap + 1 - k)) τ| + |ζ| * |evL (fun f => ev1 f τ) B ζ -
              evL (fun f => ev1 f τ) (trunc2 cap (k + 1) B).1 ζ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (asum1 (f.drop (cap + 1 - k)) : ℝ) + 1 * ((trunc2 cap (k + 1) B).2 : ℝ) := by
          gcongr
          · exact ev1_take f _ hτ
      _ = _ := by ring

/-- **Error of the truncation** on the cube. -/
theorem ev3_trunc3 (cap : ℕ) {σ ζ τ : ℝ} (hσ : |σ| ≤ 1) (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    ∀ (j : ℕ) (A : D3), |ev3 A σ ζ τ - ev3 (trunc3 cap j A).1 σ ζ τ| ≤ (trunc3 cap j A).2
  | _, [] => by simp [trunc3, ev3]
  | j, B :: A => by
    have ih := ev3_trunc3 cap hσ hζ hτ (j + 1) A
    have key : ∀ (B' : D2) (e : ℝ), |ev2 B ζ τ - ev2 B' ζ τ| ≤ e →
        |ev3 (B :: A) σ ζ τ - ev3 (B' :: (trunc3 cap (j + 1) A).1) σ ζ τ| ≤
          e + (trunc3 cap (j + 1) A).2 := by
      intro B' e hB
      simp only [ev3, evL_cons] at ih ⊢
      calc |ev2 B ζ τ + σ * evL (fun B => ev2 B ζ τ) A σ -
            (ev2 B' ζ τ + σ * evL (fun B => ev2 B ζ τ) (trunc3 cap (j + 1) A).1 σ)|
          = |(ev2 B ζ τ - ev2 B' ζ τ) + σ * (evL (fun B => ev2 B ζ τ) A σ -
              evL (fun B => ev2 B ζ τ) (trunc3 cap (j + 1) A).1 σ)| := by ring_nf
        _ ≤ |ev2 B ζ τ - ev2 B' ζ τ| + |σ| * |evL (fun B => ev2 B ζ τ) A σ -
              evL (fun B => ev2 B ζ τ) (trunc3 cap (j + 1) A).1 σ| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ e + 1 * ((trunc3 cap (j + 1) A).2 : ℝ) := by gcongr
        _ = _ := by ring
    unfold trunc3
    split_ifs with hj
    · push_cast
      exact key _ _ (ev2_trunc2 (cap - j) hζ hτ 0 B)
    · push_cast
      exact key [] _ (by simpa [ev2] using abs_ev2_le B hζ hτ)


/-! ### Padded equality -/

/-- A zero polynomial has value `0`. -/
theorem ev1_zero1 (f : D1) (h : zero1 f = true) (τ : ℝ) : ev1 f τ = 0 := by
  unfold zero1 at h
  refine evL_zero_of_all _ f (fun c hc => ?_) τ
  have := List.all_eq_true.mp h c hc
  simp at this; simp [this]

/-- A zero polynomial has value `0`. -/
theorem ev2_zero2 (B : D2) (h : zero2 B = true) (ζ τ : ℝ) : ev2 B ζ τ = 0 := by
  unfold zero2 at h
  exact evL_zero_of_all _ B (fun f hf => ev1_zero1 f (List.all_eq_true.mp h f hf) τ) ζ

/-- A zero polynomial has value `0`. -/
theorem ev3_zero3 (A : D3) (h : zero3 A = true) (σ ζ τ : ℝ) : ev3 A σ ζ τ = 0 := by
  unfold zero3 at h
  exact evL_zero_of_all _ A (fun B hB => ev2_zero2 B (List.all_eq_true.mp h B hB) ζ τ) σ

/-- Padded equality gives equal values. -/
theorem ev1_beq1 : ∀ (a b : D1), beq1 a b = true → ∀ τ, ev1 a τ = ev1 b τ
  | [], b, h, τ => by rw [ev1_zero1 b (by simpa [beq1] using h)]; rfl
  | a :: as, [], h, τ => by rw [ev1_zero1 (a :: as) (by simpa [beq1] using h)]; rfl
  | x :: a, y :: b, h, τ => by
    simp only [beq1, Bool.and_eq_true, beq_iff_eq] at h
    have := ev1_beq1 a b h.2 τ
    simp only [ev1, evL_cons] at this ⊢
    rw [h.1, this]

/-- Padded equality gives equal values. -/
theorem ev2_beq2 : ∀ (a b : D2), beq2 a b = true → ∀ ζ τ, ev2 a ζ τ = ev2 b ζ τ
  | [], b, h, ζ, τ => by rw [ev2_zero2 b (by simpa [beq2] using h)]; rfl
  | a :: as, [], h, ζ, τ => by rw [ev2_zero2 (a :: as) (by simpa [beq2] using h)]; rfl
  | x :: a, y :: b, h, ζ, τ => by
    simp only [beq2, Bool.and_eq_true] at h
    have := ev2_beq2 a b h.2 ζ τ
    simp only [ev2, evL_cons] at this ⊢
    rw [ev1_beq1 x y h.1 τ, this]

/-- Padded equality gives equal values. -/
theorem ev3_beq3 : ∀ (a b : D3), beq3 a b = true → ∀ σ ζ τ, ev3 a σ ζ τ = ev3 b σ ζ τ
  | [], b, h, σ, ζ, τ => by rw [ev3_zero3 b (by simpa [beq3] using h)]; rfl
  | a :: as, [], h, σ, ζ, τ => by rw [ev3_zero3 (a :: as) (by simpa [beq3] using h)]; rfl
  | x :: a, y :: b, h, σ, ζ, τ => by
    simp only [beq3, Bool.and_eq_true] at h
    have := ev3_beq3 a b h.2 σ ζ τ
    simp only [ev3, evL_cons] at this ⊢
    rw [ev2_beq2 x y h.1 ζ τ, this]

/-! ### Soundness of the checker -/

/-- Soundness of the leaf test. -/
theorem leafOK_sound {absMode : Bool} {A D : D3} {r : ℕ} (h : leafOK absMode A D r = true) :
    Good absMode A D r := by
  intro σ ζ τ hσ hζ hτ
  have hD := ev3_sub_const D hσ hζ hτ
  have hDlo : (const3 D : ℝ) - ((asum3 D : ℝ) - |(const3 D : ℝ)|) ≤ ev3 D σ ζ τ := by
    have := (abs_le.mp hD).1; linarith
  cases absMode with
  | true =>
    simp only [leafOK, ite_true, decide_eq_true_eq] at h
    have h' : (asum3 A : ℝ) + r ≤ (const3 D : ℝ) - ((asum3 D : ℝ) - |(const3 D : ℝ)|) := by
      have := (Int.cast_le (R := ℝ)).mpr h
      push_cast at this
      exact this
    simp only [ite_true]
    have := abs_ev3_le A hσ hζ hτ
    linarith
  | false =>
    simp only [leafOK, Bool.false_eq_true, ite_false, decide_eq_true_eq] at h
    have h' : (const3 A : ℝ) + ((asum3 A : ℝ) - |(const3 A : ℝ)|) + r ≤
        (const3 D : ℝ) - ((asum3 D : ℝ) - |(const3 D : ℝ)|) := by
      have := (Int.cast_le (R := ℝ)).mpr h
      push_cast at this
      exact this
    simp only [Bool.false_eq_true, ite_false]
    have := (abs_le.mp (ev3_sub_const A hσ hζ hτ)).2
    linarith

/-- Soundness of a truncation step. -/
theorem good_trunc {absMode : Bool} {A D : D3} {r : ℕ} (cap : ℕ)
    (h : Good absMode (trunc3 cap 0 A).1 D (r + (trunc3 cap 0 A).2)) : Good absMode A D r := by
  intro σ ζ τ hσ hζ hτ
  have ht := ev3_trunc3 cap hσ hζ hτ 0 A
  have hg := h σ ζ τ hσ hζ hτ
  push_cast at hg
  cases absMode with
  | true =>
    simp only [ite_true] at hg ⊢
    have := abs_sub_abs_le_abs_sub (ev3 A σ ζ τ) (ev3 (trunc3 cap 0 A).1 σ ζ τ)
    linarith
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hg ⊢
    have := (abs_le.mp ht).2
    linarith

/-- The mode-dependent left-hand side scales with a positive factor. -/
theorem mode_scale (absMode : Bool) {k : ℝ} (hk : 0 < k) (x : ℝ) :
    (if absMode then |k * x| else k * x) = k * (if absMode then |x| else x) := by
  cases absMode <;> simp [abs_mul, abs_of_pos hk]

/-- Halving lemma: a claim on both halves (in rescaled form) gives the claim on the cube. -/
theorem good_halves {absMode : Bool} {d : ℕ} {r : ℕ} (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hL : ∀ v, |v| ≤ 1 → v ≤ 0 →
      (if absMode then |2 ^ d * f v| else 2 ^ d * f v) + (r * 2 ^ d : ℕ) ≤ 2 ^ d * g v)
    (hR : ∀ v, |v| ≤ 1 → 0 ≤ v →
      (if absMode then |2 ^ d * f v| else 2 ^ d * f v) + (r * 2 ^ d : ℕ) ≤ 2 ^ d * g v) :
    ∀ v, |v| ≤ 1 → (if absMode then |f v| else f v) + r ≤ g v := by
  intro v hv
  have hk : (0 : ℝ) < 2 ^ d := by positivity
  have key : (if absMode then |2 ^ d * f v| else 2 ^ d * f v) + (r * 2 ^ d : ℕ) ≤ 2 ^ d * g v := by
    rcases le_total v 0 with h | h
    · exact hL v hv h
    · exact hR v hv h
  rw [mode_scale absMode hk] at key
  push_cast at key
  have : 2 ^ d * ((if absMode then |f v| else f v) + r) ≤ 2 ^ d * g v := by linarith
  exact le_of_mul_le_mul_left this hk


/-- Soundness of a bisection step. -/
theorem good_split {absMode : Bool} {A D : D3} {r : ℕ} (ax d : ℕ)
    (hA : lenOK ax d A = true) (hD : lenOK ax d D = true)
    (hl : Good absMode (shiftAx ax false d A) (shiftAx ax false d D) (r * 2 ^ d))
    (hr : Good absMode (shiftAx ax true d A) (shiftAx ax true d D) (r * 2 ^ d)) :
    Good absMode A D r := by
  have hmid : ∀ v : ℝ, |v| ≤ 1 → v ≤ 0 → |2 * v + 1| ≤ 1 ∧ (2 * v + 1 + -1) / 2 = v := by
    intro v hv h0
    refine ⟨abs_le.mpr ⟨by linarith [(abs_le.mp hv).1], by linarith⟩, by ring⟩
  have hmid' : ∀ v : ℝ, |v| ≤ 1 → 0 ≤ v → |2 * v - 1| ≤ 1 ∧ (2 * v - 1 + 1) / 2 = v := by
    intro v hv h0
    refine ⟨abs_le.mpr ⟨by linarith, by linarith [(abs_le.mp hv).2]⟩, by ring⟩
  intro σ ζ τ hσ hζ hτ
  rcases ax with _ | _ | ax
  · simp only [lenOK, decide_eq_true_eq] at hA hD
    simp only [shiftAx] at hl hr
    refine good_halves (d := d) (fun v => ev3 A v ζ τ) (fun v => ev3 D v ζ τ)
      (fun v hv h0 => ?_) (fun v hv h0 => ?_) σ hσ
    · obtain ⟨h1, h2⟩ := hmid v hv h0
      have := hl (2 * v + 1) ζ τ h1 hζ hτ
      simp only [ev3_shift0 _ _ _ hA, ev3_shift0 _ _ _ hD, Bool.false_eq_true, ite_false,
        h2] at this
      exact this
    · obtain ⟨h1, h2⟩ := hmid' v hv h0
      have := hr (2 * v - 1) ζ τ h1 hζ hτ
      simp only [ev3_shift0 _ _ _ hA, ev3_shift0 _ _ _ hD, ite_true, h2] at this
      exact this
  · simp only [lenOK, List.all_eq_true, decide_eq_true_eq] at hA hD
    simp only [shiftAx] at hl hr
    refine good_halves (d := d) (fun v => ev3 A σ v τ) (fun v => ev3 D σ v τ)
      (fun v hv h0 => ?_) (fun v hv h0 => ?_) ζ hζ
    · obtain ⟨h1, h2⟩ := hmid v hv h0
      have := hl σ (2 * v + 1) τ hσ h1 hτ
      simp only [ev3_shift1 _ _ _ hA, ev3_shift1 _ _ _ hD, Bool.false_eq_true, ite_false,
        h2] at this
      exact this
    · obtain ⟨h1, h2⟩ := hmid' v hv h0
      have := hr σ (2 * v - 1) τ hσ h1 hτ
      simp only [ev3_shift1 _ _ _ hA, ev3_shift1 _ _ _ hD, ite_true, h2] at this
      exact this
  · simp only [lenOK, List.all_eq_true, decide_eq_true_eq] at hA hD
    simp only [shiftAx] at hl hr
    refine good_halves (d := d) (fun v => ev3 A σ ζ v) (fun v => ev3 D σ ζ v)
      (fun v hv h0 => ?_) (fun v hv h0 => ?_) τ hτ
    · obtain ⟨h1, h2⟩ := hmid v hv h0
      have := hl σ ζ (2 * v + 1) hσ hζ h1
      simp only [ev3_shift2 _ _ _ hA, ev3_shift2 _ _ _ hD, Bool.false_eq_true, ite_false,
        h2] at this
      exact this
    · obtain ⟨h1, h2⟩ := hmid' v hv h0
      have := hr σ ζ (2 * v - 1) hσ hζ h1
      simp only [ev3_shift2 _ _ _ hA, ev3_shift2 _ _ _ hD, ite_true, h2] at this
      exact this

/-- A claim with larger margin implies one with smaller margin. -/
theorem good_mono {absMode : Bool} {A D : D3} {r r' : ℕ} (h : Good absMode A D r') (hr : r ≤ r') :
    Good absMode A D r := by
  intro σ ζ τ hσ hζ hτ
  have := h σ ζ τ hσ hζ hτ
  have : (r : ℝ) ≤ r' := by exact_mod_cast hr
  linarith

/-- Claims transfer along padded equality. -/
theorem good_congr {absMode : Bool} {A A' D D' : D3} {r : ℕ} (h : Good absMode A' D' r)
    (hA : beq3 A A' = true) (hD : beq3 D D' = true) : Good absMode A D r := by
  intro σ ζ τ hσ hζ hτ
  rw [ev3_beq3 A A' hA, ev3_beq3 D D' hD]
  exact h σ ζ τ hσ hζ hτ

/-- **Soundness of the checker.** -/
theorem check_sound {absMode : Bool} {dd : ℕ × ℕ × ℕ} {lits : List (D3 × D3 × ℕ)}
    (hlits : ∀ x ∈ lits, Good absMode x.1 x.2.1 x.2.2) :
    ∀ (p : Plan) (A D : D3) (r : ℕ), check absMode dd lits p A D r = true → Good absMode A D r
  | .leaf, A, D, r, h => leafOK_sound h
  | .trunc cap p, A, D, r, h => good_trunc cap (check_sound hlits p _ _ _ h)
  | .split ax l rt, A, D, r, h => by
    simp only [check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hA, hD⟩, hl⟩, hr⟩ := h
    exact good_split ax _ hA hD (check_sound hlits l _ _ _ hl) (check_sound hlits rt _ _ _ hr)
  | .ext i, A, D, r, h => by
    simp only [check] at h
    rcases hi : lits[i]? with _ | x
    · simp [hi] at h
    · simp only [hi, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hA, hD⟩, hr⟩ := h
      exact good_mono (good_congr (hlits x (List.mem_of_getElem? hi)) hA hD) hr


/-! ### Rescaling, restriction, charts -/

/-- Value of the rescaling in `σ`. -/
theorem ev3_scale0 (Q d : ℕ) (hQ : 0 < Q) (A : D3) (hA : A.length ≤ d + 1) (σ ζ τ : ℝ) :
    ev3 (scale0 Q d A) σ ζ τ = (Q : ℝ) ^ d * ev3 A (σ / Q) ζ τ :=
  scaleL_spec (fun B => ev2 B ζ τ) Q hQ smul2 (fun k a => ev2_smul2 k a ζ τ) A d hA σ

/-- Value of the rescaling in `ζ`. -/
theorem ev3_scale1 (Q d : ℕ) (hQ : 0 < Q) (A : D3) (hA : ∀ B ∈ A, B.length ≤ d + 1)
    (σ ζ τ : ℝ) : ev3 (scale1 Q d A) σ ζ τ = (Q : ℝ) ^ d * ev3 A σ (ζ / Q) τ := by
  unfold ev3 scale1
  rw [evL_map, ← evL_smul]
  exact evL_congr _ _ A (fun B hB => scaleL_spec (fun f => ev1 f τ) Q hQ smul1
    (fun k a => ev1_smul1 k a τ) B d (hA B hB) ζ) σ

/-- Value of the restriction `σ = ±1`. -/
theorem ev3_restrict0 (pos : Bool) (A : D3) (σ ζ τ : ℝ) :
    ev3 (restrict0 pos A) σ ζ τ = ev3 A (if pos then 1 else -1) ζ τ := by
  have : ∀ A : D3, ev2 (A.foldr (fun B acc => if pos then add2 B acc else sub2 B acc) []) ζ τ =
      ev3 A (if pos then 1 else -1) ζ τ := by
    intro A
    induction A with
    | nil => simp [ev2, ev3]
    | cons B A ih =>
      cases pos
      · simp only [Bool.false_eq_true, ite_false, List.foldr_cons] at ih ⊢
        rw [ev2_sub2, ih]; simp [ev3]; ring
      · simp only [ite_true, List.foldr_cons] at ih ⊢
        rw [ev2_add2, ih]; simp [ev3]
  simp [restrict0, ev3, this]

/-- Value of the restriction `ζ = ±1`. -/
theorem ev3_restrict1 (pos : Bool) (A : D3) (σ ζ τ : ℝ) :
    ev3 (restrict1 pos A) σ ζ τ = ev3 A σ (if pos then 1 else -1) τ := by
  have : ∀ B : D2, ev1 (B.foldr (fun f acc => if pos then add1 f acc else sub1 f acc) []) τ =
      ev2 B (if pos then 1 else -1) τ := by
    intro B
    induction B with
    | nil => simp [ev1, ev2]
    | cons f B ih =>
      cases pos
      · simp only [Bool.false_eq_true, ite_false, List.foldr_cons] at ih ⊢
        rw [ev1_sub1, ih]; simp [ev2]; ring
      · simp only [ite_true, List.foldr_cons] at ih ⊢
        rw [ev1_add1, ih]; simp [ev2]
  unfold restrict1 ev3
  rw [evL_map]
  exact evL_congr _ _ A (fun B _ => by simp [ev2, this]) σ

/-- Value of a product of factors. -/
theorem ev1_foldr_mul1 (l : List D1) (τ : ℝ) :
    ev1 (l.foldr mul1 [1]) τ = (l.map fun f => ev1 f τ).prod := by
  induction l with
  | nil => simp [ev1]
  | cons f l ih => simp [ev1_mul1, ih]

/-- Value of `(1 + τ²)^d`. -/
theorem ev1_onePlusSq (d : ℕ) (τ : ℝ) : ev1 (onePlusSq d) τ = (1 + τ ^ 2) ^ d := by
  induction d with
  | zero => simp [onePlusSq, ev1]
  | succ n ih => simp only [onePlusSq, ev1_mul1, ih]; simp [ev1, pow_succ]; ring

/-- Value of the chart basis polynomial. -/
theorem ev1_tbasis (a b d : ℕ) (τ : ℝ) :
    ev1 (tbasis a b d) τ = (1 + τ ^ 2) ^ (d - a - b) * (2 * τ) ^ b * (1 - τ ^ 2) ^ a := by
  simp only [tbasis, ev1_foldr_mul1, List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate]
  simp [ev1]; ring

/-- Lookup in the chart table. -/
theorem tblD_getD (d a b : ℕ) (h : a + b ≤ d) :
    ((tblD d).getD a []).getD b [] = tbasis a b d := by
  simp [tblD, List.getD_eq_getElem?_getD, show a < d + 1 by omega,
    show b < d + 1 - a by omega]

/-- Value of a placed monomial. -/
theorem ev3_place (j k : ℕ) (f : D1) (σ ζ τ : ℝ) :
    ev3 (place j k f) σ ζ τ = σ ^ j * ζ ^ k * ev1 f τ := by
  unfold place ev3
  rw [evL_append, evL_replicate_zero _ _ (by simp [ev2]), List.length_replicate]
  simp only [evL_cons, evL_nil, mul_zero, add_zero, zero_add]
  unfold ev2
  rw [evL_append, evL_replicate_zero _ _ (by simp [ev1]), List.length_replicate]
  simp; ring

/-- A monomial in four variables. -/
theorem evalMono_four (e : List ℕ) (he : e.length ≤ 4) (x : ℕ → ℝ) :
    evalMono e x = x 0 ^ e.getD 0 0 * x 1 ^ e.getD 1 0 * x 2 ^ e.getD 2 0 * x 3 ^ e.getD 3 0 := by
  rcases e with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨f, e⟩⟩⟩⟩⟩
  · simp [evalMono]
  · simp [evalMono]
  · simp [evalMono]
  · simp [evalMono]; ring
  · simp [evalMono]; ring
  · simp at he; omega

/-- The chart coordinates `(s, z, C(t), S(t))` as a variable assignment. -/
@[expose] def chartVars (sg : ℤ) (s z t : ℝ) : ℕ → ℝ := fun i =>
  [s, z, sg * (1 - t ^ 2) / (1 + t ^ 2), sg * (2 * t) / (1 + t ^ 2)].getD i 0

/-- **Chart lemma**: `chartD d sg p` has value `(1 + t²)^d p(s, z, C(t), S(t))`. -/
theorem ev3_chartD (d : ℕ) (sg : ℤ) (hsg : sg ^ 2 = 1) (p : FPoly) (hp : chartOK d p = true)
    (s z t : ℝ) :
    ev3 (chartD d sg p) s z t = (1 + t ^ 2) ^ d * eval (toQ p) (chartVars sg s z t) := by
  unfold chartOK at hp
  rw [List.all_eq_true] at hp
  unfold chartD
  induction p with
  | nil => simp [ev3, toQ]
  | cons u p ih =>
    have hu := hp u (by simp)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    simp only [List.foldr_cons, ev3_add3, toQ, List.map_cons, eval_cons]
    rw [ih (fun x hx => hp x (by simp [hx]))]
    simp only [toQ]
    rw [ev3_place, ev1_smul1, tblD_getD _ _ _ hu.2, ev1_tbasis, evalMono_four _ hu.1]
    have ht : (1 + t ^ 2) ≠ 0 := by positivity
    simp only [chartVars, List.getD_cons_zero, List.getD_cons_succ]
    set a := u.2.getD 2 0
    set b := u.2.getD 3 0
    have hd : d = (d - a - b) + a + b := by omega
    have hs : (sg : ℝ) ^ (a + b) * (sg : ℝ) ^ (a + b) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      exact_mod_cast (by rw [hsg]; simp : (sg ^ 2) ^ (a + b) = 1)
    push_cast
    rw [mul_add]
    congr 1
    conv_rhs => rw [hd]
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
    ring

/-- The integer partial derivative agrees with `LiePoly.pderiv`. -/
theorem toQ_pderivZ (p : FPoly) (i : ℕ) : toQ (pderivZ p i) = pderiv (toQ p) i := by
  induction p with
  | nil => rfl
  | cons u p ih =>
    simp only [pderivZ, toQ, pderiv, List.filterMap_cons, List.map_cons] at ih ⊢
    split_ifs with h
    · exact ih
    · simp only [List.map_cons, ih]; push_cast; rfl

/-! ## Sanity checks -/

/-- Accepted fixture: `|1| ≤ 2` on the cube (one leaf). -/
theorem check_leaf_fixture : check true (0, 0, 0) [] .leaf [[[1]]] [[[2]]] 0 = true := by
  decide +kernel

/-- Rejected fixture: `|3| ≤ 2` is not certified. -/
theorem check_reject_fixture : check true (0, 0, 0) [] .leaf [[[3]]] [[[2]]] 0 = false := by
  decide +kernel

/-- `|2σ² - 1| ≤ 2` is not certified by a single leaf (coefficient sum `3`)… -/
theorem check_split_reject :
    check true (2, 0, 0) [] .leaf [[[-1]], [], [[2]]] [[[2]]] 0 = false := by
  decide +kernel

/-- …but it is after one bisection in `σ` (the Taylor re-expansion at `σ = ±1/2`). -/
theorem check_split_fixture :
    check true (2, 0, 0) [] (.split 0 .leaf .leaf) [[[-1]], [], [[2]]] [[[2]]] 0 = true := by
  decide +kernel

/-- Non-vacuous use of soundness: `|2σ² - 1| ≤ 2` on `[-1, 1]`. -/
theorem split_fixture_sound (σ : ℝ) (hσ : |σ| ≤ 1) : |2 * σ ^ 2 - 1| ≤ 2 := by
  have h := check_sound (by simp) _ _ _ _ check_split_fixture σ 0 0 hσ (by simp) (by simp)
  simp only [ite_true, Nat.cast_zero, add_zero] at h
  have e1 : ev3 [[[-1]], [], [[2]]] σ 0 0 = 2 * σ ^ 2 - 1 := by
    simp [ev3, ev2, ev1]; ring
  have e2 : ev3 [[[(2 : ℤ)]]] σ 0 0 = 2 := by simp [ev3, ev2, ev1]
  rwa [e1, e2] at h

/-- Degenerate case: the zero polynomial is bounded by `0`. -/
theorem good_zero : Good true [] [[[0]]] 0 :=
  check_sound (dd := (0, 0, 0)) (lits := []) (by simp) .leaf _ _ _ (by decide +kernel)

end PlasmaLean.Design.RationalStellarator.Cover

end

/-! ## Literal parsers (`meta`, outside the trusted kernel) -/

namespace PlasmaLean.Design.RationalStellarator.Cover
open Lean Elab Term Meta

/-- Parse a dense trivariate literal: slices separated by `|`, fibres by `;`, integers by
whitespace. -/
meta def parseD3 (s : String) : Except String (List (List (List Int))) :=
  ((s.replace "\n" " ").splitOn "|").mapM fun sl =>
    (sl.splitOn ";").mapM fun fb =>
      ((fb.splitOn " ").filter (· ≠ "")).mapM fun t => match t.toInt? with
        | some k => pure k
        | none => throw s!"bad integer {t}"

/-- Literal dense trivariate polynomial `d3% "…"`. -/
elab "d3% " s:str : term => do
  let rows ← match parseD3 s.getString with
    | .ok r => pure r
    | .error e => throwError "d3%: {e}"
  let i := Lean.mkConst ``Int
  let l1 := mkApp (Lean.mkConst ``List [0]) i
  let l2 := mkApp (Lean.mkConst ``List [0]) l1
  let sl ← rows.mapM fun sl => do
    let fs ← sl.mapM fun f => mkListLit i (f.map toExpr)
    mkListLit l1 fs
  mkListLit l2 sl

/-- Parse a plan string: `L` leaf, `D<n>` truncation, `E<i>` external node, `S`/`Z`/`T` split in
`σ`/`ζ`/`τ`. -/
meta partial def parsePlan : List Char → Except String (Expr × List Char)
  | 'L' :: rest => pure (Lean.mkConst ``Plan.leaf, rest)
  | 'D' :: rest => do
    let digits := rest.takeWhile Char.isDigit
    let rest := rest.dropWhile Char.isDigit
    let some n := (String.ofList digits).toNat? | throw "bad truncation"
    let (p, rest) ← parsePlan rest
    pure (mkApp2 (Lean.mkConst ``Plan.trunc) (mkNatLit n) p, rest)
  | 'E' :: rest => do
    let digits := rest.takeWhile Char.isDigit
    let rest := rest.dropWhile Char.isDigit
    let some n := (String.ofList digits).toNat? | throw "bad external index"
    pure (mkApp (Lean.mkConst ``Plan.ext) (mkNatLit n), rest)
  | c :: rest =>
    let ax := if c == 'S' then 0 else if c == 'Z' then 1 else 2
    if c == 'S' || c == 'Z' || c == 'T' then do
      let (l, rest) ← parsePlan rest
      let (r, rest) ← parsePlan rest
      pure (mkApp3 (Lean.mkConst ``Plan.split) (mkNatLit ax) l r, rest)
    else throw s!"bad plan character {c}"
  | [] => throw "unexpected end of plan"

/-- Literal plan `plan% "…"`. -/
elab "plan% " s:str : term => do
  match parsePlan (s.getString.toList.filter (!·.isWhitespace)) with
  | .ok (p, []) => pure p
  | .ok _ => throwError "plan%: trailing characters"
  | .error e => throwError "plan%: {e}"

end PlasmaLean.Design.RationalStellarator.Cover
