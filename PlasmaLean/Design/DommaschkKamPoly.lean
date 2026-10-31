/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowField
public import PlasmaLean.Certificates.KernelFact

/-!
# Sparse rational polynomials in `(u, z, c, s)` with a kernel-checkable normal form (`DkPoly`)

The flow-form polynomials of the Dommaschk QA target (`Design/DommaschkKamField`, N-33 plan
item 5) have about 350 terms each, with 130-bit rational coefficients, and degree up to 18 in `u`.
Their identities are too large for `ring`. This file provides a computable representation and a
sound checker:

* `Tm` (a term `q · u^a z^b c^c s^d`, `q : ℚ`) and `SP = List Tm` (a sparse polynomial);
* computable operations: `merge` (addition of two exponent-sorted lists, combining like terms and
  dropping zeros; structural recursion on a fuel argument, with the fallback `p ++ q`), `scale`,
  `mulMono`, `mul`, the formal partial derivatives `dU`, `dZ`, `dC`, `dS`, and the formal
  `φ`-derivative `phiS = −2s ∂_c + 2c ∂_s` of the interface (`KamFlowField.phiD`);
* the evaluation `ev x p` in any normed commutative `ℂ`-algebra, and the translation
  `toPE p : PolyExpr ℂ (Fin 6)` (a `sumE` of `monoE`, the format of `KamNewtonField`);
* soundness, unconditionally (sortedness is only needed for completeness): `ev_merge`,
  `ev_scale`, `ev_mulMono`, `ev_mul`, `eval_toPE`, and the derivative bridges `pd_toPE_U`, …,
  `phiD_toPE` (`pd x i (toPE p) = ev x (dU p)` etc.).

An identity between polynomial expressions is then proved by rewriting it into `ev x Q = 0` for a
combination `Q` built with these operations, and checking `Q = []` by kernel evaluation
(`kernel_fact`: the leaf `Eq.refl`, checked only by the kernel).

Angle-only polynomials (`AO p`: no `u`, no `z`) describe a moving frame centre: their value does
not depend on the torus (`ev_congr_AO`), and `AO` is preserved by `phiS` (`AO_phiS`).

**Sanity.** `merge_fixture` (`(u + 1) + (−u) = 1`), `mul_fixture` (`(u + 1)(u − 1) = u² − 1`),
`dU_fixture`, and the rejected fixture `merge_fixture_ne` (`u + u ≠ 0`).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKam.DkPoly

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton

/-! ## Data and computable operations -/

/-- A term `q · u^a z^b c^c s^d` (`u = x 0`, `z = x 1`, `c = x 2`, `s = x 3`). -/
structure Tm where
  /-- The rational coefficient. -/
  q : ℚ
  /-- The exponent of `u`. -/
  a : ℕ
  /-- The exponent of `z`. -/
  b : ℕ
  /-- The exponent of `c = cos 2φ`. -/
  c : ℕ
  /-- The exponent of `s = sin 2φ`. -/
  d : ℕ

/-- A sparse polynomial: a list of terms (normally sorted by exponent, without zero terms). -/
abbrev SP := List Tm

/-- The lexicographic order on the exponents `(a, b, c, d)`. -/
def Tm.lt (t s : Tm) : Bool :=
  Nat.blt t.a s.a || (Nat.beq t.a s.a && (Nat.blt t.b s.b || (Nat.beq t.b s.b &&
    (Nat.blt t.c s.c || (Nat.beq t.c s.c && Nat.blt t.d s.d)))))

/-- Equal exponents. -/
def Tm.same (t s : Tm) : Bool :=
  Nat.beq t.a s.a && Nat.beq t.b s.b && Nat.beq t.c s.c && Nat.beq t.d s.d

/-- Merge two sorted sums (with fuel), combining like terms and dropping zeros. When the fuel
runs out, or two incomparable terms meet, the result is still a correct sum. -/
def mergeF : ℕ → SP → SP → SP
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, t :: p, [] => t :: p
  | n + 1, t :: p, s :: q =>
    if t.lt s then t :: mergeF n p (s :: q)
    else if s.lt t then s :: mergeF n (t :: p) q
    else if t.same s then
      (if t.q + s.q == 0 then mergeF n p q else ⟨t.q + s.q, t.a, t.b, t.c, t.d⟩ :: mergeF n p q)
    else t :: s :: mergeF n p q

/-- The sum of two sparse polynomials. -/
def merge (p q : SP) : SP := mergeF (p.length + q.length) p q

/-- Scalar multiple. -/
def scale (k : ℚ) (p : SP) : SP := p.map fun t => ⟨k * t.q, t.a, t.b, t.c, t.d⟩

/-- Product with a term. -/
def mulMono (t : Tm) (p : SP) : SP :=
  p.map fun s => ⟨t.q * s.q, t.a + s.a, t.b + s.b, t.c + s.c, t.d + s.d⟩

/-- Product of two sparse polynomials. -/
def mul (p q : SP) : SP := p.foldr (fun t acc => merge (mulMono t q) acc) []

/-- `∂_u` of a term. -/
def Tm.dU (t : Tm) : SP := if Nat.beq t.a 0 then [] else [⟨t.q * t.a, t.a - 1, t.b, t.c, t.d⟩]
/-- `∂_z` of a term. -/
def Tm.dZ (t : Tm) : SP := if Nat.beq t.b 0 then [] else [⟨t.q * t.b, t.a, t.b - 1, t.c, t.d⟩]
/-- `∂_c` of a term. -/
def Tm.dC (t : Tm) : SP := if Nat.beq t.c 0 then [] else [⟨t.q * t.c, t.a, t.b, t.c - 1, t.d⟩]
/-- `∂_s` of a term. -/
def Tm.dS (t : Tm) : SP := if Nat.beq t.d 0 then [] else [⟨t.q * t.d, t.a, t.b, t.c, t.d - 1⟩]

/-- Formal `∂_u`. -/
def dU (p : SP) : SP := p.flatMap Tm.dU
/-- Formal `∂_z`. -/
def dZ (p : SP) : SP := p.flatMap Tm.dZ
/-- Formal `∂_c`. -/
def dC (p : SP) : SP := p.flatMap Tm.dC
/-- Formal `∂_s`. -/
def dS (p : SP) : SP := p.flatMap Tm.dS

/-- The formal `φ`-derivative `−2s ∂_c + 2c ∂_s` (`KamFlowField.phiD`). -/
def phiS (p : SP) : SP := merge (mulMono ⟨-2, 0, 0, 0, 1⟩ (dC p)) (mulMono ⟨2, 0, 0, 1, 0⟩ (dS p))

/-- Angle-only: no term contains `u` or `z`. -/
def AO (p : SP) : Bool := p.all fun t => Nat.beq t.a 0 && Nat.beq t.b 0

/-- The terms without `u` and `z` (the restriction to `u = z = 0`). -/
def atZero (p : SP) : SP := p.filter fun t => Nat.beq t.a 0 && Nat.beq t.b 0

/-! ## Evaluation -/

noncomputable section

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/-- Value of a term at `x` (only `x 0, …, x 3` are used). -/
def Tm.ev (x : Fin 6 → A) (t : Tm) : A :=
  algebraMap ℂ A (t.q : ℂ) * (x 0 ^ t.a * x 1 ^ t.b * x 2 ^ t.c * x 3 ^ t.d)

/-- Value of a sparse polynomial. -/
def ev (x : Fin 6 → A) (p : SP) : A := (p.map (Tm.ev x)).sum

/-- The empty sum. -/
@[simp] theorem ev_nil (x : Fin 6 → A) : ev x [] = 0 := rfl

/-- A sum with a first term. -/
@[simp] theorem ev_cons (x : Fin 6 → A) (t : Tm) (p : SP) : ev x (t :: p) = t.ev x + ev x p := by
  simp [ev]

/-- Concatenation is addition. -/
@[simp] theorem ev_append (x : Fin 6 → A) (p q : SP) : ev x (p ++ q) = ev x p + ev x q := by
  simp [ev]

/-- Evaluation of a `flatMap`. -/
theorem ev_flatMap (x : Fin 6 → A) (p : SP) (f : Tm → SP) :
    ev x (p.flatMap f) = (p.map fun t => ev x (f t)).sum := by
  induction p with
  | nil => rfl
  | cons t p ih => simp [List.flatMap_cons, ih]

/-- Terms with `same` have equal exponents. -/
theorem Tm.same_eq {t s : Tm} (h : t.same s = true) :
    s.a = t.a ∧ s.b = t.b ∧ s.c = t.c ∧ s.d = t.d := by
  simp only [Tm.same, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨(Nat.eq_of_beq_eq_true h1).symm, (Nat.eq_of_beq_eq_true h2).symm,
    (Nat.eq_of_beq_eq_true h3).symm, (Nat.eq_of_beq_eq_true h4).symm⟩

/-- **Soundness of the merge**: it is the sum (for every fuel, sorted or not). -/
theorem ev_mergeF (x : Fin 6 → A) : ∀ (n : ℕ) (p q : SP), ev x (mergeF n p q) = ev x p + ev x q
  | 0, p, q => by simp [mergeF]
  | _ + 1, [], q => by simp [mergeF]
  | _ + 1, t :: p, [] => by simp [mergeF]
  | n + 1, t :: p, s :: q => by
    simp only [mergeF]
    split_ifs with h1 h2 h3 h4
    · rw [ev_cons, ev_mergeF x n, ev_cons, ev_cons]; ring
    · rw [ev_cons, ev_mergeF x n, ev_cons, ev_cons]; ring
    · obtain ⟨ha, hb, hc, hd⟩ := Tm.same_eq h3
      have h0 : t.q + s.q = 0 := by simpa using h4
      have hs : s.ev x = -t.ev x := by
        have : s.q = -t.q := by linarith
        simp only [Tm.ev, ha, hb, hc, hd, this, Rat.cast_neg, map_neg, neg_mul]
      rw [ev_mergeF x n, ev_cons, ev_cons, hs]; ring
    · obtain ⟨ha, hb, hc, hd⟩ := Tm.same_eq h3
      rw [ev_cons, ev_mergeF x n, ev_cons, ev_cons]
      simp only [Tm.ev, ha, hb, hc, hd, Rat.cast_add, map_add]
      ring
    · rw [ev_cons, ev_cons, ev_mergeF x n, ev_cons, ev_cons]; ring

/-- **Soundness of the merge** (with the default fuel). -/
@[simp] theorem ev_merge (x : Fin 6 → A) (p q : SP) : ev x (merge p q) = ev x p + ev x q :=
  ev_mergeF x _ p q

/-- Evaluation of a scalar multiple. -/
@[simp] theorem ev_scale (x : Fin 6 → A) (k : ℚ) (p : SP) :
    ev x (scale k p) = algebraMap ℂ A (k : ℂ) * ev x p := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
    simp only [scale, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; simp only [Tm.ev, Rat.cast_mul, map_mul]; ring

/-- Evaluation of a product with a term. -/
@[simp] theorem ev_mulMono (x : Fin 6 → A) (t : Tm) (p : SP) :
    ev x (mulMono t p) = t.ev x * ev x p := by
  induction p with
  | nil => simp [mulMono]
  | cons s p ih =>
    simp only [mulMono, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; simp only [Tm.ev, Rat.cast_mul, map_mul, pow_add]; ring

/-- **Evaluation of a product.** -/
@[simp] theorem ev_mul (x : Fin 6 → A) (p q : SP) : ev x (mul p q) = ev x p * ev x q := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
    simp only [mul, List.foldr_cons] at ih ⊢
    rw [ev_merge, ev_mulMono, ih, ev_cons]; ring

/-! ## Translation to polynomial expressions and the derivative bridges -/

/-- A term as a polynomial expression (`monoE`, the format of `KamNewtonField`). -/
def Tm.toE (t : Tm) : PolyExpr ℂ (Fin 6) := monoE (t.q : ℂ) [(0, t.a), (1, t.b), (2, t.c), (3, t.d)]

/-- A sparse polynomial as a polynomial expression (`sumE` of `monoE`). -/
def toPE (p : SP) : PolyExpr ℂ (Fin 6) := sumE (p.map Tm.toE)

/-- Evaluation of the translation of a term. -/
theorem eval_toE (x : Fin 6 → A) (t : Tm) : PolyExpr.eval x t.toE = t.ev x := by
  simp only [Tm.toE, monoE, PolyExpr.eval, PolyExpr.eval_npow, Tm.ev]; ring

/-- **Evaluation of the translation** is the evaluation of the sparse polynomial. -/
@[simp] theorem eval_toPE (x : Fin 6 → A) (p : SP) : PolyExpr.eval x (toPE p) = ev x p := by
  induction p with
  | nil => simp [toPE, sumE, PolyExpr.eval]
  | cons t p ih =>
    simp only [toPE, List.map_cons, sumE, PolyExpr.eval] at ih ⊢
    rw [ih, eval_toE, ev_cons]

/-- The directional derivative of `x_j^k`. -/
theorem deriv_npow_var (x h : Fin 6 → A) (j : Fin 6) :
    ∀ k : ℕ, PolyExpr.deriv x h (PolyExpr.npow (PolyExpr.var j : PolyExpr ℂ (Fin 6)) k) =
      (k : A) * x j ^ (k - 1) * h j
  | 0 => by simp [PolyExpr.npow, PolyExpr.deriv]
  | k + 1 => by
    rw [PolyExpr.npow, PolyExpr.deriv, deriv_npow_var x h j k, PolyExpr.eval_npow]
    simp only [PolyExpr.deriv, PolyExpr.eval, Nat.add_sub_cancel]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring

/-- The directional derivative of a term. -/
theorem deriv_toE (x h : Fin 6 → A) (t : Tm) :
    PolyExpr.deriv x h t.toE = algebraMap ℂ A (t.q : ℂ) *
      ((t.a : A) * x 0 ^ (t.a - 1) * h 0 * x 1 ^ t.b * x 2 ^ t.c * x 3 ^ t.d +
        x 0 ^ t.a * ((t.b : A) * x 1 ^ (t.b - 1) * h 1) * x 2 ^ t.c * x 3 ^ t.d +
        x 0 ^ t.a * x 1 ^ t.b * ((t.c : A) * x 2 ^ (t.c - 1) * h 2) * x 3 ^ t.d +
        x 0 ^ t.a * x 1 ^ t.b * x 2 ^ t.c * ((t.d : A) * x 3 ^ (t.d - 1) * h 3)) := by
  simp only [Tm.toE, monoE, PolyExpr.deriv, PolyExpr.eval, PolyExpr.eval_npow, deriv_npow_var]
  ring

/-- Partial derivatives of a translated sum, termwise. -/
theorem pd_toPE_aux (x : Fin 6 → A) (i : Fin 6) (f : Tm → SP)
    (hf : ∀ t, PolyExpr.deriv x (Pi.single i 1) t.toE = ev x (f t)) (p : SP) :
    pd x i (toPE p) = ev x (p.flatMap f) := by
  rw [ev_flatMap]
  induction p with
  | nil => simp [toPE, sumE, pd, PolyExpr.deriv]
  | cons t p ih =>
    simp only [toPE, List.map_cons, sumE, pd, PolyExpr.deriv, List.sum_cons] at ih ⊢
    rw [ih, hf]

/-- `∂_u (toPE p) = toPE (dU p)` (evaluated). -/
theorem pd_toPE_U (x : Fin 6 → A) (p : SP) : pd x 0 (toPE p) = ev x (dU p) := by
  refine pd_toPE_aux x 0 Tm.dU (fun t => ?_) p
  rw [deriv_toE]
  rcases t with ⟨q, a, b, c, d⟩
  rcases a with _ | a
  · simp [Tm.dU]
  · simp [Tm.dU, Tm.ev]; ring

/-- `∂_z (toPE p) = toPE (dZ p)` (evaluated). -/
theorem pd_toPE_Z (x : Fin 6 → A) (p : SP) : pd x 1 (toPE p) = ev x (dZ p) := by
  refine pd_toPE_aux x 1 Tm.dZ (fun t => ?_) p
  rw [deriv_toE]
  rcases t with ⟨q, a, b, c, d⟩
  rcases b with _ | b
  · simp [Tm.dZ]
  · simp [Tm.dZ, Tm.ev]; ring

/-- `∂_c (toPE p) = toPE (dC p)` (evaluated). -/
theorem pd_toPE_C (x : Fin 6 → A) (p : SP) : pd x 2 (toPE p) = ev x (dC p) := by
  refine pd_toPE_aux x 2 Tm.dC (fun t => ?_) p
  rw [deriv_toE]
  rcases t with ⟨q, a, b, c, d⟩
  rcases c with _ | c
  · simp [Tm.dC]
  · simp [Tm.dC, Tm.ev]; ring

/-- `∂_s (toPE p) = toPE (dS p)` (evaluated). -/
theorem pd_toPE_S (x : Fin 6 → A) (p : SP) : pd x 3 (toPE p) = ev x (dS p) := by
  refine pd_toPE_aux x 3 Tm.dS (fun t => ?_) p
  rw [deriv_toE]
  rcases t with ⟨q, a, b, c, d⟩
  rcases d with _ | d
  · simp [Tm.dS]
  · simp [Tm.dS, Tm.ev]; ring

/-- **The `φ`-derivative bridge**: `phiD x (toPE p) = ev x (phiS p)`. -/
theorem phiD_toPE (x : Fin 6 → A) (p : SP) : phiD x (toPE p) = ev x (phiS p) := by
  rw [phiD, pd_toPE_C, pd_toPE_S, phiS, ev_merge, ev_mulMono, ev_mulMono]
  simp only [Tm.ev, pow_zero, pow_one, one_mul, mul_one]
  push_cast
  simp only [map_ofNat]
  ring

/-- `x_j^k` has real constants. -/
theorem realConsts_npow_var (j : Fin 6) :
    ∀ k : ℕ, (PolyExpr.npow (PolyExpr.var j : PolyExpr ℂ (Fin 6)) k).RealConsts
  | 0 => by simp [PolyExpr.npow, PolyExpr.RealConsts]
  | k + 1 => ⟨realConsts_npow_var j k, trivial⟩

/-- `x_j^k` (`j < 4`) has no velocities. -/
theorem noW_npow_var {j : Fin 6} (hj : j.val < 4) :
    ∀ k : ℕ, NoW (PolyExpr.npow (PolyExpr.var j : PolyExpr ℂ (Fin 6)) k)
  | 0 => by simp [PolyExpr.npow, NoW]
  | k + 1 => ⟨noW_npow_var hj k, hj⟩

/-- The translation has real (rational) constants. -/
theorem realConsts_toPE (p : SP) : (toPE p).RealConsts := by
  induction p with
  | nil => simp [toPE, sumE, PolyExpr.RealConsts]
  | cons t p ih =>
    simp only [toPE, List.map_cons, sumE, PolyExpr.RealConsts] at ih ⊢
    refine ⟨?_, ih⟩
    simp only [Tm.toE, monoE, PolyExpr.RealConsts]
    refine ⟨⟨⟨⟨?_, realConsts_npow_var _ _⟩, realConsts_npow_var _ _⟩, realConsts_npow_var _ _⟩,
      realConsts_npow_var _ _⟩
    simp

/-- The translation does not involve the velocity variables. -/
theorem noW_toPE (p : SP) : NoW (toPE p) := by
  induction p with
  | nil => simp [toPE, sumE, NoW]
  | cons t p ih =>
    simp only [toPE, List.map_cons, sumE, NoW] at ih ⊢
    refine ⟨?_, ih⟩
    simp only [Tm.toE, monoE, NoW]
    exact ⟨⟨⟨⟨trivial, noW_npow_var (by simp) _⟩, noW_npow_var (by simp) _⟩,
      noW_npow_var (by simp) _⟩, noW_npow_var (by simp) _⟩

/-! ## Angle-only polynomials (the moving frame centre) -/

/-- An angle-only polynomial only sees the angle variables. -/
theorem ev_congr_AO {p : SP} (hp : AO p = true) {x y : Fin 6 → A} (h2 : x 2 = y 2)
    (h3 : x 3 = y 3) : ev x p = ev y p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [AO, List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨⟨ha, hb⟩, hp⟩ := hp
    rw [ev_cons, ev_cons, ih hp]
    simp only [Tm.ev, Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true hb, h2, h3, pow_zero]

/-- At `u = z = 0` only the terms without `u` and `z` survive. -/
theorem ev_atZero {x : Fin 6 → A} (h0 : x 0 = 0) (h1 : x 1 = 0) (p : SP) :
    ev x (atZero p) = ev x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [atZero, List.filter_cons]
    split_ifs with h
    · simp only [Bool.and_eq_true] at h
      rw [ev_cons, ev_cons, ← ih, atZero]
    · rw [ev_cons, ← ih, atZero]
      have : t.ev x = 0 := by
        simp only [Bool.and_eq_true, not_and] at h
        rcases t with ⟨q, a, b, c, d⟩
        rcases a with _ | a
        · rcases b with _ | b
          · exact absurd rfl (h rfl)
          · simp [Tm.ev, h1]
        · simp [Tm.ev, h0]
      rw [this, zero_add]

/-- `AO` of a cons. -/
theorem AO_cons {t : Tm} {p : SP} : AO (t :: p) = true ↔ (t.a = 0 ∧ t.b = 0) ∧ AO p = true := by
  simp [AO]

/-- `AO` of a concatenation. -/
theorem AO_append {p q : SP} : AO (p ++ q) = true ↔ AO p = true ∧ AO q = true := by
  simp [AO, List.all_append]

/-- The merge of angle-only sums is angle-only. -/
theorem AO_mergeF : ∀ (n : ℕ) (p q : SP), AO p = true → AO q = true → AO (mergeF n p q) = true
  | 0, p, q, hp, hq => by simp only [mergeF]; exact AO_append.2 ⟨hp, hq⟩
  | _ + 1, [], q, _, hq => by simpa [mergeF] using hq
  | _ + 1, t :: p, [], hp, _ => by simpa [mergeF] using hp
  | n + 1, t :: p, s :: q, hp, hq => by
    have hp' := AO_cons.1 hp
    have hq' := AO_cons.1 hq
    simp only [mergeF]
    split_ifs
    · exact AO_cons.2 ⟨hp'.1, AO_mergeF n _ _ hp'.2 hq⟩
    · exact AO_cons.2 ⟨hq'.1, AO_mergeF n _ _ hp hq'.2⟩
    · exact AO_mergeF n _ _ hp'.2 hq'.2
    · exact AO_cons.2 ⟨hp'.1, AO_mergeF n _ _ hp'.2 hq'.2⟩
    · exact AO_cons.2 ⟨hp'.1, AO_cons.2 ⟨hq'.1, AO_mergeF n _ _ hp'.2 hq'.2⟩⟩

/-- The sum of angle-only polynomials is angle-only. -/
theorem AO_merge {p q : SP} (hp : AO p = true) (hq : AO q = true) : AO (merge p q) = true :=
  AO_mergeF _ p q hp hq

/-- Product of an angle-only term and an angle-only polynomial. -/
theorem AO_mulMono {t : Tm} {p : SP} (ht : t.a = 0 ∧ t.b = 0) (hp : AO p = true) :
    AO (mulMono t p) = true := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    have hp' := AO_cons.1 hp
    simp only [mulMono, List.map_cons] at ih ⊢
    exact AO_cons.2 ⟨⟨by simp [ht.1, hp'.1.1], by simp [ht.2, hp'.1.2]⟩, ih hp'.2⟩

/-- `AO` of a `flatMap`. -/
theorem AO_flatMap {p : SP} {f : Tm → SP} (hf : ∀ t, t.a = 0 ∧ t.b = 0 → AO (f t) = true)
    (hp : AO p = true) : AO (p.flatMap f) = true := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    have hp' := AO_cons.1 hp
    rw [List.flatMap_cons]
    exact AO_append.2 ⟨hf t hp'.1, ih hp'.2⟩

/-- The `φ`-derivative of an angle-only polynomial is angle-only. -/
theorem AO_phiS {p : SP} (hp : AO p = true) : AO (phiS p) = true := by
  refine AO_merge (AO_mulMono ⟨rfl, rfl⟩ (AO_flatMap (fun t ht => ?_) hp))
    (AO_mulMono ⟨rfl, rfl⟩ (AO_flatMap (fun t ht => ?_) hp))
  · unfold Tm.dC; split_ifs
    · rfl
    · exact AO_cons.2 ⟨ht, rfl⟩
  · unfold Tm.dS; split_ifs
    · rfl
    · exact AO_cons.2 ⟨ht, rfl⟩

end

/-! ## Sanity -/

/-- **Sanity**: `(u + 1) + (−u) = 1`. -/
theorem merge_fixture :
    merge [⟨1, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩] [⟨-1, 1, 0, 0, 0⟩] = [⟨1, 0, 0, 0, 0⟩] := by
  kernel_fact

/-- **Sanity**: `(u + 1)(u − 1) = u² − 1`. -/
theorem mul_fixture :
    mul [⟨1, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩] [⟨-1, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩] =
      [⟨-1, 0, 0, 0, 0⟩, ⟨1, 2, 0, 0, 0⟩] := by
  kernel_fact

/-- **Sanity**: `∂_u (u³ z) = 3u² z`, `∂_u z = 0`. -/
theorem dU_fixture : dU [⟨1, 0, 1, 0, 0⟩, ⟨1, 3, 1, 0, 0⟩] = [⟨3, 2, 1, 0, 0⟩] := by
  kernel_fact

/-- **Sanity (rejected fixture)**: `u + u` is not `0`. -/
theorem merge_fixture_ne : merge [⟨1, 1, 0, 0, 0⟩] [⟨1, 1, 0, 0, 0⟩] ≠ [] := by
  simp [merge, mergeF, Tm.lt, Tm.same]

end PlasmaLean.Design.DommaschkKam.DkPoly
