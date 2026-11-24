/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicTaylorModel
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Design.DommaschkBounceField
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sparse Dommaschk field evaluation along a Taylor-model slab

Each multiplication uses the exact product of two bounded-degree polynomials and
immediately rounds its coefficients and error radius to a dyadic grid. Every
discarded coefficient contributes to the error on the whole normalized slab.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkBounceTaylor

open Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly
open Certificates.QPoly

/-- Degree in normalized time and number of fractional bits in each stored coefficient. -/
structure Format where
  degree : ℕ
  bits : ℕ

/-- Coefficient grid denominator. -/
def Format.scale (F : Format) : ℚ := 2 ^ F.bits

/-- Truncate and round coefficients downward, then round the resulting radius upward. -/
def Format.fit (F : Format) (m : Model) : Model :=
  let p := (m.poly.take (F.degree + 1)).map fun a => (⌊a * F.scale⌋ : ℚ) / F.scale
  let error := m.radius + magnitude (difference m.poly p)
  ⟨p, (⌈error * F.scale⌉ : ℚ) / F.scale⟩

/-- Fitting includes the total coefficient error on all of the closed unit slab. -/
theorem Format.fit_mem (F : Format) {m : Model} {s x : ℝ} (hs : |s| ≤ 1) (h : m.Mem s x) :
    (F.fit m).Mem s x := by
  apply enclose hs h
  dsimp only [fit]
  apply (le_div_iff₀ (show 0 < F.scale by unfold scale; positivity)).mpr
  exact Int.le_ceil _

/-- Add on the coefficient grid and charge the truncation and rounding. -/
def Format.add (F : Format) (a b : Model) : Model := F.fit (addModel a b)

/-- Multiply on the coefficient grid and charge the truncation and rounding. -/
def Format.mul (F : Format) (a b : Model) : Model := F.fit (mulModel a b)

theorem Format.add_mem (F : Format) {a b : Model} {s x y : ℝ} (hs : |s| ≤ 1)
    (hx : a.Mem s x) (hy : b.Mem s y) : (F.add a b).Mem s (x + y) :=
  F.fit_mem hs (mem_add hx hy)

theorem Format.mul_mem (F : Format) {a b : Model} {s x y : ℝ} (hs : |s| ≤ 1)
    (hx : a.Mem s x) (hy : b.Mem s y) : (F.mul a b).Mem s (x * y) :=
  F.fit_mem hs (mem_mul hs hx hy)

/-- Constant coefficient model, also used for exact rational term weights. -/
def constant (q : ℚ) : Model := exactPoly [q]

theorem constant_mem (q : ℚ) (s : ℝ) : (constant q).Mem s (q : ℝ) := by
  simpa [constant] using mem_exact [q] s

/-- Each step in a power uses the rounded product in the same format. -/
def Format.pow (F : Format) (a : Model) : ℕ → Model
  | 0 => constant 1
  | n + 1 => F.mul (F.pow a n) a

theorem Format.pow_mem (F : Format) {a : Model} {s x : ℝ} (hs : |s| ≤ 1)
    (hx : a.Mem s x) (n : ℕ) : (F.pow a n).Mem s (x ^ n) := by
  induction n with
  | zero => simpa [pow] using constant_mem 1 s
  | succ n ih => simpa only [pow, pow_succ] using F.mul_mem hs ih hx

/-- The four models share the same normalized time. -/
structure Inputs where
  u : Model
  z : Model
  cos : Model
  sin : Model

/-- All four input values are enclosed at the same normalized time. -/
def Inputs.Mem (a : Inputs) (t u z c s : ℝ) : Prop :=
  a.u.Mem t u ∧ a.z.Mem t z ∧ a.cos.Mem t c ∧ a.sin.Mem t s

/-- Model for a monomial in the exact QA2R sparse representation. -/
def term (F : Format) (a : Inputs) (m : Tm) : Model :=
  F.mul (constant m.q) (F.mul (F.mul (F.mul (F.pow a.u m.a) (F.pow a.z m.b))
    (F.pow a.cos m.c)) (F.pow a.sin m.d))

/-- The evaluator rounds after each monomial product and addition. -/
def poly (F : Format) (a : Inputs) : SP → Model
  | [] => constant 0
  | m :: ms => F.add (term F a m) (poly F a ms)

/-- Every pointwise enclosure obtained by evaluating the sparse terms against
the Taylor input encloses the corresponding exact real polynomial value. -/
theorem poly_mem (F : Format) {a : Inputs} {t u z c s : ℝ} (ht : |t| ≤ 1)
    (ha : a.Mem t u z c s) (p : SP) : (poly F a p).Mem t (evR u z c s p) := by
  induction p with
  | nil => simpa [poly, evR] using constant_mem 0 t
  | cons m p ih =>
    exact F.add_mem ht (F.mul_mem ht (constant_mem m.q t) (F.mul_mem ht
      (F.mul_mem ht (F.mul_mem ht (F.pow_mem ht ha.1 _) (F.pow_mem ht ha.2.1 _))
        (F.pow_mem ht ha.2.2.1 _)) (F.pow_mem ht ha.2.2.2 _))) ih

/-- Local rounded outputs for two ranges of consecutive monomials give a
certified sum for their concatenation. No reassociation of rounded sums is required. -/
theorem append_mem (F : Format) {p q : SP} {a b : Model} {t u z c s : ℝ} (ht : |t| ≤ 1)
    (hp : a.Mem t (evR u z c s p)) (hq : b.Mem t (evR u z c s q)) :
    (F.add a b).Mem t (evR u z c s (p ++ q)) := by
  simpa [evR] using F.add_mem ht hp hq

/-- Equality of a Taylor model to the two proposed rational data columns. -/
structure Matches (m v : Model) : Prop where
  coefficients : m.poly = v.poly
  error : m.radius = v.radius

theorem Matches.eq {m v : Model} (h : Matches m v) : m = v := by
  cases m
  cases v
  obtain ⟨rfl,rfl⟩ := h
  rfl

/-- Each certificate leaf checks boundedly many sparse terms. Intermediate
Taylor coefficients and errors are stored in the common dyadic format. -/
inductive Blocks (F : Format) (a : Inputs) : SP → Model → Prop
  | nil : Blocks F a [] (constant 0)
  | chunk {p : SP} (k : ℕ) (head tail out : Model)
      (terms : Matches (poly F a (p.take k)) head)
      (rest : Blocks F a (p.drop k) tail)
      (combine : Matches (F.add head tail) out) : Blocks F a p out

/-- Every checked block partition encloses the original sparse polynomial
throughout the slab. The real sum is independent of where the blocks split. -/
theorem Blocks.mem {F : Format} {a : Inputs} {p : SP} {out : Model}
    (C : Blocks F a p out) {t u z c s : ℝ} (ht : |t| ≤ 1) (h : a.Mem t u z c s) :
    out.Mem t (evR u z c s p) := by
  induction C with
  | nil => simpa [evR] using constant_mem 0 t
  | @chunk p k _ _ out terms _ combine ih =>
    rw [← combine.eq]
    have head := poly_mem F ht h (p.take k)
    rw [terms.eq] at head
    simpa only [List.take_append_drop] using append_mem F ht head ih

/-- The actual cylindrical QA2R denominator and velocity numerators share one
physical trajectory and one normalized time, including between sampling points. -/
theorem physical_field_slab (F : Format) (a : Inputs) (R z φ : ℝ → ℝ)
    (hR : ∀ t, |t| ≤ 1 → 0 < R t)
    (h : ∀ t, |t| ≤ 1 → a.Mem t (R t - dkR0) (z t) (Real.cos (2 * φ t)) (Real.sin (2 * φ t))) :
    ∀ t, |t| ≤ 1 →
      (poly F a dD).Mem t (R t ^ 7 * cylBphi (R t) (φ t) (z t)) ∧
      (poly F a dnR).Mem t (R t ^ 8 * cylBR (R t) (φ t) (z t)) ∧
      (poly F a dnZ).Mem t (R t ^ 8 * cylBz (R t) (φ t) (z t)) := by
  intro t ht
  obtain ⟨hd,hr,hz⟩ := DommaschkBounceField.field_id (hR t ht) (φ t) (z t)
  rw [← hd, ← hr, ← hz]
  exact ⟨poly_mem F ht (h t ht) _, poly_mem F ht (h t ht) _, poly_mem F ht (h t ht) _⟩

/-- Input models for the centre-section clock with angle t/128. -/
def clockFixture : Inputs :=
  ⟨constant 0, constant 0, ⟨[], 1⟩, ⟨[0, 1/64], 1/1048576⟩⟩

/-- The first radial-field monomial of the packed QA2R field has a genuinely
time-varying dyadic enclosure on the entire clock slab. -/
theorem first_radial_term (t : ℝ) (ht : |t| ≤ 1) :
    |evR 0 0 (Real.cos (t / 64)) (Real.sin (t / 64)) (dnR.take 1) -
        (-7848 / 16777216) * t| ≤ 2 / 16777216 := by
  have clock : clockFixture.Mem t 0 0 (Real.cos (t / 64)) (Real.sin (t / 64)) := by
    refine ⟨by simpa [clockFixture] using constant_mem 0 t,
      by simpa [clockFixture] using constant_mem 0 t, ?_, ?_⟩
    · simpa [clockFixture, Model.Mem] using Real.abs_cos_le_one (t / 64)
    · have bound := Real.abs_sub_sin_le (t / 64)
      rw [abs_sub_comm, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 64)] at bound
      have hc : |t| ^ 3 ≤ (1 : ℝ) ^ 3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
      change |Real.sin (t / 64) - eval [0,1/64] t| ≤ ((1/1048576 : ℚ) : ℝ)
      simp only [eval_cons, eval_nil, Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        mul_zero, add_zero, zero_add]
      convert bound.trans (show (|t| / 64) ^ 3 / 6 ≤ 1 / 1048576 by nlinarith) using 1; ring
  have eval := poly_mem (F := ⟨7,24⟩) ht clock (dnR.take 1)
  have coeffs : (poly ⟨7,24⟩ clockFixture (dnR.take 1)).poly = [0,-7848/16777216] :=
    eq_of_beq (by kernel_fact)
  have radius : (poly ⟨7,24⟩ clockFixture (dnR.take 1)).radius = 2/16777216 :=
    eq_of_beq (by kernel_fact)
  unfold Model.Mem at eval
  rw [coeffs, radius] at eval
  simpa [mul_comm t] using eval

end PlasmaLean.Design.DommaschkBounceTaylor
