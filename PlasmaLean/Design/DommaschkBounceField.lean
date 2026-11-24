/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamIdent
public import PlasmaLean.Certificates.ValidatedQuadrature

/-! # Checked interval evaluation of the physical QA2R field
The four input intervals enclose the shifted radius, height, cosine and sine.
The sparse coefficient lists are the same lists used in the QA2R field identification.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkBounceField

open PlasmaLean.Design.DommaschkKam DommaschkKam.DkPoly
open PlasmaLean.Certificates.ValidatedQuadrature
open Real

/-- Enclosures in the four variables of the candidate polynomial. -/
structure Box where
  u : FIv
  z : FIv
  c : FIv
  s : FIv

/-- Enclose a nonnegative integral power. -/
def powBox (I : FIv) : ℕ → FIv
  | 0 => FIv.ofInt 1
  | n+1 => (powBox I n).mul I

/-- Enclose one monomial, including its exact rational coefficient. -/
def termBox (B : Box) (t : Tm) : FIv :=
  (FIv.ofFrac t.q.num t.q.den).mul <|
    ((((powBox B.u t.a).mul (powBox B.z t.b)).mul (powBox B.c t.c)).mul (powBox B.s t.d))

/-- Sum the interval evaluations of the monomials. -/
def polyBox (B : Box) : SP → FIv
  | [] => FIv.ofInt 0
  | t :: ts => (termBox B t).add (polyBox B ts)

/-- A point belongs to all four input enclosures. -/
def Box.Mem (B : Box) (u z c s : ℝ) : Prop :=
  B.u.Mem u ∧ B.z.Mem z ∧ B.c.Mem c ∧ B.s.Mem s

theorem powBox_mem {I : FIv} {x : ℝ} (hx : I.Mem x) (n : ℕ) :
    (powBox I n).Mem (x ^ n) := by
  induction n with
  | zero => simpa [powBox] using FIv.mem_ofInt 1
  | succ n ih => simpa only [powBox, pow_succ] using FIv.mem_mul ih hx

theorem polyBox_mem {B : Box} {u z c s : ℝ} (h : B.Mem u z c s) (p : SP) :
    (polyBox B p).Mem (evR u z c s p) := by
  induction p with
  | nil => simpa [evR, polyBox] using FIv.mem_ofInt 0
  | cons t ts ih =>
    have hq : (FIv.ofFrac t.q.num t.q.den).Mem (t.q : ℝ) := by
      simpa only [Int.cast_natCast, Rat.cast_def] using FIv.mem_ofFrac t.q.num t.q.den
    exact FIv.mem_add (FIv.mem_mul hq (FIv.mem_mul (FIv.mem_mul
      (FIv.mem_mul (powBox_mem h.1 _) (powBox_mem h.2.1 _)) (powBox_mem h.2.2.1 _))
      (powBox_mem h.2.2.2 _))) ih

private theorem add_assoc_box (a b c : FIv) : (a.add b).add c = a.add (b.add c) := by
  simp [FIv.add, add_assoc, Bool.and_assoc]

theorem polyBox_append (B : Box) (p q : SP) :
    polyBox B (p ++ q) = (polyBox B p).add (polyBox B q) := by
  induction p with
  | nil => simp [polyBox, FIv.ofInt, FIv.add]
  | cons t p ih => simp only [List.cons_append, polyBox, ih, add_assoc_box]

/-- A proof tree may partition a sparse list into arbitrary consecutive blocks.
Only the evaluations within each block and the sums of their endpoints are kernel leaves. -/
inductive BlockCheck (B : Box) : SP → FIv → Prop where
  | nil : BlockCheck B [] (FIv.ofInt 0)
  | chunk {p : SP} (k : ℕ) (a b : FIv) {v : FIv} :
      polyBox B (p.take k) = a → a.add b = v →
      BlockCheck B (p.drop k) b → BlockCheck B p v

theorem BlockCheck.eq {B : Box} {p : SP} {v : FIv} (h : BlockCheck B p v) :
    polyBox B p = v := by
  induction h with
  | nil => rfl
  | @chunk p k a b v ha hs hb ih =>
    calc
      polyBox B p = polyBox B (p.take k ++ p.drop k) := by rw [List.take_append_drop]
      _ = _ := by rw [polyBox_append, ha, ih, hs]

/-- Real evaluation at an actual cylindrical point. -/
noncomputable def atPoint (p : SP) (R φ z : ℝ) : ℝ :=
  evR (R - dkR0) z (cos (2 * φ)) (sin (2 * φ)) p

/-- Every enclosure of the sparse polynomial encloses the identified physical quantity. -/
theorem field_id {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    atPoint dD R φ z = R^7 * cylBphi R φ z ∧
    atPoint dnR R φ z = R^8 * cylBR R φ z ∧
    atPoint dnZ R φ z = R^8 * cylBz R φ z := by
  have hd := Dp_ident hR φ z
  have hr := nRp_ident hR φ z
  have hz := nZp_ident hR φ z
  rw [Dp, eval_toPE, ptC, ev_ofReal] at hd
  rw [nRp, eval_toPE, ptC, ev_ofReal] at hr
  rw [nZp, eval_toPE, ptC, ev_ofReal] at hz
  exact ⟨Complex.ofReal_inj.mp hd, Complex.ofReal_inj.mp hr, Complex.ofReal_inj.mp hz⟩

end PlasmaLean.Design.DommaschkBounceField
