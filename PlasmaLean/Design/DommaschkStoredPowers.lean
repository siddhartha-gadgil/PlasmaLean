/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceTaylor

/-! # Shared certified powers in sparse Taylor evaluation

Each stored power is identified with the original rounded power model. Every
polynomial block can therefore use a table lookup while retaining the existing
physical field and derivative certificate interface.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkStoredPowers

open DommaschkBounceTaylor DommaschkKam DommaschkKam.DkPoly
open Certificates.TrajectoryTaylorModel

inductive Valid (f : Format) (a : Model) : ℕ → List Model → Prop where
  | nil (i : ℕ) : Valid f a i []
  | cons {i : ℕ} {y : Model} {ys : List Model} (val : Matches (f.pow a i) y)
      (rest : Valid f a (i + 1) ys) : Valid f a i (y :: ys)

theorem Valid.get {f a i data} (ok : Valid f a i data) {k : ℕ} {v : Model}
    (h : data[k]? = some v) : f.pow a (i + k) = v := by
  induction ok generalizing k with
  | nil i => simp at h
  | @cons i y ys val _ ih =>
    cases k with
    | zero =>
      simp at h
      simpa [h] using val.eq
    | succ k =>
      have h' : ys[k]? = some v := by simpa using h
      simpa only [Nat.add_right_comm i 1 k, Nat.add_assoc] using ih h'

def lookup (f : Format) (a : Model) (p : List Model) (k : ℕ) : Model :=
  match p[k]? with
  | some v => v
  | none => f.pow a k

theorem lookup_eq {f a p} (h : Valid f a 0 p) (k : ℕ) : lookup f a p k = f.pow a k := by
  unfold lookup
  split
  · rename_i v e
    simpa only [Nat.zero_add] using (h.get e).symm
  · rfl

structure Powers where
  u : List Model
  z : List Model
  cos : List Model
  sin : List Model

structure Powers.Checked (p : Powers) (f : Format) (a : Inputs) : Prop where
  u : Valid f a.u 0 p.u
  z : Valid f a.z 0 p.z
  cos : Valid f a.cos 0 p.cos
  sin : Valid f a.sin 0 p.sin

def term (p : Powers) (f : Format) (a : Inputs) (q : Tm) : Model :=
  f.mul (constant q.q) (f.mul (f.mul (f.mul (lookup f a.u p.u q.a)
    (lookup f a.z p.z q.b)) (lookup f a.cos p.cos q.c)) (lookup f a.sin p.sin q.d))

def poly (p : Powers) (f : Format) (a : Inputs) : SP → Model
  | [] => constant 0
  | m :: ms => f.add (term p f a m) (poly p f a ms)

theorem poly_eq {p f a} (hp : Powers.Checked p f a) (sp : SP) :
    poly p f a sp = DommaschkBounceTaylor.poly f a sp := by
  induction sp with
  | nil => rfl
  | cons q qs ih =>
    simp only [poly, DommaschkBounceTaylor.poly, ih, term, DommaschkBounceTaylor.term,
      lookup_eq hp.u, lookup_eq hp.z, lookup_eq hp.cos, lookup_eq hp.sin]

/-- A chunk checked with shared powers constructs precisely the existing
`Blocks` predicate on the original sparse polynomial. -/
theorem checkedChunk {f a sp} (p : Powers) (hp : Powers.Checked p f a)
    (k : ℕ) (head tail out : Model) (terms : Matches (poly p f a (sp.take k)) head)
    (rest : Blocks f a (sp.drop k) tail) (combine : Matches (f.add head tail) out) :
    Blocks f a sp out := by
  rw [poly_eq hp] at terms
  exact Blocks.chunk k head tail out terms rest combine

end PlasmaLean.Design.DommaschkStoredPowers
