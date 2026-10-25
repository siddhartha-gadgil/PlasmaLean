/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public meta import PlasmaLeanMeta.EvalCert

/-!
# Evaluation certificates for ball, interval and polynomial terms (`eval_cert`)

The remaining kernel-evaluated checks of the library (`legAOk`, `cellCheck`, `lineOut4 … = data`,
`cornerOK`, `pieceCheck*`) are closed terms built from ball or interval operations (`FIv.add`,
`FIv.mul`, …), integer and rational arithmetic, records, lists, `if`, `match` and structural
recursion over cells. Closing them by one `Eq.refl` (or `decide +kernel`) leaves the whole
evaluation opaque, and `bool_cert` stops at comparison leaves that still contain whole ball
evaluations. This module certifies the evaluation itself, node by node, in the SubsetSum
pattern.

* **`ECert e v`**: the closed term `e` evaluates to the value `v` (a constructor term over
  literals: integers, Booleans, balls, pairs, lists, records). One constructor per node of the
  term tree:
  - `lit`: a value evaluates to itself;
  - `op₁`, `op₂`, `op₃`: an **operation node** `f t₁ … tₖ` (e.g. `FIv.add t₁ t₂`, `x * y` on
    `ℤ`, `decide (x ≤ y)`, a record field): the children evaluate to `v₁ … vₖ` and the single
    operation `f v₁ … vₖ = v` on values is a **leaf**, checked by the kernel (`Eq.refl v`). So
    "the ball of `t₁ + t₂` is the outward-rounded sum of the balls of `t₁` and `t₂`" is
    `op₂ FIv.add t₁ t₂ I J (I.add J)` with leaf `I.add J = ⟨…⟩`;
  - `leaf`: an operation whose arguments are already values, and `arg`: one argument of a node
    replaced by its value (nodes with more than three evaluated children);
  - `unfold`: a step `e = e'` by the equation lemma `f.eq_def` of a recursive definition (sums
    and products over cells, Horner recursion, list recursion); non-recursive definitions,
    `match` on a value, `β`/`ζ` steps and projections of records are definitional steps carried
    as type hints;
  - `ite_t`/`ite_f`, `dite_t`/`dite_f`: the branch of an `if`, with the certificate of its
    condition (only the branch taken is evaluated).
* **`ECert.sound`**: soundness, `ECert e v → e = v`, by induction. With the soundness theorem of
  a checker (`checker … = true → per-cell inequality`), the certificate implies the checker's
  per-cell inequality.
* **`eval_cert`**: the `meta` builder, a call-by-value evaluator. Every intermediate value is
  computed **once** and held as a **shared expression**: the builder keeps a table from each
  evaluated subterm to its value and certificate, so a subterm occurring many times (a cell
  record read for several fields, a prefix sum reused by the next cell, an interval used by
  several checks) appears once in the proof DAG and is checked once by the kernel. Values of
  leaves are computed in `meta` code (Lean's own integer arithmetic, or the kernel's `whnf` on a
  single operation applied to values); the kernel re-checks each leaf when the declaration is
  added. The builder lives in `PlasmaLeanMeta/EvalCert.lean`, a library precompiled to native
  code (`lakefile.toml`); interpreted, it cost as much as the kernel check itself.

**Size.** The certificate has one node per operation, about 300–400 bytes each in the `.olean`.
Checks of a few hundred operations (final combinations, small cell checks) cost ≈ 0.1 MB each;
checks of ≈ 4·10⁴ interval operations (the oscillation legs `legAOk`) cost ≈ 13 MB each and are
left to `decide +kernel` for now (see the implementation plan, Phase 16 stage 4).

The operations that are leaves are the arithmetic operations (`+`, `-`, `*`, `/`, `%`, `^`, `max`,
`min`, casts, numerals on `ℕ`/`ℤ`), the Boolean connectives, comparisons under `decide`, record
fields, and the extra operations listed in `eval_cert [f₁, …]` (for example the ball operations
`FIv.add`, `FIv.mul`, … of `Certificates/ValidatedQuadrature`; see `fiv_cert` in
`Certificates/EvalCertFIv.lean`). Every other definition is unfolded. A leaf is never a whole
evaluation: its arguments are values.

**Sanity.** `ECert.sound_lit` (degenerate case), `evalCert_fixture` (accepted: a recursive
integer interval sum with `if` and records), `evalCert_false_fixture` (a check evaluating to
`false`), `evalCert_reject_fixture` (a false equation is refused).
-/

@[expose] public section

namespace PlasmaLean.Certificates.EvalCert

open Lean Meta Elab Tactic

/-- **Certificate that the closed term `e` evaluates to the value `v`.** One constructor per node
of the term tree; the arguments are explicit so that the `meta` builder can supply them. -/
inductive ECert : {α : Type} → α → α → Prop where
  /-- A value evaluates to itself. -/
  | lit {α : Type} (v : α) : ECert v v
  /-- A single operation on values, checked by the kernel. -/
  | leaf {α : Type} (e v : α) : e = v → ECert e v
  /-- A unary operation node: the child evaluates to `xv`, and `f xv = v` is a kernel leaf. -/
  | op₁ {α β : Type} (f : β → α) (x xv : β) (v : α) : ECert x xv → f xv = v → ECert (f x) v
  /-- A binary operation node (e.g. the ball sum of two balls), with one kernel leaf. -/
  | op₂ {α β γ : Type} (f : β → γ → α) (x : β) (y : γ) (xv : β) (yv : γ) (v : α) :
      ECert x xv → ECert y yv → f xv yv = v → ECert (f x y) v
  /-- A ternary operation node, with one kernel leaf. -/
  | op₃ {α β γ δ : Type} (f : β → γ → δ → α) (x : β) (y : γ) (z : δ) (xv : β) (yv : γ)
      (zv : δ) (v : α) :
      ECert x xv → ECert y yv → ECert z zv → f xv yv zv = v → ECert (f x y z) v
  /-- One argument of a node replaced by its value. -/
  | arg {α β : Type} (g : β → α) (x xv : β) (v : α) : ECert x xv → ECert (g xv) v → ECert (g x) v
  /-- An unfolding step by an equation lemma. -/
  | unfold {α : Type} (e e' v : α) : e = e' → ECert e' v → ECert e v
  /-- The `then` branch of `if c then x else y`, with the certificate of the condition. -/
  | ite_t {α : Type} (c : Prop) (h : Decidable c) (x y v : α) :
      ECert (@decide c h) true → ECert x v → ECert (@ite α c h x y) v
  /-- The `else` branch of `if c then x else y`, with the certificate of the condition. -/
  | ite_f {α : Type} (c : Prop) (h : Decidable c) (x y v : α) :
      ECert (@decide c h) false → ECert y v → ECert (@ite α c h x y) v
  /-- The `then` branch of a dependent `if`. -/
  | dite_t {α : Type} (c : Prop) (h : Decidable c) (x : c → α) (y : ¬c → α) (v : α) (hc : c) :
      ECert (x hc) v → ECert (@dite α c h x y) v
  /-- The `else` branch of a dependent `if`. -/
  | dite_f {α : Type} (c : Prop) (h : Decidable c) (x : c → α) (y : ¬c → α) (v : α) (hc : ¬c) :
      ECert (y hc) v → ECert (@dite α c h x y) v

/-- **Soundness**: a certified term has the certified value. -/
theorem ECert.sound {α : Type} {e v : α} (h : ECert e v) : e = v := by
  induction h with
  | lit => rfl
  | leaf _ _ h => exact h
  | op₁ f x xv v _ h ih => rw [ih, h]
  | op₂ f x y xv yv v _ _ h ih₁ ih₂ => rw [ih₁, ih₂, h]
  | op₃ f x y z xv yv zv v _ _ _ h ih₁ ih₂ ih₃ => rw [ih₁, ih₂, ih₃, h]
  | arg g x xv v _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | unfold e e' v h _ ih => rw [h, ih]
  | ite_t c h x y v _ _ ihc ihx => rw [ite_eq_left (of_decide_eq_true ihc), ihx]
  | ite_f c h x y v _ _ ihc ihy => rw [ite_eq_right (of_decide_eq_false ihc), ihy]
  | dite_t c h x y v hc _ ih => rw [dite_eq_left hc, ih]
  | dite_f c h x y v hc _ ih => rw [dite_eq_right hc, ih]

/-- **Sanity** (degenerate case): the certificate of a value. -/
theorem ECert.sound_lit {α : Type} (v : α) : (ECert.lit v).sound = rfl := rfl

/-- `decide (p ∧ q)` is the conjunction of the decisions (an unfolding step for `eval_cert`). -/
theorem decide_and_eq (p q : Prop) (hp : Decidable p) (hq : Decidable q) :
    @decide (p ∧ q) (@instDecidableAnd p q hp hq) = (@decide p hp && @decide q hq) := by
  cases hp <;> cases hq <;> rfl

/-- `decide (p ∨ q)` is the disjunction of the decisions. -/
theorem decide_or_eq (p q : Prop) (hp : Decidable p) (hq : Decidable q) :
    @decide (p ∨ q) (@instDecidableOr p q hp hq) = (@decide p hp || @decide q hq) := by
  cases hp <;> cases hq <;> rfl

/-- `decide ¬p` is the negation of the decision. -/
theorem decide_not_eq (p : Prop) (hp : Decidable p) :
    @decide (¬p) (@instDecidableNot p hp) = !(@decide p hp) := by
  cases hp <;> rfl

/-! ## Sanity -/

/-- An integer interval for the fixtures. -/
structure FixIv where
  /-- Lower end. -/
  lo : Int
  /-- Upper end. -/
  hi : Int

/-- Interval sum (an operation of the fixtures). -/
def FixIv.add (I J : FixIv) : FixIv := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Interval product (an operation of the fixtures). -/
def FixIv.mul (I J : FixIv) : FixIv :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Horner-type recursion over cells with a shared prefix (the fixture's checker). -/
def fixSum (c : Nat → FixIv) : Nat → FixIv
  | 0 => ⟨0, 0⟩
  | n + 1 => (fixSum c n).add ((c n).mul (c n))

/-- The fixture's cell intervals. -/
def fixCell (i : Nat) : FixIv := if i % 2 = 0 then ⟨-(i : Int), 1⟩ else ⟨1, (i : Int) + 2⟩

/-- The fixture's check: the sum of the squared cells lies below `100`. -/
def fixCheck (n : Nat) : Bool := decide ((fixSum fixCell n).hi ≤ 100) && decide (0 ≤ 1)

/-- **Sanity** (accepted): a recursive interval evaluation, by `eval_cert` with the interval
operations as leaves. -/
theorem evalCert_fixture : fixSum fixCell 4 = ⟨0, 39⟩ := by
  eval_cert [FixIv.add, FixIv.mul]

/-- **Sanity** (a Boolean check). -/
theorem evalCert_check_fixture : fixCheck 5 = true := by
  eval_cert [FixIv.add, FixIv.mul]

/-- **Sanity** (a check evaluating to `false`). -/
theorem evalCert_false_fixture : fixCheck 8 = false := by
  eval_cert

/-- **Sanity** (rejected): a false equation is refused. -/
theorem evalCert_reject_fixture : True := by
  fail_if_success (have : fixSum fixCell 4 = ⟨0, 40⟩ := by eval_cert)
  trivial

end PlasmaLean.Certificates.EvalCert
