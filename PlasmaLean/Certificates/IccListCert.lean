/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import PlasmaLean.Certificates.EvalCert

/-!
# Finite sums and quantifiers over integer intervals as list computations (`icc_cert`)

The rational checks of `Design/ValidatedBVP` and `Design/ValidatedSlabData` are stated with
`Finset` sums and bounded quantifiers over integer intervals `Finset.Icc a b` (and over
`Finset.range n`). A `Finset` is a quotient (a `Multiset` of a list), which the evaluation
certificates of `Certificates/EvalCert.lean` do not enter. This module restates them as list
computations, once and for all:

* `sum_Icc_eq_list`: `∑ k ∈ Icc a b, f k = ((List.range (b + 1 - a).toNat).map (f (a + ·))).sum`;
* `sum_range_eq_list`: `∑ n ∈ range m, f n = ((List.range m).map f).sum`;
* `forall_Icc_of_all`, `forall_range_of_all`: a bounded quantifier from a Boolean `List.all`;
* `ite_mem_Icc`: an `if k ∈ Icc a b` becomes `if a ≤ k ∧ k ≤ b`.

The tactic **`icc_cert [d₁, …]`** unfolds the definitions `dᵢ`, rewrites with these lemmas
(`simp only`), reduces the goal to `decide p = true` and closes it by `eval_cert`: the rational
evaluation is then an explicit certificate (one node per rational operation, `ECert`).

**Sanity.** `iccCert_sum_fixture`, `iccCert_forall_fixture` (accepted), `iccCert_reject_fixture`
(a false bound is refused).
-/

public section

namespace PlasmaLean.Certificates.IccListCert

open Finset

/-- **A sum over `range m` is a list sum.** -/
theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ n ∈ range m, f n = ((List.range m).map f).sum := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- **A sum over an integer interval is a list sum.** -/
theorem sum_Icc_eq_list {M : Type*} [AddCommMonoid M] (a b : ℤ) (f : ℤ → M) :
    ∑ k ∈ Icc a b, f k = ((List.range (b + 1 - a).toNat).map fun i : ℕ => f (a + i)).sum := by
  rw [Int.Icc_eq_finset_map, sum_map, sum_range_eq_list]
  rfl

/-- **A bounded quantifier over an integer interval from a Boolean list check.** -/
theorem forall_Icc_of_all (a b : ℤ) (P : ℤ → Prop) [DecidablePred P]
    (h : ((List.range (b + 1 - a).toNat).all fun i : ℕ => decide (P (a + i))) = true) :
    ∀ k ∈ Icc a b, P k := by
  intro k hk
  rw [mem_Icc] at hk
  have := List.all_eq_true.1 h (k - a).toNat (List.mem_range.2 (by omega))
  have hk' : a + ((k - a).toNat : ℤ) = k := by omega
  rw [hk'] at this
  simpa using this

/-- **A bounded quantifier over `range m` from a Boolean list check.** -/
theorem forall_range_of_all (m : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ((List.range m).all fun n => decide (P n)) = true) : ∀ n ∈ range m, P n := by
  intro n hn
  simpa using List.all_eq_true.1 h n (List.mem_range.2 (mem_range.1 hn))

/-- **Membership in an integer interval inside an `if`.** -/
theorem ite_mem_Icc {α : Type*} (a b k : ℤ) (x y : α) :
    (if k ∈ Icc a b then x else y) = if a ≤ k ∧ k ≤ b then x else y := by
  simp only [mem_Icc]

/-- **`icc_cert [d₁, …]`**: unfold `d₁, …`, restate the `Finset` sums, bounded quantifiers and
memberships over integer intervals and `range` as list computations, and close the resulting
decision by an evaluation certificate (`eval_cert`). -/
syntax (name := iccCertStx) "icc_cert" " [" ident,* "]" : tactic

/-- The closing step of `icc_cert`: a bounded quantifier or a decision, by `eval_cert`. -/
macro "icc_close" : tactic => `(tactic| first
  | (apply forall_Icc_of_all; eval_cert)
  | (apply forall_range_of_all; eval_cert)
  | (apply of_decide_eq_true; eval_cert))

macro_rules
  | `(tactic| icc_cert [$ds,*]) => do
    let ls : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← ds.getElems.mapM fun d =>
      `(Lean.Parser.Tactic.simpLemma| $d:ident)
    `(tactic| (simp only [$ls,*, sum_Icc_eq_list, sum_range_eq_list, ite_mem_Icc]; icc_close))

/-! ## Sanity -/

/-- A fixture function. -/
def fixF (k : ℤ) : ℚ := if k ∈ Icc (-1 : ℤ) 1 then (k : ℚ) / 2 else 1

/-- **Sanity** (accepted): a sum with an interval membership inside. -/
theorem iccCert_sum_fixture : ∑ k ∈ Icc (-2 : ℤ) 2, |fixF k| ≤ 3 := by
  icc_cert [fixF]

/-- **Sanity** (accepted): a bounded quantifier with an inner sum. -/
theorem iccCert_forall_fixture :
    ∀ m ∈ Icc (-2 : ℤ) 2, ∑ k ∈ Icc (-1 : ℤ) 1, |fixF (k + m)| ≤ 3 := by
  icc_cert [fixF]

/-- **Sanity** (rejected): a false bound is refused. -/
theorem iccCert_reject_fixture : True := by
  fail_if_success (have : ∑ k ∈ Icc (-2 : ℤ) 2, |fixF k| ≤ 2 := by icc_cert [fixF])
  trivial

end PlasmaLean.Certificates.IccListCert
