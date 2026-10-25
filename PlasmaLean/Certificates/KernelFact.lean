/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronProof
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Eval
public meta import Lean.Meta.Offset
public meta import PlasmaLean.Certificates.KronProof

/-!
# Closed side conditions as explicit proof terms (`kernel_fact`)

The tactic **`kernel_fact`** replaces `decide +kernel` for the closed side conditions of the
family ball bridges and chains (degree conditions `nodeDims3N`, box and image equations, rational
bounds, conditions on the stored coefficients and on grids). It builds an explicit proof term:
conjunctions are split, list quantifiers `∀ x ∈ l` and bounded quantifiers `∀ i ≤ n`, `∀ i < n`
on `ℕ` are expanded element by element, and the leaves are kernel facts closed by `Eq.refl`
(`Nat.ble a c = true`, `Nat.beq a c = false`, `Rat.blt a c`, `a = a`), which only the kernel
evaluates. No `decide`.

Quantifiers `∀ i : Fin n` are expanded through `Fin.forall_fin_succ`, and implications `a = c → B`
with a closed hypothesis on `ℕ` are decided from the values of both sides (the failing case is the
kernel fact `Nat.beq a c = false`).

**Sanity.** `kernelFact_fixture`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronProof

open Lean Meta Elab Tactic

/-- `∀ i ≤ 0, p i` from `p 0`. -/
theorem forall_le_zero' (p : Nat → Prop) (h : p 0) : ∀ i, i ≤ 0 → p i :=
  fun i hi => by rw [Nat.le_zero.1 hi]; exact h

/-- `∀ i ≤ n + 1, p i` from `∀ i ≤ n, p i` and `p (n + 1)`. -/
theorem forall_le_succ' (p : Nat → Prop) (n : Nat) (h : ∀ i, i ≤ n → p i) (h' : p (n + 1)) :
    ∀ i, i ≤ n + 1 → p i := fun i hi => by
  rcases Nat.lt_or_eq_of_le hi with hi | hi
  · exact h i (Nat.le_of_lt_succ hi)
  · rw [hi]; exact h'

/-- `∀ i < 0, p i`. -/
theorem forall_lt_zero' (p : Nat → Prop) (k : Nat) (hk : k = 0) : ∀ i, i < k → p i :=
  fun i hi => absurd hi (by rw [hk]; exact Nat.not_lt_zero i)

/-- `∀ i < n + 1, p i` from `∀ i ≤ n, p i`. -/
theorem forall_lt_of_le' (p : Nat → Prop) (n : Nat) (h : ∀ i, i ≤ n → p i) :
    ∀ i, i < n + 1 → p i := fun i hi => h i (Nat.le_of_lt_succ hi)

/-- `∀ x ∈ [], p x`. -/
theorem forall_mem_nil' {α : Type} (p : α → Prop) : ∀ x ∈ ([] : List α), p x :=
  fun _ h => nomatch h

/-- `∀ x ∈ a :: l, p x` from `p a` and `∀ x ∈ l, p x`. -/
theorem forall_mem_cons' {α : Type} (p : α → Prop) (a : α) (l : List α) (h : p a)
    (t : ∀ x ∈ l, p x) : ∀ x ∈ a :: l, p x :=
  List.forall_mem_cons.2 ⟨h, t⟩

/-- `∀ i : Fin 0, p i`. -/
theorem forall_fin_zero' (p : Fin 0 → Prop) : ∀ i, p i := fun i => i.elim0

/-- `∀ i : Fin (n + 1), p i` from `p 0` and `∀ i : Fin n, p i.succ`. -/
theorem forall_fin_succ' (n : Nat) (p : Fin (n + 1) → Prop) (h : p ⟨0, Nat.succ_pos n⟩)
    (t : ∀ i : Fin n, p i.succ) : ∀ i, p i := Fin.forall_fin_succ.2 ⟨h, t⟩

/-- An implication whose hypothesis holds, from its conclusion. -/
theorem imp_of_concl' {A B : Prop} (h : B) : A → B := fun _ => h

/-- An implication whose hypothesis `a = c` on `ℕ` fails (the kernel fact `Nat.beq a c = false`). -/
theorem imp_of_nat_ne' (a c : Nat) (B : Prop) (h : Nat.beq a c = false) : a = c → B :=
  fun e => absurd e (Nat.ne_of_beq_eq_false h)

/-- The value of a small closed natural-number expression, by `whnf` (no compiled code, so that
no `meta import` of the data modules is needed). -/
meta def natValue (e : Expr) : MetaM Nat := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return n
  if let some n := e.rawNatLit? then return n
  if let some n ← Meta.evalNat e |>.run then return n
  let e' ← whnfD e
  if let some n := e'.nat? then return n
  if let some n := e'.rawNatLit? then return n
  throwError "kernel_fact: cannot evaluate the bound{indentExpr e}"

/-- **Proof term of a closed fact** built from `∧`, `True`, `≤`, `<`, `≠` on `ℕ`, `≤`, `<` on `ℚ`,
equations and `∀ x ∈ l` over a closed list: conjunctions are split, list quantifiers expanded
element by element, `a ≤ c` on `ℕ` becomes the kernel fact `Nat.ble a c = true`, `a < c` the fact
`Nat.ble (a + 1) c = true`, `a ≠ c` the fact `Nat.beq a c = false`, `a ≤ c` on `ℚ` the fact
`Rat.blt c a = false`, `a < c` on `ℚ` the fact `Rat.blt a c = true`, and an equation `a = c` the
leaf `Eq.refl a` (the kernel evaluates both sides); any other head is unfolded (`fuel` times). The
leaves are checked by the kernel only. -/
meta partial def kernelFactTerm (P : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let P ← instantiateMVars P
  if P.hasExprMVar then throwError "kernel_fact: the goal has metavariables{indentExpr P}"
  let pf ← match P.getAppFnArgs with
    | (``And, #[a, b]) =>
      pure (mkApp4 (mkConst ``And.intro) a b (← kernelFactTerm a fuel) (← kernelFactTerm b fuel))
    | (``True, #[]) => pure (mkConst ``True.intro)
    | (``LE.le, #[α, _, x, y]) =>
      if α.isConstOf ``Nat then
        pure (mkApp3 (mkConst ``Nat.le_of_ble_eq_true) x y (reflBool true))
      else if α.isConstOf ``Rat then pure (reflBool false)
      else unfoldOrFail P
    | (``LT.lt, #[α, _, x, y]) =>
      if α.isConstOf ``Nat then pure (mkApp3 (mkConst ``lt_of_ble_succ) x y (reflBool true))
      else if α.isConstOf ``Rat then pure (reflBool true)
      else unfoldOrFail P
    | (``Eq, #[_, a, _]) => mkEqRefl a
    | (``Not, #[Q]) =>
      match Q.getAppFnArgs with
      | (``Eq, #[α, a, b]) =>
        if α.isConstOf ``Nat then
          pure (mkApp3 (mkConst ``Nat.ne_of_beq_eq_false) a b (reflBool false))
        else throwError "kernel_fact: unsupported negation{indentExpr P}"
      | _ => throwError "kernel_fact: unsupported negation{indentExpr P}"
    | _ =>
      match forallMem? P with
      | some (α, l, p) => forallMem α l p
      | none =>
        match forallLe? P with
        | some (strict, n, p) => forallLe strict p (← natValue n) n
        | none =>
          match forallFin? P with
          | some (n, p) => forallFin p (← natValue n)
          | none =>
            match P with
            | .forallE _ A B _ =>
              if B.hasLooseBVars then unfoldOrFail P else implication A B
            | _ => unfoldOrFail P
  mkExpectedTypeHint pf P
where
  /-- Unfold the head of the goal and retry. -/
  unfoldOrFail (P : Expr) : MetaM Expr := do
    if fuel = 0 then throwError "kernel_fact: unsupported goal{indentExpr P}"
    match ← unfoldDefinition? P with
    | some P' => kernelFactTerm P'.headBeta (fuel - 1)
    | none =>
      let P' ← whnfR P
      if P' == P then throwError "kernel_fact: unsupported goal{indentExpr P}"
      kernelFactTerm P' (fuel - 1)
  /-- `∀ x, x ∈ l → q x` as `(α, l, fun x => q x)`. -/
  forallMem? (P : Expr) : Option (Expr × Expr × Expr) :=
    match P with
    | .forallE n α (.forallE _ mem q _) bi =>
      match mem.getAppFnArgs with
      | (``Membership.mem, #[_, _, _, l, .bvar 0]) =>
        if q.hasLooseBVar 0 || l.hasLooseBVars then none
        else some (α, l, .lam n α (q.lowerLooseBVars 1 1) bi)
      | _ => none
    | _ => none
  /-- `∀ i, i ≤ n → q i` (or `i < n`) on `ℕ` as `(strict, n, fun i => q i)`. -/
  forallLe? (P : Expr) : Option (Bool × Expr × Expr) :=
    match P with
    | .forallE n α (.forallE _ hyp q _) bi =>
      if !α.isConstOf ``Nat then none else
      match hyp.getAppFnArgs with
      | (``LE.le, #[β, _, .bvar 0, m]) | (``LT.lt, #[β, _, .bvar 0, m]) =>
        if !β.isConstOf ``Nat || q.hasLooseBVar 0 || m.hasLooseBVars then none
        else some (hyp.isAppOf ``LT.lt, m, .lam n α (q.lowerLooseBVars 1 1) bi)
      | _ => none
    | _ => none
  /-- `∀ i : Fin n, q i` as `(n, fun i => q i)`. -/
  forallFin? (P : Expr) : Option (Expr × Expr) :=
    match P with
    | .forallE n α q bi =>
      match α.getAppFnArgs with
      | (``Fin, #[m]) => if m.hasLooseBVars then none else some (m, .lam n α q bi)
      | _ => none
    | _ => none
  /-- Expand `∀ i : Fin n, p i` (for the value `n` of the bound) through `Fin.forall_fin_succ`. -/
  forallFin (p : Expr) (nv : Nat) : MetaM Expr := do
    if nv = 0 then return mkApp (mkConst ``forall_fin_zero') p
    let n' := mkRawNatLit (nv - 1)
    let i₀ := mkApp3 (mkConst ``Fin.mk) (mkApp (mkConst ``Nat.succ) n') (mkRawNatLit 0)
      (mkApp (mkConst ``Nat.succ_pos) n')
    let h₀ ← kernelFactTerm (mkApp p i₀).headBeta fuel
    let pS := Expr.lam `i (mkApp (mkConst ``Fin) n')
      (mkApp p (mkApp2 (mkConst ``Fin.succ) n' (.bvar 0))) .default
    let t ← forallFin pS (nv - 1)
    return mkApp4 (mkConst ``forall_fin_succ') n' p h₀ t
  /-- An implication `A → B` with a closed hypothesis: `A` is an equation on `ℕ`, decided from
  the values of both sides (`imp_of_nat_ne'` when it fails), or holds (`imp_of_concl'`). -/
  implication (A B : Expr) : MetaM Expr := do
    match A.getAppFnArgs with
    | (``Eq, #[α, a, c]) =>
      if α.isConstOf ``Nat then
        if (← natValue a) == (← natValue c) then
          return mkApp3 (mkConst ``imp_of_concl') A B (← kernelFactTerm B fuel)
        else return mkApp4 (mkConst ``imp_of_nat_ne') a c B (reflBool false)
      else throwError "kernel_fact: unsupported hypothesis{indentExpr A}"
    | _ => throwError "kernel_fact: unsupported hypothesis{indentExpr A}"
  /-- Expand `∀ i ≤ k, p i` (`strict`: `∀ i < k`) for the value `kv` of `k`, one index at a time. -/
  forallLe (strict : Bool) (p : Expr) (kv : Nat) (k : Expr) : MetaM Expr := do
    if strict then
      if kv = 0 then return mkApp3 (mkConst ``forall_lt_zero') p k (reflNat 0)
      let k' := mkRawNatLit (kv - 1)
      let h ← forallLe false p (kv - 1) k'
      return mkApp3 (mkConst ``forall_lt_of_le') p k' h
    let h₀ ← kernelFactTerm (mkApp p (mkRawNatLit 0)).headBeta fuel
    let mut pf := mkApp2 (mkConst ``forall_le_zero') p h₀
    for i in [1:kv + 1] do
      let hi ← kernelFactTerm (mkApp p (mkRawNatLit i)).headBeta fuel
      pf := mkApp4 (mkConst ``forall_le_succ') p (mkRawNatLit (i - 1)) pf hi
    return pf
  /-- Expand `∀ x ∈ l, p x` over the cells of the closed list `l`. -/
  forallMem (α l p : Expr) : MetaM Expr := do
    let l' ← whnfD l
    match l'.getAppFnArgs with
    | (``List.nil, _) => pure (mkApp2 (mkConst ``forall_mem_nil') α p)
    | (``List.cons, #[_, a, t]) =>
      let h ← kernelFactTerm (mkApp p a).headBeta fuel
      let ht ← forallMem α t p
      pure (mkAppN (mkConst ``forall_mem_cons') #[α, p, a, t, h, ht])
    | _ => throwError "kernel_fact: list did not reduce to a constructor{indentExpr l'}"

/-- **`kernel_fact`**: prove a closed fact built from `∧`, `≤`, `<`, `≠` on `ℕ` and equations by an
explicit proof term whose leaves are kernel facts (`kernelFactTerm`); replaces `decide +kernel`
for degree conditions and small side conditions. -/
syntax (name := kernelFact) "kernel_fact" : tactic

/-- The elaborator of `kernel_fact`. -/
@[tactic kernelFact] meta def evalKernelFact : Tactic := fun _ => do
  let g ← getMainGoal
  g.assign (← kernelFactTerm (← instantiateMVars (← g.getType)))
  replaceMainGoal []

/-- **Sanity**: `kernel_fact` on a conjunction of closed facts. -/
theorem kernelFact_fixture : 2 ≤ 3 ∧ 3 < 2 ^ 2 ∧ (5 : Nat) ≠ 6 ∧ 2 + 2 = 4 ∧ 7 ≥ 7 ∧
    (1 / 3 : Rat) < 1 / 2 ∧ (2 / 4 : Rat) ≤ 1 / 2 ∧ (∀ x ∈ [1, 2, 3], x ≤ 3) ∧
    (∀ i ≤ 3, i * i ≤ 9) ∧ (∀ i < 2 * 2, i + 1 ≤ 4) ∧ (∀ i < 0, i = 7) ∧
    (∀ i : Fin 3, (i : Nat) ≤ 2) ∧ (∀ i < 4, i % 2 = 0 → i ≤ 2) := by
  kernel_fact

end PlasmaLean.Certificates.KronProof
