/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public meta import Lean.Elab.Tactic.Basic

/-!
# Boolean checkers as explicit certificates (`bool_cert`)

Many certificate checks in the library are Boolean checkers `check data = true` that recurse
over lists of cells, rows, elements or terms and combine local comparisons with `&&`, `||`, `!`,
`if` and `bif`. Closing such a goal by one `Eq.refl` (or `decide +kernel`) leaves the whole
evaluation opaque. This module replaces it by an explicit certificate in the SubsetSum pattern:

* **`BCert b v`**: the Boolean `b` evaluates to `v`. One constructor per local step of a checker:
  a conjunction (both sides true, or one side false), a disjunction (one side true, or both
  false), a negation, a branch of `if`/`bif` together with the certificate of its condition, a
  conjunction or disjunction of decidable propositions, and **leaves** `b = v` that are single
  comparisons (`decide (x ≤ y)`, `decide (x < y)`, `decide (x = y)` on `ℕ`, `ℤ`, `ℚ`, `Nat.ble`,
  `Nat.beq`, `==`), checked by the kernel with GMP arithmetic.
* **`BCert.sound`**: soundness, `BCert b v → b = v`, by induction.
* **`bool_cert`**: the `meta` builder. It unfolds the checker one definition (or matcher) at a
  time until the head is a connective or a comparison (`whnfHeadPred`), so that the recursion of
  the checker over its list of cells/rows/elements becomes a tree of `and_tt` steps with one
  subtree per cell, and each cell's subtree ends in its own comparison leaves. Every node carries
  its unreduced statement as a type hint, so the kernel checks the unfolding steps by
  definitional unfolding only. The values needed to pick a branch (`||`, `if`, a false side of
  `&&`) are computed by `whnf` in `meta` code; the kernel re-checks them through the leaves.

A leaf is never a whole checker: the builder refuses (with an error) any stuck subterm that is
not a comparison, a field of a computed record or a `match` on a computed value. The last two
kinds (*collapsed* leaves, reported by `bool_cert?`) cover record projections, list lookups and
validity flags; their operands, like those of the comparisons, may still be arithmetic over the
data (polynomial or ball evaluations), which the kernel evaluates inside the leaf.

**Sanity.** `BCert.sound_true`, `boolCert_fixture` (accepted: a small list checker with `&&`,
`||`, `!`, `if` and `ℚ` comparisons), `boolCert_false_fixture` (a checker evaluating to `false`),
`boolCert_reject_fixture` (a false check is refused by `bool_cert?`, by `fail_if_success`; with
`bool_cert` the kernel refuses it).
-/

@[expose] public section

namespace PlasmaLean.Certificates.BoolCert

open Lean Meta Elab Tactic

/-- **Certificate that the Boolean `b` evaluates to `v`.** One constructor per local step of a
Boolean checker; the arguments are explicit so that the `meta` builder can supply them. -/
inductive BCert : Bool → Bool → Prop where
  /-- A leaf: a single comparison, checked by the kernel. -/
  | leaf (b v : Bool) : b = v → BCert b v
  /-- `a && b` is true if both sides are. -/
  | and_tt (a b : Bool) : BCert a true → BCert b true → BCert (a && b) true
  /-- `a && b` is false if the left side is. -/
  | and_ffl (a b : Bool) : BCert a false → BCert (a && b) false
  /-- `a && b` is false if the right side is. -/
  | and_ffr (a b : Bool) : BCert b false → BCert (a && b) false
  /-- `a || b` is true if the left side is. -/
  | or_ttl (a b : Bool) : BCert a true → BCert (a || b) true
  /-- `a || b` is true if the right side is. -/
  | or_ttr (a b : Bool) : BCert b true → BCert (a || b) true
  /-- `a || b` is false if both sides are. -/
  | or_ff (a b : Bool) : BCert a false → BCert b false → BCert (a || b) false
  /-- Negation. -/
  | not (a v : Bool) : BCert a v → BCert (!a) (!v)
  /-- The `then` branch of `if c then x else y`, with the certificate of the condition. -/
  | ite_t (c : Prop) (h : Decidable c) (x y v : Bool) :
      BCert (@decide c h) true → BCert x v → BCert (@ite Bool c h x y) v
  /-- The `else` branch of `if c then x else y`, with the certificate of the condition. -/
  | ite_f (c : Prop) (h : Decidable c) (x y v : Bool) :
      BCert (@decide c h) false → BCert y v → BCert (@ite Bool c h x y) v
  /-- The `then` branch of `bif c then x else y`. -/
  | cond_t (c x y v : Bool) : BCert c true → BCert x v → BCert (cond c x y) v
  /-- The `else` branch of `bif c then x else y`. -/
  | cond_f (c x y v : Bool) : BCert c false → BCert y v → BCert (cond c x y) v
  /-- `decide (p ∧ q)` is true if both decisions are. -/
  | dand_tt (p q : Prop) (hp : Decidable p) (hq : Decidable q) :
      BCert (@decide p hp) true → BCert (@decide q hq) true →
      BCert (@decide (p ∧ q) (@instDecidableAnd p q hp hq)) true
  /-- `decide (p ∨ q)` is true if the left decision is. -/
  | dor_ttl (p q : Prop) (hp : Decidable p) (hq : Decidable q) :
      BCert (@decide p hp) true → BCert (@decide (p ∨ q) (@instDecidableOr p q hp hq)) true
  /-- `decide (p ∨ q)` is true if the right decision is. -/
  | dor_ttr (p q : Prop) (hp : Decidable p) (hq : Decidable q) :
      BCert (@decide q hq) true → BCert (@decide (p ∨ q) (@instDecidableOr p q hp hq)) true

/-- **Soundness**: a certified Boolean has the certified value. -/
theorem BCert.sound {b v : Bool} (h : BCert b v) : b = v := by
  induction h with
  | leaf b v h => exact h
  | and_tt a b _ _ iha ihb => rw [iha, ihb]; rfl
  | and_ffl a b _ iha => rw [iha]; rfl
  | and_ffr a b _ ihb => rw [ihb]; cases a <;> rfl
  | or_ttl a b _ iha => rw [iha]; rfl
  | or_ttr a b _ ihb => rw [ihb]; cases a <;> rfl
  | or_ff a b _ _ iha ihb => rw [iha, ihb]; rfl
  | not a v _ ih => rw [ih]
  | ite_t c h x y v _ _ ihc ihx =>
    have hc : c := of_decide_eq_true ihc
    cases h with
    | isTrue _ => exact ihx
    | isFalse hn => exact absurd hc hn
  | ite_f c h x y v _ _ ihc ihy =>
    have hc : ¬c := of_decide_eq_false ihc
    cases h with
    | isTrue hp => exact absurd hp hc
    | isFalse _ => exact ihy
  | cond_t c x y v _ _ ihc ihx => rw [ihc, ← ihx]; rfl
  | cond_f c x y v _ _ ihc ihy => rw [ihc, ← ihy]; rfl
  | dand_tt p q hp hq _ _ ihp ihq =>
    exact decide_eq_true ⟨of_decide_eq_true ihp, of_decide_eq_true ihq⟩
  | dor_ttl p q hp hq _ ihp => exact decide_eq_true (Or.inl (of_decide_eq_true ihp))
  | dor_ttr p q hp hq _ ihq => exact decide_eq_true (Or.inr (of_decide_eq_true ihq))

/-- **Sanity**: the degenerate certificate of `true`. -/
theorem BCert.sound_true : BCert true true → True := fun _ => trivial

/-! ## The builder -/

/-- `Eq.refl v` for a Boolean literal. -/
meta def reflB (v : Bool) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (toExpr v)

/-- The heads at which unfolding stops: the connectives handled by `BCert` and the comparison
leaves. -/
meta def stopHeads : List Name :=
  [``and, ``or, ``not, ``ite, ``cond, ``Decidable.decide, ``Nat.ble, ``Nat.beq, ``Nat.blt,
    ``BEq.beq, ``bne, ``Bool.true, ``Bool.false]

/-- The comparison propositions accepted under `decide` as leaves. -/
meta def leafProps : List Name :=
  [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Eq, ``Ne, ``Membership.mem, ``Dvd.dvd]

/-- The Boolean value of a closed Boolean expression, computed by the kernel's `whnf` (falling
back to `Meta.whnfD`). This is `meta` code that only chooses the branch of the certificate; the
kernel re-checks the value through the certificate's leaves. -/
meta def evalBool (e : Expr) : MetaM Bool := do
  if let .ok e' := Kernel.whnf (← getEnv) (← getLCtx) e then
    if e'.isConstOf ``Bool.true then return true
    if e'.isConstOf ``Bool.false then return false
  let e' ← whnfD e
  if e'.isConstOf ``Bool.true then return true
  if e'.isConstOf ``Bool.false then return false
  throwError "bool_cert: cannot evaluate{indentExpr e}"

/-- **The certificate of `BCert e v`**, built by unfolding the checker `e` to its connectives and
comparison leaves. The state counts the leaves and the *collapsed* nodes (subterms that unfold
to a literal `true`/`false` without passing through a connective, or stop at a field of a
computed record or a `match` on a computed value: projections of records, list lookups,
validity flags of computed balls); the flag (reader) asks for every leaf to be evaluated in
`meta` code as well, for early and precise error messages. -/
meta partial def bcertTerm (e : Expr) (v : Bool) :
    StateT (Nat × Nat) (ReaderT Bool MetaM) Expr := do
  let e' ← whnfHeadPred e (fun x => return !(stopHeads.contains x.getAppFn.constName))
  let pf ← match e'.getAppFnArgs with
    | (``and, #[a, b]) =>
      if v then
        pure (mkApp4 (mkConst ``BCert.and_tt) a b (← bcertTerm a true) (← bcertTerm b true))
      else if !(← evalBool a) then
        pure (mkApp3 (mkConst ``BCert.and_ffl) a b (← bcertTerm a false))
      else pure (mkApp3 (mkConst ``BCert.and_ffr) a b (← bcertTerm b false))
    | (``or, #[a, b]) =>
      if !v then
        pure (mkApp4 (mkConst ``BCert.or_ff) a b (← bcertTerm a false) (← bcertTerm b false))
      else if (← evalBool a) then
        pure (mkApp3 (mkConst ``BCert.or_ttl) a b (← bcertTerm a true))
      else pure (mkApp3 (mkConst ``BCert.or_ttr) a b (← bcertTerm b true))
    | (``not, #[a]) => pure (mkApp3 (mkConst ``BCert.not) a (toExpr !v) (← bcertTerm a !v))
    | (``ite, #[_, c, h, x, y]) =>
      let dc := mkApp2 (mkConst ``Decidable.decide) c h
      if (← evalBool dc) then
        pure (mkAppN (mkConst ``BCert.ite_t) #[c, h, x, y, toExpr v, ← bcertTerm dc true,
          ← bcertTerm x v])
      else
        pure (mkAppN (mkConst ``BCert.ite_f) #[c, h, x, y, toExpr v, ← bcertTerm dc false,
          ← bcertTerm y v])
    | (``cond, #[_, c, x, y]) =>
      if (← evalBool c) then
        pure (mkAppN (mkConst ``BCert.cond_t) #[c, x, y, toExpr v, ← bcertTerm c true,
          ← bcertTerm x v])
      else
        pure (mkAppN (mkConst ``BCert.cond_f) #[c, x, y, toExpr v, ← bcertTerm c false,
          ← bcertTerm y v])
    | (``Decidable.decide, #[p, h]) => decideTerm e' p h v
    | (``Bool.true, _) | (``Bool.false, _) =>
      unless e.isConstOf ``Bool.true || e.isConstOf ``Bool.false do
        modify fun (n, c) => (n, c + 1)
      leaf e' v
    | (``Nat.ble, _) | (``Nat.beq, _) | (``Nat.blt, _) | (``BEq.beq, _) | (``bne, _) => leaf e' v
    | _ =>
      if e'.isProj || (← isMatcherApp e') then
        -- a field of a computed record (e.g. the validity flag of a ball) or a `match` on a
        -- computed value (e.g. a list lookup `find?`): a collapsed leaf
        modify fun (n, c) => (n, c + 1)
        leaf e' v
      else throwError "bool_cert: stuck at a subterm that is not a comparison{indentExpr e'}"
  return mkApp2 (mkConst ``id [0]) (mkApp2 (mkConst ``BCert) e (toExpr v)) pf
where
  /-- A kernel-checked leaf `e = v`. -/
  leaf (e : Expr) (v : Bool) : StateT (Nat × Nat) (ReaderT Bool MetaM) Expr := do
    if (← read) then
      if (← evalBool e) != v then throwError "bool_cert: the leaf is not {v}{indentExpr e}"
    modify fun (n, c) => (n + 1, c)
    return mkApp3 (mkConst ``BCert.leaf) e (toExpr v) (reflB v)
  /-- `decide p`: split `∧`/`∨` of decidable propositions, otherwise a comparison leaf. -/
  decideTerm (e p h : Expr) (v : Bool) : StateT (Nat × Nat) (ReaderT Bool MetaM) Expr := do
    let p' ← whnfR p
    match p'.getAppFnArgs, (← whnfR h).getAppFnArgs with
    | (``And, #[a, b]), (``instDecidableAnd, #[_, _, ha, hb]) =>
      if v then
        let da := mkApp2 (mkConst ``Decidable.decide) a ha
        let db := mkApp2 (mkConst ``Decidable.decide) b hb
        return mkAppN (mkConst ``BCert.dand_tt) #[a, b, ha, hb, ← bcertTerm da true,
          ← bcertTerm db true]
      else leaf e v
    | (``Or, #[a, b]), (``instDecidableOr, #[_, _, ha, hb]) =>
      if v then
        let da := mkApp2 (mkConst ``Decidable.decide) a ha
        let db := mkApp2 (mkConst ``Decidable.decide) b hb
        if (← evalBool da) then
          return mkAppN (mkConst ``BCert.dor_ttl) #[a, b, ha, hb, ← bcertTerm da true]
        else return mkAppN (mkConst ``BCert.dor_ttr) #[a, b, ha, hb, ← bcertTerm db true]
      else leaf e v
    | _, _ =>
      if leafProps.contains p'.getAppFn.constName || p'.isConstOf ``True ||
          p'.isConstOf ``False then leaf e v
      else throwError "bool_cert: unsupported decision{indentExpr p}"

/-- **`bool_cert`**: prove `b = true` (or `b = false`) for a closed Boolean checker `b` by an
explicit `BCert` certificate (`bcertTerm`) whose leaves are single comparisons. The leaves are
evaluated by the kernel only (a false leaf is a kernel error when the declaration is added). -/
syntax (name := boolCert) "bool_cert" : tactic

/-- `bool_cert?`: `bool_cert`, also evaluating every leaf in `meta` code (precise error messages
before the kernel check; slower) and reporting the number of leaves. -/
syntax (name := boolCertV) "bool_cert?" : tactic

/-- The elaborator of `bool_cert`. -/
@[tactic boolCert, tactic boolCertV] meta def evalBoolCert : Tactic := fun stx => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, b, rhs) := ty.eq? | throwError "bool_cert: expected `b = true` or `b = false`"
  let v ← if rhs.isConstOf ``Bool.true then pure true
    else if rhs.isConstOf ``Bool.false then pure false
    else throwError "bool_cert: expected `b = true` or `b = false`"
  let verbose := stx.isOfKind ``boolCertV
  let (cert, n, c) ← ((bcertTerm b v).run (0, 0)).run verbose
  if verbose then logInfo m!"bool_cert: {n} leaves, of which {c} collapsed"
  g.assign (mkApp3 (mkConst ``BCert.sound) b (toExpr v) cert)
  replaceMainGoal []

/-- A small list checker for the fixtures. -/
def fixtureCheck : List (Nat × Int) → Bool
  | [] => true
  | (n, z) :: rest =>
    (decide (n ≤ 10) && (decide (z < 0) || !decide (z = 3))) &&
      (if n % 2 = 0 then decide ((n : Int) ≤ z + 20) else true) && fixtureCheck rest

/-- **Sanity** (accepted): `bool_cert` on a list checker. -/
theorem boolCert_fixture : fixtureCheck [(2, -1), (3, 5), (10, 4)] = true := by
  bool_cert

/-- **Sanity** (a checker evaluating to `false`). -/
theorem boolCert_false_fixture : fixtureCheck [(2, -1), (11, 5)] = false := by
  bool_cert

/-- **Sanity** (rejected): a false check is refused. -/
theorem boolCert_reject_fixture : True := by
  fail_if_success (have : fixtureCheck [(2, 3)] = true := by bool_cert?)
  trivial

end PlasmaLean.Certificates.BoolCert
