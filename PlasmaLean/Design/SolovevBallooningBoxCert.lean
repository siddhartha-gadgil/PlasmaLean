/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningEvalCert
public meta import Lean.Elab.Tactic.Basic

/-!
# Box checks of the Solov'ev ballooning cover with explicit second-derivative certificates

`ballooning_cover` (`Design/SolovevBallooningDefs`) closes the second-derivative check `hessOK`
of a box with shared corner tests by `Eq.refl true`, i.e. by one kernel evaluation of the whole
check. `ballooning_box "Q:a,b,c,d"` (resp. `"Z:a,b"` for an axis box) proves the same `Cover`
leaf, `Cover.leaf2` (resp. `Cover.axis2`), with the corner lemmas `a, b, c, d` and with the
obligation `hessOK … = true` proved by `bl_cert`: an evaluation certificate (`ECert`) with one
node per ball operation of the second-derivative evaluation.

**Sanity.** `ballooningBox_reject_fixture`: a malformed token is refused.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

open Lean Meta Elab Tactic in
/-- **`ballooning_box "Q:a,b,c,d"`** / **`"Z:a,b"`**: prove `Cover D t₀ t₁ n₀ n₁` for one box
whose corner tests are the lemmas `a, b, c, d` (at `(t₀,n₀), (t₁,n₀), (t₀,n₁), (t₁,n₁)`; for an
axis box `a, b` at `(t₀,n₁), (t₁,n₁)`), with the second-derivative check certified by
`bl_cert`. -/
elab "ballooning_box " s:str : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Cover D t0 t1 n0 n1 := ty | throwError "ballooning_box: expected a Cover goal"
  let tok := s.getString
  let nm (x : String) : Name := Name.mkStr `PlasmaLean.Design.SolovevBallooning x
  let reserveOf (c : Name) : MetaM Expr := do
    let cty ← inferType (mkConst c)
    let_expr Eq _ lhs _ := cty | throwError "ballooning_box: bad corner lemma {c}"
    let_expr cornerOK _ _ _ R := lhs | throwError "ballooning_box: bad corner lemma {c}"
    return R
  let (axis, cs) ←
    if tok.startsWith "Q:" then pure (false, ((tok.drop 2).toString.splitOn ",").map nm)
    else if tok.startsWith "Z:" then pure (true, ((tok.drop 2).toString.splitOn ",").map nm)
    else throwError "ballooning_box: bad token {tok}"
  unless cs.length == (if axis then 2 else 4) do throwError "ballooning_box: bad token {tok}"
  let Rs ← cs.mapM fun c => reserveOf c
  let tLN := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let RsE ← mkListLit tLN Rs
  let hessTy ← mkEq (mkAppN (mkConst ``hessOK) #[D, t0, t1, n0, n1, toExpr axis, RsE])
    (mkConst ``Bool.true)
  let hm ← mkFreshExprSyntheticOpaqueMVar hessTy
  let rest ← Term.withoutErrToSorry <| Tactic.run hm.mvarId! (evalTactic (← `(tactic| bl_cert)))
  unless rest.isEmpty do throwError "ballooning_box: bl_cert left goals"
  let pf := if axis then
      mkAppN (mkConst ``Cover.axis2) (#[D, t0, t1, n1] ++ Rs.toArray ++ #[hm] ++
        (cs.map mkConst).toArray)
    else
      mkAppN (mkConst ``Cover.leaf2) (#[D, t0, t1, n0, n1] ++ Rs.toArray ++ #[hm] ++
        (cs.map mkConst).toArray)
  g.assign (← instantiateMVars pf)
  replaceMainGoal []

/-- **Sanity** (rejected): a malformed plan token is refused. -/
theorem ballooningBox_reject_fixture : True := by
  fail_if_success (have : Cover gdata 0 1 0 1 := by ballooning_box "X:a")
  trivial

end PlasmaLean.Design.SolovevBallooning
