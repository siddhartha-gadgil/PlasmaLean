/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Eqns

/-!
# The `eval_cert` builder (`meta` code, compiled to native code)

The certificate predicate `ECert`, its soundness theorem and the sanity fixtures are in
`LeanTheory/Certificates/EvalCert.lean`; this module holds only the untrusted `meta` builder and
the tactic front end, referring to the constructors of `ECert` by name. It depends only on Lean,
and its library `LeanTheoryMeta` is precompiled (`precompileModules`, see `lakefile.toml`): run by
the interpreter, the builder took about as long as the kernel check of the certificate, compiled
it takes about a tenth of that. Nothing here is trusted: the kernel checks the term it produces.

The builder is a call-by-value evaluator over closed terms. Each evaluated subterm is entered in a
table with its value and certificate, so every intermediate value is computed once and is a shared
node of the proof DAG. Operation nodes (the default arithmetic, Boolean and comparison operations,
record fields, and the extra operations named in `eval_cert [f₁, …]`) evaluate their arguments,
then end in one kernel leaf `f v₁ … vₖ = v` whose value `v` is computed by an untrusted fast path
(`fastV`: Lean's own integer arithmetic) or, failing that, by the kernel's `whnf`. Recursive
definitions unfold by their `eq_def` equations, other definitions, `match` on values and `β`/`ζ`
steps by definitional type hints, and `if` by the branch taken.
-/

public section

namespace LeanTheoryMeta.EvalCert

open Lean Meta Elab Tactic


/-- Configuration of the builder: the extra operations treated as kernel leaves. -/
meta structure Cfg where
  /-- Heads of operation nodes (their arguments are evaluated, then one kernel leaf). -/
  prims : NameSet
  /-- Bound on the number of evaluated nodes. -/
  maxNodes : Nat := 50000000
  /-- Bound on the nesting depth of the evaluation (native stack). -/
  maxDepth : Nat := 4000

/-- State of the builder: the table of shared intermediate results and the caches. -/
meta structure St where
  /-- Evaluated subterms: value and certificate. -/
  memo : Std.HashMap Expr (Expr × Expr) := {}
  /-- Number of evaluated nodes. -/
  nodes : Nat := 0
  /-- Current nesting depth of the evaluation. -/
  depth : Nat := 0
  /-- Number of kernel leaves. -/
  leaves : Nat := 0
  /-- Which fields of a constructor are proofs. -/
  propFields : NameMap (Array Bool) := {}
  /-- The positions of the explicit data arguments of a definition. -/
  dataPos : NameMap (Array Nat) := {}
  /-- The unfolding equation of a recursive definition. -/
  eqns : NameMap (Option Name) := {}
  /-- The positions of the arguments of a constant on which the types of later arguments or the
  result type depend. -/
  depPos : NameMap (Array Nat) := {}
  /-- Number of evaluated nodes per head constant (statistics for `eval_cert?`). -/
  heads : Std.HashMap Name Nat := {}
  /-- Compound terms already known to be values. -/
  vals : Std.HashSet Expr := {}
  /-- Bodies of the non-recursive definitions unfolded by `fastV` (none: not unfolded). -/
  bodies : NameMap (Option Expr) := {}
  /-- Values of closed constants computed by `fastV`. -/
  consts : NameMap Expr := {}

/-- The builder monad. -/
abbrev EvM := ReaderT Cfg (StateRefT St MetaM)

/-- The operations that are kernel leaves by default. -/
meta def defaultPrims : List Name :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``HPow.hPow, ``Neg.neg,
    ``Max.max, ``Min.min, ``OfNat.ofNat, ``Nat.cast, ``NatCast.natCast, ``IntCast.intCast,
    ``Int.cast, ``Inv.inv, ``OfScientific.ofScientific, ``Int.toNat, ``Int.natAbs, ``Int.sign, ``Nat.succ, ``Nat.zero, ``Nat.pred,
    ``Int.add, ``Int.sub, ``Int.mul, ``Int.neg, ``Int.ediv, ``Int.emod,
    ``Int.fdiv, ``Int.fmod, ``Int.tdiv, ``Int.tmod, ``Int.pow, ``Int.subNatNat,
    ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.gcd, ``Nat.log2,
    ``Nat.min, ``Nat.max, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
    ``HShiftLeft.hShiftLeft, ``HShiftRight.hShiftRight, ``HAnd.hAnd, ``HOr.hOr, ``HXor.hXor,
    ``and, ``or, ``not, ``xor, ``BEq.beq, ``bne, ``Nat.ble, ``Nat.beq, ``Nat.blt, ``Int.decEq]

/-- The comparison propositions decided at a leaf. -/
meta def relProps : List Name := [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt, ``Eq, ``Ne]

/-- Which fields of the constructor `c` are proofs. -/
meta def propFieldsOf (c : Name) (cv : ConstructorVal) : EvM (Array Bool) := do
  if let some r := (← get).propFields.find? c then return r
  let r ← forallTelescopeReducing cv.type fun xs _ => do
    let mut out := #[]
    for i in [cv.numParams:xs.size] do
      out := out.push (← isProp (← inferType xs[i]!))
    return out
  modify fun s => { s with propFields := s.propFields.insert c r }
  return r

/-- `e` is a value: a raw natural literal or a constructor applied to values (proof fields
excepted). Natural numbers are values only as raw literals. -/
meta partial def isVal (e : Expr) : EvM Bool := do
  match e with
  | .lit _ => return true
  | .lam .. => return true
  | .mdata _ b => isVal b
  | .const c _ =>
    if c == ``Nat.zero then return false
    match (← getEnv).find? c with
    | some (.ctorInfo cv) => return cv.numParams == 0 && cv.numFields == 0
    | _ => return false
  | .app .. =>
    if (← get).vals.contains e then return true
    let .const c _ := e.getAppFn | return false
    if c == ``Nat.succ then return false
    -- a quotient value `Quot.mk r a` (e.g. a `Multiset` under a `Finset.sum`)
    if c == ``Quot.mk && e.getAppNumArgs == 3 then
      unless ← isVal e.appArg! do return false
      modify fun s => { s with vals := s.vals.insert e }
      return true
    let some (.ctorInfo cv) := (← getEnv).find? c | return false
    let args := e.getAppArgs
    if args.size != cv.numParams + cv.numFields then return false
    let pf ← propFieldsOf c cv
    for i in [0:cv.numFields] do
      if !pf[i]! then
        unless ← isVal args[cv.numParams + i]! do return false
    modify fun s => { s with vals := s.vals.insert e }
    return true
  | _ => return false

/-- The unfolding equation `c.eq_def` of a recursive definition (none for non-recursive ones). -/
meta def eqnOf (c : Name) : EvM (Option Name) := do
  if let some r := (← get).eqns.find? c then return r
  let r ← try getUnfoldEqnFor? c (nonRec := false) catch _ => pure none
  modify fun s => { s with eqns := s.eqns.insert c r }
  return r

/-- Untrusted native mirror of the Newton iterations `FIv.isqrtAux`, `Bl.isqrtAux`, for `fastV`. -/
meta def isqrtNative : Nat → Nat → Nat → Nat
  | 0, _, g => g
  | k + 1, n, g => if (g + n / g) / 2 < g then isqrtNative k n ((g + n / g) / 2) else g

/-- The normal form of an integer value: `Int.ofNat n` or `Int.negSucc n`. -/
meta def mkIntVal (i : Int) : Expr :=
  if i ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit i.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit (-i - 1).toNat)

/-- An integer or natural value read back from its normal form. -/
meta def readNum? (e : Expr) : Option Int :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.const ``Int.ofNat _) (.lit (.natVal n)) => some n
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) => some (-(n : Int) - 1)
  | _ => none

/-- The numeric type of an arithmetic operation: `true` for `ℤ`, `false` for `ℕ`. -/
meta def numTy? (t : Expr) : Option Bool :=
  match t.consumeMData with
  | .const ``Int _ => some true
  | .const ``Nat _ => some false
  | _ => none

/-- A number of type `ℤ` (`true`) or `ℕ` (`false`) as a value. -/
meta def mkNumVal (isInt : Bool) (i : Int) : Expr :=
  if isInt then mkIntVal i else mkRawNatLit i.toNat

/-- A rational value `Rat.mk' n d h₁ h₂` in normal form. The proof fields are small closed
terms checked by the kernel: `Nat.succ_ne_zero (d - 1) : d ≠ 0` and `Eq.refl 1`, whose type
`1 = 1` is the coprimality `Nat.gcd |n| d = 1` after unfolding (one `Nat.gcd` on literals). -/
meta def mkRatVal (q : Rat) : Expr :=
  mkApp4 (mkConst ``Rat.mk') (mkIntVal q.num) (mkRawNatLit q.den)
    (mkApp (mkConst ``Nat.succ_ne_zero) (mkRawNatLit (q.den - 1)))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit 1))

/-- A rational value read back from its normal form `Rat.mk' n d _ _`. -/
meta def readRat? (e : Expr) : Option Rat :=
  match e.getAppFnArgs with
  | (``Rat.mk', #[n, d, _, _]) =>
    match readNum? n, readNum? d with
    | some n, some d => if d > 0 then some (Rat.divInt n d) else none
    | _, _ => none
  | _ => none

/-- `t` is the type `ℚ`. -/
meta def isRatTy (t : Expr) : Bool := t.consumeMData.isConstOf ``Rat

/-- **Fast untrusted evaluation of a rational leaf** (`ℚ` numerals, casts, `+ - * / ⁻¹`, `^` by a
natural number, `max`, `min` and comparisons), by Lean's own `Rat` arithmetic; `none` outside this
fragment. `fastQ? fastV e` uses `fastV` for the arguments. -/
meta def fastQ? (fv : Expr → EvM (Option Expr)) (e : Expr) : EvM (Option Expr) := do
  let c := e.getAppFn.constName?.getD .anonymous
  let args := e.getAppArgs
  let rat (x : Expr) : EvM (Option Rat) := do return (← fv x).bind readRat?
  let num (x : Expr) : EvM (Option Int) := do return (← fv x).bind readNum?
  match c, args.size with
  | ``OfNat.ofNat, 3 =>
    unless isRatTy args[0]! do return none
    let .lit (.natVal n) := args[1]!.consumeMData | return none
    return some (mkRatVal n)
  | ``OfScientific.ofScientific, 5 =>
    unless isRatTy args[0]! do return none
    let some m ← num args[2]! | return none
    let some k ← num args[4]! | return none
    let s ← fv args[3]!
    let p : Rat := (10 : Rat) ^ k.toNat
    match s with
    | some (.const ``Bool.true _) => return some (mkRatVal ((m : Rat) / p))
    | some (.const ``Bool.false _) => return some (mkRatVal ((m : Rat) * p))
    | _ => return none
  | ``Nat.cast, 3 | ``NatCast.natCast, 3 | ``Int.cast, 3 | ``IntCast.intCast, 3 =>
    unless isRatTy args[0]! do return none
    return (← num args[2]!).map fun n => mkRatVal n
  | ``Neg.neg, 3 =>
    unless isRatTy args[0]! do return none
    return (← rat args[2]!).map fun a => mkRatVal (-a)
  | ``Inv.inv, 3 =>
    unless isRatTy args[0]! do return none
    return (← rat args[2]!).map fun a => mkRatVal a⁻¹
  | ``HAdd.hAdd, 6 | ``HSub.hSub, 6 | ``HMul.hMul, 6 | ``HDiv.hDiv, 6 =>
    unless isRatTy args[0]! && isRatTy args[1]! && isRatTy args[2]! do return none
    let some a ← rat args[4]! | return none
    let some b ← rat args[5]! | return none
    return some (mkRatVal (match c with
      | ``HAdd.hAdd => a + b | ``HSub.hSub => a - b | ``HMul.hMul => a * b | _ => a / b))
  | ``HPow.hPow, 6 =>
    unless isRatTy args[0]! && numTy? args[1]! == some false do return none
    let some a ← rat args[4]! | return none
    let some k ← num args[5]! | return none
    return some (mkRatVal (a ^ k.toNat))
  | ``Max.max, 4 | ``Min.min, 4 =>
    unless isRatTy args[0]! do return none
    let some a ← rat args[2]! | return none
    let some b ← rat args[3]! | return none
    return some (mkRatVal (if c == ``Max.max then max a b else min a b))
  | ``Decidable.decide, 2 =>
    let p := args[0]!.consumeMData
    let pa := p.getAppArgs
    let .const r _ := p.getAppFn | return none
    if pa.size == 4 && (r == ``LE.le || r == ``LT.lt || r == ``GE.ge || r == ``GT.gt) then
      unless isRatTy pa[0]! do return none
      let some a ← rat pa[2]! | return none
      let some b ← rat pa[3]! | return none
      return some (toExpr (match r with
        | ``LE.le => decide (a ≤ b) | ``LT.lt => decide (a < b)
        | ``GE.ge => decide (a ≥ b) | _ => decide (a > b)))
    if pa.size == 3 && (r == ``Eq || r == ``Ne) then
      unless isRatTy pa[0]! do return none
      let some a ← rat pa[1]! | return none
      let some b ← rat pa[2]! | return none
      return some (toExpr (if r == ``Eq then a == b else a != b))
    return none
  | _, _ => return none

/-- **Fast untrusted evaluation** of a leaf (integer and natural arithmetic, Booleans,
comparisons, `if`, records and non-recursive definitions), by Lean's own arithmetic in `meta`
code; `none` when the term is outside this fragment (then the kernel's `whnf` is used). The
value only fills in the leaf `e = v`, which the kernel checks. -/
meta partial def fastV (e : Expr) : EvM (Option Expr) := do
  match e with
  | .lit _ => return some e
  | .mdata _ b => fastV b
  | .proj _ i s =>
    let some s' ← fastV s | return none
    let .const c _ := s'.getAppFn | return none
    let some (.ctorInfo cv) := (← getEnv).find? c | return none
    return s'.getAppArgs[cv.numParams + i]?
  | .app .. | .const .. =>
    if e.isApp && (← get).vals.contains e then return some e
    let .const c _ := e.getAppFn | return none
    let args := e.getAppArgs
    let num (x : Expr) : EvM (Option Int) := do return (← fastV x).bind readNum?
    let bool (x : Expr) : EvM (Option Bool) := do
      match ← fastV x with
      | some (.const ``Bool.true _) => return some true
      | some (.const ``Bool.false _) => return some false
      | _ => return none
    let mkB (b : Bool) : Expr := toExpr b
    if let some v ← fastQ? fastV e then return some v
    match c, args.size with
    | ``Int.ofNat, 1 => return (← num args[0]!).map mkIntVal
    | ``Int.negSucc, 1 => return (← num args[0]!).map fun n => mkIntVal (-n - 1)
    | ``OfNat.ofNat, 3 =>
      let some t := numTy? args[0]! | return none
      let .lit (.natVal n) := args[1]!.consumeMData | return none
      return some (mkNumVal t n)
    | ``Nat.cast, 3 | ``NatCast.natCast, 3 =>
      let some t := numTy? args[0]! | return none
      return (← num args[2]!).map (mkNumVal t)
    | ``Neg.neg, 3 =>
      let some true := numTy? args[0]! | return none
      return (← num args[2]!).map fun a => mkIntVal (-a)
    | ``HAdd.hAdd, 6 | ``HSub.hSub, 6 | ``HMul.hMul, 6 | ``HDiv.hDiv, 6 | ``HMod.hMod, 6 =>
      let some t := numTy? args[0]! | return none
      unless numTy? args[1]! == some t && numTy? args[2]! == some t do return none
      let some a ← num args[4]! | return none
      let some b ← num args[5]! | return none
      if t then
        let r : Int := match c with
          | ``HAdd.hAdd => a + b | ``HSub.hSub => a - b | ``HMul.hMul => a * b
          | ``HDiv.hDiv => a / b | _ => a % b
        return some (mkIntVal r)
      else
        let (a, b) := (a.toNat, b.toNat)
        let r : Nat := match c with
          | ``HAdd.hAdd => a + b | ``HSub.hSub => a - b | ``HMul.hMul => a * b
          | ``HDiv.hDiv => a / b | _ => a % b
        return some (mkRawNatLit r)
    | ``Max.max, 4 | ``Min.min, 4 =>
      let some t := numTy? args[0]! | return none
      let some a ← num args[2]! | return none
      let some b ← num args[3]! | return none
      return some (mkNumVal t (if c == ``Max.max then max a b else min a b))
    | ``and, 2 =>
      let some a ← bool args[0]! | return none
      let some b ← bool args[1]! | return none
      return some (mkB (a && b))
    | ``or, 2 =>
      let some a ← bool args[0]! | return none
      let some b ← bool args[1]! | return none
      return some (mkB (a || b))
    | ``not, 1 => return (← bool args[0]!).map (mkB !·)
    | ``Int.add, 2 | ``Int.sub, 2 | ``Int.mul, 2 | ``Int.ediv, 2 | ``Int.emod, 2 =>
      let some a ← num args[0]! | return none
      let some b ← num args[1]! | return none
      return some (mkIntVal (match c with
        | ``Int.add => a + b | ``Int.sub => a - b | ``Int.mul => a * b
        | ``Int.ediv => a / b | _ => a % b))
    | ``Int.neg, 1 => return (← num args[0]!).map fun a => mkIntVal (-a)
    | ``Int.natAbs, 1 => return (← num args[0]!).map fun a => mkRawNatLit a.natAbs
    | ``Nat.add, 2 | ``Nat.sub, 2 | ``Nat.mul, 2 | ``Nat.div, 2 | ``Nat.mod, 2 =>
      let some a ← num args[0]! | return none
      let some b ← num args[1]! | return none
      let (a, b) := (a.toNat, b.toNat)
      return some (mkRawNatLit (match c with
        | ``Nat.add => a + b | ``Nat.sub => a - b | ``Nat.mul => a * b
        | ``Nat.div => a / b | _ => a % b))
    | ``Nat.ble, 2 | ``Nat.beq, 2 | ``Nat.blt, 2 =>
      let some a ← num args[0]! | return none
      let some b ← num args[1]! | return none
      return some (mkB (match c with
        | ``Nat.ble => decide (a ≤ b) | ``Nat.beq => a == b | _ => decide (a < b)))
    | .str _ "isqrtAux", 3 =>
      -- untrusted native mirror of the Newton iteration (the kernel checks the leaf)
      let some k ← num args[0]! | return none
      let some n ← num args[1]! | return none
      let some g ← num args[2]! | return none
      return some (mkRawNatLit (isqrtNative k.toNat n.toNat g.toNat))
    | ``Int.toNat, 1 => return (← num args[0]!).map fun a => mkRawNatLit a.toNat
    | ``Decidable.decide, 2 =>
      let p := args[0]!.consumeMData
      let pa := p.getAppArgs
      let .const r _ := p.getAppFn | return none
      if pa.size == 4 && (r == ``LE.le || r == ``LT.lt || r == ``GE.ge || r == ``GT.gt) then
        let some _ := numTy? pa[0]! | return none
        let some a ← num pa[2]! | return none
        let some b ← num pa[3]! | return none
        return some (mkB (match r with
          | ``LE.le => decide (a ≤ b) | ``LT.lt => decide (a < b)
          | ``GE.ge => decide (a ≥ b) | _ => decide (a > b)))
      if pa.size == 3 && (r == ``Eq || r == ``Ne) then
        match numTy? pa[0]! with
        | some _ =>
          let some a ← num pa[1]! | return none
          let some b ← num pa[2]! | return none
          return some (mkB (if r == ``Eq then a == b else a != b))
        | none =>
          unless pa[0]!.consumeMData.isConstOf ``Bool do return none
          let some a ← bool pa[1]! | return none
          let some b ← bool pa[2]! | return none
          return some (mkB (if r == ``Eq then a == b else a != b))
      return none
    | ``ite, 5 =>
      let some b ← bool (mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!) | return none
      fastV (if b then args[3]! else args[4]!)
    | ``cond, 4 =>
      let some b ← bool args[1]! | return none
      fastV (if b then args[2]! else args[3]!)
    | _, _ =>
      match (← getEnv).find? c with
      | some (.ctorInfo cv) =>
        if c == ``Nat.succ || c == ``Nat.zero then return none
        if args.size != cv.numParams + cv.numFields then return none
        let pf ← propFieldsOf c cv
        let mut out := args
        for i in [0:cv.numFields] do
          unless pf[i]! do
            let some x ← fastV args[cv.numParams + i]! | return none
            out := out.set! (cv.numParams + i) x
        let r := mkAppN e.getAppFn out
        modify fun s => { s with vals := s.vals.insert r }
        return some r
      | some (.defnInfo dv) =>
        let .const _ lvls := e.getAppFn | return none
        if args.isEmpty then
          if let some v := (← get).consts.find? c then return some v
        let body ← if lvls.isEmpty then
            match (← get).bodies.find? c with
            | some b => pure b
            | none =>
              let b ← if (← eqnOf c).isSome || (← getMatcherInfo? c).isSome then pure none
                else pure (some dv.value)
              modify fun s => { s with bodies := s.bodies.insert c b }
              pure b
          else if (← eqnOf c).isSome || (← getMatcherInfo? c).isSome then pure none
          else pure (some (dv.value.instantiateLevelParams dv.levelParams lvls))
        let some body := body | return none
        let r ← fastV (body.beta args)
        if args.isEmpty then
          if let some v := r then modify fun s => { s with consts := s.consts.insert c v }
        return r
      | _ => return none
  | _ => return none

/-- The value of a closed term whose operation arguments are values: the kernel's `whnf`,
recursively on the fields of the resulting constructor. This only computes the value written
into a leaf; the kernel re-checks the leaf. -/
meta partial def kval (e : Expr) : EvM Expr := do
  if let some v ← fastV e then return v
  let r ← match Kernel.whnf (← getEnv) {} e with
    | .ok r => pure r
    | .error ex => throwError "eval_cert: kernel whnf failed: {← ex.toMessageData {} |>.toString}"
  match r with
  | .lit _ => return r
  | _ =>
    let f := r.getAppFn
    let .const c _ := f | throwError "eval_cert: the term does not reduce to a value{indentExpr r}"
    if c == ``Nat.zero then return mkRawNatLit 0
    if c == ``Nat.succ then
      match ← kval r.appArg! with
      | .lit (.natVal k) => return mkRawNatLit (k + 1)
      | _ => throwError "eval_cert: not a natural number{indentExpr r}"
    if c == ``Quot.mk && r.getAppNumArgs == 3 then
      return mkApp r.appFn! (← kval r.appArg!)
    let some (.ctorInfo cv) := (← getEnv).find? c |
      throwError "eval_cert: the term does not reduce to a value{indentExpr r}"
    let args := r.getAppArgs
    let pf ← propFieldsOf c cv
    let mut out := args
    for i in [0:cv.numFields] do
      unless pf[i]! do
        out := out.set! (cv.numParams + i) (← kval args[cv.numParams + i]!)
    return mkAppN f out

/-- Replace the occurrences of the closed terms `subs` in `e` by bound variables (the `i`-th
by the `i`-th of `subs.size` binders, outermost first). -/
meta partial def absOcc (subs : Array Expr) (e : Expr) (d : Nat) : Expr :=
  match subs.findIdx? (· == e) with
  | some i => .bvar (d + subs.size - 1 - i)
  | none =>
    match e with
    | .app f a => e.updateApp! (absOcc subs f d) (absOcc subs a d)
    | .lam _ t b _ => e.updateLambdaE! (absOcc subs t d) (absOcc subs b (d + 1))
    | .forallE _ t b _ => e.updateForallE! (absOcc subs t d) (absOcc subs b (d + 1))
    | .letE _ t v b _ => e.updateLetE! (absOcc subs t d) (absOcc subs v d) (absOcc subs b (d + 1))
    | .mdata _ b => e.updateMData! (absOcc subs b d)
    | .proj _ _ b => e.updateProj! (absOcc subs b d)
    | _ => e

/-- The positions of the explicit data arguments of the constant `c` (not types, proofs,
functions or instances): these are evaluated before `c` is unfolded (call by value). -/
meta def dataPositions (c : Name) : EvM (Array Nat) := do
  if let some r := (← get).dataPos.find? c then return r
  let info ← getConstInfo c
  let r ← forallTelescopeReducing info.type fun xs _ => do
    let mut out := #[]
    for i in [0:xs.size] do
      let ld ← xs[i]!.fvarId!.getDecl
      if ld.binderInfo != .default then continue
      let t ← whnf ld.type
      if t.isForall || t.isSort then continue
      if ← isProp ld.type then continue
      if (← isClass? ld.type).isSome then continue
      out := out.push i
    return out
  modify fun s => { s with dataPos := s.dataPos.insert c r }
  return r

/-- The positions `i` of the binders of the constant `c` on which the type of a later binder or
the result type depends (e.g. `n` in `Fin.ofNat (n : ℕ) [NeZero n] (a : ℕ) : Fin n`, `val` in
`Fin.mk (val : ℕ) (isLt : val < n)`). Replacing such an argument by its value can make the
abstraction `fun x => c … x …` of `ECert.arg`/`ECert.op₁` ill-typed. -/
meta def depPositions (c : Name) : EvM (Array Nat) := do
  if let some r := (← get).depPos.find? c then return r
  let info ← getConstInfo c
  let r ← forallTelescopeReducing info.type fun xs body => do
    let mut out := #[]
    for i in [0:xs.size] do
      let fv := xs[i]!.fvarId!
      let mut dep := body.containsFVar fv
      for j in [i+1:xs.size] do
        if dep then break
        dep := (← inferType xs[j]!).containsFVar fv
      if dep then out := out.push i
    return out
  modify fun s => { s with depPos := s.depPos.insert c r }
  return r

/-- Drop from `subs` the arguments of `e` that cannot be abstracted: those occurring in an argument
at a dependent position of the head (`depPositions`) whose abstraction `fun x => e[x/a]` is not a
well-typed non-dependent function. Such an argument is left unevaluated (the later unfolding or
the kernel leaf handles it). `decide` and matchers are not filtered (the sides of `decide p h` occur in `h` as well; the discriminants are dependent only
through the motive), nor are terms without a dependent position, so the certificates of terms
that were already well-typed are unchanged. -/
meta def filterDep (α e : Expr) (subs : Array Expr) : EvM (Array Expr) := do
  if subs.isEmpty then return subs
  let .const c _ := e.getAppFn | return subs
  -- `decide p h`: the sides occur in `p` and in the instance `h` alike
  if c == ``Decidable.decide then return subs
  if (← getMatcherInfo? c).isSome then return subs
  let dps ← depPositions c
  if dps.isEmpty then return subs
  let args := e.getAppArgs
  let mut out := #[]
  for a in subs do
    let risky := dps.any fun i => i < args.size && (args[i]!.find? (· == a)).isSome
    if !risky then
      out := out.push a
      continue
    let β ← inferType a
    let g := mkLambda `x .default β (absOcc #[a] e 0)
    let ok ← try
        Meta.check g
        isDefEq (← inferType g) (← mkArrow β α)
      catch _ => pure false
    if ok then out := out.push a
  return out

/-- Unfold the instance under a projection `s.i` (the structure `s` is a class instance). -/
meta def unfoldInst (e : Expr) : MetaM Expr := do
  match e with
  | .proj n i s =>
    let s' ← withTransparency .all (whnf s)
    return .proj n i s'
  | _ => return e

/-- The certificate `ECert.lit v`. -/
meta def mkLit (α v : Expr) : Expr := mkApp2 (mkConst `LeanTheory.Certificates.EvalCert.ECert.lit) α v

/-- `Eq.refl v`. -/
meta def mkRefl (α v : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) α v

/-- The certificate `p : ECert e' v` with the type hint `ECert e v` (a definitional step). -/
meta def hint (_α _e : Expr) (r : Expr × Expr) : Expr × Expr := r

/-- The distinct subterms of `xs` that are not values. Proofs (e.g. the bound `Fin.ofNat._proof_1
n a` of a `Fin` numeral, a discriminant `h : i < n` of a `match`) are irrelevant and never
evaluated: `ECert` is only stated over types. -/
meta def nonVals (xs : Array Expr) : EvM (Array Expr) := do
  let mut out := #[]
  for x in xs do
    unless (← isVal x) || out.contains x do
      unless ← isProof x do out := out.push x
  return out

mutual

/-- **The certificate of `e`**: its value `v` and a proof of `ECert e v`, shared through the
table of evaluated subterms. -/
meta partial def ev (e : Expr) : EvM (Expr × Expr) := do
  if let some r := (← get).memo[e]? then return r
  let s ← get
  if s.nodes ≥ (← read).maxNodes then throwError "eval_cert: node budget exhausted"
  let h := e.getAppFn.constName?.getD .anonymous
  set { s with nodes := s.nodes + 1 }
  modify fun s => { s with heads := s.heads.alter h (fun n => some (n.getD 0 + 1)) }
  let d := (← get).depth
  if d ≥ (← read).maxDepth then
    throwError "eval_cert: evaluation depth {d} exceeded (a loop, or a very deep term) at{indentExpr e}"
  modify fun s => { s with depth := d + 1 }
  let r ← evCore e
  modify fun s => { s with memo := s.memo.insert e r, depth := d }
  return r

/-- One evaluation step at the root of `e`. -/
meta partial def evCore (e : Expr) : EvM (Expr × Expr) := do
  let α ← inferType e
  if ← isVal e then return (e, mkLit α e)
  match e with
  | .mdata _ b => return hint α e (← ev b)
  | .letE _ _ v b _ => return hint α e (← ev (b.instantiate1 v))
  | .proj _ _ s =>
    if (← isClass? (← inferType s)).isSome then
      -- a method of an instance: unfold the instance (a definitional step)
      return hint α e (← ev (← withTransparency .all (whnfCore (← unfoldInst e))))
    opNode α e (← nonVals #[s])
  | _ =>
    let f := e.getAppFn
    if f.isLambda then return hint α e (← ev e.headBeta)
    if f.isProj then
      let f' ← withTransparency .all (whnfCore (← unfoldInst f))
      if f' == f then throwError "eval_cert: stuck at an instance method{indentExpr e}"
      return hint α e (← ev (mkAppN f' e.getAppArgs).headBeta)
    let .const c lvls := f | throwError "eval_cert: stuck at{indentExpr e}"
    let args := e.getAppArgs
    if c == ``ite && args.size == 5 then return ← iteNode α e args
    if c == ``dite && args.size == 5 then return ← diteNode α e args
    if c == ``Decidable.decide && args.size == 2 then return ← decideNode α e args[0]! args[1]!
    if (← read).prims.contains c then
      -- a partial application of an operation (e.g. `Int.add` in `zipL Int.add`) is a value
      if (← whnf α).isForall then return (e, mkLit α e)
      let ps ← dataPositions c
      return ← opNode α e (← nonVals (ps.filter (· < args.size) |>.map (args[·]!)))
    if let some pinfo ← getProjectionFnInfo? c then
      unless pinfo.fromClass do
        if args.size > pinfo.numParams then
          return ← opNode α e (← nonVals #[args[pinfo.numParams]!])
    if let some info ← getMatcherInfo? c then
      let ds := (List.range info.numDiscrs).toArray.map (args[info.numParams + 1 + ·]!)
      return ← argChain α e (← nonVals ds) fun e' => do
        match ← withTransparency .all (reduceMatcher? e') with
        | .reduced e'' => return hint α e' (← ev e'')
        | _ => throwError "eval_cert: stuck at a `match`{indentExpr e'}"
    if c == ``Quot.mk && args.size == 3 then
      return ← argChain α e (← nonVals #[args[2]!]) fun e' => return (e', mkLit α e')
    if let some (.ctorInfo cv) := (← getEnv).find? c then
      -- proof fields (e.g. those of `Rat.mk'`) are not evaluated: they are irrelevant
      let pf ← propFieldsOf c cv
      let ps := ((List.range cv.numFields).filter (fun i => !(pf[i]?.getD false))).toArray.map
        (cv.numParams + ·)
      return ← argChain α e (← nonVals (ps.filter (· < args.size) |>.map (args[·]!)))
        fun e' => return (e', mkLit α e')
    let ps ← dataPositions c
    argChain α e (← nonVals (ps.filter (· < args.size) |>.map (args[·]!))) fun e' => do
      let args' := e'.getAppArgs
      if let some eqn ← eqnOf c then
        let eqc := mkConst eqn lvls
        let n := (← inferType eqc).getForallArity
        if args'.size ≥ n then
          let mut pf := mkAppN eqc args'[0:n]
          let some (_, _, rhs) := (← inferType pf).eq? |
            throwError "eval_cert: unexpected equation{indentExpr pf}"
          let mut rhs' := rhs
          for a in args'[n:] do
            pf ← mkCongrFun pf a
            rhs' := mkApp rhs' a
          let rhs := rhs'.headBeta
          let (v, p) ← ev rhs
          return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.unfold) #[α, e', rhs, v, pf, p])
      match ← withTransparency .all (unfoldDefinition? e') with
      | some e'' => return hint α e' (← ev e''.headBeta)
      | none =>
        -- a recursor (e.g. the cast `h ▸ v`, `Eq.rec` reduced by the K rule): one `whnfCore`
        -- step, a definitional step
        -- likewise `Quot.lift f h (Quot.mk r a)` reduces to `f a`
        match (← getEnv).find? c with
        | some (.recInfo _) | some (.quotInfo _) =>
          let e'' ← withTransparency .all (whnfCore e')
          if e'' != e' then return hint α e' (← ev e''.headBeta)
        | _ => pure ()
        -- a partial application of a recursive definition (e.g. `zipL add1`, a function passed
        -- as data): a function is a value
        if (← whnf α).isForall then return (e', mkLit α e')
        throwError "eval_cert: cannot unfold{indentExpr e'}"

/-- Replace the non-value arguments `subs` of `e` by their values one at a time (`ECert.arg`),
then continue with `k`. -/
meta partial def argChain (α e : Expr) (subs : Array Expr)
    (k : Expr → EvM (Expr × Expr)) (filtered : Bool := false) : EvM (Expr × Expr) := do
  let subs ← if filtered then pure subs else filterDep α e subs
  if subs.isEmpty then return ← k e
  let a := subs[0]!
  let β ← inferType a
  let (va, pa) ← ev a
  let body := absOcc #[a] e 0
  let g := mkLambda `x .default β body
  let e₁ := body.instantiate1 va
  let (v, p₁) ← argChain α e₁ subs[1:] k (filtered := true)
  return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.arg) #[α, β, g, a, va, v, pa, p₁])

/-- An operation node: evaluate the non-value arguments `subs`, then one kernel leaf. -/
meta partial def opNode (α e : Expr) (subs : Array Expr) : EvM (Expr × Expr) := do
  let leafOf (e' : Expr) : EvM (Expr × Expr) := do
    let v ← kval e'
    modify fun s => { s with leaves := s.leaves + 1 }
    return (v, mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.ECert.leaf) α e' v (mkRefl α v))
  let subs ← filterDep α e subs
  if subs.isEmpty || subs.size > 3 then return ← argChain α e subs leafOf
  let n := subs.size
  let βs ← subs.mapM fun x => inferType x
  let rs ← subs.mapM ev
  let args := e.getAppArgs
  let trailing := args.size ≥ n && (List.range n).all fun i => args[args.size - n + i]! == subs[i]!
  let (f, e') ← if trailing && !(e.getAppFn.isLambda) then
      let f := mkAppN e.getAppFn args[0:args.size - n]
      pure (f, mkAppN f (rs.map (·.1)))
    else
      let body := absOcc subs e 0
      let mut f := body
      for i in [0:n] do
        f := mkLambda `x .default βs[n - 1 - i]! f
      pure (f, body.instantiateRev (rs.map (·.1)))
  let v ← kval e'
  modify fun s => { s with leaves := s.leaves + 1 }
  let leafPf := mkRefl α v
  match n with
  | 1 => return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.op₁) #[α, βs[0]!, f, subs[0]!, rs[0]!.1, v,
      rs[0]!.2, leafPf])
  | 2 => return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.op₂) #[α, βs[0]!, βs[1]!, f, subs[0]!, subs[1]!,
      rs[0]!.1, rs[1]!.1, v, rs[0]!.2, rs[1]!.2, leafPf])
  | _ => return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.op₃) #[α, βs[0]!, βs[1]!, βs[2]!, f, subs[0]!,
      subs[1]!, subs[2]!, rs[0]!.1, rs[1]!.1, rs[2]!.1, v, rs[0]!.2, rs[1]!.2, rs[2]!.2, leafPf])

/-- `if c then x else y`: certify `decide c`, then the branch taken. -/
meta partial def iteNode (α e : Expr) (args : Array Expr) : EvM (Expr × Expr) := do
  let c := args[1]!; let h := args[2]!; let x := args[3]!; let y := args[4]!
  let (bv, pc) ← ev (mkApp2 (mkConst ``Decidable.decide) c h)
  if bv.isConstOf ``Bool.true then
    let (v, px) ← ev x
    return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.ite_t) #[α, c, h, x, y, v, pc, px])
  else if bv.isConstOf ``Bool.false then
    let (v, py) ← ev y
    return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.ite_f) #[α, c, h, x, y, v, pc, py])
  else throwError "eval_cert: the condition is not a Boolean value{indentExpr e}"

/-- `if h : c then x h else y h`: certify `decide c`, then the branch taken. -/
meta partial def diteNode (α e : Expr) (args : Array Expr) : EvM (Expr × Expr) := do
  let c := args[1]!; let h := args[2]!; let x := args[3]!; let y := args[4]!
  let dc := mkApp2 (mkConst ``Decidable.decide) c h
  let (bv, pc) ← ev dc
  let snd := mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.ECert.sound) (mkConst ``Bool) dc bv pc
  if bv.isConstOf ``Bool.true then
    let hc := mkApp3 (mkConst ``of_decide_eq_true) c h snd
    let (v, px) ← ev (mkApp x hc).headBeta
    return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.dite_t) #[α, c, h, x, y, v, hc, px])
  else if bv.isConstOf ``Bool.false then
    let hc := mkApp3 (mkConst ``of_decide_eq_false) c h snd
    let (v, py) ← ev (mkApp y hc).headBeta
    return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.dite_f) #[α, c, h, x, y, v, hc, py])
  else throwError "eval_cert: the condition is not a Boolean value{indentExpr e}"

/-- `decide p`: a comparison is an operation node on its two sides; `∧`, `∨`, `¬` unfold to the
Boolean connectives. -/
meta partial def decideNode (α e p h : Expr) : EvM (Expr × Expr) := do
  let p := p.consumeMData
  let pargs := p.getAppArgs
  match p.getAppFn with
  | .const n _ =>
    if relProps.contains n && pargs.size ≥ 2 then
      return ← opNode α e (← nonVals #[pargs[pargs.size - 2]!, pargs[pargs.size - 1]!])
    let h' := h.consumeMData
    match n, h'.getAppFnArgs with
    | ``And, (``instDecidableAnd, #[a, b, ha, hb]) =>
      let rhs := mkApp2 (mkConst ``and) (mkApp2 (mkConst ``Decidable.decide) a ha)
        (mkApp2 (mkConst ``Decidable.decide) b hb)
      let (v, pr) ← ev rhs
      return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.unfold) #[α, e, rhs, v,
        mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.decide_and_eq) a b ha hb, pr])
    | ``Or, (``instDecidableOr, #[a, b, ha, hb]) =>
      let rhs := mkApp2 (mkConst ``or) (mkApp2 (mkConst ``Decidable.decide) a ha)
        (mkApp2 (mkConst ``Decidable.decide) b hb)
      let (v, pr) ← ev rhs
      return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.unfold) #[α, e, rhs, v,
        mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.decide_or_eq) a b ha hb, pr])
    | ``Not, (``instDecidableNot, #[a, ha]) =>
      let rhs := mkApp (mkConst ``not) (mkApp2 (mkConst ``Decidable.decide) a ha)
      let (v, pr) ← ev rhs
      return (v, mkAppN (mkConst `LeanTheory.Certificates.EvalCert.ECert.unfold) #[α, e, rhs, v,
        mkApp2 (mkConst `LeanTheory.Certificates.EvalCert.decide_not_eq) a ha, pr])
    | ``True, _ | ``False, _ => opNode α e #[]
    | _, _ => throwError "eval_cert: unsupported decision{indentExpr p}"
  | _ => throwError "eval_cert: unsupported decision{indentExpr p}"

end

/-- Run the builder on `e` with the extra leaf operations `extra`: value, certificate, number of
nodes and of kernel leaves. -/
meta def evalCertOf (e : Expr) (extra : Array Name) : MetaM (Expr × Expr × Nat × Nat) := do
  let prims := (defaultPrims ++ extra.toList).foldl (fun s n => s.insert n) {}
  let ((v, p), s) ← ((ev e).run { prims }).run {}
  return (v, p, s.nodes, s.leaves)

/-- **`eval_cert [f₁, …]`**: prove `lhs = rhs` for closed terms by evaluation certificates
(`ECert`) of both sides, with `f₁, …` as extra operations that are kernel leaves (e.g. ball
operations). The two values must coincide. -/
syntax (name := evalCertStx) "eval_cert" (" [" ident,* "]")? : tactic

/-- `eval_cert?`: `eval_cert`, also reporting the numbers of nodes and kernel leaves. -/
syntax (name := evalCertStxV) "eval_cert?" (" [" ident,* "]")? : tactic

/-- The elaborator of `eval_cert`. -/
@[tactic evalCertStx, tactic evalCertStxV] meta def evalEvalCert : Tactic := fun stx => do
  let o := stx[1]
  let ids : Array Syntax :=
    if o.getNumArgs == 3 then o[1].getSepArgs
    else if o.getNumArgs == 1 && o[0].getNumArgs == 3 then o[0][1].getSepArgs
    else #[]
  let extra ← ids.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, rhs) := ty.eq? | throwError "eval_cert: expected an equation `lhs = rhs`"
  let prims := (defaultPrims ++ extra.toList).foldl (fun s n => s.insert n) {}
  let run : EvM Expr := do
    let (vl, pl) ← ev lhs
    let snd (x v p : Expr) := mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.ECert.sound) α x v p
    if vl == rhs then return snd lhs vl pl
    let (vr, pr) ← ev rhs
    unless vl == vr do
      throwError "eval_cert: the sides evaluate to different values{indentExpr vl}\nand{indentExpr vr}"
    return mkApp6 (mkConst ``Eq.trans [1]) α lhs vl rhs (snd lhs vl pl)
      (mkApp4 (mkConst ``Eq.symm [1]) α rhs vr (snd rhs vr pr))
  let (pf, s) ← (run.run { prims }).run {}
  if stx.isOfKind ``evalCertStxV then
    let top := (s.heads.toArray.qsort (fun a b => a.2 > b.2)).toList.take 25
    logInfo m!"eval_cert: {s.nodes} nodes, {s.leaves} kernel leaves; by head: {top}"
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

/-- **`eval_decide [f₁, …]`**: prove a decidable closed proposition `p` (a comparison of rationals,
a conjunction of checks, …) as `of_decide_eq_true` of the evaluation certificate of `decide p`,
with `f₁, …` as extra kernel-leaf operations. -/
syntax (name := evalDecideStx) "eval_decide" (" [" ident,* "]")? : tactic

/-- The elaborator of `eval_decide`. -/
@[tactic evalDecideStx] meta def evalEvalDecide : Tactic := fun stx => do
  let o := stx[1]
  let ids : Array Syntax :=
    if o.getNumArgs == 3 then o[1].getSepArgs
    else if o.getNumArgs == 1 && o[0].getNumArgs == 3 then o[0][1].getSepArgs
    else #[]
  let extra ← ids.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  let g ← getMainGoal
  let p ← instantiateMVars (← g.getType)
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let d := mkApp2 (mkConst ``Decidable.decide) p inst
  let prims := (defaultPrims ++ extra.toList).foldl (fun s n => s.insert n) {}
  let run : EvM Expr := do
    let (v, pf) ← ev d
    unless v.isConstOf ``Bool.true do
      throwError "eval_decide: the proposition evaluates to{indentExpr v}"
    let snd := mkApp4 (mkConst `LeanTheory.Certificates.EvalCert.ECert.sound) (mkConst ``Bool) d v pf
    return mkApp3 (mkConst ``of_decide_eq_true) p inst snd
  let (pf, _) ← (run.run { prims }).run {}
  g.assign (← mkExpectedTypeHint pf p)
  replaceMainGoal []

end LeanTheoryMeta.EvalCert
