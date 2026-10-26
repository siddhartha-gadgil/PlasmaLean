/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilData
public import PlasmaLean.Design.PolygonCoilCubicLineCert
public meta import Lean.Elab.Tactic.Basic
public meta import PlasmaLean.Design.PolygonCoilCubicLineCert
public meta import PlasmaLean.Design.PolygonCoilData

/-!
# Certificates for the literal filament data of the polygon-coil checkers (`fils_cert`)

The line checks of the polygon-coil frontier certificates read the checker's filament data
(vertex records `Vt` and segment constants `Seg`) from a literal list, so that the segment
constants are not recomputed for every line. This module proves that such a literal equals the
data computed from the coil set,
`lit = ((List.zip RK RV).flatMap (fun kv => orbit kv.1 kv.2)).map (fun f => mkFil o f.1 f.2)`,
by an explicit certificate (SubsetSum pattern) instead of one kernel evaluation:

* `ORB`: the symmetry orbits of the representative filaments, one leaf per vertex image
  (`gRi p = q`, `gSi p = q`, `gRi (gSi p) = q`, through `LineCert.MC`);
* `CP`: the segment constants of a closed polygon, one leaf `mkSeg o K p q = s` per segment
  (including the closing segment back to the first vertex);
* `mkFil_of`: a filament from its vertex leaves `mkVt p = v` and its `CP` certificate;
* `fils_of`: the whole literal.

The leaves are single non-recursive arithmetic functions on literals; the only bounded iteration
inside a leaf is the fixed Newton count (80) of `sqrtUp` in `mkSeg`. The builder `fils_cert`
takes every expected value from the literal itself (nothing is computed natively except the
orbit images); the kernel checks each leaf.

**Sanity.** `filsCert_reject_fixture`: a goal of the wrong shape is refused.
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

namespace FilsCert

open LineCert

/-- Integer points. -/
abbrev Pt := Int × Int × Int

/-- **Segment constants of a closed polygon** with first vertex `x0`: `CP o K x0 xs ss` says
that the segments `xs[i] → xs[i+1]` (and the last vertex back to `x0`) have the constants
`ss`; one leaf per segment. -/
inductive CP (o : Offs) (K : Int) (x0 : Pt) : List Pt → List Seg → Prop where
  /-- the closing segment `p → x0` -/
  | last (p : Pt) (s : Seg) : mkSeg o K p x0 = s → CP o K x0 [p] [s]
  /-- a segment `p → q`, then the rest -/
  | cons (p q : Pt) (rest : List Pt) (s : Seg) (ss : List Seg) :
      mkSeg o K p q = s → CP o K x0 (q :: rest) ss → CP o K x0 (p :: q :: rest) (s :: ss)

theorem CP.sound {o : Offs} {K : Int} {x0 : Pt} {xs : List Pt} {ss : List Seg}
    (h : CP o K x0 xs ss) :
    ∀ a l, xs = a :: l → (List.zip (a :: l) (l ++ [x0])).map (fun pq => mkSeg o K pq.1 pq.2) = ss
    := by
  induction h with
  | last p s h1 =>
    intro a l hl
    simp only [List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [h1]
  | cons p q rest s ss h1 _ ih =>
    intro a l hl
    simp only [List.cons.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    have := ih q rest rfl
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons] at this ⊢
    rw [h1, this]

/-- **A filament** from its vertex leaves and its segment certificate. -/
theorem mkFil_of (o : Offs) (K : Int) (x0 : Pt) (rest : List Pt) (vts : List Vt) (sgs : List Seg)
    (hv : MC mkVt (x0 :: rest) vts) (hs : CP o K x0 (x0 :: rest) sgs) :
    mkFil o K (x0 :: rest) = ⟨vts, sgs⟩ := by
  have h1 := hv.sound
  have h2 := hs.sound x0 rest rfl
  simp only [mkFil, rot1, h1, h2]

/-- **The symmetry orbits** of the representatives `(RK, RV)`: `ORB RK RV L` says
`(List.zip RK RV).flatMap (fun kv => orbit kv.1 kv.2) = L`. -/
inductive ORB : List Int → List (List Pt) → List (Int × List Pt) → Prop where
  /-- no representative left -/
  | nil : ORB [] [] []
  /-- one representative and its four images, then the others -/
  | cons (K : Int) (vs : List Pt) (RK : List Int) (RV : List (List Pt)) (a b c : List Pt)
      (rest : List (Int × List Pt)) :
      vs.map gRi = a → vs.map gSi = b → vs.map (fun p => gRi (gSi p)) = c → ORB RK RV rest →
      ORB (K :: RK) (vs :: RV) ((K, vs) :: (K, a) :: (-K, b) :: (-K, c) :: rest)

theorem ORB.sound {RK : List Int} {RV : List (List Pt)} {L : List (Int × List Pt)}
    (h : ORB RK RV L) : (List.zip RK RV).flatMap (fun kv => orbit kv.1 kv.2) = L := by
  induction h with
  | nil => rfl
  | cons K vs RK RV a b c rest h1 h2 h3 _ ih =>
    rw [List.zip_cons_cons, List.flatMap_cons, ih, ← h1, ← h2, ← h3]
    rfl

/-- **The literal filament data** from the orbit and filament certificates. -/
theorem fils_of (o : Offs) (RK : List Int) (RV : List (List Pt)) (L : List (Int × List Pt))
    (D : List Fil) (hz : ORB RK RV L) (hm : MC (fun f => mkFil o f.1 f.2) L D) :
    D = ((List.zip RK RV).flatMap (fun kv => orbit kv.1 kv.2)).map
      (fun f => mkFil o f.1 f.2) := by
  rw [hz.sound, hm.sound]

/-! ## The builder (`meta`, untrusted) -/

open Lean Meta Elab Tactic

/-- The type `ℤ × ℤ × ℤ`. -/
meta def tPt : Expr := tP tI (tP tI tI)

/-- A point expression. -/
meta def ptE (p : Pt) : Expr :=
  pairE tI (tP tI tI) (intE p.1) (pairE tI tI (intE p.2.1) (intE p.2.2))

/-- Read a point literal. -/
meta def readPt (e : Expr) : MetaM Pt := do
  let a ← fieldsOf e 4
  let b ← fieldsOf a[3]! 4
  return (← readInt a[2]!, ← readInt b[2]!, ← readInt b[3]!)

/-- An `MC f xs ys` proof with `Eq.refl` leaves (`xs`, `ys` given as element arrays). -/
meta def mcE (α β f : Expr) (xs ys : Array Expr) : Expr := Id.run do
  let xT := tailsE α xs
  let yT := tailsE β ys
  let mut pf := mkApp3 (mkConst ``MC.nil) α β f
  for j in [0:xs.size] do
    let i := xs.size - 1 - j
    pf := mkAppN (mkConst ``MC.cons) #[α, β, f, xs[i]!, xT[i + 1]!, ys[i]!, yT[i + 1]!,
      reflE β ys[i]!, pf]
  return pf

/-- `List.cons`/`List.nil` tails of an array (shared). -/
meta def listOf (α : Expr) (xs : Array Expr) : Expr := (tailsE α xs)[0]!

/-- **`fils_cert`**: prove `lit = filsX` where `lit` is a constant whose body is a literal
`List Fil` and `filsX` unfolds to
`((List.zip RK RV).flatMap (fun kv => orbit kv.1 kv.2)).map (fun f => mkFil o f.1 f.2)`
with `RK`, `RV`, `o` constants with literal bodies. -/
syntax (name := filsCertStx) "fils_cert" : tactic

/-- The elaborator of `fils_cert`. -/
@[tactic filsCertStx] meta def evalFilsCert : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "fils_cert: expected an equation"
  let litB ← bodyOf lhs
  let rB ← bodyOf rhs
  let (``List.map, #[_, _, _, filsE]) := rB.getAppFnArgs |
    throwError "fils_cert: expected `List.map (fun f => mkFil o f.1 f.2) fils`{indentExpr rB}"
  let fB ← bodyOf filsE
  let (``List.flatMap, #[_, _, _, zE]) := fB.getAppFnArgs |
    throwError "fils_cert: expected `List.flatMap`{indentExpr fB}"
  let (``List.zip, #[_, _, RKE, RVE]) := zE.getAppFnArgs |
    throwError "fils_cert: expected `List.zip RK RV`{indentExpr zE}"
  -- the offsets: from the mapped function `fun f => mkFil o f.1 f.2`
  let (``List.map, #[_, _, mapF, _]) := rB.getAppFnArgs | unreachable!
  let oE ← match mapF with
    | .lam _ _ b _ =>
      match b.getAppFnArgs with
      | (``mkFil, #[o, _, _]) => pure o
      | _ => throwError "fils_cert: expected `fun f => mkFil o f.1 f.2`"
    | _ => throwError "fils_cert: expected `fun f => mkFil o f.1 f.2`"
  let rkEl ← listElems (← bodyOf RKE)
  let rvEl ← listElems (← bodyOf RVE)
  let rkT ← listTails (← bodyOf RKE)
  let rvT ← listTails (← bodyOf RVE)
  unless rkEl.size == rvEl.size do throwError "fils_cert: RK and RV differ in length"
  let litEl ← listElems litB
  let litT ← listTails litB
  unless litEl.size == 4 * rkEl.size do throwError "fils_cert: literal has the wrong length"
  let tF := mkConst ``Fil
  let tVt := mkConst ``Vt
  let tSeg := mkConst ``Seg
  let tKL := tP tI (tL tPt)
  -- orbit images
  let mut Lel : Array Expr := #[]
  let mut orbParts : Array (Array Expr) := #[]
  for r in [0:rkEl.size] do
    let KE := rkEl[r]!
    let K ← readInt KE
    let vsEl ← listElems rvEl[r]!
    let vs ← vsEl.mapM fun e => readPt e
    let aEl := vs.map fun p => ptE (gRi p)
    let bEl := vs.map fun p => ptE (gSi p)
    let cEl := vs.map fun p => ptE (gRi (gSi p))
    let aE := listOf tPt aEl
    let bE := listOf tPt bEl
    let cE := listOf tPt cEl
    let gRiE := mkConst ``gRi
    let gSiE := mkConst ``gSi
    let gRSE := Expr.lam `p tPt (mkApp gRiE (mkApp gSiE (.bvar 0))) .default
    let ha := mkApp (mkAppN (mkConst ``MC.sound) #[tPt, tPt, gRiE, rvEl[r]!, aE])
      (mcE tPt tPt gRiE vsEl aEl)
    let hb := mkApp (mkAppN (mkConst ``MC.sound) #[tPt, tPt, gSiE, rvEl[r]!, bE])
      (mcE tPt tPt gSiE vsEl bEl)
    let hc := mkApp (mkAppN (mkConst ``MC.sound) #[tPt, tPt, gRSE, rvEl[r]!, cE])
      (mcE tPt tPt gRSE vsEl cEl)
    let nK := intE (-K)
    Lel := Lel ++ #[pairE tI (tL tPt) KE rvEl[r]!, pairE tI (tL tPt) KE aE,
      pairE tI (tL tPt) nK bE, pairE tI (tL tPt) nK cE]
    orbParts := orbParts.push #[KE, rvEl[r]!, aE, bE, cE, ha, hb, hc]
  let LT := tailsE tKL Lel
  -- ORB proof
  let mut orb := mkConst ``ORB.nil
  for j in [0:rkEl.size] do
    let r := rkEl.size - 1 - j
    let P := orbParts[r]!
    orb := mkAppN (mkConst ``ORB.cons) #[P[0]!, P[1]!, rkT[r + 1]!, rvT[r + 1]!, P[2]!, P[3]!,
      P[4]!, LT[4 * r + 4]!, P[5]!, P[6]!, P[7]!, orb]
  -- filament certificates
  let mapFE := mapF
  let mut mc := mkApp3 (mkConst ``MC.nil) tKL tF mapFE
  for j in [0:Lel.size] do
    let i := Lel.size - 1 - j
    let r := i / 4
    let q := i % 4
    let Kv ← readInt rkEl[r]!
    let KE := if q < 2 then rkEl[r]! else intE (-Kv)
    let xsE := Lel[i]!.appArg!
    let xsEl ← match q with
      | 0 => listElems rvEl[r]!
      | _ => listElems xsE
    let xsT := tailsE tPt xsEl
    let x0 := xsEl[0]!
    let fa ← fieldsOf litEl[i]! 2
    let vtsEl ← listElems fa[0]!
    let vtsT ← listTails fa[0]!
    let sgsEl ← listElems fa[1]!
    let sgsT ← listTails fa[1]!
    let n := xsEl.size
    unless vtsEl.size == n && sgsEl.size == n do
      throwError "fils_cert: filament {i} has the wrong number of vertices or segments"
    let hv := mcE tPt tVt (mkConst ``mkVt) xsEl vtsEl
    let mut cp := mkAppN (mkConst ``CP.last) #[oE, KE, x0, xsEl[n - 1]!, sgsEl[n - 1]!,
      reflE tSeg sgsEl[n - 1]!]
    for jj in [0:n - 1] do
      let k := n - 2 - jj
      cp := mkAppN (mkConst ``CP.cons) #[oE, KE, x0, xsEl[k]!, xsEl[k + 1]!, xsT[k + 2]!,
        sgsEl[k]!, sgsT[k + 1]!, reflE tSeg sgsEl[k]!, cp]
    let hf := mkAppN (mkConst ``mkFil_of) #[oE, KE, x0, xsT[1]!, vtsT[0]!, sgsT[0]!, hv, cp]
    mc := mkAppN (mkConst ``MC.cons) #[tKL, tF, mapFE, Lel[i]!, LT[i + 1]!, litEl[i]!,
      litT[i + 1]!, hf, mc]
  let pf := mkAppN (mkConst ``fils_of) #[oE, rkT[0]!, rvT[0]!, LT[0]!, litT[0]!, orb, mc]
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

/-- **Sanity** (rejected): a goal of the wrong shape is refused. -/
theorem filsCert_reject_fixture : True := by
  fail_if_success (have : (1 : Nat) = 1 := by fils_cert)
  trivial

end FilsCert

end PlasmaLean.Design.PolygonCoil
