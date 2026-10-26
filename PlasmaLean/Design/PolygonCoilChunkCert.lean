/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicLineCert
public meta import Lean.Elab.Tactic.Basic
public meta import PlasmaLean.Design.PolygonCoilCubicLineCert

/-!
# Per-segment certificates for the bilinear frontier chunks (`chunk_cert`)

A chunk check `checkChunk o fs F [m₀, …, m₄] = true` of `Design/PolygonCoilCheck` evaluates the
grid lines `m₀, …, m₄` (`lineOut`: ≈ 20 corners per line, at each corner one vertex step per
filament vertex, one Biot–Savart segment step with the cell remainder per segment, and the final
assembly `cornerFinal`), and then the cell checks `cellsOK` between consecutive lines. This module
certifies it step by step (SubsetSum pattern), reusing the vertex certificates `FV`/`AV` and the
map certificate `MC` of `Design/PolygonCoilCubicLineCert`:

* `WR`/`AWR`: the segment walk with the remainder data `r` of the attached cell (`segStep … r`),
  one leaf per block of up to three segments, with the closing segment back to the first vertex;
* `corner_of`: the corner output `cornerEval … = ⟨ok, e, rem, gs'⟩` from the vertex and walk
  certificates and one leaf for `cornerFinal`;
* `LCB`: the corners along a line, through `lineStepB` (one iteration of `lineGo`), with leaves
  for `cornerXYZ`, `rhOf` (the cell constants `cellRC`), `helAt`;
* `CO`: the cell checks `cellsOK` between two lines, one leaf per cell;
* `CLines`, `chunk_of`: the chunk, from its lines, the face check `faceOK F = true` and the
  `hel` coefficients (`MC`).

The leaves are single non-recursive arithmetic functions on literals (the only bounded iterations
inside a leaf are the fixed Newton counts of `coldStart` and `sqrtUpFrom`). The `meta` builder
`chunk_cert` runs the checker's own functions on native values (untrusted; the kernel re-checks
each leaf). It rewrites the filament data to a literal copy (`chunk_cert hfils hface`: `hfils :
lit = fs`, `hface : faceOK F = true`) and the chunk `(grid.drop k).take n` to a literal list
(`DT`, one step per list cell).

**Sanity.** `chunkCert_reject_fixture`: a goal of the wrong shape is refused.
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

namespace ChunkCert

open LineCert

/-! ## Segment walks with a cell remainder -/

/-- **Segment walk of one filament** with the remainder data `r` (`filWalkAux … r`), one leaf
per block of up to three segments; `first` closes the loop. -/
inductive WR (D2 D3S : Nat) (r : RC) (first : VR) : Acc → List Seg → List VR → Acc → Prop where
  /-- a segment `a → b` followed by more segments -/
  | step (acc : Acc) (s : Seg) (ss : List Seg) (a b : VR) (rs : List VR) (acc' out : Acc) :
      segStep D2 D3S r acc s a b = acc' → WR D2 D3S r first acc' ss (b :: rs) out →
      WR D2 D3S r first acc (s :: ss) (a :: b :: rs) out
  /-- two segments as one leaf, followed by more segments -/
  | step2 (acc : Acc) (s₁ s₂ : Seg) (ss : List Seg) (a b c : VR) (rs : List VR) (acc' out : Acc) :
      segStep D2 D3S r (segStep D2 D3S r acc s₁ a b) s₂ b c = acc' →
      WR D2 D3S r first acc' ss (c :: rs) out →
      WR D2 D3S r first acc (s₁ :: s₂ :: ss) (a :: b :: c :: rs) out
  /-- three segments as one leaf, followed by more segments -/
  | step3 (acc : Acc) (s₁ s₂ s₃ : Seg) (ss : List Seg) (a b c d : VR) (rs : List VR)
      (acc' out : Acc) :
      segStep D2 D3S r (segStep D2 D3S r (segStep D2 D3S r acc s₁ a b) s₂ b c) s₃ c d = acc' →
      WR D2 D3S r first acc' ss (d :: rs) out →
      WR D2 D3S r first acc (s₁ :: s₂ :: s₃ :: ss) (a :: b :: c :: d :: rs) out
  /-- the closing segment `a → first` -/
  | last (acc : Acc) (s : Seg) (a : VR) (out : Acc) :
      segStep D2 D3S r acc s a first = out → WR D2 D3S r first acc [s] [a] out

theorem WR.sound {D2 D3S : Nat} {r : RC} {first : VR} {acc : Acc} {ss : List Seg} {L : List VR}
    {out : Acc} (h : WR D2 D3S r first acc ss L out) :
    filWalkAux D2 D3S r first acc ss L = out := by
  induction h with
  | step acc s ss a b rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | step2 acc s₁ s₂ ss a b c rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | step3 acc s₁ s₂ s₃ ss a b c d rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | last acc s a out h1 => simp [filWalkAux, h1]

/-- **Walk of all filaments** with the remainder data `r` (`allWalk … r`). -/
inductive AWR (D2 D3S : Nat) (r : RC) : Acc → List Fil → List (List VR) → Acc → Prop where
  /-- no filament left -/
  | nil (acc : Acc) : AWR D2 D3S r acc [] [] acc
  /-- one filament, then the others -/
  | cons (acc : Acc) (f : Fil) (fs : List Fil) (v : VR) (vv : List VR) (vs : List (List VR))
      (acc' out : Acc) :
      WR D2 D3S r v acc f.sgs (v :: vv) acc' → AWR D2 D3S r acc' fs vs out →
      AWR D2 D3S r acc (f :: fs) ((v :: vv) :: vs) out

theorem AWR.sound {D2 D3S : Nat} {r : RC} {acc : Acc} {fs : List Fil} {vs : List (List VR)}
    {out : Acc} (h : AWR D2 D3S r acc fs vs out) : allWalk D2 D3S r acc fs vs = out := by
  induction h with
  | nil acc => simp [allWalk]
  | cons acc f fs v vv vs acc' out h1 _ ih => simp only [allWalk, filWalk, h1.sound]; exact ih

/-! ## Corners -/

/-- **A corner** from the vertex and walk certificates and the final assembly. -/
theorem corner_of (o : Offs) (fs : List Fil) (Xt Yt Zt D : Nat) (h : QQ × QQ × QQ) (r : RC)
    (gs : List (List Nat)) (c : CD) (D2 D3S : Nat) (vs : List (List VR))
    (gs' : List (List Nat)) (acc : Acc) (fin : Bool × Nat) (ok : Bool)
    (hc : cdOf Xt Yt Zt D = c) (hD2 : Nat.mul D D = D2)
    (hD3 : Nat.mul (Nat.mul D2 D) two136 = D3S)
    (hv : AV c fs gs vs gs') (hw : AWR D2 D3S r accInit fs vs acc)
    (hf : cornerFinal o Xt Yt Zt D c.lam acc h = fin)
    (hok : (((acc.ok && fin.1) && Nat.ble (Nat.mul 1000 KT) c.lam) &&
      (!r.doRem || Nat.ble r.rBD r.s0l)) = ok) :
    cornerEval o fs Xt Yt Zt D h r gs = ⟨ok, fin.2, acc.rem, gs'⟩ := by
  subst hc hD2 hD3
  obtain ⟨hv1, hv2⟩ := hv.sound
  have hw1 := hw.sound
  simp only [cornerEval]
  simp only [cdOf, accInit] at hv1 hw1 hf hok
  rw [hv1, hw1, hf, hok, hv2]

/-! ## Lines -/

/-- The cell constants of `lineGo` (attached cell towards the next line, if any). -/
def rhOf (F : Face) (m : Nat) (m' : Option Nat) (wn : Int) (ws : List Int) (D : Nat) : RC × Nat :=
  match m', ws with
  | some m1, wn' :: _ => cellRC F m m1 wn wn' D
  | _, _ => (noRC, 0)

/-- One iteration of `lineGo`: the corner entry and the new warm starts. -/
def lineStepB (o : Offs) (fs : List Fil) (F : Face) (m : Nat) (m' : Option Nat) (t : Trig)
    (wn : Int) (ws : List Int) (hc : HC) (gs : List (List Nat)) :
    (Bool × Nat × Nat) × List (List Nat) :=
  let cx := cornerXYZ F m wn
  let xyz := cx.1
  let rh := rhOf F m m' wn ws xyz.2.2.2
  let co := cornerEval o fs xyz.1 xyz.2.1 xyz.2.2.1 xyz.2.2.2 (helAt hc t) rh.1 gs
  ((co.ok && cx.2, co.e, Nat.add co.rem rh.2), co.gs)

theorem lineGo_cons (o : Offs) (fs : List Fil) (F : Face) (m : Nat) (m' : Option Nat) (t : Trig)
    (wn : Int) (ws : List Int) (hc : HC) (hcs : List HC) (gs : List (List Nat)) :
    lineGo o fs F m m' t (wn :: ws) (hc :: hcs) gs =
      (lineStepB o fs F m m' t wn ws hc gs).1 ::
        lineGo o fs F m m' t ws hcs (lineStepB o fs F m m' t wn ws hc gs).2 := by
  rcases m' with _ | m1 <;> rcases ws with _ | ⟨a, l⟩ <;> rfl

/-- **The corners of a line**: `LCB … ws hcs gs rs` says `lineGo … ws hcs gs = rs`; one node per
corner. -/
inductive LCB (o : Offs) (fs : List Fil) (F : Face) (m : Nat) (m' : Option Nat) (t : Trig) :
    List Int → List HC → List (List Nat) → List (Bool × Nat × Nat) → Prop where
  /-- end of the `w`-grid -/
  | nil (hcs : List HC) (gs : List (List Nat)) : LCB o fs F m m' t [] hcs gs []
  /-- one corner, then the rest of the line -/
  | cons (wn : Int) (ws : List Int) (hc : HC) (hcs : List HC) (gs : List (List Nat))
      (r : Bool × Nat × Nat) (gs' : List (List Nat)) (rs : List (Bool × Nat × Nat)) :
      lineStepB o fs F m m' t wn ws hc gs = (r, gs') → LCB o fs F m m' t ws hcs gs' rs →
      LCB o fs F m m' t (wn :: ws) (hc :: hcs) gs (r :: rs)

theorem LCB.sound {o : Offs} {fs : List Fil} {F : Face} {m : Nat} {m' : Option Nat} {t : Trig}
    {ws : List Int} {hcs : List HC} {gs : List (List Nat)} {rs : List (Bool × Nat × Nat)}
    (h : LCB o fs F m m' t ws hcs gs rs) : lineGo o fs F m m' t ws hcs gs = rs := by
  induction h with
  | nil hcs gs => rcases hcs with _ | _ <;> rfl
  | cons wn ws hc hcs gs r gs' rs h1 _ ih => rw [lineGo_cons, h1]; exact congrArg _ ih

/-- **A corner step.** -/
theorem lineStepB_of (o : Offs) (fs : List Fil) (F : Face) (m : Nat) (m' : Option Nat)
    (t : Trig) (wn : Int) (ws : List Int) (hc : HC) (gs : List (List Nat))
    (X Y Z D : Nat) (okx : Bool) (rc : RC) (ht : Nat) (hv : QQ × QQ × QQ) (co : CornerOut)
    (r : Bool × Nat × Nat)
    (hcx : cornerXYZ F m wn = ((X, Y, Z, D), okx)) (hrh : rhOf F m m' wn ws D = (rc, ht))
    (hh : helAt hc t = hv) (hco : cornerEval o fs X Y Z D hv rc gs = co)
    (hr : (co.ok && okx, co.e, Nat.add co.rem ht) = r) :
    lineStepB o fs F m m' t wn ws hc gs = (r, co.gs) := by
  simp only [lineStepB, hcx, hrh, hh, hco, hr]

/-- **A grid line** from its corner certificates. -/
theorem lineB_of (o : Offs) (fs : List Fil) (F : Face) (hcs : List HC) (m : Nat)
    (m' : Option Nat) (t : Trig) (ws : List Int) (rs : List (Bool × Nat × Nat))
    (ht : trigOf m = t) (hw : F.wn = ws) (h : LCB o fs F m m' t ws hcs [] rs) :
    lineOut o fs F hcs m m' = rs := by
  simp only [lineOut, ht, hw]
  exact h.sound

/-! ## Cells and chunks -/

/-- **The cell checks between two lines** (`cellsOK`), one leaf per cell. -/
inductive CO : List (Bool × Nat × Nat) → List (Bool × Nat × Nat) → Prop where
  /-- the last corner pair -/
  | one (a b : Bool × Nat × Nat) : CO [a] [b]
  /-- one cell, then the others -/
  | cons (a a' : Bool × Nat × Nat) (as : List (Bool × Nat × Nat)) (b b' : Bool × Nat × Nat)
      (bs : List (Bool × Nat × Nat)) :
      (((a.1 && a'.1) && (b.1 && b'.1)) &&
        Nat.ble (Nat.add (nmax (nmax a.2.1 a'.2.1) (nmax b.2.1 b'.2.1)) a.2.2) etaFp) = true →
      CO (a' :: as) (b' :: bs) → CO (a :: a' :: as) (b :: b' :: bs)

theorem CO.sound {l₁ l₂ : List (Bool × Nat × Nat)} (h : CO l₁ l₂) : cellsOK l₁ l₂ = true := by
  induction h with
  | one a b => simp [cellsOK]
  | cons a a' as b b' bs h1 _ ih => simp only [cellsOK, h1, ih, Bool.and_self]

/-- **The lines of a chunk** after the first: `CLines … prev m₀ ms` says
`checkLines o fs F hcs prev m₀ ms = true`. -/
inductive CLines (o : Offs) (fs : List Fil) (F : Face) (hcs : List HC) :
    List (Bool × Nat × Nat) → Nat → List Nat → Prop where
  /-- an inner line `m` (next line `m'`) -/
  | cons (prev : List (Bool × Nat × Nat)) (m0 m m' : Nat) (rest : List Nat)
      (cur : List (Bool × Nat × Nat)) :
      lineOut o fs F hcs m (some m') = cur → Nat.blt m0 m = true → CO prev cur →
      CLines o fs F hcs cur m (m' :: rest) → CLines o fs F hcs prev m0 (m :: m' :: rest)
  /-- the last line `m` -/
  | last (prev : List (Bool × Nat × Nat)) (m0 m : Nat) (cur : List (Bool × Nat × Nat)) :
      lineOut o fs F hcs m none = cur → Nat.blt m0 m = true → CO prev cur →
      CLines o fs F hcs prev m0 [m]

theorem CLines.sound {o : Offs} {fs : List Fil} {F : Face} {hcs : List HC}
    {prev : List (Bool × Nat × Nat)} {m0 : Nat} {ms : List Nat}
    (h : CLines o fs F hcs prev m0 ms) : checkLines o fs F hcs prev m0 ms = true := by
  induction h with
  | cons prev m0 m m' rest cur h1 h2 h3 _ ih =>
    simp only [checkLines, h1, h2, h3.sound, ih, Bool.and_self]
  | last prev m0 m cur h1 h2 h3 => simp only [checkLines, h1, h2, h3.sound, Bool.and_self]

/-- **A chunk** from its lines, the face check and the `hel` coefficients. -/
theorem chunk_of (o : Offs) (fs : List Fil) (F : Face) (m m' : Nat) (rest : List Nat)
    (ws : List Int) (hcs : List HC) (first : List (Bool × Nat × Nat)) (hw : F.wn = ws)
    (hh : MC (fun wn => let rz := faceRZ F wn; helCoef rz.1 rz.2) ws hcs)
    (hF : faceOK F = true) (h1 : lineOut o fs F hcs m (some m') = first)
    (hL : CLines o fs F hcs first m (m' :: rest)) : checkChunk o fs F (m :: m' :: rest) = true := by
  have h2 : faceHC F = hcs := by rw [faceHC, hw]; exact hh.sound
  simp only [checkChunk, h2, hF, h1, hL.sound, Bool.and_self]

/-- **Drop and take of a list**, one step per list cell: `DT xs k n ys` says
`(xs.drop k).take n = ys`. -/
inductive DT {α : Type} : List α → Nat → Nat → List α → Prop where
  /-- drop one more cell -/
  | drop (x : α) (xs : List α) (k n : Nat) (ys : List α) : DT xs k n ys → DT (x :: xs) (k + 1) n ys
  /-- take one cell -/
  | take (x : α) (xs : List α) (n : Nat) (ys : List α) : DT xs 0 n ys → DT (x :: xs) 0 (n + 1) (x :: ys)
  /-- nothing left to take -/
  | done (xs : List α) : DT xs 0 0 []
  /-- the list is exhausted -/
  | short (n : Nat) : DT [] 0 n []

theorem DT.sound {α : Type} {xs : List α} {k n : Nat} {ys : List α} (h : DT xs k n ys) :
    (xs.drop k).take n = ys := by
  induction h with
  | drop x xs k n ys _ ih => simpa using ih
  | take x xs n ys _ ih => simp only [List.drop_zero, List.take_succ_cons] at ih ⊢; rw [ih]
  | done xs => simp
  | short n => simp

/-! ## The builder (`meta`, untrusted) -/

open Lean Meta Elab Tactic

/-- Inline the `have`/`let` bindings of a definition body (long list literals are elaborated
with local bindings). -/
meta def zetaAll (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => match e with
    | .letE _ _ v b _ => return .done (b.instantiate1 v)
    | _ => return .continue)

/-- A `Bool × ℕ × ℕ` value. -/
meta def bnnE (r : Bool × Nat × Nat) : Expr :=
  pairE tB (tP tN tN) (boolE r.1) (pairE tN tN (natE r.2.1) (natE r.2.2))

/-- The type `Bool × ℕ × ℕ`. -/
meta def tBNN : Expr := tP tB (tP tN tN)

/-- Read a `Face` literal. -/
meta def readFaceB (e : Expr) : MetaM Face := do
  let f ← fieldsOf e 7
  return ⟨← readNat f[0]!, ← readNat f[1]!, (← (← listElems f[2]!).mapM readInt).toList,
    ← readNat f[3]!, ← readNat f[4]!, ← readNat f[5]!, ← readNat f[6]!⟩

/-- Certificate of one corner: `(proof of cornerEval … = co, co expression, native output,
new warm-start element expressions)`. -/
meta def cornerCertB (blk : Nat) (oE fsE : Expr) (o : Offs) (fils : Array FilE)
    (filT : Array Expr) (X Y Z D : Nat) (hv : QQ × QQ × QQ) (hvE : Expr) (r : RC) (rE : Expr)
    (gs : List (List Nat)) (gsE : Expr) (gsElems : Array (Array Expr × Array Expr)) :
    MetaM (Expr × Expr × CornerOut × Array (Array Expr × Array Expr)) := do
  let D2 := Nat.mul D D
  let c : CD := ⟨D, D2, Nat.mul X two32, Nat.mul Y two32, Nat.mul Z two32,
    Nat.add (Nat.add (sq (Nat.mul X two32)) (sq (Nat.mul Y two32))) (sq (Nat.mul Z two32)),
    Nat.mul D two32⟩
  let D3S := Nat.mul (Nat.mul D2 D) two136
  let cE := cdE c
  let tVR := mkConst ``VR
  let tLN := tL tN
  let rVR := reflH tVR
  let rN := reflH tN
  let fvWarm := mkApp (mkConst ``FV.warm) cE
  let fvCold := mkApp (mkConst ``FV.cold) cE
  let warm := !gs.isEmpty
  let gsA := gs.toArray
  let mut vsN : Array (Array VR) := #[]
  let mut rsT : Array (Array Expr) := #[]
  let mut rsEl : Array (Array Expr) := #[]
  let mut gNew : Array (Array Expr × Array Expr) := #[]
  let mut fvPf : Array Expr := #[]
  for k in [0:fils.size] do
    let F := fils[k]!
    let vts := F.val.vts.toArray
    let n := vts.size
    let gk : Array Nat := if warm then (gsA[k]!).toArray else #[]
    let mut rs : Array VR := #[]
    let mut g0s : Array Nat := #[]
    for i in [0:n] do
      let g0 := if warm then gk[i]! else coldStart c vts[i]!
      g0s := g0s.push g0
      rs := rs.push (vertStep c vts[i]! g0)
    let gEl := rs.map fun r => natE r.g
    let rEl := (rs.zip gEl).map fun (r, gE) => vrE r gE
    let rT := tailsE tVR rEl
    let gT := tailsE tN gEl
    let mut pf := mkApp2 (mkConst ``FV.nil) cE
      (if warm then (gsElems[k]!).2[n]! else mkApp (mkConst ``List.nil [Level.zero]) tN)
    for j in [0:n] do
      let i := n - 1 - j
      if warm then
        let (gEi, gTi) := gsElems[k]!
        pf := mkAppN fvWarm #[F.vts[i]!, F.vtsT[i + 1]!, gEi[i]!, gTi[i + 1]!,
          rEl[i]!, rT[i + 1]!, gT[i + 1]!, mkApp rVR rEl[i]!, pf]
      else
        let gE := natE g0s[i]!
        pf := mkAppN fvCold #[F.vts[i]!, F.vtsT[i + 1]!, gE, rEl[i]!, rT[i + 1]!,
          gT[i + 1]!, mkApp rN gE, mkApp rVR rEl[i]!, pf]
    vsN := vsN.push rs
    rsT := rsT.push rT
    rsEl := rsEl.push rEl
    gNew := gNew.push (gEl, gT)
    fvPf := fvPf.push pf
  let tLVR := tL tVR
  let vsT := tailsE tLVR (rsT.map (·[0]!))
  let gsT' := tailsE tLN (gNew.map (·.2[0]!))
  let gsTails : Array Expr ← if warm then listTails gsE else pure #[]
  let mut av := if warm then mkApp2 (mkConst ``AV.nil) cE gsTails[fils.size]!
    else mkApp2 (mkConst ``AV.nil) cE gsE
  for j in [0:fils.size] do
    let k := fils.size - 1 - j
    if warm then
      av := mkAppN (mkConst ``AV.warm) #[cE, fils[k]!.e, filT[k + 1]!, (gsElems[k]!).2[0]!,
        gsTails[k + 1]!, rsT[k]![0]!, vsT[k + 1]!, gNew[k]!.2[0]!, gsT'[k + 1]!, fvPf[k]!, av]
    else
      av := mkAppN (mkConst ``AV.cold) #[cE, fils[k]!.e, filT[k + 1]!, rsT[k]![0]!, vsT[k + 1]!,
        gNew[k]!.2[0]!, gsT'[k + 1]!, fvPf[k]!, av]
  -- walks
  let D2E := natE D2
  let D3E := natE D3S
  let mut acc : Acc := ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  let mut accX := accE acc
  let mut steps : Array (Array Expr) := #[]
  for k in [0:fils.size] do
    let sgs := fils[k]!.val.sgs.toArray
    let rs := vsN[k]!
    let n := sgs.size
    let mut st := #[accX]
    for i in [0:n] do
      let a := rs[i]!
      let b := if i + 1 < n then rs[i + 1]! else rs[0]!
      acc := segStep D2 D3S r acc sgs[i]! a b
      accX := accE acc
      st := st.push accX
    steps := steps.push st
  let tAcc := mkConst ``Acc
  let rAcc := reflH tAcc
  let mut aw := mkAppN (mkConst ``AWR.nil) #[D2E, D3E, rE, accX]
  for j in [0:fils.size] do
    let k := fils.size - 1 - j
    let F := fils[k]!
    let st := steps[k]!
    let n := F.sgs.size
    let rEl := rsEl[k]!
    let rT := rsT[k]!
    let first := rEl[0]!
    let outX := st[n]!
    let a0X := st[0]!
    let wStep := mkAppN (mkConst ``WR.step) #[D2E, D3E, rE, first]
    let wStep2 := mkAppN (mkConst ``WR.step2) #[D2E, D3E, rE, first]
    let wStep3 := mkAppN (mkConst ``WR.step3) #[D2E, D3E, rE, first]
    let blocks : Array (Nat × Nat) := Id.run do
      let mut out := #[]
      let mut i := 0
      while i + 1 < n do
        let k := min blk (n - 1 - i)
        out := out.push (i, k)
        i := i + k
      return out
    let mut sw := mkAppN (mkConst ``WR.last) #[D2E, D3E, rE, first, st[n - 1]!, F.sgs[n - 1]!,
      rEl[n - 1]!, outX, reflE tAcc outX]
    for (i, k) in blocks.reverse do
      let aX := st[i]!
      let aX' := st[i + k]!
      sw := match k with
        | 1 => mkAppN wStep #[aX, F.sgs[i]!, F.sgsT[i + 1]!, rEl[i]!,
            rEl[i + 1]!, rT[i + 2]!, aX', outX, mkApp rAcc aX', sw]
        | 2 => mkAppN wStep2 #[aX, F.sgs[i]!, F.sgs[i + 1]!, F.sgsT[i + 2]!, rEl[i]!,
            rEl[i + 1]!, rEl[i + 2]!, rT[i + 3]!, aX', outX, mkApp rAcc aX', sw]
        | _ => mkAppN wStep3 #[aX, F.sgs[i]!, F.sgs[i + 1]!, F.sgs[i + 2]!, F.sgsT[i + 3]!,
            rEl[i]!, rEl[i + 1]!, rEl[i + 2]!, rEl[i + 3]!, rT[i + 4]!, aX', outX,
            mkApp rAcc aX', sw]
    aw := mkAppN (mkConst ``AWR.cons) #[D2E, D3E, rE, a0X, F.e, filT[k + 1]!, first, rT[1]!,
      vsT[k + 1]!, outX, accX, sw, aw]
  -- final assembly
  let fin := cornerFinal o X Y Z D c.lam acc hv
  let finX := pairE tB tN (boolE fin.1) (natE fin.2)
  let ok := ((acc.ok && fin.1) && Nat.ble (Nat.mul 1000 KT) c.lam) &&
    (!r.doRem || Nat.ble r.rBD r.s0l)
  let okX := boolE ok
  let gsOut := vsN.toList.map (fun l => l.toList.map VR.g)
  let vsX := vsT[0]!
  let gsX := gsT'[0]!
  let pf := mkAppN (mkConst ``corner_of) #[oE, fsE, natE X, natE Y, natE Z, natE D, hvE, rE, gsE,
    cE, D2E, D3E, vsX, gsX, accX, finX, okX, reflE (mkConst ``CD) cE, reflE tN D2E,
    reflE tN D3E, av, aw, reflE (tP tB tN) finX, reflE tB okX]
  let co : CornerOut := ⟨ok, fin.2, acc.rem, gsOut⟩
  let coX := mkAppN (mkConst ``CornerOut.mk) #[okX, natE fin.2, natE acc.rem, gsX]
  return (pf, coX, co, gNew)

/-- Certificate of one grid line `lineOut o fs F hcs m m' = rs`; returns the proof and the
native and expression values of `rs`. -/
meta def lineCertB (blk : Nat) (oE fsE FE hcsE : Expr) (o : Offs) (fils : Array FilE)
    (filT : Array Expr) (F : Face) (hcs : Array HC) (hcEl : Array Expr) (m : Nat)
    (m' : Option Nat) : MetaM (Expr × List (Bool × Nat × Nat) × Expr) := do
  let t := trigOf m
  let tX := trigE t
  let mE := natE m
  let m'E := match m' with
    | some v => mkApp2 (mkConst ``Option.some [Level.zero]) tN (natE v)
    | none => mkApp (mkConst ``Option.none [Level.zero]) tN
  let wsA := F.wn.toArray
  let wsEl := wsA.map intE
  let wsT := tailsE tI wsEl
  let tHC := mkConst ``HC
  let hcT := tailsE tHC hcEl
  let params := #[oE, fsE, FE, mE, m'E, tX]
  let mut gs : List (List Nat) := []
  let mut gsX := mkApp (mkConst ``List.nil [Level.zero]) (tL tN)
  let mut gsElems : Array (Array Expr × Array Expr) := #[]
  let mut stepPf : Array (Expr × Expr × Expr × Expr) := #[]
  let mut recs : Array Expr := #[]
  let mut outs : Array (Bool × Nat × Nat) := #[]
  for i in [0:wsA.size] do
    let wn := wsA[i]!
    let ws := (wsA.extract (i + 1) wsA.size).toList
    let cx := cornerXYZ F m wn
    let (X, Y, Z, D) := cx.1
    let cxX := pairE (tP tN (tP tN (tP tN tN))) tB
      (pairE tN (tP tN (tP tN tN)) (natE X) (pairE tN (tP tN tN) (natE Y) (pairE tN tN (natE Z)
        (natE D)))) (boolE cx.2)
    let hv := helAt hcs[i]! t
    let hvX := q3E hv
    let rh : RC × Nat := match m', ws with
      | some m1, wn' :: _ => cellRC F m m1 wn wn' D
      | _, _ => (noRC, 0)
    let rcX := rcE rh.1
    let rhX := pairE (mkConst ``RC) tN rcX (natE rh.2)
    let (cpf, coX, co, gNew) ← cornerCertB blk oE fsE o fils filT X Y Z D hv hvX rh.1 rcX gs gsX
      gsElems
    let r : Bool × Nat × Nat := (co.ok && cx.2, co.e, Nat.add co.rem rh.2)
    let rX := bnnE r
    let newGsX := coX.getAppArgs[3]!
    let spf := mkAppN (mkConst ``lineStepB_of) (params ++ #[wsEl[i]!, wsT[i + 1]!, hcEl[i]!, gsX,
      natE X, natE Y, natE Z, natE D, boolE cx.2, rcX, natE rh.2, hvX, coX, rX,
      reflE (tP (tP tN (tP tN (tP tN tN))) tB) cxX, reflE (tP (mkConst ``RC) tN) rhX,
      reflE tQ3 hvX, cpf, reflE tBNN rX])
    stepPf := stepPf.push (gsX, rX, newGsX, spf)
    recs := recs.push rX
    outs := outs.push r
    gs := co.gs
    gsX := newGsX
    gsElems := gNew
  let recT := tailsE tBNN recs
  let mut lc := mkAppN (mkConst ``LCB.nil) (params ++ #[hcT[wsA.size]!, gsX])
  for j in [0:wsA.size] do
    let i := wsA.size - 1 - j
    let (gX, rX, g'X, spf) := stepPf[i]!
    lc := mkAppN (mkConst ``LCB.cons) (params ++ #[wsEl[i]!, wsT[i + 1]!, hcEl[i]!, hcT[i + 1]!,
      gX, rX, g'X, recT[i + 1]!, spf, lc])
  let pf := mkAppN (mkConst ``lineB_of) #[oE, fsE, FE, hcsE, mE, m'E, tX, wsT[0]!, recT[0]!,
    reflE (mkConst ``Trig) tX, reflE (tL tI) wsT[0]!, lc]
  return (pf, outs.toList, recT[0]!)

/-- A `CO prev cur` proof (one `Eq.refl true` leaf per cell). -/
meta def coCert (prev cur : Array Expr) : MetaM Expr := do
  unless prev.size == cur.size && prev.size > 0 do
    throwError "chunk_cert: lines of different lengths"
  let pT := tailsE tBNN prev
  let cT := tailsE tBNN cur
  let n := prev.size
  let mut pf := mkApp2 (mkConst ``CO.one) prev[n - 1]! cur[n - 1]!
  for j in [0:n - 1] do
    let i := n - 2 - j
    pf := mkAppN (mkConst ``CO.cons) #[prev[i]!, prev[i + 1]!, pT[i + 2]!, cur[i]!, cur[i + 1]!,
      cT[i + 2]!, reflE tB (mkConst ``Bool.true), pf]
  return pf

/-- **`chunk_cert hfils hface`**: prove `checkChunk o fs F ms = true` where `hfils : lit = fs`
(`lit` a constant whose body is a literal filament list), `hface : faceOK F = true`, `o` and
`F` constants with literal bodies, and `ms` a literal list or `(grid.drop k).take n` with a
literal `grid`. -/
syntax (name := chunkCertStx) "chunk_cert " ident ident (num)? : tactic

/-- The elaborator of `chunk_cert`. -/
@[tactic chunkCertStx] meta def evalChunkCert : Tactic := fun stx => do
  let blk := if stx[3].getNumArgs == 1 then stx[3][0].isNatLit?.getD 3 else 3
  let hfils ← realizeGlobalConstNoOverload stx[1]
  let hface ← realizeGlobalConstNoOverload stx[2]
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "chunk_cert: expected an equation"
  let (``checkChunk, #[oE, fsE, FE, msE]) := lhs.getAppFnArgs |
    throwError "chunk_cert: expected `checkChunk o fs F ms = true`"
  let hfTy ← inferType (mkConst hfils)
  let some (_, litE, fs2) := hfTy.eq? | throwError "chunk_cert: {hfils} is not an equation"
  unless ← isDefEq fs2 fsE do throwError "chunk_cert: {hfils} is not about {fsE}"
  -- the chunk list
  let (msLit, dtPf?) ← match msE.getAppFnArgs with
    | (``List.take, #[_, nE, dE]) =>
      let (``List.drop, #[_, kE, gE]) := dE.getAppFnArgs |
        throwError "chunk_cert: expected `(grid.drop k).take n`"
      let k ← readNat (← whnf kE)
      let n ← readNat (← whnf nE)
      let gB ← zetaAll (← bodyOf gE)
      let gEl ← listElems gB
      let gT ← listTails gB
      unless k < gEl.size do throwError "chunk_cert: chunk out of range"
      let avail := min n (gEl.size - k)
      let ys := gEl.extract k (k + avail)
      let yT := tailsE tN ys
      -- DT proof from the inside out
      let mut pf := if avail == n then mkApp2 (mkConst ``DT.done) tN gT[k + n]!
        else mkApp2 (mkConst ``DT.short) tN (natE (n - avail))
      for j in [0:avail] do
        let i := avail - 1 - j
        pf := mkAppN (mkConst ``DT.take) #[tN, ys[i]!, gT[k + i + 1]!,
          natE (n - 1 - i), yT[i + 1]!, pf]
      for j in [0:k] do
        let i := k - 1 - j
        pf := mkAppN (mkConst ``DT.drop) #[tN, gEl[i]!, gT[i + 1]!, natE (k - 1 - i),
          natE n, yT[0]!, pf]
      let hdt := mkApp (mkAppN (mkConst ``DT.sound) #[tN, gT[0]!, natE k, natE n,
        yT[0]!]) pf
      pure (yT[0]!, some hdt)
    | _ => pure (msE, none)
  let msEl ← listElems msLit
  let ms ← msEl.mapM fun e => readNat e
  unless ms.size ≥ 2 do throwError "chunk_cert: a chunk needs at least two lines"
  let o ← readOffs (← bodyOf oE)
  let litB ← bodyOf litE
  let fils ← (← listElems litB).mapM fun x => readFil x
  let filT ← listTails litB
  let F ← readFaceB (← bodyOf FE)
  let hcs := (faceHC F).toArray
  let hcEl := hcs.map hcE
  let tHC := mkConst ``HC
  let hcT := tailsE tHC hcEl
  let hcsE := hcT[0]!
  let wsEl := F.wn.toArray.map intE
  let wsT := tailsE tI wsEl
  -- hel coefficients
  let cty ← inferType (mkAppN (mkConst ``chunk_of) #[oE, litE, FE, natE ms[0]!, natE ms[1]!,
    (tailsE tN (msEl.extract 2 msEl.size))[0]!, wsT[0]!, hcsE])
  let hhTy := cty.bindingBody!.bindingBody!.bindingDomain!
  let fX := hhTy.getAppArgs[2]!
  let mut mc := mkApp3 (mkConst ``MC.nil) tI tHC fX
  for j in [0:wsEl.size] do
    let i := wsEl.size - 1 - j
    mc := mkAppN (mkConst ``MC.cons) #[tI, tHC, fX, wsEl[i]!, wsT[i + 1]!, hcEl[i]!, hcT[i + 1]!,
      reflE tHC hcEl[i]!, mc]
  -- lines
  let msT := tailsE tN (ms.map natE)
  let mut lines : Array (Expr × Array Expr) := #[]
  for i in [0:ms.size] do
    let m' := if i + 1 < ms.size then some ms[i + 1]! else none
    let (lpf, _, rsE) ← lineCertB blk oE litE FE hcsE o fils filT F hcs hcEl ms[i]! m'
    lines := lines.push (lpf, ← listElems rsE)
  let lineList (i : Nat) : Expr := (tailsE tBNN lines[i]!.2)[0]!
  -- CLines from the end
  let last := ms.size - 1
  let mut cl := mkAppN (mkConst ``CLines.last) #[oE, litE, FE, hcsE, lineList (last - 1),
    natE ms[last - 1]!, natE ms[last]!, lineList last, lines[last]!.1, reflE tB (mkConst ``Bool.true),
    ← coCert lines[last - 1]!.2 lines[last]!.2]
  for j in [0:last - 1] do
    let i := last - 1 - j
    cl := mkAppN (mkConst ``CLines.cons) #[oE, litE, FE, hcsE, lineList (i - 1), natE ms[i - 1]!,
      natE ms[i]!, natE ms[i + 1]!, msT[i + 2]!, lineList i, lines[i]!.1,
      reflE tB (mkConst ``Bool.true), ← coCert lines[i - 1]!.2 lines[i]!.2, cl]
  let pf := mkAppN (mkConst ``chunk_of) #[oE, litE, FE, natE ms[0]!, natE ms[1]!, msT[2]!, wsT[0]!,
    hcsE, lineList 0, reflE (tL tI) wsT[0]!, mc, mkConst hface, lines[0]!.1, cl]
  -- rewrite the filament data and the chunk list
  let motiveF := Expr.lam `x (tL (mkConst ``Fil))
    (← mkEq (mkAppN (mkConst ``checkChunk) #[oE, .bvar 0, FE, msLit]) (mkConst ``Bool.true))
    .default
  let pf := mkAppN (mkConst ``Eq.subst [Level.one]) #[tL (mkConst ``Fil), motiveF, litE, fsE,
    mkConst hfils, pf]
  let pf := match dtPf? with
    | some hdt =>
      let motiveM := Expr.lam `x (tL tN)
        (mkApp3 (mkConst ``Eq [Level.one]) tB (mkAppN (mkConst ``checkChunk) #[oE, fsE, FE, .bvar 0])
          (mkConst ``Bool.true)) .default
      mkAppN (mkConst ``Eq.subst [Level.one]) #[tL tN, motiveM, msLit, msE,
        mkApp4 (mkConst ``Eq.symm [Level.one]) (tL tN) msE msLit hdt, pf]
    | none => pf
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

/-- **Sanity** (rejected): a goal of the wrong shape is refused. -/
theorem chunkCert_reject_fixture : True := by
  fail_if_success (have : (1 : Nat) = 1 := by chunk_cert True.intro True.intro)
  trivial

end ChunkCert

end PlasmaLean.Design.PolygonCoil
