/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicCheck
public meta import Lean.Elab.Tactic.Basic
public meta import PlasmaLean.Design.PolygonCoilCubicCheck

/-!
# Per-segment certificates for the cubic grid lines (`line_cert`)

A grid-line check `lineOut4 o nS fs F mp m mn mn2 = data` evaluates, at each of the ≈ 25 corners
of the line, one vertex step (`vertStep`: `|A|²` and three Newton steps from the warm start) per
filament vertex, one Biot–Savart segment step (`segStep`) and one remainder step (`remStep`) per
segment, and a fixed final assembly (`cornerFinalV`), with the corner geometry (`cornerXYZ4`), the
remainder parameters (`remP4`), the `hel` value (`helAt`) and the remainder contributions
(`rwC`, `rtC`). This module certifies that evaluation step by step (SubsetSum pattern), one
certificate node per vertex, segment and corner, so that no recursion of the checker is left to
the kernel:

* `FV`/`AV`: the vertex results of a filament / of all filaments, one leaf
  `vertStep c v g = r` per vertex (cold starts: `coldStart c v = g` first);
* `SW`/`AW` (with the remainder fold) and `W`/`AW0` (corners without an attached cell): the
  segment walk, one leaf `segStep … acc s a b = acc'` (and `remStep … rm (s, a, b) = rm'`) per
  segment, with the closing segment back to the first vertex;
* `corner_some`, `corner_none`: the corner output `cornerEval4 … = ⟨ok, fin, rw, rt, gs'⟩` from
  these certificates and one leaf for `cornerFinalV`;
* `LC`: the corners along the line, through `lineStep` (one iteration of `lineGo4`), with leaves
  for `cornerXYZ4`, `helAt`, `remP4`, `rwC`, `rtC`; `MC` for the `hel` coefficients `faceHC4`.

The leaves are single non-recursive arithmetic functions applied to literal values (the only
bounded iterations inside a leaf are the fixed Newton counts of `coldStart` and `sqrtUpFrom`).
Soundness theorems (`FV.sound`, …, `line_of`) are proved once by induction. The `meta` builder
`line_cert` computes every value by running the checker's own functions (untrusted; the kernel
re-checks each leaf) and assembles the term.
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

namespace LineCert

/-! ## Vertex results -/

/-- **Vertex results of one filament**: `FV c vs gs rs gs'` says `filVerts c vs gs = rs` and
`rs.map VR.g = gs'`; one leaf per vertex. -/
inductive FV (c : CD) : List Vt → List Nat → List VR → List Nat → Prop where
  /-- no vertex left -/
  | nil (gs : List Nat) : FV c [] gs [] []
  /-- a vertex with a warm start `g` -/
  | warm (v : Vt) (vs : List Vt) (g : Nat) (gs : List Nat) (r : VR) (rs : List VR)
      (gs' : List Nat) :
      vertStep c v g = r → FV c vs gs rs gs' → FV c (v :: vs) (g :: gs) (r :: rs) (r.g :: gs')
  /-- a vertex with a cold start -/
  | cold (v : Vt) (vs : List Vt) (g : Nat) (r : VR) (rs : List VR) (gs' : List Nat) :
      coldStart c v = g → vertStep c v g = r → FV c vs [] rs gs' →
      FV c (v :: vs) [] (r :: rs) (r.g :: gs')

theorem FV.sound {c : CD} {vs : List Vt} {gs : List Nat} {rs : List VR} {gs' : List Nat}
    (h : FV c vs gs rs gs') : filVerts c vs gs = rs ∧ rs.map VR.g = gs' := by
  induction h with
  | nil gs => cases gs <;> simp [filVerts]
  | warm v vs g gs r rs gs' h1 _ ih => simp [filVerts, h1, ih.1, ih.2]
  | cold v vs g r rs gs' h0 h1 _ ih => simp [filVerts, h0, h1, ih.1, ih.2]

/-- **Vertex results of all filaments** (`allVerts`), with the new warm starts. -/
inductive AV (c : CD) : List Fil → List (List Nat) → List (List VR) → List (List Nat) → Prop where
  /-- no filament left -/
  | nil (gs : List (List Nat)) : AV c [] gs [] []
  /-- a filament with warm starts -/
  | warm (f : Fil) (fs : List Fil) (g : List Nat) (gs : List (List Nat)) (r : List VR)
      (rs : List (List VR)) (g' : List Nat) (gs' : List (List Nat)) :
      FV c f.vts g r g' → AV c fs gs rs gs' → AV c (f :: fs) (g :: gs) (r :: rs) (g' :: gs')
  /-- a filament with cold starts -/
  | cold (f : Fil) (fs : List Fil) (r : List VR) (rs : List (List VR)) (g' : List Nat)
      (gs' : List (List Nat)) :
      FV c f.vts [] r g' → AV c fs [] rs gs' → AV c (f :: fs) [] (r :: rs) (g' :: gs')

theorem AV.sound {c : CD} {fs : List Fil} {gs : List (List Nat)} {rs : List (List VR)}
    {gs' : List (List Nat)} (h : AV c fs gs rs gs') :
    allVerts c fs gs = rs ∧ rs.map (fun l => l.map VR.g) = gs' := by
  induction h with
  | nil gs => cases gs <;> simp [allVerts]
  | warm f fs g gs r rs g' gs' h1 _ ih =>
    have := h1.sound; simp [allVerts, this.1, this.2, ih.1, ih.2]
  | cold f fs r rs g' gs' h1 _ ih =>
    have := h1.sound; simp [allVerts, this.1, this.2, ih.1, ih.2]

/-! ## Segment walks -/

/-- State of the remainder fold. -/
abbrev RS := Nat × Nat × Bool

/-- **Segment walk of one filament with the remainder fold** (`filWalkAux` and the `remStep`
fold over the same segment triples), one pair of leaves per segment; `first` closes the loop. -/
inductive SW (D2 D3S : Nat) (P : RemP) (first : VR) :
    Acc → RS → List Seg → List VR → Acc → RS → Prop where
  /-- a segment `a → b` followed by more segments -/
  | step (acc : Acc) (rm : RS) (s : Seg) (ss : List Seg) (a b : VR) (rs : List VR) (acc' : Acc)
      (rm' : RS) (out : Acc) (orm : RS) :
      segStep D2 D3S noRC acc s a b = acc' → remStep D2 P rm (s, a, b) = rm' →
      SW D2 D3S P first acc' rm' ss (b :: rs) out orm →
      SW D2 D3S P first acc rm (s :: ss) (a :: b :: rs) out orm
  /-- two segments `a → b → c` as one leaf pair, followed by more segments -/
  | step2 (acc : Acc) (rm : RS) (s₁ s₂ : Seg) (ss : List Seg) (a b c : VR) (rs : List VR)
      (acc' : Acc) (rm' : RS) (out : Acc) (orm : RS) :
      segStep D2 D3S noRC (segStep D2 D3S noRC acc s₁ a b) s₂ b c = acc' →
      remStep D2 P (remStep D2 P rm (s₁, a, b)) (s₂, b, c) = rm' →
      SW D2 D3S P first acc' rm' ss (c :: rs) out orm →
      SW D2 D3S P first acc rm (s₁ :: s₂ :: ss) (a :: b :: c :: rs) out orm
  /-- three segments `a → b → c → d` as one leaf pair, followed by more segments -/
  | step3 (acc : Acc) (rm : RS) (s₁ s₂ s₃ : Seg) (ss : List Seg) (a b c d : VR) (rs : List VR)
      (acc' : Acc) (rm' : RS) (out : Acc) (orm : RS) :
      segStep D2 D3S noRC (segStep D2 D3S noRC (segStep D2 D3S noRC acc s₁ a b) s₂ b c) s₃ c d =
        acc' →
      remStep D2 P (remStep D2 P (remStep D2 P rm (s₁, a, b)) (s₂, b, c)) (s₃, c, d) = rm' →
      SW D2 D3S P first acc' rm' ss (d :: rs) out orm →
      SW D2 D3S P first acc rm (s₁ :: s₂ :: s₃ :: ss) (a :: b :: c :: d :: rs) out orm
  /-- the closing segment `a → first` -/
  | last (acc : Acc) (rm : RS) (s : Seg) (a : VR) (out : Acc) (orm : RS) :
      segStep D2 D3S noRC acc s a first = out → remStep D2 P rm (s, a, first) = orm →
      SW D2 D3S P first acc rm [s] [a] out orm

theorem SW.sound {D2 D3S : Nat} {P : RemP} {first : VR} {acc : Acc} {rm : RS} {ss : List Seg}
    {L : List VR} {out : Acc} {orm : RS} (h : SW D2 D3S P first acc rm ss L out orm) :
    filWalkAux D2 D3S noRC first acc ss L = out ∧
      (List.zip ss (List.zip L (L.tail ++ [first]))).foldl (remStep D2 P) rm = orm := by
  induction h with
  | step acc rm s ss a b rs acc' rm' out orm h1 h2 _ ih =>
    refine ⟨?_, ?_⟩
    · simp only [filWalkAux, h1]; exact ih.1
    · have := ih.2
      simp only [List.tail_cons] at this
      simp [h2, this]
  | step2 acc rm s₁ s₂ ss a b c rs acc' rm' out orm h1 h2 _ ih =>
    refine ⟨?_, ?_⟩
    · simp only [filWalkAux, h1]; exact ih.1
    · have := ih.2
      simp only [List.tail_cons] at this
      simp [h2, this]
  | step3 acc rm s₁ s₂ s₃ ss a b c d rs acc' rm' out orm h1 h2 _ ih =>
    refine ⟨?_, ?_⟩
    · simp only [filWalkAux, h1]; exact ih.1
    · have := ih.2
      simp only [List.tail_cons] at this
      simp [h2, this]
  | last acc rm s a out orm h1 h2 => simp [filWalkAux, h1, h2]

/-- **Segment walk of one filament without remainder** (corners without an attached cell). -/
inductive W (D2 D3S : Nat) (first : VR) : Acc → List Seg → List VR → Acc → Prop where
  /-- a segment `a → b` followed by more segments -/
  | step (acc : Acc) (s : Seg) (ss : List Seg) (a b : VR) (rs : List VR) (acc' out : Acc) :
      segStep D2 D3S noRC acc s a b = acc' → W D2 D3S first acc' ss (b :: rs) out →
      W D2 D3S first acc (s :: ss) (a :: b :: rs) out
  /-- two segments as one leaf, followed by more segments -/
  | step2 (acc : Acc) (s₁ s₂ : Seg) (ss : List Seg) (a b c : VR) (rs : List VR) (acc' out : Acc) :
      segStep D2 D3S noRC (segStep D2 D3S noRC acc s₁ a b) s₂ b c = acc' →
      W D2 D3S first acc' ss (c :: rs) out →
      W D2 D3S first acc (s₁ :: s₂ :: ss) (a :: b :: c :: rs) out
  /-- three segments as one leaf, followed by more segments -/
  | step3 (acc : Acc) (s₁ s₂ s₃ : Seg) (ss : List Seg) (a b c d : VR) (rs : List VR)
      (acc' out : Acc) :
      segStep D2 D3S noRC (segStep D2 D3S noRC (segStep D2 D3S noRC acc s₁ a b) s₂ b c) s₃ c d =
        acc' →
      W D2 D3S first acc' ss (d :: rs) out →
      W D2 D3S first acc (s₁ :: s₂ :: s₃ :: ss) (a :: b :: c :: d :: rs) out
  /-- the closing segment `a → first` -/
  | last (acc : Acc) (s : Seg) (a : VR) (out : Acc) :
      segStep D2 D3S noRC acc s a first = out → W D2 D3S first acc [s] [a] out

theorem W.sound {D2 D3S : Nat} {first : VR} {acc : Acc} {ss : List Seg} {L : List VR} {out : Acc}
    (h : W D2 D3S first acc ss L out) : filWalkAux D2 D3S noRC first acc ss L = out := by
  induction h with
  | step acc s ss a b rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | step2 acc s₁ s₂ ss a b c rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | step3 acc s₁ s₂ s₃ ss a b c d rs acc' out h1 _ ih => simp only [filWalkAux, h1]; exact ih
  | last acc s a out h1 => simp [filWalkAux, h1]

/-- **Walk of all filaments with the remainder fold** (`allWalk` and the fold over
`triples4`). -/
inductive AW (D2 D3S : Nat) (P : RemP) : Acc → RS → List Fil → List (List VR) → Acc → RS → Prop
    where
  /-- no filament left -/
  | nil (acc : Acc) (rm : RS) : AW D2 D3S P acc rm [] [] acc rm
  /-- one filament, then the others -/
  | cons (acc : Acc) (rm : RS) (f : Fil) (fs : List Fil) (v : VR) (vv : List VR)
      (vs : List (List VR)) (acc' : Acc) (rm' : RS) (out : Acc) (orm : RS) :
      SW D2 D3S P v acc rm f.sgs (v :: vv) acc' rm' → AW D2 D3S P acc' rm' fs vs out orm →
      AW D2 D3S P acc rm (f :: fs) ((v :: vv) :: vs) out orm

theorem AW.sound {D2 D3S : Nat} {P : RemP} {acc : Acc} {rm : RS} {fs : List Fil}
    {vs : List (List VR)} {out : Acc} {orm : RS} (h : AW D2 D3S P acc rm fs vs out orm) :
    allWalk D2 D3S noRC acc fs vs = out ∧ (triples4 fs vs).foldl (remStep D2 P) rm = orm := by
  induction h with
  | nil acc rm => simp [allWalk, triples4]
  | cons acc rm f fs v vv vs acc' rm' out orm h1 _ ih =>
    have h1s := h1.sound
    simp only [List.tail_cons] at h1s
    refine ⟨?_, ?_⟩
    · simp only [allWalk, filWalk, h1s.1]; exact ih.1
    · simp only [triples4, List.zip_cons_cons, List.flatMap_cons, List.foldl_append, rot1] at ih ⊢
      rw [h1s.2]; exact ih.2

/-- **Walk of all filaments without remainder**. -/
inductive AW0 (D2 D3S : Nat) : Acc → List Fil → List (List VR) → Acc → Prop where
  /-- no filament left -/
  | nil (acc : Acc) : AW0 D2 D3S acc [] [] acc
  /-- one filament, then the others -/
  | cons (acc : Acc) (f : Fil) (fs : List Fil) (v : VR) (vv : List VR) (vs : List (List VR))
      (acc' out : Acc) :
      W D2 D3S v acc f.sgs (v :: vv) acc' → AW0 D2 D3S acc' fs vs out →
      AW0 D2 D3S acc (f :: fs) ((v :: vv) :: vs) out

theorem AW0.sound {D2 D3S : Nat} {acc : Acc} {fs : List Fil} {vs : List (List VR)} {out : Acc}
    (h : AW0 D2 D3S acc fs vs out) : allWalk D2 D3S noRC acc fs vs = out := by
  induction h with
  | nil acc => simp [allWalk]
  | cons acc f fs v vv vs acc' out h1 _ ih => simp only [allWalk, filWalk, h1.sound]; exact ih

/-! ## Corners -/

/-- The corner data `CD` of `cornerEval4`. -/
def cdOf (Xt Yt Zt D : Nat) : CD :=
  ⟨D, Nat.mul D D, Nat.mul Xt two32, Nat.mul Yt two32, Nat.mul Zt two32,
    Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32))) (sq (Nat.mul Zt two32)),
    Nat.mul D two32⟩

/-- Initial state of the remainder fold of `cornerEval4`. -/
def rmInit (P : RemP) : RS :=
  (0, 0, (Nat.ble P.rcW.rBD P.rcW.s0l && Nat.ble P.rcT.rBD P.rcT.s0l) && Nat.ble P.nt (sq P.rcT.rBD))

/-- Initial accumulator of `cornerEval4`. -/
def accInit : Acc := ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩

/-- **A corner with an attached cell** from the vertex and walk certificates. -/
theorem corner_some (o : Offs) (nS : Nat) (fs : List Fil) (Xt Yt Zt D : Nat) (h : QQ × QQ × QQ)
    (P : RemP) (gs : List (List Nat)) (c : CD) (D2 D3S : Nat) (vs : List (List VR))
    (gs' : List (List Nat)) (rm0 : RS) (acc : Acc) (rm : RS) (fin : FinV) (ok : Bool)
    (hc : cdOf Xt Yt Zt D = c) (hD2 : Nat.mul D D = D2)
    (hD3 : Nat.mul (Nat.mul D2 D) two136 = D3S) (hr0 : rmInit P = rm0)
    (hv : AV c fs gs vs gs') (hw : AW D2 D3S P accInit rm0 fs vs acc rm)
    (hf : cornerFinalV o nS Xt Yt Zt D c.lam acc h = fin)
    (hok : (((acc.ok && fin.ok) && Nat.ble (Nat.mul 1000 KT) c.lam) && rm.2.2) = ok) :
    cornerEval4 o nS fs Xt Yt Zt D h (some P) gs = ⟨ok, fin, rm.1, rm.2.1, gs'⟩ := by
  subst hc hD2 hD3 hr0
  obtain ⟨hv1, hv2⟩ := hv.sound
  obtain ⟨hw1, hw2⟩ := hw.sound
  simp only [cornerEval4]
  simp only [cdOf, accInit, rmInit] at hv1 hw1 hw2 hf hok
  rw [hv1, hw1, hw2, hf, hok, hv2]

/-- **A corner without an attached cell**. -/
theorem corner_none (o : Offs) (nS : Nat) (fs : List Fil) (Xt Yt Zt D : Nat) (h : QQ × QQ × QQ)
    (gs : List (List Nat)) (c : CD) (D2 D3S : Nat) (vs : List (List VR))
    (gs' : List (List Nat)) (acc : Acc) (fin : FinV) (ok : Bool)
    (hc : cdOf Xt Yt Zt D = c) (hD2 : Nat.mul D D = D2)
    (hD3 : Nat.mul (Nat.mul D2 D) two136 = D3S)
    (hv : AV c fs gs vs gs') (hw : AW0 D2 D3S accInit fs vs acc)
    (hf : cornerFinalV o nS Xt Yt Zt D c.lam acc h = fin)
    (hok : (((acc.ok && fin.ok) && Nat.ble (Nat.mul 1000 KT) c.lam) && true) = ok) :
    cornerEval4 o nS fs Xt Yt Zt D h none gs = ⟨ok, fin, 0, 0, gs'⟩ := by
  subst hc hD2 hD3
  obtain ⟨hv1, hv2⟩ := hv.sound
  have hw1 := hw.sound
  simp only [cornerEval4]
  simp only [cdOf, accInit] at hv1 hw1 hf hok
  rw [hv1, hw1, hf, hok, hv2]

/-! ## Lines -/

/-- The cell window of `lineGo4`. -/
def winOf (prev : Option Int) (ws : List Int) : Option (Int × Int × Int) :=
  match prev, ws with
  | some wp, wn1 :: wn2 :: _ => some (wp, wn1, wn2)
  | _, _ => none

/-- One iteration of `lineGo4`: the corner record and the new warm starts. -/
def lineStep (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int) (t : Trig)
    (prev : Option Int) (wn : Int) (ws : List Int) (hc : HC) (gs : List (List Nat)) :
    CRec × List (List Nat) :=
  let cx := cornerXYZ4 F m wn
  let xyz := cx.1
  let win := winOf prev ws
  let P : Option RemP := match win with
    | some w => some (remP4 F mp m mn2 w.1 wn w.2.1 w.2.2 xyz.2.2.2)
    | none => none
  let co := cornerEval4 o nS fs xyz.1 xyz.2.1 xyz.2.2.1 xyz.2.2.2 (helAt hc t) P gs
  let rr : Nat × Nat := match win with
    | some w => (rwC F w.1 wn w.2.1 w.2.2 co.rw, rtC F mp m mn mn2 co.rt)
    | none => (0, 0)
  (⟨co.ok && cx.2, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez, co.fin.rho, rr.1, rr.2⟩, co.gs)

theorem lineGo4_cons (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int)
    (t : Trig) (prev : Option Int) (wn : Int) (ws : List Int) (hc : HC) (hcs : List HC)
    (gs : List (List Nat)) :
    lineGo4 o nS fs F mp m mn mn2 t prev (wn :: ws) (hc :: hcs) gs =
      (lineStep o nS fs F mp m mn mn2 t prev wn ws hc gs).1 ::
        lineGo4 o nS fs F mp m mn mn2 t (some wn) ws hcs
          (lineStep o nS fs F mp m mn mn2 t prev wn ws hc gs).2 := by
  rcases prev with _ | wp <;> rcases ws with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp only [lineGo4, lineStep, winOf]

/-- **The corners of a line**: `LC … prev ws hcs gs rs` says `lineGo4 … prev ws hcs gs = rs`;
one node per corner. -/
inductive LC (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int) (t : Trig) :
    Option Int → List Int → List HC → List (List Nat) → List CRec → Prop where
  /-- end of the `w`-grid -/
  | nil (prev : Option Int) (hcs : List HC) (gs : List (List Nat)) :
      LC o nS fs F mp m mn mn2 t prev [] hcs gs []
  /-- one corner, then the rest of the line -/
  | cons (prev : Option Int) (wn : Int) (ws : List Int) (hc : HC) (hcs : List HC)
      (gs : List (List Nat)) (r : CRec) (gs' : List (List Nat)) (rs : List CRec) :
      lineStep o nS fs F mp m mn mn2 t prev wn ws hc gs = (r, gs') →
      LC o nS fs F mp m mn mn2 t (some wn) ws hcs gs' rs →
      LC o nS fs F mp m mn mn2 t prev (wn :: ws) (hc :: hcs) gs (r :: rs)

theorem LC.sound {o : Offs} {nS : Nat} {fs : List Fil} {F : Face4} {mp m mn mn2 : Int} {t : Trig}
    {prev : Option Int} {ws : List Int} {hcs : List HC} {gs : List (List Nat)} {rs : List CRec}
    (h : LC o nS fs F mp m mn mn2 t prev ws hcs gs rs) :
    lineGo4 o nS fs F mp m mn mn2 t prev ws hcs gs = rs := by
  induction h with
  | nil prev hcs gs => rcases prev with _ | _ <;> rcases hcs with _ | _ <;> simp [lineGo4]
  | cons prev wn ws hc hcs gs r gs' rs h1 _ ih => rw [lineGo4_cons, h1]; exact congrArg _ ih

/-- **A corner step with an attached cell.** -/
theorem lineStep_some (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int)
    (t : Trig) (prev : Option Int) (wn : Int) (ws : List Int) (hc : HC) (gs : List (List Nat))
    (wp wn1 wn2 : Int) (X Y Z D : Nat) (okx : Bool) (hv : QQ × QQ × QQ) (P : RemP) (co : Corner4)
    (rw rt : Nat) (r : CRec)
    (hwin : winOf prev ws = some (wp, wn1, wn2))
    (hcx : cornerXYZ4 F m wn = ((X, Y, Z, D), okx)) (hh : helAt hc t = hv)
    (hP : remP4 F mp m mn2 wp wn wn1 wn2 D = P)
    (hco : cornerEval4 o nS fs X Y Z D hv (some P) gs = co)
    (hrw : rwC F wp wn wn1 wn2 co.rw = rw) (hrt : rtC F mp m mn mn2 co.rt = rt)
    (hr : (⟨co.ok && okx, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez, co.fin.rho, rw, rt⟩ : CRec)
      = r) :
    lineStep o nS fs F mp m mn mn2 t prev wn ws hc gs = (r, co.gs) := by
  simp only [lineStep, hwin, hcx, hh, hP, hco, hrw, hrt, hr]

/-- **A corner step without an attached cell.** -/
theorem lineStep_none (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int)
    (t : Trig) (prev : Option Int) (wn : Int) (ws : List Int) (hc : HC) (gs : List (List Nat))
    (X Y Z D : Nat) (okx : Bool) (hv : QQ × QQ × QQ) (co : Corner4) (r : CRec)
    (hwin : winOf prev ws = none)
    (hcx : cornerXYZ4 F m wn = ((X, Y, Z, D), okx)) (hh : helAt hc t = hv)
    (hco : cornerEval4 o nS fs X Y Z D hv none gs = co)
    (hr : (⟨co.ok && okx, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez, co.fin.rho, 0, 0⟩ : CRec)
      = r) :
    lineStep o nS fs F mp m mn mn2 t prev wn ws hc gs = (r, co.gs) := by
  simp only [lineStep, hwin, hcx, hh, hco, hr]

/-- **A list map, one leaf per element.** -/
inductive MC {α β : Type} (f : α → β) : List α → List β → Prop where
  /-- empty list -/
  | nil : MC f [] []
  /-- one element, then the rest -/
  | cons (x : α) (xs : List α) (y : β) (ys : List β) : f x = y → MC f xs ys → MC f (x :: xs) (y :: ys)

theorem MC.sound {α β : Type} {f : α → β} {xs : List α} {ys : List β} (h : MC f xs ys) :
    xs.map f = ys := by
  induction h with
  | nil => rfl
  | cons x xs y ys h1 _ ih => simp [h1, ih]

/-- **A grid line** from its corner certificates. -/
theorem line_of (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int) (t : Trig)
    (ws : List Int) (hcs : List HC) (rs : List CRec) (ht : trigOf4 m = t) (hw : F.wn = ws)
    (hh : MC (fun wn => let rz := faceRZ4 F wn; helCoef rz.1 rz.2) ws hcs)
    (h : LC o nS fs F mp m mn mn2 t none ws hcs [] rs) :
    lineOut4 o nS fs F mp m mn mn2 = rs := by
  have h2 : faceHC4 F = hcs := by rw [faceHC4, hw]; exact hh.sound
  simp only [lineOut4, ht, hw, h2]
  exact h.sound


/-! ## The builder (`meta`, untrusted) -/

open Lean Meta Elab Tactic

/-- A natural number literal. -/
meta def natE (n : Nat) : Expr := mkRawNatLit n

/-- An integer value in normal form. -/
meta def intE (i : Int) : Expr :=
  if i ≥ 0 then mkApp (mkConst ``Int.ofNat) (mkRawNatLit i.toNat)
  else mkApp (mkConst ``Int.negSucc) (mkRawNatLit (-i - 1).toNat)

/-- A Boolean value. -/
meta def boolE (b : Bool) : Expr := if b then mkConst ``Bool.true else mkConst ``Bool.false

/-- `ℕ`, `ℤ`, `Bool`. -/
meta def tN : Expr := mkConst ``Nat
/-- `ℤ`. -/
meta def tI : Expr := mkConst ``Int
/-- `Bool`. -/
meta def tB : Expr := mkConst ``Bool

/-- The product type `α × β`. -/
meta def tP (α β : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) α β

/-- A pair. -/
meta def pairE (α β a b : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b

/-- `List α`. -/
meta def tL (α : Expr) : Expr := mkApp (mkConst ``List [Level.zero]) α

/-- The list of `xs` with all its tails (`tails[i]` starts at `xs[i]`, `tails[n] = []`). -/
meta def tailsE (α : Expr) (xs : Array Expr) : Array Expr := Id.run do
  let mut out := Array.replicate (xs.size + 1) (mkApp (mkConst ``List.nil [Level.zero]) α)
  for j in [0:xs.size] do
    let i := xs.size - 1 - j
    out := out.set! i (mkApp3 (mkConst ``List.cons [Level.zero]) α xs[i]! out[i + 1]!)
  return out

/-- `Eq.refl v` at a type in `Type`. -/
meta def reflE (α v : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) α v

/-- `ℕ × Bool`. -/
meta def tNB : Expr := tP tN tB

/-- The type of the remainder state. -/
meta def tRS : Expr := tP tN tNB

/-- `Prod.mk ℕ (ℕ × Bool)` (shared head). -/
meta def pairRS : Expr := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) tN tNB

/-- `Prod.mk ℕ Bool` (shared head). -/
meta def pairNB : Expr := mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) tN tB

/-- `true` (shared). -/
meta def trueE : Expr := mkConst ``Bool.true

/-- `false` (shared). -/
meta def falseE : Expr := mkConst ``Bool.false

/-- A remainder state. -/
meta def rsE (r : Nat × Nat × Bool) : Expr :=
  mkApp2 pairRS (natE r.1) (mkApp2 pairNB (natE r.2.1) (if r.2.2 then trueE else falseE))

/-- `@Eq.refl α` (a shared head for the leaves at type `α`). -/
meta def reflH (α : Expr) : Expr := mkApp (mkConst ``Eq.refl [Level.one]) α

/-- `VR.mk` (shared head). -/
meta def vrMk : Expr := mkConst ``VR.mk

/-- `Acc.mk` (shared head). -/
meta def accMk : Expr := mkConst ``Acc.mk

/-- A `QQ` value. -/
meta def qqE (q : QQ) : Expr := mkApp2 (mkConst ``QQ.mk) (intE q.num) (natE q.den)

/-- A `VR` value. -/
meta def vrE (v : VR) (gE : Expr) : Expr :=
  mkApp4 vrMk (natE v.n) (natE v.al) (if v.ok then trueE else falseE) gE

/-- An `Acc` value. -/
meta def accE (a : Acc) : Expr :=
  mkAppN accMk #[natE a.sx, natE a.sy, natE a.sz, natE a.tx, natE a.ty, natE a.tz,
    natE a.sf, natE a.rem, if a.ok then trueE else falseE]


/-- A `FinV` value. -/
meta def finE (f : FinV) : Expr :=
  mkAppN (mkConst ``FinV.mk) #[boolE f.ok, natE f.e, intE f.ex, intE f.ey, intE f.ez, natE f.rho]

/-- A `CRec` value. -/
meta def crecE (r : CRec) : Expr :=
  mkAppN (mkConst ``CRec.mk) #[boolE r.ok, natE r.e, intE r.ex, intE r.ey, intE r.ez, natE r.rho,
    natE r.rw, natE r.rt]

/-- An `RC` value. -/
meta def rcE (r : RC) : Expr :=
  mkAppN (mkConst ``RC.mk) #[boolE r.doRem, natE r.s0l, natE r.rBD, natE r.lam2, natE r.K1,
    natE r.K2, natE r.K3, natE r.Cbn]

/-- A `RemP` value. -/
meta def rempE (P : RemP) : Expr :=
  mkAppN (mkConst ``RemP.mk) #[rcE P.rcW, rcE P.rcT, natE P.w6, natE P.t6, natE P.t4, natE P.t2,
    natE P.lam2, natE P.nt]

/-- A `CD` value. -/
meta def cdE (c : CD) : Expr :=
  mkAppN (mkConst ``CD.mk) #[natE c.D, natE c.D2, natE c.Xs, natE c.Ys, natE c.Zs, natE c.XX,
    natE c.lam]

/-- An `HC` value. -/
meta def hcE (h : HC) : Expr :=
  mkAppN (mkConst ``HC.mk) #[qqE h.A, qqE h.B, qqE h.G, qqE h.Dd, qqE h.E, qqE h.F]

/-- A `Trig` value. -/
meta def trigE (t : Trig) : Expr :=
  mkAppN (mkConst ``Trig.mk) #[qqE t.c, qqE t.s, qqE t.c3, qqE t.s3, qqE t.s2, qqE t.c2]

/-- The type `QQ × QQ × QQ`. -/
meta def tQ3 : Expr := tP (mkConst ``QQ) (tP (mkConst ``QQ) (mkConst ``QQ))

/-- A `QQ × QQ × QQ` value. -/
meta def q3E (h : QQ × QQ × QQ) : Expr :=
  pairE (mkConst ``QQ) (tP (mkConst ``QQ) (mkConst ``QQ)) (qqE h.1)
    (pairE (mkConst ``QQ) (mkConst ``QQ) (qqE h.2.1) (qqE h.2.2))

/-- A natural number read from a literal or numeral. -/
meta partial def readNat (e : Expr) : MetaM Nat := do
  match e.consumeMData with
  | .lit (.natVal n) => return n
  | e' =>
    match e'.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => readNat n
    | _ => throwError "line_cert: not a natural number literal{indentExpr e}"

/-- An integer read from a numeral or normal form. -/
meta partial def readInt (e : Expr) : MetaM Int := do
  match e.consumeMData.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => return (← readNat n)
  | (``Int.ofNat, #[n]) => return (← readNat n)
  | (``Int.negSucc, #[n]) => return -((← readNat n) : Int) - 1
  | (``Neg.neg, #[_, _, x]) => return -(← readInt x)
  | (``Int.neg, #[x]) => return -(← readInt x)
  | _ => throwError "line_cert: not an integer literal{indentExpr e}"

/-- The elements of a list literal. -/
meta partial def listElems (e : Expr) : MetaM (Array Expr) := do
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => return #[]
  | (``List.cons, #[_, h, t]) => return #[h] ++ (← listElems t)
  | _ => throwError "line_cert: not a list literal{indentExpr e}"

/-- The tails of a list literal (`tails[i]` starts at the `i`-th element). -/
meta partial def listTails (e : Expr) : MetaM (Array Expr) := do
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => return #[e]
  | (``List.cons, #[_, _, t]) => return #[e] ++ (← listTails t)
  | _ => throwError "line_cert: not a list literal{indentExpr e}"

/-- The fields of a structure literal. -/
meta def fieldsOf (e : Expr) (n : Nat) : MetaM (Array Expr) := do
  let args := e.consumeMData.getAppArgs
  unless args.size == n do throwError "line_cert: unexpected structure literal{indentExpr e}"
  return args

/-- The value of a definition (its literal body). -/
meta def bodyOf (e : Expr) : MetaM Expr := do
  match e.consumeMData with
  | .const c _ =>
    let some v := (← getConstInfo c).value? | throwError "line_cert: no value for {c}"
    return v
  | e' => return e'

/-- A filament literal: its expression, its vertex and segment list expressions (with tails),
and its native value. -/
meta structure FilE where
  /-- the filament expression -/
  e : Expr
  /-- vertex expressions -/
  vts : Array Expr
  /-- tails of the vertex list -/
  vtsT : Array Expr
  /-- segment expressions -/
  sgs : Array Expr
  /-- tails of the segment list -/
  sgsT : Array Expr
  /-- native value -/
  val : Fil

/-- Default vertex (for array indexing in `meta` code). -/
meta instance : Inhabited Vt := ⟨⟨0, 0, 0, 0⟩⟩
/-- Default segment. -/
meta instance : Inhabited Seg := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩
/-- Default vertex result. -/
meta instance : Inhabited VR := ⟨⟨0, 0, false, 0⟩⟩
/-- Default accumulator. -/
meta instance : Inhabited Acc := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, false⟩⟩
/-- Default rational. -/
meta instance : Inhabited QQ := ⟨⟨0, 1⟩⟩
/-- Default `hel` coefficients. -/
meta instance : Inhabited HC := ⟨⟨default, default, default, default, default, default⟩⟩
/-- Default filament literal. -/
meta instance : Inhabited FilE := ⟨⟨default, #[], #[], #[], #[], ⟨[], []⟩⟩⟩

/-- Read a filament literal. -/
meta def readFil (e : Expr) : MetaM FilE := do
  let a ← fieldsOf e 2
  let vts ← listElems a[0]!
  let sgs ← listElems a[1]!
  let vtv ← vts.mapM fun v => do
    let f ← fieldsOf v 4
    return (⟨← readNat f[0]!, ← readNat f[1]!, ← readNat f[2]!, ← readNat f[3]!⟩ : Vt)
  let sgv ← sgs.mapM fun s => do
    let f ← fieldsOf s 8
    return (⟨← readNat f[0]!, ← readNat f[1]!, ← readNat f[2]!, ← readNat f[3]!, ← readNat f[4]!,
      ← readNat f[5]!, ← readNat f[6]!, ← readNat f[7]!⟩ : Seg)
  let vtsT ← listTails a[0]!
  let sgsT ← listTails a[1]!
  return ⟨e, vts, vtsT, sgs, sgsT, ⟨vtv.toList, sgv.toList⟩⟩

/-- Read an `Offs` literal. -/
meta def readOffs (e : Expr) : MetaM Offs := do
  let f ← fieldsOf e 8
  return ⟨← readNat f[0]!, ← readNat f[1]!, ← readNat f[2]!, ← readNat f[3]!, ← readNat f[4]!,
    ← readNat f[5]!, ← readNat f[6]!, ← readNat f[7]!⟩

/-- Read a `Face4` literal. -/
meta def readFace (e : Expr) : MetaM Face4 := do
  let f ← fieldsOf e 7
  return ⟨← readNat f[0]!, ← readNat f[1]!, (← (← listElems f[2]!).mapM readInt).toList,
    ← readNat f[3]!, ← readNat f[4]!, ← readNat f[5]!, ← readNat f[6]!⟩

/-- `Option (ℤ × ℤ × ℤ)`-free window of `lineGo4` (native mirror of `winOf`). -/
meta def winN (prev : Option Int) (ws : List Int) : Option (Int × Int × Int) :=
  match prev, ws with
  | some wp, wn1 :: wn2 :: _ => some (wp, wn1, wn2)
  | _, _ => none

/-- Certificates of one corner: the expressions of the vertex results, the walk, and the proof of
`cornerEval4 … = ⟨ok, fin, rw, rt, gs'⟩`; returns `(proof, Corner4 expression, native warm
starts, native corner)`. -/
meta def cornerCert (blk : Nat) (oE nSE fsE : Expr) (o : Offs) (nS : Nat) (fils : Array FilE) (filT : Array Expr)
    (X Y Z D : Nat) (hv : QQ × QQ × QQ) (hvE : Expr) (P : Option RemP) (PE : Expr)
    (gs : List (List Nat)) (gsE : Expr) (gsElems : Array (Array Expr × Array Expr)) :
    MetaM (Expr × Expr × List (List Nat) × Array (Array Expr × Array Expr) × Corner4) := do
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
  -- vertex results
  let warm := !gs.isEmpty
  let gsA := gs.toArray
  let mut vsN : Array (Array VR) := #[]
  let mut rsT : Array (Array Expr) := #[]   -- tails of each filament's VR list
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
    -- FV proof from the end
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
  -- AV proof
  let mut av := mkApp2 (mkConst ``AV.nil) cE gsE
  -- the tail of the warm-start list at filament k
  let gsTails : Array Expr ← if warm then listTails gsE else pure #[]
  if warm then av := mkApp2 (mkConst ``AV.nil) cE gsTails[fils.size]!
  else av := mkApp2 (mkConst ``AV.nil) cE gsE
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
  let rm0 : Nat × Nat × Bool := match P with
    | some P => (0, 0, (Nat.ble P.rcW.rBD P.rcW.s0l && Nat.ble P.rcT.rBD P.rcT.s0l) &&
        Nat.ble P.nt (sq P.rcT.rBD))
    | none => (0, 0, true)
  let mut rm := rm0
  let mut rmX := rsE rm
  let rm0E := rmX
  -- per filament: the states before each segment
  let mut steps : Array (Array (Acc × Expr × (Nat × Nat × Bool) × Expr)) := #[]
  for k in [0:fils.size] do
    let sgs := fils[k]!.val.sgs.toArray
    let rs := vsN[k]!
    let n := sgs.size
    let mut st := #[(acc, accX, rm, rmX)]
    for i in [0:n] do
      let a := rs[i]!
      let b := if i + 1 < n then rs[i + 1]! else rs[0]!
      acc := segStep D2 D3S noRC acc sgs[i]! a b
      accX := accE acc
      if let some P := P then
        rm := remStep D2 P rm (sgs[i]!, a, b)
        rmX := rsE rm
      st := st.push (acc, accX, rm, rmX)
    steps := steps.push st
  let tAcc := mkConst ``Acc
  let rAcc := reflH tAcc
  let rRS := reflH tRS
  let mut aw := if P.isSome then mkAppN (mkConst ``AW.nil) #[D2E, D3E, PE, accX, rmX]
    else mkAppN (mkConst ``AW0.nil) #[D2E, D3E, accX]
  for j in [0:fils.size] do
    let k := fils.size - 1 - j
    let F := fils[k]!
    let st := steps[k]!
    let n := F.sgs.size
    let rEl := rsEl[k]!
    let rT := rsT[k]!
    let first := rEl[0]!
    let (_, outX, _, ormX) := st[n]!
    let (_, a0X, _, r0X) := st[0]!
    let mut sw : Expr := default
    let swStep := mkAppN (mkConst ``SW.step) #[D2E, D3E, PE, first]
    let swStep2 := mkAppN (mkConst ``SW.step2) #[D2E, D3E, PE, first]
    let swStep3 := mkAppN (mkConst ``SW.step3) #[D2E, D3E, PE, first]
    let wStep := mkAppN (mkConst ``W.step) #[D2E, D3E, first]
    let wStep2 := mkAppN (mkConst ``W.step2) #[D2E, D3E, first]
    let wStep3 := mkAppN (mkConst ``W.step3) #[D2E, D3E, first]
    -- blocks of segments `[i, i + k)` before the closing segment (sizes 3, then 2 or 1)
    let blocks : Array (Nat × Nat) := Id.run do
      let mut out := #[]
      let mut i := 0
      while i + 1 < n do
        let k := min blk (n - 1 - i)
        out := out.push (i, k)
        i := i + k
      return out
    if P.isSome then
      let (_, aX, _, rX) := st[n - 1]!
      sw := mkAppN (mkConst ``SW.last) #[D2E, D3E, PE, first, aX, rX, F.sgs[n - 1]!, rEl[n - 1]!,
        outX, ormX, reflE tAcc outX, reflE tRS ormX]
      for (i, k) in blocks.reverse do
        let (_, aX, _, rX) := st[i]!
        let (_, aX', _, rX') := st[i + k]!
        sw := match k with
          | 1 => mkAppN swStep #[aX, rX, F.sgs[i]!, F.sgsT[i + 1]!,
              rEl[i]!, rEl[i + 1]!, rT[i + 2]!, aX', rX', outX, ormX, mkApp rAcc aX', mkApp rRS rX', sw]
          | 2 => mkAppN swStep2 #[aX, rX, F.sgs[i]!, F.sgs[i + 1]!, F.sgsT[i + 2]!,
              rEl[i]!, rEl[i + 1]!, rEl[i + 2]!, rT[i + 3]!, aX', rX', outX, ormX, mkApp rAcc aX',
              mkApp rRS rX', sw]
          | _ => mkAppN swStep3 #[aX, rX, F.sgs[i]!, F.sgs[i + 1]!, F.sgs[i + 2]!, F.sgsT[i + 3]!,
              rEl[i]!, rEl[i + 1]!, rEl[i + 2]!, rEl[i + 3]!, rT[i + 4]!, aX', rX', outX, ormX,
              mkApp rAcc aX', mkApp rRS rX', sw]
      aw := mkAppN (mkConst ``AW.cons) #[D2E, D3E, PE, a0X, r0X, F.e, filT[k + 1]!, first, rT[1]!,
        vsT[k + 1]!, outX, ormX, accX, rmX, sw, aw]
    else
      let (_, aX, _, _) := st[n - 1]!
      sw := mkAppN (mkConst ``W.last) #[D2E, D3E, first, aX, F.sgs[n - 1]!, rEl[n - 1]!, outX,
        reflE tAcc outX]
      for (i, k) in blocks.reverse do
        let (_, aX, _, _) := st[i]!
        let (_, aX', _, _) := st[i + k]!
        sw := match k with
          | 1 => mkAppN wStep #[aX, F.sgs[i]!, F.sgsT[i + 1]!, rEl[i]!,
              rEl[i + 1]!, rT[i + 2]!, aX', outX, mkApp rAcc aX', sw]
          | 2 => mkAppN wStep2 #[aX, F.sgs[i]!, F.sgs[i + 1]!, F.sgsT[i + 2]!, rEl[i]!,
              rEl[i + 1]!, rEl[i + 2]!, rT[i + 3]!, aX', outX, mkApp rAcc aX', sw]
          | _ => mkAppN wStep3 #[aX, F.sgs[i]!, F.sgs[i + 1]!, F.sgs[i + 2]!, F.sgsT[i + 3]!,
              rEl[i]!, rEl[i + 1]!, rEl[i + 2]!, rEl[i + 3]!, rT[i + 4]!, aX', outX,
              mkApp rAcc aX', sw]
      aw := mkAppN (mkConst ``AW0.cons) #[D2E, D3E, a0X, F.e, filT[k + 1]!, first, rT[1]!,
        vsT[k + 1]!, outX, accX, sw, aw]
  -- final assembly
  let fin := cornerFinalV o nS X Y Z D c.lam acc hv
  let finX := finE fin
  let ok := ((acc.ok && fin.ok) && Nat.ble (Nat.mul 1000 KT) c.lam) && rm.2.2
  let okX := boolE ok
  let gsOut := vsN.toList.map (fun l => l.toList.map VR.g)
  let vsX := vsT[0]!
  let gsX := gsT'[0]!
  let XE := natE X; let YE := natE Y; let ZE := natE Z; let DE := natE D
  let pf := match P with
    | some _ => mkAppN (mkConst ``corner_some) #[oE, nSE, fsE, XE, YE, ZE, DE, hvE, PE, gsE, cE,
        D2E, D3E, vsX, gsX, rm0E, accX, rmX, finX, okX, reflE (mkConst ``CD) cE, reflE tN D2E,
        reflE tN D3E, reflE tRS rm0E, av, aw, reflE (mkConst ``FinV) finX, reflE tB okX]
    | none => mkAppN (mkConst ``corner_none) #[oE, nSE, fsE, XE, YE, ZE, DE, hvE, gsE, cE,
        D2E, D3E, vsX, gsX, accX, finX, okX, reflE (mkConst ``CD) cE, reflE tN D2E,
        reflE tN D3E, av, aw, reflE (mkConst ``FinV) finX, reflE tB okX]
  let co : Corner4 := ⟨ok, fin, rm.1, rm.2.1, gsOut⟩
  let coX := mkAppN (mkConst ``Corner4.mk) #[okX, finX, natE rm.1, natE rm.2.1, gsX]
  return (pf, coX, gsOut, gNew, co)

/-- **`line_cert`**: prove `lineOut4 o nS fs F mp m mn mn2 = data` (with `o`, `nS`, `fs`, `F`
constants with literal bodies) by the per-segment certificates of this module. -/
syntax (name := lineCertStx) "line_cert" (num)? : tactic

/-- The elaborator of `line_cert`. -/
@[tactic lineCertStx] meta def evalLineCert : Tactic := fun stx => do
  let blk := if stx[1].getNumArgs == 1 then stx[1][0].isNatLit?.getD 3 else 3
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "line_cert: expected an equation"
  let (``lineOut4, #[oE, nSE, fsE, FE, mpE, mE, mnE, mn2E]) := lhs.getAppFnArgs |
    throwError "line_cert: expected `lineOut4 … = data`"
  let o ← readOffs (← bodyOf oE)
  let nS ← readNat (← bodyOf nSE)
  let fsB ← bodyOf fsE
  let fils ← (← listElems fsB).mapM fun x => readFil x
  let filT ← listTails fsB
  let F ← readFace (← bodyOf FE)
  let mp ← readInt mpE; let m ← readInt mE; let mn ← readInt mnE; let mn2 ← readInt mn2E
  let t := trigOf4 m
  let tX := trigE t
  let wsA := F.wn.toArray
  let wsEl := wsA.map intE
  let wsT := tailsE tI wsEl
  let hcs := (faceHC4 F).toArray
  let hcEl := hcs.map hcE
  let tHC := mkConst ``HC
  let hcT := tailsE tHC hcEl
  let tLLN := tL (tL tN)
  let tOI := mkApp (mkConst ``Option [Level.zero]) tI
  let tO3 := mkApp (mkConst ``Option [Level.zero]) (tP tI (tP tI tI))
  let tCR := mkConst ``CRec
  let params := #[oE, nSE, fsE, FE, mpE, mE, mnE, mn2E, tX]
  -- corners
  let mut prev : Option Int := none
  let mut prevX := mkApp (mkConst ``Option.none [Level.zero]) tI
  let mut gs : List (List Nat) := []
  let mut gsX := mkApp (mkConst ``List.nil [Level.zero]) (tL tN)
  let mut gsElems : Array (Array Expr × Array Expr) := #[]
  let mut stepPf : Array (Expr × Expr × Expr × Expr × Expr × Expr) := #[]  -- prev, gs, r, gs', pf
  let mut recs : Array Expr := #[]
  for i in [0:wsA.size] do
    let wn := wsA[i]!
    let wnX := wsEl[i]!
    let ws := (wsA.extract (i + 1) wsA.size).toList
    let cx := cornerXYZ4 F m wn
    let (X, Y, Z, D) := cx.1
    let cxX := pairE (tP tN (tP tN (tP tN tN))) tB
      (pairE tN (tP tN (tP tN tN)) (natE X) (pairE tN (tP tN tN) (natE Y) (pairE tN tN (natE Z)
        (natE D)))) (boolE cx.2)
    let hv := helAt hcs[i]! t
    let hvX := q3E hv
    let win := winN prev ws
    let P : Option RemP := win.map fun w => remP4 F mp m mn2 w.1 wn w.2.1 w.2.2 D
    let PX := match P with | some P => rempE P | none => mkConst ``Unit.unit
    let (cpf, coX, gsOut, gNew, co) ← cornerCert blk oE nSE fsE o nS fils filT X Y Z D hv hvX P PX gs
      gsX gsElems
    let rr : Nat × Nat := match win with
      | some w => (rwC F w.1 wn w.2.1 w.2.2 co.rw, rtC F mp m mn mn2 co.rt)
      | none => (0, 0)
    let r : CRec := ⟨co.ok && cx.2, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez, co.fin.rho, rr.1,
      rr.2⟩
    let rX := crecE r
    let gs'X := mkAppN (mkConst ``Corner4.gs) #[coX]
    let base := params ++ #[prevX, wnX, wsT[i + 1]!, hcEl[i]!, gsX]
    let spf ← match win, P with
      | some w, some Pv =>
        let wX := mkApp2 (mkConst ``Option.some [Level.zero]) (tP tI (tP tI tI))
          (pairE tI (tP tI tI) (intE w.1) (pairE tI tI (intE w.2.1) (intE w.2.2)))
        let rwX := natE rr.1; let rtX := natE rr.2
        pure <| mkAppN (mkConst ``lineStep_some) (base ++ #[intE w.1, intE w.2.1, intE w.2.2,
          natE X, natE Y, natE Z, natE D, boolE cx.2, hvX, rempE Pv, coX, rwX, rtX, rX,
          reflE tO3 wX, reflE (tP (tP tN (tP tN (tP tN tN))) tB) cxX, reflE tQ3 hvX,
          reflE (mkConst ``RemP) PX, cpf, reflE tN rwX, reflE tN rtX, reflE tCR rX])
      | _, _ =>
        pure <| mkAppN (mkConst ``lineStep_none) (base ++ #[natE X, natE Y, natE Z, natE D,
          boolE cx.2, hvX, coX, rX, reflE tO3 (mkApp (mkConst ``Option.none [Level.zero])
            (tP tI (tP tI tI))), reflE (tP (tP tN (tP tN (tP tN tN))) tB) cxX, reflE tQ3 hvX, cpf,
          reflE tCR rX])
    let _ := gs'X
    let newGsX := (match coX.getAppArgs[4]? with | some x => x | none => gsX)
    stepPf := stepPf.push (prevX, gsX, rX, newGsX, spf, wnX)
    recs := recs.push rX
    prev := some wn
    prevX := mkApp2 (mkConst ``Option.some [Level.zero]) tI wnX
    gs := gsOut
    gsX := newGsX
    gsElems := gNew
  let recT := tailsE tCR recs
  let mut lc := mkAppN (mkConst ``LC.nil) (params ++ #[prevX, hcT[wsA.size]!, gsX])
  for j in [0:wsA.size] do
    let i := wsA.size - 1 - j
    let (pX, gX, rX, g'X, spf, wnX) := stepPf[i]!
    lc := mkAppN (mkConst ``LC.cons) (params ++ #[pX, wnX, wsT[i + 1]!, hcEl[i]!, hcT[i + 1]!, gX,
      rX, g'X, recT[i + 1]!, spf, lc])
  -- the hel coefficients
  let lt ← inferType (mkAppN (mkConst ``line_of) #[oE, nSE, fsE, FE, mpE, mE, mnE, mn2E, tX, wsT[0]!,
    hcT[0]!, recT[0]!])
  let hhTy := lt.bindingBody!.bindingBody!.bindingDomain!
  let fX := hhTy.getAppArgs[2]!
  let mut mc := mkApp3 (mkConst ``MC.nil) tI tHC fX
  for j in [0:wsA.size] do
    let i := wsA.size - 1 - j
    mc := mkAppN (mkConst ``MC.cons) #[tI, tHC, fX, wsEl[i]!, wsT[i + 1]!, hcEl[i]!, hcT[i + 1]!,
      reflE tHC hcEl[i]!, mc]
  let pf := mkAppN (mkConst ``line_of) #[oE, nSE, fsE, FE, mpE, mE, mnE, mn2E, tX, wsT[0]!,
    hcT[0]!, recT[0]!, reflE (mkConst ``Trig) tX, reflE (tL tI) wsT[0]!, mc, lc]
  let _ := tLLN; let _ := tOI
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal []

end LineCert

end PlasmaLean.Design.PolygonCoil
