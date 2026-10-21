/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCheck

/-!
# The cubic-interpolation frontier checker (computational part)

Core-only natural-number checker for the higher-order frontier certificate. Its meaning is given
in `Design/PolygonCoilCubicSound*`. Compared with `Design/PolygonCoilCheck` (bilinear cells with
a remainder bounded by second derivatives):

* grid lines are parametrised by `t = m/4096` with `φ = π/2 + 2 arctan t` (so the fundamental
  piece `φ ∈ [π/4, 3π/4]` is `|t| ≤ √2 - 1`), corner points
  `(-2ρt/(1 + t²), ρ(1 - t²)/(1 + t²), ζ)` are exact rationals;
* each corner returns, besides the norm bound `e ≥ 2⁴⁰‖Bh - hel‖`, a rounded vector
  `Ê ≈ 2⁴⁰(Bh - hel)` with componentwise error `≤ ρ`, and two remainder contributions
  `RwC`, `RtC` (scale `2⁴⁰`) bounding the cubic-interpolation errors along the `w`-line through
  the corner and along the `t`-strip of the cell starting at the corner (fourth-derivative bounds
  `120/d⁶` along lines and `c₆/d⁶ + c₄/d⁴ + c₂/d²` along the circles, with `d` a lower bound for
  the distance to each segment);
* a cell `[t₁, t₂] × [w₁, w₂]` passes if `max e + C_w + Λ_w C_t + Λ_t max RwC + RtC ≤ η` with
  the divided-difference corrections `C_w`, `C_t` of the `4 × 4` stencil and the Lebesgue
  factors `Λ`.

Line outputs are computed once per grid line (`lineOut4`) and compared with literal data; the
cell checks (`cellsOK4`) then run on the literal data.
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-! ## Constants -/

/-- `2²⁴ = 2⁶⁴/2⁴⁰`. -/
def two24 : Nat := 16777216

/-- Minimum of two naturals. -/
def nmin2 (a b : Nat) : Nat := cond (Nat.ble a b) a b

/-! ## Faces -/

/-- A face of the fundamental frontier piece for the cubic checker: `kind` as in `Face`, the
`w`-grid `wn/wd` **including one extra node beyond each end of the face**, and the bounds
`HT = htn/htd`, `HW = hwn/hwd` on the fourth derivatives of `⟨n, hel⟩` along `t` and `w`. -/
structure Face4 where
  /-- face kind -/
  kind : Nat
  /-- common denominator of the `w`-grid -/
  wd : Nat
  /-- numerators of the `w`-grid (increasing; first and last nodes lie outside the face) -/
  wn : List Int
  /-- `HT` numerator -/
  htn : Nat
  /-- `HT` denominator -/
  htd : Nat
  /-- `HW` numerator -/
  hwn : Nat
  /-- `HW` denominator -/
  hwd : Nat

-- Decidable equality of the precomputed filament data (to check literal copies once).
deriving instance DecidableEq for Vt, Seg, Fil

/-- `(ρ, ζ)` of the grid value `w = wn/wd` on a face. -/
def faceRZ4 (F : Face4) (wn : Int) : QQ × QQ :=
  if F.kind < 2 then (⟨cylR F.kind, 181⟩, ⟨wn, F.wd⟩)
  else (⟨wn, F.wd⟩, ⟨if F.kind = 2 then 3420 else -3420, 32761⟩)

/-- The corner `(t = m/4096, w = wn/wd)`: translated numerators, denominator, nonnegativity check.
With `c = q² + m²`: `x = -2ρmq/c`, `y = ρ(q² - m²)/c`. The common denominator carries an extra
factor `2¹⁰`: this does not change the point, but it makes the rounding of the vertex square
roots (absolute tolerance `KT`, relative to `λ = D·2³²`) negligible. -/
def cornerXYZ4 (F : Face4) (m : Int) (wn : Int) : (Nat × Nat × Nat × Nat) × Bool :=
  let q : Int := qT
  let cd : Int := q * q + m * m
  let cn : Int := q * q - m * m
  let sn : Int := 2 * m * q
  let rz := faceRZ4 F wn
  let D : Int := rz.1.den * cd * rz.2.den * 1024
  let X := -(rz.1.num * sn * rz.2.den * 1024) + 4 * D
  let Y := rz.1.num * cn * rz.2.den * 1024 + 4 * D
  let Z := rz.2.num * rz.1.den * cd * 1024 + 4 * D
  ((X.toNat, Y.toNat, Z.toNat, D.toNat), decide (0 ≤ X) && decide (0 ≤ Y) && decide (0 ≤ Z))

/-- `cos φ = -2mq/(q² + m²)`, `sin φ = (q² - m²)/(q² + m²)` of the grid line `m`. -/
def trigOf4 (m : Int) : Trig :=
  let q : Int := qT
  let cd : Nat := (q * q + m * m).toNat
  mkTrig ⟨-(2 * m * q), cd⟩ ⟨q * q - m * m, cd⟩

/-! ## The corner -/

/-- Corner output with the rounded error vector: checks, norm bound `e`, `Ê = (ex, ey, ez)` and
its componentwise error `rho` (all at scale `2⁴⁰`). -/
structure FinV where
  /-- checks -/
  ok : Bool
  /-- norm bound -/
  e : Nat
  /-- `x`-component of `Ê` -/
  ex : Int
  /-- `y`-component of `Ê` -/
  ey : Int
  /-- `z`-component of `Ê` -/
  ez : Int
  /-- componentwise error of `Ê` -/
  rho : Nat

/-- The final assembly of a corner (as `cornerFinal`, with the segment count bound `nS`) together
with the rounded error vector. -/
def cornerFinalV (o : Offs) (nS : Nat) (Xt Yt Zt D lam : Nat) (acc : Acc) (h : QQ × QQ × QQ) :
    FinV :=
  let sf := acc.sf
  let S1x := unoff acc.sx o.c1x sf
  let S1y := unoff acc.sy o.c1y sf
  let S1z := unoff acc.sz o.c1z sf
  let S2x := unoff acc.tx o.c2x sf
  let S2y := unoff acc.ty o.c2y sf
  let S2z := unoff acc.tz o.c2z sf
  let Dz : Int := D
  let Xi : Int := Xt
  let Yi : Int := Yt
  let Zi : Int := Zt
  let Tx := Dz * S1x - 4294967296 * (Yi * S2z - Zi * S2y)
  let Ty := Dz * S1y - 4294967296 * (Zi * S2x - Xi * S2z)
  let Tz := Dz * S1z - 4294967296 * (Xi * S2y - Yi * S2x)
  let E1 := Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c1m) sf) lam) (Nat.mul nS o.c1m)
  let E2 := Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c2m) sf) lam) (Nat.mul nS o.c2m)
  let Rxn : Nat := Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Yt Zt) E2))
  let Ryn : Nat := Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Zt Xt) E2))
  let Rzn : Nat := Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Xt Yt) E2))
  let Rx : Int := Rxn
  let Ry : Int := Ryn
  let Rz : Int := Rzn
  let SE := Nat.mul D two136
  let mx := nmax (Tx - Rx - h.1.ceilMul SE).natAbs (Tx + Rx - h.1.floorMul SE).natAbs
  let my := nmax (Ty - Ry - h.2.1.ceilMul SE).natAbs (Ty + Ry - h.2.1.floorMul SE).natAbs
  let mz := nmax (Tz - Rz - h.2.2.ceilMul SE).natAbs (Tz + Rz - h.2.2.floorMul SE).natAbs
  let N := Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz)) (sq two40)
  let sN := sqrtUpFrom N (Nat.mul (Nat.add (Nat.add mx my) mz) two40)
  let ex := Int.fdiv ((Tx * h.1.den - h.1.num * SE) * two40) (SE * h.1.den)
  let ey := Int.fdiv ((Ty * h.2.1.den - h.2.1.num * SE) * two40) (SE * h.2.1.den)
  let ez := Int.fdiv ((Tz * h.2.2.den - h.2.2.num * SE) * two40) (SE * h.2.2.den)
  let rho := Nat.add (cdiv (Nat.mul (nmax (nmax Rxn Ryn) Rzn) two40) SE) 1
  ⟨Nat.ble N (sq sN), cdiv sN SE, ex, ey, ez, rho⟩

/-- Remainder parameters of a corner: the radii data of the `w`-line region (`rcW`) and of the
`t`-strip region (`rcT`) (only `rBD`, `s0l` are used), the scaled kernel constants
`w6 ≥ 120λ⁶`, `t6 ≥ c₆λ⁶`, `t4 ≥ c₄λ⁴`, `t2 ≥ c₂λ²`, and `λ²`. -/
structure RemP where
  /-- `w`-line region -/
  rcW : RC
  /-- `t`-strip region -/
  rcT : RC
  /-- `≥ 120 λ⁶` -/
  w6 : Nat
  /-- `≥ c₆ λ⁶` -/
  t6 : Nat
  /-- `≥ c₄ λ⁴` -/
  t4 : Nat
  /-- `≥ c₂ λ²` -/
  t2 : Nat
  /-- `λ²` -/
  lam2 : Nat
  /-- `≥ λ² (radius of the t-strip region)²`, checked against `rcT.rBD²` -/
  nt : Nat

/-- The segment triples `(segment constants, vertex result at p, vertex result at q)` of all
filaments at a corner. -/
def triples4 (fs : List Fil) (vss : List (List VR)) : List (Seg × VR × VR) :=
  (List.zip fs vss).flatMap fun fv => List.zip fv.1.sgs (List.zip fv.2 (rot1 fv.2))

/-- Remainder step of one segment: the distance bounds `L_w`, `L_t` of the two regions and the
two kernel terms; checks `L_w > 0`, `L_t > 0`, `λ² ≤ 25 L_t` (distance `≥ 1/5`). -/
def remStep (D2 : Nat) (P : RemP) (acc : Nat × Nat × Bool) (x : Seg × VR × VR) :
    Nat × Nat × Bool :=
  let d2 := d2Low x.2.1.n x.2.2.n (Nat.mul D2 x.1.vv)
  let Lw := cellL P.rcW d2
  let Lt := cellL P.rcT d2
  let tw := cdiv (Nat.mul x.1.kv P.w6) (Nat.mul (Nat.mul (Nat.mul Lw Lw) Lw) two24)
  let tt := cdiv (Nat.mul x.1.kv (Nat.add P.t6 (Nat.mul Lt (Nat.add P.t4 (Nat.mul Lt P.t2)))))
    (Nat.mul (Nat.mul (Nat.mul Lt Lt) Lt) two24)
  (Nat.add acc.1 tw, Nat.add acc.2.1 tt,
    ((acc.2.2 && Nat.blt 0 Lw) && Nat.blt 0 Lt) && Nat.ble P.lam2 (Nat.mul 25 Lt))

/-- Raw corner output: checks, `FinV`, the two remainder sums, and the Newton warm starts. -/
structure Corner4 where
  /-- all checks -/
  ok : Bool
  /-- values -/
  fin : FinV
  /-- `w`-remainder sum -/
  rw : Nat
  /-- `t`-remainder sum -/
  rt : Nat
  /-- warm starts -/
  gs : List (List Nat)

/-- Evaluate one corner (with optional remainder parameters). -/
def cornerEval4 (o : Offs) (nS : Nat) (fs : List Fil) (Xt Yt Zt D : Nat) (h : QQ × QQ × QQ)
    (P : Option RemP) (gs : List (List Nat)) : Corner4 :=
  let D2 := Nat.mul D D
  let Xs := Nat.mul Xt two32
  let Ys := Nat.mul Yt two32
  let Zs := Nat.mul Zt two32
  let lam := Nat.mul D two32
  let c : CD := ⟨D, D2, Xs, Ys, Zs, Nat.add (Nat.add (sq Xs) (sq Ys)) (sq Zs), lam⟩
  let vs := allVerts c fs gs
  let acc := allWalk D2 (Nat.mul (Nat.mul D2 D) two136) noRC ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ fs vs
  let fin := cornerFinalV o nS Xt Yt Zt D lam acc h
  let rem : Nat × Nat × Bool := match P with
    | some P => (triples4 fs vs).foldl (remStep D2 P) (0, 0,
        (Nat.ble P.rcW.rBD P.rcW.s0l && Nat.ble P.rcT.rBD P.rcT.s0l) && Nat.ble P.nt (sq P.rcT.rBD))
    | none => (0, 0, true)
  ⟨((acc.ok && fin.ok) && Nat.ble (Nat.mul 1000 KT) lam) && rem.2.2, fin, rem.1, rem.2.1,
    vs.map (fun l => l.map VR.g)⟩

/-! ## Remainder parameters from the grid -/

/-- Absolute value of an integer as a natural number. -/
def iabs (a : Int) : Nat := a.natAbs

/-- Remainder parameters of the corner `(m, wn)` of face `F`, for the `t`-strip
`[mp, mn2] × [wn, wn1]` and the `w`-line `{m} × [wp, wn2]`, at denominator `D`. -/
def remP4 (F : Face4) (mp m mn2 wp wn wn1 wn2 : Int) (D : Nat) : RemP :=
  let q : Nat := qT
  let lam := Nat.mul D two32
  -- `w`-line region `{t} × [wp, wn2]` around `wn`: radius `max(wn - wp, wn2 - wn)/wd`
  let dW := nmax (iabs (wn - wp)) (iabs (wn2 - wn))
  let rBW := cdiv (Nat.mul lam dW) F.wd
  -- `t`-strip region `[mp, mn2] × [wn, wn1]` around `(m, wn)`
  let ρn : Nat := if F.kind < 2 then (cylR F.kind).toNat else iabs wn1
  let ρd : Nat := if F.kind < 2 then 181 else F.wd
  let dm := nmax (iabs (m - mp)) (iabs (mn2 - m))
  let dw := iabs (wn1 - wn)
  -- `λ²((2ρΔt)² + Δw²)` with `Δt = dm/q`, `Δw = dw/wd`
  let Nt := cdiv
    (Nat.mul (sq lam) (Nat.add (Nat.mul 4 (Nat.mul (sq ρn) (Nat.mul (sq dm) (sq F.wd))))
      (Nat.mul (sq dw) (Nat.mul (sq ρd) (sq q))))) (Nat.mul (sq ρd) (Nat.mul (sq q) (sq F.wd)))
  let g0 := Nat.add (cdiv (Nat.mul lam (Nat.mul 2 (Nat.mul ρn dm))) (Nat.mul ρd q))
    (cdiv (Nat.mul lam dw) F.wd)
  let rBT := sqrtUpFrom Nt g0
  -- kernel constants: `T = q²/(q² + mmin²)`, `tmax = mmax/q`, `ρ = ρn/ρd`
  let mlo := mp
  let mhi := mn2
  let mmin : Nat := if mlo ≤ 0 ∧ 0 ≤ mhi then 0 else nmin2 (iabs mlo) (iabs mhi)
  let mmax : Nat := nmax (iabs mlo) (iabs mhi)
  let Tn := sq q
  let Td := Nat.add (sq q) (sq mmin)
  -- `c₆ = (11520 ρ⁴T⁴ + (2304 tmax + 2309) ρ³T⁴)/6`
  -- `c₄ = 3 (2304 tmax + 2309) ρ³T⁴/2 + 864 ρ² + 16 ρ`, `c₂ = 144 ρ`
  let T4n := sq (sq Tn)
  let T4d := sq (sq Td)
  let aT := Nat.add (Nat.mul 2304 mmax) (Nat.mul 2309 q)
  let c6n := Nat.mul T4n (Nat.add (Nat.mul 11520 (Nat.mul (sq (sq ρn)) q))
    (Nat.mul aT (Nat.mul (sq ρn) (Nat.mul ρn ρd))))
  let c6d := Nat.mul 6 (Nat.mul T4d (Nat.mul (sq (sq ρd)) q))
  let c4n := Nat.add (Nat.mul 3 (Nat.mul T4n (Nat.mul aT (Nat.mul (sq ρn) ρn))))
    (Nat.mul (Nat.mul 2 T4d) (Nat.mul q (Nat.add (Nat.mul 864 (Nat.mul (sq ρn) ρd))
      (Nat.mul 16 (Nat.mul ρn (sq ρd))))))
  let c4d := Nat.mul 2 (Nat.mul T4d (Nat.mul q (Nat.mul (sq ρd) ρd)))
  let lam2 := sq lam
  let lam4 := sq lam2
  let lam6 := Nat.mul lam4 lam2
  ⟨⟨true, Nat.mul D two30, rBW, 0, 0, 0, 1, 0⟩, ⟨true, Nat.mul D two30, rBT, 0, 0, 0, 1, 0⟩,
   Nat.mul 120 lam6, cdiv (Nat.mul c6n lam6) c6d, cdiv (Nat.mul c4n lam4) c4d,
   cdiv (Nat.mul (Nat.mul 144 ρn) lam2) ρd, lam2, Nt⟩

/-! ## Lines -/

/-- One corner record of a grid line: checks, norm bound `e`, rounded error vector `Ê`, its
componentwise error `rho`, and the remainder contributions `rw` (along the `w`-line, cell
`[w, w⁺]`) and `rt` (along the `t`-strip of the cell starting at this corner), all at scale
`2⁴⁰`. -/
structure CRec where
  /-- checks -/
  ok : Bool
  /-- norm bound -/
  e : Nat
  /-- `x`-component of `Ê` -/
  ex : Int
  /-- `y`-component of `Ê` -/
  ey : Int
  /-- `z`-component of `Ê` -/
  ez : Int
  /-- componentwise error of `Ê` -/
  rho : Nat
  /-- `w`-remainder contribution -/
  rw : Nat
  /-- `t`-remainder contribution -/
  rt : Nat
deriving DecidableEq

/-- `w`-remainder contribution: `⌈(R_w + 2⁴⁰ HW) ω_w/24⌉` with
`ω_w ≤ (w₂ - w₁)²(w₂ - w₀)(w₃ - w₁)/4`. -/
def rwC (F : Face4) (w0 w1 w2 w3 : Int) (rw : Nat) : Nat :=
  cdiv (Nat.mul (Nat.add rw (cdiv (Nat.mul F.hwn two40) F.hwd))
    (Nat.mul (sq (iabs (w2 - w1))) (Nat.mul (iabs (w2 - w0)) (iabs (w3 - w1)))))
    (Nat.mul 96 (sq (sq F.wd)))

/-- `t`-remainder contribution: `⌈(R_t + 2⁴⁰ HT) ω_t/24⌉` with `t = m/4096`. -/
def rtC (F : Face4) (m0 m1 m2 m3 : Int) (rt : Nat) : Nat :=
  cdiv (Nat.mul (Nat.add rt (cdiv (Nat.mul F.htn two40) F.htd))
    (Nat.mul (sq (iabs (m2 - m1))) (Nat.mul (iabs (m2 - m0)) (iabs (m3 - m1)))))
    (Nat.mul 96 (sq (sq qT)))

/-- Corner records along the grid line `m` (with `t`-neighbours `mp`, `mn`, `mn2`), over the
`w`-values `ws` (previous value `prev`), with the precomputed `hel` coefficients `hcs`. -/
def lineGo4 (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int) (t : Trig) :
    Option Int → List Int → List HC → List (List Nat) → List CRec
  | prev, wn :: ws, hc :: hcs, gs =>
    let cx := cornerXYZ4 F m wn
    let xyz := cx.1
    let win : Option (Int × Int × Int) := match prev, ws with
      | some wp, wn1 :: wn2 :: _ => some (wp, wn1, wn2)
      | _, _ => none
    let P : Option RemP := match win with
      | some w => some (remP4 F mp m mn2 w.1 wn w.2.1 w.2.2 xyz.2.2.2)
      | none => none
    let co := cornerEval4 o nS fs xyz.1 xyz.2.1 xyz.2.2.1 xyz.2.2.2 (helAt hc t) P gs
    let rr : Nat × Nat := match win with
      | some w => (rwC F w.1 wn w.2.1 w.2.2 co.rw, rtC F mp m mn mn2 co.rt)
      | none => (0, 0)
    ⟨co.ok && cx.2, co.fin.e, co.fin.ex, co.fin.ey, co.fin.ez, co.fin.rho, rr.1, rr.2⟩ ::
      lineGo4 o nS fs F mp m mn mn2 t (some wn) ws hcs co.gs
  | _, _, _, _ => []

/-- The precomputed `hel` coefficients along the `w`-grid of a face. -/
def faceHC4 (F : Face4) : List HC := F.wn.map (fun wn => let rz := faceRZ4 F wn; helCoef rz.1 rz.2)

/-- **Corner records of the grid line `m`** (neighbours `mp < m < mn < mn2`). -/
def lineOut4 (o : Offs) (nS : Nat) (fs : List Fil) (F : Face4) (mp m mn mn2 : Int) : List CRec :=
  lineGo4 o nS fs F mp m mn mn2 (trigOf4 m) none F.wn (faceHC4 F) []

/-! ## Cells -/

/-- `|x| + |y| + |z|` of an integer vector. -/
def l1 (x y z : Int) : Nat := Nat.add (Nat.add (iabs x) (iabs y)) (iabs z)

/-- The second-difference correction `⌈(X₂ - X₁)²/4 |dd₂|⌉` (`ℓ¹` norm, with rounding) of a
stencil with nodes `X₀ < X₁ < X₂`: `dd₂` is `N₂/((X₁ - X₀)(X₂ - X₁)(X₂ - X₀))` with
`N₂ = (X₂ - X₁)v₀ - (X₂ - X₀)v₁ + (X₁ - X₀)v₂`. -/
def corrA (X0 X1 X2 : Int) (v0 v1 v2 : CRec) : Nat :=
  let a := X1 - X0
  let b := X2 - X1
  let ac := X2 - X0
  let k0 := b
  let k1 := -ac
  let k2 := a
  let r := Nat.mul 3 (Nat.add (Nat.add (Nat.mul (iabs k0) v0.rho) (Nat.mul (iabs k1) v1.rho))
    (Nat.mul (iabs k2) v2.rho))
  cdiv (Nat.mul (iabs b) (Nat.add (l1 (k0 * v0.ex + k1 * v1.ex + k2 * v2.ex)
    (k0 * v0.ey + k1 * v1.ey + k2 * v2.ey) (k0 * v0.ez + k1 * v1.ez + k2 * v2.ez)) r))
    (Nat.mul 4 (iabs (a * ac)))

/-- The third-difference correction `⌈(X₂ - X₁)²(X₂ - X₀)/4 |dd₃|⌉` (`ℓ¹` norm, with rounding)
of a stencil `X₀ < X₁ < X₂ < X₃`. -/
def corrB (X0 X1 X2 X3 : Int) (v0 v1 v2 v3 : CRec) : Nat :=
  let a := X1 - X0
  let b := X2 - X1
  let c := X3 - X2
  let ac := X2 - X0
  let bc := X3 - X1
  let abc := X3 - X0
  let k0 := -(c * bc * b)
  let k1 := a * ac * c + c * bc * ac
  let k2 := -(a * ac * bc + c * bc * a)
  let k3 := a * ac * b
  let r := Nat.mul 3 (Nat.add (Nat.add (Nat.mul (iabs k0) v0.rho) (Nat.mul (iabs k1) v1.rho))
    (Nat.add (Nat.mul (iabs k2) v2.rho) (Nat.mul (iabs k3) v3.rho)))
  cdiv (Nat.mul (iabs b) (Nat.add (l1 (k0 * v0.ex + k1 * v1.ex + k2 * v2.ex + k3 * v3.ex)
    (k0 * v0.ey + k1 * v1.ey + k2 * v2.ey + k3 * v3.ey)
    (k0 * v0.ez + k1 * v1.ez + k2 * v2.ez + k3 * v3.ez)) r))
    (Nat.mul 4 (iabs (a * c * bc * abc)))

/-- The divided-difference correction of a `4`-node stencil (nodes `X₀ < X₁ < X₂ < X₃`, values
the rounded vectors of `v₀, …, v₃`): `⌈(X₂ - X₁)²/4 |dd₂|⌉ + ⌈(X₂ - X₁)²(X₂ - X₀)/4 |dd₃|⌉` in
the `ℓ¹` norm, including the rounding errors. -/
def corr4 (X0 X1 X2 X3 : Int) (v0 v1 v2 v3 : CRec) : Nat :=
  Nat.add (corrA X0 X1 X2 v0 v1 v2) (corrB X0 X1 X2 X3 v0 v1 v2 v3)

/-- Lebesgue factor applied to `C`: `⌈(1 + 2(B₀ + B₃)) C⌉` with
`B₀ = (X₂ - X₁)²(X₃ - X₁)/(4(X₁ - X₀)(X₂ - X₀)(X₃ - X₀))`,
`B₃ = (X₂ - X₁)²(X₂ - X₀)/(4(X₃ - X₀)(X₃ - X₁)(X₃ - X₂))`. -/
def leb4 (X0 X1 X2 X3 : Int) (C : Nat) : Nat :=
  let n0 := Nat.mul (sq (iabs (X2 - X1))) (iabs (X3 - X1))
  let d0 := Nat.mul 4 (iabs ((X1 - X0) * (X2 - X0) * (X3 - X0)))
  let n3 := Nat.mul (sq (iabs (X2 - X1))) (iabs (X2 - X0))
  let d3 := Nat.mul 4 (iabs ((X3 - X0) * (X3 - X1) * (X3 - X2)))
  cdiv (Nat.mul C (Nat.add (Nat.mul d0 d3) (Nat.mul 2 (Nat.add (Nat.mul n0 d3) (Nat.mul n3 d0)))))
    (Nat.mul d0 d3)

/-- Maximum of four naturals. -/
def nmax4 (a b c d : Nat) : Nat := nmax (nmax a b) (nmax c d)

/-- A `w`-value lies in the range of the face: `|w| ≤ a` (cylinders), `161/181 ≤ w ≤ 199/181`
(planes). -/
def inFaceB (F : Face4) (w : Int) : Bool :=
  if F.kind < 2 then decide (iabs w * 32761 ≤ 3420 * F.wd)
  else decide (161 * (F.wd : Int) ≤ 181 * w) && decide (181 * w ≤ 199 * (F.wd : Int))

/-- The geometric conditions of a cell stencil: increasing nodes, `|t| ≤ 1/2`, the lowest
`w`-node `≥ 17/20` on the plane faces, and the cell inside the face range. -/
def cellCond (F : Face4) (M0 M1 M2 M3 W0 W1 W2 W3 : Int) : Bool :=
  ((decide (M0 < M1) && decide (M1 < M2) && decide (M2 < M3)) &&
    (decide (W0 < W1) && decide (W1 < W2) && decide (W2 < W3))) &&
  ((decide (-2048 ≤ M0) && decide (M3 ≤ 2048)) &&
    ((decide (F.kind < 2) || decide (17 * (F.wd : Int) ≤ 20 * W0)) &&
      (inFaceB F W1 && inFaceB F W2)))

/-- **The check of one cell** `[t₁, t₂] × [w₁, w₂]` from its `4 × 4` stencil: rows `a, b, c, d`
(the lines `t₀, …, t₃`), columns `0, …, 3` (the nodes `w₀, …, w₃`). -/
def cellOK4 (F : Face4) (eta : Nat) (M0 M1 M2 M3 W0 W1 W2 W3 : Int)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : CRec) : Bool :=
  let oks := ((a0.ok && a1.ok) && (a2.ok && a3.ok)) && ((b0.ok && b1.ok) && (b2.ok && b3.ok)) &&
    (((c0.ok && c1.ok) && (c2.ok && c3.ok)) && ((d0.ok && d1.ok) && (d2.ok && d3.ok)))
  let E := nmax4 b1.e b2.e c1.e c2.e
  let Cw := nmax (corr4 W0 W1 W2 W3 b0 b1 b2 b3) (corr4 W0 W1 W2 W3 c0 c1 c2 c3)
  let Cs := nmax4 (corr4 M0 M1 M2 M3 a0 b0 c0 d0) (corr4 M0 M1 M2 M3 a1 b1 c1 d1)
    (corr4 M0 M1 M2 M3 a2 b2 c2 d2) (corr4 M0 M1 M2 M3 a3 b3 c3 d3)
  let RW := nmax4 a1.rw b1.rw c1.rw d1.rw
  (cellCond F M0 M1 M2 M3 W0 W1 W2 W3 && oks) &&
    Nat.ble (Nat.add (Nat.add (Nat.add (Nat.add E Cw) (leb4 W0 W1 W2 W3 Cs))
      (leb4 M0 M1 M2 M3 RW)) b1.rt) eta

/-- The cells of one row (lines `t₀ < t₁ < t₂ < t₃`, cells between `t₁` and `t₂`), sliding along
the `w`-grid. -/
def cellsRow4 (F : Face4) (eta : Nat) (M0 M1 M2 M3 : Int) :
    List CRec → List CRec → List CRec → List CRec → List Int → Bool
  | a0 :: a1 :: a2 :: a3 :: as, b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: c2 :: c3 :: cs,
      d0 :: d1 :: d2 :: d3 :: ds, W0 :: W1 :: W2 :: W3 :: ws =>
    cellOK4 F eta M0 M1 M2 M3 W0 W1 W2 W3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 &&
      cellsRow4 F eta M0 M1 M2 M3 (a1 :: a2 :: a3 :: as) (b1 :: b2 :: b3 :: bs)
        (c1 :: c2 :: c3 :: cs) (d1 :: d2 :: d3 :: ds) (W1 :: W2 :: W3 :: ws)
  | _, _, _, _, _ => true

/-- All rows of a face: consecutive quadruples of grid lines and their records. -/
def cellsAll4 (eta : Nat) (F : Face4) : List Int → List (List CRec) → Bool
  | m0 :: m1 :: m2 :: m3 :: ms, L0 :: L1 :: L2 :: L3 :: Ls =>
    cellsRow4 F eta m0 m1 m2 m3 L0 L1 L2 L3 F.wn &&
      cellsAll4 eta F (m1 :: m2 :: m3 :: ms) (L1 :: L2 :: L3 :: Ls)
  | _, _ => true

end PlasmaLean.Design.PolygonCoil
