/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

/-!
# Polygonal helical coils: the computational frontier checker

This module is deliberately **core-only** (no Mathlib): it contains the executable natural-number
checker that the kernel runs (`decide +kernel`) on the certificate chunks
`Design/PolygonCoilCert*.lean`. Its meaning is given in `Design/PolygonCoilSoundA`-`D`, where
every quantity below is related to the real Biot–Savart field of the polygonal coils, to the
helical target field `hel`, and to the interpolation-error bounds of `Design/PolygonCoilInterp`.

Conventions (all checked, nothing is trusted):
* Vertex coordinates are integers at scale `2⁻³²`; they are translated by `+4` (so that all
  coordinates are positive) before conversion to naturals. Corner points of the frontier grid are
  exact rationals `(X, Y, Z)/D`, translated the same way.
* A filament is a closed polygon with vertex list `xs`; segment `k` joins `xs[k]` to
  `xs[k+1 mod n]` (`List.zip xs (rot1 xs)`).
* A segment `p → q` with current factor `κ = K/2³²` (`κ = μ₀I/4π`) has the closed-form field
  `κ (a × b)(|a| + |b|)/(|a||b|(|a||b| + a·b))`, `a = p - y`, `b = q - y`. With
  `A = 2³² D a`, `B = 2³² D b` (integers) it equals `K D² (A × V) f(|A|, |B|)` where
  `f(α, β) = 2(α + β)/(αβ(2αβ + 2A·B))`. The checker brackets `|A|` by `α ≤ |A| ≤ α + 2·2⁴⁷`
  (Newton iterates, verified by squaring), evaluates `f` at the lower brackets with a floor
  division, and accumulates `Σ f·(K P'×V + C₁)`, `Σ f·(K V + C₂)` and `Σ f`, where the offsets `C`
  make every summand a natural number.
* The remainder of a grid cell is `Σ_seg κ|v|(Δφ²(6ρ²/d⁴ + 2ρ/(d² d₀)) + 6Δw²/d⁴)/8` plus the
  `hel` part, with `d` a lower bound for the distance of the cell to the segment computed from
  the corner–vertex distances (`d₀ = 1/5`).
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-! ## Constants and helpers -/

/-- `2³²`, the scale of vertex coordinates. -/
def two32 : Nat := 4294967296
/-- `2³⁰ = 2³²/4` (`s₀ λ` with `s₀ = 1/4`). -/
def two30 : Nat := 1073741824
/-- `2⁴⁰`, the scale of the final bounds. -/
def two40 : Nat := 1099511627776
/-- `2⁶⁴ = (2³²)²`. -/
def two64 : Nat := 18446744073709551616
/-- `2¹³⁶ = 2^(3·32 + 40)`, the scale of the kernel factor `f`. -/
def two136 : Nat := 87112285931760246646623899502532662132736
/-- Tolerance of the square-root brackets, `2⁴⁷`. -/
def KT : Nat := 140737488355328
/-- Denominator of the grid parameter `t = m/4096`. -/
def qT : Nat := 4096
/-- Number of segments (8 filaments of 16 segments). -/
def nSeg : Nat := 128
/-- The target `η = 6.5 × 10⁻⁴` at scale `2⁴⁰` (floor). -/
def etaFp : Nat := 714682558

/-- Square of a natural number. -/
def sq (a : Nat) : Nat := Nat.mul a a
/-- Ceiling division (for `b > 0`). -/
def cdiv (a b : Nat) : Nat := Nat.div (Nat.add a (Nat.sub b 1)) b
/-- One floor-Newton step for `√n`. -/
def nst (n x : Nat) : Nat := Nat.div (Nat.add x (Nat.div n x)) 2
/-- `k` floor-Newton steps. -/
def nstK (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => nstK n k (nst n x)
/-- Maximum of two naturals. -/
def nmax (a b : Nat) : Nat := cond (Nat.ble a b) b a

/-! ## Vertices and segments -/

/-- Rotation of a list by one place: `[x₀, x₁, …, xₙ₋₁] ↦ [x₁, …, xₙ₋₁, x₀]`. -/
def rot1 {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

/-- Translation of an integer coordinate (scale `2³²`) by `+4`. -/
def tr (x : Int) : Int := x + 4 * 4294967296

/-- A translated vertex `P' = p + 4` (naturals at scale `2³²`) and `|P'|²`. -/
structure Vt where
  /-- translated `x` -/
  px : Nat
  /-- translated `y` -/
  py : Nat
  /-- translated `z` -/
  pz : Nat
  /-- `|P'|²` -/
  pp : Nat

/-- The translated vertex of an integer point. -/
def mkVt (p : Int × Int × Int) : Vt :=
  ⟨(tr p.1).toNat, (tr p.2.1).toNat, (tr p.2.2).toNat,
   (tr p.1 * tr p.1 + tr p.2.1 * tr p.2.1 + tr p.2.2 * tr p.2.2).toNat⟩

/-- Precomputed constants of one segment `p → q`: `|V|²` with `V = q - p`, the offset kernel
weights `K P'×V + C₁`, `K V + C₂`, and `|K| ⌈|V|⌉`. -/
structure Seg where
  /-- `|V|²` -/
  vv : Nat
  /-- `K (P' × V)ₓ + C₁ₓ` -/
  w1x : Nat
  /-- `K (P' × V)_y + C₁_y` -/
  w1y : Nat
  /-- `K (P' × V)_z + C₁_z` -/
  w1z : Nat
  /-- `K Vₓ + C₂ₓ` -/
  w2x : Nat
  /-- `K V_y + C₂_y` -/
  w2y : Nat
  /-- `K V_z + C₂_z` -/
  w2z : Nat
  /-- `|K| (⌊√|V|²⌋ + 1)` -/
  kv : Nat

/-- Offsets `C₁ = (C₁ₓ, C₁_y, C₁_z)`, `C₂` (each at least the largest weight in absolute
value, checked by `filOK`). -/
structure Offs where
  /-- `C₁ₓ` -/
  c1x : Nat
  /-- `C₁_y` -/
  c1y : Nat
  /-- `C₁_z` -/
  c1z : Nat
  /-- `C₂ₓ` -/
  c2x : Nat
  /-- `C₂_y` -/
  c2y : Nat
  /-- `C₂_z` -/
  c2z : Nat
  /-- a common bound `≥ C₁ₓ, C₁_y, C₁_z` -/
  c1m : Nat
  /-- a common bound `≥ C₂ₓ, C₂_y, C₂_z` -/
  c2m : Nat

/-- An upper square-root bracket: `80` Newton steps from `n + 1`, plus one. -/
def sqrtUp (n : Nat) : Nat := Nat.add (nstK n 80 (Nat.add n 1)) 1

/-- The segment constants of `p → q` with current numerator `K`. -/
def mkSeg (o : Offs) (K : Int) (p q : Int × Int × Int) : Seg :=
  let Px := tr p.1
  let Py := tr p.2.1
  let Pz := tr p.2.2
  let Vx := q.1 - p.1
  let Vy := q.2.1 - p.2.1
  let Vz := q.2.2 - p.2.2
  let vv := (Vx * Vx + Vy * Vy + Vz * Vz).toNat
  ⟨vv, (K * (Py * Vz - Pz * Vy) + o.c1x).toNat, (K * (Pz * Vx - Px * Vz) + o.c1y).toNat,
   (K * (Px * Vy - Py * Vx) + o.c1z).toNat,
   (K * Vx + o.c2x).toNat, (K * Vy + o.c2y).toNat, (K * Vz + o.c2z).toNat,
   Nat.mul K.natAbs (sqrtUp vv)⟩

/-- A filament: translated vertex records and segment constants (segment `k` joins vertex `k`
to vertex `k + 1 mod n`). -/
structure Fil where
  /-- vertex records -/
  vts : List Vt
  /-- segment constants -/
  sgs : List Seg

/-- The filament data of the closed polygon `xs` with current numerator `K`. -/
def mkFil (o : Offs) (K : Int) (xs : List (Int × Int × Int)) : Fil :=
  ⟨xs.map mkVt, (List.zip xs (rot1 xs)).map (fun pq => mkSeg o K pq.1 pq.2)⟩

/-- Validity of one segment's integer data: translated coordinates are nonnegative, the
offsets dominate the weights, the segment is nondegenerate, and `sqrtUp` brackets `|V|`. -/
def segOK (o : Offs) (K : Int) (p q : Int × Int × Int) : Bool :=
  let Px := tr p.1
  let Py := tr p.2.1
  let Pz := tr p.2.2
  let Vx := q.1 - p.1
  let Vy := q.2.1 - p.2.1
  let Vz := q.2.2 - p.2.2
  let vv := Vx * Vx + Vy * Vy + Vz * Vz
  decide (0 ≤ Px) && decide (0 ≤ Py) && decide (0 ≤ Pz) &&
  decide ((K * (Py * Vz - Pz * Vy)).natAbs ≤ o.c1x) &&
  decide ((K * (Pz * Vx - Px * Vz)).natAbs ≤ o.c1y) &&
  decide ((K * (Px * Vy - Py * Vx)).natAbs ≤ o.c1z) &&
  decide ((K * Vx).natAbs ≤ o.c2x) && decide ((K * Vy).natAbs ≤ o.c2y) &&
  decide ((K * Vz).natAbs ≤ o.c2z) &&
  decide (o.c1x ≤ o.c1m) && decide (o.c1y ≤ o.c1m) && decide (o.c1z ≤ o.c1m) &&
  decide (o.c2x ≤ o.c2m) && decide (o.c2y ≤ o.c2m) && decide (o.c2z ≤ o.c2m) &&
  decide (0 < vv) && decide (vv ≤ (sqrtUp vv.toNat : Int) * (sqrtUp vv.toNat : Int))

/-- Validity of one filament's data. -/
def filOK (o : Offs) (K : Int) (xs : List (Int × Int × Int)) : Bool :=
  (List.zip xs (rot1 xs)).all (fun pq => segOK o K pq.1 pq.2)

/-! ## One corner -/

/-- Per-vertex result at a corner: `n = |A|²`, the lower bracket `α`, the check, and the Newton
value (the warm start for the next corner). -/
structure VR where
  /-- `n = |A|²` -/
  n : Nat
  /-- lower bracket `α ≤ √n` -/
  al : Nat
  /-- the bracket checks -/
  ok : Bool
  /-- Newton value -/
  g : Nat

/-- Corner data: `D`, `D²`, the scaled translated corner `Xs = 2³² X'` etc., `|Xs|²`,
`λ = 2³² D`. -/
structure CD where
  /-- denominator `D` -/
  D : Nat
  /-- `D²` -/
  D2 : Nat
  /-- `2³² X'` -/
  Xs : Nat
  /-- `2³² Y'` -/
  Ys : Nat
  /-- `2³² Z'` -/
  Zs : Nat
  /-- `|Xs|² + |Ys|² + |Zs|²` -/
  XX : Nat
  /-- `λ = 2³² D` -/
  lam : Nat

/-- `|A|² = |P' D - Xs|²` through `D²|P'|² + |Xs|² - 2D P'·Xs`. -/
def vertN (c : CD) (v : Vt) : Nat :=
  Nat.sub (Nat.add (Nat.mul c.D2 v.pp) c.XX)
    (Nat.mul (Nat.mul 2 c.D) (Nat.add (Nat.add (Nat.mul v.px c.Xs) (Nat.mul v.py c.Ys))
      (Nat.mul v.pz c.Zs)))

/-- The vertex step from a Newton start value `g0` (three steps). -/
def vertStep (c : CD) (v : Vt) (g0 : Nat) : VR :=
  let n := vertN c v
  let r := nst n (nst n (nst n g0))
  let al := Nat.sub r KT
  ⟨n, al, (Nat.ble c.lam (Nat.mul 5 al) && Nat.ble (sq al) n) && Nat.ble n (sq (Nat.add r KT)), r⟩

/-- Cold start: seven Newton steps from `4λ`. -/
def coldStart (c : CD) (v : Vt) : Nat := nstK (vertN c v) 7 (Nat.mul 4 c.lam)

/-- Vertex results of one filament (warm start from `gs` if available). -/
def filVerts (c : CD) : List Vt → List Nat → List VR
  | [], _ => []
  | v :: vs, g :: gs => vertStep c v g :: filVerts c vs gs
  | v :: vs, [] => vertStep c v (coldStart c v) :: filVerts c vs []

/-- Vertex results of all filaments. -/
def allVerts (c : CD) : List Fil → List (List Nat) → List (List VR)
  | [], _ => []
  | f :: fs, g :: gs => filVerts c f.vts g :: allVerts c fs gs
  | f :: fs, [] => filVerts c f.vts [] :: allVerts c fs []

/-- Remainder constants of the cell whose reference corner is the current one. -/
structure RC where
  /-- whether a cell is attached to this corner -/
  doRem : Bool
  /-- `s₀λ = 2³⁰ D` -/
  s0l : Nat
  /-- `⌈r 2³²⌉ D` (cell radius times `λ`) -/
  rBD : Nat
  /-- `λ²` -/
  lam2 : Nat
  /-- `D² 2⁴⁰` -/
  K1 : Nat
  /-- `C_a D² 2⁶⁴` -/
  K2 : Nat
  /-- `8 C_d` -/
  K3 : Nat
  /-- `C_b` numerator -/
  Cbn : Nat

/-- Accumulators of the segment walk. -/
structure Acc where
  /-- `Σ f w1x` -/
  sx : Nat
  /-- `Σ f w1y` -/
  sy : Nat
  /-- `Σ f w1z` -/
  sz : Nat
  /-- `Σ f w2x` -/
  tx : Nat
  /-- `Σ f w2y` -/
  ty : Nat
  /-- `Σ f w2z` -/
  tz : Nat
  /-- `Σ f` -/
  sf : Nat
  /-- remainder sum -/
  rem : Nat
  /-- all checks so far -/
  ok : Bool

/-- Lower bound for the squared (scaled) distance from the corner to the segment, from
`n_a = |A|²`, `n_b = |B|²`, `dvv = |B - A|²`. -/
def d2Low (na nb dvv : Nat) : Nat :=
  cond (Nat.ble (Nat.add na dvv) nb) na
    (cond (Nat.ble (Nat.add nb dvv) na) nb
      (Nat.sub na (cdiv (sq (Nat.sub (Nat.add na dvv) nb)) (Nat.mul 4 dvv))))

/-- Lower bound `L` for `λ² d²` on the whole cell (`d` = distance to the segment). -/
def cellL (r : RC) (d2 : Nat) : Nat :=
  Nat.sub (Nat.sub d2 (cdiv (Nat.mul r.rBD d2) r.s0l)) (Nat.mul r.rBD r.s0l)

/-- Remainder term of one segment (and its check `L > 0`, `λ² ≤ 25 L`). -/
def remTerm (r : RC) (na nb dvv kv : Nat) : Nat × Bool :=
  let L := cellL r (d2Low na nb dvv)
  (cdiv (Nat.mul (Nat.mul kv r.K1) (Nat.add r.K2 (Nat.mul r.Cbn L))) (Nat.mul r.K3 (sq L)),
   Nat.blt 0 L && Nat.ble r.lam2 (Nat.mul 25 L))

/-- One segment `a → b`: kernel factor `f`, accumulation, and (optionally) the remainder. -/
def segStep (D2 D3S : Nat) (r : RC) (acc : Acc) (s : Seg) (a b : VR) : Acc :=
  let ab := Nat.mul a.al b.al
  let dvv := Nat.mul D2 s.vv
  let tc := Nat.add a.n b.n
  let f := Nat.div (Nat.mul (Nat.mul 2 (Nat.add a.al b.al)) D3S)
      (Nat.mul ab (Nat.sub (Nat.add (Nat.add ab ab) tc) dvv))
  let rt := cond r.doRem (remTerm r a.n b.n dvv s.kv) (0, true)
  ⟨Nat.add acc.sx (Nat.mul f s.w1x), Nat.add acc.sy (Nat.mul f s.w1y),
   Nat.add acc.sz (Nat.mul f s.w1z), Nat.add acc.tx (Nat.mul f s.w2x),
   Nat.add acc.ty (Nat.mul f s.w2y), Nat.add acc.tz (Nat.mul f s.w2z),
   Nat.add acc.sf f, Nat.add acc.rem rt.1,
   (((acc.ok && a.ok) && b.ok) && Nat.ble dvv (Nat.add ab tc)) && rt.2⟩

/-- Walk of one filament carrying the first vertex result (which closes the loop). -/
def filWalkAux (D2 D3S : Nat) (r : RC) (first : VR) : Acc → List Seg → List VR → Acc
  | acc, s :: ss, a :: b :: rs =>
    filWalkAux D2 D3S r first (segStep D2 D3S r acc s a b) ss (b :: rs)
  | acc, [s], [a] => segStep D2 D3S r acc s a first
  | acc, _, _ => { acc with ok := false }

/-- Walk of one filament: segment `k` uses the vertex results `k` and `k + 1 mod n`. -/
def filWalk (D2 D3S : Nat) (r : RC) (acc : Acc) (sgs : List Seg) (vs : List VR) : Acc :=
  match vs with
  | v :: _ => filWalkAux D2 D3S r v acc sgs vs
  | [] => { acc with ok := false }

/-- Walk of all filaments. -/
def allWalk (D2 D3S : Nat) (r : RC) : Acc → List Fil → List (List VR) → Acc
  | acc, f :: fs, v :: vs => allWalk D2 D3S r (filWalk D2 D3S r acc f.sgs v) fs vs
  | acc, [], [] => acc
  | acc, _, _ => { acc with ok := false }

/-! ## Exact rationals (for `hel`) -/

/-- A rational as an integer numerator and a natural denominator (not normalised). -/
structure QQ where
  /-- numerator -/
  num : Int
  /-- denominator -/
  den : Nat

/-- Sum. -/
def QQ.add (x y : QQ) : QQ := ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩
/-- Difference. -/
def QQ.sub (x y : QQ) : QQ := ⟨x.num * y.den - y.num * x.den, x.den * y.den⟩
/-- Product. -/
def QQ.mul (x y : QQ) : QQ := ⟨x.num * y.num, x.den * y.den⟩
/-- Integer constant. -/
def QQ.ofInt (a : Int) : QQ := ⟨a, 1⟩
/-- Reciprocal (meaningful for positive rationals). -/
def QQ.inv (x : QQ) : QQ := ⟨Int.ofNat x.den, x.num.toNat⟩

/-- Coefficients of the polar formula of `hel` at radius `ρ`, height `ζ`:
`hel = (A cos φ + B sin φ + G cos 3φ + Dd sin 3φ, -A sin φ + B cos φ + G sin 3φ - Dd cos 3φ,
E sin 2φ + F cos 2φ)`. -/
structure HC where
  /-- `A = (ρ² - 1)/(8ρ)` -/
  A : QQ
  /-- `B = ζ(3 - ρ²)/(8ρ)` -/
  B : QQ
  /-- `G = (ρ² - 1 + 4ζ²)/(8ρ³)` -/
  G : QQ
  /-- `Dd = ζ(5 - 3ρ² - 4ζ²)/(8ρ³)` -/
  Dd : QQ
  /-- `E = (6ρ² - ρ⁴ - 5 + 12ζ²)/(16ρ²)` -/
  E : QQ
  /-- `F = -ζ/(2ρ²)` -/
  F : QQ

/-- The coefficients `HC` from `ρ`, `ζ`. -/
def helCoef (ρ ζ : QQ) : HC :=
  let r2 := ρ.mul ρ
  let z2 := ζ.mul ζ
  let one := QQ.ofInt 1
  let i8 := ((QQ.ofInt 8).mul ρ).inv
  let i83 := (((QQ.ofInt 8).mul r2).mul ρ).inv
  let i16 := ((QQ.ofInt 16).mul r2).inv
  ⟨(r2.sub one).mul i8, (ζ.mul ((QQ.ofInt 3).sub r2)).mul i8,
   ((r2.sub one).add ((QQ.ofInt 4).mul z2)).mul i83,
   (ζ.mul (((QQ.ofInt 5).sub ((QQ.ofInt 3).mul r2)).sub ((QQ.ofInt 4).mul z2))).mul i83,
   (((((QQ.ofInt 6).mul r2).sub (r2.mul r2)).sub (QQ.ofInt 5)).add ((QQ.ofInt 12).mul z2)).mul i16,
   ((QQ.ofInt 0).sub ζ).mul ((QQ.ofInt 2).mul r2).inv⟩

/-- Trigonometric data of a grid line: `cos φ, sin φ, cos 3φ, sin 3φ, sin 2φ, cos 2φ`. -/
structure Trig where
  /-- `cos φ` -/
  c : QQ
  /-- `sin φ` -/
  s : QQ
  /-- `cos 3φ = 4c³ - 3c` -/
  c3 : QQ
  /-- `sin 3φ = 3s - 4s³` -/
  s3 : QQ
  /-- `sin 2φ = 2cs` -/
  s2 : QQ
  /-- `cos 2φ = c² - s²` -/
  c2 : QQ

/-- Trigonometric data from `c`, `s`. -/
def mkTrig (c s : QQ) : Trig :=
  ⟨c, s, ((QQ.ofInt 4).mul ((c.mul c).mul c)).sub ((QQ.ofInt 3).mul c),
   ((QQ.ofInt 3).mul s).sub ((QQ.ofInt 4).mul ((s.mul s).mul s)),
   (QQ.ofInt 2).mul (c.mul s), (c.mul c).sub (s.mul s)⟩

/-- `hel` from the coefficients and the trigonometric data. -/
def helAt (h : HC) (t : Trig) : QQ × QQ × QQ :=
  ((((h.A.mul t.c).add (h.B.mul t.s)).add (h.G.mul t.c3)).add (h.Dd.mul t.s3),
   ((((QQ.ofInt 0).sub (h.A.mul t.s)).add (h.B.mul t.c)).add (h.G.mul t.s3)).sub (h.Dd.mul t.c3),
   (h.E.mul t.s2).add (h.F.mul t.c2))

/-- Floor of `x · S`. -/
def QQ.floorMul (x : QQ) (S : Nat) : Int := Int.fdiv (x.num * S) x.den
/-- Ceiling of `x · S`. -/
def QQ.ceilMul (x : QQ) (S : Nat) : Int := - Int.fdiv (-(x.num * S)) x.den

/-! ## Corner evaluation -/

/-- Output of one corner: all checks, the bound `e ≥ 2⁴⁰ ‖E(corner)‖`, the remainder of the
attached cell (scale `2⁴⁰`, without the `hel` part), and the Newton values. -/
structure CornerOut where
  /-- all checks passed -/
  ok : Bool
  /-- bound on `2⁴⁰ ‖Bh - hel‖` at the corner -/
  e : Nat
  /-- remainder sum of the attached cell -/
  rem : Nat
  /-- warm start for the next corner -/
  gs : List (List Nat)

/-- The integer `x - c·sf` (removing the offset). -/
def unoff (x c sf : Nat) : Int := (x : Int) - (c : Int) * (sf : Int)

/-- Upper bound for `√N` (plus one), from `x₀` by six Newton steps. -/
def sqrtUpFrom (N x0 : Nat) : Nat := Nat.add (nstK N 6 x0) 1

/-- The final assembly of a corner from the accumulators: the error box of `Bh - hel` and the
bound `e`. Inputs: offsets, translated numerators `Xt Yt Zt`, `D`, `λ`, the accumulators, and
`hel` at the corner. Returns `(N ≤ sN², ⌈sN/SE⌉)`. -/
def cornerFinal (o : Offs) (Xt Yt Zt D lam : Nat) (acc : Acc) (h : QQ × QQ × QQ) : Bool × Nat :=
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
  let E1 := Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c1m) sf) lam) (Nat.mul nSeg o.c1m)
  let E2 := Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c2m) sf) lam) (Nat.mul nSeg o.c2m)
  let Rx : Int := (Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Yt Zt) E2)) : Nat)
  let Ry : Int := (Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Zt Xt) E2)) : Nat)
  let Rz : Int := (Nat.add (Nat.mul D E1) (Nat.mul two32 (Nat.mul (Nat.add Xt Yt) E2)) : Nat)
  let SE := Nat.mul D two136
  let mx := nmax (Tx - Rx - h.1.ceilMul SE).natAbs (Tx + Rx - h.1.floorMul SE).natAbs
  let my := nmax (Ty - Ry - h.2.1.ceilMul SE).natAbs (Ty + Ry - h.2.1.floorMul SE).natAbs
  let mz := nmax (Tz - Rz - h.2.2.ceilMul SE).natAbs (Tz + Rz - h.2.2.floorMul SE).natAbs
  let N := Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz)) (sq two40)
  let sN := sqrtUpFrom N (Nat.mul (Nat.add (Nat.add mx my) mz) two40)
  (Nat.ble N (sq sN), cdiv sN SE)

/-- Evaluate one corner `(X, Y, Z)/D` (translated numerators `Xt Yt Zt`), given `hel` there. -/
def cornerEval (o : Offs) (fs : List Fil) (Xt Yt Zt D : Nat) (h : QQ × QQ × QQ) (r : RC)
    (gs : List (List Nat)) : CornerOut :=
  let D2 := Nat.mul D D
  let Xs := Nat.mul Xt two32
  let Ys := Nat.mul Yt two32
  let Zs := Nat.mul Zt two32
  let lam := Nat.mul D two32
  let c : CD := ⟨D, D2, Xs, Ys, Zs, Nat.add (Nat.add (sq Xs) (sq Ys)) (sq Zs), lam⟩
  let vs := allVerts c fs gs
  let acc := allWalk D2 (Nat.mul (Nat.mul D2 D) two136) r ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ fs vs
  let fin := cornerFinal o Xt Yt Zt D lam acc h
  ⟨((acc.ok && fin.1) && Nat.ble (Nat.mul 1000 KT) lam) && (!r.doRem || Nat.ble r.rBD r.s0l),
   fin.2, acc.rem, vs.map (fun l => l.map VR.g)⟩

/-! ## Faces and grids -/

/-- A face of the fundamental frontier piece: `kind` `0`, `1` the cylinders
`ρ = 199/181`, `161/181` (`w = ζ`), `2`, `3` the planes `ζ = ±a` (`w = ρ`),
`a = 3420/32761`; the `w`-grid `wn[j]/wd`; and bounds `H_φ = h1n/h1d`, `H_w = h2n/h2d` for the
second derivatives of `⟨n, hel⟩` along the face. -/
structure Face where
  /-- face kind -/
  kind : Nat
  /-- common denominator of the `w`-grid -/
  wd : Nat
  /-- numerators of the `w`-grid (increasing) -/
  wn : List Int
  /-- `H_φ` numerator -/
  h1n : Nat
  /-- `H_φ` denominator -/
  h1d : Nat
  /-- `H_w` numerator -/
  h2n : Nat
  /-- `H_w` denominator -/
  h2d : Nat

/-- Radius numerator of a cylinder face. -/
def cylR (kind : Nat) : Int := if kind = 0 then 199 else 161

/-- `(ρ, ζ)` of the grid value `w = wn/wd` on a face. -/
def faceRZ (F : Face) (wn : Int) : QQ × QQ :=
  if F.kind < 2 then (⟨cylR F.kind, 181⟩, ⟨wn, F.wd⟩)
  else (⟨wn, F.wd⟩, ⟨if F.kind = 2 then 3420 else -3420, 32761⟩)

/-- The corner `(m, w = wn/wd)`: translated numerators, denominator, and the check that the
translated numerators are nonnegative. With `t = m/4096`, `cos φ = (q² - m²)/(q² + m²)`,
`sin φ = 2mq/(q² + m²)`. -/
def cornerXYZ (F : Face) (m : Nat) (wn : Int) : (Nat × Nat × Nat × Nat) × Bool :=
  let q : Int := qT
  let mi : Int := m
  let cd : Int := q * q + mi * mi
  let cn : Int := q * q - mi * mi
  let sn : Int := 2 * mi * q
  let rz := faceRZ F wn
  let D : Int := rz.1.den * cd * rz.2.den
  let X := rz.1.num * cn * rz.2.den + 4 * D
  let Y := rz.1.num * sn * rz.2.den + 4 * D
  let Z := rz.2.num * rz.1.den * cd + 4 * D
  ((X.toNat, Y.toNat, Z.toNat, D.toNat), decide (0 ≤ X) && decide (0 ≤ Y) && decide (0 ≤ Z))

/-- `cos φ`, `sin φ` of the grid line `m` as rationals. -/
def trigOf (m : Nat) : Trig :=
  let q : Int := qT
  let mi : Int := m
  let cd : Nat := (q * q + mi * mi).toNat
  mkTrig ⟨q * q - mi * mi, cd⟩ ⟨2 * mi * q, cd⟩

/-- Remainder constants for the cell `(m → m', wn → wn')` attached to a corner with
denominator `D`, and the `hel` part of the remainder (scale `2⁴⁰`). Cell geometry:
`Δφ ≤ 2(m' - m)q/(q² + m²)`, `ρ_max` (`R` or `wn'/wd`), `Δw = (wn' - wn)/wd`. -/
def cellRC (F : Face) (m m' : Nat) (wn wn' : Int) (D : Nat) : RC × Nat :=
  let a1 := 2 * (m' - m) * qT
  let b1 := qT * qT + m * m
  let a2 : Nat := if F.kind < 2 then (cylR F.kind).toNat else wn'.toNat
  let b2 : Nat := if F.kind < 2 then 181 else F.wd
  let a3 : Nat := (wn' - wn).toNat
  let b3 : Nat := F.wd
  let rB := cdiv ((a2 * a1 * b3 + a3 * b1 * b2) * two32) (b1 * b2 * b3)
  let Cd := b1 * b1 * (b2 * b2) * (b3 * b3)
  let Can := 6 * (a1 * a1 * (a2 * a2) * (b3 * b3) + a3 * a3 * (b1 * b1) * (b2 * b2))
  let Cbn := 10 * (a1 * a1) * a2 * b2 * (b3 * b3)
  let hterm := cdiv ((a1 * a1 * F.h1n * F.h2d * (b3 * b3) + a3 * a3 * F.h2n * F.h1d * (b1 * b1))
      * two40) (8 * (b1 * b1) * (b3 * b3) * F.h1d * F.h2d)
  (⟨true, D * two30, rB * D, sq (D * two32), D * D * two40, Can * (D * D) * two64, 8 * Cd, Cbn⟩,
   hterm)

/-- The empty remainder (corner without attached cell). -/
def noRC : RC := ⟨false, 0, 0, 0, 0, 0, 1, 0⟩

/-- Corner results along one grid line `m` over the `w`-values `ws` (with the precomputed `hel`
coefficients `hcs`), with remainder data towards the next line `m'` if present. Each entry:
`(ok, e, rem + hterm)`. -/
def lineGo (o : Offs) (fs : List Fil) (F : Face) (m : Nat) (m' : Option Nat) (t : Trig) :
    List Int → List HC → List (List Nat) → List (Bool × Nat × Nat)
  | wn :: ws, hc :: hcs, gs =>
    let cx := cornerXYZ F m wn
    let xyz := cx.1
    let rh : RC × Nat := match m', ws with
      | some m1, wn' :: _ => cellRC F m m1 wn wn' xyz.2.2.2
      | _, _ => (noRC, 0)
    let co := cornerEval o fs xyz.1 xyz.2.1 xyz.2.2.1 xyz.2.2.2 (helAt hc t) rh.1 gs
    (co.ok && cx.2, co.e, Nat.add co.rem rh.2) :: lineGo o fs F m m' t ws hcs co.gs
  | _, _, _ => []

/-- The precomputed `hel` coefficients along the `w`-grid of a face. -/
def faceHC (F : Face) : List HC := F.wn.map (fun wn => let rz := faceRZ F wn; helCoef rz.1 rz.2)

/-- Corner results along the grid line `m`. -/
def lineOut (o : Offs) (fs : List Fil) (F : Face) (hcs : List HC) (m : Nat) (m' : Option Nat) :
    List (Bool × Nat × Nat) :=
  lineGo o fs F m m' (trigOf m) F.wn hcs []

/-- Cell checks between two consecutive lines: `max e + rem ≤ η` for every cell. -/
def cellsOK : List (Bool × Nat × Nat) → List (Bool × Nat × Nat) → Bool
  | a :: a' :: as, b :: b' :: bs =>
    (((a.1 && a'.1) && (b.1 && b'.1)) &&
      Nat.ble (Nat.add (nmax (nmax a.2.1 a'.2.1) (nmax b.2.1 b'.2.1)) a.2.2) etaFp) &&
      cellsOK (a' :: as) (b' :: bs)
  | [_], [_] => true
  | _, _ => false

/-- Check all cells between consecutive lines of the list (given the output of the first
line). -/
def checkLines (o : Offs) (fs : List Fil) (F : Face) (hcs : List HC) :
    List (Bool × Nat × Nat) → Nat → List Nat → Bool
  | prev, m0, m :: m' :: rest =>
    let cur := lineOut o fs F hcs m (some m')
    (Nat.blt m0 m && cellsOK prev cur) && checkLines o fs F hcs cur m (m' :: rest)
  | prev, m0, [m] => Nat.blt m0 m && cellsOK prev (lineOut o fs F hcs m none)
  | _, _, [] => false

/-- Strictly increasing list of integers. -/
def incr : List Int → Bool
  | a :: b :: r => decide (a < b) && incr (b :: r)
  | _ => true

/-- Validity of a face: positive denominator, increasing `w`-grid with endpoints exactly the
face range (`[-a, a]` for the cylinders, `[161/181, 199/181]` for the planes). -/
def faceOK (F : Face) : Bool :=
  let wd : Int := F.wd
  decide (0 < F.wd) && incr F.wn &&
  (match F.wn.head?, F.wn.getLast? with
   | some lo, some hi =>
     if F.kind < 2 then decide (lo * 32761 = -3420 * wd) && decide (3420 * wd = hi * 32761)
     else decide (lo * 181 = 161 * wd) && decide (199 * wd = hi * 181)
   | _, _ => false) &&
  decide (F.kind < 4) && decide (0 < F.h1d) && decide (0 < F.h2d)

/-- Check the cells of a chunk `m₀ < m₁ < … < m_k` of grid lines (`k ≥ 1`) of face `F`. -/
def checkChunk (o : Offs) (fs : List Fil) (F : Face) : List Nat → Bool
  | m :: m' :: rest =>
    let hcs := faceHC F
    faceOK F && checkLines o fs F hcs (lineOut o fs F hcs m (some m')) m (m' :: rest)
  | _ => false

end PlasmaLean.Design.PolygonCoil
