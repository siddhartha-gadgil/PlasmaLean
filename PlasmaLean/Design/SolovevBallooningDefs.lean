/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Data.Int.Basic
public meta import Lean

/-!
# Ballooning certificate of the reactor Solov'ev equilibrium: computational layer

This module contains only **computable** definitions (integers, lists, booleans); the real
semantics and all soundness proofs are in `SolovevBallooningSound`. Keeping this layer light
lets the kernel-checked cell modules (`SolovevBallooningCells*`) build in parallel with the
analytic part.

* `Bl`: fixed-point balls `|2³² x − m| ≤ r` with a validity flag, with arithmetic written in
  explicit `Int`/`Nat` operations (fast kernel reduction).
* `Tm`: polynomial expression trees with interval value (`ieval`), first-order (`idual`) and
  second-order (`ihd`) forward-mode evaluation.
* The scaled ballooning coefficient trees of the reactor surface `ψ̃ = s²` over the variables
  `0 x = cos t, 1 y = sin t, 2 R, 3 r = √2, 4 1/R, 5 1/|B|², 6 s, 7 τ, 8 κ = 2/(1 + τ²)`
  (`7, 8` only for the chart derivatives). The surface label `s` is a VARIABLE, so a single
  tree describes all surfaces, and the trees are written so that no `1/s` occurs (scaled
  secular variable `σ̃ = s σ`).
* `etree k`: the coefficients `e₀, …, e₆` of the numerator `N̂(σ̃)` of the Riccati defect.
* `boxOK`/`axisOK`: the check of one box `[τ₀, τ₁] × [s₀, s₁]` of the `(τ, s)` plane (exact
  corner values, second-derivative bounds in `τ` and in `s` over the box, Pólya test at the
  corners), and of a box `[τ₀, τ₁] × [0, s₁]` touching the magnetic axis; `hessOK`/`cornerOK`:
  the same check split into the box part and separately proved (shared) corner tests.
* `Cover`: binary-subdivision certificates of a rectangle, built from an untrusted plan by the
  `meta` tactic `ballooning_cover`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

/-! ## Fixed-point balls -/

/-- A fixed-point ball: if `ok` then `|2³² x − m| ≤ r`. -/
structure Bl where
  /-- Scaled midpoint. -/
  m : ℤ
  /-- Scaled radius. -/
  r : ℕ
  /-- Validity flag (an invalid ball contains every real number). -/
  ok : Bool

namespace Bl

/-- The ball of the integer `n` (exact). -/
@[expose] def ofInt (n : ℤ) : Bl := ⟨Int.mul n 4294967296, 0, true⟩

/-- The ball of the rational `p / q` (valid for `q > 0`). -/
@[expose] def ofFrac (p q : ℤ) : Bl := ⟨Int.ediv (Int.mul p 4294967296) q, 1, decide (0 < q)⟩

/-- The zero ball. -/
@[expose] def zero : Bl := ⟨0, 0, true⟩

/-- Sum. -/
@[expose] def add (a b : Bl) : Bl := ⟨Int.add a.m b.m, Nat.add a.r b.r, a.ok && b.ok⟩

/-- Negation. -/
@[expose] def neg (a : Bl) : Bl := ⟨Int.neg a.m, a.r, a.ok⟩

/-- Difference. -/
@[expose] def sub (a b : Bl) : Bl := ⟨Int.sub a.m b.m, Nat.add a.r b.r, a.ok && b.ok⟩

/-- Doubling (exact). -/
@[expose] def dbl (a : Bl) : Bl := ⟨Int.add a.m a.m, Nat.add a.r a.r, a.ok⟩

/-- Product, rounded outward. -/
@[expose] def mul (a b : Bl) : Bl :=
  ⟨Int.ediv (Int.mul a.m b.m) 4294967296,
    Nat.add (Nat.div (Nat.add (Nat.add (Nat.mul a.m.natAbs b.r) (Nat.mul a.r b.m.natAbs))
      (Nat.mul a.r b.r)) 4294967296) 2,
    a.ok && b.ok⟩

/-- Square, rounded outward. -/
@[expose] def sq (a : Bl) : Bl :=
  ⟨Int.ediv (Int.mul a.m a.m) 4294967296,
    Nat.add (Nat.div (Nat.add (Nat.mul (Nat.add a.m.natAbs a.m.natAbs) a.r) (Nat.mul a.r a.r))
      4294967296) 2,
    a.ok⟩

/-- Scaled lower end. -/
@[expose] def lo (a : Bl) : ℤ := Int.sub a.m a.r

/-- Scaled upper end. -/
@[expose] def hi (a : Bl) : ℤ := Int.add a.m a.r

/-- Scaled upper bound of the absolute value. -/
@[expose] def mag (a : Bl) : ℕ := Nat.add a.m.natAbs a.r

/-- The ball containing the scaled interval `[l, h]`. -/
@[expose] def ofLoHi (l h : ℤ) (ok : Bool) : Bl :=
  ⟨Int.ediv (Int.add l h) 2, Nat.add (Nat.div (Int.sub h l).natAbs 2) 2, ok⟩

/-- Reciprocal (valid only for balls of strictly positive numbers). -/
@[expose] def inv (a : Bl) : Bl :=
  ofLoHi (Int.ediv 18446744073709551616 a.hi) (Int.add (Int.ediv 18446744073709551616 a.lo) 1)
    (a.ok && decide (0 < a.lo))

/-- Newton iteration for the integer square root (untrusted: results are checked). -/
@[expose] def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | k + 1, n, g => if (g + n / g) / 2 < g then isqrtAux k n ((g + n / g) / 2) else g

/-- Approximate integer square root (untrusted: results are checked by squaring). -/
@[expose] def isqrt (n : ℕ) : ℕ := isqrtAux 64 n (n / 4294967296 + 4294967296)

/-- Square root (valid only for balls of nonnegative numbers; both ends are checked). -/
@[expose] def sqrt (a : Bl) : Bl :=
  ofLoHi (if (isqrt (a.lo * 4294967296).toNat : ℤ) * (isqrt (a.lo * 4294967296).toNat : ℤ) ≤
        a.lo * 4294967296 then (isqrt (a.lo * 4294967296).toNat : ℤ) else 0)
    ((isqrt (a.hi * 4294967296).toNat : ℤ) + 1)
    (a.ok && decide (0 ≤ a.lo) && decide (a.hi * 4294967296 ≤
      ((isqrt (a.hi * 4294967296).toNat : ℤ) + 1) * ((isqrt (a.hi * 4294967296).toNat : ℤ) + 1)))

end Bl

/-! ## Expression trees -/

/-- Polynomial expression trees over numbered real variables, with rational constants `p/q`. -/
inductive Tm where
  /-- The constant `p / q`. -/
  | c (p q : ℤ)
  /-- Variable number `i`. -/
  | v (i : ℕ)
  /-- Sum. -/
  | add (a b : Tm)
  /-- Product. -/
  | mul (a b : Tm)
  /-- Negation. -/
  | neg (a : Tm)
  /-- Square. -/
  | sq (a : Tm)

namespace Tm

/-- Difference. -/
@[expose] def sub (a b : Tm) : Tm := add a (neg b)

/-- Ball value of a tree. -/
@[expose] def ieval (I : ℕ → Bl) : Tm → Bl
  | c p q => Bl.ofFrac p q
  | v i => I i
  | add a b => (a.ieval I).add (b.ieval I)
  | mul a b => (a.ieval I).mul (b.ieval I)
  | neg a => (a.ieval I).neg
  | sq a => (a.ieval I).sq

/-- Ball value and derivative of a tree (forward mode). -/
@[expose] def idual (I I' : ℕ → Bl) : Tm → Bl × Bl
  | c p q => (Bl.ofFrac p q, Bl.zero)
  | v i => (I i, I' i)
  | add a b => let A := a.idual I I'; let B := b.idual I I'; (A.1.add B.1, A.2.add B.2)
  | mul a b => let A := a.idual I I'; let B := b.idual I I';
      (A.1.mul B.1, (A.2.mul B.1).add (A.1.mul B.2))
  | neg a => let A := a.idual I I'; (A.1.neg, A.2.neg)
  | sq a => let A := a.idual I I'; (A.1.sq, (A.1.mul A.2).dbl)

/-- Ball value, first and second derivative of a tree (second-order forward mode). -/
@[expose] def ihd (I I' I'' : ℕ → Bl) : Tm → Bl × Bl × Bl
  | c p q => (Bl.ofFrac p q, Bl.zero, Bl.zero)
  | v i => (I i, I' i, I'' i)
  | add a b => let A := a.ihd I I' I''; let B := b.ihd I I' I'';
      (A.1.add B.1, A.2.1.add B.2.1, A.2.2.add B.2.2)
  | mul a b => let A := a.ihd I I' I''; let B := b.ihd I I' I'';
      (A.1.mul B.1, (A.2.1.mul B.1).add (A.1.mul B.2.1),
        ((A.2.2.mul B.1).add (A.2.1.mul B.2.1).dbl).add (A.1.mul B.2.2))
  | neg a => let A := a.ihd I I' I''; (A.1.neg, A.2.1.neg, A.2.2.neg)
  | sq a => let A := a.ihd I I' I'';
      (A.1.sq, (A.1.mul A.2.1).dbl, (A.2.1.sq.add (A.1.mul A.2.2)).dbl)

/-- Symbolic derivative tree, given derivative trees `dv i` of the variables. -/
@[expose] def diff (dv : ℕ → Tm) : Tm → Tm
  | c _ _ => c 0 1
  | v i => dv i
  | add a b => add (diff dv a) (diff dv b)
  | mul a b => add (mul (diff dv a) b) (mul a (diff dv b))
  | neg a => neg (diff dv a)
  | sq a => mul (c 2 1) (mul a (diff dv a))

end Tm

open Tm

/-! ## The scaled coefficient trees -/

/-- `x = cos t`. -/ @[expose] def tX : Tm := v 0
/-- `y = sin t`. -/ @[expose] def tY : Tm := v 1
/-- `R`. -/ @[expose] def tR : Tm := v 2
/-- `r = √2`. -/ @[expose] def tr : Tm := v 3
/-- `1/R`. -/ @[expose] def tiR : Tm := v 4
/-- `1/|B|²`. -/ @[expose] def tiB : Tm := v 5
/-- The surface label `s` (`ψ̃ = s²`). -/ @[expose] def tS : Tm := v 6
/-- The chart parameter `τ`. -/ @[expose] def tT : Tm := v 7
/-- `κ = 2/(1 + τ²)`. -/ @[expose] def tK : Tm := v 8

/-- `ẑ = z/s = √2 x/R`. -/
@[expose] def tzh : Tm := mul tr (mul tX tiR)
/-- `Ŵ = W/s = s ẑ² + 2 y` (`W = z² + R² − L²`, using `R² = L² + 2 s y`). -/
@[expose] def tWh : Tm := add (mul tS (sq tzh)) (mul (c 2 1) tY)
/-- `B_R = −c R z = −c s R ẑ` (`c = A/L² = 7/400`). -/
@[expose] def tBR : Tm := neg (mul (c 7 400) (mul tS (mul tR tzh)))
/-- `B_φ = F/R`. -/
@[expose] def tBP : Tm := mul (c 50 1) tiR
/-- `B_z = c W = c s Ŵ`. -/
@[expose] def tBZ : Tm := mul (c 7 400) (mul tS tWh)
/-- `(∇√ψ̃)_R = R Ŵ/2`. -/
@[expose] def tgsR : Tm := mul (c 1 2) (mul tR tWh)
/-- `(∇√ψ̃)_z = R x √2/2`. -/
@[expose] def tgsZ : Tm := mul (c 1 2) (mul (mul tR tX) tr)
/-- `s (∇t)_R = x (L² + s y)/R`. -/
@[expose] def tgtR : Tm := mul (mul tX (add (c 100 1) (mul tS tY))) tiR
/-- `s (∇t)_z = −R y √2/2`. -/
@[expose] def tgtZ : Tm := neg (mul (c 1 2) (mul (mul tR tY) tr))
/-- `1/R³`. -/
@[expose] def tiR3 : Tm := mul tiR (sq tiR)
/-- Winding rate `F L²/(√2 A) = 10000 √2/7`. -/
@[expose] def trate : Tm := mul (c 10000 7) tr
/-- `s k₀`, radial (`k₀ = ∇φ − ∂ₜΦ ∇t`, `∂ₜΦ = −rate/R³`). -/
@[expose] def tkR : Tm := mul (mul trate tiR3) tgtR
/-- `s k₀`, toroidal. -/
@[expose] def tkP : Tm := mul tS tiR
/-- `s k₀`, vertical. -/
@[expose] def tkZ : Tm := mul (mul trate tiR3) tgtZ
/-- `ℓ = |λ| = 200 √2/(7 R)`. -/
@[expose] def tell : Tm := mul (c 200 7) (mul tr tiR)
/-- `(DB · B)_R = −2c² s R y − F²/R³`. -/
@[expose] def tGR : Tm := neg (add (mul (c 49 80000) (mul tS (mul tR tY))) (mul (c 2500 1) tiR3))
/-- `(DB · B)_z = 2 c² s ẑ (s Ŵ − R²)`. -/
@[expose] def tGZ : Tm := mul (c 49 80000) (mul (mul tS tzh) (sub (mul tS tWh) (sq tR)))
/-- `|B|²`. -/
@[expose] def tB2 : Tm := add (add (sq tBR) (sq tBP)) (sq tBZ)
/-- `1/(ℓ |B|²) = 7 √2 R/(400 |B|²)`. -/
@[expose] def tden : Tm := mul (c 7 400) (mul (mul tr tR) tiB)
/-- `p̂₀ = s² |k₀|²/(ℓ|B|²)`. -/
@[expose] def tp0 : Tm := mul (add (add (sq tkR) (sq tkP)) (sq tkZ)) tden
/-- `p̂₁ = −2 s k₀·∇√ψ̃/(ℓ|B|²)`. -/
@[expose] def tp1 : Tm := mul (mul (c (-2) 1) (add (mul tkR tgsR) (mul tkZ tgsZ))) tden
/-- `p̂₂ = |∇√ψ̃|²/(ℓ|B|²)`. -/
@[expose] def tp2 : Tm := mul (add (sq tgsR) (sq tgsZ)) tden
/-- `(B × b)·g` for `b = (bR, bP, bZ)` and a meridional `g = (gR, 0, gZ)`. -/
@[expose] def tcross (bR bP bZ gR gZ : Tm) : Tm :=
  add (mul (sub (mul tBP bZ) (mul tBZ bP)) gR) (mul (sub (mul tBR bP) (mul tBP bR)) gZ)
/-- `s q₀ = −6 c ℓ (B × s k₀ · DB B)/|B|⁴`. -/
@[expose] def tsq0 : Tm :=
  neg (mul (mul (c 21 200) tell) (mul (tcross tkR tkP tkZ tGR tGZ) (sq tiB)))
/-- `q₁ = 6 c ℓ (B × ∇√ψ̃ · DB B)/|B|⁴`. -/
@[expose] def tq1 : Tm :=
  mul (mul (c 21 200) tell) (mul (mul tBP (sub (mul tgsZ tGR) (mul tgsR tGZ))) (sq tiB))
/-- `d̂ = s σ' = 3 rate s y/R⁵`. -/
@[expose] def td : Tm := mul (mul (mul (c 3 1) trate) (mul tY tS)) (mul tiR (sq (sq tiR)))
/-- `β̂ = (|B|² − 25)/s = c² s (2 x² + Ŵ²) − 50 y/R²`. -/
@[expose] def tbeta : Tm :=
  sub (mul (c 49 160000) (mul tS (add (mul (c 2 1) (sq tX)) (sq tWh))))
    (mul (c 50 1) (mul tY (sq tiR)))

/-! ## The certificate profiles -/

/-- Horner tree `Σ aₖ yᵏ` with tree coefficients. -/
@[expose] def ptree : List Tm → Tm → Tm
  | [], _ => c 0 1
  | a :: l, y => add a (mul y (ptree l y))

/-- Certificate data: `δ` (the constant of `a = δ + 3 β̂/|B|²`) and the coefficient trees of
`A₀, A₁, A₂` in `y` (trees in `s` and `√2` only). The flux is
`Φ = σ̃ a + x A₀(y) + x A₁(y) ρ(σ̃) + A₂(y) ν(σ̃)`, `ρ = w²/(w² + σ̃²)`, `ν = w σ̃/(w² + σ̃²)`,
`w = 2`. -/
structure Data where
  /-- The constant part `δ` of `a`. -/
  dl : Tm
  /-- Coefficients of `A₀`. -/
  A0 : List Tm
  /-- Coefficients of `A₁`. -/
  A1 : List Tm
  /-- Coefficients of `A₂`. -/
  A2 : List Tm

/-- `f₀ = x A₀(y)`. -/ @[expose] def tf0 (D : Data) : Tm := mul tX (ptree D.A0 tY)
/-- `f₁ = x A₁(y)`. -/ @[expose] def tf1 (D : Data) : Tm := mul tX (ptree D.A1 tY)
/-- `f₂ = A₂(y)`. -/ @[expose] def tf2 (D : Data) : Tm := ptree D.A2 tY

/-- Derivative trees of `x, y` along `t` (`x' = −y`, `y' = x`; `R, s, √2` handled elsewhere). -/
@[expose] def dvT : ℕ → Tm
  | 0 => neg tY
  | 1 => tX
  | _ => c 0 1

/-- The twelve base coefficient trees:
`p̂₀, p̂₁, p̂₂, A = s q₀ − f₀', g₁ = f₁', g₂ = f₂', d̂, a, f₀, f₁, f₂, s`. -/
@[expose] def baseT (D : Data) : ℕ → Tm
  | 0 => tp0
  | 1 => tp1
  | 2 => tp2
  | 3 => sub tsq0 (diff dvT (tf0 D))
  | 4 => diff dvT (tf1 D)
  | 5 => diff dvT (tf2 D)
  | 6 => td
  | 7 => add D.dl (mul (c 3 1) (mul tiB tbeta))
  | 8 => tf0 D
  | 9 => tf1 D
  | 10 => tf2 D
  | 11 => tS
  | _ => c 0 1

/-! ## The numerator polynomial

With `W = w² + σ̃²` (`w = 2`), the scaled Riccati defect is `N̂(σ̃)/(Π W²)` with
`N̂ = Π · I − s G²`, `Π = p̂₀ + p̂₁ σ̃ + p̂₂ σ̃²`,
`I = A W² − (g₁ w² + g₂ w σ̃) W − d̂ (a W² − 2 w² σ̃ f₁ + w (w² − σ̃²) f₂) = Σ Iⱼ σ̃ʲ` and
`G = (σ̃ a + f₀) W + w² f₁ + w σ̃ f₂ = Σ Gⱼ σ̃ʲ`, over the base variables
`0 p̂₀, 1 p̂₁, 2 p̂₂, 3 A, 4 g₁, 5 g₂, 6 d̂, 7 a, 8 f₀, 9 f₁, 10 f₂, 11 s`. -/

/-- The coefficients `Iⱼ` of `I`. -/
@[expose] def tin : ℕ → Tm
  | 0 => sub (mul (c 16 1) (sub (sub (v 3) (v 4)) (mul (v 6) (v 7))))
      (mul (c 8 1) (mul (v 6) (v 10)))
  | 1 => add (neg (mul (c 8 1) (v 5))) (mul (c 8 1) (mul (v 6) (v 9)))
  | 2 => add (mul (c 4 1) (sub (mul (c 2 1) (sub (v 3) (mul (v 6) (v 7)))) (v 4)))
      (mul (c 2 1) (mul (v 6) (v 10)))
  | 3 => neg (mul (c 2 1) (v 5))
  | 4 => sub (v 3) (mul (v 6) (v 7))
  | _ => c 0 1

/-- The coefficients `Gⱼ` of `G`. -/
@[expose] def tgg : ℕ → Tm
  | 0 => mul (c 4 1) (add (v 8) (v 9))
  | 1 => add (mul (c 4 1) (v 7)) (mul (c 2 1) (v 10))
  | 2 => v 8
  | 3 => v 7
  | _ => c 0 1

/-- The coefficient `e_k = Σ_{i+j=k} Πᵢ Iⱼ − s Σ_{i+j=k} Gᵢ Gⱼ` of `N̂`. -/
@[expose] def etree : ℕ → Tm
  | 0 => sub (mul (v 0) (tin 0)) (mul (v 11) (sq (tgg 0)))
  | 1 => sub (add (mul (v 0) (tin 1)) (mul (v 1) (tin 0)))
      (mul (v 11) (mul (c 2 1) (mul (tgg 0) (tgg 1))))
  | 2 => sub (add (add (mul (v 0) (tin 2)) (mul (v 1) (tin 1))) (mul (v 2) (tin 0)))
      (mul (v 11) (add (mul (c 2 1) (mul (tgg 0) (tgg 2))) (sq (tgg 1))))
  | 3 => sub (add (add (mul (v 0) (tin 3)) (mul (v 1) (tin 2))) (mul (v 2) (tin 1)))
      (mul (v 11) (mul (c 2 1) (add (mul (tgg 0) (tgg 3)) (mul (tgg 1) (tgg 2)))))
  | 4 => sub (add (add (mul (v 0) (tin 4)) (mul (v 1) (tin 3))) (mul (v 2) (tin 2)))
      (mul (v 11) (add (mul (c 2 1) (mul (tgg 1) (tgg 3))) (sq (tgg 2))))
  | 5 => sub (add (mul (v 1) (tin 4)) (mul (v 2) (tin 3)))
      (mul (v 11) (mul (c 2 1) (mul (tgg 2) (tgg 3))))
  | 6 => sub (mul (v 2) (tin 4)) (mul (v 11) (sq (tgg 3)))
  | _ => c 0 1

/-! ## Chart and its derivatives

The half circle `x ≥ 0` is `τ ↦ (x, y) = ((1 − τ²)/(1 + τ²), 2τ/(1 + τ²))`, `τ ∈ [−1, 1]`;
`R = √(L² + 2 s y)`. Along `τ` the variables satisfy `x' = −κ y`, `y' = κ x`,
`R' = s κ x/R`, `(1/R)' = −R'/R²`, `(1/|B|²)' = −(|B|²)'/|B|⁴`, `τ' = 1`, `κ' = −τ κ²`;
along `s`: `R' = y/R`, `(1/R)' = −y/R³`, `s' = 1`. -/

/-- `τ`-derivative trees of the variables other than `1/|B|²`. -/
@[expose] def Dt0 : ℕ → Tm
  | 0 => neg (mul tK tY)
  | 1 => mul tK tX
  | 2 => mul (mul tS tK) (mul tX tiR)
  | 4 => neg (mul (mul (mul tS tK) (mul tX tiR)) (sq tiR))
  | 7 => c 1 1
  | 8 => neg (mul tT (sq tK))
  | _ => c 0 1

/-- `τ`-derivative trees of all variables. -/
@[expose] def Dt : ℕ → Tm
  | 5 => neg (mul (diff Dt0 tB2) (sq tiB))
  | i => Dt0 i

/-- `s`-derivative trees of the variables other than `1/|B|²`. -/
@[expose] def Ds0 : ℕ → Tm
  | 2 => mul tY tiR
  | 4 => neg (mul tY tiR3)
  | 6 => c 1 1
  | _ => c 0 1

/-- `s`-derivative trees of all variables. -/
@[expose] def Ds : ℕ → Tm
  | 5 => neg (mul (diff Ds0 tB2) (sq tiB))
  | i => Ds0 i

/-- A ball assignment of the nine variables. -/
@[expose] def envI (x y R r iR iB s t k : Bl) : ℕ → Bl
  | 0 => x
  | 1 => y
  | 2 => R
  | 3 => r
  | 4 => iR
  | 5 => iB
  | 6 => s
  | 7 => t
  | 8 => k
  | _ => Bl.zero

/-- Ball of `√2`. -/
@[expose] def sqrt2B : Bl := (Bl.ofInt 2).sqrt

/-- Denominator of the `τ` grid (`τ = t/NT`). -/
@[expose] def NT : ℤ := 4096

/-- Denominator of the `s` grid (`s = n/NS`). -/
@[expose] def NS : ℤ := 1024

/-- The ball of the scaled interval `[p₀/q, p₁/q]`. -/
@[expose] def ivHull (p0 p1 q : ℤ) : Bl :=
  Bl.ofLoHi (Bl.ofFrac p0 q).lo (Bl.ofFrac p1 q).hi (decide (0 < q) && decide (p0 ≤ p1))

/-- Ball of `κ = 2/(1 + τ²)` from a ball `T ∋ τ`. -/
@[expose] def kapB (T : Bl) : Bl := (Bl.ofInt 2).mul ((Bl.ofInt 1).add T.sq).inv

/-- Ball of `R = √(L² + 2 s y)` from balls `T ∋ τ`, `S ∋ s` (`y = κ τ`). -/
@[expose] def RB (T S : Bl) : Bl :=
  ((Bl.ofInt 100).add ((Bl.ofInt 2).mul (S.mul ((kapB T).mul T)))).sqrt

/-- The variables over a box with the slot `1/|B|²` set to `0`. -/
@[expose] def boxVars0 (T S : Bl) : ℕ → Bl :=
  envI ((kapB T).sub (Bl.ofInt 1)) ((kapB T).mul T) (RB T S) sqrt2B (RB T S).inv Bl.zero S T
    (kapB T)

/-- The variables over a box, from balls `T ∋ τ`, `S ∋ s` (`x = κ − 1`, `y = κ τ`). -/
@[expose] def boxVars (T S : Bl) : ℕ → Bl :=
  envI ((kapB T).sub (Bl.ofInt 1)) ((kapB T).mul T) (RB T S) sqrt2B (RB T S).inv
    (tB2.ieval (boxVars0 T S)).inv S T (kapB T)

/-- The variables at the grid point `τ = t/NT`, `s = n/NS` (narrow balls). -/
@[expose] def pointVars (t n : ℤ) : ℕ → Bl :=
  boxVars (Bl.ofFrac t NT) (Bl.ofFrac n NS)

/-- Ball list of the base coefficients for given variable balls. -/
@[expose] def baseVals (D : Data) (V : ℕ → Bl) : List Bl :=
  (List.range 12).map fun j => (baseT D j).ieval V

/-- Ball lookup in a list. -/
@[expose] def lk (l : List Bl) (j : ℕ) : Bl := l.getD j Bl.zero

/-- Balls of `e₀, …, e₆` at a grid point. -/
@[expose] def eCorner (D : Data) (t n : ℤ) : List Bl :=
  (List.range 7).map fun k => (etree k).ieval (lk (baseVals D (pointVars t n)))

/-- Balls of the second derivatives of `e₀, …, e₆` along the direction with derivative trees
`Dv`, over the box with variable balls `V`. -/
@[expose] def e2 (D : Data) (Dv : ℕ → Tm) (V : ℕ → Bl) : List Bl :=
  let V1 := (List.range 9).map fun i => (Dv i).ieval V
  let V2 := (List.range 9).map fun i => ((Dv i).idual V (lk V1)).2
  let B := (List.range 12).map fun j => (baseT D j).ihd V (lk V1) (lk V2)
  (List.range 7).map fun k =>
    ((etree k).ihd (fun j => (B.getD j (Bl.zero, Bl.zero, Bl.zero)).1)
      (fun j => (B.getD j (Bl.zero, Bl.zero, Bl.zero)).2.1)
      (fun j => (B.getD j (Bl.zero, Bl.zero, Bl.zero)).2.2)).2.2

/-! ## Pólya positivity test -/

/-- Multiplication of a coefficient list by `1 + u`. -/
@[expose] def mulOnePlus : List ℤ → List ℤ
  | [] => []
  | a :: p => a :: addShift a p
where
  /-- Helper: coefficients of `p + u·(a :: p)` shifted. -/
  addShift : ℤ → List ℤ → List ℤ
  | b, [] => [b]
  | b, a :: q => Int.add a b :: addShift a q

/-- All coefficients are positive (and the list is nonempty). -/
@[expose] def allPos : List ℤ → Bool
  | [] => false
  | [a] => decide (0 < a)
  | a :: b :: p => decide (0 < a) && allPos (b :: p)

/-- Pólya test: some `(1 + u)ᵐ p` (`m ≤ M`) has positive coefficients. -/
@[expose] def polyaOK : ℕ → List ℤ → Bool
  | 0, p => allPos p
  | M + 1, p => allPos p || polyaOK M (mulOnePlus p)

/-- Powers of `2` (the Pólya test is applied in the variable `u = σ̃/2`). -/
@[expose] def pow2 : List ℤ := [1, 2, 4, 8, 16, 32, 64]

/-- Corner test: with reserve `R` (scaled), the polynomial `Σ (eₖ σ̃ᵏ − Rₖ |σ̃|ᵏ)` is positive
for `σ̃ ≥ 0` and for `σ̃ ≤ 0` (Pólya tests on the lower coefficient lists). -/
@[expose] def cornerOK (D : Data) (t n : ℤ) (R : List ℕ) : Bool :=
  let E := eCorner D t n
  ((List.range 7).all fun k => (lk E k).ok) &&
  polyaOK 24 ((List.range 7).map fun k =>
    Int.mul (Int.sub (lk E k).lo (R.getD k 0)) (pow2.getD k 0)) &&
  polyaOK 24 ((List.range 7).map fun k =>
    Int.mul (if k % 2 = 0 then Int.sub (lk E k).lo (R.getD k 0)
      else Int.sub (Int.neg (lk E k).hi) (R.getD k 0)) (pow2.getD k 0))

/-- The reserve of a box: `Rₖ ≥ Mτₖ Δτ²/8 + Msₖ Δs²/8`, from the bounds `Mτ, Ms` (scaled) of
the second derivatives (`Δτ = (t₁ − t₀)/NT`, `Δs = (n₁ − n₀)/NS`); for an axis box the second
term is `Msₖ s₁²/2`. -/
@[expose] def reserve (Mt Ms : List Bl) (dt ds : ℤ) (axis : Bool) : List ℕ :=
  (List.range 7).map fun k =>
    Nat.add (Nat.div (Nat.add (Nat.mul (Nat.mul (lk Mt k).mag (dt * dt).toNat) (NS * NS).toNat)
      (Nat.mul (Nat.mul (lk Ms k).mag (ds * ds).toNat)
        (if axis then (4 * NT * NT).toNat else (NT * NT).toNat)))
      (8 * NT * NT * NS * NS).toNat) 1

/-- **The check of one box** `[t₀/NT, t₁/NT] × [n₀/NS, n₁/NS]` (`0 ≤ n₀ < n₁ ≤ 25 NS`):
second-derivative balls in `τ` and in `s` over the box, and the corner test at the four
corners with the resulting reserve. -/
@[expose] def boxOK (D : Data) (t0 t1 n0 n1 : ℤ) : Bool :=
  let V := boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS)
  let Mt := e2 D Dt V
  let Ms := e2 D Ds V
  let R := reserve Mt Ms (t1 - t0) (n1 - n0) false
  decide (t0 < t1) && decide (0 ≤ n0) && decide (n0 < n1) && decide (n1 ≤ 25 * NS) &&
  ((List.range 7).all fun k => (lk Mt k).ok && (lk Ms k).ok) &&
  cornerOK D t0 n0 R && cornerOK D t1 n0 R && cornerOK D t0 n1 R && cornerOK D t1 n1 R

/-- **The check of an axis box** `[t₀/NT, t₁/NT] × [0, n₁/NS]`: the coefficients vanish on the
axis `s = 0`, so only the corners at `s = n₁/NS` are tested, with the reserve
`Mτ Δτ²/8 + Ms s₁²/2`. -/
@[expose] def axisOK (D : Data) (t0 t1 n1 : ℤ) : Bool :=
  let V := boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS)
  let Mt := e2 D Dt V
  let Ms := e2 D Ds V
  let R := reserve Mt Ms (t1 - t0) n1 true
  decide (t0 < t1) && decide (0 < n1) && decide (n1 ≤ 25 * NS) &&
  ((List.range 7).all fun k => (lk Mt k).ok && (lk Ms k).ok) &&
  cornerOK D t0 n1 R && cornerOK D t1 n1 R

/-- Componentwise comparison of two reserves. -/
@[expose] def leList (R R' : List ℕ) : Bool :=
  (List.range 7).all fun k => Nat.ble (R.getD k 0) (R'.getD k 0)

/-- **Second-derivative check of a box with shared corners**: the second-derivative balls are
valid and the reserve of the box (axis form if `axis`) is dominated by each of the reserves
`Rs` used by the (separately checked) corner tests. -/
@[expose] def hessOK (D : Data) (t0 t1 n0 n1 : ℤ) (axis : Bool) (Rs : List (List ℕ)) : Bool :=
  let V := boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS)
  let Mt := e2 D Dt V
  let Ms := e2 D Ds V
  let R := reserve Mt Ms (t1 - t0) (n1 - n0) axis
  decide (t0 < t1) && decide (0 ≤ n0) && decide (n0 < n1) && decide (n1 ≤ 25 * NS) &&
  ((List.range 7).all fun k => (lk Mt k).ok && (lk Ms k).ok) && Rs.all (leList R)

/-! ## Cover certificates -/

/-- Certificate that every box of a binary subdivision of `[t₀, t₁] × [n₀, n₁]` passes. -/
inductive Cover (D : Data) : ℤ → ℤ → ℤ → ℤ → Prop where
  /-- A checked box. -/
  | leaf (t0 t1 n0 n1 : ℤ) : boxOK D t0 t1 n0 n1 = true → Cover D t0 t1 n0 n1
  /-- A checked axis box. -/
  | axis (t0 t1 n1 : ℤ) : axisOK D t0 t1 n1 = true → Cover D t0 t1 0 n1
  /-- A box checked with separately proved corner tests. -/
  | leaf2 (t0 t1 n0 n1 : ℤ) (R00 R10 R01 R11 : List ℕ) :
      hessOK D t0 t1 n0 n1 false [R00, R10, R01, R11] = true → cornerOK D t0 n0 R00 = true →
      cornerOK D t1 n0 R10 = true → cornerOK D t0 n1 R01 = true → cornerOK D t1 n1 R11 = true →
      Cover D t0 t1 n0 n1
  /-- An axis box checked with separately proved corner tests. -/
  | axis2 (t0 t1 n1 : ℤ) (R0 R1 : List ℕ) :
      hessOK D t0 t1 0 n1 true [R0, R1] = true → cornerOK D t0 n1 R0 = true →
      cornerOK D t1 n1 R1 = true → Cover D t0 t1 0 n1
  /-- Split in `τ`. -/
  | splitT (t0 tm t1 n0 n1 : ℤ) : Cover D t0 tm n0 n1 → Cover D tm t1 n0 n1 →
      Cover D t0 t1 n0 n1
  /-- Split in `s`. -/
  | splitS (t0 t1 n0 nm n1 : ℤ) : Cover D t0 t1 n0 nm → Cover D t0 t1 nm n1 →
      Cover D t0 t1 n0 n1

open Lean Meta Elab Tactic in
/-- Proof builder for `Cover` from a plan (`meta`, outside the trusted kernel). Plan tokens:
`L` (checked box), `A` (axis box), `T<n>` (split in `τ` at `n`), `S<n>` (split in `s` at `n`),
`@name` (an already proved `Cover` lemma `PlasmaLean.Design.SolovevBallooning.name` for the
current box), `Q:a,b,c,d` (a box whose corner tests are the lemmas `a, b, c, d`, at the corners
`(t₀,n₀), (t₁,n₀), (t₀,n₁), (t₁,n₁)`), `Z:a,b` (an axis box with corner lemmas at
`(t₀,n₁), (t₁,n₁)`), in prefix order. Each leaf obligation `boxOK … = true` is closed by
`Eq.refl true`, i.e. by kernel evaluation when the declaration is checked. -/
meta partial def mkCover (D : Expr) (plan : List String) (t0 t1 n0 n1 : ℤ) :
    MetaM (Expr × List String) := do
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  match plan with
  | "L" :: rest =>
    return (mkAppN (mkConst ``Cover.leaf) #[D, toExpr t0, toExpr t1, toExpr n0, toExpr n1, refl],
      rest)
  | "A" :: rest =>
    unless n0 == 0 do throwError "ballooning_cover: axis box away from the axis"
    return (mkAppN (mkConst ``Cover.axis) #[D, toExpr t0, toExpr t1, toExpr n1, refl], rest)
  | tok :: rest =>
    let nm (x : String) : Name := Name.mkStr `PlasmaLean.Design.SolovevBallooning x
    let reserveOf (c : Name) : MetaM Expr := do
      let ty ← inferType (mkConst c)
      let_expr Eq _ lhs _ := ty | throwError "ballooning_cover: bad corner lemma {c}"
      let_expr cornerOK _ _ _ R := lhs | throwError "ballooning_cover: bad corner lemma {c}"
      return R
    if tok.startsWith "@" then
      return (mkConst (nm (tok.drop 1).toString), rest)
    if tok.startsWith "Q:" then
      let cs := ((tok.drop 2).toString.splitOn ",").map nm
      unless cs.length == 4 do throwError "ballooning_cover: bad token {tok}"
      let Rs ← cs.mapM reserveOf
      return (mkAppN (mkConst ``Cover.leaf2) (#[D, toExpr t0, toExpr t1, toExpr n0, toExpr n1] ++
        Rs.toArray ++ #[refl] ++ (cs.map mkConst).toArray), rest)
    if tok.startsWith "Z:" then
      unless n0 == 0 do throwError "ballooning_cover: axis box away from the axis"
      let cs := ((tok.drop 2).toString.splitOn ",").map nm
      unless cs.length == 2 do throwError "ballooning_cover: bad token {tok}"
      let Rs ← cs.mapM reserveOf
      return (mkAppN (mkConst ``Cover.axis2) (#[D, toExpr t0, toExpr t1, toExpr n1] ++
        Rs.toArray ++ #[refl] ++ (cs.map mkConst).toArray), rest)
    let some n := (tok.drop 1).toInt? | throwError "ballooning_cover: bad token {tok}"
    if tok.startsWith "T" then
      let (p1, r1) ← mkCover D rest t0 n n0 n1
      let (p2, r2) ← mkCover D r1 n t1 n0 n1
      return (mkAppN (mkConst ``Cover.splitT)
        #[D, toExpr t0, toExpr n, toExpr t1, toExpr n0, toExpr n1, p1, p2], r2)
    else if tok.startsWith "S" then
      let (p1, r1) ← mkCover D rest t0 t1 n0 n
      let (p2, r2) ← mkCover D r1 t0 t1 n n1
      return (mkAppN (mkConst ``Cover.splitS)
        #[D, toExpr t0, toExpr t1, toExpr n0, toExpr n, toExpr n1, p1, p2], r2)
    else throwError "ballooning_cover: bad token {tok}"
  | [] => throwError "ballooning_cover: plan too short"

open Lean Meta Elab Tactic in
/-- `ballooning_cover "plan"` proves a goal `Cover D t₀ t₁ n₀ n₁` (literal bounds) from a
subdivision plan; the box checks are left to the kernel. -/
elab "ballooning_cover " s:str : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Cover D t0 t1 n0 n1 := ty | throwError "ballooning_cover: expected a Cover goal"
  let ev (e : Expr) : MetaM ℤ := unsafe evalExpr ℤ (mkConst ``Int) e
  let plan := (s.getString.splitOn " ").filter (· ≠ "")
  let (pf, rest) ← mkCover D plan (← ev t0) (← ev t1) (← ev n0) (← ev n1)
  unless rest.isEmpty do throwError "ballooning_cover: unused plan suffix"
  g.assign pf

end PlasmaLean.Design.SolovevBallooning
