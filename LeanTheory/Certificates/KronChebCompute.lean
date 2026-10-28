/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Init

/-!
# The kernel computations of family ball chains (light module)

The purely computational definitions of the family ball chains (`Certificates/KronBallCheb*`),
in a module without heavy imports, so that the kernel checks of large certificates run in processes
of small memory. Nothing here is proved; the specifications are in

* `Certificates/KronBallChebDigits` (`onesK`, `absDig`, `rowBlk`),
* `Certificates/KronBallChebSpread` (`spread`, `rev`, `spreadRow`, `spreadRowR`),
* `Certificates/KronBallChebGrid`, `Certificates/KronBallChebFam` (`SliceData`, `sliceTB`, `famTB`,
  `famO`),
* `Certificates/KronBallChebNorm`, `Certificates/KronBallChebChain` (`chebK`, `node3KN`, …).

The expression trees `ExN` mirror `KronExpr.Ex` (bridge `toEx`, `Certificates/KronBallChebChain`).

**Sanity.** `onesK_two`: `onesK 1 2 = 3`.
-/

@[expose] public section

namespace LeanTheory.Certificates.KronDigits

/-- `∑_{k<n} 2^{bk}`. -/
def onesK (b n : Nat) : Nat := ((1 <<< (b * n)) - 1) / ((1 <<< b) - 1)

/-- **Sanity**: `1 + 2 = 3`. -/
theorem onesK_two : onesK 1 2 = 3 := by rfl

/-- **The absolute digits** `|e_k − 2^{b−1}|` of `T`, by masks. -/
def absDig (b n T : Nat) : Nat :=
  let o := onesK b n
  let P := (T &&& (o <<< (b - 1))) >>> (b - 1)
  let tp := T &&& ((P <<< b) - P)
  (tp - (P <<< (b - 1))) + (((o - P) <<< (b - 1)) - (T - tp))

/-- Weighted digit sum of a row by blocks of `L` digits (fuel `f`, `Nat.rec`). -/
def rowBlk (b L : Nat) (wA : Nat → Nat) (f : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ _ => 0)
    (fun _ ih i len x =>
      if len ≤ L then (x % ((1 <<< b) - 1)) * max (wA i) (wA (i + len - 1))
      else ((x % (1 <<< (b * L))) % ((1 <<< b) - 1)) * max (wA i) (wA (i + L - 1)) +
        ih (i + L) (len - L) (x >>> (b * L))) f

/-- The low-half mask at spreading level `ℓ`. -/
def lowMask (F b ℓ cnt : Nat) : Nat := ((1 <<< (F * 2 ^ ℓ)) - 1) * onesK (b * 2 ^ (ℓ + 1)) cnt

/-- One spreading level. -/
def spreadStep (F b ℓ cnt x : Nat) : Nat :=
  (x &&& lowMask F b ℓ cnt) + ((x &&& (lowMask F b ℓ cnt <<< (F * 2 ^ ℓ))) <<< ((b - F) * 2 ^ ℓ))

/-- The spreading iteration. -/
def spreadIt (F b k : Nat) (m : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => spreadStep F b (k - 1 - j) (2 ^ j) (ih x)) m

/-- Spreading `2^k` fields from width `F` to width `b`. -/
def spread (F b k x : Nat) : Nat := spreadIt F b k k x

/-- One reversing level. -/
def revStep (c cnt x : Nat) : Nat :=
  ((x &&& (((1 <<< c) - 1) * onesK (2 * c) cnt)) <<< c) +
    ((x &&& ((((1 <<< c) - 1) * onesK (2 * c) cnt) <<< c)) >>> c)

/-- The reversing iteration. -/
def revIt (b k : Nat) (m : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => revStep (b * 2 ^ (k - 1 - j)) (2 ^ j) (ih x)) m

/-- Reversing `2^k` digits of width `b`. -/
def rev (b k x : Nat) : Nat := revIt b k k x

/-- The first `n` fields of `x` spread to width `b`. -/
def spreadRow (F b k n x : Nat) : Nat := spread F b k (x % (1 <<< (F * 2 ^ k))) % (1 <<< (b * n))

/-- The first `n` fields of `x` spread to width `b`, reversed. -/
def spreadRowR (F b k n x : Nat) : Nat :=
  rev b k (spread F b k (x % (1 <<< (F * 2 ^ k)))) >>> (b * (2 ^ k - n))

/-- Divide-and-conquer digit reading (copy of `pdig`). -/
def pdigL (b : Nat) (leaf : Nat → Nat → Nat) (d : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun off c T => cond (Nat.beq c 0) 0 (leaf off T))
    (fun d ih off c T => cond (Nat.beq c 0) 0
      (ih off (min c (1 <<< d)) (T % (1 <<< (b <<< d))) +
        ih (off + (1 <<< d)) (c - (1 <<< d)) (T >>> (b <<< d)))) d

/-- `|i − i₀|` (copy of `ndist`). -/
def ndistL (i i₀ : Nat) : Nat := (i - i₀) + (i₀ - i)

/-- The integer weight `p^s 2^{e(K − s)}` (copy of `kwtS`). -/
def kwtSL (p e K s : Nat) : Nat := p ^ s * 2 ^ (e * (K - s))

end LeanTheory.Certificates.KronDigits

namespace LeanTheory.Certificates.KronBallCheb

open LeanTheory.Certificates.KronDigits

/-- **A stored Chebyshev coefficient**: box `(N_j, M_j)`, field width `F_j`, the right halves of
the rows `r = 0, …, 2 M_j` in one literal (field `r N_j + t` is column `N + 1 + t` of row
`M − M_j + r`), the centre column (`M_j + 1` fields `i = N`, `j = M + t`), and the spreading levels
`k₁`, `k₂`. -/
structure SliceData where
  /-- Half width in `θ`-modes. -/
  Nj : Nat
  /-- Half width in `ψ`-modes. -/
  Mj : Nat
  /-- Field width (bits, offset `2^{F_j − 1}`). -/
  Fj : Nat
  /-- The right halves of the rows. -/
  blk : Nat
  /-- The centre column. -/
  col : Nat
  /-- Spreading levels of the block of right halves. -/
  k1 : Nat
  /-- Spreading levels of the rows. -/
  k2 : Nat

/-- The literal of row `r`. -/
def SliceData.row (sd : SliceData) (r : Nat) : Nat :=
  (sd.blk >>> (sd.Fj * sd.Nj * r)) % (1 <<< (sd.Fj * sd.Nj))

/-- The zero coefficient. -/
def SliceData.zero : SliceData := ⟨0, 0, 1, 0, 0, 0, 0⟩

/-- The raw field `t` of `x`. -/
def rawF (F x t : Nat) : Nat := (x >>> (F * t)) % 2 ^ F

/-- `∑_{t<n} f(s + t) 2^{B t}` by divide and conquer. -/
def bsplitN (f : Nat → Nat) (B : Nat) (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun s n => if n = 0 then 0 else f s)
    (fun _ ih s n => if n ≤ 1 then (if n = 0 then 0 else f s) else
      ih s (n / 2) + (ih (s + n / 2) (n - n / 2) <<< (B * (n / 2)))) d

/-- The offset digit of the centre column (row `j`). -/
def centreN (b M c0 : Nat) (odd : Bool) (sd : SliceData) (j : Nat) : Nat :=
  if M < j then c0 * rawF sd.Fj sd.col (j - M) + (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1))
  else if j < M then
    (if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) - c0 * rawF sd.Fj sd.col (M - j)
      else c0 * rawF sd.Fj sd.col (M - j) + (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)))
  else (if odd then 2 ^ (b - 1)
    else 2 * c0 * rawF sd.Fj sd.col 0 + (2 ^ (b - 1) - 2 * c0 * 2 ^ (sd.Fj - 1)))

/-- The offsets of one row. -/
def rowO (b N : Nat) (sd : SliceData) : Nat := (2 ^ (b - 1) * onesK b (2 * sd.Nj + 1)) <<< (b * (N - sd.Nj))

/-- The offsets of a stored coefficient. -/
def sliceO (b W N M : Nat) (sd : SliceData) : Nat :=
  (rowO b N sd * onesK (b * W) (2 * sd.Mj + 1)) <<< (b * W * (M - sd.Mj))

/-- The coefficient index at a Laurent position. -/
def lpos (D' p : Nat) : Nat := if p ≤ D' then D' - p else p - D'

/-- The right halves of all rows of a block, spread to width `b` and row stride `W`. -/
def rightBlk (b W F Nj R k1 k2 x : Nat) : Nat := spread (b * Nj) (b * W) k2 (spreadRow F b k1 (R * Nj) x)

/-- The mirrored halves, spread likewise. -/
def mirBlk (b W F Nj R k1 k2 x : Nat) : Nat := spread (b * Nj) (b * W) k2 (spreadRowR F b k1 (R * Nj) x)

/-- The offset image of a stored coefficient by block spreading. -/
def sliceTB (b W N M c0 : Nat) (odd : Bool) (dr : Nat) (sd : SliceData) : Nat :=
  (((c0 * rightBlk b W sd.Fj sd.Nj (2 * sd.Mj + 1) sd.k1 sd.k2 sd.blk +
      (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * (onesK b sd.Nj * onesK (b * W) (2 * sd.Mj + 1))) <<<
        (b * (N + 1))) +
    ((if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) *
        (onesK b sd.Nj * onesK (b * W) (2 * sd.Mj + 1)) -
        c0 * mirBlk b W sd.Fj sd.Nj (2 * sd.Mj + 1) sd.k1 sd.k2 sd.blk
      else c0 * mirBlk b W sd.Fj sd.Nj (2 * sd.Mj + 1) sd.k1 sd.k2 sd.blk +
        (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * (onesK b sd.Nj * onesK (b * W) (2 * sd.Mj + 1))) <<<
          (b * (N - sd.Nj))) +
    (bsplitN (fun r => centreN b M c0 odd sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1) <<<
      (b * N))) <<< (b * W * (M - sd.Mj))

/-- The offset image of a grid family. -/
def famTB (b W R N M D c0 : Nat) (odd : Bool) (dr dw : Nat) (l : List SliceData) : Nat :=
  bsplitN (fun p => (l.map (sliceTB b W N M c0 odd dr)).getD (lpos (l.length - 1) p) 0)
    (b * W * R) dw 0 (2 * (l.length - 1) + 1) <<< (b * W * R * (D - (l.length - 1)))

/-- The offsets of a grid family. -/
def famO (b W R N M D : Nat) (dw : Nat) (l : List SliceData) : Nat :=
  bsplitN (fun p => sliceO b W N M (l.getD (lpos (l.length - 1) p) SliceData.zero))
    (b * W * R) dw 0 (2 * (l.length - 1) + 1) <<< (b * W * R * (D - (l.length - 1)))

/-- **The kernel quantity of a family polynomial** (`Certificates/KronBallChebNorm`). -/
def chebK (b W R Kw dr L fuel i₀ j₀ Ki Kj : Nat) (Nv : Int) : Nat :=
  pdigL (b * W)
    (fun j row => kwtSL 74315 16 Kj (ndistL (j % R) j₀) *
      rowBlk b L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) fuel 0 W row) dr 0 (R * Kw)
    (absDig b (W * (R * Kw)) (Nv + ((2 ^ (b - 1) * onesK b (W * (R * Kw)) : Nat) : Int)).toNat)

/-! ## Images of families with a symbol (generic, slow) -/

/-- Field `t` (width `F`, offset `2^{F−1}`) of a literal, with natural-number shifts only (fast in
the kernel; equal to `fieldW`, `fieldZ_eq`). -/
def fieldZ (F x t : Nat) : Int := (((x >>> (F * t)) % (1 <<< F) : Nat) : Int) - ((1 <<< (F - 1) : Nat) : Int)


/-- `∑_{t<n} (α + β t) f_t 2^{bt}` for the fields `f_t = fieldW F x t` of `x`, by divide and
conquer (`d` levels). -/
def rpack (b F : Nat) : Int → Int → Nat → Nat → Nat → Int
  | α, _, 0, n, x => if n = 0 then 0 else α * fieldZ F x 0
  | α, β, d + 1, n, x => if n ≤ 1 then (if n = 0 then 0 else α * fieldZ F x 0) else
      rpack b F α β d (n / 2) (x % (1 <<< (F * (n / 2)))) +
        rpack b F (α + β * ((n / 2 : Nat) : Int)) β d (n - n / 2) (x >>> (F * (n / 2))) *
          ((1 <<< (b * (n / 2)) : Nat) : Int)

/-- `∑_{t<n} (α + β t) f_{n−1−t} 2^{bt}` (reversed fields), by divide and conquer. -/
def rpackR (b F : Nat) : Int → Int → Nat → Nat → Nat → Int
  | α, _, 0, n, x => if n = 0 then 0 else α * fieldZ F x 0
  | α, β, d + 1, n, x => if n ≤ 1 then (if n = 0 then 0 else α * fieldZ F x 0) else
      rpackR b F α β d (n - n / 2) (x >>> (F * (n / 2))) +
        rpackR b F (α + β * ((n - n / 2 : Nat) : Int)) β d (n / 2) (x % (1 <<< (F * (n / 2)))) *
          ((1 <<< (b * (n - n / 2)) : Nat) : Int)


/-- `∑_{t<n} f(s + t) 2^{B t}` by divide and conquer (`d` levels, `Nat.rec`). -/
def bsplit (f : Nat → Int) (B : Nat) (d : Nat) : Nat → Nat → Int :=
  Nat.rec (motive := fun _ => Nat → Nat → Int) (fun s n => if n = 0 then 0 else f s)
    (fun _ ih s n => if n ≤ 1 then (if n = 0 then 0 else f s) else
      ih s (n / 2) + ih (s + n / 2) (n - n / 2) * ((1 <<< (B * (n / 2)) : Nat) : Int)) d


/-- The Kronecker image of one row `j` of a stored coefficient. -/
def rowV (b N M : Nat) (s c0 a b' : Int) (dd : Nat) (sd : SliceData) (j : Nat) : Int :=
  if M ≤ j + sd.Mj ∧ j ≤ M + sd.Mj then
    rpack b sd.Fj (c0 + a + b' * ((j : Int) - M)) a dd sd.Nj (sd.row (j + sd.Mj - M)) *
        ((1 <<< (b * (N + 1)) : Nat) : Int) +
      s * rpackR b sd.Fj (c0 - a * sd.Nj + b' * ((j : Int) - M)) a dd sd.Nj
        (sd.row (M + sd.Mj - j)) * ((1 <<< (b * (N - sd.Nj)) : Nat) : Int) +
      (c0 + b' * ((j : Int) - M)) * ((if M ≤ j then fieldZ sd.Fj sd.col (j - M) else 0) +
        s * (if j ≤ M then fieldZ sd.Fj sd.col (M - j) else 0)) * ((1 <<< (b * N) : Nat) : Int)
  else 0


/-- **The Kronecker image of a stored coefficient** (rows `M − M_j … M + M_j` by divide and
conquer). -/
def slicePack (b W N M : Nat) (s c0 a b' : Int) (dd dr : Nat) (sd : SliceData) : Int :=
  bsplit (fun r => rowV b N M s c0 a b' dd sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1) *
    ((1 <<< (b * W * (M - sd.Mj)) : Nat) : Int)


/-- **The Kronecker image of a family** (`w ↦ 2^{b W R}`). -/
def famPack (b W R N M D : Nat) (s c0 a b' : Int) (dd dr : Nat) : Nat → List SliceData → Int
  | _, [] => 0
  | k, sd :: rest => slicePack b W N M s c0 a b' dd dr sd *
      ((((1 <<< (b * W * R * (D + k))) : Nat) : Int) +
        (if k = 0 then (0 : Int) else (((1 <<< (b * W * R * (D - k))) : Nat) : Int))) +
      famPack b W R N M D s c0 a b' dd dr (k + 1) rest


/-! ## Expression trees -/

/-- Expression trees (mirror of `KronExpr.Ex`). -/
inductive ExN where
  /-- The variable with index `i`. -/
  | var (i : Nat)
  /-- An integer constant. -/
  | cst (k : Int)
  /-- Sum. -/
  | add (e f : ExN)
  /-- Difference. -/
  | sub (e f : ExN)
  /-- Product. -/
  | mul (e f : ExN)

namespace ExN

/-- Combine the weights of a sum. -/
def comb : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | some (d, e, p), some (d', e', p') =>
    if d = d' ∧ e = e' ∧ (p + p') % 2 = 0 then some (d, e, p) else none
  | _, _ => none

/-- Product of weights. -/
def wmul : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat)
  | some (d, e, p), some (d', e', p') => some (d + d', e + e', (p + p') % 4)
  | _, _ => none

/-- The weight of a tree. -/
def wt (W : Nat → Nat × Nat × Nat) : ExN → Option (Nat × Nat × Nat)
  | var i => some (W i)
  | cst _ => some (0, 0, 0)
  | add e f => comb (wt W e) (wt W f)
  | sub e f => comb (wt W e) (wt W f)
  | mul e f => wmul (wt W e) (wt W f)

/-- The sign of the second operand of a sum. -/
def sgn (W : Nat → Nat × Nat × Nat) (e f : ExN) : Int :=
  match wt W e, wt W f with
  | some (_, _, p), some (_, _, p') => if p = p' then 1 else -1
  | _, _ => 1

/-- Phased evaluation in `Int`. -/
def evH (W : Nat → Nat × Nat × Nat) (x : Nat → Int) : ExN → Int
  | var i => x i
  | cst k => k
  | add e f => evH W x e + sgn W e f * evH W x f
  | sub e f => evH W x e - sgn W e f * evH W x f
  | mul e f => evH W x e * evH W x f

/-- Degree box of a tree of families. -/
def box3 (Bx : Nat → Nat × Nat × Nat) : ExN → Nat × Nat × Nat
  | var i => Bx i
  | cst _ => (0, 0, 0)
  | add e f => (max (box3 Bx e).1 (box3 Bx f).1, max (box3 Bx e).2.1 (box3 Bx f).2.1,
      max (box3 Bx e).2.2 (box3 Bx f).2.2)
  | sub e f => (max (box3 Bx e).1 (box3 Bx f).1, max (box3 Bx e).2.1 (box3 Bx f).2.1,
      max (box3 Bx e).2.2 (box3 Bx f).2.2)
  | mul e f => ((box3 Bx e).1 + (box3 Bx f).1, (box3 Bx e).2.1 + (box3 Bx f).2.1,
      (box3 Bx e).2.2 + (box3 Bx f).2.2)

/-- `ℓ¹` majorant of a tree. -/
def majN (L : Nat → Nat) : ExN → Nat
  | var i => L i
  | cst k => k.natAbs
  | add e f => majN L e + majN L f
  | sub e f => majN L e + majN L f
  | mul e f => majN L e * majN L f

/-- All variables below `n`. -/
def belowN (n : Nat) : ExN → Bool
  | var i => decide (i < n)
  | cst _ => true
  | add e f => belowN n e && belowN n f
  | sub e f => belowN n e && belowN n f
  | mul e f => belowN n e && belowN n f

end ExN

/-- The kernel quantity of a family rounding node. -/
def node3KN (S N M D : Nat) (Wt : Nat → Nat × Nat × Nat) (Kv : Nat → Nat → Nat → Nat → Int) (e : ExN) (c' : Int)
    (dd de n b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebK b W R Kw dr L fuel ((1 + dd) * N) ((1 + dd) * M + (0 + de)) Ki Kj
    (ExN.evH Wt (Kv b W R) e - c' * ((((1 <<< S : Nat) : Int) *
      ((1 <<< (b * (N + W * (M + R * D)))) : Nat)) ^ dd * (2 * ((1 <<< (b * W)) : Nat)) ^ de) *
        Kv b W R n)

/-- The kernel quantity of a family norm node (weight `w`). -/
def norm3KN (Wt : Nat → Nat × Nat × Nat) (Kv : Nat → Nat → Nat → Nat → Int) (N M : Nat) (e : ExN)
    (w : Nat × Nat × Nat) (b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebK b W R Kw dr L fuel (w.1 * N) (w.1 * M + w.2.1) Ki Kj (ExN.evH Wt (Kv b W R) e)

/-- The kernel quantity of a family centre. -/
def center3KN (Kv : Nat → Nat → Nat → Nat → Int) (N M i b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebK b W R Kw dr L fuel (1 * N) (1 * M + 0) Ki Kj (Kv b W R i)

/-- The degree conditions of a family node. -/
def nodeDims3N (N M D : Nat) (Bx : Nat → Nat × Nat × Nat) (e : ExN) (dd de n A J K b W R Kw dr L fuel : Nat) :
    Prop :=
  (ExN.box3 Bx e).1 ≤ A ∧ (ExN.box3 Bx e).2.1 ≤ J ∧ (ExN.box3 Bx e).2.2 ≤ K ∧
    dd * N + (Bx n).1 ≤ A ∧ dd * M + de + (Bx n).2.1 ≤ J ∧ dd * D + (Bx n).2.2 ≤ K ∧
    A < W ∧ J < R ∧ K < Kw ∧ R * Kw ≤ 2 ^ dr ∧ W ≤ fuel * L ∧ 1 ≤ b

/-- The degree conditions of a family node are decidable. -/
instance (N M D : Nat) (Bx : Nat → Nat × Nat × Nat) (e : ExN) (dd de n A J K b W R Kw dr L fuel : Nat) :
    Decidable (nodeDims3N N M D Bx e dd de n A J K b W R Kw dr L fuel) := by
  unfold nodeDims3N; infer_instance

/-- The degree conditions of a family norm node. -/
def normDims3N (Bx : Nat → Nat × Nat × Nat) (e : ExN) (A J K b W R Kw dr L fuel : Nat) : Prop :=
  (ExN.box3 Bx e).1 ≤ A ∧ (ExN.box3 Bx e).2.1 ≤ J ∧ (ExN.box3 Bx e).2.2 ≤ K ∧
    A < W ∧ J < R ∧ K < Kw ∧ R * Kw ≤ 2 ^ dr ∧ W ≤ fuel * L ∧ 1 ≤ b

/-- The degree conditions of a family norm node are decidable. -/
instance (Bx : Nat → Nat × Nat × Nat) (e : ExN) (A J K b W R Kw dr L fuel : Nat) :
    Decidable (normDims3N Bx e A J K b W R Kw dr L fuel) := by
  unfold normDims3N; infer_instance

/-- The a priori `ℓ¹` bound of a family node polynomial. -/
def nodeL1N (S : Nat) (L : Nat → Nat) (e : ExN) (c : Int) (dd de n : Nat) : Nat :=
  ExN.majN L e + c.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n)

end LeanTheory.Certificates.KronBallCheb
