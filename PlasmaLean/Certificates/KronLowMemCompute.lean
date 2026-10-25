/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronChebCompute

/-!
# Low-memory kernel computations of family ball chains (light module)

The kernel keeps every intermediate value of one `decide +kernel` evaluation in its `whnf` caches
until the declaration is checked. The peak memory of a kernel check is therefore roughly the total
size of all intermediate big natural numbers, plus about 100–300 bytes per reduction step. The
kernel quantities of `Certificates/KronChebCompute` (`node3KN`, `norm3KN`, `center3KN`) spend this
budget in three places:

* the Kronecker images of the variables (`famTB − famO`): block spreading builds about ten full-size
  masks and intermediates per spreading level;
* `Int` arithmetic (`negSucc` representation), where every mixed-sign operation creates several
  copies of a full-size number;
* the weighted digit sum `rowBlk`, which costs about 20 reduction steps per row.

This module computes the same quantities with less memory:

* `SInt`: sign–magnitude integers, so that every operation creates one new number;
* `famS`: the image of a stored family as signed slice images (`sliceTFL`, masks per row and shared
  by all rows of a coefficient) placed by divide and conquer (`bsplitS`), each slice built once;
* `leafG`: the weighted block sums of one row by two multiplications and two masks per class of
  blocks, without a loop (`gSel ∈ {1, 2, 4}` classes, so that the weighted sums fit).

The quantities `node3KS`, `norm3KS`, `center3KS` are equal to `node3KN`, `norm3KN`, `center3KN`
under the hypotheses of the family ball steps (`Certificates/KronBallLowMem`), and they are checked
by the kernel in the same way. Nothing is proved here.

**Sanity.** `SInt.add_fixture`, `leafG_fixture`, `gSel_reject`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronLowMem

open PlasmaLean.Certificates.KronDigits PlasmaLean.Certificates.KronBallCheb

/-- **Sign–magnitude integers**: the value is `mag` or `−mag`. Every arithmetic operation on them
creates one new natural number in the kernel. -/
structure SInt where
  /-- The sign (`true` for negative values). -/
  isNeg : Bool
  /-- The magnitude. -/
  mag : Nat
  deriving DecidableEq

namespace SInt

/-- The integer value. -/
def toInt (x : SInt) : Int := if x.isNeg then -(x.mag : Int) else (x.mag : Int)

/-- Zero. -/
def zero : SInt := ⟨false, 0⟩

/-- An integer as a sign–magnitude integer. -/
def ofInt : Int → SInt
  | .ofNat n => ⟨false, n⟩
  | .negSucc n => ⟨true, n + 1⟩

/-- Sum. -/
def add (x y : SInt) : SInt :=
  if x.isNeg = y.isNeg then ⟨x.isNeg, x.mag + y.mag⟩
  else if y.mag ≤ x.mag then ⟨x.isNeg, x.mag - y.mag⟩ else ⟨y.isNeg, y.mag - x.mag⟩

/-- Negation. -/
def neg (x : SInt) : SInt := ⟨!x.isNeg, x.mag⟩

/-- Difference. -/
def sub (x y : SInt) : SInt := add x (neg y)

/-- Product. -/
def mul (x y : SInt) : SInt := ⟨x.isNeg ^^ y.isNeg, x.mag * y.mag⟩

/-- Multiplication by `2^k` (no new number for `k = 0`). -/
def shl (x : SInt) (k : Nat) : SInt := if k = 0 then x else ⟨x.isNeg, x.mag <<< k⟩

/-- The difference `a − b` of two natural numbers. -/
def subNat (a b : Nat) : SInt := if b ≤ a then ⟨false, a - b⟩ else ⟨true, b - a⟩

/-- Multiplication by an integer constant (no new number for `c = 1`). -/
def mulC (c : Int) (x : SInt) : SInt := if c = 1 then x else mul (ofInt c) x

/-- `(x + o).toNat` for a natural number `o`. -/
def offNat (x : SInt) (o : Nat) : Nat := if x.isNeg then o - x.mag else o + x.mag

/-- **Sanity**: `3 + (−5) = −2`. -/
theorem add_fixture : add ⟨false, 3⟩ ⟨true, 5⟩ = ⟨true, 2⟩ := by decide +kernel

end SInt

/-- `∑_{t<n} f(s + t) 2^{B t}` in sign–magnitude integers, by divide and conquer (`d` levels; the
signed copy of `bsplit`). -/
def bsplitS (f : Nat → SInt) (B : Nat) (d : Nat) : Nat → Nat → SInt :=
  Nat.rec (motive := fun _ => Nat → Nat → SInt) (fun s n => if n = 0 then SInt.zero else f s)
    (fun _ ih s n => if n ≤ 1 then (if n = 0 then SInt.zero else f s) else
      SInt.add (ih s (n / 2)) (SInt.shl (ih (s + n / 2) (n - n / 2)) (B * (n / 2)))) d

/-! ## Images of stored families -/

/-- The offset image of a row by masks (light copy of `rowNF`). -/
def rowNFL (b N M c0 : Nat) (odd : Bool) (kr : Nat) (sd : SliceData) (j : Nat) : Nat :=
  ((c0 * spreadRow sd.Fj b kr sd.Nj (sd.row (j + sd.Mj - M)) +
      (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj) <<< (b * (N + 1))) +
    ((if odd then (2 ^ (b - 1) + c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj -
        c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j))
      else c0 * spreadRowR sd.Fj b kr sd.Nj (sd.row (M + sd.Mj - j)) +
        (2 ^ (b - 1) - c0 * 2 ^ (sd.Fj - 1)) * onesK b sd.Nj) <<< (b * (N - sd.Nj))) +
    (centreN b M c0 odd sd j <<< (b * N))

/-- The offset image of a stored coefficient by rows (light copy of `sliceTF`). -/
def sliceTFL (b W N M c0 : Nat) (odd : Bool) (kr dr : Nat) (sd : SliceData) : Nat :=
  (bsplitN (fun r => rowNFL b N M c0 odd kr sd (M - sd.Mj + r)) (b * W) dr 0 (2 * sd.Mj + 1)) <<<
    (b * W * (M - sd.Mj))

/-- The signed image of a stored coefficient: offset image minus offsets. -/
def sliceS (b W N M c0 : Nat) (odd : Bool) (kr dr : Nat) (sd : SliceData) : SInt :=
  SInt.subNat (sliceTFL b W N M c0 odd kr dr sd) (sliceO b W N M sd)

/-- **The signed Kronecker image of a grid family**: the signed slice images (each computed once,
through `List.map`) placed at the Laurent positions by divide and conquer. -/
def famS (b W R N M D c0 : Nat) (odd : Bool) (kr dr dw : Nat) (l : List SliceData) : SInt :=
  SInt.shl (bsplitS (fun p => (l.map (sliceS b W N M c0 odd kr dr)).getD (lpos (l.length - 1) p)
      SInt.zero) (b * W * R) dw 0 (2 * (l.length - 1) + 1)) (b * W * R * (D - (l.length - 1)))

/-! ## Expression trees -/

/-- Phased evaluation in sign–magnitude integers (the copy of `ExN.evH`). -/
def evS (W : Nat → Nat × Nat × Nat) (x : Nat → SInt) : ExN → SInt
  | .var i => x i
  | .cst k => SInt.ofInt k
  | .add e f => if ExN.sgn W e f = 1 then SInt.add (evS W x e) (evS W x f)
      else SInt.sub (evS W x e) (evS W x f)
  | .sub e f => if ExN.sgn W e f = 1 then SInt.sub (evS W x e) (evS W x f)
      else SInt.add (evS W x e) (evS W x f)
  | .mul e f => SInt.mul (evS W x e) (evS W x f)

/-! ## Weighted digit sums of rows by multiplication -/

/-- `∑_{t<n} f t` (`Nat.rec`). -/
def natSum (f : Nat → Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun n s => s + f n)

/-- The weighted block sums of a row with `nB` blocks of `L` digits and reversed block weights
`cw` (entry `c` is the weight of block `nB − 1 − c`): the product with `∑_{t<L} 2^{bt}` holds the
block sum of block `c` in its digit `L c + L − 1` (masked and shifted down, one block per `b L`
bits), and the product with the reversed weights holds the weighted sum in block `nB − 1`. -/
def leafVW (b L nB : Nat) (cw : Nat → Nat) (x : Nat) : Nat :=
  (((((x * onesK b L) &&& ((((1 <<< b) - 1) * onesK (b * L) nB) <<< (b * (L - 1)))) >>>
      (b * (L - 1))) * bsplitN cw (b * L) 8 0 nB) >>> (b * L * (nB - 1))) % (1 <<< (b * L))

/-- The reversed weights of the blocks `g c + r` of a row of `W` digits (blocks of `L` digits,
superblocks of `g` blocks): the larger weight at the two ends of the block, as in `rowBlk`. -/
def blkG (W L g nB r : Nat) (wA : Nat → Nat) (c : Nat) : Nat :=
  max (wA (L * (g * (nB - 1 - c) + r))) (wA (min (L * (g * (nB - 1 - c) + r) + L) W - 1))

/-- The mask of the digits of the blocks `g c + r` (`nB` superblocks of `g L` digits). -/
def clsMask (b L g nB r : Nat) : Nat :=
  (((1 <<< (b * L)) - 1) <<< (b * (L * r))) * onesK (b * (g * L)) nB

/-- **The weighted block sums of a row of `W` digits** (blocks of `L` digits, weights `wA`) by
multiplication, the blocks split into `g` classes `c mod g` so that each weighted sum fits into one
superblock of `b g L` bits. -/
def leafG (b W L g : Nat) (wA : Nat → Nat) (x : Nat) : Nat :=
  natSum (fun r => leafVW b (g * L) ((W + g * L - 1) / (g * L))
    (blkG W L g ((W + g * L - 1) / (g * L)) r wA)
    (x &&& clsMask b L g ((W + g * L - 1) / (g * L)) r)) g

/-- The conditions under which `leafG` computes `rowBlk`: for every class, the weighted block sums
of a row whose digit sum is below `2^{b−1}` fit into one superblock. -/
def okG (b W L g : Nat) (wA : Nat → Nat) : Bool :=
  decide (1 ≤ L ∧ 1 ≤ b ∧ 1 ≤ g ∧ (W + g * L - 1) / (g * L) ≤ 2 ^ 8) &&
    (List.range g).all (fun r => decide (2 ^ (b - 1) *
      natSum (blkG W L g ((W + g * L - 1) / (g * L)) r wA) ((W + g * L - 1) / (g * L)) ≤
        2 ^ (b * (g * L))))

/-- The number of classes: the first of `1, 2, 4` for which `okG` holds (`0`: none, the row is
summed by `rowBlk`). -/
def gSel (b W L : Nat) (wA : Nat → Nat) : Nat :=
  if okG b W L 1 wA then 1 else if okG b W L 2 wA then 2 else if okG b W L 4 wA then 4 else 0

/-- **Sanity**: on the digits `3, 5, 7` (width `16`, blocks of `2`, weights `1, 2, 3`) the weighted
block sums are `max(1, 2)·(3 + 5) + 3·7 = 37`, with one class, with two classes, and by `rowBlk`. -/
theorem leafG_fixture : leafG 16 3 2 1 (fun i => i + 1) (3 + 5 * 2 ^ 16 + 7 * 2 ^ 32) = 37 ∧
    leafG 16 3 2 2 (fun i => i + 1) (3 + 5 * 2 ^ 16 + 7 * 2 ^ 32) = 37 ∧
    rowBlk 16 2 (fun i => i + 1) 2 0 3 (3 + 5 * 2 ^ 16 + 7 * 2 ^ 32) = 37 ∧
    gSel 16 3 2 (fun i => i + 1) = 1 := by decide +kernel

/-- **Sanity (rejected)**: with digits of width `2` and weights `10^6` no class split fits, and the
rows are summed by `rowBlk`. -/
theorem gSel_reject : gSel 2 3 2 (fun _ => 1000000) = 0 := by decide +kernel

/-- **The low-memory kernel quantity of a family polynomial** (the copy of `chebK` with signed
input and the rows summed by `leafG` when `gSel` finds a class split). -/
def chebKV (b W R Kw dr L fuel i₀ j₀ Ki Kj : Nat) (Nv : SInt) : Nat :=
  pdigL (b * W)
    (fun j row => kwtSL 74315 16 Kj (ndistL (j % R) j₀) *
      (if gSel b W L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) = 0 then
        rowBlk b L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) fuel 0 W row
      else leafG b W L (gSel b W L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)))
        (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) row)) dr 0 (R * Kw)
    (absDig b (W * (R * Kw)) (Nv.offNat (2 ^ (b - 1) * onesK b (W * (R * Kw)))))

/-- **The low-memory kernel quantity of a family rounding node** (equal to `node3KN`,
`Certificates/KronBallLowMem`). -/
def node3KS (S N M D : Nat) (Wt : Nat → Nat × Nat × Nat) (Kv : Nat → Nat → Nat → Nat → SInt)
    (e : ExN) (c' : Int) (dd de n b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebKV b W R Kw dr L fuel ((1 + dd) * N) ((1 + dd) * M + (0 + de)) Ki Kj
    (SInt.sub (evS Wt (Kv b W R) e)
      (SInt.mulC c' (SInt.shl (Kv b W R n)
        (dd * (S + b * (N + W * (M + R * D))) + de * (1 + b * W)))))

/-- **The low-memory kernel quantity of a family norm node** (equal to `norm3KN`). -/
def norm3KS (Wt : Nat → Nat × Nat × Nat) (Kv : Nat → Nat → Nat → Nat → SInt) (N M : Nat) (e : ExN)
    (w : Nat × Nat × Nat) (b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebKV b W R Kw dr L fuel (w.1 * N) (w.1 * M + w.2.1) Ki Kj (evS Wt (Kv b W R) e)

/-- **The low-memory kernel quantity of a family centre** (equal to `center3KN`). -/
def center3KS (Kv : Nat → Nat → Nat → Nat → SInt) (N M i b W R Kw dr L fuel Ki Kj : Nat) : Nat :=
  chebKV b W R Kw dr L fuel (1 * N) (1 * M + 0) Ki Kj (Kv b W R i)

end PlasmaLean.Certificates.KronLowMem
