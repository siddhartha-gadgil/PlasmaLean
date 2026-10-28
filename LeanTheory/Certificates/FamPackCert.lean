/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.KronBallChebGrid
public meta import Lean.Elab.Tactic.Basic
public meta import LeanTheory.Certificates.KronChebCompute

/-!
# Kronecker images of families as explicit certificates (`fampack_cert`)

The equations `Kv… b W R i = famPack b W R N M D s c0 a b' dd dr k l` of the family ball chains
(the stored derivative of a variable and the symbol family of another have the same Kronecker
image) were closed by one kernel evaluation of the generic image `famPack`: a `Nat.rec` divide
and conquer over the rows of every stored coefficient, with an `rpack` tree on every row, all
inside one `Eq.refl`. Here the generic side is an explicit certificate in the SubsetSum pattern:

* **`RowsEq f s n vs`**: the values `f s, …, f (s + n − 1)` are the literals `vs`; one kernel fact
  `f t = v` per row (`f = rowF …`, the image `rowV` of one row: a small `rpack` tree on the
  fields of one row).
* **`FPCert … k l v`**: `famPack … k l = v`, one constructor step per stored coefficient: the row
  count condition `Nat.ble (2 M_j + 1) (2^dr) = true`, the rows (`RowsEq`), and the placement of
  the coefficient at the Laurent positions `D ± k`. The value `v` is an **expression** over the
  row literals (`rowsVal`, shifts), not a literal image.
* **`famPack_eq_of_cert`**: soundness, `famPack … k l = v` (by `bsplit_eq` and induction).

The tactic **`fampack_cert`** proves `lhs = famPack … k l` for a closed `lhs`: `meta` code reads
the stored coefficients (kernel `whnf` of the list), computes the row values, and assembles the
certificate; the remaining fact is `lhs = v`, the comparison of the given image (for the chains:
the fast offset image `famTB − famO`) with the assembly of the row literals, one `Eq.refl` leaf.
No `decide`.

**Sanity.** `RowsEq.fixture`, `famPackCert_fixture` (a toy family of two coefficients, compared
with its own generic image).
-/

@[expose] public section

namespace LeanTheory.Certificates.FamPackCert

open Finset LeanTheory.Certificates.KronBallCheb

/-- `∑_t v_t 2^{B t}` of a list of row values (Horner). -/
def rowsVal (B : Nat) : List Int → Int
  | [] => 0
  | v :: vs => v + rowsVal B vs * ((1 <<< B : Nat) : Int)

/-- The values `f s, …, f (s + n − 1)`. -/
def rowsFrom (f : Nat → Int) : Nat → Nat → List Int
  | _, 0 => []
  | s, n + 1 => f s :: rowsFrom f (s + 1) n

theorem rowsVal_rowsFrom (f : Nat → Int) (B : Nat) : ∀ (s n : Nat),
    rowsVal B (rowsFrom f s n) = ∑ t ∈ range n, f (s + t) * (2 : Int) ^ (B * t)
  | s, 0 => by simp [rowsFrom, rowsVal]
  | s, n + 1 => by
    rw [rowsFrom, rowsVal, rowsVal_rowsFrom f B (s + 1) n, sum_range_succ', sum_mul,
      Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [show s + (t + 1) = s + 1 + t by omega, Nat.mul_add, pow_add, Nat.mul_one, mul_assoc]

/-- `bsplit` is the Horner value of its row list. -/
theorem bsplit_eq_rowsVal (f : Nat → Int) (B d s n : Nat) (h : n ≤ 2 ^ d) :
    bsplit f B d s n = rowsVal B (rowsFrom f s n) := by
  rw [bsplit_eq f B d s n h, rowsVal_rowsFrom]

/-- **Row certificate**: `f s, …, f (s + n − 1)` are `vs`, one kernel fact per row. -/
inductive RowsEq (f : Nat → Int) : Nat → Nat → List Int → Prop where
  /-- No rows. -/
  | nil (s : Nat) : RowsEq f s 0 []
  /-- One row, a kernel fact, and the rest. -/
  | cons (s n : Nat) (v : Int) (vs : List Int) : f s = v → RowsEq f (s + 1) n vs →
      RowsEq f s (n + 1) (v :: vs)

theorem RowsEq.sound {f : Nat → Int} {s n : Nat} {vs : List Int} (h : RowsEq f s n vs) :
    rowsFrom f s n = vs := by
  induction h with
  | nil s => rfl
  | cons s n v vs hv _ ih => rw [rowsFrom, hv, ih]

/-- **Sanity**: two rows of the identity. -/
theorem RowsEq.fixture : RowsEq (fun t => (t : Int)) 3 2 [3, 4] :=
  .cons 3 1 3 [4] rfl (.cons 4 0 4 [] rfl (.nil 5))

/-- The image of row `M − M_j + r` of a stored coefficient (the summand of `slicePack`). -/
def rowF (b N M : Nat) (s c0 a b' : Int) (dd : Nat) (sd : SliceData) (r : Nat) : Int :=
  rowV b N M s c0 a b' dd sd (M - sd.Mj + r)

/-- The placement factor of the coefficient `k` (Laurent positions `D ± k`). -/
def placeF (b W R D k : Nat) : Int :=
  (((1 <<< (b * W * R * (D + k))) : Nat) : Int) +
    (if k = 0 then (0 : Int) else (((1 <<< (b * W * R * (D - k))) : Nat) : Int))

/-- **Certificate of a family image**: `famPack … k l = v`, one step per stored coefficient. -/
inductive FPCert (b W R N M D : Nat) (s c0 a b' : Int) (dd dr : Nat) :
    Nat → List SliceData → Int → Prop where
  /-- No coefficient. -/
  | nil (k : Nat) : FPCert b W R N M D s c0 a b' dd dr k [] 0
  /-- A stored coefficient with its rows, placed at `D ± k`, and the rest. -/
  | cons (k : Nat) (sd : SliceData) (rest : List SliceData) (rows : List Int) (v : Int) :
      Nat.ble (2 * sd.Mj + 1) (2 ^ dr) = true →
      RowsEq (rowF b N M s c0 a b' dd sd) 0 (2 * sd.Mj + 1) rows →
      FPCert b W R N M D s c0 a b' dd dr (k + 1) rest v →
      FPCert b W R N M D s c0 a b' dd dr k (sd :: rest)
        (rowsVal (b * W) rows * ((1 <<< (b * W * (M - sd.Mj)) : Nat) : Int) *
          placeF b W R D k + v)

/-- **Soundness** of a family-image certificate. -/
theorem famPack_eq_of_cert {b W R N M D : Nat} {s c0 a b' : Int} {dd dr k : Nat}
    {l : List SliceData} {v : Int} (h : FPCert b W R N M D s c0 a b' dd dr k l v) :
    famPack b W R N M D s c0 a b' dd dr k l = v := by
  induction h with
  | nil k => rfl
  | cons k sd rest rows v hdr hrows _ ih =>
    rw [famPack, ih, slicePack, bsplit_eq_rowsVal _ _ _ _ _ (Nat.le_of_ble_eq_true hdr)]
    rw [show (fun r => rowV b N M s c0 a b' dd sd (M - sd.Mj + r)) =
      rowF b N M s c0 a b' dd sd from rfl, hrows.sound, placeF]

/-- **An image equation from a certificate**: `lhs = famPack … k l` from the certificate of the
right-hand side and the fact `lhs = v`. -/
theorem eq_famPack_of_cert {lhs : Int} {b W R N M D : Nat} {s c0 a b' : Int} {dd dr k : Nat}
    {l : List SliceData} {v : Int} (h : FPCert b W R N M D s c0 a b' dd dr k l v)
    (hv : lhs = v) : lhs = famPack b W R N M D s c0 a b' dd dr k l := by
  rw [famPack_eq_of_cert h, hv]

/-! ## The builder -/

open Lean Meta Elab Tactic

/-- A closed natural number, by the kernel's `whnf` (to read the data; untrusted). -/
meta def kNat (e : Expr) : MetaM Nat := do
  if let some n := e.rawNatLit? then return n
  if let some n := e.nat? then return n
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e' =>
    if let some n := e'.rawNatLit? then return n
    if let some n := e'.nat? then return n
    throwError "fampack_cert: not a natural-number literal{indentExpr e'}"
  | .error _ => throwError "fampack_cert: kernel evaluation failed{indentExpr e}"

/-- A closed integer, by the kernel's `whnf`. -/
meta def kInt (e : Expr) : MetaM Int := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e' =>
    match e'.getAppFnArgs with
    | (``Int.ofNat, #[n]) => return Int.ofNat (← kNat n)
    | (``Int.negSucc, #[n]) => return Int.negSucc (← kNat n)
    | _ => throwError "fampack_cert: not an integer literal{indentExpr e'}"
  | .error _ => throwError "fampack_cert: kernel evaluation failed{indentExpr e}"

/-- The integer literal in the kernel's normal form (`Int.ofNat n`, `Int.negSucc n`). -/
meta def intLit : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

/-- The elements of a closed list (kernel `whnf` of every tail). -/
meta partial def kList (e : Expr) : MetaM (List Expr) := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e' =>
    match e'.getAppFnArgs with
    | (``List.nil, _) => return []
    | (``List.cons, #[_, x, t]) => return x :: (← kList t)
    | _ => throwError "fampack_cert: the list did not reduce to a constructor{indentExpr e'}"
  | .error _ => throwError "fampack_cert: kernel evaluation failed{indentExpr e}"

/-- The value of a stored coefficient. -/
meta def kSlice (e : Expr) : MetaM SliceData := do
  let f (n : Name) := kNat (mkApp (mkConst n) e)
  return ⟨← f ``SliceData.Nj, ← f ``SliceData.Mj, ← f ``SliceData.Fj, ← f ``SliceData.blk,
    ← f ``SliceData.col, ← f ``SliceData.k1, ← f ``SliceData.k2⟩

/-- The list literal `[v₀, …]` of type `List Int`. -/
meta def intListLit : List Int → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Int)
  | v :: vs => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Int) (intLit v) (intListLit vs)

/-- The row certificate `RowsEq f s n vs` for the computed values `vs` (leaves `Eq.refl v`, checked
by the kernel only). -/
meta def mkRowsEq (f : Expr) : Nat → List Int → MetaM Expr
  | s, [] => return mkApp2 (mkConst ``RowsEq.nil) f (mkRawNatLit s)
  | s, v :: vs => do
    let tl ← mkRowsEq f (s + 1) vs
    let leaf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Int) (intLit v)
    return mkAppN (mkConst ``RowsEq.cons)
      #[f, mkRawNatLit s, mkRawNatLit vs.length, intLit v, intListLit vs, leaf, tl]

/-- **`fampack_cert`**: prove `lhs = famPack b W R N M D s c0 a b' dd dr k l` (closed) by a
family-image certificate (`FPCert`, one kernel fact per row) and the fact `lhs = v`. -/
syntax (name := fampackCert) "fampack_cert" : tactic

/-- The elaborator of `fampack_cert`. -/
@[tactic fampackCert] meta def evalFampackCert : Tactic := fun _ => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Eq _ lhs rhs := ty | throwError "fampack_cert: expected an equation"
  let_expr famPack be We Re Ne Me De se c0e ae b'e dde dre ke le := rhs
    | throwError "fampack_cert: expected `_ = famPack …`"
  let b ← kNat be; let N ← kNat Ne; let M ← kNat Me
  let s ← kInt se; let c0 ← kInt c0e; let a ← kInt ae; let b' ← kInt b'e
  let dd ← kNat dde; let dr ← kNat dre; let k₀ ← kNat ke
  let sds ← kList le
  let pre := #[be, We, Re, Ne, Me, De, se, c0e, ae, b'e, dde, dre]
  -- the certificate, last coefficient first
  let rec go (k : Nat) : List Expr → MetaM (Expr × Expr × Expr)
    | [] => do
      return (mkAppN (mkConst ``FPCert.nil) (pre.push (mkRawNatLit k)),
        mkApp (mkConst ``List.nil [0]) (mkConst ``SliceData), intLit 0)
    | sdE :: rest => do
      let (ptl, ltl, vtl) ← go (k + 1) rest
      let sd ← kSlice sdE
      let n := 2 * sd.Mj + 1
      unless n ≤ 2 ^ dr do throwError "fampack_cert: too many rows for the reading level"
      let rows := (List.range n).map fun r => rowV b N M s c0 a b' dd sd (M - sd.Mj + r)
      let f := mkAppN (mkConst ``rowF) #[be, Ne, Me, se, c0e, ae, b'e, dde, sdE]
      let prows ← mkRowsEq f 0 rows
      let rowsE := intListLit rows
      let hdr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
      let pf := mkAppN (mkConst ``FPCert.cons)
        (pre ++ #[mkRawNatLit k, sdE, ltl, rowsE, vtl, hdr, prows, ptl])
      let vE ← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[← mkAppM ``HMul.hMul
        #[mkApp2 (mkConst ``rowsVal) (← mkAppM ``HMul.hMul #[be, We]) rowsE,
          ← mkAppOptM ``Nat.cast #[mkConst ``Int, none,
            ← mkAppM ``HShiftLeft.hShiftLeft #[mkNatLit 1, ← mkAppM ``HMul.hMul
              #[← mkAppM ``HMul.hMul #[be, We], ← mkAppM ``HSub.hSub
                #[Me, mkApp (mkConst ``SliceData.Mj) sdE]]]]],
        mkAppN (mkConst ``placeF) #[be, We, Re, De, mkRawNatLit k]], vtl]
      return (pf, mkApp3 (mkConst ``List.cons [0]) (mkConst ``SliceData) sdE ltl, vE)
  let (pf, lE, vE) ← go k₀ sds
  let hv := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Int) lhs
  let rhs' := mkAppN (mkConst ``famPack) (pre ++ #[mkRawNatLit k₀, lE])
  let full := mkAppN (mkConst ``eq_famPack_of_cert)
    (#[lhs] ++ pre ++ #[mkRawNatLit k₀, lE, vE, pf, hv])
  -- the stated `famPack … k l` and the certified `famPack … k₀ [sd₀, …]` agree by unfolding the
  -- data definitions (checked by the kernel)
  g.assign (← mkExpectedTypeHint (← mkExpectedTypeHint full
    (← mkEq lhs rhs')) ty)
  replaceMainGoal []

/-- A toy stored coefficient (`N_j = 1`, `M_j = 1`, width `4`). -/
def toySD : SliceData := ⟨1, 1, 4, 0x9a7, 0x58, 0, 0⟩

/-- **Sanity** (accepted): a family of two coefficients, compared with its own generic image. -/
theorem famPackCert_fixture :
    famPack 8 4 3 2 2 1 1 3 1 2 1 2 0 [toySD, toySD] =
      famPack 8 4 3 2 2 1 1 3 1 2 1 2 0 [toySD, toySD] := by
  fampack_cert

end LeanTheory.Certificates.FamPackCert
