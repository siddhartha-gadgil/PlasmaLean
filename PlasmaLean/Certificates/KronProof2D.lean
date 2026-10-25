/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.Kronecker2DWeighted
public import PlasmaLean.Certificates.KronProof
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Eval
public meta import PlasmaLean.Certificates.Kronecker2DWeighted
public meta import PlasmaLean.Certificates.KronProof

/-!
# Two-dimensional Kronecker ball checks as explicit proof terms (`kron2_proof`)

The kernel checks `nodeK … ≤ Kb`, `normK … ≤ Kb`, `centerK … ≤ Kb` of the torus certificates
(`Certificates/KronBallGrid`; the `Torus`, `NegTorus` families) all unfold to the weighted digit
sum `wl1KronP b W dc dr R wA wB Nv` (`Certificates/Kronecker2DWeighted`): the divide-and-conquer
reading `pdig` of the rows of the offset Kronecker image `T = (Nv + offs …).toNat`. Instead of one
Boolean evaluation, these checks are proved by the certificate

* **`PCert2`** (digit reading): the reading `pdig` of a block of `2^{d+1}` rows split into its two
  halves (`loPart`, `hiPart` of `Certificates/KronProof`, with the kernel fact
  `Nat.beq c 0 = false`), down to blocks of `2^dB` rows whose weighted sums are kernel facts
  `pdig … = s` with small literals `s`;
* **the final comparison** `Nat.ble (s₁ + ⋯ + s_n) Kb = true`.

The image `T` stays an expression over the data definitions (the kernel evaluates it once per
declaration, with GMP); only the block sums are literals. Soundness (`PCert2.sound`,
`wl1KronP_le_of_cert`) is proved once by induction. The tactic **`kron2_proof`** (optionally
`kron2_proof dB`, default `dB = 3`) evaluates the witness (the image and the block sums) outside the
kernel and assembles the term from raw constructor applications whose leaves are `Eq.refl` terms,
which only the kernel evaluates. No `decide`.

**Sanity.** `PCert2.zero_fixture` (degenerate: an empty block), `kron2Proof_fixture` (the tactic
on a toy image), and a false bound on the same image refused by `fail_if_success`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronProof

open PlasmaLean.Certificates.Kron2

/-- **Certificate that the digit reading `pdig bw leaf d off c T` is `s`**: a block whose sum is a
kernel fact, or the split of a block into its two halves. -/
inductive PCert2 (bw : Nat) (leaf : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Prop where
  /-- A block of rows whose weighted sum is a kernel fact. -/
  | blk (d off c T s : Nat) : pdig bw leaf d off c T = s → PCert2 bw leaf d off c T s
  /-- A nonempty block of `2^{d+1}` rows split into its two halves. -/
  | split (d off c T s₁ s₂ : Nat) : Nat.beq c 0 = false →
      PCert2 bw leaf d off (min c (1 <<< d)) (loPart bw d T) s₁ →
      PCert2 bw leaf d (off + (1 <<< d)) (c - (1 <<< d)) (hiPart bw d T) s₂ →
      PCert2 bw leaf (d + 1) off c T (s₁ + s₂)

/-- One level of the digit reading (definitional unfolding of `pdig`). -/
theorem pdig_succ (bw : Nat) (leaf : Nat → Nat → Nat) (d off c T : Nat) :
    pdig bw leaf (d + 1) off c T = cond (Nat.beq c 0) 0
      (pdig bw leaf d off (min c (1 <<< d)) (loPart bw d T) +
        pdig bw leaf d (off + (1 <<< d)) (c - (1 <<< d)) (hiPart bw d T)) := rfl

/-- **Soundness of reading certificates.** -/
theorem PCert2.sound {bw : Nat} {leaf : Nat → Nat → Nat} {d off c T s : Nat}
    (h : PCert2 bw leaf d off c T s) : pdig bw leaf d off c T = s := by
  induction h with
  | blk d off c T s h => exact h
  | split d off c T s₁ s₂ hc _ _ ih₁ ih₂ => rw [pdig_succ, hc, ih₁, ih₂]; rfl

/-- **Sanity**: an empty block reads `0`. -/
theorem PCert2.zero_fixture (bw : Nat) (leaf : Nat → Nat → Nat) (T : Nat) :
    PCert2 bw leaf 3 0 0 T 0 := PCert2.blk 3 0 0 T 0 rfl

/-- The row function of `wl1KronP`. -/
def wl1Leaf (b W dc : Nat) (wA wB : Nat → Nat) (j T : Nat) : Nat :=
  wB j * pdig b (fun i x => wA i * ((x - 2 ^ (b - 1)) + (2 ^ (b - 1) - x))) dc 0 W T

/-- The offset image read by `wl1KronP`. -/
def wl1Img (b W dr : Nat) (Nv : Int) : Nat :=
  (Nv + offs (rowOffs (2 ^ (b - 1)) b W) (b * W) dr).toNat

/-- **Soundness of the two-dimensional Kronecker ball certificate**: a reading certificate of the
offset image and the final comparison prove the bound `wl1KronP … ≤ Kb`. -/
theorem wl1KronP_le_of_cert (b W dc dr R : Nat) (wA wB : Nat → Nat) (Nv : Int) (tot Kb : Nat)
    (hP : PCert2 (b * W) (wl1Leaf b W dc wA wB) dr 0 R (wl1Img b W dr Nv) tot)
    (hK : Nat.ble tot Kb = true) : wl1KronP b W dc dr R wA wB Nv ≤ Kb := by
  have h : wl1KronP b W dc dr R wA wB Nv = tot := hP.sound
  rw [h]
  exact Nat.le_of_ble_eq_true hK

/-! ## The `meta` builder -/

open Lean Meta Elab Tactic

/-- The `meta` copy of `wl1Leaf` (untrusted: used only to compute the block sums of the witness;
a wrong value is rejected by the kernel). -/
meta def wl1LeafM (b W dc : Nat) (wA wB : Nat → Nat) (j T : Nat) : Nat :=
  wB j * pdig b (fun i x => wA i * ((x - 2 ^ (b - 1)) + (2 ^ (b - 1) - x))) dc 0 W T

/-- **The reading certificate builder**: a proof of `PCert2 bw leaf d off c T s` for the block of
level `d` with value `Tv`, split down to blocks of level `≤ dB` whose sums are kernel facts, and
the value of `s`. -/
meta partial def mkPCert2 (bw leaf : Expr) (bwv : Nat) (leafv : Nat → Nat → Nat) (dB : Nat)
    (d off c : Nat) (T : Expr) (Tv : Nat) : MetaM (Expr × Nat) := do
  if d ≤ dB || c = 0 then
    let s := pdig bwv leafv d off c Tv
    let sE := mkRawNatLit s
    return (mkAppN (mkConst ``PCert2.blk) #[bw, leaf, mkRawNatLit d, mkRawNatLit off,
      mkRawNatLit c, T, sE, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) sE], s)
  else
    let d' := d - 1
    let k := bwv <<< d'
    let T₁ := mkApp3 (mkConst ``loPart) bw (mkRawNatLit d') T
    let T₂ := mkApp3 (mkConst ``hiPart) bw (mkRawNatLit d') T
    let (p₁, v₁) ← mkPCert2 bw leaf bwv leafv dB d' off (min c (1 <<< d')) T₁ (Tv % (1 <<< k))
    let (p₂, v₂) ←
      mkPCert2 bw leaf bwv leafv dB d' (off + (1 <<< d')) (c - (1 <<< d')) T₂ (Tv >>> k)
    let s₁ := (← inferType p₁).appArg!
    let s₂ := (← inferType p₂).appArg!
    return (mkAppN (mkConst ``PCert2.split) #[bw, leaf, mkRawNatLit d', mkRawNatLit off,
      mkRawNatLit c, T, s₁, s₂, reflBool false, p₁, p₂], v₁ + v₂)

/-- Evaluate a closed function `ℕ → ℕ` (compiled code). -/
meta def evalNatFun (e : Expr) : MetaM (Nat → Nat) := do
  unsafe evalExpr (Nat → Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) (← instantiateMVars e)

/-- **Proof term of a two-dimensional Kronecker ball check** `X ≤ Kb`, `X` one of `nodeK`,
`normK`, `centerK`, `wl1KronP` (blocks of `2^dB` rows). -/
meta def kron2ProofTerm (goal : Expr) (dB : Nat) : MetaM Expr := do
  let_expr LE.le _ _ X Kb := goal | throwError "kron2_proof: expected a goal `X ≤ Kb`"
  let mut X := X
  for _ in [0:8] do
    if X.isAppOfArity ``wl1KronP 8 then break
    match ← unfoldDefinition? X with
    | some X' => X := X'.headBeta
    | none => throwError "kron2_proof: cannot unfold{indentExpr X}"
  unless X.isAppOfArity ``wl1KronP 8 do
    throwError "kron2_proof: expected `wl1KronP`{indentExpr X}"
  let a := X.getAppArgs
  let [b, W, dc, dr, R] ← (a.extract 0 5).toList.mapM evalNatE | throwError "kron2_proof: arity"
  let wA ← evalNatFun a[5]!
  let wB ← evalNatFun a[6]!
  let Nv := a[7]!
  let Nvv ← evalIntE Nv
  let Tv := (Nvv + offs (rowOffs (2 ^ (b - 1)) b W) (b * W) dr).toNat
  let bw := mkNatMul a[0]! a[1]!
  let leaf := mkAppN (mkConst ``wl1Leaf) #[a[0]!, a[1]!, a[2]!, a[5]!, a[6]!]
  let T := mkAppN (mkConst ``wl1Img) #[a[0]!, a[1]!, a[3]!, Nv]
  let (pP, totv) ← mkPCert2 bw leaf (b * W) (wl1LeafM b W dc wA wB) dB dr 0 R T Tv
  let Kbv ← evalNatE Kb
  unless totv ≤ Kbv do
    throwError "kron2_proof: the bound fails: the kernel quantity is {totv} > {Kbv}"
  let tot := (← inferType pP).appArg!
  return mkAppN (mkConst ``wl1KronP_le_of_cert) (a ++ #[tot, Kb, pP, reflBool true])

/-- **`kron2_proof`** (optionally `kron2_proof dB`): prove a two-dimensional Kronecker ball check
`nodeK … ≤ Kb` (`normK`, `centerK`, `wl1KronP`) by an explicit certificate
(`wl1KronP_le_of_cert`); the default block level is `dB = 3` (`8` rows per block sum). The witness
is evaluated first and the bound compared, so a failing bound is reported here and not by the
kernel. -/
syntax (name := kron2Proof) "kron2_proof" (ppSpace num)? : tactic

/-- The elaborator of `kron2_proof`. -/
@[tactic kron2Proof] meta def evalKron2Proof : Tactic := fun stx => do
  let dB := match stx[1].getOptional? with
    | some n => n.isNatLit?.getD 3
    | none => 3
  let g ← getMainGoal
  let goal ← instantiateMVars (← g.getType)
  let pf ← kron2ProofTerm goal dB
  g.assign (← mkExpectedTypeHint pf goal)
  replaceMainGoal []

/-- **Sanity (accepted)**: the tactic on a toy image `3 − 5 · 2^8` (two rows of one slot,
digits `3` and `−5`, unit weights), split into blocks of one row. -/
theorem kron2Proof_fixture :
    wl1KronP 8 1 0 1 2 (fun _ => 1) (fun _ => 1) (3 - 5 * 2 ^ 8) ≤ 8 := by
  kron2_proof 0

/-- **Sanity (rejected)**: the tactic refuses the false bound `8 ≤ 7` on the same toy image. -/
example : True := by
  fail_if_success
    have : wl1KronP 8 1 0 1 2 (fun _ => 1) (fun _ => 1) (3 - 5 * 2 ^ 8) ≤ 7 := by kron2_proof 0
  trivial

end PlasmaLean.Certificates.KronProof
