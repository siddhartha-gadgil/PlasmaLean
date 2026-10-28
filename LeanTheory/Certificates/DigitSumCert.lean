/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.Kronecker2D
public import LeanTheory.Certificates.KernelFact
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Rewrite
public meta import LeanTheory.Certificates.KernelFact

/-!
# Kronecker digit sums `l1Kron` as explicit certificates (`l1kron_cert`)

The exact `ℓ¹` norms of the 2-D Kronecker checks (`Certificates/Kronecker2D`) are digit sums
`l1Kron b d Nv = digitSum H b d T` of the offset image `T = (Nv + offs H b d).toNat`,
`H = 2^(b-1)`, read by divide and conquer over the `2^d` base-`2^b` digits. Closing a bound
`… l1Kron b d Nv … ≤ K` by one kernel evaluation leaves the whole digit reading opaque. Here it
is an explicit certificate in the SubsetSum pattern:

* **`DCert H b d T s`**: the digit sum of the `2^d` digits of `T` is `s`. Constructors: a block of
  `2^d` digits whose sum is the kernel fact `digitSum H b d T = s` (small literal `s`, blocks of
  `2^k` digits, default `k = 9`), and the split of `2^(d+1)` digits into the low and high halves
  `T % (1 <<< (b <<< d))`, `T >>> (b <<< d)`. The halves are **expressions** over the stated
  image (never literals), evaluated by the kernel with GMP and shared through its cache.
* **`DCert.sound`**: soundness by induction (the split is the defining recursion of
  `digitSum`), and `l1Kron_eq_of_cert`.
* **`l1kron_cert`**: the tactic. For every `l1Kron b d Nv` in a closed `ℕ` goal it computes the
  witness (the image, by the kernel's `whnf`, and the block sums, in `meta` code), proves
  `l1Kron b d Nv = s` by the certificate, rewrites, and closes the remaining comparison of small
  numbers by `kernel_fact`.

**Sanity.** `DCert.zero_fixture` (degenerate: one digit), `l1kronCert_fixture` (accepted: a toy
image, with block level `0`), `l1kronCert_reject_fixture` (a false bound is refused).
-/

@[expose] public section

namespace LeanTheory.Certificates.DigitSumCert

open Lean Meta Elab Tactic LeanTheory.Certificates.Kron2

/-- **Certificate of a digit sum**: the `2^d` base-`2^b` digits `e` of `T` have
`∑ |e − H| = s`. -/
inductive DCert (H b : Nat) : Nat → Nat → Nat → Prop where
  /-- A block whose digit sum is a kernel fact. -/
  | leaf (d T s : Nat) : digitSum H b d T = s → DCert H b d T s
  /-- The split into the low and the high half of the digits. -/
  | split (d T s₁ s₂ : Nat) : DCert H b d (T % (1 <<< (b <<< d))) s₁ →
      DCert H b d (T >>> (b <<< d)) s₂ → DCert H b (d + 1) T (s₁ + s₂)

/-- **Soundness** of a digit-sum certificate. -/
theorem DCert.sound {H b d T s : Nat} (h : DCert H b d T s) : digitSum H b d T = s := by
  induction h with
  | leaf d T s h => exact h
  | split d T s₁ s₂ _ _ ih₁ ih₂ =>
    change digitSum H b d (T % (1 <<< (b <<< d))) + digitSum H b d (T >>> (b <<< d)) = s₁ + s₂
    rw [ih₁, ih₂]

/-- **The `ℓ¹` norm from a certificate** of the digit sum of the offset image. -/
theorem l1Kron_eq_of_cert (b d : Nat) (Nv : Int) (s : Nat)
    (h : DCert (2 ^ (b - 1)) b d (Nv + offs (2 ^ (b - 1)) b d).toNat s) : l1Kron b d Nv = s :=
  h.sound

/-- **Sanity** (degenerate): the certificate of one digit is the kernel fact. -/
theorem DCert.zero_fixture : DCert 1 2 0 3 2 := .leaf 0 3 2 rfl

/-! ## The builder -/

/-- `digitSum` in `meta` code (the witness; the kernel re-checks every block). -/
meta def digitSumM (H b : Nat) : Nat → Nat → Nat
  | 0, T => (T - H) + (H - T)
  | d + 1, T => digitSumM H b d (T % (1 <<< (b <<< d))) + digitSumM H b d (T >>> (b <<< d))

/-- The certificate `DCert H b d T s` for the term `Te` of value `T`, with blocks of `2^k` digits;
returns the proof and `s`. -/
meta partial def mkDCert (H b k : Nat) (He be : Expr) (d : Nat) (Te : Expr) (T : Nat) :
    MetaM (Expr × Nat) := do
  if d ≤ k then
    let s := digitSumM H b d T
    let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit s)
    return (mkAppN (mkConst ``DCert.leaf) #[He, be, mkRawNatLit d, Te, mkRawNatLit s, pf], s)
  let d' := d - 1
  let sh := b <<< d'
  -- the halves as the expressions of the definition of `digitSum` (unfolded by the kernel)
  let shE ← mkAppM ``HShiftLeft.hShiftLeft #[be, mkRawNatLit d']
  let mE ← mkAppM ``HShiftLeft.hShiftLeft #[mkNatLit 1, shE]
  let loE ← mkAppM ``HMod.hMod #[Te, mE]
  let hiE ← mkAppM ``HShiftRight.hShiftRight #[Te, shE]
  let (p₁, s₁) ← mkDCert H b k He be d' loE (T % (1 <<< sh))
  let (p₂, s₂) ← mkDCert H b k He be d' hiE (T >>> sh)
  return (mkAppN (mkConst ``DCert.split) #[He, be, mkRawNatLit d', Te, mkRawNatLit s₁,
    mkRawNatLit s₂, p₁, p₂], s₁ + s₂)

/-- A closed natural number, by the kernel's `whnf` (`meta`; only to compute the witness). -/
meta def kernelNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e' =>
    if let some n := e'.rawNatLit? then return n
    if let some n := e'.nat? then return n
    throwError "l1kron_cert: the value did not reduce to a literal{indentExpr e'}"
  | .error _ => throwError "l1kron_cert: kernel evaluation failed{indentExpr e}"

/-- The proof of `l1Kron b d Nv = s` for the subterm `e = l1Kron b d Nv`, blocks of `2^k`
digits. -/
meta def l1KronEq (e : Expr) (k : Nat) : MetaM Expr := do
  let_expr l1Kron be de Nv := e | throwError "l1kron_cert: expected `l1Kron b d Nv`"
  let b ← kernelNat be
  let d ← kernelNat de
  let H := 2 ^ (b - 1)
  let He ← mkAppM ``HPow.hPow #[mkNatLit 2, ← mkAppM ``HSub.hSub #[be, mkNatLit 1]]
  let offsE := mkApp3 (mkConst ``offs) He be de
  let TeI ← mkAppM ``HAdd.hAdd #[Nv, ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, offsE]]
  let Te := mkApp (mkConst ``Int.toNat) TeI
  let T ← kernelNat Te
  let (pf, s) ← mkDCert H b k He be d Te T
  return mkAppN (mkConst ``l1Kron_eq_of_cert) #[be, de, Nv, mkRawNatLit s, pf]

/-- **`l1kron_cert`** (optionally `l1kron_cert k`, blocks of `2^k` digits, default `9`): prove a
closed `ℕ` comparison containing `l1Kron b d Nv` terms by digit-sum certificates (`DCert`), then
`kernel_fact` on the comparison of the resulting small numbers. -/
syntax (name := l1kronCert) "l1kron_cert" (ppSpace num)? : tactic

/-- The elaborator of `l1kron_cert`. -/
@[tactic l1kronCert] meta def evalL1kronCert : Tactic := fun stx => do
  let k := if stx[1].isNone then 9 else stx[1][0].isNatLit?.getD 9
  let g ← getMainGoal
  let ty₀ ← instantiateMVars (← g.getType)
  if ty₀.hasLooseBVars || ty₀.isForall then throwError "l1kron_cert: expected a closed comparison"
  -- the equations `l1Kron b d Nv = sᵢ`, and the goal with the `l1Kron` terms replaced by `sᵢ`
  let mut eqs : Array (Expr × Expr × Expr × Expr) := #[]
  let mut ty := ty₀
  repeat
    let some e := ty.find? (fun x => x.isAppOfArity ``l1Kron 3) | break
    let h ← l1KronEq e k
    let some (_, _, s) := (← inferType h).eq? | throwError "l1kron_cert: internal error"
    let tmpl := ty.replace fun x => if x == e then some (.bvar 0) else none
    eqs := eqs.push (e, s, h, tmpl)
    ty := tmpl.instantiate1 s
  -- refuse a false comparison here (the kernel would refuse it only when the declaration is
  -- added)
  match_expr ty with
  | LE.le α _ a c =>
    if α.isConstOf ``Nat then
      unless (← kernelNat a) ≤ (← kernelNat c) do
        throwError "l1kron_cert: the bound fails{indentExpr ty}"
  | LT.lt α _ a c =>
    if α.isConstOf ``Nat then
      unless (← kernelNat a) < (← kernelNat c) do
        throwError "l1kron_cert: the bound fails{indentExpr ty}"
  | _ => pure ()
  let mut pf ← LeanTheory.Certificates.KronProof.kernelFactTerm ty
  -- transport back along the equations, last one first (`Eq.mpr` of `congrArg`)
  for (e, s, h, tmpl) in eqs.reverse do
    let ty' := tmpl.instantiate1 e
    let motive := Expr.lam `x (mkConst ``Nat) tmpl .default
    let hc := mkAppN (mkConst ``congrArg [1, 1])
      #[mkConst ``Nat, mkSort 0, e, s, motive, h]
    pf := mkAppN (mkConst ``Eq.mpr [0]) #[ty', ty, hc, pf]
    ty := ty'
  g.assign (← mkExpectedTypeHint pf ty₀)
  replaceMainGoal []

/-- **Sanity** (accepted): a toy image `1 + 3·2^8` (two digits) read with block level `0`. -/
theorem l1kronCert_fixture : 2 * l1Kron 8 1 (1 + 3 * 2 ^ 8) + 1 ≤ 2 * 4 + 1 := by
  l1kron_cert 0

/-- **Sanity** (rejected): a false bound is refused. -/
theorem l1kronCert_reject_fixture : True := by
  fail_if_success (have : l1Kron 8 1 (1 + 3 * 2 ^ 8) ≤ 3 := by l1kron_cert 0)
  trivial

end LeanTheory.Certificates.DigitSumCert
