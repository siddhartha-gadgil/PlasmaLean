/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronLowMemCompute
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Eval
public meta import Lean.Meta.Offset
public meta import PlasmaLean.Certificates.KronLowMemCompute

/-!
# Kronecker ball checks as explicit proof terms (SubsetSum pattern)

The low-memory kernel checks `node3KS … ≤ Kb`, `norm3KS … ≤ Kb`, `center3KS … ≤ Kb`
(`Certificates/KronLowMemCompute`) proved by explicit certificates instead of one Boolean
evaluation. The quantity `chebKV … Nv` is the weighted sum of the absolute digits of the offset
image of a signed Kronecker image `Nv`; its certificate consists of

* **`SCert x s m`** (sign handling): the signed value `x` is `⟨s, m⟩`. One constructor per local
  step: an atom (a variable image, a constant) with its sign as a kernel fact `x.isNeg = s`;
  sums with equal signs; sums with opposite signs and the magnitude comparison `Nat.ble m₂ m₁` as a
  kernel fact; negation, difference, product, shift (`Nat.beq k 0`), multiplication by a constant;
  and the steps of the phased tree evaluation `evS` (`ExN.sgn` as a kernel fact). The magnitudes
  `m` are **expressions** over the data definitions (`(KvS b W R i).mag * …`), never literals:
  the kernel evaluates them once per declaration, with GMP.
* **`PCert`** (digit reading): the divide-and-conquer digit reading `pdigL` of the absolute
  digits, split into its two halves (`loPart`, `hiPart`, with `Nat.beq c 0 = false`) down to blocks
  of `2^k` rows, whose weighted sums are kernel facts `pdigL … = s` with small literals `s`.
* **the class selection** `gSel … = g` and **the final comparison** `Nat.ble (s₁ + ⋯ + s_n) Kb`.

Soundness (`SCert.sound`, `PCert.sound`, `chebKV_le_of_cert`) is proved once by induction; the
check statements, and hence the bridges `node3KN_le_of_S`, … and the chains, are unchanged.

The tactic **`kron_proof`** builds the certificate: `meta` code evaluates the witness (the signs,
the magnitude comparisons and the block sums) outside the kernel and assembles the term with raw
`mkAppN` applications, whose leaves are `Eq.refl` terms; the elaborator never evaluates them, only
the kernel does. **`kron_lt`** proves the `ℓ¹` checks `a < c` by the kernel fact
`Nat.ble (a + 1) c = true`. No `decide`, no `native_decide`, nothing opaque.

**Sanity.** `SCert.add_fixture` (accepted: `3 + (−5) = −2`), `SCert.reject_fixture` (rejected:
`⟨false, 3⟩` has no certificate with sign `true`), `PCert.zero_fixture` (degenerate: an empty
block), `kronProof_fixture` (the tactic on a toy image; a false bound on it is refused, by
`fail_if_success`), `kronLt_fixture`.
-/

@[expose] public section

namespace PlasmaLean.Certificates.KronProof

open PlasmaLean.Certificates.KronDigits PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.KronLowMem

/-! ## Signed values -/

/-- **Certificate that the signed value `x` is `⟨s, m⟩`.** Each constructor is one local step of
the evaluation of a signed Kronecker image; the arguments are explicit so that the `meta` builder
can supply them. -/
inductive SCert : SInt → Bool → Nat → Prop where
  /-- An atom with its sign (a kernel fact); the magnitude is the expression `x.mag`. -/
  | atom (x : SInt) (s : Bool) : x.isNeg = s → SCert x s x.mag
  /-- A sum of values of equal signs. -/
  | add_same (x y : SInt) (s : Bool) (m₁ m₂ : Nat) :
      SCert x s m₁ → SCert y s m₂ → SCert (SInt.add x y) s (m₁ + m₂)
  /-- A sum of values of opposite signs, the first magnitude not smaller. -/
  | add_ge (x y : SInt) (s : Bool) (m₁ m₂ : Nat) :
      SCert x s m₁ → SCert y (!s) m₂ → Nat.ble m₂ m₁ = true → SCert (SInt.add x y) s (m₁ - m₂)
  /-- A sum of values of opposite signs, the second magnitude larger. -/
  | add_lt (x y : SInt) (s : Bool) (m₁ m₂ : Nat) :
      SCert x s m₁ → SCert y (!s) m₂ → Nat.ble m₂ m₁ = false →
        SCert (SInt.add x y) (!s) (m₂ - m₁)
  /-- Negation. -/
  | neg (x : SInt) (s : Bool) (m : Nat) : SCert x s m → SCert (SInt.neg x) (!s) m
  /-- A difference is the sum with the negation. -/
  | sub (x y : SInt) (s : Bool) (m : Nat) :
      SCert (SInt.add x (SInt.neg y)) s m → SCert (SInt.sub x y) s m
  /-- A product. -/
  | mul (x y : SInt) (s t : Bool) (m₁ m₂ : Nat) :
      SCert x s m₁ → SCert y t m₂ → SCert (SInt.mul x y) (s ^^ t) (m₁ * m₂)
  /-- A shift by zero. -/
  | shl_zero (x : SInt) (k : Nat) (s : Bool) (m : Nat) :
      Nat.beq k 0 = true → SCert x s m → SCert (SInt.shl x k) s m
  /-- A shift by a positive amount. -/
  | shl_pos (x : SInt) (k : Nat) (s : Bool) (m : Nat) :
      Nat.beq k 0 = false → SCert x s m → SCert (SInt.shl x k) s (m <<< k)
  /-- Multiplication by the constant `1`. -/
  | mulC_one (c : Int) (x : SInt) (s : Bool) (m : Nat) :
      c = 1 → SCert x s m → SCert (SInt.mulC c x) s m
  /-- Multiplication by a constant other than `1`. -/
  | mulC_ne (c : Int) (x : SInt) (s : Bool) (m : Nat) :
      (c == 1) = false → SCert (SInt.mul (SInt.ofInt c) x) s m → SCert (SInt.mulC c x) s m
  /-- Tree evaluation: a variable. -/
  | ev_var (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (i : Nat) (s : Bool) (m : Nat) :
      SCert (v i) s m → SCert (evS W v (.var i)) s m
  /-- Tree evaluation: a constant. -/
  | ev_cst (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (k : Int) (s : Bool) (m : Nat) :
      SCert (SInt.ofInt k) s m → SCert (evS W v (.cst k)) s m
  /-- Tree evaluation: a sum of equal phases. -/
  | ev_add_pos (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (e f : ExN) (s : Bool) (m : Nat) :
      ExN.sgn W e f = 1 → SCert (SInt.add (evS W v e) (evS W v f)) s m →
        SCert (evS W v (.add e f)) s m
  /-- Tree evaluation: a sum of opposite phases. -/
  | ev_add_neg (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (e f : ExN) (s : Bool) (m : Nat) :
      (ExN.sgn W e f == 1) = false → SCert (SInt.sub (evS W v e) (evS W v f)) s m →
        SCert (evS W v (.add e f)) s m
  /-- Tree evaluation: a difference of equal phases. -/
  | ev_sub_pos (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (e f : ExN) (s : Bool) (m : Nat) :
      ExN.sgn W e f = 1 → SCert (SInt.sub (evS W v e) (evS W v f)) s m →
        SCert (evS W v (.sub e f)) s m
  /-- Tree evaluation: a difference of opposite phases. -/
  | ev_sub_neg (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (e f : ExN) (s : Bool) (m : Nat) :
      (ExN.sgn W e f == 1) = false → SCert (SInt.add (evS W v e) (evS W v f)) s m →
        SCert (evS W v (.sub e f)) s m
  /-- Tree evaluation: a product. -/
  | ev_mul (W : Nat → Nat × Nat × Nat) (v : Nat → SInt) (e f : ExN) (s : Bool) (m : Nat) :
      SCert (SInt.mul (evS W v e) (evS W v f)) s m → SCert (evS W v (.mul e f)) s m

/-- **Soundness of signed certificates**: the value is the certified sign and magnitude. -/
theorem SCert.sound {x : SInt} {s : Bool} {m : Nat} (h : SCert x s m) : x = ⟨s, m⟩ := by
  induction h with
  | atom x s h => cases x; cases h; rfl
  | add_same x y s m₁ m₂ _ _ ih₁ ih₂ => subst ih₁ ih₂; simp [SInt.add]
  | add_ge x y s m₁ m₂ _ _ h ih₁ ih₂ =>
    subst ih₁ ih₂; cases s <;> simp_all [SInt.add, Nat.ble_eq]
  | add_lt x y s m₁ m₂ _ _ h ih₁ ih₂ =>
    subst ih₁ ih₂
    have h' : ¬ m₂ ≤ m₁ := fun h'' => by rw [Nat.ble_eq_true_of_le h''] at h; cases h
    cases s <;> simp [SInt.add, h']
  | neg x s m _ ih => subst ih; rfl
  | sub x y s m _ ih => exact ih
  | mul x y s t m₁ m₂ _ _ ih₁ ih₂ => subst ih₁ ih₂; rfl
  | shl_zero x k s m h _ ih =>
    have hk : k = 0 := Nat.eq_of_beq_eq_true h
    subst hk ih; rfl
  | shl_pos x k s m h _ ih =>
    have hk : k ≠ 0 := Nat.ne_of_beq_eq_false h
    subst ih; simp [SInt.shl, hk]
  | mulC_one c x s m h _ ih => subst h ih; rfl
  | mulC_ne c x s m h _ ih =>
    have hc : c ≠ 1 := by simpa using h
    simp [SInt.mulC, hc, ih]
  | ev_var W v i s m _ ih => exact ih
  | ev_cst W v k s m _ ih => exact ih
  | ev_add_pos W v e f s m h _ ih => simp [evS, h, ih]
  | ev_add_neg W v e f s m h _ ih =>
    have h' : ExN.sgn W e f ≠ 1 := by simpa using h
    simp [evS, h', ih]
  | ev_sub_pos W v e f s m h _ ih => simp [evS, h, ih]
  | ev_sub_neg W v e f s m h _ ih =>
    have h' : ExN.sgn W e f ≠ 1 := by simpa using h
    simp [evS, h', ih]
  | ev_mul W v e f s m _ ih => exact ih

/-- **Sanity (accepted)**: `3 + (−5) = −2`, certified by the opposite-sign step. -/
theorem SCert.add_fixture : SCert (SInt.add ⟨false, 3⟩ ⟨true, 5⟩) true (5 - 3) :=
  SCert.add_lt _ _ false 3 5 (SCert.atom ⟨false, 3⟩ false rfl) (SCert.atom ⟨true, 5⟩ true rfl) rfl

/-- **Sanity (rejected)**: a positive value has no certificate with a negative sign. -/
theorem SCert.reject_fixture : ¬ SCert ⟨false, 3⟩ true 3 := fun h => by
  cases h.sound

/-! ## Digit reading -/

/-- The low half of a block of `2^{d+1}` rows of width `bw`. -/
def loPart (bw d T : Nat) : Nat := T % (1 <<< (bw <<< d))

/-- The high half of a block of `2^{d+1}` rows of width `bw`. -/
def hiPart (bw d T : Nat) : Nat := T >>> (bw <<< d)

/-- **Certificate that the digit reading `pdigL bw leaf d off c T` is `s`**: a block whose sum is
a kernel fact, or the split of a block into its two halves. -/
inductive PCert (bw : Nat) (leaf : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Nat → Prop where
  /-- A block of rows whose weighted sum is a kernel fact. -/
  | blk (d off c T s : Nat) : pdigL bw leaf d off c T = s → PCert bw leaf d off c T s
  /-- A nonempty block of `2^{d+1}` rows split into its two halves. -/
  | split (d off c T s₁ s₂ : Nat) : Nat.beq c 0 = false →
      PCert bw leaf d off (min c (1 <<< d)) (loPart bw d T) s₁ →
      PCert bw leaf d (off + (1 <<< d)) (c - (1 <<< d)) (hiPart bw d T) s₂ →
      PCert bw leaf (d + 1) off c T (s₁ + s₂)

/-- One level of the digit reading (definitional unfolding of `pdigL`). -/
theorem pdigL_succ (bw : Nat) (leaf : Nat → Nat → Nat) (d off c T : Nat) :
    pdigL bw leaf (d + 1) off c T = cond (Nat.beq c 0) 0
      (pdigL bw leaf d off (min c (1 <<< d)) (loPart bw d T) +
        pdigL bw leaf d (off + (1 <<< d)) (c - (1 <<< d)) (hiPart bw d T)) := rfl

/-- **Soundness of reading certificates.** -/
theorem PCert.sound {bw : Nat} {leaf : Nat → Nat → Nat} {d off c T s : Nat}
    (h : PCert bw leaf d off c T s) : pdigL bw leaf d off c T = s := by
  induction h with
  | blk d off c T s h => exact h
  | split d off c T s₁ s₂ hc _ _ ih₁ ih₂ => rw [pdigL_succ, hc, ih₁, ih₂]; rfl

/-- **Sanity**: an empty block reads `0`. -/
theorem PCert.zero_fixture (bw : Nat) (leaf : Nat → Nat → Nat) (T : Nat) :
    PCert bw leaf 3 0 0 T 0 := PCert.blk 3 0 0 T 0 rfl

/-! ## The kernel quantity -/

/-- The row weight function of `chebKV` with the class number `g` fixed (`g = 0`: rows summed by
`rowBlk`). -/
def chebLeaf (b W R L fuel i₀ j₀ Ki Kj g : Nat) (j row : Nat) : Nat :=
  kwtSL 74315 16 Kj (ndistL (j % R) j₀) *
    (if g = 0 then rowBlk b L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) fuel 0 W row
    else leafG b W L g (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) row)

/-- `chebKV` is the digit reading with the row weights `chebLeaf` for the selected class number. -/
theorem chebKV_eq_pdigL (b W R Kw dr L fuel i₀ j₀ Ki Kj g : Nat) (Nv : SInt)
    (hg : gSel b W L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) = g) :
    chebKV b W R Kw dr L fuel i₀ j₀ Ki Kj Nv =
      pdigL (b * W) (chebLeaf b W R L fuel i₀ j₀ Ki Kj g) dr 0 (R * Kw)
        (absDig b (W * (R * Kw)) (Nv.offNat (2 ^ (b - 1) * onesK b (W * (R * Kw))))) := by
  subst hg; rfl

/-- **Soundness of the Kronecker ball certificate**: a signed certificate of the image, the class
number, a reading certificate of the absolute digits and the final comparison prove the
low-memory bound `chebKV … ≤ Kb`. -/
theorem chebKV_le_of_cert (b W R Kw dr L fuel i₀ j₀ Ki Kj : Nat) (Nv : SInt) (s : Bool)
    (m g tot Kb : Nat) (hN : SCert Nv s m)
    (hg : gSel b W L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) = g)
    (hP : PCert (b * W) (chebLeaf b W R L fuel i₀ j₀ Ki Kj g) dr 0 (R * Kw)
      (absDig b (W * (R * Kw)) (SInt.offNat ⟨s, m⟩ (2 ^ (b - 1) * onesK b (W * (R * Kw))))) tot)
    (hK : Nat.ble tot Kb = true) : chebKV b W R Kw dr L fuel i₀ j₀ Ki Kj Nv ≤ Kb := by
  rw [chebKV_eq_pdigL b W R Kw dr L fuel i₀ j₀ Ki Kj g Nv hg, hN.sound, hP.sound]
  exact Nat.le_of_ble_eq_true hK

/-- A strict bound from the kernel fact `Nat.ble (a + 1) c = true` (the `ℓ¹` checks). -/
theorem lt_of_ble_succ {a c : Nat} (h : Nat.ble (a + 1) c = true) : a < c :=
  Nat.le_of_ble_eq_true h

/-! ## The `meta` builder -/

open Lean Meta Elab Tactic

/-- The `meta` copy of `chebLeaf` (untrusted: used only to compute the block sums of the witness;
a wrong value is rejected by the kernel). -/
meta def chebLeafM (b W R L fuel i₀ j₀ Ki Kj g : Nat) (j row : Nat) : Nat :=
  kwtSL 74315 16 Kj (ndistL (j % R) j₀) *
    (if g = 0 then rowBlk b L (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) fuel 0 W row
    else leafG b W L g (fun i => kwtSL 74315 16 Ki (ndistL i i₀)) row)

/-- The `meta` copy of `famS` with every slice image computed once (untrusted, for the witness). -/
meta def famSM (b W R N M D c0 : Nat) (odd : Bool) (kr dr dw : Nat) (l : List SliceData) : SInt :=
  let arr := (l.map (sliceS b W N M c0 odd kr dr)).toArray
  SInt.shl (bsplitS (fun p => arr.getD (lpos (l.length - 1) p) SInt.zero) (b * W * R) dw 0
    (2 * (l.length - 1) + 1)) (b * W * R * (D - (l.length - 1)))

/-- Evaluate a closed natural-number expression (literal, simple arithmetic, or compiled code). -/
meta def evalNatE (e : Expr) : MetaM Nat := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return n
  if let some n := e.rawNatLit? then return n
  if let some n ← Meta.evalNat e |>.run then return n
  unsafe evalExpr Nat (mkConst ``Nat) e

/-- Evaluate a closed integer expression. -/
meta def evalIntE (e : Expr) : MetaM Int := do
  unsafe evalExpr Int (mkConst ``Int) (← instantiateMVars e)

/-- Evaluate a closed Boolean expression. -/
meta def evalBoolE (e : Expr) : MetaM Bool := do
  unsafe evalExpr Bool (mkConst ``Bool) (← instantiateMVars e)

/-- The witness evaluator: caches the values of signed subexpressions. -/
abbrev EvalM := StateRefT (Std.HashMap Expr SInt) MetaM

/-- Evaluate a closed signed expression for the witness: sign–magnitude operations are evaluated
directly, `famS` by `famSM`, `ite` by its decided branch, other definitions by unfolding, and
anything else by compiled code. -/
meta partial def evalSI (e : Expr) : EvalM SInt := do
  if let some v := (← get)[e]? then return v
  let v ← match e.getAppFnArgs with
    | (``SInt.add, #[x, y]) => return SInt.add (← evalSI x) (← evalSI y)
    | (``SInt.sub, #[x, y]) => return SInt.sub (← evalSI x) (← evalSI y)
    | (``SInt.neg, #[x]) => return SInt.neg (← evalSI x)
    | (``SInt.mul, #[x, y]) => return SInt.mul (← evalSI x) (← evalSI y)
    | (``SInt.shl, #[x, k]) => return SInt.shl (← evalSI x) (← evalNatE k)
    | (``SInt.mulC, #[c, x]) => return SInt.mulC (← evalIntE c) (← evalSI x)
    | (``SInt.ofInt, #[k]) => return SInt.ofInt (← evalIntE k)
    | (``famS, #[b, W, R, N, M, D, c0, odd, kr, dr, dw, l]) =>
      return famSM (← evalNatE b) (← evalNatE W) (← evalNatE R) (← evalNatE N) (← evalNatE M)
        (← evalNatE D) (← evalNatE c0) (← evalBoolE odd) (← evalNatE kr) (← evalNatE dr)
        (← evalNatE dw) (← unsafe evalExpr (List SliceData) (mkApp (mkConst ``List [0])
          (mkConst ``SliceData)) l)
    | (``ite, #[_, c, inst, a, b]) =>
      if ← evalBoolE (mkApp2 (mkConst ``Decidable.decide) c inst) then evalSI a else evalSI b
    | _ =>
      match ← unfoldDefinition? e with
      | some e' => evalSI e'.headBeta
      | none => unsafe evalExpr SInt (mkConst ``SInt) e
  modify (·.insert e v)
  return v

/-- The sign and magnitude indices of a signed certificate. -/
meta def scertIdx (pf : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType pf
  let_expr SCert _ s m := ty | throwError "kron_proof: unexpected certificate type{indentExpr ty}"
  return (s, m)

/-- `Eq.refl` of a Boolean literal (a leaf, checked by the kernel only). -/
meta def reflBool (b : Bool) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (toExpr b)

/-- `Eq.refl` of a natural-number literal (a leaf, checked by the kernel only). -/
meta def reflNat (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkRawNatLit n)

/-- **The signed certificate builder**: returns a proof of `SCert e s m`, the sign `s` and the
value. The terms are raw applications of the constructors (no elaborator checks); the leaves
are `Eq.refl` terms checked by the kernel. -/
meta partial def mkSCert (e : Expr) : EvalM (Expr × Bool × SInt) := do
  match e.getAppFnArgs with
  | (``SInt.add, #[x, y]) =>
    let (px, sx, vx) ← mkSCert x
    let (py, sy, vy) ← mkSCert y
    let (_, mx) ← scertIdx px
    let (_, my) ← scertIdx py
    let v := SInt.add vx vy
    if sx == sy then
      return (mkAppN (mkConst ``SCert.add_same) #[x, y, toExpr sx, mx, my, px, py], sx, v)
    else if vy.mag ≤ vx.mag then
      return (mkAppN (mkConst ``SCert.add_ge) #[x, y, toExpr sx, mx, my, px, py, reflBool true],
        sx, v)
    else
      return (mkAppN (mkConst ``SCert.add_lt) #[x, y, toExpr sx, mx, my, px, py, reflBool false],
        !sx, v)
  | (``SInt.sub, #[x, y]) =>
    let (p, s, v) ← mkSCert (mkApp2 (mkConst ``SInt.add) x (mkApp (mkConst ``SInt.neg) y))
    let (_, m) ← scertIdx p
    return (mkAppN (mkConst ``SCert.sub) #[x, y, toExpr s, m, p], s, v)
  | (``SInt.neg, #[x]) =>
    let (p, s, v) ← mkSCert x
    let (_, m) ← scertIdx p
    return (mkAppN (mkConst ``SCert.neg) #[x, toExpr s, m, p], !s, SInt.neg v)
  | (``SInt.mul, #[x, y]) =>
    let (px, sx, vx) ← mkSCert x
    let (py, sy, vy) ← mkSCert y
    let (_, mx) ← scertIdx px
    let (_, my) ← scertIdx py
    return (mkAppN (mkConst ``SCert.mul) #[x, y, toExpr sx, toExpr sy, mx, my, px, py],
      sx ^^ sy, SInt.mul vx vy)
  | (``SInt.shl, #[x, k]) =>
    let kv ← evalNatE k
    let (p, s, v) ← mkSCert x
    let (_, m) ← scertIdx p
    let c := if kv = 0 then ``SCert.shl_zero else ``SCert.shl_pos
    return (mkAppN (mkConst c) #[x, k, toExpr s, m, reflBool (kv = 0), p], s, SInt.shl v kv)
  | (``SInt.mulC, #[c, x]) =>
    let cv ← evalIntE c
    if cv = 1 then
      let (p, s, v) ← mkSCert x
      let (_, m) ← scertIdx p
      return (mkAppN (mkConst ``SCert.mulC_one) #[c, x, toExpr s, m, ← mkEqRefl c, p], s, v)
    else
      let (p, s, v) ← mkSCert (mkApp2 (mkConst ``SInt.mul) (mkApp (mkConst ``SInt.ofInt) c) x)
      let (_, m) ← scertIdx p
      return (mkAppN (mkConst ``SCert.mulC_ne) #[c, x, toExpr s, m, reflBool false, p], s, v)
  | (``evS, #[Wt, vf, t]) =>
    let t ← whnfD t
    let evS' (u : Expr) : Expr := mkApp3 (mkConst ``evS) Wt vf u
    match t.getAppFnArgs with
    | (``ExN.var, #[i]) =>
      let (p, s, v) ← mkSCert (mkApp vf i)
      let (_, m) ← scertIdx p
      return (mkAppN (mkConst ``SCert.ev_var) #[Wt, vf, i, toExpr s, m, p], s, v)
    | (``ExN.cst, #[k]) =>
      let (p, s, v) ← mkSCert (mkApp (mkConst ``SInt.ofInt) k)
      let (_, m) ← scertIdx p
      return (mkAppN (mkConst ``SCert.ev_cst) #[Wt, vf, k, toExpr s, m, p], s, v)
    | (``ExN.mul, #[a, b]) =>
      let (p, s, v) ← mkSCert (mkApp2 (mkConst ``SInt.mul) (evS' a) (evS' b))
      let (_, m) ← scertIdx p
      return (mkAppN (mkConst ``SCert.ev_mul) #[Wt, vf, a, b, toExpr s, m, p], s, v)
    | (``ExN.add, #[a, b]) | (``ExN.sub, #[a, b]) =>
      let isAdd := t.isAppOf ``ExN.add
      let pos := (← evalIntE (mkApp3 (mkConst ``ExN.sgn) Wt a b)) = 1
      let op := if isAdd == pos then ``SInt.add else ``SInt.sub
      let (p, s, v) ← mkSCert (mkApp2 (mkConst op) (evS' a) (evS' b))
      let (_, m) ← scertIdx p
      let c := if isAdd then (if pos then ``SCert.ev_add_pos else ``SCert.ev_add_neg)
        else (if pos then ``SCert.ev_sub_pos else ``SCert.ev_sub_neg)
      let h ← if pos then mkEqRefl (toExpr (1 : Int)) else pure (reflBool false)
      return (mkAppN (mkConst c) #[Wt, vf, a, b, toExpr s, m, h, p], s, v)
    | _ => throwError "kron_proof: tree did not reduce to a constructor{indentExpr t}"
  | _ =>
    let v ← evalSI e
    return (mkAppN (mkConst ``SCert.atom) #[e, toExpr v.isNeg, reflBool v.isNeg], v.isNeg, v)

/-- **The reading certificate builder**: a proof of `PCert bw leaf d off c T s` for the block of
level `d` with value `Tv`, split down to blocks of level `≤ dB` whose sums are kernel facts, and
the value of `s`. -/
meta partial def mkPCert (bw leaf : Expr) (bwv : Nat) (leafv : Nat → Nat → Nat) (dB : Nat)
    (d off c : Nat) (T : Expr) (Tv : Nat) : MetaM (Expr × Nat) := do
  if d ≤ dB || c = 0 then
    let s := pdigL bwv leafv d off c Tv
    let sE := mkRawNatLit s
    return (mkAppN (mkConst ``PCert.blk) #[bw, leaf, mkRawNatLit d, mkRawNatLit off,
      mkRawNatLit c, T, sE, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) sE], s)
  else
    let d' := d - 1
    let k := bwv <<< d'
    let T₁ := mkApp3 (mkConst ``loPart) bw (mkRawNatLit d') T
    let T₂ := mkApp3 (mkConst ``hiPart) bw (mkRawNatLit d') T
    let (p₁, v₁) ← mkPCert bw leaf bwv leafv dB d' off (min c (1 <<< d')) T₁ (Tv % (1 <<< k))
    let (p₂, v₂) ←
      mkPCert bw leaf bwv leafv dB d' (off + (1 <<< d')) (c - (1 <<< d')) T₂ (Tv >>> k)
    let s₁ := (← inferType p₁).appArg!
    let s₂ := (← inferType p₂).appArg!
    return (mkAppN (mkConst ``PCert.split) #[bw, leaf, mkRawNatLit d', mkRawNatLit off,
      mkRawNatLit c, T, s₁, s₂, reflBool false, p₁, p₂], v₁ + v₂)

/-- **Proof term of a low-memory Kronecker ball check** `X ≤ Kb`, `X` one of `node3KS`, `norm3KS`,
`center3KS`, `chebKV` (blocks of `2^dB` rows). -/
meta def kronProofTerm (goal : Expr) (dB : Nat) : MetaM Expr := do
  let_expr LE.le _ _ X Kb := goal | throwError "kron_proof: expected a goal `X ≤ Kb`"
  let mut X := X
  for _ in [0:8] do
    if X.isAppOfArity ``chebKV 12 then break
    match ← unfoldDefinition? X with
    | some X' => X := X'.headBeta
    | none => throwError "kron_proof: cannot unfold{indentExpr X}"
  unless X.isAppOfArity ``chebKV 12 do throwError "kron_proof: expected `chebKV`{indentExpr X}"
  let a := X.getAppArgs
  let [b, W, R, Kw, _dr, L, fuel, i₀, j₀, Ki, Kj] ← (a.extract 0 11).toList.mapM evalNatE
    | throwError "kron_proof: arity"
  let Nv := a[11]!
  let (pN, s, vN) ← (mkSCert Nv).run' {}
  let (_, m) ← scertIdx pN
  let wA := fun i => kwtSL 74315 16 Ki (ndistL i i₀)
  let g := gSel b W L wA
  let lemPart := mkAppN (mkConst ``chebKV_le_of_cert) (a ++ #[toExpr s, m, mkRawNatLit g])
  -- the type of the reading hypothesis, read off the lemma (its indices do not depend on `tot`)
  let ty ← instantiateForall (← inferType lemPart) #[mkRawNatLit 0, Kb]
  let hPty := ty.bindingBody!.bindingBody!.bindingDomain!
  let_expr PCert bw leaf dr off c T _ := hPty | throwError "kron_proof: unexpected lemma type"
  let n := W * (R * Kw)
  let Av := absDig b n (vN.offNat (2 ^ (b - 1) * onesK b n))
  let (pP, totv) ← mkPCert bw leaf (b * W) (chebLeafM b W R L fuel i₀ j₀ Ki Kj g) dB
    (← evalNatE dr) (← evalNatE off) (← evalNatE c) T Av
  let Kbv ← evalNatE Kb
  unless totv ≤ Kbv do
    throwError "kron_proof: the bound fails: the kernel quantity is {totv} > {Kbv}"
  let tot := (← inferType pP).appArg!
  return mkAppN lemPart #[tot, Kb, pN, reflNat g, pP, reflBool true]

/-- **`kron_proof`** (optionally `kron_proof dB`): prove a low-memory Kronecker ball check
`node3KS … ≤ Kb` (`norm3KS`, `center3KS`, `chebKV`) by an explicit certificate
(`chebKV_le_of_cert`); the default block level is `dB = 9` (`512` rows per block sum). The
witness is evaluated first and the bound compared, so a failing bound is reported here and not by
the kernel. -/
syntax (name := kronProof) "kron_proof" (ppSpace num)? : tactic

/-- The elaborator of `kron_proof`. -/
@[tactic kronProof] meta def evalKronProof : Tactic := fun stx => do
  let dB := match stx[1].getOptional? with
    | some n => n.isNatLit?.getD 9
    | none => 9
  let g ← getMainGoal
  let goal ← instantiateMVars (← g.getType)
  let pf ← kronProofTerm goal dB
  g.assign (← mkExpectedTypeHint pf goal)
  replaceMainGoal []

/-- **Sanity (accepted)**: the tactic on a toy image `3 − 5 = −2` (one digit `|−2| = 2`). -/
theorem kronProof_fixture :
    chebKV 8 2 1 1 0 1 2 0 0 0 0 (SInt.add ⟨false, 3⟩ ⟨true, 5⟩) ≤ 2 := by
  kron_proof

/-- **Sanity (rejected)**: the tactic refuses the false bound `2 ≤ 1` on the same toy image. -/
example : True := by
  fail_if_success
    have : chebKV 8 2 1 1 0 1 2 0 0 0 0 (SInt.add ⟨false, 3⟩ ⟨true, 5⟩) ≤ 1 := by kron_proof
  trivial

/-- **`kron_lt`**: prove a closed strict bound `a < c` on natural numbers by the kernel fact
`Nat.ble (a + 1) c = true` (`lt_of_ble_succ`), evaluated by the kernel only. -/
syntax (name := kronLt) "kron_lt" : tactic

/-- The elaborator of `kron_lt`. -/
@[tactic kronLt] meta def evalKronLt : Tactic := fun _ => do
  let g ← getMainGoal
  let goal ← instantiateMVars (← g.getType)
  let_expr LT.lt _ _ a c := goal | throwError "kron_lt: expected a goal `a < c` on `ℕ`"
  g.assign (← mkExpectedTypeHint
    (mkAppN (mkConst ``lt_of_ble_succ) #[a, c, reflBool true]) goal)
  replaceMainGoal []

/-- **Sanity**: `kron_lt` on a closed bound. -/
theorem kronLt_fixture : 2 ^ 10 + 1 < 2 ^ 11 := by
  kron_lt

end PlasmaLean.Certificates.KronProof
