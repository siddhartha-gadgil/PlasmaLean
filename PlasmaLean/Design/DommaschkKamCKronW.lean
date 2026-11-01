/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallGrid
public import PlasmaLean.Design.DommaschkKamCTorus
public import PlasmaLean.Certificates.KernelFact

/-!
# KronBall steps with general strip weights, oracle-angle constants, trees of sparse polynomials

Infrastructure of the low-resolution admissibility chain of Dommaschk torus C (N-33 plan item 8,
`Design/DommaschkKamCAdm*`).

**General strip weights.** The node, norm and centre steps of `Certificates/KronBallGrid`
(`node_full`, `norm_full`, `center_full`) fix the strip weights `74315^s 2^{16(K − s)}`, i.e.
`e^r ≤ 74315/2^16` (`r ≤ 0.1258`). The Dommaschk constants are sharp at `r = 0.045`, so here the
weights are `P^s 2^{E(K − s)}` with `e^r ≤ P/2^E` for arbitrary `P`, `E`: the kernel quantities
`nodeKw`, `normKw`, `centerKw` and the steps `node_fullw`, `norm_fullw`, `center_fullw`
(same proofs, through `Bd_ctr_of_wl1`). For torus C, `P = 68553`, `E = 16`
(`exp_dk_le : e^{9/200} ≤ 68553/2^16`).

**Oracle-angle constants.** The torus data are stored in the oracle angle `ψₒ = 2φ`
(`Design/DommaschkKamCTorus`), so the constant variables of the chain are `cos ψₒ = cSo` (the
polynomial `v² + 1` of weight `(0, 1, 0)`, `ctr_C_o`) and `sin ψₒ = sSo` (`v² − 1` of weight
`(0, 1, 1)`, `ctr_S_o`).

**Trees of sparse polynomials.** `polyT L ep mono p` is the expression tree (`KronExpr.Ex`) of the
sparse polynomial `p` (`DommaschkKam.DkPoly.SP`) scaled by `L`: the term `q u^a z^b c^c s^d` becomes
`(L q) · C^c S^d V^{ep − c − d} · X_{mono a b}`, with the monomial `u^a z^b` read from the variable
`mono a b`. `eval_polyT`: if `X 1 = 1`, every `L q` is an integer and every monomial variable has
the value `x₀^a x₁^b`, then `eval X (polyT L ep mono p) = L · ev x p`.

**Sanity.** `pwT_zero`, `polyT_single` (degenerate), `exp_dk_le` (concrete), `eval_polyT_fixture`
(an accepted two-term polynomial) and `polyT_reject` (the tree of a polynomial with a non-integral
scaled coefficient changes its value: the integrality hypothesis is needed).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex

/-! ## The strip weight of torus C -/

/-- `e^{9/200} ≤ 68553/2^16` (the Kronecker strip weight of the torus-C chain, `r = 0.045`). -/
theorem exp_dk_le : Real.exp (9 / 200) ≤ (68553 : ℕ) / 2 ^ 16 := by
  have h := Real.exp_bound' (x := 9 / 200) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-! ## Kernel quantities and steps with general weights -/

/-- The kernel quantity of a rounding node (weights `P^s 2^{E(K − s)}`). -/
def nodeKw (P Eb S N M : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (e : Ex) (c : ℤ)
    (dd de n b W dc dr J Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (J + 1) (fun i => kwtS P Eb Ki (ndist i ((1 + dd) * N)))
    (fun j => kwtS P Eb Kj (ndist j ((1 + dd) * M + (0 + de))))
    (Ex.evH Wt (Kv b W) e - c * (((2 : ℤ) ^ S * ((1 <<< (b * (N + W * M)) : ℕ) : ℤ)) ^ dd *
      (2 * ((1 <<< (b * W) : ℕ) : ℤ)) ^ de) * Kv b W n)

/-- The kernel quantity of a norm node (weights `P^s 2^{E(K − s)}`). -/
def normKw (P Eb N M : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (e : Ex)
    (w : ℕ × ℕ × ℕ) (b W dc dr J Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (J + 1) (fun i => kwtS P Eb Ki (ndist i (w.1 * N)))
    (fun j => kwtS P Eb Kj (ndist j (w.1 * M + w.2.1))) (Ex.evH Wt (Kv b W) e)

/-- The kernel quantity of a centre (weight `(1, 0, p)`, box `(2N, 2M)`). -/
def centerKw (P Eb N M : ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (i b W dc dr Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (2 * M + 1) (fun i => kwtS P Eb Ki (ndist i (1 * N)))
    (fun j => kwtS P Eb Kj (ndist j (1 * M + 0))) (Kv b W i)

/-- The radius budget of a node with general weights. -/
def nodeFinw (Eb S : ℕ) (B E : ℕ → ℚ) (e : Ex) (K Ki Kj dd de : ℕ) : ℚ :=
  Ex.dmajQ B E e + (K : ℚ) / 2 ^ (Eb * (Ki + Kj)) / 2 ^ (S * (1 + dd) + (0 + de))

/-- The radius budget of a norm node with general weights. -/
def normFinw (Eb S : ℕ) (B E : ℕ → ℚ) (e : Ex) (w : ℕ × ℕ × ℕ) (K Ki Kj : ℕ) : ℚ :=
  Ex.dmajQ B E e + (K : ℚ) / 2 ^ (Eb * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1)

/-- `Bd` of a centre from its kernel data, with general weights. -/
theorem Bd_ctr_kronw {r : ℝ} {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb) {S N M : ℕ}
    {w : ℕ × ℕ × ℕ} {G : P2} {a J W b dc dr Ki Kj K : ℕ} {Nv : ℤ} (hb : 1 ≤ b)
    (hbox : InBox G a J) (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr)
    (hl1 : l1 G < 2 ^ (b - 1)) (hk : kron b W G = Nv)
    (hK : wl1KronP b W dc dr (J + 1) (fun i => kwtS P Eb Ki (ndist i (w.1 * N)))
        (fun j => kwtS P Eb Kj (ndist j (w.1 * M + w.2.1))) Nv ≤ K) :
    Bd r (ctr S N M w G) (((K : ℚ) / 2 ^ (Eb * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1) : ℚ) : ℝ) := by
  have := Bd_ctr_of_wl1 (S := S) (N := N) (M := M) (w := w) hb hbox ha hW hJ hl1 hq Ki Kj
    (hk ▸ hK)
  push_cast
  exact this

/-- **One rounding node of a ball chain, general weights.** -/
theorem node_fullw {r : ℝ} (hr : 0 ≤ r) {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb)
    {S N M : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {Pl : ℕ → P2}
    {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox (Pl i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (Pl i) ≤ L i) (hPk : ∀ b W i, kron b W (Pl i) = Kv b W i) {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (Pl i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (dd de p : ℕ) (c : ℤ) (A J b W dc dr Ki Kj K : ℕ)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) (hc0 : c ≠ 0)
    (hdims : nodeDims N M Bx e dd de n A J b W dc dr)
    (hl1 : nodeL1 S L e c dd de n < 2 ^ (b - 1))
    (hK : nodeKw P Eb S N M Wt Kv e c dd de n b W dc dr J Ki Kj ≤ K)
    (hfin : nodeFinw Eb S B E e K Ki Kj dd de ≤ |(c : ℚ)| * E n)
    (hrel : (c : ℂ) • X n = Ex.eval X e) :
    Bd r (X n - x n) (E n) := by
  obtain ⟨hA, hJ, hA', hJ', hAW, hWd, hJd, hb⟩ := hdims
  obtain ⟨fb, fl, fk⟩ := node_facts (S := S) (N := N) (M := M) (Wt := Wt) hPbox hPl1 hPk e c n dd
    de A J b W hA hJ hA' hJ'
  have hG := Bd_ctr_kronw (S := S) (N := N) (M := M) (w := (1 + dd, 0 + de, p)) hq hb fb hAW hWd
    hJd (lt_of_le_of_lt fl hl1) fk hK
  refine node_step hr hW hx hB hE hv hwt hWn hc0 hrel hG ?_
  have : |(c : ℚ)| = ((|c| : ℤ) : ℚ) := by push_cast; rfl
  rw [← this]; exact hfin

/-- **One norm node of a ball chain, general weights**: `‖eval X e‖ ≤ Rq`. -/
theorem norm_fullw {r : ℝ} (hr : 0 ≤ r) {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb)
    {S N M : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {Pl : ℕ → P2}
    {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox (Pl i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (Pl i) ≤ L i) (hPk : ∀ b W i, kron b W (Pl i) = Kv b W i) {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (Pl i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (w : ℕ × ℕ × ℕ) (A J b W dc dr Ki Kj K : ℕ) (Rq : ℚ)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some w)
    (hdims : normDims Bx e A J b W dc dr)
    (hl1 : Ex.majN L e < 2 ^ (b - 1))
    (hK : normKw P Eb N M Wt Kv e w b W dc dr J Ki Kj ≤ K)
    (hfin : normFinw Eb S B E e w K Ki Kj ≤ Rq) :
    Bd r (Ex.eval X e) Rq := by
  obtain ⟨hA, hJ, hAW, hWd, hJd, hb⟩ := hdims
  have fb := (Ex.inBox_evH Wt hPbox e).mono hA hJ
  have fl := Ex.l1_evH Wt hPl1 e
  have fk : kron b W (Ex.evH Wt Pl e) = Ex.evH Wt (Kv b W) e := by
    rw [Ex.evH_map]; exact congrArg (fun y => Ex.evH Wt y e) (funext fun i => hPk b W i)
  have hG := Bd_ctr_kronw (S := S) (N := N) (M := M) (w := w) hq hb fb hAW hWd hJd
    (lt_of_le_of_lt fl hl1) fk hK
  have h := norm_step hr hW hx hB hE hv hwt hG
  refine h.le ?_
  have h2 : ((Ex.dmajQ B E e + ((K : ℚ) / 2 ^ (Eb * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1) : ℚ) :
      ℚ) : ℝ) ≤ (Rq : ℝ) := by unfold normFinw at hfin; exact_mod_cast hfin
  exact h2

/-- **The norm of one centre, general weights.** -/
theorem center_fullw {r : ℝ} {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb) {S N M : ℕ}
    {Wt : ℕ → ℕ × ℕ × ℕ} {Pl : ℕ → P2} {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℤ} (hPbox : ∀ i, InBox (Pl i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (Pl i) ≤ L i) (hPk : ∀ b W i, kron b W (Pl i) = Kv b W i) {x : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (Pl i)) (i p b W dc dr Ki Kj K : ℕ) (Bq : ℚ)
    (hWi : Wt i = (1, 0, p))
    (hdims : 2 * N < W ∧ W ≤ 2 ^ dc ∧ 2 * M + 1 ≤ 2 ^ dr ∧ 1 ≤ b)
    (hl1 : L i < 2 ^ (b - 1))
    (hBx : Bx i = (2 * N, 2 * M)) (hK : centerKw P Eb N M Kv i b W dc dr Ki Kj ≤ K)
    (hfin : (K : ℚ) / 2 ^ (Eb * (Ki + Kj)) / 2 ^ (S * 1 + 0) ≤ Bq) :
    Bd r (x i) Bq := by
  obtain ⟨hAW, hWd, hJd, hb⟩ := hdims
  have hbox := hPbox i
  rw [hBx] at hbox
  have h := Bd_ctr_kronw (S := S) (N := N) (M := M) (w := (1, 0, p)) hq hb hbox hAW hWd hJd
    (lt_of_le_of_lt (hPl1 i) hl1) (hPk b W i) hK
  rw [hx i, hWi]
  refine h.le ?_
  exact_mod_cast hfin

/-- **An exact step of a ball chain**: a variable whose value is its centre has radius `0`. -/
theorem step_exact_w {r : ℝ} {X x : FA} {e : ℚ} (h : X = x) (he : 0 ≤ e) : Bd r (X - x) e := by
  rw [h, sub_self]; exact (Bd_zero r).le (by exact_mod_cast he)

/-! ## The constant variables in the oracle angle -/

/-- `cos ψₒ` is the strip-algebra `sS` (both are `cos` of the algebra's second angle). -/
theorem cSo_eq : cSo = sS := rfl

/-- `sin ψₒ = −cS`. -/
theorem sSo_eq : sSo = -cS := by
  rw [sSo, cS, ← neg_smul]; congr 1; ring

/-- The centre of `C = v² + 1` (weight `(0, 1, 0)`) is `cos ψₒ`. -/
theorem ctr_C_o (S N M : ℕ) : ctr S N M (0, 1, 0) sPoly = cSo := by
  have hP : phiK sPoly = mode 0 (0, 2) + 1 := by
    rw [sPoly, map_add, phiK_monomial, phiK_monomial]
    simp [mode_zero_pair]
  rw [ctr, hP, add_mul, one_mul, mode_mul, cSo]
  have e1 : ((0 : ℤ), (2 : ℤ)) + -ofsW N M (0, 1, 0) = (0, 1) := by ext <;> simp [ofsW]
  have e2 : -ofsW N M (0, 1, 0) = (0, -1) := by ext <;> simp [ofsW]
  rw [e1, e2]
  have e3 : (scal S (0, 1, 0))⁻¹ = 1 / 2 := by
    simp only [scal, mul_zero, zero_add, pow_one, pow_zero, mul_one]
    norm_num
  rw [e3]

/-- The centre of `S = v² − 1` (weight `(0, 1, 1)`) is `sin ψₒ`. -/
theorem ctr_S_o (S N M : ℕ) : ctr S N M (0, 1, 1) cPoly = sSo := by
  have hP : phiK cPoly = mode 0 (0, 2) - 1 := by
    rw [cPoly, map_sub, phiK_monomial, phiK_monomial]
    simp [mode_zero_pair]
  rw [ctr, hP, sub_mul, one_mul, mode_mul, sSo]
  have e1 : ((0 : ℤ), (2 : ℤ)) + -ofsW N M (0, 1, 1) = (0, 1) := by ext <;> simp [ofsW]
  have e2 : -ofsW N M (0, 1, 1) = (0, -1) := by ext <;> simp [ofsW]
  rw [e1, e2]
  have e3 : (scal S (0, 1, 1))⁻¹ = -I / 2 := by
    simp only [scal, mul_zero, zero_add, pow_one]
    field_simp
    rw [I_sq]; ring
  rw [e3]

/-- `‖cos ψₒ‖_r ≤ P/2^E` on strips with `e^r ≤ P/2^E`. -/
theorem Bd_cSo_q {r : ℝ} {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb) :
    Bd r cSo (((P / 2 ^ Eb : ℚ) : ℚ) : ℝ) :=
  (Bd_sS r).le (by push_cast at hq ⊢; linarith)

/-- `‖sin ψₒ‖_r ≤ P/2^E` on strips with `e^r ≤ P/2^E`. -/
theorem Bd_sSo_q {r : ℝ} {P Eb : ℕ} (hq : Real.exp r ≤ (P : ℕ) / 2 ^ Eb) :
    Bd r sSo (((P / 2 ^ Eb : ℚ) : ℚ) : ℝ) := by
  rw [sSo_eq]; exact (Bd_cS r).neg.le (by push_cast at hq ⊢; linarith)

/-! ## Trees of sparse polynomials -/

/-- `acc` multiplied `n` times by the variable `v`. -/
def pwT (v : ℕ) : ℕ → Ex → Ex
  | 0, acc => acc
  | n + 1, acc => .mul (.var v) (pwT v n acc)

/-- The tree of one term `q u^a z^b c^c s^d`, scaled by `L` and homogenized to `V`-degree `ep`:
`(L q) · C^c (S^d (V^{ep − c − d} X_{mono a b}))`. -/
def termT (L : ℚ) (ep : ℕ) (mono : ℕ → ℕ → ℕ) (t : DkPoly.Tm) : Ex :=
  .mul (.cst (L * t.q).num) (pwT 2 t.c (pwT 3 t.d (pwT 1 (ep - t.c - t.d) (.var (mono t.a t.b)))))

/-- The tree of a sparse polynomial (right-nested sum of the term trees). -/
def polyT (L : ℚ) (ep : ℕ) (mono : ℕ → ℕ → ℕ) : DkPoly.SP → Ex
  | [] => .cst 0
  | [t] => termT L ep mono t
  | t :: p => .add (termT L ep mono t) (polyT L ep mono p)

/-- **Sanity (degenerate)**: no factor. -/
theorem pwT_zero (v : ℕ) (acc : Ex) : pwT v 0 acc = acc := rfl

/-- **Sanity (degenerate)**: a one-term polynomial is its term. -/
theorem polyT_single (L : ℚ) (ep : ℕ) (mono : ℕ → ℕ → ℕ) (t : DkPoly.Tm) :
    polyT L ep mono [t] = termT L ep mono t := rfl

/-- The value of `pwT`. -/
theorem eval_pwT (X : ℕ → FA) (v : ℕ) : ∀ (n : ℕ) (acc : Ex),
    Ex.eval X (pwT v n acc) = X v ^ n * Ex.eval X acc
  | 0, acc => by simp [pwT]
  | n + 1, acc => by simp only [pwT, Ex.eval, eval_pwT X v n acc]; ring

/-- An integral rational is the cast of its numerator. -/
theorem num_cast_of_den {q : ℚ} (h : q.den = 1) : ((q.num : ℤ) : ℂ) = ((q : ℚ) : ℂ) := by
  have : (q.num : ℚ) = q := Rat.coe_int_num_of_den_eq_one h
  rw [← this]; push_cast; rfl

/-- The value of one term tree. -/
theorem eval_termT (X : ℕ → FA) (hV : X 1 = 1) (x : Fin 6 → FA) (hx2 : x 2 = X 2)
    (hx3 : x 3 = X 3) (L : ℚ) (ep : ℕ) (mono : ℕ → ℕ → ℕ) (t : DkPoly.Tm)
    (hden : (L * t.q).den = 1) (hmono : X (mono t.a t.b) = x 0 ^ t.a * x 1 ^ t.b) :
    Ex.eval X (termT L ep mono t) = ((L : ℚ) : ℂ) • DkPoly.Tm.ev x t := by
  simp only [termT, Ex.eval, eval_pwT, hV, one_pow, one_mul, hmono, DkPoly.Tm.ev, ← hx2, ← hx3]
  have hc : ((((L * t.q).num : ℤ)) : FA) = algebraMap ℂ FA ((L : ℂ) * (t.q : ℂ)) := by
    rw [show ((((L * t.q).num : ℤ)) : FA) = algebraMap ℂ FA (((L * t.q).num : ℤ) : ℂ) by simp,
      num_cast_of_den hden]
    push_cast; rfl
  rw [hc, map_mul, Algebra.smul_def]
  ring

/-- **The value of a polynomial tree**: `eval X (polyT L ep mono p) = L · ev x p`. -/
theorem eval_polyT (X : ℕ → FA) (hV : X 1 = 1) (x : Fin 6 → FA) (hx2 : x 2 = X 2)
    (hx3 : x 3 = X 3) (L : ℚ) (ep : ℕ) (mono : ℕ → ℕ → ℕ) :
    ∀ (p : DkPoly.SP), p ≠ [] → (∀ t ∈ p, (L * t.q).den = 1) →
      (∀ t ∈ p, X (mono t.a t.b) = x 0 ^ t.a * x 1 ^ t.b) →
      Ex.eval X (polyT L ep mono p) = ((L : ℚ) : ℂ) • DkPoly.ev x p
  | [], h, _, _ => absurd rfl h
  | [t], _, hd, hm => by
    rw [polyT_single, eval_termT X hV x hx2 hx3 L ep mono t (hd t (by simp)) (hm t (by simp))]
    simp [DkPoly.ev]
  | t :: s :: p, _, hd, hm => by
    have ih := eval_polyT X hV x hx2 hx3 L ep mono (s :: p) (by simp)
      (fun u hu => hd u (List.mem_cons_of_mem _ hu)) (fun u hu => hm u (List.mem_cons_of_mem _ hu))
    rw [show polyT L ep mono (t :: s :: p) = .add (termT L ep mono t) (polyT L ep mono (s :: p))
      from rfl, Ex.eval, ih, eval_termT X hV x hx2 hx3 L ep mono t (hd t (by simp))
      (hm t (by simp))]
    simp only [DkPoly.ev, List.map_cons, List.sum_cons, smul_add]

/-- **Sanity (accepted)**: the tree of `2u + z/2` scaled by `2`, with `u = X 4`, `z = X 5`. -/
theorem eval_polyT_fixture (u z : FA) :
    Ex.eval (fun i => if i = 4 then u else if i = 5 then z else 1)
      (polyT 2 0 (fun a _ => if a = 1 then 4 else 5) [⟨2, 1, 0, 0, 0⟩, ⟨1 / 2, 0, 1, 0, 0⟩]) =
      ((2 : ℚ) : ℂ) • DkPoly.ev ![u, z, 1, 1, 0, 0] [⟨2, 1, 0, 0, 0⟩, ⟨1 / 2, 0, 1, 0, 0⟩] := by
  refine eval_polyT _ (by simp) _ (by simp) (by simp) _ _ _ _ (by simp) ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> norm_num
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp

/-- **Rejected fixture**: with the non-integral scaled coefficient `1 · (1/2)`, the tree has the
integer constant `num (1/2) = 1`, so its value is not `1 · (1/2)`: the integrality hypothesis of
`eval_polyT` cannot be dropped. -/
theorem polyT_reject :
    Ex.eval (fun _ => (1 : ℂ)) (polyT 1 0 (fun _ _ => 0) [⟨1 / 2, 0, 0, 0, 0⟩]) ≠ 1 / 2 := by
  norm_num [polyT, termT, pwT, Ex.eval]

end PlasmaLean.Design.DommaschkKamC
