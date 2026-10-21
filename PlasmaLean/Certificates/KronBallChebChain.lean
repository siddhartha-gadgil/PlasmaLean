/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebGrid

/-!
# Steps of family ball chains from kernel data

The family analogues of `KronBall.node_full`, `norm_full`, `center_full`
(`Certificates/KronBallGrid`): one rounding node, one norm node or one centre norm of a ball chain
of families (`Certificates/KronBallCheb`), valid **at every parameter value `|c| = 1` at once**,
from

* the degree boxes `InBox3`, static `ℓ¹` bounds and Kronecker images `Kv b W R i` of the variable
  polynomials (for grid families: `inBox3_famPoly`, `l1_flat_famPoly_le`, `famPack_eq`);
* one kernel evaluation of `chebK` (`Certificates/KronBallChebNorm`) on the Kronecker image of the
  truncation polynomial `G = evH e − c' T₃^{dd} V^{de} Q`, computed from the images of the
  variables by integer arithmetic (`node3_kron`);
* rational radius bookkeeping (`Ex.dmajQ`).

**Sanity.** `kron_flat_T3`: the image of `T₃` is `2^S X^{N + W(M + R D)}`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronDigits PlasmaLean.Theory.KAM
  Complex

/-! ## The images of `T₃` and `V` -/

/-- **Sanity**: the Kronecker image of `T₃ = 2^S uᴺ vᴹ wᴰ`. -/
theorem kron_flat_T3 (S N M D b W R : ℕ) :
    kron b W (flat R (T3 S N M D)) =
      (2 : ℤ) ^ S * ((1 <<< (b * (N + W * (M + R * D))) : ℕ) : ℤ) := by
  rw [T3, map_mul, map_mul, flat_C, kron_Tpoly, kron_flat_X_pow]
  simp only [Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

/-- The Kronecker image of `V = 2v`. -/
theorem kron_flat_V3 (b W R : ℕ) : kron b W (flat R V3) = 2 * ((1 <<< (b * W)) : ℕ) := by
  rw [V3, flat_C, kron_Vpoly]

/-- The degree box of `T₃`. -/
theorem inBox3_T3 (S N M D : ℕ) : InBox3 (T3 S N M D) N M D := by
  have h := (InBox3.C (InBox.monomial N M ((2 : ℤ) ^ S))).mul (InBox3.X_pow D)
  simpa [T3, Tpoly] using h

/-- The degree box of `V`. -/
theorem inBox3_V3 : InBox3 V3 0 1 0 := InBox3.C (InBox.monomial 0 1 2)

/-- The `ℓ¹` norm of the flattened `T₃`. -/
theorem l1_flat_T3 (S N M D R : ℕ) : l1 (flat R (T3 S N M D)) ≤ 2 ^ S := by
  rw [T3, map_mul, flat_C]
  refine (l1_mul_le _ _).trans ?_
  have h1 : l1 (flat R ((X : P3) ^ D)) = 1 := by
    have : flat R ((X : P3) ^ D) = monomial (R * D) (monomial 0 1) := by
      simp [flat, pow_mul, ← C_mul_X_pow_eq_monomial]
    rw [this, l1_monomial]; rfl
  rw [h1, mul_one]
  exact l1_Tpoly S N M

/-- The `ℓ¹` norm of the flattened `V`. -/
theorem l1_flat_V3 (R : ℕ) : l1 (flat R V3) ≤ 2 := by rw [V3, flat_C]; exact l1_Vpoly

/-! ## The data of a node polynomial -/

/-- **The data of a family node polynomial** `G = evH e − c' T₃^{dd} V^{de} Q`: degree box,
`ℓ¹` bound of the flattening and Kronecker image. -/
theorem node3_facts {S N M D : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P3} {Bx : ℕ → ℕ × ℕ × ℕ}
    {R : ℕ} {L : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ L i)
    (e : Ex) (c' : ℤ) (n dd de A J K b W : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i) (hA : (Ex.box3 Bx e).1 ≤ A)
    (hJ : (Ex.box3 Bx e).2.1 ≤ J) (hK : (Ex.box3 Bx e).2.2 ≤ K)
    (hA' : dd * N + (Bx n).1 ≤ A) (hJ' : dd * M + de + (Bx n).2.1 ≤ J)
    (hK' : dd * D + (Bx n).2.2 ≤ K) :
    InBox3 (Ex.evH Wt P e - Polynomial.C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * P n) A J K ∧
    l1 (flat R (Ex.evH Wt P e - Polynomial.C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * P n)) ≤
      Ex.majN L e + c'.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n) ∧
    kron b W (flat R (Ex.evH Wt P e - Polynomial.C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * P n)) =
      Ex.evH Wt (Kv b W R) e - c' * (((2 : ℤ) ^ S *
        ((1 <<< (b * (N + W * (M + R * D)))) : ℕ)) ^ dd * (2 * ((1 <<< (b * W)) : ℕ)) ^ de) *
          Kv b W R n := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (inBox3_evH Wt hPbox e).mono hA hJ hK
    have h2 := (((InBox3.C (Ex.inBox_intCast c')).mul
      ((inBox3_T3 S N M D).pow dd |>.mul (inBox3_V3.pow de))).mul (hPbox n))
    refine h1.sub (h2.mono ?_ ?_ ?_)
    · simp only [zero_add, mul_zero, add_zero]; linarith [mul_comm dd N]
    · simp only [zero_add]; nlinarith [mul_comm dd M]
    · simp only [zero_add, mul_zero, add_zero]; linarith [mul_comm dd D]
  · have hev : flat R (Ex.evH Wt P e) = Ex.evH Wt (fun i => flat R (P i)) e := Ex.evH_map _ Wt P e
    rw [map_sub (flat R), hev]
    refine (l1_sub_le _ _).trans (add_le_add (Ex.l1_evH Wt hPl1 e) ?_)
    rw [map_mul, map_mul, flat_C, map_mul, map_pow, map_pow, Ex.intCast_P2]
    have h1 := (l1_mul_le _ _).trans (Nat.mul_le_mul (l1_pow_le (l1_flat_T3 S N M D R) dd)
      (l1_pow_le (l1_flat_V3 R) de))
    calc l1 (Polynomial.C (Polynomial.C c') * (flat R (T3 S N M D) ^ dd * flat R V3 ^ de) *
          flat R (P n))
        ≤ l1 (Polynomial.C (Polynomial.C c') * (flat R (T3 S N M D) ^ dd * flat R V3 ^ de)) *
            l1 (flat R (P n)) := l1_mul_le _ _
      _ ≤ (c'.natAbs * l1 (flat R (T3 S N M D) ^ dd * flat R V3 ^ de)) * L n :=
          Nat.mul_le_mul (l1_C_mul_le _ _) (hPl1 n)
      _ ≤ (c'.natAbs * ((2 ^ S) ^ dd * 2 ^ de)) * L n :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (le_refl _)
      _ = c'.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n) := by ring
  · rw [map_sub (flat R), map_sub (kron b W), Ex.evH_map _ Wt P e, Ex.evH_map _ Wt _ e]
    simp only [map_mul, map_pow, kron_flat_T3, kron_flat_V3, map_intCast, hPk, Int.cast_id,
      Nat.cast_ofNat]

/-! ## Complete steps from kernel data -/

/-- The kernel quantity of a family rounding node. -/
def node3K (S N M D : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℕ → ℤ) (e : Ex) (c' : ℤ)
    (dd de n b W R Kw dr L fuel Ki Kj : ℕ) : ℕ :=
  chebK b W R Kw dr L fuel ((1 + dd) * N) ((1 + dd) * M + (0 + de)) Ki Kj
    (Ex.evH Wt (Kv b W R) e - c' * (((2 : ℤ) ^ S *
      ((1 <<< (b * (N + W * (M + R * D)))) : ℕ)) ^ dd * (2 * ((1 <<< (b * W)) : ℕ)) ^ de) *
        Kv b W R n)

/-- The kernel quantity of a family norm node (weight `w`). -/
def norm3K (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℕ → ℤ) (N M : ℕ) (e : Ex)
    (w : ℕ × ℕ × ℕ) (b W R Kw dr L fuel Ki Kj : ℕ) : ℕ :=
  chebK b W R Kw dr L fuel (w.1 * N) (w.1 * M + w.2.1) Ki Kj (Ex.evH Wt (Kv b W R) e)

/-- The kernel quantity of a family centre (weight `(1, 0, p)`). -/
def center3K (Kv : ℕ → ℕ → ℕ → ℕ → ℤ) (N M i b W R Kw dr L fuel Ki Kj : ℕ) : ℕ :=
  chebK b W R Kw dr L fuel (1 * N) (1 * M + 0) Ki Kj (Kv b W R i)

/-- The degree conditions of a family node. -/
def nodeDims3 (N M D : ℕ) (Bx : ℕ → ℕ × ℕ × ℕ) (e : Ex) (dd de n A J K b W R Kw dr L fuel : ℕ) :
    Prop :=
  (Ex.box3 Bx e).1 ≤ A ∧ (Ex.box3 Bx e).2.1 ≤ J ∧ (Ex.box3 Bx e).2.2 ≤ K ∧
    dd * N + (Bx n).1 ≤ A ∧ dd * M + de + (Bx n).2.1 ≤ J ∧ dd * D + (Bx n).2.2 ≤ K ∧
    A < W ∧ J < R ∧ K < Kw ∧ R * Kw ≤ 2 ^ dr ∧ W ≤ fuel * L ∧ 1 ≤ b

/-- The degree conditions of a family node are decidable. -/
instance (N M D : ℕ) (Bx : ℕ → ℕ × ℕ × ℕ) (e : Ex) (dd de n A J K b W R Kw dr L fuel : ℕ) :
    Decidable (nodeDims3 N M D Bx e dd de n A J K b W R Kw dr L fuel) := by
  unfold nodeDims3; infer_instance

/-- The degree conditions of a family norm node. -/
def normDims3 (Bx : ℕ → ℕ × ℕ × ℕ) (e : Ex) (A J K b W R Kw dr L fuel : ℕ) : Prop :=
  (Ex.box3 Bx e).1 ≤ A ∧ (Ex.box3 Bx e).2.1 ≤ J ∧ (Ex.box3 Bx e).2.2 ≤ K ∧
    A < W ∧ J < R ∧ K < Kw ∧ R * Kw ≤ 2 ^ dr ∧ W ≤ fuel * L ∧ 1 ≤ b

/-- The degree conditions of a family norm node are decidable. -/
instance (Bx : ℕ → ℕ × ℕ × ℕ) (e : Ex) (A J K b W R Kw dr L fuel : ℕ) :
    Decidable (normDims3 Bx e A J K b W R Kw dr L fuel) := by
  unfold normDims3; infer_instance

/-- **One rounding node of a family ball chain, from kernel data**: for every parameter value
`|c| = 1`, the radius `E n` of the new centre `x n` of `X n` (`c' · X n = eval X e`). -/
theorem node3_full {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x X : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (dd de p : ℕ) (c' : ℤ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) (hc0 : c' ≠ 0)
    (hdims : nodeDims3 N M D Bx e dd de n A J K b W R Kw dr L fuel)
    (hl1 : nodeL1 S Lv e c' dd de n < 2 ^ (b - 1))
    (hK : node3K S N M D Wt Kv e c' dd de n b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : nodeFin S B E e Kb Ki Kj dd de ≤ |(c' : ℚ)| * E n)
    (hrel : (c' : ℂ) • X n = Ex.eval X e) :
    Bd r (X n - x n) (E n) := by
  obtain ⟨hA, hJ, hK', hA', hJ', hK'', hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  obtain ⟨fb, fl, fk⟩ := node3_facts (S := S) (N := N) (M := M) (D := D) (Wt := Wt) hPbox hPl1
    e c' n dd de A J K b W hPk hA hJ hK' hA' hJ' hK''
  have hc0' : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hG := Bd_ctr3_kron (S := S) (N := N) (M := M) (D := D) (w := (1 + dd, 0 + de, p)) hq hc hb
    fb hAW hJR hKw hdr hfuel (lt_of_le_of_lt fl hl1) fk hK
  refine node_step3 hr hc0' hW hx hB hE hv hwt hWn hc0 hrel hG ?_
  rw [Int.cast_abs]
  exact hfin

/-- **One norm node of a family ball chain, from kernel data**: `‖eval X e‖ ≤ Rq` at every
parameter value `|c| = 1`. -/
theorem norm3_full {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x X : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (w : ℕ × ℕ × ℕ) (A J K b W Kw dr L fuel Ki Kj Kb : ℕ) (Rq : ℚ)
    (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some w)
    (hdims : normDims3 Bx e A J K b W R Kw dr L fuel)
    (hl1 : Ex.majN Lv e < 2 ^ (b - 1))
    (hK : norm3K Wt Kv N M e w b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : normFin S B E e w Kb Ki Kj ≤ Rq) :
    Bd r (Ex.eval X e) Rq := by
  obtain ⟨hA, hJ, hK', hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  have fb := (inBox3_evH Wt hPbox e).mono hA hJ hK'
  have hev : flat R (Ex.evH Wt P e) = Ex.evH Wt (fun i => flat R (P i)) e := Ex.evH_map _ Wt P e
  have fl : l1 (flat R (Ex.evH Wt P e)) ≤ Ex.majN Lv e := by rw [hev]; exact Ex.l1_evH Wt hPl1 e
  have fk : kron b W (flat R (Ex.evH Wt P e)) = Ex.evH Wt (Kv b W R) e := by
    rw [hev, Ex.evH_map]; exact congrArg (fun y => Ex.evH Wt y e) (funext fun i => hPk i)
  have hc0' : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hG := Bd_ctr3_kron (S := S) (N := N) (M := M) (D := D) (w := w) hq hc hb fb hAW hJR hKw hdr
    hfuel (lt_of_le_of_lt fl hl1) fk hK
  have h := norm_step3 hr hc0' hW hx hB hE hv hwt hG
  refine h.le ?_
  unfold normFin at hfin
  exact_mod_cast hfin

/-- **The norm of one family centre, from kernel data.** -/
theorem center3_full {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ}
    {c : ℂ} (hc : ‖c‖ = 1) {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P3}
    {Bx : ℕ → ℕ × ℕ × ℕ} {R : ℕ} {Lv : ℕ → ℕ} {Kv : ℕ → ℕ → ℕ → ℕ → ℤ}
    (hPbox : ∀ i, InBox3 (P i) (Bx i).1 (Bx i).2.1 (Bx i).2.2)
    (hPl1 : ∀ i, l1 (flat R (P i)) ≤ Lv i)
    {x : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) (i p b W Kw dr L fuel Ki Kj Kb : ℕ)
    (Bq : ℚ) (hPk : ∀ i, kron b W (flat R (P i)) = Kv b W R i) (hWi : Wt i = (1, 0, p))
    (hdims : (Bx i).1 < W ∧ (Bx i).2.1 < R ∧ (Bx i).2.2 < Kw ∧ R * Kw ≤ 2 ^ dr ∧
      W ≤ fuel * L ∧ 1 ≤ b)
    (hl1 : Lv i < 2 ^ (b - 1)) (hK : center3K Kv N M i b W R Kw dr L fuel Ki Kj ≤ Kb)
    (hfin : (Kb : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * 1 + 0) ≤ Bq) :
    Bd r (x i) Bq := by
  obtain ⟨hAW, hJR, hKw, hdr, hfuel, hb⟩ := hdims
  have h := Bd_ctr3_kron (S := S) (N := N) (M := M) (D := D) (w := (1, 0, p)) hq hc hb (hPbox i)
    hAW hJR hKw hdr hfuel (lt_of_le_of_lt (hPl1 i) hl1) (hPk i) hK
  rw [hx i, hWi]
  refine h.le ?_
  exact_mod_cast hfin

end PlasmaLean.Certificates.KronBallCheb
