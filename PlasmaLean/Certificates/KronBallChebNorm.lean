/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallCheb
public import PlasmaLean.Certificates.KronBallChebDigits

/-!
# Norms of families from Kronecker images

The strip norm of a family centre `ctr3 c w P` (`Certificates/KronBallCheb`), **uniformly in the
parameter value `c` on the unit circle**, from one kernel computation on the Kronecker image of
`P ∈ ℤ[u][v][w]`:

* `flat R : ℤ[u][v][w] →+* ℤ[u][v]` substitutes `w ↦ v^R`; for polynomials whose coefficients in
  `w` have `v`-degree below `R` (`InBox3`) the slots of `flat R P` are the slots of the Chebyshev
  coefficients (`slot_flat`), so the Kronecker image `kron b W (flat R P)` stores all coefficients
  side by side (rows `j + R k`);
* `chebK`: the kernel quantity — absolute digits by masks (`KronDigits.absDig`), rows by
  divide and conquer (`pdig`), and block sums along rows (`KronDigits.rowBlk`) with the separable
  weights `p^s 2^{e(K − s)}` dominating `e^{r s}`;
* **`Bd_ctr3_kron`**: `‖ctr3 c w P‖_r ≤ K / 2^{e(K_i + K_j)} / 2^{S d + e}` for every `|c| = 1`
  whenever `chebK ≤ K`.

Degree boxes of trees of families: `InBox3`, `Ex.box3`, `inBox3_evH`.

**Sanity.** `kwtS_mono` (the weights grow with the distance), `flat_C` (constants in `w` are not
moved).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronDigits PlasmaLean.Theory.KAM
  Complex

/-! ## Flattening -/

/-- `w ↦ v^R`. -/
def flat (R : ℕ) : P3 →+* P2 := eval₂RingHom (RingHom.id P2) (X ^ R)

/-- **Sanity**: constants in `w` are not moved. -/
theorem flat_C (R : ℕ) (P : P2) : flat R (C P) = P := by simp [flat]

/-- `flat` as a sum. -/
theorem flat_eq_sum (R : ℕ) (P : P3) :
    flat R P = ∑ k ∈ range (P.natDegree + 1), P.coeff k * X ^ (R * k) := by
  rw [flat, coe_eval₂RingHom, eval₂_eq_sum_range]
  simp [pow_mul]

/-- The degree box of a family: `w`-degree `≤ K`, every coefficient in the box `(a, J)`. -/
def InBox3 (P : P3) (a J K : ℕ) : Prop := P.natDegree ≤ K ∧ ∀ k, InBox (P.coeff k) a J

/-- Degree boxes are monotone. -/
theorem InBox3.mono {P : P3} {a J K a' J' K' : ℕ} (h : InBox3 P a J K) (ha : a ≤ a')
    (hJ : J ≤ J') (hK : K ≤ K') : InBox3 P a' J' K' :=
  ⟨h.1.trans hK, fun k => (h.2 k).mono ha hJ⟩

/-- Degree boxes of sums. -/
theorem InBox3.add {P Q : P3} {a J K : ℕ} (hP : InBox3 P a J K) (hQ : InBox3 Q a J K) :
    InBox3 (P + Q) a J K :=
  ⟨(natDegree_add_le _ _).trans (max_le hP.1 hQ.1), fun k => by
    rw [Polynomial.coeff_add]; exact (hP.2 k).add (hQ.2 k)⟩

/-- Degree boxes of negatives. -/
theorem InBox3.neg {P : P3} {a J K : ℕ} (hP : InBox3 P a J K) : InBox3 (-P) a J K :=
  ⟨by rw [natDegree_neg]; exact hP.1, fun k => by rw [Polynomial.coeff_neg]; exact (hP.2 k).neg⟩

/-- Degree boxes of differences. -/
theorem InBox3.sub {P Q : P3} {a J K : ℕ} (hP : InBox3 P a J K) (hQ : InBox3 Q a J K) :
    InBox3 (P - Q) a J K :=
  ⟨(natDegree_sub_le _ _).trans (max_le hP.1 hQ.1), fun k => by
    rw [Polynomial.coeff_sub]; exact (hP.2 k).sub (hQ.2 k)⟩

/-- Degree boxes of products. -/
theorem InBox3.mul {P Q : P3} {a J K a' J' K' : ℕ} (hP : InBox3 P a J K) (hQ : InBox3 Q a' J' K') :
    InBox3 (P * Q) (a + a') (J + J') (K + K') :=
  ⟨natDegree_mul_le.trans (add_le_add hP.1 hQ.1), fun k => by
    rw [Polynomial.coeff_mul]
    exact InBox.sum _ fun x _ => (hP.2 x.1).mul (hQ.2 x.2)⟩

/-- Degree boxes of polynomials constant in `w`. -/
theorem InBox3.C {P : P2} {a J : ℕ} (h : InBox P a J) : InBox3 (C P) a J 0 :=
  ⟨by simp, fun k => by
    rw [coeff_C]; split_ifs
    · exact h
    · exact ⟨by simp, fun j => by simp⟩⟩

/-- Degree boxes of integers. -/
theorem InBox3.intCast (k : ℤ) : InBox3 (k : P3) 0 0 0 := by
  have : (k : P3) = Polynomial.C (k : P2) := by simp
  rw [this]; exact InBox3.C (Ex.inBox_intCast k)

/-- Degree boxes of powers of `w`. -/
theorem InBox3.X_pow (D : ℕ) : InBox3 ((X : P3) ^ D) 0 0 D :=
  ⟨by simp, fun k => by
    rw [coeff_X_pow]; split_ifs
    · exact ⟨by simp, fun j => by rw [Polynomial.coeff_one]; split_ifs <;> simp⟩
    · exact ⟨by simp, fun j => by simp⟩⟩

/-- Degree boxes of powers. -/
theorem InBox3.pow {P : P3} {a J K : ℕ} (h : InBox3 P a J K) :
    ∀ n : ℕ, InBox3 (P ^ n) (n * a) (n * J) (n * K)
  | 0 => by
    simpa using InBox3.C (P := 1)
      ⟨by simp, fun j => by rw [Polynomial.coeff_one]; split_ifs <;> simp⟩
  | n + 1 => by
    rw [pow_succ, show (n + 1) * a = n * a + a by ring, show (n + 1) * J = n * J + J by ring,
      show (n + 1) * K = n * K + K by ring]
    exact (InBox3.pow h n).mul h

/-- Degree box of a tree of families. -/
def Ex.box3 (Bx : ℕ → ℕ × ℕ × ℕ) : Ex → ℕ × ℕ × ℕ
  | .var i => Bx i
  | .cst _ => (0, 0, 0)
  | .add e f => (max (Ex.box3 Bx e).1 (Ex.box3 Bx f).1, max (Ex.box3 Bx e).2.1 (Ex.box3 Bx f).2.1,
      max (Ex.box3 Bx e).2.2 (Ex.box3 Bx f).2.2)
  | .sub e f => (max (Ex.box3 Bx e).1 (Ex.box3 Bx f).1, max (Ex.box3 Bx e).2.1 (Ex.box3 Bx f).2.1,
      max (Ex.box3 Bx e).2.2 (Ex.box3 Bx f).2.2)
  | .mul e f => ((Ex.box3 Bx e).1 + (Ex.box3 Bx f).1, (Ex.box3 Bx e).2.1 + (Ex.box3 Bx f).2.1,
      (Ex.box3 Bx e).2.2 + (Ex.box3 Bx f).2.2)

/-- **Degree box** of the phased evaluation of a tree of families. -/
theorem inBox3_evH {Bx : ℕ → ℕ × ℕ × ℕ} (W : ℕ → ℕ × ℕ × ℕ) {x : ℕ → P3}
    (hx : ∀ i, InBox3 (x i) (Bx i).1 (Bx i).2.1 (Bx i).2.2) :
    ∀ e : Ex, InBox3 (Ex.evH W x e) (Ex.box3 Bx e).1 (Ex.box3 Bx e).2.1 (Ex.box3 Bx e).2.2
  | .var i => hx i
  | .cst k => InBox3.intCast k
  | .add e f => by
    have h1 := inBox3_evH W hx e
    have h2 := (InBox3.intCast (Ex.sgn W e f)).mul (inBox3_evH W hx f)
    simp only [zero_add] at h2
    exact (h1.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)).add
      (h2.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _))
  | .sub e f => by
    have h1 := inBox3_evH W hx e
    have h2 := (InBox3.intCast (Ex.sgn W e f)).mul (inBox3_evH W hx f)
    simp only [zero_add] at h2
    exact (h1.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)).sub
      (h2.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _))
  | .mul e f => (inBox3_evH W hx e).mul (inBox3_evH W hx f)

/-- `flat` as a sum over any range beyond the degree. -/
theorem flat_eq_sum' (R : ℕ) (P : P3) {n : ℕ} (hn : P.natDegree < n) :
    flat R P = ∑ k ∈ range n, P.coeff k * X ^ (R * k) := by
  rw [flat, coe_eval₂RingHom, eval₂_eq_sum_range' _ hn]
  simp [pow_mul]

/-- The coefficients of a flattened family. -/
theorem coeff_flat {P : P3} {a J K R : ℕ} (hbox : InBox3 P a J K) (hJ : J < R) (j k : ℕ)
    (hj : j < R) : (flat R P).coeff (j + R * k) = (P.coeff k).coeff j := by
  rw [flat_eq_sum' R P (n := P.natDegree + k + 1) (by omega), finsetSum_coeff,
    sum_eq_single k]
  · rw [coeff_mul_X_pow]
  · intro k' _ hk'
    rw [coeff_mul_X_pow']
    split_ifs with h
    · rcases Nat.lt_or_gt_of_ne hk' with h' | h'
      · have h1 : R * k' + R ≤ R * k := by nlinarith
        have : J < j + R * k - R * k' := by omega
        exact coeff_eq_zero_of_natDegree_lt ((hbox.2 k').1.trans_lt this)
      · exfalso
        have : R * k + R ≤ R * k' := by nlinarith
        omega
    · rfl
  · intro h; simp at h

/-- **Slots of a flattened family** are the slots of its coefficients. -/
theorem slot_flat {P : P3} {a J K R W : ℕ} (hbox : InBox3 P a J K) (hJ : J < R) {i j k : ℕ}
    (hi : i < W) (hj : j < R) :
    slot (flat R P) W (i + W * (j + R * k)) = slot (P.coeff k) W (i + W * j) := by
  rw [slot_add_mul hi, slot_add_mul hi, coeff_flat hbox hJ j k hj]

/-- The box of a flattened family. -/
theorem inBox_flat {P : P3} {a J K R : ℕ} (hbox : InBox3 P a J K) :
    InBox (flat R P) a (J + R * K) := by
  rw [flat_eq_sum]
  refine InBox.sum _ fun k hk => ?_
  have hk' : k ≤ K := by have := hbox.1; simp at hk; omega
  have h1 : InBox ((X : P2) ^ (R * k)) 0 (R * k) := by
    rw [show ((X : P2) ^ (R * k)) = monomial (R * k) (monomial 0 1) by
      simp [← C_mul_X_pow_eq_monomial]]
    exact InBox.monomial 0 (R * k) 1
  have := (hbox.2 k).mul h1
  refine this.mono (by simp) ?_
  have : R * k ≤ R * K := Nat.mul_le_mul_left _ hk'
  omega

/-- The `ℓ¹` norm of a flattened family is at most the sum over its coefficients. -/
theorem l1_flat_le (R : ℕ) (P : P3) :
    l1 (flat R P) ≤ ∑ k ∈ range (P.natDegree + 1), l1 (P.coeff k) := by
  rw [flat_eq_sum]
  refine (l1_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  refine (l1_mul_le _ _).trans ?_
  have : l1 ((X : P2) ^ (R * k)) = 1 := by
    rw [show ((X : P2) ^ (R * k)) = monomial (R * k) (monomial 0 1) by
      simp [← C_mul_X_pow_eq_monomial], l1_monomial]; rfl
  rw [this, mul_one]

/-! ## The weights -/

/-- **Sanity / monotonicity**: the integer weights `p^s 2^{e(K − s)}` grow with `s` when
`2^e ≤ p`. -/
theorem kwtS_mono {p e K s s' : ℕ} (hp : 2 ^ e ≤ p) (hs : s ≤ s') :
    kwtS p e K s ≤ kwtS p e K s' := by
  unfold kwtS
  obtain ⟨t, rfl⟩ : ∃ t, s' = s + t := ⟨s' - s, by omega⟩
  have h1 : 2 ^ (e * (K - s)) ≤ 2 ^ (e * t) * 2 ^ (e * (K - (s + t))) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num)
      (by rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega))
  have h2 : 2 ^ (e * t) ≤ p ^ t := by rw [pow_mul]; exact Nat.pow_le_pow_left hp t
  calc p ^ s * 2 ^ (e * (K - s)) ≤ p ^ s * (2 ^ (e * t) * 2 ^ (e * (K - (s + t)))) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ p ^ s * (p ^ t * 2 ^ (e * (K - (s + t)))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ = p ^ (s + t) * 2 ^ (e * (K - (s + t))) := by rw [pow_add]; ring

/-- The column weights are block-monotone. -/
theorem blockMono_kwtS {p e K i₀ : ℕ} (hp : 2 ^ e ≤ p) :
    BlockMono (fun i => kwtS p e K (ndist i i₀)) := by
  intro i m t ht
  simp only
  by_cases h : ndist (i + t) i₀ ≤ ndist i i₀
  · exact le_max_of_le_left (kwtS_mono hp h)
  · refine le_max_of_le_right (kwtS_mono hp ?_)
    unfold ndist at h ⊢
    omega

/-! ## The kernel quantity and the norm bound -/

/-- The light copies are the originals. -/
theorem pdigL_eq : pdigL = pdig := rfl

/-- The light weight is `kwtS`. -/
theorem kwtSL_eq : kwtSL = kwtS := rfl

/-- The light distance is `ndist`. -/
theorem ndistL_eq : ndistL = ndist := rfl

/-- An expansion read as rows. -/
theorem dexp_rows (b W : ℕ) (a : ℕ → ℕ) (Rows : ℕ) :
    dexp b a (W * Rows) =
      ∑ j ∈ range Rows, dexp b (fun i => a (i + W * j)) W * (2 ^ (b * W)) ^ j := by
  induction Rows with
  | zero => simp
  | succ Rows ih =>
    rw [Nat.mul_succ, dexp_add, ih, sum_range_succ]
    congr 1
    rw [dexp, dexp, mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm (W * Rows) i, ← pow_mul, ← mul_assoc]
    ring

/-- **The kernel quantity bounds the weighted slot sum** of a polynomial `P ∈ ℤ[u][v]` given by
its Kronecker image (rows `j` weighted by `j mod R`). -/
theorem sum_le_chebK {P : P2} {a J' b W R Kw dr L fuel i₀ j₀ Ki Kj : ℕ} {Nv : ℤ} (hb : 1 ≤ b)
    (hbox : InBox P a J') (ha : a < W) (hJ' : J' + 1 ≤ R * Kw) (hdr : R * Kw ≤ 2 ^ dr)
    (hfuel : W ≤ fuel * L) (hl1 : l1 P < 2 ^ (b - 1)) (hk : kron b W P = Nv) :
    ∑ j ∈ range (R * Kw), kwtS 74315 16 Kj (ndist (j % R) j₀) *
        ∑ i ∈ range W, kwtS 74315 16 Ki (ndist i i₀) * (slot P W (i + W * j)).natAbs ≤
      chebK b W R Kw dr L fuel i₀ j₀ Ki Kj Nv := by
  set H := 2 ^ (b - 1) with hH
  have hbH : 2 ^ b = 2 * H := by rw [hH, ← pow_succ']; congr 1; omega
  set Ntot := W * (R * Kw) with hNtot
  have hS : W * (J' + 1) ≤ Ntot := Nat.mul_le_mul_left _ hJ'
  have hsl : ∀ n, (slot P W n).natAbs < H := fun n =>
    (natAbs_coeff_le_l1 P _ _).trans_lt hl1
  set e : ℕ → ℕ := fun n => (slot P W n + H).toNat with he_def
  have he_int : ∀ n, ((e n : ℕ) : ℤ) = slot P W n + H := fun n => by
    have := hsl n
    simp only [he_def]
    rw [Int.toNat_of_nonneg (by omega)]
  have hbHz : (2 : ℤ) ^ b = 2 * (H : ℤ) := by exact_mod_cast hbH
  have he_lt : ∀ n, e n < 2 ^ b := fun n => by
    have h1 := he_int n; have h2 := hsl n
    have : ((e n : ℕ) : ℤ) < 2 ^ b := by rw [h1, hbHz]; omega
    exact_mod_cast this
  -- the offset integer is the expansion of the offset digits
  have hT : (Nv + ((H * onesK b Ntot : ℕ) : ℤ)).toNat = dexp b e Ntot := by
    rw [← hk, kron_eq_sum b hbox ha hS, onesK_eq b Ntot hb, mul_dexp]
    have : (∑ n ∈ range Ntot, slot P W n * ((2 : ℤ) ^ b) ^ n) +
        ((dexp b (fun _ => H * 1) Ntot : ℕ) : ℤ) = ((dexp b e Ntot : ℕ) : ℤ) := by
      simp only [dexp]
      push_cast
      rw [← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [he_int n, ← pow_mul]; ring
    rw [this, Int.toNat_natCast]
  -- absolute digits
  have hA : absDig b Ntot (dexp b e Ntot) = dexp b (fun n => (slot P W n).natAbs) Ntot := by
    rw [absDig_dexp hb fun n _ => he_lt n]
    refine dexp_congr b Ntot fun n _ => ?_
    have h1 := he_int n
    omega
  -- rows
  set row : ℕ → ℕ := fun j => if j < R * Kw then
    dexp b (fun i => (slot P W (i + W * j)).natAbs) W else 0 with hrow
  have hrow_lt : ∀ j, row j < 2 ^ (b * W) := fun j => by
    simp only [hrow]; split_ifs
    · exact dexp_lt fun i _ => (hsl _).trans (by rw [hbH]; omega)
    · positivity
  have hrows : dexp b (fun n => (slot P W n).natAbs) Ntot =
      ∑ n ∈ range (2 ^ dr), row (0 + n) * (2 ^ (b * W)) ^ n := by
    rw [hNtot, dexp_rows]
    rw [← sum_subset (range_subset_range.2 hdr) fun n _ hn => by
      have : ¬ n < R * Kw := by simpa using hn
      simp [hrow, this]]
    refine sum_congr rfl fun n hn => ?_
    have : n < R * Kw := mem_range.1 hn
    simp [hrow, this]
  rw [chebK, pdigL_eq, kwtSL_eq, ndistL_eq, ← hH, hT, hA, hrows,
    pdig_spec (b * W) _ row hrow_lt dr 0 (R * Kw), min_eq_left hdr]
  refine sum_le_sum fun j hj => ?_
  have hj' : j < R * Kw := mem_range.1 hj
  simp only [zero_add, hrow, hj', ↓reduceIte]
  refine Nat.mul_le_mul_left _ ?_
  have hsum : ∑ t ∈ range W, (slot P W (t + W * j)).natAbs < 2 ^ b - 1 := by
    have h1 : ∑ t ∈ range W, (slot P W (t + W * j)).natAbs ≤ l1 P := by
      rw [l1_eq_sum hbox ha hS, hNtot, sum_range_mul_eq]
      exact single_le_sum (f := fun j => ∑ t ∈ range W, (slot P W (t + W * j)).natAbs)
        (fun _ _ => Nat.zero_le _) hj
    omega
  have := sum_le_rowBlk (b := b) (L := L)
    (blockMono_kwtS (p := 74315) (e := 16) (K := Ki) (i₀ := i₀) (by norm_num))
    fuel 0 W (fun t => (slot P W (t + W * j)).natAbs)
    (fun t _ => (hsl _).trans (by rw [hbH]; omega))
    hsum hfuel
  simpa using this

/-- The weighted slot sums of the Chebyshev coefficients are the row-weighted slot sum of the
flattened family. -/
theorem sum_slices_eq {G : P3} {a J K R W Kw : ℕ} (hbox : InBox3 G a J K) (hJR : J < R)
    (hW : 0 < W) (i₀ j₀ Ki Kj : ℕ) :
    ∑ k ∈ range Kw, ∑ n ∈ range (W * R),
        sepWt 74315 16 W i₀ j₀ Ki Kj n * (slot (G.coeff k) W n).natAbs =
      ∑ j ∈ range (R * Kw), kwtS 74315 16 Kj (ndist (j % R) j₀) *
        ∑ i ∈ range W, kwtS 74315 16 Ki (ndist i i₀) * (slot (flat R G) W (i + W * j)).natAbs := by
  rw [sum_range_mul_eq (fun j => kwtS 74315 16 Kj (ndist (j % R) j₀) *
      ∑ i ∈ range W, kwtS 74315 16 Ki (ndist i i₀) * (slot (flat R G) W (i + W * j)).natAbs) R Kw]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_range_mul_eq _ W R]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < R := mem_range.1 hj
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < W := mem_range.1 hi
  rw [sepWt, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hi', zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hi', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj',
    slot_flat hbox hJR hi' hj']
  ring

/-- **The norm of a family centre from kernel data**: if the kernel quantity of the Kronecker
image of `flat R G` is at most `Kb`, then for every parameter value `|c| = 1` the family centre
`ctr3 c w G` has strip norm at most `Kb / 2^{16(K_i + K_j)} / 2^{S d + e}` (strips with
`e^r ≤ 74315/2^16`). -/
theorem Bd_ctr3_kron {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M D : ℕ} {c : ℂ}
    (hc : ‖c‖ = 1) {w : ℕ × ℕ × ℕ} {G : P3} {a J K b W R Kw dr L fuel Ki Kj Kb : ℕ} {Nv : ℤ}
    (hb : 1 ≤ b) (hbox : InBox3 G a J K) (ha : a < W) (hJR : J < R) (hK : K < Kw)
    (hdr : R * Kw ≤ 2 ^ dr) (hfuel : W ≤ fuel * L) (hl1 : l1 (flat R G) < 2 ^ (b - 1))
    (hk : kron b W (flat R G) = Nv)
    (hKb : chebK b W R Kw dr L fuel (w.1 * N) (w.1 * M + w.2.1) Ki Kj Nv ≤ Kb) :
    Bd r (ctr3 S N M D c w G)
      (((Kb : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1) : ℚ) : ℝ) := by
  have hW : 0 < W := by omega
  set i₀ := w.1 * N
  set j₀ := w.1 * M + w.2.1
  set C : ℝ := 2 ^ (16 * (Ki + Kj)) with hC
  have hCpos : 0 < C := by positivity
  set sk : ℕ → ℕ := fun k => ∑ n ∈ range (W * R),
    sepWt 74315 16 W i₀ j₀ Ki Kj n * (slot (G.coeff k) W n).natAbs with hsk
  -- each Chebyshev coefficient
  have hslice : ∀ k, k ≤ Kw - 1 → Bd r (ctr S N M w (G.coeff k))
      ((sk k : ℝ) / C / 2 ^ (S * w.1 + w.2.1)) := fun k _ => by
    obtain ⟨h1, h2⟩ := wnorm_coefZ2_le (hbox.2 k) ha (Nat.mul_le_mul_left W hJR) i₀ j₀
      (sepWt 74315 16 W i₀ j₀ Ki Kj) (fun n => exp_le_sepWt hq _ i₀ j₀ Ki Kj n)
    refine Bd_ctr h1 ?_
    rw [le_div_iff₀ hCpos]
    exact h2
  have h3 := Bd_ctr3_of_slices S N M D hc w G (Kw - 1) (by have := hbox.1; omega) _ hslice
  refine h3.le ?_
  rw [show Kw - 1 + 1 = Kw by omega, ← sum_div, ← sum_div]
  have hsum : ∑ k ∈ range Kw, (sk k : ℝ) ≤ Kb := by
    rw [← Nat.cast_sum]
    have := (sum_slices_eq (Kw := Kw) hbox hJR hW i₀ j₀ Ki Kj).le.trans
      ((sum_le_chebK hb (inBox_flat hbox) ha (by
        have : R * K + R ≤ R * Kw := by nlinarith
        omega) hdr hfuel hl1 hk).trans hKb)
    exact_mod_cast this
  push_cast
  gcongr

end PlasmaLean.Certificates.KronBallCheb
