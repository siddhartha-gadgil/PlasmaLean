/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallChebFam

/-!
# Environments of family ball chains

The facts used by the generated environments of family ball chains
(`Design/RationalStellaratorGCFamEnv*`):

* `kron_famTB`: the Kronecker image of a stored family is the fast offset image `famTB − famO`,
  under static conditions on the stored coefficients (`FamStatic`, decided once per family) and
  width conditions (`FamDyn`, monotone in `b` and `W`: `FamDyn.mono`);
* `famPoly_congr`: families with the same coefficient grids on the box are equal (used for
  derivatives stored as data);
* the **parameter polynomial** `Pr3 = 64 T₃ + 2^{S−1} uᴺ vᴹ (w^{D+1} + w^{D−1})`, whose family
  centre is `64 + (c + c⁻¹)/2` (`ctr3_Pr3`), i.e. `64 + cos ϑ` at `c = e^{iϑ}`;
* renaming the variables of light trees (`ExN.rename`, `rel_rename`) and congruence of
  evaluations on the variables of a tree (`rel_congr`), to transfer node identities between ball
  pipelines.

**Sanity.** `ctr_Tpoly'`: the centre of `2^{S'} uᴺ vᴹ` at scale `2^S` is `2^{S'−S}`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronDigits PlasmaLean.Theory.KAM
  Complex WEll1Z2

/-! ## Stored families -/

/-- The static conditions on a stored family (layout `(N, M, D)`, reading levels `dd`, `dr`,
`dw`). -/
def FamStatic (N M D dd dr dw : ℕ) (l : List SliceData) : Prop :=
  1 ≤ l.length ∧ l.length - 1 ≤ D ∧ 2 * (l.length - 1) + 1 ≤ 2 ^ dw ∧
    ∀ sd ∈ l, SliceOK N M dd dr sd ∧ (2 * sd.Mj + 1) * sd.Nj ≤ 2 ^ sd.k1 ∧
      2 * sd.Mj + 1 ≤ 2 ^ sd.k2

/-- The static conditions are decidable. -/
instance (N M D dd dr dw : ℕ) (l : List SliceData) : Decidable (FamStatic N M D dd dr dw l) := by
  unfold FamStatic; infer_instance

/-- The width conditions on a stored family with symbol `c₀`. -/
def FamDyn (b W c0 : ℕ) (l : List SliceData) : Prop :=
  1 ≤ b ∧ 1 ≤ W ∧ ∀ sd ∈ l, sd.Fj ≤ b ∧ 2 * c0 * 2 ^ (sd.Fj - 1) ≤ 2 ^ (b - 1) ∧ sd.Nj ≤ W

/-- The width conditions are decidable. -/
instance (b W c0 : ℕ) (l : List SliceData) : Decidable (FamDyn b W c0 l) := by
  unfold FamDyn; infer_instance

/-- The width conditions are monotone. -/
theorem FamDyn.mono {b W b' W' c0 : ℕ} {l : List SliceData} (h : FamDyn b W c0 l) (hb : b ≤ b')
    (hW : W ≤ W') : FamDyn b' W' c0 l := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, fun sd hsd => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h3 sd hsd
  refine ⟨by omega, e2.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), by omega⟩

/-- **The Kronecker image of a stored family** is its fast offset image. -/
theorem kron_famTB {N M D dd dr dw b W c0 : ℕ} {l : List SliceData}
    (hs : FamStatic N M D dd dr dw l) (hd : FamDyn b W c0 l) (odd : Bool) (R : ℕ) :
    kron b W (flat R (famPoly N M D (if odd then -1 else 1) (c0 : ℤ) 0 0 0 l)) =
      ((famTB b W R N M D c0 odd dr dw l : ℕ) : ℤ) - ((famO b W R N M D dw l : ℕ) : ℤ) := by
  obtain ⟨hl, hD, hdw, hsl⟩ := hs
  obtain ⟨hb, hW, hdl⟩ := hd
  rw [← famPack_eq b W R N M D _ _ 0 0 0 l fun sd h => (hsl sd h).1,
    ← famPackN_eq b W R N M D c0 odd hb hW 0 l fun sd h => ⟨(hsl sd h).1, (hdl sd h).2.1⟩,
    ← famT_sub_famO b W R N M D c0 odd dd dr dw l hl hD hdw,
    famTB_eq b W R N M D c0 odd dd dr dw l hl hdw fun sd h => ?_]
  obtain ⟨⟨o1, o2, o3, o4, o5⟩, k1, k2⟩ := hsl sd h
  obtain ⟨d1, d2, d3⟩ := hdl sd h
  refine ⟨d1, o5, d3, o2, k1, k2, o3, o4, le_trans ?_ d2⟩
  calc c0 * 2 ^ (sd.Fj - 1) ≤ 2 * (c0 * 2 ^ (sd.Fj - 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    _ = 2 * c0 * 2 ^ (sd.Fj - 1) := by ring

/-- **Families with the same coefficient grids on the box are equal.** -/
theorem famPoly_congr (N M D : ℕ) (s c0 a b' s' c0' a' b'' : ℤ) :
    ∀ (k : ℕ) (l l' : List SliceData), l.length = l'.length →
      (∀ t, t < l.length → ∀ i, i ≤ 2 * N → ∀ j, j ≤ 2 * M →
        sliceG N M s c0 a b' (l.getD t SliceData.zero) i j =
          sliceG N M s' c0' a' b'' (l'.getD t SliceData.zero) i j) →
      famPoly N M D s c0 a b' k l = famPoly N M D s' c0' a' b'' k l'
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | k, sd :: rest, sd' :: rest', hlen, h => by
    simp only [List.length_cons, add_left_inj] at hlen
    rw [famPoly, famPoly, famPoly_congr N M D s c0 a b' s' c0' a' b'' (k + 1) rest rest' hlen
      fun t ht i hi j hj => by
        have := h (t + 1) (by simp; omega) i hi j hj
        simpa using this]
    have hg : gridPolyNM N M (sliceG N M s c0 a b' sd) =
        gridPolyNM N M (sliceG N M s' c0' a' b'' sd') :=
      gridPolyNM_congr fun i j hi hj => by simpa using h 0 (by simp) i hi j hj
    rw [hg]

/-- The zero family has every degree box. -/
theorem inBox3_zero (a J K : ℕ) : InBox3 (0 : P3) a J K :=
  ⟨by simp, fun j => by simp only [Polynomial.coeff_zero]; exact ⟨by simp, fun _ => by simp⟩⟩

/-- The centre of a family with one stored coefficient. -/
theorem famCtr_single (S N M p : ℕ) (s c0 a b' : ℤ) (c : ℂ) (sd : SliceData) :
    famCtr S N M p s c0 a b' c 0 [sd] =
      ctr S N M (1, 0, p) (gridPolyNM N M (sliceG N M s c0 a b' sd)) := by
  simp [famCtr]

/-- **Kronecker images determine bounded polynomials**: two families in a box whose flattenings
have the same Kronecker image (with total `ℓ¹` norm below `2^{b−1}`) are equal. -/
theorem eq_of_kron_flat {P Q : P3} {a J K b W R d : ℕ} (hb : 1 ≤ b) (hP : InBox3 P a J K)
    (hQ : InBox3 Q a J K) (ha : a < W) (hJ : J < R) (hS : W * (J + R * K + 1) ≤ 2 ^ d)
    (hl : l1 (flat R P) + l1 (flat R Q) < 2 ^ (b - 1))
    (h : kron b W (flat R P) = kron b W (flat R Q)) : P = Q := by
  have hG : InBox (flat R P - flat R Q) a (J + R * K) := (inBox_flat hP).sub (inBox_flat hQ)
  have hGl : l1 (flat R P - flat R Q) < 2 ^ (b - 1) := (l1_sub_le _ _).trans_lt hl
  have hk : kron b W (flat R P - flat R Q) = kron b W 0 := by rw [map_sub, h, sub_self, map_zero]
  have h0 : l1 (flat R P - flat R Q) = 0 := by
    rw [l1_eq_l1Kron hb hG ha hS hGl, hk,
      ← l1_eq_l1Kron hb (P := (0 : P2)) ⟨by simp, fun j => by simp⟩ ha hS (by simp [l1, liftN])]
    simp [l1, liftN]
  have hz : flat R P = flat R Q := by
    rw [← sub_eq_zero]
    refine Polynomial.ext fun j => Polynomial.ext fun i => ?_
    have := natAbs_coeff_le_l1 (flat R P - flat R Q) i j
    rw [h0] at this
    simpa using this
  refine Polynomial.ext fun k => Polynomial.ext fun j => ?_
  by_cases hj : j < R
  · have e1 := coeff_flat hP hJ j k hj
    have e2 := coeff_flat hQ hJ j k hj
    rw [← e1, ← e2, hz]
  · have h1 : (P.coeff k).natDegree ≤ J := (hP.2 k).1
    have h2 : (Q.coeff k).natDegree ≤ J := (hQ.2 k).1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-! ## Averages of family centres -/

/-- The average of a grid centre (weight `(1, 0, 0)`) is its centre entry over `2^S`. -/
theorem avg_ctr_grid (S N M : ℕ) (g : ℕ → ℕ → ℤ) :
    avg (ctr S N M (1, 0, 0) (gridPolyNM N M g)) = ((2 : ℂ) ^ S)⁻¹ * (g N M : ℂ) := by
  unfold avg
  rw [coeff_ctr_grid]
  simp

/-- The average of a family centre (weight `(1, 0, 0)`), one coefficient at a time. -/
theorem avg_famCtr_cons (S N M : ℕ) (s c0 : ℤ) (c : ℂ) (k : ℕ) (sd : SliceData)
    (l : List SliceData) :
    avg (famCtr S N M 0 s c0 0 0 c k (sd :: l)) =
      (c ^ k + if k = 0 then 0 else (c ^ k)⁻¹) *
          (((2 : ℂ) ^ S)⁻¹ * (sliceG N M s c0 0 0 sd N M : ℂ)) +
        avg (famCtr S N M 0 s c0 0 0 c (k + 1) l) := by
  rw [famCtr, avg_add, ← Algebra.smul_def, avg_smul, avg_ctr_grid]

/-- The sum of the absolute centre entries of stored coefficients. -/
def avgB (N M : ℕ) (s c0 : ℤ) : List SliceData → ℕ
  | [] => 0
  | sd :: l => (sliceG N M s c0 0 0 sd N M).natAbs + avgB N M s c0 l

/-- **The averages of the higher Chebyshev coefficients** are bounded by their centre entries
(`|c^k + c^{−k}| ≤ 2` on the unit circle). -/
theorem norm_avg_famCtr_le (S N M : ℕ) (s c0 : ℤ) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ (k : ℕ) (l : List SliceData), 1 ≤ k →
      ‖avg (famCtr S N M 0 s c0 0 0 c k l)‖ ≤ 2 * (avgB N M s c0 l : ℝ) / 2 ^ S
  | _, [], _ => by simp [famCtr, avgB, avg]
  | k, sd :: l, hk => by
    rw [avg_famCtr_cons, ite_eq_right (by omega : ¬ k = 0)]
    have ih := norm_avg_famCtr_le S N M s c0 hc (k + 1) l (by omega)
    have hck : ‖c ^ k + (c ^ k)⁻¹‖ ≤ 2 := by
      calc _ ≤ ‖c ^ k‖ + ‖(c ^ k)⁻¹‖ := norm_add_le _ _
        _ = 2 := by rw [norm_inv, norm_pow, hc]; norm_num
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat, Complex.norm_intCast]
    simp only [avgB, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]
    have h2 : (0 : ℝ) < 2 ^ S := by positivity
    have e : (2 : ℝ) * (|(sliceG N M s c0 0 0 sd N M : ℝ)| + (avgB N M s c0 l : ℝ)) / 2 ^ S =
        2 * ((2 ^ S)⁻¹ * |(sliceG N M s c0 0 0 sd N M : ℝ)|) +
          2 * (avgB N M s c0 l : ℝ) / 2 ^ S := by
      field_simp
    rw [e]
    gcongr

/-! ## The parameter polynomial -/

/-- **The parameter polynomial** `2^{S+6} uᴺ vᴹ w^D + 2^{S−1} uᴺ vᴹ (w^{D+1} + w^{D−1})`. -/
def Pr3 (S N M D : ℕ) : P3 :=
  C (Tpoly (S + 6) N M) * X ^ D + C (Tpoly (S - 1) N M) * (X ^ (D + 1) + X ^ (D - 1))

/-- The centre of `2^{S'} uᴺ vᴹ` at scale `2^S` is `2^{S'}/2^S`. -/
theorem ctr_Tpoly' (S S' N M : ℕ) :
    ctr S N M (1, 0, 0) (Tpoly S' N M) = algebraMap ℂ FA ((2 : ℂ) ^ S' / 2 ^ S) := by
  rw [ctr, phiK_Tpoly, Tc, smul_mul_assoc, mode_mul, smul_smul]
  simp only [scal, ofsW, one_mul, add_zero, pow_zero, mul_one, add_neg_cancel]
  rw [mode_zero, Algebra.algebraMap_eq_smul_one, div_eq_mul_inv, mul_comm]

/-- **The family centre of the parameter polynomial** is `64 + (c + c⁻¹)/2`. -/
theorem ctr3_Pr3 (S N M D : ℕ) (hS : 1 ≤ S) (hD : 1 ≤ D) {c : ℂ} (hc : c ≠ 0) :
    ctr3 S N M D c (1, 0, 0) (Pr3 S N M D) = algebraMap ℂ FA (64 + (c + c⁻¹) / 2) := by
  have e : ∀ n P, ctr3 S N M D c (1, 0, 0) (C P * X ^ n) =
      algebraMap ℂ FA (c ^ n * (c ^ (D * 1))⁻¹) * ctr S N M (1, 0, 0) P := fun n P => by
    rw [mul_comm]; exact ctr3_X_pow_C S N M D c (1, 0, 0) n P
  rw [Pr3, ctr3_add, mul_add, ctr3_add, e, e, e, ctr_Tpoly', ctr_Tpoly', ← map_mul, ← map_mul,
    ← map_mul, ← map_add, ← map_add]
  congr 1
  have h1 : c ^ (D + 1) * (c ^ (D * 1))⁻¹ = c := by
    rw [mul_one, pow_succ]; field_simp
  have h2 : c ^ (D - 1) * (c ^ (D * 1))⁻¹ = c⁻¹ := by
    have : c ^ D = c ^ (D - 1) * c := by rw [← pow_succ]; congr 1; omega
    rw [mul_one, this]; field_simp
  have h3 : c ^ D * (c ^ (D * 1))⁻¹ = 1 := by rw [mul_one]; field_simp
  rw [h1, h2, h3]
  have h4 : (2 : ℂ) ^ (S + 6) / 2 ^ S = 64 := by rw [pow_add]; field_simp; norm_num
  have h5 : (2 : ℂ) ^ (S - 1) / 2 ^ S = 1 / 2 := by
    have : (2 : ℂ) ^ S = 2 ^ (S - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    rw [this]; field_simp
  rw [h4, h5]; ring

/-- The Kronecker image of `2^{S'} uᴺ vᴹ wⁿ`. -/
theorem kron_flat_TX (S' N M n b W R : ℕ) :
    kron b W (flat R (C (Tpoly S' N M) * X ^ n)) =
      ((1 <<< S' : ℕ) : ℤ) * ((1 <<< (b * (N + W * (M + R * n))) : ℕ) : ℤ) := by
  rw [map_mul, map_mul, flat_C, kron_Tpoly, kron_flat_X_pow]
  simp only [Nat.shiftLeft_eq, one_mul]
  push_cast
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

/-- **The Kronecker image of the parameter polynomial.** -/
theorem kron_flat_Pr3 (S N M D b W R : ℕ) :
    kron b W (flat R (Pr3 S N M D)) =
      ((1 <<< (S + 6) : ℕ) : ℤ) * ((1 <<< (b * (N + W * (M + R * D))) : ℕ) : ℤ) +
        ((1 <<< (S - 1) : ℕ) : ℤ) * (((1 <<< (b * (N + W * (M + R * (D + 1)))) : ℕ) : ℤ) +
          ((1 <<< (b * (N + W * (M + R * (D - 1)))) : ℕ) : ℤ)) := by
  rw [Pr3, map_add, map_add, mul_add, map_add, map_add, kron_flat_TX, kron_flat_TX, kron_flat_TX]
  ring

/-- The degree box of the parameter polynomial. -/
theorem inBox3_Pr3 (S N M D : ℕ) : InBox3 (Pr3 S N M D) N M (D + 1) := by
  have hT : ∀ S' n, n ≤ D + 1 → InBox3 (C (Tpoly S' N M) * X ^ n) N M (D + 1) := fun S' n hn => by
    have h := (InBox3.C (InBox.monomial N M ((2 : ℤ) ^ S'))).mul (InBox3.X_pow n)
    simp only [add_zero, zero_add] at h
    exact (by simpa [Tpoly] using h : InBox3 (C (Tpoly S' N M) * X ^ n) N M n).mono le_rfl le_rfl hn
  rw [Pr3, mul_add]
  exact (hT _ _ (by omega)).add ((hT _ _ le_rfl).add (hT _ _ (by omega)))

/-- The `ℓ¹` bound of the flattened parameter polynomial. -/
theorem l1_flat_Pr3 (S N M D R : ℕ) :
    l1 (flat R (Pr3 S N M D)) ≤ 2 ^ (S + 6) + 2 * 2 ^ (S - 1) := by
  have hT : ∀ S' n, l1 (flat R (C (Tpoly S' N M) * X ^ n)) ≤ 2 ^ S' := fun S' n => by
    rw [map_mul, flat_C]
    refine (l1_mul_le _ _).trans ?_
    have h1 : l1 (flat R ((X : P3) ^ n)) = 1 := by
      have : flat R ((X : P3) ^ n) = monomial (R * n) (monomial 0 1) := by
        simp [flat, pow_mul, ← C_mul_X_pow_eq_monomial]
      rw [this, l1_monomial]; rfl
    rw [h1, mul_one]
    exact l1_Tpoly S' N M
  rw [Pr3, mul_add, map_add, map_add]
  refine (l1_add_le _ _).trans (add_le_add (hT _ _) ((l1_add_le _ _).trans ?_))
  have := add_le_add (hT (S - 1) (D + 1)) (hT (S - 1) (D - 1))
  omega

/-! ## Renaming and congruence of trees -/

/-- Renaming the variables of a light tree. -/
def ExN.rename (f : ℕ → ℕ) : ExN → ExN
  | .var i => .var (f i)
  | .cst k => .cst k
  | .add e g => .add (ExN.rename f e) (ExN.rename f g)
  | .sub e g => .sub (ExN.rename f e) (ExN.rename f g)
  | .mul e g => .mul (ExN.rename f e) (ExN.rename f g)

/-- All variables of a tree satisfy `p`. -/
def Ex.allV (p : ℕ → Bool) : Ex → Bool
  | .var i => p i
  | .cst _ => true
  | .add e g => Ex.allV p e && Ex.allV p g
  | .sub e g => Ex.allV p e && Ex.allV p g
  | .mul e g => Ex.allV p e && Ex.allV p g

/-- Evaluation of a renamed tree. -/
theorem eval_toEx_rename {α : Type*} [CommRing α] (X : ℕ → α) (f : ℕ → ℕ) :
    ∀ e : ExN, Ex.eval X (toEx (e.rename f)) = Ex.eval (fun i => X (f i)) (toEx e)
  | .var _ => rfl
  | .cst _ => rfl
  | .add e g => by
    simp only [ExN.rename, toEx, Ex.eval, eval_toEx_rename X f e, eval_toEx_rename X f g]
  | .sub e g => by
    simp only [ExN.rename, toEx, Ex.eval, eval_toEx_rename X f e, eval_toEx_rename X f g]
  | .mul e g => by
    simp only [ExN.rename, toEx, Ex.eval, eval_toEx_rename X f e, eval_toEx_rename X f g]

/-- Evaluations agree if the values agree on the variables of the tree. -/
theorem eval_congr_allV {α : Type*} [CommRing α] {X Y : ℕ → α} {p : ℕ → Bool}
    (hp : ∀ i, p i = true → X i = Y i) : ∀ e : Ex, Ex.allV p e = true → Ex.eval X e = Ex.eval Y e
  | .var i, h => hp i h
  | .cst _, _ => rfl
  | .add e g, h => by
    simp only [Ex.allV, Bool.and_eq_true] at h
    simp only [Ex.eval, eval_congr_allV hp e h.1, eval_congr_allV hp g h.2]
  | .sub e g, h => by
    simp only [Ex.allV, Bool.and_eq_true] at h
    simp only [Ex.eval, eval_congr_allV hp e h.1, eval_congr_allV hp g h.2]
  | .mul e g, h => by
    simp only [Ex.allV, Bool.and_eq_true] at h
    simp only [Ex.eval, eval_congr_allV hp e h.1, eval_congr_allV hp g h.2]

/-- **A node identity transferred by congruence** of the values on the variables of the tree. -/
theorem rel_congr {X Y : ℕ → FA} {p : ℕ → Bool} (hp : ∀ i, p i = true → X i = Y i) {e : Ex}
    (hv : Ex.allV p e = true) {n : ℕ} {c' : ℂ} (hn : X n = Y n) (h : c' • Y n = Ex.eval Y e) :
    c' • X n = Ex.eval X e := by
  rw [hn, h, eval_congr_allV hp e hv]

/-- **A node identity transferred by renaming**: if the values `XH` at the renamed variables are
the values `XL`, the identity of a tree gives the identity of the renamed tree. -/
theorem rel_rename {XH XL : ℕ → FA} {f : ℕ → ℕ} {p : ℕ → Bool}
    (hp : ∀ i, p i = true → XH (f i) = XL i) {eL eH : ExN} (hre : eL.rename f = eH)
    (hv : Ex.allV p (toEx eL) = true) {n m : ℕ} {c' : ℂ} (hn : XH n = XL m)
    (h : c' • XL m = Ex.eval XL (toEx eL)) : c' • XH n = Ex.eval XH (toEx eH) := by
  rw [← hre, eval_toEx_rename, hn, h]
  exact (eval_congr_allV (X := fun i => XH (f i)) hp _ hv).symm

end PlasmaLean.Certificates.KronBallCheb
