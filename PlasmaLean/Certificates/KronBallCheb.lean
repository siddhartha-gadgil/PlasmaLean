/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallGrid

/-!
# Ball arithmetic for families: Chebyshev series in a parameter with ball coefficients

Validated numerics for **one-parameter families** of elements of the strip algebra `𝔸 = FA`
(`Certificates/KronBall`), used to certify a whole interval of the guiding-centre parameter
`ρ = ρ_c + h cos ϑ` at once (`Design/RationalStellaratorGCFam*`).

A family is a **Chebyshev series** `x(ϑ) = ∑_{|k| ≤ D} a_k e^{ikϑ}` with `a_{−k} = a_k`, i.e.
`∑_k a_k T_k(cos ϑ)` up to the normalisation of `a_0`; each coefficient `a_k` is a trigonometric
polynomial in `(θ, ψ)`. Such a family is stored as a polynomial in three variables
`P ∈ ℤ[u][v][w]` (`P3`), `w` standing for `e^{iϑ}`:

* `phiW c : P3 →+* 𝔸` evaluates `u ↦ e^{iθ}`, `v ↦ e^{iψ}`, `w ↦ c` (for `c = e^{iϑ}`, the
  **evaluation at the parameter value** `ϑ`, a ring homomorphism);
* with `T₃ = 2^S uᴺ vᴹ wᴰ` (`T3`), a polynomial of weight `(d, e, p)` represents the centre
  `ctr3 c w P` with `phiW c P = λ₃(w) · ctr3 c w P` (`phiW_eq_lam_ctr3`), exactly as
  `Certificates/KronBall` does for one parameter value;
* **contraction**: `ctr3 c w P = ∑_k c^{k − D d} ctr w P_k` (`ctr3_eq_sum`), so for `|c| = 1`
  the strip norm of the family at *every* parameter value is at most the sum of the strip norms of
  the coefficients (`Bd_ctr3_of_slices`);
* **the node identity** `node_eq3` and the ball steps `node_step3`, `norm_step3`: one exact
  polynomial computation in `ℤ[u][v][w]` and one norm bound certify a rounding step of a ball chain
  for all parameter values simultaneously. Products of families are handled exactly by the
  polynomial product in `w` (the Chebyshev product rule `T_i T_j = (T_{i+j} + T_{|i−j|})/2` is
  the Laurent product), and truncation of the Chebyshev degree is part of the rounding.

**Sanity.** `phiW_C`: a polynomial constant in `w` evaluates as in `Certificates/KronBall`;
`ctr3_C`: a family constant in `ϑ` is the one-parameter centre.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBallCheb

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Theory.KAM WEll1Z2 Complex

/-- Integer polynomials in three variables `ℤ[u][v][w]` (`w` outermost). -/
abbrev P3 : Type := Polynomial P2

/-- **Evaluation at a parameter value**: `u ↦ e^{iθ}`, `v ↦ e^{iψ}`, `w ↦ c`. -/
def phiW (c : ℂ) : P3 →+* FA := eval₂RingHom phiK (algebraMap ℂ FA c)

/-- **Sanity**: polynomials constant in `w` evaluate by `phiK`. -/
theorem phiW_C (c : ℂ) (P : P2) : phiW c (C P) = phiK P := by
  simp [phiW]

/-- `phiW` of `w`. -/
theorem phiW_X (c : ℂ) : phiW c (X : P3) = algebraMap ℂ FA c := by
  simp [phiW]

/-- `T₃ = 2^S uᴺ vᴹ wᴰ`. -/
def T3 (S N M D : ℕ) : P3 := C (Tpoly S N M) * X ^ D

/-- `V = 2v` as a three-variable polynomial. -/
def V3 : P3 := C Vpoly

/-- The value `c^D T` of `T₃`. -/
def Tc3 (S N M D : ℕ) (c : ℂ) : FA := algebraMap ℂ FA (c ^ D) * Tc S N M

/-- `phiW T₃ = c^D T`. -/
theorem phiW_T3 (S N M D : ℕ) (c : ℂ) : phiW c (T3 S N M D) = Tc3 S N M D c := by
  rw [T3, map_mul, phiW_C, phiK_Tpoly, map_pow, phiW_X, Tc3, map_pow, mul_comm]

/-- `phiW V = V`. -/
theorem phiW_V3 (c : ℂ) : phiW c V3 = Vc := by rw [V3, phiW_C, phiK_Vpoly]

/-- `λ₃(w) = (c^D T)^d V^e i^p`. -/
def lam3 (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) : FA := lamG (Tc3 S N M D c) Vc w

/-- `λ₃(w) = c^{Dd} λ(w)`. -/
theorem lam3_eq (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) :
    lam3 S N M D c w = algebraMap ℂ FA (c ^ (D * w.1)) * lamF S N M w := by
  obtain ⟨d, e, p⟩ := w
  simp only [lam3, lamG, Tc3, lamF, mul_pow, ← map_pow, ← pow_mul]
  ring

/-- **The centre of a family** at the parameter value `w = c`, for a polynomial of weight `w`. -/
def ctr3 (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) (P : P3) : FA :=
  algebraMap ℂ FA ((c ^ (D * w.1))⁻¹) * ((scal S w)⁻¹ • (phiW c P * mode 0 (-ofsW N M w)))

/-- `phiW P = λ₃(w) · ctr3 w P` (for `c ≠ 0`). -/
theorem phiW_eq_lam_ctr3 (S N M D : ℕ) {c : ℂ} (hc : c ≠ 0) (w : ℕ × ℕ × ℕ) (P : P3) :
    phiW c P = lam3 S N M D c w * ctr3 S N M D c w P := by
  rw [lam3_eq, lamF_eq, ctr3]
  have h1 : algebraMap ℂ FA (c ^ (D * w.1)) * algebraMap ℂ FA ((c ^ (D * w.1))⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hc), map_one]
  calc phiW c P = (algebraMap ℂ FA (c ^ (D * w.1)) * algebraMap ℂ FA ((c ^ (D * w.1))⁻¹)) *
        ((scal S w • mode 0 (ofsW N M w)) *
          ((scal S w)⁻¹ • (phiW c P * mode 0 (-ofsW N M w)))) := by
          rw [h1, one_mul, smul_mul_smul_comm, mul_inv_cancel₀ (scal_ne_zero S w), one_smul,
            mul_left_comm, mode_mul, add_neg_cancel, mode_zero, mul_one]
    _ = _ := by ring

/-- `λ₃(w)` is a unit (for `c ≠ 0`). -/
theorem lam3_isUnit (S N M D : ℕ) {c : ℂ} (hc : c ≠ 0) (w : ℕ × ℕ × ℕ) :
    IsUnit (lam3 S N M D c w) := by
  rw [lam3_eq]
  refine IsUnit.mul ?_ (lamF_isUnit S N M w)
  refine ⟨⟨algebraMap ℂ FA (c ^ (D * w.1)), algebraMap ℂ FA ((c ^ (D * w.1))⁻¹), ?_, ?_⟩, rfl⟩
  · rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hc), map_one]
  · rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), map_one]

/-- `λ₃` of a sum of weights (same phase). -/
theorem lam3_add (S N M D : ℕ) (c : ℂ) (d e p d' e' : ℕ) :
    lam3 S N M D c (d + d', e + e', p) =
      Tc3 S N M D c ^ d' * Vc ^ e' * lam3 S N M D c (d, e, p) := by
  simp only [lam3, lamG, pow_add]; ring

/-! ## Contraction: the norm of a family at every parameter value -/

/-- `phiW P = ∑_k c^k phiK P_k`. -/
theorem phiW_eq_sum (c : ℂ) (P : P3) :
    phiW c P = ∑ k ∈ range (P.natDegree + 1), algebraMap ℂ FA (c ^ k) * phiK (P.coeff k) := by
  rw [phiW, coe_eval₂RingHom, eval₂_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [map_pow, mul_comm]

/-- **The centre of a family is a combination of the centres of its coefficients**:
`ctr3 c w P = ∑_k c^{k} c^{−Dd} ctr w P_k`. -/
theorem ctr3_eq_sum (S N M D : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) (P : P3) :
    ctr3 S N M D c w P = ∑ k ∈ range (P.natDegree + 1),
      algebraMap ℂ FA (c ^ k * (c ^ (D * w.1))⁻¹) * ctr S N M w (P.coeff k) := by
  rw [ctr3, phiW_eq_sum, sum_mul, smul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [ctr, mul_assoc, mul_smul_comm, ← mul_assoc, ← mul_assoc, ← map_mul, mul_comm (c ^ k),
    mul_assoc, mul_smul_comm]

/-- **Sanity**: a family constant in `w` is the one-parameter centre. -/
theorem ctr3_C (S N M : ℕ) (c : ℂ) (w : ℕ × ℕ × ℕ) (P : P2) :
    ctr3 S N M 0 c w (C P) = ctr S N M w P := by
  rw [ctr3_eq_sum]
  simp [natDegree_C]

/-- A finite sum of balls. -/
theorem Bd_sum {r : ℝ} {ι : Type*} (s : Finset ι) (x : ι → FA) (B : ι → ℝ)
    (h : ∀ i ∈ s, Bd r (x i) (B i)) : Bd r (∑ i ∈ s, x i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bd_zero r
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- **Contraction**: for `|c| = 1` (a real parameter value), the strip norm of the family is at
most the sum of the strip norms of its Chebyshev coefficients. -/
theorem Bd_ctr3_of_slices {r : ℝ} (S N M D : ℕ) {c : ℂ} (hc : ‖c‖ = 1) (w : ℕ × ℕ × ℕ)
    (P : P3) (K : ℕ) (hK : P.natDegree ≤ K) (B : ℕ → ℝ)
    (hB : ∀ k, k ≤ K → Bd r (ctr S N M w (P.coeff k)) (B k)) :
    Bd r (ctr3 S N M D c w P) (∑ k ∈ range (K + 1), B k) := by
  have h1 : ctr3 S N M D c w P = ∑ k ∈ range (K + 1),
      algebraMap ℂ FA (c ^ k * (c ^ (D * w.1))⁻¹) * ctr S N M w (P.coeff k) := by
    rw [ctr3_eq_sum]
    refine sum_subset (range_subset_range.2 (by omega)) fun k _ hk => ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simp at hk; omega)]
    simp [ctr]
  rw [h1]
  refine Bd_sum _ _ _ fun k hk => ?_
  have hn : ‖c ^ k * (c ^ (D * w.1))⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, norm_pow, norm_pow, hc, one_pow, one_pow, inv_one, one_mul]
  have := (hB k (by simp at hk; omega)).smul (c ^ k * (c ^ (D * w.1))⁻¹)
  rw [hn, one_mul] at this
  rwa [Algebra.smul_def] at this

/-! ## The node identity for families -/

/-- **The truncation identity for families.** If every variable polynomial `P i` represents the
family centre `x i` (weight `W i`) at `w = c ≠ 0`, the tree `e` has weight
`(dq + dd, eq + de, p)` and `Q` has weight `(dq, eq, p)`, then
`eval x e − c' · ctr3 (dq, eq, p) Q = ctr3 (dq + dd, eq + de, p) G` with
`G = evH e − c' T₃^{dd} V^{de} Q`. -/
theorem node_eq3 {S N M D : ℕ} {c : ℂ} (hc : c ≠ 0) {W : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (W i).2.2 < 4)
    {P : ℕ → P3} {x : ℕ → FA} (hx : ∀ i, x i = ctr3 S N M D c (W i) (P i)) {e : Ex}
    {dq eq p dd de : ℕ} (hwt : Ex.wt W e = some (dq + dd, eq + de, p)) (Q : P3) (c' : ℤ) :
    Ex.eval x e - (c' : ℂ) • ctr3 S N M D c (dq, eq, p) Q =
      ctr3 S N M D c (dq + dd, eq + de, p)
        (Ex.evH W P e - C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * Q) := by
  have hxh : ∀ i, phiW c (P i) = lamG (Tc3 S N M D c) Vc (W i) * x i := fun i => by
    rw [hx i]; exact phiW_eq_lam_ctr3 S N M D hc (W i) (P i)
  have hev := evH_phaseF hW (Tc3 S N M D c) Vc hxh e _ hwt
  rw [← Ex.evH_map (phiW c) W P e] at hev
  have hQ := phiW_eq_lam_ctr3 S N M D hc (dq, eq, p) Q
  have hG := phiW_eq_lam_ctr3 S N M D hc (dq + dd, eq + de, p)
    (Ex.evH W P e - C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * Q)
  have key : phiW c (Ex.evH W P e - C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * Q) =
      lam3 S N M D c (dq + dd, eq + de, p) *
        (Ex.eval x e - (c' : ℂ) • ctr3 S N M D c (dq, eq, p) Q) := by
    rw [map_sub (phiW c)]
    simp only [map_mul, map_pow, phiW_T3, phiW_V3, map_intCast]
    rw [hQ, hev, show lamG (Tc3 S N M D c) Vc (dq + dd, eq + de, p) =
      lam3 S N M D c (dq + dd, eq + de, p) from rfl, lam3_add, Algebra.smul_def, map_intCast]
    ring
  rw [hG] at key
  obtain ⟨u, hu⟩ := lam3_isUnit S N M D hc (dq + dd, eq + de, p)
  rw [← hu] at key
  exact (u.isUnit.mul_left_cancel key).symm

/-- **A rounding step of a family ball chain**: the new centre `x n` (weight `(1, 0, p)`) of the
value `X n` with `c' · X n = eval X e`, from the balls of the variables of `e` and the norm `β` of
the truncation polynomial. -/
theorem node_step3 {r : ℝ} (hr : 0 ≤ r) {S N M D : ℕ} {c : ℂ} (hc : c ≠ 0)
    {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3} {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i)) {e : Ex}
    (hv : below n e = true) {dd de p : ℕ} (hwt : Ex.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) {c' : ℤ} (hc0 : c' ≠ 0) (hrel : (c' : ℂ) • X n = Ex.eval X e)
    {β : ℚ}
    (hG : Bd r (ctr3 S N M D c (1 + dd, 0 + de, p)
      (Ex.evH Wt P e - C (c' : P2) * (T3 S N M D ^ dd * V3 ^ de) * P n)) β)
    (hfin : Ex.dmajQ B E e + β ≤ |c'| * E n) : Bd r (X n - x n) (E n) := by
  have h1 := (Bd_eval_sub_below hr hB hE e hv).2
  have h2 := node_eq3 hc hW hx hwt (P n) c'
  rw [← hWn, ← hx n] at h2
  have h3 := h1.add hG
  rw [← h2, show Ex.eval X e - Ex.eval x e + (Ex.eval x e - (c' : ℂ) • x n) =
    (c' : ℂ) • (X n - x n) by rw [smul_sub, hrel]; ring] at h3
  have h4 := h3.smul ((c' : ℂ)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc0), one_smul] at h4
  refine h4.le ?_
  have hcp : (0 : ℝ) < |(c' : ℝ)| := abs_pos.2 (by exact_mod_cast hc0)
  rw [norm_inv, Complex.norm_intCast, inv_mul_le_iff₀ hcp]
  have := (Rat.cast_le (K := ℝ)).2 hfin
  push_cast at this
  linarith

/-- **A norm step of a family ball chain** (no new centre): `‖eval X e‖ ≤ dmajQ + β`. -/
theorem norm_step3 {r : ℝ} (hr : 0 ≤ r) {S N M D : ℕ} {c : ℂ} (hc : c ≠ 0)
    {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P3} {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr3 S N M D c (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i)) {e : Ex}
    (hv : below n e = true) {w : ℕ × ℕ × ℕ} (hwt : Ex.wt Wt e = some w) {β : ℚ}
    (hG : Bd r (ctr3 S N M D c w (Ex.evH Wt P e)) β) :
    Bd r (Ex.eval X e) ((Ex.dmajQ B E e + β : ℚ) : ℝ) := by
  have h1 := (Bd_eval_sub_below hr hB hE e hv).2
  obtain ⟨d, e', p⟩ := w
  have h2 := node_eq3 (dq := d) (eq := e') (dd := 0) (de := 0) hc hW hx (by simpa using hwt) 0 0
  have e0 : Ex.evH Wt P e - C ((0 : ℤ) : P2) * (T3 S N M D ^ 0 * V3 ^ 0) * 0 = Ex.evH Wt P e := by
    ring
  simp only [add_zero] at h2
  rw [e0, Int.cast_zero, zero_smul, sub_zero] at h2
  have h3 := h1.add hG
  rw [← h2, sub_add_cancel] at h3
  simpa using h3

end PlasmaLean.Certificates.KronBallCheb
