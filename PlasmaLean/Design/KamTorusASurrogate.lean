/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusASurrogateCheck
public import PlasmaLean.Design.KamTorusATwist
public import PlasmaLean.Design.KamTorusAStrip

/-!
# A low-degree surrogate of torus A in the strip algebra (KAM route, final stage)

Sharp strip bounds (`r_A = 0.1257`) for rational functions of torus A that the crude
Banach-algebra estimates of `Theory/KAM/StripAlgebra` cannot give. They are computed on a
**surrogate torus** `K_S = (1 + u_S, z_S)` (the modes `0 ≤ k ≤ 7`, `|m| ≤ 5` of torus A rounded to
`2^{-32}`, `Design/KamTorusAFrameData`) with a trigonometric polynomial `q_S ≈ 1/(D³ W₀²)`
(modes `|k| ≤ 14`, `|m| ≤ 10`, `Design/KamTorusASurrogateData`).

**Results** (`torusA_surrogate`):
* `isReal_uS`, `isReal_zS`, `isReal_qS`, `ana_uS`, `ana_zS`, `ana_qS`;
* distance to torus A (`Design/KamTorusAStrip`): `Bd_du`, `Bd_dz` (`≤ 2.2 × 10⁻⁷`), `Bd_da`,
  `Bd_db` (`∂_θ`, `≤ 7.7 × 10⁻⁷`);
* the winding form: `Bd_W0S`, `‖W₀(K_S) − w_S‖ ≤ 0.004078`, `w_S = c0W/σ₁² ≈ −0.018135`
  (`wS_bounds`);
* the inverse: `Bd_X4`, `‖q_S D³ W₀² − 1‖ ≤ 5.13 × 10⁻⁶`, and `Bd_qS`, `‖q_S‖ ≤ 16162`;
* the torsion `T = R³ P q`: `Bd_X5`, `‖T‖ ≤ 19.655`, with exact average
  `⟨T⟩ = c0T / (512 σ₁^{16}) ≈ 0.398640` (`avg_X5`), so `avg_X5_re : 0.3986 ≤ Re ⟨T⟩` and
  `avg_X5_im : Im ⟨T⟩ = 0`.

**Method.** Every quantity is the value on the unit torus of an integer polynomial in `ℤ[u][v]`.
The surrogate variables are represented with weights and phases as in `Design/KamTorusATwist`
(`evalC_bP`, the phase bridge `Ex.evH_phase`); `8 D`, `128 P` and `W₀` are expression trees
(`Design/KamTorusASurrogateData`) whose real values are the polynomials `Dp`, `Pp` of
`Design/KamNewtonField` (`Dp_tree`, `Pp_tree`). An element `X ∈ 𝔸` whose function is read off
a polynomial `P` (`P(e^{iθ}, e^{iψ}) = c X(θ, ψ) e^{i(i₀θ + j₀ψ)}`) has the Fourier coefficients
`c⁻¹ coefZ2 P i₀ j₀` by uniqueness of Fourier coefficients (`eq_ofP`, via `ext_eval`), so its
strip norm is the separable weighted digit sum of the Kronecker image (`Bd_of_evalC`,
`wnorm_of_check`, kernel checks of `Design/KamTorusASurrogateCheck`). The exact centre
coefficient is one balanced digit of the Kronecker image (`slot_eq_of_digit`).

**Sanity.** `eval_uS`, `eval_zS`: the elements are the surrogate functions of
`Design/KamTorusATwist`; `digit_fixture` (accepted), `digit_reject_fixture` (without the digit
bound the extraction misreads), `coefZ2_gridPolyG_out` (degenerate: outside the box the
coefficients vanish).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open Finset PlasmaLean.Theory.KAM PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Design.KamTorusA WEll1Z2 Complex
open PlasmaLean.Design.KamTorusA.Frame (n1 m1 sig1 gridPoly1 gRc gZc gAc gBc tP1 vP2 T1 V1 w1 rS aS
  bS)

/-! ## Generic: elements of `𝔸` read off integer polynomials -/

/-- `v = e^{iψ}` at `φ = phiOf ψ`. -/
theorem vv_phiOf (ψ : ℝ) : vv (phiOf ψ) = Complex.exp (ψ * Complex.I) := by
  rw [vv, psi_phiOf]

/-- Scaled coefficients of a polynomial in a box are in `ℓ¹_{r_A}` (finite support). -/
theorem inW_coefZ2 {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (c : ℂ) :
    InWeighted rA (fun km => c * (coefZ2 P i₀ j₀ km : ℂ)) :=
  inWeighted_smul (summable_coefZ2 hbox ha hS i₀ j₀ (fun km z => ‖z‖ * weight rA km) (by simp)) c

/-- The element of `𝔸` with coefficients `c⁻¹ coefZ2 P i₀ j₀`. -/
def ofP {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W) (hS : W * (J + 1) ≤ S)
    (i₀ j₀ : ℕ) (c : ℂ) : FA :=
  ofA (fun km => c⁻¹ * (coefZ2 P i₀ j₀ km : ℂ)) (inW_coefZ2 hbox ha hS i₀ j₀ c⁻¹)

/-- Coefficients of `ofP`. -/
theorem coeff_ofP {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (c : ℂ) :
    coeff (ofP hbox ha hS i₀ j₀ c) = fun km => c⁻¹ * (coefZ2 P i₀ j₀ km : ℂ) := by
  rw [ofP, coeff_ofA]

/-- `ofP` is analytic. -/
theorem ana_ofP {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) (c : ℂ) : Ana (ofP hbox ha hS i₀ j₀ c) :=
  ana_ofA _

/-- **Reading the function of `ofP`**: if `P(e^{iθ}, e^{iψ}) = c F(θ, ψ) e^{i i₀ θ} e^{i j₀ ψ}`,
then `ofP` is the function `F`. -/
theorem eval_ofP {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {c : ℂ} (hc : c ≠ 0) {F : ℝ → ℝ → ℂ}
    (h : ∀ θ ψ, evalC (uu θ) (vv (phiOf ψ)) P = c * F θ ψ * (uu θ ^ i₀ * vv (phiOf ψ) ^ j₀))
    (θ ψ : ℝ) : eval (ofP hbox ha hS i₀ j₀ c) θ ψ = F θ ψ := by
  rw [ofP, eval_ofA]
  have h1 := h θ ψ
  rw [vv_phiOf] at h1
  exact (eq_fourierSum_of_evalC hbox ha hS i₀ j₀ hc h1).symm

/-- **The polynomial of `ofP`**: `P(e^{iθ}, e^{iψ}) = c · ofP(θ, ψ) · e^{i i₀ θ} e^{i j₀ ψ}`. -/
theorem evalC_ofP {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {c : ℂ} (hc : c ≠ 0) (θ ψ : ℝ) :
    evalC (uu θ) (vv (phiOf ψ)) P =
      c * eval (ofP hbox ha hS i₀ j₀ c) θ ψ * (uu θ ^ i₀ * vv (phiOf ψ) ^ j₀) := by
  rw [ofP, eval_ofA, vv_phiOf, uu, evalC_exp_eq_fourierSum hbox ha hS i₀ j₀ θ ψ]
  simp only [fourierSum, mul_assoc]
  rw [tsum_mul_left]
  field_simp

/-- **Uniqueness**: an element whose function is read off a polynomial is `ofP`. -/
theorem eq_ofP {X : FA} {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ θ ψ, evalC (uu θ) (vv (phiOf ψ)) P = c * eval X θ ψ * (uu θ ^ i₀ * vv (phiOf ψ) ^ j₀)) :
    X = ofP hbox ha hS i₀ j₀ c :=
  ext_eval fun θ ψ => (eval_ofP hbox ha hS i₀ j₀ hc (F := fun θ ψ => eval X θ ψ) h θ ψ).symm

/-- **Strip bound from a polynomial reading** and a weighted bound of its coefficients. -/
theorem Bd_of_evalC {X : FA} {P : P2} {a J W S : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (i₀ j₀ : ℕ) {c : ℂ} (hc : c ≠ 0)
    (h : ∀ θ ψ, evalC (uu θ) (vv (phiOf ψ)) P = c * eval X θ ψ * (uu θ ^ i₀ * vv (phiOf ψ) ^ j₀))
    {B : ℝ} (hB : wnorm rA (fun km => (coefZ2 P i₀ j₀ km : ℂ)) ≤ B) :
    Bd rA X (‖c‖⁻¹ * B) := by
  rw [eq_ofP hbox ha hS i₀ j₀ hc h, ofP]
  refine Bd_ofA _ ?_
  rw [wnorm_smul, norm_inv]
  gcongr

/-- `∂_θ` of `ofP`: if the coefficients of `Q` are `k` times those of `P`, then
`∂_θ (c⁻¹ P) = (−i c)⁻¹ Q`. -/
theorem dTh_ofP {P Q : P2} {a J W S a' J' W' S' : ℕ} (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ S) (hbox' : InBox Q a' J') (ha' : a' < W') (hS' : W' * (J' + 1) ≤ S')
    (i₀ j₀ : ℕ) (c : ℂ) (hk : ∀ km, coefZ2 Q i₀ j₀ km = km.1 * coefZ2 P i₀ j₀ km) :
    dTh (ofP hbox ha hS i₀ j₀ c) = ofP hbox' ha' hS' i₀ j₀ (-Complex.I * c) := by
  refine ext_coeff fun n => ?_
  rw [dTh, (ana_ofP hbox ha hS i₀ j₀ c).coeff_dS, coeff_ofP, coeff_ofP]
  simp only [dsym, hk]
  push_cast
  rw [mul_inv, inv_neg, Complex.inv_I]
  ring

/-! ## Grid polynomials and their coefficients -/

/-- `∑_{i ≤ A, j ≤ B} g i j uⁱ vʲ`. -/
noncomputable def gridPolyG (A B : ℕ) (g : ℕ → ℕ → ℤ) : P2 :=
  ∑ i ∈ range (A + 1), ∑ j ∈ range (B + 1), Polynomial.monomial j (Polynomial.monomial i (g i j))

/-- The compact grid polynomials of `Design/KamTorusAFrame` are grid polynomials. -/
theorem gridPoly1_eq (g : ℕ → ℕ → ℤ) : gridPoly1 g = gridPolyG (2 * n1) (2 * m1) g := rfl

/-- Coefficients of a grid polynomial. -/
theorem coeff_gridPolyG (A B : ℕ) (g : ℕ → ℕ → ℤ) (i j : ℕ) :
    ((gridPolyG A B g).coeff j).coeff i = if i ≤ A ∧ j ≤ B then g i j else 0 := by
  simp only [gridPolyG, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  simp only [apply_ite (fun p : Polynomial ℤ => p.coeff i), Polynomial.coeff_monomial,
    Polynomial.coeff_zero]
  simp [Finset.sum_ite_eq']
  grind

/-- Fourier coefficients of a grid polynomial. -/
theorem coefZ2_gridPolyG (A B : ℕ) (g : ℕ → ℕ → ℤ) (i₀ j₀ : ℕ) (km : ℤ × ℤ) :
    coefZ2 (gridPolyG A B g) i₀ j₀ km =
      if 0 ≤ km.1 + i₀ ∧ 0 ≤ km.2 + j₀ ∧ (km.1 + i₀).toNat ≤ A ∧ (km.2 + j₀).toNat ≤ B then
        g (km.1 + i₀).toNat (km.2 + j₀).toNat else 0 := by
  unfold coefZ2
  rw [coeff_gridPolyG]
  split_ifs <;> grind

/-- The `θ`-weighted grid `(i − i₀) g` has the Fourier coefficients `k ĝ_{km}`. -/
theorem coefZ2_wgrid (A B : ℕ) (g : ℕ → ℕ → ℤ) (i₀ j₀ : ℕ) (km : ℤ × ℤ) :
    coefZ2 (gridPolyG A B (fun i j => ((i : ℤ) - i₀) * g i j)) i₀ j₀ km =
      km.1 * coefZ2 (gridPolyG A B g) i₀ j₀ km := by
  rw [coefZ2_gridPolyG, coefZ2_gridPolyG]
  split_ifs with h
  · rw [Int.toNat_of_nonneg h.1]; ring
  · rw [mul_zero]

/-- A grid symmetric under `(i, j) ↦ (2i₀ − i, 2j₀ − j)` has even Fourier coefficients. -/
theorem coefZ2_neg_of_symm {i₀ j₀ A B : ℕ} (hA : A = 2 * i₀) (hB : B = 2 * j₀)
    {g : ℕ → ℕ → ℤ} (hg : ∀ i j, i ≤ A → j ≤ B → g (A - i) (B - j) = g i j) (km : ℤ × ℤ) :
    coefZ2 (gridPolyG A B g) i₀ j₀ (-km) = coefZ2 (gridPolyG A B g) i₀ j₀ km := by
  obtain ⟨k, m⟩ := km
  rw [coefZ2_gridPolyG, coefZ2_gridPolyG]
  simp only [Prod.fst_neg, Prod.snd_neg]
  subst hA hB
  by_cases h : 0 ≤ k + i₀ ∧ 0 ≤ m + j₀ ∧ (k + i₀).toNat ≤ 2 * i₀ ∧ (m + j₀).toNat ≤ 2 * j₀
  · have h2 : 0 ≤ -k + i₀ ∧ 0 ≤ -m + j₀ ∧ (-k + i₀).toNat ≤ 2 * i₀ ∧
        (-m + j₀).toNat ≤ 2 * j₀ := by omega
    simp only [h, h2, and_self, ↓reduceIte]
    have e1 : (-k + i₀).toNat = 2 * i₀ - (k + i₀).toNat := by omega
    have e2 : (-m + j₀).toNat = 2 * j₀ - (m + j₀).toNat := by omega
    rw [e1, e2, hg _ _ h.2.2.1 h.2.2.2]
  · have h2 : ¬ (0 ≤ -k + i₀ ∧ 0 ≤ -m + j₀ ∧ (-k + i₀).toNat ≤ 2 * i₀ ∧
        (-m + j₀).toNat ≤ 2 * j₀) := by omega
    simp only [h, h2, ↓reduceIte]

/-- Degree box of a grid polynomial. -/
theorem box_gridPolyG (A B : ℕ) (g : ℕ → ℕ → ℤ) : InBox (gridPolyG A B g) A B :=
  InBox.sum _ fun i hi => InBox.sum _ fun j hj =>
    InBox.mono (InBox.monomial i j _) (by simp at hi; omega) (by simp at hj; omega)

/-- `ℓ¹` of the `q` grid polynomial. -/
theorem l1_gridPolyQ_le (g : ℕ → ℕ → ℤ) : l1 (gridPolyG 28 20 g) ≤ gridL1Q g := by
  refine (l1_sum_le _ _).trans ?_
  simp only [gridL1Q, rsum_eq]
  rw [sum_comm (s := range 21)]
  refine sum_le_sum fun i _ => ?_
  refine (l1_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun j _ => by rw [l1_monomial]

/-- `packRowQ` as a sum. -/
theorem packRowQ_eq (b : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    packRowQ b f n = ∑ i ∈ range n, f i * (2 : ℤ) ^ (b * i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packRowQ, ih, sum_range_succ]; push_cast; rfl

/-- `packGridQ` as a double sum. -/
theorem packGridQ_eq (b W : ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ) :
    packGridQ b W g m = ∑ j ∈ range m, ∑ i ∈ range 29, g i j * (2 : ℤ) ^ (b * (i + W * j)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [packGridQ, ih, sum_range_succ, packRowQ_eq, sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [mul_assoc, ← pow_add]; ring_nf

/-- Kronecker image of the `q` grid polynomial. -/
theorem kron_gridPolyQ (b W : ℕ) (g : ℕ → ℕ → ℤ) :
    kron b W (gridPolyG 28 20 g) = packGridQ b W g 21 := by
  rw [gridPolyG, packGridQ_eq, map_sum, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact sum_congr rfl fun i _ => by rw [kron_monomial]

/-- `gQc` is symmetric under `(i, j) ↦ (28 − i, 20 − j)`. -/
theorem gQc_symm (i j : ℕ) (hi : i ≤ 28) (hj : j ≤ 20) : gQc (28 - i) (20 - j) = gQc i j := by
  unfold gQc
  rw [Nat.sub_sub_self hi, Nat.sub_sub_self hj, add_comm]

/-! ## The surrogate torus and `q` as elements of `𝔸` -/

/-- `2 n₁ < 2 n₁ + 1`. -/
theorem n1_lt : 2 * n1 < 2 * n1 + 1 := Nat.lt_succ_self _

/-- `σ₁ ≠ 0` in `ℂ`. -/
theorem sig1C_ne : (sig1 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < sig1 := by unfold sig1; positivity
  exact_mod_cast this.ne'

/-- **The surrogate `u_S = R̃ − 1`** (modes `0 ≤ k ≤ 7`, `|m| ≤ 5` of torus A, rounded to
`2^{-32}`). -/
def uS : FA := ofP (Frame.box_gridPoly1 gRc) n1_lt le_rfl n1 m1 (sig1 : ℂ)

/-- **The surrogate `z_S = z̃`**. -/
def zS : FA := ofP (Frame.box_gridPoly1 gZc) n1_lt le_rfl n1 m1 (Complex.I * sig1)

/-- The polynomial `q̂` (centre `(14, 10)`, scale `σ₁²`). -/
noncomputable def PQ : P2 := gridPolyG 28 20 gQc

/-- **The multiplier `q_S ≈ 1/(D³ W₀²)`** on the surrogate torus (modes `|k| ≤ 14`, `|m| ≤ 10`). -/
def qS : FA := ofP (box_gridPolyG 28 20 gQc) (by norm_num : 28 < 29) le_rfl 14 10
  ((sig1 : ℂ) ^ 2)

/-- The function of `u_S`. -/
theorem eval_uS (θ ψ : ℝ) : eval uS θ ψ = (rS θ (phiOf ψ) : ℂ) :=
  eval_ofP _ _ _ n1 m1 sig1C_ne (F := fun θ ψ => (rS θ (phiOf ψ) : ℂ))
    (fun θ ψ => by rw [Frame.evalC_rS, T1, w1]; ring) θ ψ

/-- The function of `z_S`. -/
theorem eval_zS (θ ψ : ℝ) : eval zS θ ψ = (Frame.zS θ (phiOf ψ) : ℂ) :=
  eval_ofP _ _ _ n1 m1 (mul_ne_zero Complex.I_ne_zero sig1C_ne)
    (F := fun θ ψ => (Frame.zS θ (phiOf ψ) : ℂ))
    (fun θ ψ => by rw [Frame.evalC_zS, T1, w1]; ring) θ ψ

/-- `∂_θ u_S` is read off `â`. -/
theorem dTh_uS :
    dTh uS = ofP (Frame.box_gridPoly1 gAc) n1_lt le_rfl n1 m1 (-Complex.I * sig1) :=
  dTh_ofP _ _ _ _ _ _ n1 m1 _ fun km => by
    rw [gridPoly1_eq, gridPoly1_eq, ← coefZ2_wgrid]; rfl

/-- `∂_θ z_S` is read off `b̂`. -/
theorem dTh_zS :
    dTh zS = ofP (Frame.box_gridPoly1 gBc) n1_lt le_rfl n1 m1 (-Complex.I * (Complex.I * sig1)) :=
  dTh_ofP _ _ _ _ _ _ n1 m1 _ fun km => by
    rw [gridPoly1_eq, gridPoly1_eq, ← coefZ2_wgrid]; rfl

/-- `−i (i σ₁) = σ₁`. -/
theorem negI_I_sig1 : -Complex.I * (Complex.I * sig1) = (sig1 : ℂ) := by
  rw [← mul_assoc, neg_mul, Complex.I_mul_I]; ring

/-- The function of `∂_θ u_S`. -/
theorem eval_dTh_uS (θ ψ : ℝ) : eval (dTh uS) θ ψ = (aS θ (phiOf ψ) : ℂ) := by
  rw [dTh_uS]
  exact eval_ofP _ _ _ n1 m1 (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) sig1C_ne)
    (F := fun θ ψ => (aS θ (phiOf ψ) : ℂ)) (fun θ ψ => by rw [Frame.evalC_aS, T1, w1]; ring) θ ψ

/-- The function of `∂_θ z_S`. -/
theorem eval_dTh_zS (θ ψ : ℝ) : eval (dTh zS) θ ψ = (bS θ (phiOf ψ) : ℂ) := by
  rw [dTh_zS]
  refine eval_ofP _ _ _ n1 m1 (by rw [negI_I_sig1]; exact sig1C_ne)
    (F := fun θ ψ => (bS θ (phiOf ψ) : ℂ)) (fun θ ψ => ?_) θ ψ
  rw [Frame.evalC_bS, T1, w1, negI_I_sig1]; ring

/-- `u_S` is real. -/
theorem isReal_uS : IsReal uS := isReal_of_eval_real eval_uS
/-- `z_S` is real. -/
theorem isReal_zS : IsReal zS := isReal_of_eval_real eval_zS
/-- `q_S` is real (its grid is symmetric). -/
theorem isReal_qS : IsReal qS := by
  refine IsReal.of_coeff fun n => ?_
  rw [qS, coeff_ofP]
  simp only
  rw [coefZ2_neg_of_symm (i₀ := 14) (j₀ := 10) rfl rfl (fun i j hi hj => gQc_symm i j hi hj)]
  simp [map_mul, map_inv₀, map_pow]

/-- `u_S` is analytic. -/
theorem ana_uS : Ana uS := ana_ofP _ _ _ _ _ _
/-- `z_S` is analytic. -/
theorem ana_zS : Ana zS := ana_ofP _ _ _ _ _ _
/-- `q_S` is analytic. -/
theorem ana_qS : Ana qS := ana_ofP _ _ _ _ _ _

/-! ## The variable polynomials and their three readings -/

/-- The variable polynomials `r̂, ẑ, Ĉ, Ŝ, t̂, V̂, â, b̂`. -/
noncomputable def bP : ℕ → P2 :=
  envS (gridPoly1 gRc) (gridPoly1 gZc) SvP ChP tP1 vP2 (gridPoly1 gAc) (gridPoly1 gBc)

/-- The real values of the variables on the surrogate torus (`t = V = 1`). -/
def xS (θ φ : ℝ) : ℕ → ℝ :=
  envS (rS θ φ) (Frame.zS θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) 1 1 (aS θ φ) (bS θ φ)

/-- Phases are below `4`. -/
theorem WS_ph (i : ℕ) : (WS i).2.2 < 4 := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [WS]

/-- The variable polynomials represent the surrogate variables with their weights. -/
theorem evalC_bP (θ φ : ℝ) (i : ℕ) :
    evalC (uu θ) (vv φ) (bP i) = Ex.lam (T1 θ φ) (V1 φ) (WS i) * (xS θ φ i : ℂ) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_rS]; ring
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_zS]; ring
  · simp only [bP, envS, WS, xS, Ex.lam, evalC_SvP, cos_two_mul_eq, V1]
    push_cast; rw [I_pow3]; ring
  · simp only [bP, envS, WS, xS, Ex.lam, evalC_ChP, sin_two_mul_eq, V1]
    push_cast; ring
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_tP1]; push_cast; ring
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_vP2]; push_cast; ring
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_aS, I_pow3]; ring
  · simp only [bP, envS, WS, xS, Ex.lam, Frame.evalC_bS]; ring
  · simp only [bP, envS, WS, xS, map_zero, Complex.ofReal_zero, mul_zero]

/-- **Phase bridge** for the trees. -/
theorem evalC_tree {e : Ex} {w : ℕ × ℕ × ℕ} (hw : Ex.wt WS e = some w) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (Ex.evH WS bP e) =
      Ex.lam (T1 θ φ) (V1 φ) w * ((Ex.eval (xS θ φ) e : ℝ) : ℂ) := by
  rw [Ex.evH_map]
  exact Ex.evH_phase WS_ph (T1 θ φ) (V1 φ) (evalC_bP θ φ) e w hw

/-- Kronecker images of the variable polynomials. -/
theorem kron_bP (b W : ℕ) : (fun i => kron b W (bP i)) = bInt b W := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · exact Frame.kron_gridPoly1 b W gRc
  · exact Frame.kron_gridPoly1 b W gZc
  · exact kron_SvP b W
  · exact kron_ChP b W
  · exact Frame.kron_tP1 b W
  · exact Frame.kron_vP2 b W
  · exact Frame.kron_gridPoly1 b W gAc
  · exact Frame.kron_gridPoly1 b W gBc
  · exact map_zero _

/-- Degree boxes of the variable polynomials. -/
theorem box_bP : ∀ i, InBox (bP i) (BxS i).1 (BxS i).2
  | 0 => Frame.box_gridPoly1 _
  | 1 => Frame.box_gridPoly1 _
  | 2 => box_SvP
  | 3 => box_ChP
  | 4 => Frame.box_tP1
  | 5 => Frame.box_vP2
  | 6 => Frame.box_gridPoly1 _
  | 7 => Frame.box_gridPoly1 _
  | _ + 8 => Frame.inBox_zero _ _

/-- `ℓ¹` bounds of the variable polynomials. -/
theorem l1_bP : ∀ i, l1 (bP i) ≤ LS i
  | 0 => Frame.l1_gridPoly1_le _
  | 1 => Frame.l1_gridPoly1_le _
  | 2 => l1_SvP
  | 3 => l1_ChP
  | 4 => Frame.l1_tP1
  | 5 => Frame.l1_vP2
  | 6 => Frame.l1_gridPoly1_le _
  | 7 => Frame.l1_gridPoly1_le _
  | _ + 8 => Frame.l1_zero_le _

/-- `8 D̂`. -/
noncomputable def PD : P2 := Ex.evH WS bP treeD
/-- `128 P̂`. -/
noncomputable def PP : P2 := Ex.evH WS bP treeP
/-- `Ŵ₀`. -/
noncomputable def PW : P2 := Ex.evH WS bP treeW

/-- Degree box of `8 D̂`. -/
theorem box_PD : InBox PD 70 52 := by
  have := Ex.inBox_evH WS box_bP treeD; rwa [box_treeD] at this
/-- Degree box of `128 P̂`. -/
theorem box_PP : InBox PP 154 114 := by
  have := Ex.inBox_evH WS box_bP treeP; rwa [box_treeP] at this
/-- Degree box of `Ŵ₀`. -/
theorem box_PW : InBox PW 28 20 := by
  have := Ex.inBox_evH WS box_bP treeW; rwa [box_treeW] at this

/-- Powers stay in boxes. -/
theorem inBox_pow {P : P2} {a b : ℕ} (h : InBox P a b) : ∀ n : ℕ, InBox (P ^ n) (n * a) (n * b)
  | 0 => by simpa using InBox.C 1
  | n + 1 => by
    rw [pow_succ, add_mul, add_mul, one_mul, one_mul]; exact (inBox_pow h n).mul h

/-- `‖Pⁿ‖₁ ≤ ‖P‖₁ⁿ`. -/
theorem l1_pow_le (P : P2) : ∀ n : ℕ, l1 (P ^ n) ≤ l1 P ^ n
  | 0 => by simp only [pow_zero]; exact (le_of_eq (by simpa using l1_C 1))
  | n + 1 => by
    rw [pow_succ, pow_succ]; exact (l1_mul_le _ _).trans (Nat.mul_le_mul_right _ (l1_pow_le P n))

/-! ## The tree identities -/

/-- `8 D` is the tree `treeD` at `t = V = 1`. -/
theorem Dp_tree (r z c s a b : ℝ) :
    PolyExpr.eval (ptC r z c s 0 0) Dp = ((Ex.eval (envS r z c s 1 1 a b) treeD / 8 : ℝ) : ℂ) := by
  simp only [PolyExpr.eval, Dp, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Ex.eval, treeD, treeD0, treeD1, treeD2, treeD3, treeD4,
    envS]
  push_cast; ring

/-- `128 P` is the tree `treeP` at `t = V = 1`. -/
theorem Pp_tree (r z c s a b : ℝ) :
    PolyExpr.eval (ptC r z c s 0 0) Pp =
      ((Ex.eval (envS r z c s 1 1 a b) treeP / 128 : ℝ) : ℂ) := by
  simp only [PolyExpr.eval, Pp, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, Ex.eval, treeP, treeP0, treeP1, treeP2, treeP3, treeP4,
    treeP5, treeP6, treeP7, treeP8, treeP9, treeP10, treeP11, envS]
  push_cast; ring

/-- The variables `(u, z, c, s, 0, 0)` at the surrogate torus. -/
theorem eval_xB_S (θ ψ : ℝ) :
    (fun j => eval (xB uS zS j) θ ψ) = ptC (rS θ (phiOf ψ)) (Frame.zS θ (phiOf ψ))
      (Real.cos (2 * phiOf ψ)) (Real.sin (2 * phiOf ψ)) 0 0 := by
  funext j
  fin_cases j
  · simp [xB, ptC, eval_uS]
  · simp [xB, ptC, eval_zS]
  · simp [xB, ptC, eval_cS, cos_two_mul_eq, psi_phiOf]
  · simp [xB, ptC, eval_sS, sin_two_mul_eq, psi_phiOf]
  · simp [xB, ptC]
  · simp [xB, ptC]

/-- The function of `D(K_S)`. -/
theorem eval_DS (θ ψ : ℝ) :
    eval (Dof uS zS) θ ψ = ((Ex.eval (xS θ (phiOf ψ)) treeD / 8 : ℝ) : ℂ) := by
  rw [Dof, eval_polyExpr, eval_xB_S, Dp_tree _ _ _ _ (aS θ (phiOf ψ)) (bS θ (phiOf ψ))]
  rfl

/-- The function of `P(K_S)`. -/
theorem eval_PS (θ ψ : ℝ) :
    eval (Pof uS zS) θ ψ = ((Ex.eval (xS θ (phiOf ψ)) treeP / 128 : ℝ) : ℂ) := by
  rw [Pof, eval_polyExpr, eval_xB_S, Pp_tree _ _ _ _ (aS θ (phiOf ψ)) (bS θ (phiOf ψ))]
  rfl

/-- The function of `W₀(K_S)`. -/
theorem eval_W0S (θ ψ : ℝ) :
    eval (W0of uS zS) θ ψ = ((Ex.eval (xS θ (phiOf ψ)) treeW : ℝ) : ℂ) := by
  rw [W0of, eval_sub', eval_mul, eval_mul, eval_dTh_uS, eval_dTh_zS, eval_uS, eval_zS]
  simp only [Ex.eval, treeW, xS, envS]
  push_cast; ring

/-- The polynomial of `q_S`. -/
theorem evalC_PQ (θ ψ : ℝ) :
    evalC (uu θ) (vv (phiOf ψ)) PQ =
      (sig1 : ℂ) ^ 2 * eval qS θ ψ * (uu θ ^ 14 * vv (phiOf ψ) ^ 10) :=
  evalC_ofP _ _ _ 14 10 (pow_ne_zero 2 sig1C_ne) θ ψ

/-! ## Item 3: the winding form `W₀` -/

/-- The constant part `w_S = c0W / σ₁² ≈ −0.018135` of `W₀` on the surrogate torus. -/
def wS : ℝ := c0W / (sig1 : ℝ) ^ 2

/-- `Ŵ₀ − c0W u^{14} v^{10}`. -/
noncomputable def BigW : P2 := PW - Polynomial.monomial 10 (Polynomial.monomial 14 c0W)

/-- Degree box of `BigW`. -/
theorem box_BigW : InBox BigW 28 20 :=
  box_PW.sub ((InBox.monomial _ _ _).mono (by norm_num) (by norm_num))

/-- A priori bound of `BigW`. -/
theorem l1_BigW : l1 BigW < 2 ^ (80 - 1) := by
  refine lt_of_le_of_lt ?_ aprioriW
  refine (l1_sub_le _ _).trans (Nat.add_le_add (Ex.l1_evH WS l1_bP treeW) ?_)
  rw [l1_monomial]

/-- Kronecker image of `BigW`. -/
theorem kron_BigW : kron 80 29 BigW = intW 80 29 := by
  rw [BigW, map_sub, PW, Ex.evH_map, kron_bP, kron_monomial, intW, Nat.cast_pow, Nat.cast_ofNat]

/-- The polynomial `BigW` reads `σ₁² (W₀ − w_S)`. -/
theorem evalC_BigW (θ ψ : ℝ) :
    evalC (uu θ) (vv (phiOf ψ)) BigW = (sig1 : ℂ) ^ 2 *
      eval (W0of uS zS - algebraMap ℂ FA (wS : ℂ)) θ ψ * (uu θ ^ 14 * vv (phiOf ψ) ^ 10) := by
  rw [BigW, map_sub, PW, evalC_tree wt_treeW, evalC_monomial, eval_sub', eval_algebraMap,
    eval_W0S]
  have hs : (sig1 : ℂ) ≠ 0 := sig1C_ne
  simp only [Ex.lam, T1, w1, n1, m1, wS]
  push_cast
  field_simp

/-- **Item 3**: `‖W₀(K_S) − w_S‖_{r_A} ≤ 0.004078` (`w_S ≈ −0.018135`). -/
theorem Bd_W0S : Bd rA (W0of uS zS - algebraMap ℂ FA (wS : ℂ)) (4078 / 10 ^ 6) := by
  have hB := (wnorm_of_check (dc := 5) (dr := 5) (by norm_num) box_BigW (by norm_num)
    (by norm_num) (by norm_num) l1_BigW 14 10 14 10 kron_BigW (D := 10 ^ 6) (by norm_num)
    (c := 4078) (κ := (sig1 : ℝ) ^ 2) (by exact_mod_cast wcheckW)).2
  have h := Bd_of_evalC box_BigW (by norm_num : 28 < 29) le_rfl 14 10
    (pow_ne_zero 2 sig1C_ne) evalC_BigW hB
  have hs : (0 : ℝ) < sig1 := by unfold sig1; positivity
  rwa [norm_pow, Complex.norm_natCast, show ((sig1 : ℝ) ^ 2)⁻¹ * (4078 / 10 ^ 6 * (sig1 : ℝ) ^ 2) =
    4078 / 10 ^ 6 by field_simp] at h

/-- `w_S` lies in `[−0.01814, −0.01813]`. -/
theorem wS_bounds : -1814 / 100000 ≤ wS ∧ wS ≤ -1813 / 100000 := by
  have hs : (0 : ℝ) < (sig1 : ℝ) ^ 2 := by unfold sig1; positivity
  obtain ⟨h1, h2⟩ := check_wS
  have h1' : -1814 * (sig1 : ℝ) ^ 2 ≤ c0W * 100000 := by exact_mod_cast h1
  have h2' : (c0W : ℝ) * 100000 ≤ -1813 * (sig1 : ℝ) ^ 2 := by exact_mod_cast h2
  constructor
  · rw [wS, le_div_iff₀ hs]; linarith
  · rw [wS, div_le_iff₀ hs]; linarith

/-! ## Item 4: `q D³ W₀² ≈ 1` -/

/-- `q̂ (8D̂)³ Ŵ₀² − 512 t^{21} V³`. -/
noncomputable def Big4 : P2 := PQ * PD ^ 3 * PW ^ 2 - ((512 : ℤ) : P2) * tP1 ^ 21 * vP2 ^ 3

/-- Degree box of `Big4`. -/
theorem box_Big4 : InBox Big4 294 216 := by
  have h1 := ((box_gridPolyG 28 20 gQc).mul (inBox_pow box_PD 3)).mul (inBox_pow box_PW 2)
  have h2 := ((Ex.inBox_intCast 512).mul (inBox_pow Frame.box_tP1 21)).mul
    (inBox_pow Frame.box_vP2 3)
  exact (h1.mono (by norm_num) (by norm_num)).sub (h2.mono (by norm_num [n1])
    (by norm_num [m1]))

/-- A priori bound of `Big4`. -/
theorem l1_Big4 : l1 Big4 < 2 ^ (720 - 1) := by
  refine lt_of_le_of_lt ?_ apriori4
  refine (l1_sub_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine (l1_mul_le _ _).trans (Nat.mul_le_mul ((l1_mul_le _ _).trans (Nat.mul_le_mul
      (l1_gridPolyQ_le _) ((l1_pow_le _ 3).trans (Nat.pow_le_pow_left
        (Ex.l1_evH WS l1_bP treeD) 3)))) ((l1_pow_le _ 2).trans (Nat.pow_le_pow_left
          (Ex.l1_evH WS l1_bP treeW) 2)))
  · have h512 : l1 ((512 : ℤ) : P2) ≤ 512 := by rw [Ex.intCast_P2, l1_C]; rfl
    calc l1 (((512 : ℤ) : P2) * tP1 ^ 21 * vP2 ^ 3)
        ≤ l1 ((512 : ℤ) : P2) * l1 (tP1 ^ 21) * l1 (vP2 ^ 3) :=
          (l1_mul_le _ _).trans (Nat.mul_le_mul_right _ (l1_mul_le _ _))
      _ ≤ 512 * sig1 ^ 21 * 2 ^ 3 := Nat.mul_le_mul (Nat.mul_le_mul h512
          ((l1_pow_le _ 21).trans (Nat.pow_le_pow_left Frame.l1_tP1 21)))
          ((l1_pow_le _ 3).trans (Nat.pow_le_pow_left Frame.l1_vP2 3))
      _ = 512 * (sig1 ^ 21 * 2 ^ 3) := by ring

/-- Kronecker image of `Big4`. -/
theorem kron_Big4 : kron 720 295 Big4 = int4 720 295 := by
  rw [Big4, map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_intCast, PQ, kron_gridPolyQ, PD, PW, Ex.evH_map, Ex.evH_map, kron_bP, Frame.kron_tP1,
    Frame.kron_vP2, int4, qInt, Int.cast_id]

/-- The element `q D³ W₀² − 1` at the surrogate torus. -/
def X4 : FA := qS * Dof uS zS ^ 3 * W0of uS zS ^ 2 - 1

/-- The polynomial `Big4` reads `4096 σ₁^{21} (q D³ W₀² − 1)`. -/
theorem evalC_Big4 (θ ψ : ℝ) :
    evalC (uu θ) (vv (phiOf ψ)) Big4 = 4096 * (sig1 : ℂ) ^ 21 * eval X4 θ ψ *
      (uu θ ^ 147 * vv (phiOf ψ) ^ 108) := by
  rw [Big4, map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_intCast, evalC_PQ, PD, PW, evalC_tree wt_treeD, evalC_tree wt_treeW, Frame.evalC_tP1,
    Frame.evalC_vP2, X4, eval_sub', eval_mul, eval_mul, eval_pow', eval_pow', eval_DS, eval_W0S,
    eval_one]
  simp only [Ex.lam, T1, w1, V1, n1, m1]
  push_cast
  ring

/-- **Item 4**: `‖q_S D(K_S)³ W₀(K_S)² − 1‖_{r_A} ≤ 5.13 × 10⁻⁶`. -/
theorem Bd_X4 : Bd rA (qS * Dof uS zS ^ 3 * W0of uS zS ^ 2 - 1) (513 / 10 ^ 8) := by
  have hB := (wnorm_of_check (dc := 9) (dr := 8) (by norm_num) box_Big4 (by norm_num)
    (by norm_num) (by norm_num) l1_Big4 147 108 147 108 kron_Big4 (D := 10 ^ 8) (by norm_num)
    (c := 513) (κ := 4096 * (sig1 : ℝ) ^ 21) (by exact_mod_cast wcheck4)).2
  have hc : (4096 * (sig1 : ℂ) ^ 21) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ sig1C_ne)
  have h := Bd_of_evalC box_Big4 (by norm_num : 294 < 295) le_rfl 147 108 hc evalC_Big4 hB
  have hs : (0 : ℝ) < sig1 := by unfold sig1; positivity
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show ‖(4096 : ℂ)‖ = 4096 by norm_num,
    show (4096 * (sig1 : ℝ) ^ 21)⁻¹ * (513 / 10 ^ 8 * (4096 * (sig1 : ℝ) ^ 21)) = 513 / 10 ^ 8 by
      field_simp] at h
  exact h

/-- **Item 4** (`q`): `‖q_S‖_{r_A} ≤ 16162`. -/
theorem Bd_qS : Bd rA qS 16162 := by
  have hc : ((wl1KronP 96 29 5 5 (20 + 1) (fun i => kwtS 74315 16 14 (ndist i 14))
      (fun j => kwtS 74315 16 10 (ndist j 10)) (qInt 96 29) : ℕ) : ℝ) * 10 ≤
      161620 * ((sig1 : ℝ) ^ 2 * 2 ^ (16 * (14 + 10))) := by
    have h := wcheckQ
    generalize wl1KronP 96 29 5 5 (20 + 1) (fun i => kwtS 74315 16 14 (ndist i 14))
      (fun j => kwtS 74315 16 10 (ndist j 10)) (qInt 96 29) = X at h ⊢
    exact_mod_cast h
  have hB := (wnorm_of_check (dc := 5) (dr := 5) (by norm_num) (box_gridPolyG 28 20 gQc)
    (by norm_num) (by norm_num) (by norm_num)
    ((l1_gridPolyQ_le gQc).trans_lt aprioriQ) 14 10 14 10
    (kron_gridPolyQ 96 29 gQc : kron 96 29 (gridPolyG 28 20 gQc) = qInt 96 29)
    (D := 10) (by norm_num) (c := 161620) (κ := (sig1 : ℝ) ^ 2) hc).2
  have h := Bd_of_evalC (X := qS) (box_gridPolyG 28 20 gQc) (by norm_num : 28 < 29) le_rfl 14 10
    (pow_ne_zero 2 sig1C_ne) evalC_PQ hB
  have hs : (0 : ℝ) < sig1 := by unfold sig1; positivity
  rwa [norm_pow, Complex.norm_natCast, show ((sig1 : ℝ) ^ 2)⁻¹ * (161620 / 10 * (sig1 : ℝ) ^ 2) =
    16162 by field_simp; norm_num] at h

/-! ## Exact digit extraction -/

/-- Digit `n` of a number with digits `e_k < X`. -/
theorem digit_of_sum (e : ℕ → ℕ) {X : ℕ} (he : ∀ k, e k < X) {S n : ℕ} (hn : n < S) :
    (∑ k ∈ range S, e k * X ^ k) / X ^ n % X = e n := by
  have hX : 0 < X := lt_of_le_of_lt (Nat.zero_le _) (he 0)
  obtain ⟨L, rfl⟩ : ∃ L, S = n + (L + 1) := ⟨S - n - 1, by omega⟩
  rw [sum_range_add]
  have hA := sum_digits_lt e he n
  have e1 : ∑ k ∈ range (L + 1), e (n + k) * X ^ (n + k) =
      X ^ n * (e n + X * ∑ k ∈ range L, e (n + 1 + k) * X ^ k) := by
    rw [sum_range_succ', mul_add, mul_sum, mul_sum, add_comm]
    simp only [add_zero]
    congr 1
    · ring
    · refine sum_congr rfl fun k _ => ?_
      rw [show n + (k + 1) = n + 1 + k by ring, pow_add, pow_add, pow_one]; ring
  rw [e1, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (he n)]

/-- **Exact slot extraction**: under the box and a priori hypotheses of `l1_eq_l1Kron`, the slot
coefficient `n` of `P` is the balanced digit `n` of the Kronecker image. -/
theorem slot_eq_of_digit {P : P2} {a J W b d : ℕ} (hb : 1 ≤ b) (hbox : InBox P a J) (ha : a < W)
    (hS : W * (J + 1) ≤ 2 ^ d) (hl1 : l1 P < 2 ^ (b - 1)) {n : ℕ} (hn : n < 2 ^ d) {e₀ : ℕ}
    (hc : ((kron b W P + offs (2 ^ (b - 1)) b d).toNat >>> (b * n)) % 2 ^ b = e₀) :
    slot P W n = (e₀ : ℤ) - 2 ^ (b - 1) := by
  set H := 2 ^ (b - 1) with hH
  have hX : (2 : ℕ) ^ b = 2 * H := by
    rw [hH, ← pow_succ']; congr 1; omega
  have hcoef : ∀ k, (slot P W k).natAbs < H := fun k =>
    (natAbs_coeff_le_l1 P _ _).trans_lt hl1
  set e : ℕ → ℕ := fun k => (slot P W k + H).toNat with he_def
  have he_int : ∀ k, ((e k : ℕ) : ℤ) = slot P W k + H := fun k => by
    have := hcoef k
    rw [he_def]; simp only
    rw [Int.toNat_of_nonneg (by omega)]
  have he_lt : ∀ k, e k < 2 ^ b := fun k => by
    have h1 := he_int k; have h2 := hcoef k
    rw [hX]; omega
  have hsum : kron b W P + (offs H b d : ℤ) =
      ((∑ k ∈ range (2 ^ d), e k * (2 ^ b) ^ k : ℕ) : ℤ) := by
    rw [kron_eq_sum b hbox ha hS, offs_spec]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [he_int]; ring
  rw [hsum, Int.toNat_natCast, Nat.shiftRight_eq_div_pow, pow_mul,
    digit_of_sum e he_lt hn] at hc
  have := he_int n
  rw [hc, hH] at this
  push_cast at this
  linarith

/-! ## Item 5: the torsion `R³ P q` and its average -/

/-- `(t + r̂)³ (128 P̂) q̂`. -/
noncomputable def Big5 : P2 := (tP1 + bP 0) ^ 3 * PP * PQ

/-- Degree box of `Big5`. -/
theorem box_Big5 : InBox Big5 224 164 := by
  have h0 : InBox (tP1 + bP 0) 14 10 :=
    (Frame.box_tP1.mono (by norm_num [n1]) (by norm_num [m1])).add (box_bP 0)
  exact ((inBox_pow h0 3).mul box_PP).mul (box_gridPolyG 28 20 gQc)

/-- A priori bound of `Big5`. -/
theorem l1_Big5 : l1 Big5 < 2 ^ (560 - 1) := by
  refine lt_of_le_of_lt ?_ apriori5
  refine (l1_mul_le _ _).trans (Nat.mul_le_mul ((l1_mul_le _ _).trans (Nat.mul_le_mul
    ((l1_pow_le _ 3).trans (Nat.pow_le_pow_left ((l1_add_le _ _).trans
      (Nat.add_le_add Frame.l1_tP1 (l1_bP 0))) 3)) (Ex.l1_evH WS l1_bP treeP)))
    (l1_gridPolyQ_le _))

/-- Kronecker image of `Big5`. -/
theorem kron_Big5 : kron 560 225 Big5 = int5 560 225 := by
  rw [Big5, map_mul, map_mul, map_pow, map_add, PP, PQ, kron_gridPolyQ, Ex.evH_map, kron_bP,
    Frame.kron_tP1, int5, qInt,
    show kron 560 225 (bP 0) = Frame.packGrid1 560 225 gRc (2 * m1 + 1) from
      Frame.kron_gridPoly1 _ _ _]

/-- The element `R³ P q` at the surrogate torus. -/
def X5 : FA := (1 + uS) ^ 3 * Pof uS zS * qS

/-- The polynomial `Big5` reads `512 σ₁^{16} R³ P q`. -/
theorem evalC_Big5 (θ ψ : ℝ) :
    evalC (uu θ) (vv (phiOf ψ)) Big5 = 512 * (sig1 : ℂ) ^ 16 * eval X5 θ ψ *
      (uu θ ^ 112 * vv (phiOf ψ) ^ 82) := by
  rw [Big5, map_mul, map_mul, map_pow, map_add, evalC_PQ, PP, evalC_tree wt_treeP,
    Frame.evalC_tP1, X5, eval_mul, eval_mul, eval_pow', eval_add', eval_one, eval_uS, eval_PS]
  rw [evalC_bP θ (phiOf ψ) 0]
  simp only [Ex.lam, T1, w1, V1, n1, m1, WS, xS, envS]
  push_cast
  ring

/-- `512 σ₁^{16} ≠ 0`. -/
theorem c5_ne : (512 * (sig1 : ℂ) ^ 16) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ sig1C_ne)

/-- `X5` is read off `Big5`. -/
theorem X5_eq :
    X5 = ofP box_Big5 (by norm_num : 224 < 225) le_rfl 112 82 (512 * (sig1 : ℂ) ^ 16) :=
  eq_ofP box_Big5 _ le_rfl 112 82 c5_ne evalC_Big5

/-- **Item 5**: `‖R_S³ P(K_S) q_S‖_{r_A} ≤ 19.655`. -/
theorem Bd_X5 : Bd rA ((1 + uS) ^ 3 * Pof uS zS * qS) (19655 / 1000) := by
  have hc : ((wl1KronP 560 225 8 8 (164 + 1) (fun i => kwtS 74315 16 112 (ndist i 112))
      (fun j => kwtS 74315 16 82 (ndist j 82)) (int5 560 225) : ℕ) : ℝ) * 1000 ≤
      19655 * (512 * (sig1 : ℝ) ^ 16 * 2 ^ (16 * (112 + 82))) := by
    have h := wcheck5
    generalize wl1KronP 560 225 8 8 (164 + 1) (fun i => kwtS 74315 16 112 (ndist i 112))
      (fun j => kwtS 74315 16 82 (ndist j 82)) (int5 560 225) = X at h ⊢
    exact_mod_cast h
  have hB := (wnorm_of_check (dc := 8) (dr := 8) (by norm_num) box_Big5 (by norm_num)
    (by norm_num) (by norm_num) l1_Big5 112 82 112 82 kron_Big5 (D := 1000) (by norm_num)
    (c := 19655) (κ := 512 * (sig1 : ℝ) ^ 16) hc).2
  have h := Bd_of_evalC box_Big5 (by norm_num : 224 < 225) le_rfl 112 82 c5_ne evalC_Big5 hB
  have hs : (0 : ℝ) < sig1 := by unfold sig1; positivity
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show ‖(512 : ℂ)‖ = 512 by norm_num,
    show (512 * (sig1 : ℝ) ^ 16)⁻¹ * (19655 / 1000 * (512 * (sig1 : ℝ) ^ 16)) = 19655 / 1000 by
      field_simp] at h
  exact h

/-- The centre coefficient of `Big5` (an integer `≈ 0.3986 · 512 σ₁^{16}`). -/
def c0T : ℤ := (e0T : ℤ) - 2 ^ (560 - 1)

/-- The centre coefficient of `Big5`, read off the Kronecker image (`digit5`). -/
theorem centre_Big5 : coefZ2 Big5 112 82 (0, 0) = c0T := by
  have h := slot_eq_of_digit (d := 16) (by norm_num) box_Big5 (by norm_num : 224 < 225)
    (by norm_num) l1_Big5 (n := 112 + 225 * 82) (by norm_num) (e₀ := e0T)
    (by rw [kron_Big5]; exact digit5)
  rw [c0T, ← h]
  simp [coefZ2, slot]

/-- **The average of the torsion** on the surrogate torus: `⟨R³ P q⟩ = c0T / (512 σ₁^{16})`. -/
theorem avg_X5 : avg ((1 + uS) ^ 3 * Pof uS zS * qS) =
    (((c0T : ℝ) / (512 * (sig1 : ℝ) ^ 16) : ℝ) : ℂ) := by
  rw [← X5, X5_eq, avg, coeff_ofP]
  simp only
  rw [centre_Big5]
  push_cast
  field_simp

/-- **Item 5** (average): `0.3986 ≤ ⟨R³ P q⟩` (`⟨R³ P q⟩ ≈ 0.398640`). -/
theorem avg_X5_re : 3986 / 10000 ≤ (avg ((1 + uS) ^ 3 * Pof uS zS * qS)).re := by
  rw [avg_X5, Complex.ofReal_re]
  have hs : (0 : ℝ) < 512 * (sig1 : ℝ) ^ 16 := by unfold sig1; positivity
  have c : 3986 * (512 * (sig1 : ℤ) ^ 16) ≤ c0T * 10000 := check_avg
  have c' : 3986 * (512 * (sig1 : ℝ) ^ 16) ≤ (c0T : ℝ) * 10000 := by exact_mod_cast c
  rw [le_div_iff₀ hs]; linarith

/-- **Item 5** (reality of the average): `Im ⟨R³ P q⟩ = 0`. -/
theorem avg_X5_im : (avg ((1 + uS) ^ 3 * Pof uS zS * qS)).im = 0 := by
  rw [avg_X5, Complex.ofReal_im]

/-! ## Item 2: the distance from the surrogate to torus A -/

/-- A big-grid polynomial supported on the window is a shifted compact grid polynomial. -/
theorem evalC_gridPoly_cpt {G : ℕ → ℕ → ℤ}
    (hG : ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ Frame.inWin i j → G i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly G) =
      uu θ ^ (N - n1) * vv φ ^ (M - m1) * evalC (uu θ) (vv φ) (gridPoly1 (Frame.cpt G)) := by
  rw [evalC_gridPoly, Frame.evalC_gridPoly1_cpt G hG, ww, w1]
  simp only [N, M, n1, m1]
  norm_num
  ring

/-- `σ = 2^{58} σ₁`. -/
theorem sig_eq_mul : (sig : ℂ) = 2 ^ 58 * (sig1 : ℂ) := by
  simp only [sig, sig1, P, Frame.pS]; push_cast; ring

/-- `R̂ − t − 2^{58} R̃̂` (big grid). -/
noncomputable def PdU : P2 :=
  gridPoly gR - tP - ((2 ^ 58 : ℤ) : P2) * gridPoly (Frame.symC Frame.tA)
/-- `Ẑ − 2^{58} Z̃̂`. -/
noncomputable def PdZ : P2 := gridPoly gZ - ((2 ^ 58 : ℤ) : P2) * gridPoly (Frame.symS Frame.tB)
/-- `R̂_θ − 2^{58} R̃̂_θ`. -/
noncomputable def PdA : P2 :=
  gridPoly gRth - ((2 ^ 58 : ℤ) : P2) * gridPoly (wθ (Frame.symC Frame.tA))
/-- `Ẑ_θ − 2^{58} Z̃̂_θ`. -/
noncomputable def PdB : P2 :=
  gridPoly gZth - ((2 ^ 58 : ℤ) : P2) * gridPoly (wθ (Frame.symS Frame.tB))

/-- Box of `2^{58} ×` a grid polynomial. -/
theorem box_c58 (g : ℕ → ℕ → ℤ) : InBox (((2 ^ 58 : ℤ) : P2) * gridPoly g) (2 * N) (2 * M) := by
  have h := (Ex.inBox_intCast (2 ^ 58)).mul (box_gridPoly g)
  rwa [zero_add, zero_add] at h

/-- `ℓ¹` of `2^{58} ×` a grid polynomial. -/
theorem l1_c58 (g : ℕ → ℕ → ℤ) : l1 (((2 ^ 58 : ℤ) : P2) * gridPoly g) ≤ 2 ^ 58 * gridL1 g := by
  rw [Ex.intCast_P2]
  exact (l1_C_mul_le _ _).trans (Nat.mul_le_mul (le_of_eq rfl) (l1_gridPoly_le g))

/-- Box of `PdU`. -/
theorem box_PdU : InBox PdU (2 * N) (2 * M) :=
  ((box_gridPoly _).sub (box_tP.mono (by norm_num [N]) (by norm_num [M]))).sub (box_c58 _)
/-- Box of `PdZ`. -/
theorem box_PdZ : InBox PdZ (2 * N) (2 * M) := (box_gridPoly _).sub (box_c58 _)
/-- Box of `PdA`. -/
theorem box_PdA : InBox PdA (2 * N) (2 * M) := (box_gridPoly _).sub (box_c58 _)
/-- Box of `PdB`. -/
theorem box_PdB : InBox PdB (2 * N) (2 * M) := (box_gridPoly _).sub (box_c58 _)

/-- A priori bound of `PdU`. -/
theorem l1_PdU : l1 PdU < 2 ^ (128 - 1) :=
  lt_of_le_of_lt ((l1_sub_le _ _).trans (Nat.add_le_add ((l1_sub_le _ _).trans
    (Nat.add_le_add (l1_gridPoly_le _) l1_tP)) (l1_c58 _))) apriori_dist.1
/-- A priori bound of `PdZ`. -/
theorem l1_PdZ : l1 PdZ < 2 ^ (128 - 1) :=
  lt_of_le_of_lt ((l1_sub_le _ _).trans (Nat.add_le_add (l1_gridPoly_le _) (l1_c58 _)))
    apriori_dist.2.1
/-- A priori bound of `PdA`. -/
theorem l1_PdA : l1 PdA < 2 ^ (128 - 1) :=
  lt_of_le_of_lt ((l1_sub_le _ _).trans (Nat.add_le_add (l1_gridPoly_le _) (l1_c58 _)))
    apriori_dist.2.2.1
/-- A priori bound of `PdB`. -/
theorem l1_PdB : l1 PdB < 2 ^ (128 - 1) :=
  lt_of_le_of_lt ((l1_sub_le _ _).trans (Nat.add_le_add (l1_gridPoly_le _) (l1_c58 _)))
    apriori_dist.2.2.2

/-- Kronecker image of `PdU`. -/
theorem kron_PdU : kron 128 65 PdU = distU := by
  rw [PdU, map_sub, map_sub, map_mul, map_intCast, kron_gridPoly, kron_gridPoly, kron_tP, distU,
    tGrid, Int.cast_id]
/-- Kronecker image of `PdZ`. -/
theorem kron_PdZ : kron 128 65 PdZ = distZ := by
  rw [PdZ, map_sub, map_mul, map_intCast, kron_gridPoly, kron_gridPoly, distZ, Int.cast_id]
/-- Kronecker image of `PdA`. -/
theorem kron_PdA : kron 128 65 PdA = distA := by
  rw [PdA, map_sub, map_mul, map_intCast, kron_gridPoly, kron_gridPoly, distA, Int.cast_id]
/-- Kronecker image of `PdB`. -/
theorem kron_PdB : kron 128 65 PdB = distB := by
  rw [PdB, map_sub, map_mul, map_intCast, kron_gridPoly, kron_gridPoly, distB, Int.cast_id]

/-- `PdU` reads `σ (u₀ − u_S)`. -/
theorem evalC_PdU (θ ψ : ℝ) : evalC (uu θ) (vv (phiOf ψ)) PdU =
    (sig : ℂ) * eval (u₀ - uS) θ ψ * (uu θ ^ N * vv (phiOf ψ) ^ M) := by
  rw [PdU, map_sub, map_sub, map_mul, map_intCast, evalC_Rh, evalC_tP,
    evalC_gridPoly_cpt (Frame.symC_support Frame.tA_supp),
    show Frame.cpt (Frame.symC Frame.tA) = gRc from rfl, Frame.evalC_rS, eval_sub', eval_u₀,
    eval_uS, tt, ww, T1, w1, sig_eq_mul]
  simp only [N, M, n1, m1]
  push_cast
  ring

/-- `PdZ` reads `i σ (z₀ − z_S)`. -/
theorem evalC_PdZ (θ ψ : ℝ) : evalC (uu θ) (vv (phiOf ψ)) PdZ =
    (Complex.I * sig) * eval (z₀ - zS) θ ψ * (uu θ ^ N * vv (phiOf ψ) ^ M) := by
  rw [PdZ, map_sub, map_mul, map_intCast, evalC_Zh,
    evalC_gridPoly_cpt (Frame.symS_support Frame.tB_supp),
    show Frame.cpt (Frame.symS Frame.tB) = gZc from rfl, Frame.evalC_zS, eval_sub', eval_z₀,
    eval_zS, tt, ww, T1, w1, sig_eq_mul]
  simp only [N, M, n1, m1]
  push_cast
  ring

/-- `PdA` reads `−i σ (∂_θ u₀ − ∂_θ u_S)`. -/
theorem evalC_PdA (θ ψ : ℝ) : evalC (uu θ) (vv (phiOf ψ)) PdA =
    (-Complex.I * sig) * eval (dTh u₀ - dTh uS) θ ψ * (uu θ ^ N * vv (phiOf ψ) ^ M) := by
  rw [PdA, map_sub, map_mul, map_intCast, evalC_Rth,
    evalC_gridPoly_cpt (G := wθ (Frame.symC Frame.tA)) (fun i j h1 h2 h3 =>
      Frame.wsym_support (Frame.symC_support Frame.tA_supp) i j h1 h2 h3),
    show Frame.cpt (wθ (Frame.symC Frame.tA)) = gAc from Frame.gAc_eq.symm, Frame.evalC_aS,
    eval_sub', dTh_u₀, eval_Rθ₀, eval_dTh_uS, tt, ww, T1, w1, sig_eq_mul]
  simp only [N, M, n1, m1]
  push_cast
  ring

/-- `PdB` reads `σ (∂_θ z₀ − ∂_θ z_S)`. -/
theorem evalC_PdB (θ ψ : ℝ) : evalC (uu θ) (vv (phiOf ψ)) PdB =
    (sig : ℂ) * eval (dTh z₀ - dTh zS) θ ψ * (uu θ ^ N * vv (phiOf ψ) ^ M) := by
  rw [PdB, map_sub, map_mul, map_intCast, evalC_Zth,
    evalC_gridPoly_cpt (G := wθ (Frame.symS Frame.tB)) (fun i j h1 h2 h3 =>
      Frame.wsym_support (Frame.symS_support Frame.tB_supp) i j h1 h2 h3),
    show Frame.cpt (wθ (Frame.symS Frame.tB)) = gBc from Frame.gBc_eq.symm, Frame.evalC_bS,
    eval_sub', dTh_z₀, eval_zθ₀, eval_dTh_zS, tt, ww, T1, w1, sig_eq_mul]
  simp only [N, M, n1, m1]
  push_cast
  ring

/-- `σ ≠ 0` in `ℂ`. -/
theorem sigC_ne' : (sig : ℂ) ≠ 0 := by exact_mod_cast sig_pos.ne'

/-- `‖σ‖⁻¹ (c σ) = c`. -/
theorem sig_cancel (c : ℝ) : ‖(sig : ℂ)‖⁻¹ * (c * sig) = c := by
  have := sig_pos.ne'
  rw [Complex.norm_natCast]; field_simp

/-- **Item 2** (`u`): `‖u₀ − u_S‖_{r_A} ≤ 2.2 × 10⁻⁷`. -/
theorem Bd_du : Bd rA (u₀ - uS) (22 / 10 ^ 8) := by
  have hB := (wnorm_of_check (dc := 7) (dr := 6) (by norm_num) box_PdU (by norm_num [N])
    (by norm_num [N]) (by norm_num [M]) l1_PdU N M 32 22 kron_PdU (D := 10 ^ 8) (by norm_num)
    (c := 22) (κ := (sig : ℝ)) (by exact_mod_cast wcheck_du)).2
  have h := Bd_of_evalC box_PdU (by norm_num [N] : 2 * N < 65) le_rfl N M sigC_ne' evalC_PdU hB
  rwa [sig_cancel] at h

/-- **Item 2** (`z`): `‖z₀ − z_S‖_{r_A} ≤ 2.2 × 10⁻⁷`. -/
theorem Bd_dz : Bd rA (z₀ - zS) (22 / 10 ^ 8) := by
  have hB := (wnorm_of_check (dc := 7) (dr := 6) (by norm_num) box_PdZ (by norm_num [N])
    (by norm_num [N]) (by norm_num [M]) l1_PdZ N M 32 22 kron_PdZ (D := 10 ^ 8) (by norm_num)
    (c := 22) (κ := (sig : ℝ)) (by exact_mod_cast wcheck_dz)).2
  have h := Bd_of_evalC box_PdZ (by norm_num [N] : 2 * N < 65) le_rfl N M
    (mul_ne_zero Complex.I_ne_zero sigC_ne') evalC_PdZ hB
  rwa [norm_mul, Complex.norm_I, one_mul, sig_cancel] at h

/-- **Item 2** (`∂_θ u`): `‖∂_θ u₀ − ∂_θ u_S‖_{r_A} ≤ 7.7 × 10⁻⁷`. -/
theorem Bd_da : Bd rA (dTh u₀ - dTh uS) (77 / 10 ^ 8) := by
  have hB := (wnorm_of_check (dc := 7) (dr := 6) (by norm_num) box_PdA (by norm_num [N])
    (by norm_num [N]) (by norm_num [M]) l1_PdA N M 32 22 kron_PdA (D := 10 ^ 8) (by norm_num)
    (c := 77) (κ := (sig : ℝ)) (by exact_mod_cast wcheck_da)).2
  have h := Bd_of_evalC box_PdA (by norm_num [N] : 2 * N < 65) le_rfl N M
    (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) sigC_ne') evalC_PdA hB
  rwa [norm_mul, norm_neg, Complex.norm_I, one_mul, sig_cancel] at h

/-- **Item 2** (`∂_θ z`): `‖∂_θ z₀ − ∂_θ z_S‖_{r_A} ≤ 7.7 × 10⁻⁷`. -/
theorem Bd_db : Bd rA (dTh z₀ - dTh zS) (77 / 10 ^ 8) := by
  have hB := (wnorm_of_check (dc := 7) (dr := 6) (by norm_num) box_PdB (by norm_num [N])
    (by norm_num [N]) (by norm_num [M]) l1_PdB N M 32 22 kron_PdB (D := 10 ^ 8) (by norm_num)
    (c := 77) (κ := (sig : ℝ)) (by exact_mod_cast wcheck_db)).2
  have h := Bd_of_evalC box_PdB (by norm_num [N] : 2 * N < 65) le_rfl N M sigC_ne' evalC_PdB hB
  rwa [sig_cancel] at h

/-! ## Summary -/

/-- **The surrogate torus of torus A in the strip algebra.** At `r_A = 0.1257`:
* `u_S, z_S, q_S` are real and analytic;
* `‖u₀ − u_S‖, ‖z₀ − z_S‖ ≤ 2.2 × 10⁻⁷`, `‖∂_θ u₀ − ∂_θ u_S‖, ‖∂_θ z₀ − ∂_θ z_S‖ ≤ 7.7 × 10⁻⁷`;
* `‖W₀(K_S) − w_S‖ ≤ 0.004078` with `w_S ∈ [−0.01814, −0.01813]`;
* `‖q_S D(K_S)³ W₀(K_S)² − 1‖ ≤ 5.13 × 10⁻⁶`, `‖q_S‖ ≤ 16162`;
* `‖R_S³ P(K_S) q_S‖ ≤ 19.655`, `⟨R_S³ P(K_S) q_S⟩` is real and `≥ 0.3986`. -/
theorem torusA_surrogate :
    (IsReal uS ∧ IsReal zS ∧ IsReal qS ∧ Ana uS ∧ Ana zS ∧ Ana qS) ∧
    (Bd rA (u₀ - uS) (22 / 10 ^ 8) ∧ Bd rA (z₀ - zS) (22 / 10 ^ 8) ∧
      Bd rA (dTh u₀ - dTh uS) (77 / 10 ^ 8) ∧ Bd rA (dTh z₀ - dTh zS) (77 / 10 ^ 8)) ∧
    (Bd rA (W0of uS zS - algebraMap ℂ FA (wS : ℂ)) (4078 / 10 ^ 6) ∧
      -1814 / 100000 ≤ wS ∧ wS ≤ -1813 / 100000) ∧
    (Bd rA (qS * Dof uS zS ^ 3 * W0of uS zS ^ 2 - 1) (513 / 10 ^ 8) ∧ Bd rA qS 16162) ∧
    (Bd rA ((1 + uS) ^ 3 * Pof uS zS * qS) (19655 / 1000) ∧
      3986 / 10000 ≤ (avg ((1 + uS) ^ 3 * Pof uS zS * qS)).re ∧
      (avg ((1 + uS) ^ 3 * Pof uS zS * qS)).im = 0) :=
  ⟨⟨isReal_uS, isReal_zS, isReal_qS, ana_uS, ana_zS, ana_qS⟩, ⟨Bd_du, Bd_dz, Bd_da, Bd_db⟩,
    ⟨Bd_W0S, wS_bounds⟩, ⟨Bd_X4, Bd_qS⟩, ⟨Bd_X5, avg_X5_re, avg_X5_im⟩⟩

/-! ## Sanity checks -/

/-- Accepted fixture: digit `1` of `3 + 4·10 + 5·100` is `4`. -/
theorem digit_fixture : (∑ k ∈ range 3, (k + 3) % 10 * 10 ^ k) / 10 ^ 1 % 10 = 4 :=
  digit_of_sum (fun k => (k + 3) % 10) (fun k => Nat.mod_lt _ (by norm_num)) (by norm_num)

/-- Rejected fixture: with a digit `12 ≥ 10` the extraction of digit `0` reads `2`, not `12`. -/
theorem digit_reject_fixture : (12 + 0 * 10) / 10 ^ 0 % 10 = 2 := by norm_num

/-- Degenerate case: outside the box, the Fourier coefficients of a grid polynomial vanish. -/
theorem coefZ2_gridPolyG_out (g : ℕ → ℕ → ℤ) : coefZ2 (gridPolyG 0 0 g) 0 0 (1, 0) = 0 := by
  rw [coefZ2_gridPolyG]; simp

end PlasmaLean.Design.KamNewton
