/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.KronExpr
public import LeanTheory.Theory.KAM.StripAlgebra

/-!
# Ball arithmetic in the strip algebra by Kronecker certificates

Validated numerics in the strip algebra `𝔸 = FA` (`Theory/KAM/StripAlgebra`) for long chains of
products of trigonometric polynomials (as in KAM residual certificates).
A quantity `X ∈ 𝔸` is enclosed in a **ball**: a trigonometric polynomial *centre* `x` with
integer coefficients over `2^S` and a radius `ε` with `‖X − x‖_r ≤ ε` (`Bd r (X − x) ε`).
Centres are truncated and rounded after every step (the data are supplied by an untrusted
oracle), so that their size stays bounded; each step is checked by one kernel computation.

**Centres.** `phiK : ℤ[u][v] →+* 𝔸` sends `u ↦ e^{iθ}`, `v ↦ e^{iψ}`. With
`T = 2^S e^{i(Nθ + Mψ)}` and `V = 2 e^{iψ}`, a polynomial `P` of *weight*
`w = (d, e, p)` (`KronExpr.Ex.wt`) represents the centre `ctr S N M w P` with
`phiK P = λ(w) · ctr S N M w P`, `λ(w) = T^d V^e i^p` (`phiK_eq_lam_ctr`). Its coefficients are
those of `P`, shifted by `(dN, dM + e)` and divided by `2^{Sd + e} i^p` (`coeff_ctr`), so its strip
norm is a weighted digit sum of a Kronecker image (`Bd_ctr_of_wl1`).

**Steps.** For an expression tree `e` (`KronExpr.Ex`) in variables with centres `x i`:
* `evH_phaseF`: the phased evaluation of `e` on the polynomials is `λ(w)` times the honest value
  `Ex.eval x e` in `𝔸` (the `𝔸`-version of `KronExpr.Ex.evH_phase`);
* `Bd_eval_sub` (Lipschitz part): `‖eval X e − eval x e‖ ≤ dmajQ B E e` from `‖x i‖ ≤ B i`,
  `‖X i − x i‖ ≤ E i`;
* `node_eq` (truncation part): with a new centre `Q` of weight `w'` and an integer `c`,
  `eval x e − c · ctr w' Q = ctr w G`, `G = evH e − c T^{d−d'} V^{e−e'} Q`, so the truncation
  error is the norm of one explicit polynomial `G` (one kernel check `wl1KronP`).

**Sanity.** `phiK_one_var`, `ctr_zero`, `lamF_zero`, `coefZ2_add`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Certificates.KronBall

open Polynomial Finset LeanTheory.Certificates.Kron2 LeanTheory.Certificates.KronExpr
  LeanTheory.Theory.KAM WEll1Z2 Complex

/-! ## The evaluation `ℤ[u][v] → 𝔸` -/

/-- `u ↦ e^{iθ}`, `v ↦ e^{iψ}`. -/
def phiK : P2 →+* FA :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom FA) (mode 0 (1, 0))) (mode 0 (0, 1))

/-- Powers of a mode. -/
theorem mode_pow (a : ℤ × ℤ) : ∀ n : ℕ, (mode 0 a : FA) ^ n = mode 0 ((n : ℤ) • a)
  | 0 => by simp [mode_zero]
  | n + 1 => by
    rw [pow_succ, mode_pow a n, mode_mul]
    congr 1
    push_cast
    rw [add_smul, one_smul]

/-- The mode `(0, 0)` is `1`. -/
theorem mode_zero_pair : (mode 0 ((0 : ℤ), (0 : ℤ)) : FA) = 1 := mode_zero

/-- Integer casts in `𝔸` are scalar multiples of `1`. -/
theorem intCast_FA (c : ℤ) : (c : FA) = (c : ℂ) • (1 : FA) := by
  rw [Algebra.smul_def, mul_one, map_intCast]

/-- `phiK` of a monomial. -/
theorem phiK_monomial (i j : ℕ) (c : ℤ) :
    phiK (monomial j (monomial i c)) = (c : ℂ) • mode 0 ((i : ℤ), (j : ℤ)) := by
  simp only [phiK, coe_eval₂RingHom, eval₂_monomial, eq_intCast]
  rw [mode_pow, mode_pow, mul_assoc, mode_mul, intCast_FA, smul_mul_assoc, one_mul]
  congr 2
  simp

/-- `phiK` of a monomial times a mode. -/
theorem phiK_monomial_mul_mode (i j : ℕ) (c : ℤ) (a : ℤ × ℤ) :
    phiK (monomial j (monomial i c)) * mode 0 a = (c : ℂ) • mode 0 (((i : ℤ), (j : ℤ)) + a) := by
  rw [phiK_monomial, smul_mul_assoc, mode_mul]

/-- `coefZ2` is additive. -/
theorem coefZ2_add (P Q : P2) (i₀ j₀ : ℕ) (km : ℤ × ℤ) :
    coefZ2 (P + Q) i₀ j₀ km = coefZ2 P i₀ j₀ km + coefZ2 Q i₀ j₀ km := by
  unfold coefZ2
  split_ifs <;> simp

/-- `coefZ2` of a monomial. -/
theorem coefZ2_monomial (i j : ℕ) (c : ℤ) (i₀ j₀ : ℕ) (km : ℤ × ℤ) :
    coefZ2 (monomial j (monomial i c)) i₀ j₀ km =
      if km = ((i : ℤ) - i₀, (j : ℤ) - j₀) then c else 0 := by
  obtain ⟨k, m⟩ := km
  by_cases h2 : k = (i : ℤ) - i₀ ∧ m = (j : ℤ) - j₀
  · obtain ⟨rfl, rfl⟩ := h2
    simp [coefZ2]
  · simp only [Prod.mk.injEq, h2, ↓reduceIte]
    unfold coefZ2
    split_ifs with h1
    · rw [Polynomial.coeff_monomial]
      split_ifs with h3
      · rw [Polynomial.coeff_monomial]
        split_ifs with h4
        · exfalso; omega
        · rfl
      · rfl
    · rfl

/-- **Coefficients of `phiK P` shifted by a mode** are `coefZ2`. -/
theorem coeff_phiK_mul_mode (P : P2) (i₀ j₀ : ℕ) :
    coeff (phiK P * mode 0 (-(i₀ : ℤ), -(j₀ : ℤ))) = fun km => (coefZ2 P i₀ j₀ km : ℂ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    funext km
    rw [map_add, add_mul, coeff_add, hp, hq, coefZ2_add]
    push_cast; ring
  | monomial j p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      funext km
      rw [show monomial j (p + q) = monomial j p + monomial j q from (monomial j).map_add p q,
        map_add, add_mul, coeff_add, congrFun hp km, congrFun hq km, coefZ2_add]
      push_cast; ring
    | monomial i c =>
      funext km
      rw [phiK_monomial_mul_mode, WEll1Z2.coeff_smul, coeff_mode, coefZ2_monomial]
      simp only [Pi.single_apply]
      have e : (((i : ℤ), (j : ℤ)) + (-(i₀ : ℤ), -(j₀ : ℤ))) = ((i : ℤ) - i₀, (j : ℤ) - j₀) := by
        ext <;> simp [sub_eq_add_neg]
      rw [e]
      split_ifs <;> simp

/-! ## Centres -/

/-- `λ(w) = T^d V^e i^p` for elements `T, V` of `𝔸`. -/
def lamG (T V : FA) (w : ℕ × ℕ × ℕ) : FA := T ^ w.1 * V ^ w.2.1 * algebraMap ℂ FA (I ^ w.2.2)

/-- `T = 2^S e^{i(Nθ + Mψ)}`. -/
def Tc (S N M : ℕ) : FA := ((2 : ℂ) ^ S) • mode 0 ((N : ℤ), (M : ℤ))

/-- `V = 2 e^{iψ}`. -/
def Vc : FA := (2 : ℂ) • mode 0 (0, 1)

/-- `λ(w)` for `T = 2^S e^{i(Nθ+Mψ)}`, `V = 2 e^{iψ}`. -/
def lamF (S N M : ℕ) (w : ℕ × ℕ × ℕ) : FA := lamG (Tc S N M) Vc w

/-- The scalar `2^{Sd + e} i^p` of a weight. -/
def scal (S : ℕ) (w : ℕ × ℕ × ℕ) : ℂ := (2 : ℂ) ^ (S * w.1 + w.2.1) * I ^ w.2.2

/-- The scalar of a weight is nonzero. -/
theorem scal_ne_zero (S : ℕ) (w : ℕ × ℕ × ℕ) : scal S w ≠ 0 := by
  unfold scal
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ I_ne_zero)

/-- The norm of the scalar of a weight. -/
theorem norm_scal (S : ℕ) (w : ℕ × ℕ × ℕ) : ‖scal S w‖ = 2 ^ (S * w.1 + w.2.1) := by
  simp [scal, norm_pow]

/-- The mode offset `(dN, dM + e)` of a weight. -/
def ofsW (N M : ℕ) (w : ℕ × ℕ × ℕ) : ℤ × ℤ := ((w.1 * N : ℕ), (w.1 * M + w.2.1 : ℕ))

/-- `λ(w) = 2^{Sd+e} i^p e^{i(dNθ + (dM+e)ψ)}`. -/
theorem lamF_eq (S N M : ℕ) (w : ℕ × ℕ × ℕ) :
    lamF S N M w = scal S w • mode 0 (ofsW N M w) := by
  obtain ⟨d, e, p⟩ := w
  simp only [lamF, lamG, Tc, Vc, scal, ofsW, smul_pow, mode_pow, Algebra.algebraMap_eq_smul_one]
  rw [smul_mul_smul_comm, mode_mul, mul_smul_comm, mul_one, smul_smul]
  congr 1
  · rw [← pow_mul, pow_add]; ring
  · congr 1; ext <;> simp [mul_comm]

/-- **The centre represented by a polynomial of weight `w`.** -/
def ctr (S N M : ℕ) (w : ℕ × ℕ × ℕ) (P : P2) : FA :=
  (scal S w)⁻¹ • (phiK P * mode 0 (-ofsW N M w))

/-- The negated offset in coordinates. -/
theorem neg_offs (N M : ℕ) (w : ℕ × ℕ × ℕ) :
    -ofsW N M w = (-((w.1 * N : ℕ) : ℤ), -((w.1 * M + w.2.1 : ℕ) : ℤ)) := by
  ext <;> simp [ofsW]

/-- `phiK P = λ(w) · ctr w P`. -/
theorem phiK_eq_lam_ctr (S N M : ℕ) (w : ℕ × ℕ × ℕ) (P : P2) :
    phiK P = lamF S N M w * ctr S N M w P := by
  rw [lamF_eq, ctr, smul_mul_smul_comm, mul_inv_cancel₀ (scal_ne_zero S w), one_smul,
    mul_left_comm, mode_mul, add_neg_cancel, mode_zero, mul_one]

/-- Coefficients of a centre. -/
theorem coeff_ctr (S N M : ℕ) (w : ℕ × ℕ × ℕ) (P : P2) :
    coeff (ctr S N M w P) =
      fun km => (scal S w)⁻¹ * (coefZ2 P (w.1 * N) (w.1 * M + w.2.1) km : ℂ) := by
  funext km
  rw [ctr, WEll1Z2.coeff_smul, neg_offs]
  have := congrFun (coeff_phiK_mul_mode P (w.1 * N) (w.1 * M + w.2.1)) km
  rw [this]

/-- **Strip norm of a centre** from a weighted norm of its coefficients. -/
theorem Bd_ctr {S N M : ℕ} {w : ℕ × ℕ × ℕ} {P : P2} {r B : ℝ}
    (hin : InWeighted r (fun km => (coefZ2 P (w.1 * N) (w.1 * M + w.2.1) km : ℂ)))
    (hB : wnorm r (fun km => (coefZ2 P (w.1 * N) (w.1 * M + w.2.1) km : ℂ)) ≤ B) :
    Bd r (ctr S N M w P) (B / 2 ^ (S * w.1 + w.2.1)) := by
  rw [Bd, coeff_ctr]
  refine ⟨inWeighted_smul hin _, ?_⟩
  rw [wnorm_smul, norm_inv, norm_scal, inv_mul_eq_div]
  gcongr

/-- **Strip norm of a centre by one kernel computation** (`wl1KronP`, weights
`p^s 2^{e(K − s)}` dominating `e^{r s}`). -/
theorem Bd_ctr_of_wl1 {S N M : ℕ} {w : ℕ × ℕ × ℕ} {P : P2} {a J W b dc dr : ℕ} (hb : 1 ≤ b)
    (hbox : InBox P a J) (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr)
    (hl1 : l1 P < 2 ^ (b - 1)) {r : ℝ} {p e : ℕ} (hq : Real.exp r ≤ p / 2 ^ e) (Ki Kj : ℕ)
    {K : ℕ}
    (hK : wl1KronP b W dc dr (J + 1) (fun i => kwtS p e Ki (ndist i (w.1 * N)))
        (fun j => kwtS p e Kj (ndist j (w.1 * M + w.2.1))) (kron b W P) ≤ K) :
    Bd r (ctr S N M w P) (K / 2 ^ (e * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1)) := by
  obtain ⟨h1, h2⟩ := wnorm_coefZ2_le_wl1KronP hb hbox ha hW hJ hl1 (w.1 * N) (w.1 * M + w.2.1)
    hq Ki Kj
  refine Bd_ctr h1 ?_
  rw [le_div_iff₀ (by positivity)]
  exact h2.trans (by exact_mod_cast hK)

/-! ## The phase bridge in `𝔸` -/

/-- `i^(n mod 4) = i^n` in `𝔸`. -/
theorem algI_pow_mod4 (n : ℕ) :
    algebraMap ℂ FA (I ^ (n % 4)) = algebraMap ℂ FA (I ^ n) := by rw [Ex.I_pow_mod4]

/-- Sum step of `evH_phaseF`. -/
theorem phase_addF {T V : FA} {d dv p p' : ℕ} (hp : p < 4) (hp' : p' < 4)
    (h2 : (p + p') % 2 = 0) (A B : FA) :
    lamG T V (d, dv, p) * A + ((if p = p' then 1 else -1 : ℤ) : FA) * (lamG T V (d, dv, p') * B) =
      lamG T V (d, dv, p) * (A + B) := by
  split_ifs with h
  · subst h; push_cast; ring
  · simp only [lamG, Ex.I_pow_flip hp hp' h h2, map_neg]; push_cast; ring

/-- **The phase bridge in `𝔸`.** If each variable is represented by `x̂ᵢ = λ(Wᵢ) xᵢ` and the tree
is homogeneous with weight `w`, then the phased evaluation is `λ(w)` times the honest value. -/
theorem evH_phaseF {W : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (W i).2.2 < 4) (T V : FA) {xh x : ℕ → FA}
    (hx : ∀ i, xh i = lamG T V (W i) * x i) :
    ∀ (e : Ex) (w : ℕ × ℕ × ℕ), Ex.wt W e = some w →
      Ex.evH W xh e = lamG T V w * Ex.eval x e
  | .var i, w, h => by
    simp only [Ex.wt, Option.some.injEq] at h; rw [← h]; exact hx i
  | .cst k, w, h => by
    simp only [Ex.wt, Option.some.injEq] at h; rw [← h]; simp [Ex.evH, Ex.eval, lamG]
  | .add e f, w, h => by
    simp only [Ex.wt] at h
    rcases he : Ex.wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : Ex.wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, Ex.comb, reduceCtorEq] at h
    split_ifs at h with hc
    obtain ⟨rfl, rfl, h2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have hp : p < 4 := Ex.wt_ph_lt hW e _ he
    have hp' : p' < 4 := Ex.wt_ph_lt hW f _ hf
    simp only [Ex.evH, Ex.eval, Ex.sgn, he, hf, evH_phaseF hW T V hx e _ he,
      evH_phaseF hW T V hx f _ hf]
    rw [phase_addF hp hp' h2]
  | .sub e f, w, h => by
    simp only [Ex.wt] at h
    rcases he : Ex.wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : Ex.wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, Ex.comb, reduceCtorEq] at h
    split_ifs at h with hc
    obtain ⟨rfl, rfl, h2⟩ := hc
    simp only [Option.some.injEq] at h; subst h
    have hp : p < 4 := Ex.wt_ph_lt hW e _ he
    have hp' : p' < 4 := Ex.wt_ph_lt hW f _ hf
    simp only [Ex.evH, Ex.eval, Ex.sgn, he, hf, evH_phaseF hW T V hx e _ he,
      evH_phaseF hW T V hx f _ hf]
    have key := phase_addF (T := T) (V := V) (d := d) (dv := dv) hp hp' h2
      (Ex.eval x e) (-(Ex.eval x f))
    linear_combination key
  | .mul e f, w, h => by
    simp only [Ex.wt] at h
    rcases he : Ex.wt W e with _ | ⟨d, dv, p⟩ <;> rcases hf : Ex.wt W f with _ | ⟨d', dv', p'⟩ <;>
      simp only [he, hf, Ex.wmul, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [Ex.evH, Ex.eval, evH_phaseF hW T V hx e _ he, evH_phaseF hW T V hx f _ hf, lamG,
      algI_pow_mod4, pow_add, map_mul]
    ring

/-! ## The Lipschitz part -/

/-- **Majorant and perturbation bounds in `𝔸`**: from `‖x' i‖ ≤ B i` and `‖x i − x' i‖ ≤ E i`,
`‖eval x' e‖ ≤ majQ B e` and `‖eval x e − eval x' e‖ ≤ dmajQ B E e`. -/
theorem Bd_eval_sub {r : ℝ} (hr : 0 ≤ r) {B E : ℕ → ℚ} {x x' : ℕ → FA}
    (hB : ∀ i, Bd r (x' i) (B i)) (hE : ∀ i, Bd r (x i - x' i) (E i)) :
    ∀ e : Ex, Bd r (Ex.eval x' e) (Ex.majQ B e) ∧
      Bd r (Ex.eval x e - Ex.eval x' e) (Ex.dmajQ B E e)
  | .var i => ⟨hB i, hE i⟩
  | .cst k => by
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ]
      have := Bd_algebraMap r (k : ℂ)
      rw [map_intCast] at this
      simpa [Complex.norm_intCast] using this
    · simp only [Ex.eval, Ex.dmajQ, sub_self, Rat.cast_zero]; exact Bd_zero r
  | .add e f => by
    obtain ⟨h1, h2⟩ := Bd_eval_sub hr hB hE e
    obtain ⟨h3, h4⟩ := Bd_eval_sub hr hB hE f
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_add]; exact h1.add h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add]
      have := h2.add h4
      rwa [show Ex.eval x e - Ex.eval x' e + (Ex.eval x f - Ex.eval x' f) =
        Ex.eval x e + Ex.eval x f - (Ex.eval x' e + Ex.eval x' f) by ring] at this
  | .sub e f => by
    obtain ⟨h1, h2⟩ := Bd_eval_sub hr hB hE e
    obtain ⟨h3, h4⟩ := Bd_eval_sub hr hB hE f
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_add]; exact h1.sub h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add]
      have := h2.sub h4
      rwa [show Ex.eval x e - Ex.eval x' e - (Ex.eval x f - Ex.eval x' f) =
        Ex.eval x e - Ex.eval x f - (Ex.eval x' e - Ex.eval x' f) by ring] at this
  | .mul e f => by
    obtain ⟨h1, h2⟩ := Bd_eval_sub hr hB hE e
    obtain ⟨h3, h4⟩ := Bd_eval_sub hr hB hE f
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_mul]; exact h1.mul hr h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add, Rat.cast_mul]
      have hxf : Bd r (Ex.eval x f) (Ex.majQ B f + Ex.dmajQ B E f) := by
        have := h3.add h4
        rwa [add_sub_cancel] at this
      have := (h2.mul hr hxf).add (h1.mul hr h4)
      rwa [show (Ex.eval x e - Ex.eval x' e) * Ex.eval x f +
          Ex.eval x' e * (Ex.eval x f - Ex.eval x' f) =
          Ex.eval x e * Ex.eval x f - Ex.eval x' e * Ex.eval x' f by ring] at this

/-! ## The truncation part -/

/-- The polynomial `T = 2^S uᴺ vᴹ`. -/
def Tpoly (S N M : ℕ) : P2 := monomial M (monomial N ((2 : ℤ) ^ S))

/-- The polynomial `V = 2v`. -/
def Vpoly : P2 := monomial 1 (monomial 0 2)

/-- `phiK T = T`. -/
theorem phiK_Tpoly (S N M : ℕ) : phiK (Tpoly S N M) = Tc S N M := by
  rw [Tpoly, phiK_monomial, Tc]; push_cast; rfl

/-- `phiK V = V`. -/
theorem phiK_Vpoly : phiK Vpoly = Vc := by
  rw [Vpoly, phiK_monomial, Vc]; push_cast; rfl

/-- `λ` of a sum of weights (same phase): `λ(d + d', e + e', p) = T^{d'} V^{e'} λ(d, e, p)`. -/
theorem lamF_add (S N M d e p d' e' : ℕ) :
    lamF S N M (d + d', e + e', p) = Tc S N M ^ d' * Vc ^ e' * lamF S N M (d, e, p) := by
  simp only [lamF, lamG, pow_add]; ring

/-- `λ(w)` is a unit. -/
theorem lamF_isUnit (S N M : ℕ) (w : ℕ × ℕ × ℕ) : IsUnit (lamF S N M w) := by
  rw [lamF_eq]
  refine ⟨⟨scal S w • mode 0 (ofsW N M w), (scal S w)⁻¹ • mode 0 (-ofsW N M w), ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ (scal_ne_zero S w), mode_mul, add_neg_cancel,
      mode_zero, one_smul]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ (scal_ne_zero S w), mode_mul, neg_add_cancel,
      mode_zero, one_smul]

/-- **The truncation identity.** If every variable polynomial `P i` represents the centre `x i`
(weight `W i`), the tree `e` has weight `(dq + dd, eq + de, p)` and `Q` has weight
`(dq, eq, p)`, then `eval x e − c · ctr (dq, eq, p) Q = ctr (dq + dd, eq + de, p) G` with
`G = evH e − c T^{dd} V^{de} Q`. -/
theorem node_eq {S N M : ℕ} {W : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (W i).2.2 < 4) {P : ℕ → P2}
    {x : ℕ → FA} (hx : ∀ i, x i = ctr S N M (W i) (P i)) {e : Ex} {dq eq p dd de : ℕ}
    (hwt : Ex.wt W e = some (dq + dd, eq + de, p)) (Q : P2) (c : ℤ) :
    Ex.eval x e - (c : ℂ) • ctr S N M (dq, eq, p) Q =
      ctr S N M (dq + dd, eq + de, p)
        (Ex.evH W P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * Q) := by
  have hxh : ∀ i, phiK (P i) = lamG (Tc S N M) Vc (W i) * x i := fun i => by
    rw [hx i]; exact phiK_eq_lam_ctr S N M (W i) (P i)
  have hev := evH_phaseF hW (Tc S N M) Vc hxh e _ hwt
  rw [← Ex.evH_map phiK W P e] at hev
  have hQ := phiK_eq_lam_ctr S N M (dq, eq, p) Q
  have hG := phiK_eq_lam_ctr S N M (dq + dd, eq + de, p)
    (Ex.evH W P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * Q)
  have key : phiK (Ex.evH W P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * Q) =
      lamF S N M (dq + dd, eq + de, p) * (Ex.eval x e - (c : ℂ) • ctr S N M (dq, eq, p) Q) := by
    simp only [map_sub, map_mul, map_pow, phiK_Tpoly, phiK_Vpoly, map_intCast]
    rw [hQ, hev, show lamG (Tc S N M) Vc (dq + dd, eq + de, p) =
      lamF S N M (dq + dd, eq + de, p) from rfl, lamF_add, Algebra.smul_def, map_intCast]
    ring
  rw [hG] at key
  obtain ⟨u, hu⟩ := lamF_isUnit S N M (dq + dd, eq + de, p)
  rw [← hu] at key
  exact (u.isUnit.mul_left_cancel key).symm

/-! ## Steps of a certificate chain -/

/-- All variables of a tree are below `n` (computable). -/
def below (n : ℕ) : Ex → Bool
  | .var i => decide (i < n)
  | .cst _ => true
  | .add e f => below n e && below n f
  | .sub e f => below n e && below n f
  | .mul e f => below n e && below n f

/-- `Bd_eval_sub` using only the variables below `n`. -/
theorem Bd_eval_sub_below {r : ℝ} (hr : 0 ≤ r) {B E : ℕ → ℚ} {x x' : ℕ → FA} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x' i) (B i)) (hE : ∀ i, i < n → Bd r (x i - x' i) (E i)) :
    ∀ e : Ex, below n e = true → Bd r (Ex.eval x' e) (Ex.majQ B e) ∧
      Bd r (Ex.eval x e - Ex.eval x' e) (Ex.dmajQ B E e)
  | .var i, h => by
    have hi : i < n := by simpa [below] using h
    exact ⟨hB i hi, hE i hi⟩
  | .cst k, _ => Bd_eval_sub hr (B := fun _ => 0) (E := fun _ => 0) (x := fun _ => 0)
      (x' := fun _ => 0) (fun _ => by simpa using Bd_zero r) (fun _ => by simpa using Bd_zero r)
      (.cst k)
  | .add e f, h => by
    simp only [below, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := Bd_eval_sub_below hr hB hE e h.1
    obtain ⟨h3, h4⟩ := Bd_eval_sub_below hr hB hE f h.2
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_add]; exact h1.add h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add]
      have := h2.add h4
      rwa [show Ex.eval x e - Ex.eval x' e + (Ex.eval x f - Ex.eval x' f) =
        Ex.eval x e + Ex.eval x f - (Ex.eval x' e + Ex.eval x' f) by ring] at this
  | .sub e f, h => by
    simp only [below, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := Bd_eval_sub_below hr hB hE e h.1
    obtain ⟨h3, h4⟩ := Bd_eval_sub_below hr hB hE f h.2
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_add]; exact h1.sub h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add]
      have := h2.sub h4
      rwa [show Ex.eval x e - Ex.eval x' e - (Ex.eval x f - Ex.eval x' f) =
        Ex.eval x e - Ex.eval x f - (Ex.eval x' e - Ex.eval x' f) by ring] at this
  | .mul e f, h => by
    simp only [below, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := Bd_eval_sub_below hr hB hE e h.1
    obtain ⟨h3, h4⟩ := Bd_eval_sub_below hr hB hE f h.2
    refine ⟨?_, ?_⟩
    · simp only [Ex.eval, Ex.majQ, Rat.cast_mul]; exact h1.mul hr h3
    · simp only [Ex.eval, Ex.dmajQ, Rat.cast_add, Rat.cast_mul]
      have hxf : Bd r (Ex.eval x f) (Ex.majQ B f + Ex.dmajQ B E f) := by
        have := h3.add h4
        rwa [add_sub_cancel] at this
      have := (h2.mul hr hxf).add (h1.mul hr h4)
      rwa [show (Ex.eval x e - Ex.eval x' e) * Ex.eval x f +
          Ex.eval x' e * (Ex.eval x f - Ex.eval x' f) =
          Ex.eval x e * Ex.eval x f - Ex.eval x' e * Ex.eval x' f by ring] at this

/-- **A rounding step of a ball chain**: the new centre `x n` (weight `(1, 0, p)`) of the value
`X n` with `c · X n = eval X e`, from the balls of the variables below `n` and the norm `β` of the
truncation polynomial `G`. -/
theorem node_step {r : ℝ} (hr : 0 ≤ r) {S N M : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4)
    {P : ℕ → P2} {x X : ℕ → FA} (hx : ∀ i, x i = ctr S N M (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i)) {e : Ex}
    (hv : below n e = true) {dd de p : ℕ} (hwt : Ex.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) {c : ℤ} (hc0 : c ≠ 0) (hrel : (c : ℂ) • X n = Ex.eval X e) {β : ℚ}
    (hG : Bd r (ctr S N M (1 + dd, 0 + de, p)
      (Ex.evH Wt P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * P n)) β)
    (hfin : Ex.dmajQ B E e + β ≤ |c| * E n) : Bd r (X n - x n) (E n) := by
  have h1 := (Bd_eval_sub_below hr hB hE e hv).2
  have h2 := node_eq hW hx hwt (P n) c
  rw [← hWn, ← hx n] at h2
  have h3 := h1.add hG
  rw [← h2, show Ex.eval X e - Ex.eval x e + (Ex.eval x e - (c : ℂ) • x n) =
    (c : ℂ) • (X n - x n) by rw [smul_sub, hrel]; ring] at h3
  have h4 := h3.smul ((c : ℂ)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc0), one_smul] at h4
  refine h4.le ?_
  have hc : (0 : ℝ) < |(c : ℝ)| := abs_pos.2 (by exact_mod_cast hc0)
  rw [norm_inv, Complex.norm_intCast, inv_mul_le_iff₀ hc]
  have := (Rat.cast_le (K := ℝ)).2 hfin
  push_cast at this
  linarith

/-- **A norm step of a ball chain** (no new centre): `‖eval X e‖ ≤ dmajQ + β`. -/
theorem norm_step {r : ℝ} (hr : 0 ≤ r) {S N M : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4)
    {P : ℕ → P2} {x X : ℕ → FA} (hx : ∀ i, x i = ctr S N M (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i)) {e : Ex}
    (hv : below n e = true) {w : ℕ × ℕ × ℕ} (hwt : Ex.wt Wt e = some w) {β : ℚ}
    (hG : Bd r (ctr S N M w (Ex.evH Wt P e)) β) :
    Bd r (Ex.eval X e) ((Ex.dmajQ B E e + β : ℚ) : ℝ) := by
  have h1 := (Bd_eval_sub_below hr hB hE e hv).2
  obtain ⟨d, e', p⟩ := w
  have h2 := node_eq (dq := d) (eq := e') (dd := 0) (de := 0) hW hx (by simpa using hwt) 0 0
  simp only [Int.cast_zero, zero_smul, sub_zero, zero_mul, add_zero] at h2
  have h3 := h1.add hG
  rw [← h2, sub_add_cancel] at h3
  simpa using h3

/-- `Bd` of a centre from the kernel data of its polynomial: box, `ℓ¹` bound, Kronecker image and
weighted digit sum (strip `r` with `e^r ≤ 74315/2^16`). -/
theorem Bd_ctr_kron {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M : ℕ}
    {w : ℕ × ℕ × ℕ} {G : P2} {a J W b dc dr Ki Kj K : ℕ} {Nv : ℤ} (hb : 1 ≤ b)
    (hbox : InBox G a J) (ha : a < W) (hW : W ≤ 2 ^ dc) (hJ : J + 1 ≤ 2 ^ dr)
    (hl1 : l1 G < 2 ^ (b - 1)) (hk : kron b W G = Nv)
    (hK : wl1KronP b W dc dr (J + 1) (fun i => kwtS 74315 16 Ki (ndist i (w.1 * N)))
        (fun j => kwtS 74315 16 Kj (ndist j (w.1 * M + w.2.1))) Nv ≤ K) :
    Bd r (ctr S N M w G) (((K : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1) : ℚ) : ℝ) := by
  have := Bd_ctr_of_wl1 (S := S) (N := N) (M := M) (w := w) hb hbox ha hW hJ hl1 hq Ki Kj
    (hk ▸ hK)
  push_cast
  exact this

end LeanTheory.Certificates.KronBall
