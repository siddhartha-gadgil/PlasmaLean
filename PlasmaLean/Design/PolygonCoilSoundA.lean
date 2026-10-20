/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCheck
public import PlasmaLean.Design.PolygonCoilHel

/-!
# Soundness of the polygonal-coil checker, part A: corners

Meaning of the natural-number computations of `Design/PolygonCoilCheck` at one corner:

* `vertN_eq`, `vertStep_sound`: `n = λ²|p - y|²` exactly (`λ = 2³² D`) and, if the checks
  pass, `α ≤ λ|p - y| ≤ α + 2·2⁴⁷`, `λ ≤ 5α`;
* `segClosed_scaled`: the closed-form segment field at `y` in terms of the integer weights
  `W₁ = K P'×V`, `W₂ = K V` and the scaled factor `F = f(|A|, |B|; A·B)·D³ 2¹³⁶`;
* `segStep_f_sound`: the floor value `f` of the checker brackets `F`:
  `f(1 - 7u) ≤ F ≤ f + 1`, `u = 10·2⁴⁷/λ`;
* `fold_segStep`: the accumulators are sums over the segments;
* `cornerEval_sound` (**corner bound**): if a corner passes, then
  `2⁴⁰ ‖Σ_seg segClosed - hel‖ ≤ e` at that corner.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  Set
open scoped RealInnerProductSpace

/-! ## Arithmetic helpers -/

theorem sq_cast (a : ℕ) : ((sq a : ℕ) : ℝ) = (a : ℝ) ^ 2 := by
  simp [sq, pow_two]

theorem nat_sub_cast {a b : ℕ} (h : b ≤ a) : ((Nat.sub a b : ℕ) : ℝ) = a - b := by
  rw [show Nat.sub a b = a - b from rfl, Nat.cast_sub h]

theorem nat_div_le_real (a b : ℕ) : ((Nat.div a b : ℕ) : ℝ) ≤ (a : ℝ) / b :=
  Nat.cast_div_le

theorem real_lt_nat_div_succ (a : ℕ) {b : ℕ} (hb : 0 < b) :
    (a : ℝ) / b < (Nat.div a b : ℕ) + 1 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  have := Nat.lt_div_mul_add (a := a) hb
  have h2 : (a : ℝ) < ((a / b) * b + b : ℕ) := by exact_mod_cast this
  push_cast at h2
  change (a : ℝ) < ((a / b : ℕ) + 1) * b
  nlinarith

theorem cdiv_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℕ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold cdiv
  rw [div_le_iff₀ hb']
  have h := Nat.lt_div_mul_add (a := Nat.add a (Nat.sub b 1)) hb
  have h2 : ((Nat.add a (Nat.sub b 1) : ℕ) : ℝ) < ((Nat.div (Nat.add a (Nat.sub b 1)) b * b + b : ℕ)
    : ℝ) := by exact_mod_cast h
  have e : ((Nat.add a (Nat.sub b 1) : ℕ) : ℝ) = a + (b - 1) := by
    rw [show Nat.add a (Nat.sub b 1) = a + (b - 1) from rfl]; push_cast [Nat.cast_sub hb]; ring
  rw [e] at h2
  push_cast at h2
  change (a : ℝ) ≤ ((a + (b - 1)) / b : ℕ) * b
  have : ((Nat.div (Nat.add a (Nat.sub b 1)) b : ℕ) : ℝ) = ((a + (b - 1)) / b : ℕ) := rfl
  -- from integrality: (a + b - 1) < q b + b and q b ≤ a + b - 1 gives a ≤ q b
  have hq := Nat.div_mul_le_self (a + (b - 1)) b
  have hqa : a ≤ (a + (b - 1)) / b * b := by
    by_contra hc
    push Not at hc
    have h3 : (a + (b - 1)) < (a + (b - 1)) / b * b + b := Nat.lt_div_mul_add hb
    omega
  exact_mod_cast hqa

theorem nmax_ge_left (a b : ℕ) : a ≤ nmax a b := by
  unfold nmax
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; exact h
  · have : Nat.ble a b = false := by
      cases hb : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [this]; exact le_rfl

theorem nmax_ge_right (a b : ℕ) : b ≤ nmax a b := by
  unfold nmax
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; exact le_rfl
  · have : Nat.ble a b = false := by
      cases hb : Nat.ble a b
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [this]; change b ≤ a; omega

theorem fdiv_le_real (x : ℤ) {d : ℕ} (hd : 0 < d) : ((Int.fdiv x d : ℤ) : ℝ) ≤ (x : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd', Int.fdiv_eq_ediv_of_nonneg x (by positivity)]
  have := Int.ediv_mul_le x (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)
  exact_mod_cast this

theorem real_lt_fdiv_succ (x : ℤ) {d : ℕ} (hd : 0 < d) :
    (x : ℝ) / d < ((Int.fdiv x d : ℤ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd', Int.fdiv_eq_ediv_of_nonneg x (by positivity)]
  have := Int.lt_ediv_add_one_mul_self x (by exact_mod_cast hd : (0 : ℤ) < d)
  exact_mod_cast this

theorem toNat_cast_real {z : ℤ} (h : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
  exact_mod_cast this

/-- `‖v‖² = v₀² + v₁² + v₂²`. -/
theorem norm_sq_coords (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq_abs]

/-! ## Points and corners -/

/-- The scale `2³²` as a real number. -/
@[expose] def S32 : ℝ := 4294967296

theorem S32_pos : 0 < S32 := by norm_num [S32]

theorem two32_cast : ((two32 : ℕ) : ℝ) = S32 := by norm_num [two32, S32]

/-- The real point of an integer triple (scale `2⁻³²`). -/
@[expose] def ptR (p : ℤ × ℤ × ℤ) : Space :=
  WithLp.toLp 2 ![(p.1 : ℝ) / S32, (p.2.1 : ℝ) / S32, (p.2.2 : ℝ) / S32]

/-- The real corner `((Xt - 4D)/D, (Yt - 4D)/D, (Zt - 4D)/D)` of translated numerators. -/
@[expose] def cornerR (Xt Yt Zt D : ℕ) : Space :=
  WithLp.toLp 2 ![((Xt : ℝ) - 4 * D) / D, ((Yt : ℝ) - 4 * D) / D, ((Zt : ℝ) - 4 * D) / D]

/-- The corner data used by `cornerEval`. -/
@[expose] def mkCD (Xt Yt Zt D : ℕ) : CD :=
  ⟨D, Nat.mul D D, Nat.mul Xt two32, Nat.mul Yt two32, Nat.mul Zt two32,
   Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32))) (sq (Nat.mul Zt two32)),
   Nat.mul D two32⟩

/-- Translated coordinates are nonnegative. -/
@[expose] def trOK (p : ℤ × ℤ × ℤ) : Prop := 0 ≤ tr p.1 ∧ 0 ≤ tr p.2.1 ∧ 0 ≤ tr p.2.2

/-- The scaled difference `λ(p - y)` in integer coordinates: `D P' - 2³² X'`. -/
theorem scaled_diff (Xt Yt Zt D : ℕ) (hD : 0 < D) (p : ℤ × ℤ × ℤ) :
    ((D : ℝ) * S32) ^ 2 * ‖ptR p - cornerR Xt Yt Zt D‖ ^ 2 =
      ((D : ℝ) * (tr p.1 : ℝ) - S32 * Xt) ^ 2 + ((D : ℝ) * (tr p.2.1 : ℝ) - S32 * Yt) ^ 2 +
        ((D : ℝ) * (tr p.2.2 : ℝ) - S32 * Zt) ^ 2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [norm_sq_coords]
  simp only [ptR, cornerR, PiLp.sub_apply, tr]
  simp
  have hS := S32_pos
  field_simp
  simp only [S32]
  ring

/-- **The vertex distance** `n = λ²|p - y|²` (exactly). -/
theorem vertN_eq (Xt Yt Zt D : ℕ) (hD : 0 < D) {p : ℤ × ℤ × ℤ} (hp : trOK p) :
    ((vertN (mkCD Xt Yt Zt D) (mkVt p) : ℕ) : ℝ) =
      ((D : ℝ) * S32) ^ 2 * ‖ptR p - cornerR Xt Yt Zt D‖ ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := hp
  rw [scaled_diff Xt Yt Zt D hD p]
  have hpx := toNat_cast_real h1
  have hpy := toNat_cast_real h2
  have hpz := toNat_cast_real h3
  have hpp : (((tr p.1 * tr p.1 + tr p.2.1 * tr p.2.1 + tr p.2.2 * tr p.2.2).toNat : ℕ) : ℝ) =
      (tr p.1 : ℝ) ^ 2 + (tr p.2.1 : ℝ) ^ 2 + (tr p.2.2 : ℝ) ^ 2 := by
    rw [toNat_cast_real (by positivity)]; push_cast; ring
  unfold vertN mkCD mkVt
  simp only
  set a := Nat.add (Nat.mul (Nat.mul D D) (tr p.1 * tr p.1 + tr p.2.1 * tr p.2.1 +
    tr p.2.2 * tr p.2.2).toNat) (Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32)))
      (sq (Nat.mul Zt two32)))
  set b := Nat.mul (Nat.mul 2 D) (Nat.add (Nat.add (Nat.mul (tr p.1).toNat (Nat.mul Xt two32))
    (Nat.mul (tr p.2.1).toNat (Nat.mul Yt two32))) (Nat.mul (tr p.2.2).toNat (Nat.mul Zt two32)))
  have ha : (a : ℝ) = (D : ℝ) ^ 2 * ((tr p.1 : ℝ) ^ 2 + (tr p.2.1 : ℝ) ^ 2 + (tr p.2.2 : ℝ) ^ 2) +
      ((Xt : ℝ) * S32) ^ 2 + ((Yt : ℝ) * S32) ^ 2 + ((Zt : ℝ) * S32) ^ 2 := by
    simp only [a, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, sq_cast, hpp, two32_cast]
    ring
  have hb : (b : ℝ) = 2 * D * ((tr p.1 : ℝ) * (Xt * S32) + (tr p.2.1 : ℝ) * (Yt * S32) +
      (tr p.2.2 : ℝ) * (Zt * S32)) := by
    simp only [b, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, hpx, hpy, hpz, two32_cast]
    push_cast; ring
  have hle : b ≤ a := by
    have : (b : ℝ) ≤ a := by
      rw [ha, hb]
      nlinarith [sq_nonneg ((D : ℝ) * (tr p.1 : ℝ) - S32 * Xt),
        sq_nonneg ((D : ℝ) * (tr p.2.1 : ℝ) - S32 * Yt),
        sq_nonneg ((D : ℝ) * (tr p.2.2 : ℝ) - S32 * Zt)]
    exact_mod_cast this
  rw [nat_sub_cast hle, ha, hb]
  ring

/-- Validity of a vertex result for vertex `p` at the corner: exact `n`, and the bracket facts
when the checks pass. -/
@[expose] def VRok (Xt Yt Zt D : ℕ) (p : ℤ × ℤ × ℤ) (v : VR) : Prop :=
  (v.n : ℝ) = ((D : ℝ) * S32) ^ 2 * ‖ptR p - cornerR Xt Yt Zt D‖ ^ 2 ∧
  (v.ok = true → (v.al : ℝ) ≤ (D : ℝ) * S32 * ‖ptR p - cornerR Xt Yt Zt D‖ ∧
    (D : ℝ) * S32 * ‖ptR p - cornerR Xt Yt Zt D‖ ≤ v.al + 2 * KT ∧
    (D : ℝ) * S32 ≤ 5 * v.al)

/-- **The vertex step is sound** (for any Newton start value). -/
theorem vertStep_sound (Xt Yt Zt D : ℕ) (hD : 0 < D) {p : ℤ × ℤ × ℤ} (hp : trOK p) (g : ℕ) :
    VRok Xt Yt Zt D p (vertStep (mkCD Xt Yt Zt D) (mkVt p) g) := by
  have hn := vertN_eq Xt Yt Zt D hD hp
  refine ⟨hn, fun hok => ?_⟩
  have hlam : ((mkCD Xt Yt Zt D).lam : ℝ) = D * S32 := by
    simp only [mkCD, Nat.mul_eq]; push_cast [two32_cast]; ring
  simp only [vertStep, Bool.and_eq_true, Nat.ble_eq] at hok ⊢
  rw [← hlam]
  generalize (mkCD Xt Yt Zt D).lam = lam at hok hlam ⊢
  generalize vertN (mkCD Xt Yt Zt D) (mkVt p) = n at hn hok ⊢
  generalize nst n (nst n (nst n g)) = r at hok ⊢
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq, sq] at hok ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  set d := ‖ptR p - cornerR Xt Yt Zt D‖
  have hlam_pos : (0 : ℝ) < D * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hd0 : 0 ≤ d := norm_nonneg _
  have hKr : KT ≤ r := by
    by_contra hc
    push Not at hc
    have : r - KT = 0 := Nat.sub_eq_zero_of_le hc.le
    rw [this] at h1
    have : (lam : ℝ) ≤ 0 := by exact_mod_cast (by simpa using h1)
    linarith
  have hsub : ((r - KT : ℕ) : ℝ) = r - KT := by rw [Nat.cast_sub hKr]
  have hn' : (n : ℝ) = (lam * d) ^ 2 := by rw [hn, hlam]; ring
  have h1' : (lam : ℝ) ≤ 5 * ((r - KT : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : ((r - KT : ℕ) : ℝ) * ((r - KT : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
  have h3' : (n : ℝ) ≤ ((r : ℝ) + KT) * ((r : ℝ) + KT) := by exact_mod_cast h3
  have hlam' : (0 : ℝ) < lam := by rw [hlam]; exact hlam_pos
  refine ⟨?_, ?_, h1'⟩
  · rw [hn'] at h2'
    have hα0 : (0 : ℝ) ≤ ((r - KT : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (((r - KT : ℕ) : ℝ) - lam * d), mul_nonneg hlam'.le hd0]
  · rw [hn'] at h3'
    rw [hsub]
    have hr0 : (0 : ℝ) ≤ r + KT := add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg (lam * d - (r + KT)), mul_nonneg hlam'.le hd0]

/-! ## The closed form at a corner, in integer weights -/

/-- The real vector of an integer triple (no scaling). -/
@[expose] def vecZ (x y z : ℤ) : Space := WithLp.toLp 2 ![(x : ℝ), (y : ℝ), (z : ℝ)]

/-- Scaled differences: `λ(ptR P - y) = D P' - 2³² X'`. -/
theorem lam_sub (Xt Yt Zt D : ℕ) (hD : 0 < D) (P : ℤ × ℤ × ℤ) :
    ((D : ℝ) * S32) • (ptR P - cornerR Xt Yt Zt D) =
      (D : ℝ) • vecZ (tr P.1) (tr P.2.1) (tr P.2.2) - S32 • vecZ Xt Yt Zt := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hS : S32 ≠ 0 := S32_pos.ne'
  ext i; fin_cases i <;> simp [ptR, cornerR, vecZ, tr, S32] <;> field_simp <;> ring

/-- Homogeneity of the factor: `f(α, β, c) = λ³ f(λα, λβ, λ²c)`. -/
theorem segFac'_scale {lam : ℝ} (hl : 0 < lam) (α β c : ℝ) :
    segFac' α β c = lam ^ 3 * segFac' (lam * α) (lam * β) (lam ^ 2 * c) := by
  unfold segFac'
  by_cases h : α * β * (α * β + c) = 0
  · have h' : lam * α * (lam * β) * (lam * α * (lam * β) + lam ^ 2 * c) = 0 := by
      have : lam * α * (lam * β) * (lam * α * (lam * β) + lam ^ 2 * c) =
          lam ^ 4 * (α * β * (α * β + c)) := by ring
      rw [this, h, mul_zero]
    rw [h, h', div_zero, div_zero, mul_zero]
  · have h' : lam * α * (lam * β) * (lam * α * (lam * β) + lam ^ 2 * c) ≠ 0 := by
      have : lam * α * (lam * β) * (lam * α * (lam * β) + lam ^ 2 * c) =
          lam ^ 4 * (α * β * (α * β + c)) := by ring
      rw [this]; exact mul_ne_zero (by positivity) h
    field_simp

/-- **The closed-form segment field at a corner** in terms of the integer weights
`W₁ = K P'×V`, `W₂ = K V` and the scaled factor `f(|A|, |B|; A·B)`, `A = λ(p - y)`. -/
theorem segClosed_scaled (Xt Yt Zt D : ℕ) (hD : 0 < D) (K : ℤ) (P Q : ℤ × ℤ × ℤ) :
    segClosed ((K : ℝ) / S32) (ptR P) (ptR Q) (cornerR Xt Yt Zt D) =
      ((D : ℝ) ^ 2 * segFac' (‖((D : ℝ) * S32) • (ptR P - cornerR Xt Yt Zt D)‖)
        (‖((D : ℝ) * S32) • (ptR Q - cornerR Xt Yt Zt D)‖)
        ⟪((D : ℝ) * S32) • (ptR P - cornerR Xt Yt Zt D),
          ((D : ℝ) * S32) • (ptR Q - cornerR Xt Yt Zt D)⟫) •
      ((D : ℝ) • ((K : ℝ) • cross (vecZ (tr P.1) (tr P.2.1) (tr P.2.2))
          (vecZ (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2))) -
        S32 • cross (vecZ Xt Yt Zt) ((K : ℝ) • vecZ (Q.1 - P.1) (Q.2.1 - P.2.1) (Q.2.2 - P.2.2)))
            := by
  set lam := (D : ℝ) * S32 with hlam
  have hl : 0 < lam := mul_pos (by exact_mod_cast hD) S32_pos
  set a := ptR P - cornerR Xt Yt Zt D
  set b := ptR Q - cornerR Xt Yt Zt D
  rw [norm_smul, norm_smul, inner_smul_left, inner_smul_right, Real.norm_eq_abs, abs_of_pos hl]
  simp only [conj_trivial]
  have hf := segFac'_scale hl ‖a‖ ‖b‖ ⟪a, b⟫
  rw [show lam * (lam * ⟪a, b⟫) = lam ^ 2 * ⟪a, b⟫ by ring] 
  unfold segClosed
  rw [hf]
  set F := segFac' (lam * ‖a‖) (lam * ‖b‖) (lam ^ 2 * ⟪a, b⟫)
  -- cross products in integer coordinates
  have hA := lam_sub Xt Yt Zt D hD P
  have hB := lam_sub Xt Yt Zt D hD Q
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hS : S32 ≠ 0 := S32_pos.ne'
  have hlam0 : lam ≠ 0 := hl.ne'
  have ea : ptR P - cornerR Xt Yt Zt D =
      lam⁻¹ • ((D : ℝ) • vecZ (tr P.1) (tr P.2.1) (tr P.2.2) - S32 • vecZ Xt Yt Zt) := by
    rw [← hA, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have eb : ptR Q - cornerR Xt Yt Zt D =
      lam⁻¹ • ((D : ℝ) • vecZ (tr Q.1) (tr Q.2.1) (tr Q.2.2) - S32 • vecZ Xt Yt Zt) := by
    rw [← hB, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  rw [ea, eb]
  ext i; fin_cases i <;>
    simp [cross, crossProduct, vecZ, tr, smul_eq_mul, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp <;> simp only [hlam, S32] <;> ring

/-! ## The kernel factor of one segment -/

/-- `B - A = D (Q - P)` in integer coordinates, so `|B - A|² = D²|V|²`. -/
theorem lam_diff_norm (Xt Yt Zt D : ℕ) (hD : 0 < D) (P Q : ℤ × ℤ × ℤ) :
    ‖((D : ℝ) * S32) • (ptR Q - cornerR Xt Yt Zt D) - ((D : ℝ) * S32) • (ptR P - cornerR Xt Yt Zt
        D)‖ ^ 2
      = (D : ℝ) ^ 2 * (((Q.1 - P.1 : ℤ) : ℝ) ^ 2 + ((Q.2.1 - P.2.1 : ℤ) : ℝ) ^ 2 +
        ((Q.2.2 - P.2.2 : ℤ) : ℝ) ^ 2) := by
  rw [norm_sq_coords]
  simp [ptR, cornerR]
  have hS := S32_pos.ne'
  field_simp
  ring

/-- **The floor value of the checker brackets the exact scaled kernel factor.**
With `A = λ(p - y)`, `B = λ(q - y)` and `F = f(|A|, |B|; A·B)·D³ 2¹³⁶`:
`F ≤ f + 1` and `(1 - 7u) f ≤ F` for `u = 10·2⁴⁷/λ`. -/
theorem segFactor_sound (Xt Yt Zt D : ℕ) (hD : 0 < D) {P Q : ℤ × ℤ × ℤ} {a b : VR}
    (ha : VRok Xt Yt Zt D P a) (hb : VRok Xt Yt Zt D Q b) (hoka : a.ok = true)
    (hokb : b.ok = true) (hlam : 1000 * KT ≤ D * two32) {vv : ℕ}
    (hvv : (vv : ℝ) = ((Q.1 - P.1 : ℤ) : ℝ) ^ 2 + ((Q.2.1 - P.2.1 : ℤ) : ℝ) ^ 2 +
      ((Q.2.2 - P.2.2 : ℤ) : ℝ) ^ 2)
    (hc : D * D * vv ≤ a.al * b.al + (a.n + b.n)) :
    let f := Nat.div (2 * (a.al + b.al) * (D * D * D * two136))
      (a.al * b.al * (a.al * b.al + a.al * b.al + (a.n + b.n) - D * D * vv))
    let A := ((D : ℝ) * S32) • (ptR P - cornerR Xt Yt Zt D)
    let B := ((D : ℝ) * S32) • (ptR Q - cornerR Xt Yt Zt D)
    let F := segFac' ‖A‖ ‖B‖ ⟪A, B⟫ * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ))
    F ≤ f + 1 ∧ (1 - 7 * (10 * KT / ((D : ℝ) * S32))) * f ≤ F := by
  intro f A B F
  have hlamR : (0 : ℝ) < D * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  obtain ⟨hna, hbra⟩ := ha
  obtain ⟨hnb, hbrb⟩ := hb
  obtain ⟨a1, a2, a3⟩ := hbra hoka
  obtain ⟨b1, b2, b3⟩ := hbrb hokb
  have hnA : ‖A‖ = (D : ℝ) * S32 * ‖ptR P - cornerR Xt Yt Zt D‖ := by
    simp only [A]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlamR]
  have hnB : ‖B‖ = (D : ℝ) * S32 * ‖ptR Q - cornerR Xt Yt Zt D‖ := by
    simp only [B]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlamR]
  set α : ℝ := (a.al : ℝ)
  set β : ℝ := (b.al : ℝ)
  have hα : 0 < α := by
    have : (0 : ℝ) < D * S32 := hlamR; linarith
  have hβ : 0 < β := by linarith
  -- inner product from the polarisation identity
  have hAB : ⟪A, B⟫ = ((a.n : ℝ) + b.n - (D : ℝ) ^ 2 * vv) / 2 := by
    have h1 := lam_diff_norm Xt Yt Zt D hD P Q
    rw [← hvv] at h1
    have h2 : ‖B - A‖ ^ 2 = ‖B‖ ^ 2 - 2 * ⟪A, B⟫ + ‖A‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm]
    have hA2 : ‖A‖ ^ 2 = a.n := by rw [hnA, hna]; ring
    have hB2 : ‖B‖ ^ 2 = b.n := by rw [hnB, hnb]; ring
    simp only [A, B] at h2 hA2 hB2 ⊢
    linarith
  set c := ⟪A, B⟫
  have hc' : (D : ℝ) ^ 2 * vv ≤ α * β + ((a.n : ℝ) + b.n) := by
    have : ((D * D * vv : ℕ) : ℝ) ≤ ((a.al * b.al + (a.n + b.n) : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this; nlinarith
  have hc2 : 0 ≤ α * β + 2 * c := by rw [hAB]; linarith
  have hcpos : 0 < α * β + c := by nlinarith [mul_pos hα hβ]
  -- the checker's denominator and numerator
  have hden_nat : D * D * vv ≤ a.al * b.al + a.al * b.al + (a.n + b.n) := by
    nlinarith [Nat.zero_le (a.al * b.al)]
  have hden : ((a.al * b.al * (a.al * b.al + a.al * b.al + (a.n + b.n) - D * D * vv) : ℕ) : ℝ) =
      α * β * (2 * α * β + 2 * c) := by
    rw [Nat.cast_mul, Nat.cast_sub hden_nat, hAB]; push_cast; ring
  have hden_pos : (0 : ℝ) < α * β * (2 * α * β + 2 * c) :=
    mul_pos (mul_pos hα hβ) (by linarith)
  have hnum : ((2 * (a.al + b.al) * (D * D * D * two136) : ℕ) : ℝ) =
      2 * (α + β) * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) := by push_cast; ring
  have hD3 : (0 : ℝ) < (D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((two136 : ℕ) : ℝ) := by norm_num [two136]
    positivity
  have hfhi : segFac' α β c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) =
      ((2 * (a.al + b.al) * (D * D * D * two136) : ℕ) : ℝ) /
        ((a.al * b.al * (a.al * b.al + a.al * b.al + (a.n + b.n) - D * D * vv) : ℕ) : ℝ) := by
    rw [hnum, hden]; unfold segFac'; field_simp
  have hdenN : 0 < a.al * b.al * (a.al * b.al + a.al * b.al + (a.n + b.n) - D * D * vv) := by
    exact_mod_cast hden.symm ▸ hden_pos
  have hf_le : (f : ℝ) ≤ segFac' α β c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) := by
    rw [hfhi]; exact nat_div_le_real _ _
  have hf_gt : segFac' α β c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) < f + 1 := by
    rw [hfhi]; exact real_lt_nat_div_succ _ hdenN
  -- monotonicity and relative change
  have hmono : segFac' ‖A‖ ‖B‖ c ≤ segFac' α β c :=
    segFac'_mono hα hβ (by rw [hnA]; exact a1) (by rw [hnB]; exact b1) hcpos
  set u := 10 * (KT : ℝ) / ((D : ℝ) * S32)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 100 := by
    have : (1000 * KT : ℝ) ≤ D * S32 := by
      have := (by exact_mod_cast hlam : ((1000 * KT : ℕ) : ℝ) ≤ ((D * two32 : ℕ) : ℝ))
      push_cast [two32_cast] at this; linarith
    simp only [u]; rw [div_le_iff₀ hlamR]; linarith
  have hKT0 : (0 : ℝ) ≤ (KT : ℝ) := Nat.cast_nonneg _
  have hαu : ‖A‖ ≤ α * (1 + u) := by
    rw [hnA]
    have : 2 * (KT : ℝ) ≤ α * u := by
      have e : α * u = 10 * (KT : ℝ) * (α / ((D : ℝ) * S32)) := by simp only [u]; ring
      have h5 : 1 / 5 ≤ α / ((D : ℝ) * S32) := by
        rw [le_div_iff₀ hlamR]; linarith
      rw [e]
      have := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 10 * (KT : ℝ))
      linarith
    linarith
  have hβu : ‖B‖ ≤ β * (1 + u) := by
    rw [hnB]
    have : 2 * (KT : ℝ) ≤ β * u := by
      have e : β * u = 10 * (KT : ℝ) * (β / ((D : ℝ) * S32)) := by simp only [u]; ring
      have h5 : 1 / 5 ≤ β / ((D : ℝ) * S32) := by
        rw [le_div_iff₀ hlamR]; linarith
      rw [e]
      have := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 10 * (KT : ℝ))
      linarith
    linarith
  have hratio := segFac'_ratio hα hβ (by rw [hnA]; exact a1) (by rw [hnB]; exact b1) hαu hβu hu0 hu1
    hc2
  constructor
  · calc F = segFac' ‖A‖ ‖B‖ c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) := rfl
      _ ≤ segFac' α β c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hmono hD3.le
      _ ≤ f + 1 := hf_gt.le
  · have h7 : 0 ≤ 1 - 7 * u := by linarith
    calc (1 - 7 * u) * f ≤ (1 - 7 * u) * (segFac' α β c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hf_le h7
      _ = ((1 - 7 * u) * segFac' α β c) * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) := by ring
      _ ≤ segFac' ‖A‖ ‖B‖ c * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hratio hD3.le

/-! ## The segment walk as a fold -/

/-- The kernel factor computed by `segStep`. -/
@[expose] def segF (D2 D3S : ℕ) (s : Seg) (a b : VR) : ℕ :=
  Nat.div (Nat.mul (Nat.mul 2 (Nat.add a.al b.al)) D3S)
    (Nat.mul (Nat.mul a.al b.al) (Nat.sub (Nat.add (Nat.add (Nat.mul a.al b.al) (Nat.mul a.al b.al))
      (Nat.add a.n b.n)) (Nat.mul D2 s.vv)))

/-- The remainder data computed by `segStep`. -/
@[expose] def segRT (D2 : ℕ) (r : RC) (s : Seg) (a b : VR) : ℕ × Bool :=
  cond r.doRem (remTerm r a.n b.n (Nat.mul D2 s.vv) s.kv) (0, true)

/-- The checks of `segStep`. -/
@[expose] def segChk (D2 : ℕ) (r : RC) (s : Seg) (a b : VR) : Bool :=
  ((a.ok && b.ok) && Nat.ble (Nat.mul D2 s.vv) (Nat.add (Nat.mul a.al b.al) (Nat.add a.n b.n))) &&
    (segRT D2 r s a b).2

/-- `segStep` adds the contributions of one segment. -/
theorem segStep_eq (D2 D3S : ℕ) (r : RC) (acc : Acc) (s : Seg) (a b : VR) :
    segStep D2 D3S r acc s a b =
      ⟨acc.sx + segF D2 D3S s a b * s.w1x, acc.sy + segF D2 D3S s a b * s.w1y,
       acc.sz + segF D2 D3S s a b * s.w1z, acc.tx + segF D2 D3S s a b * s.w2x,
       acc.ty + segF D2 D3S s a b * s.w2y, acc.tz + segF D2 D3S s a b * s.w2z,
       acc.sf + segF D2 D3S s a b, acc.rem + (segRT D2 r s a b).1,
       acc.ok && segChk D2 r s a b⟩ := by
  simp only [segStep, segF, segRT, segChk, Bool.and_assoc]
  rfl

/-- The fold of `segStep` over a list of segment triples. -/
@[expose] def walkL (D2 D3S : ℕ) (r : RC) (L : List (Seg × VR × VR)) (acc : Acc) : Acc :=
  L.foldl (fun a x => segStep D2 D3S r a x.1 x.2.1 x.2.2) acc

/-- Folding `segStep` over a list of segment triples. -/
theorem fold_segStep (D2 D3S : ℕ) (r : RC) (L : List (Seg × VR × VR)) (acc : Acc) :
    (walkL D2 D3S r L acc).sx = acc.sx + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w1x).sum
        ∧
    (walkL D2 D3S r L acc).sy = acc.sy + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w1y).sum
        ∧
    (walkL D2 D3S r L acc).sz = acc.sz + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w1z).sum
        ∧
    (walkL D2 D3S r L acc).tx = acc.tx + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w2x).sum
        ∧
    (walkL D2 D3S r L acc).ty = acc.ty + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w2y).sum
        ∧
    (walkL D2 D3S r L acc).tz = acc.tz + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2 * x.1.w2z).sum
        ∧
    (walkL D2 D3S r L acc).sf = acc.sf + (L.map fun x => segF D2 D3S x.1 x.2.1 x.2.2).sum ∧
    (walkL D2 D3S r L acc).rem = acc.rem + (L.map fun x => (segRT D2 r x.1 x.2.1 x.2.2).1).sum ∧
    ((walkL D2 D3S r L acc).ok = true →
      acc.ok = true ∧ ∀ x ∈ L, segChk D2 r x.1 x.2.1 x.2.2 = true) := by
  induction L generalizing acc with
  | nil => simp [walkL]
  | cons x L ih =>
    have e : walkL D2 D3S r (x :: L) acc = walkL D2 D3S r L (segStep D2 D3S r acc x.1 x.2.1 x.2.2)
        :=
      rfl
    rw [e]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ih (segStep D2 D3S r acc x.1 x.2.1 x.2.2)
    rw [segStep_eq] at h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
    simp only [List.map_cons, List.sum_cons]
    refine ⟨by rw [h1]; dsimp only; ring, by rw [h2]; dsimp only; ring,
      by rw [h3]; dsimp only; ring,
      by rw [h4]; dsimp only; ring, by rw [h5]; dsimp only; ring, by rw [h6]; dsimp only; ring,
      by rw [h7]; dsimp only; ring, by rw [h8]; dsimp only; ring, fun hok => ?_⟩
    obtain ⟨hacc, hall⟩ := h9 hok
    dsimp only at hacc
    simp only [Bool.and_eq_true] at hacc
    refine ⟨hacc.1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hacc.2
    · exact hall y hy

/-- `filWalkAux` is a fold over consecutive pairs (closing with `first`). -/
theorem filWalkAux_eq (D2 D3S : ℕ) (r : RC) (first : VR) :
    ∀ (ss : List Seg) (vs : List VR) (acc : Acc), ss.length = vs.length → 0 < vs.length →
      filWalkAux D2 D3S r first acc ss vs =
        walkL D2 D3S r (List.zip ss (List.zip vs (vs.tail ++ [first]))) acc
  | [], vs, acc, h, hp => by simp at h; omega
  | [s], [v], acc, _, _ => by simp [filWalkAux, walkL]
  | [s], [], acc, h, _ => by simp at h
  | [s], _ :: _ :: _, acc, h, _ => by simp at h
  | s :: s' :: ss, [], acc, h, _ => by simp at h
  | s :: s' :: ss, [v], acc, h, _ => by simp at h
  | s :: s' :: ss, v :: v' :: vs, acc, h, _ => by
    simp only [filWalkAux]
    rw [filWalkAux_eq D2 D3S r first (s' :: ss) (v' :: vs) _ (by simpa using h) (by simp)]
    simp [walkL]

/-- `filWalk` is a fold over the pairs `(vs[i], vs[i+1 mod n])`. -/
theorem filWalk_eq (D2 D3S : ℕ) (r : RC) (acc : Acc) (ss : List Seg) (vs : List VR)
    (h : ss.length = vs.length) (hp : 0 < vs.length) :
    filWalk D2 D3S r acc ss vs = walkL D2 D3S r (List.zip ss (List.zip vs (rot1 vs))) acc := by
  match vs, hp with
  | v :: vs', _ =>
    simp only [filWalk, rot1]
    exact filWalkAux_eq D2 D3S r v ss (v :: vs') acc h (by simp)

/-! ## The structure of the walk over all filaments -/

/-- `rot1` preserves length. -/
theorem rot1_length {α : Type} (l : List α) : (rot1 l).length = l.length := by
  cases l <;> simp [rot1]

/-- `filVerts` produces one result per vertex. -/
theorem filVerts_length (c : CD) : ∀ (vs : List Vt) (gs : List ℕ), (filVerts c vs gs).length =
    vs.length
  | [], _ => rfl
  | v :: vs, g :: gs => by simp [filVerts, filVerts_length c vs gs]
  | v :: vs, [] => by simp [filVerts, filVerts_length c vs []]

/-- Every vertex result of `filVerts` on `xs.map mkVt` is valid for its vertex. -/
theorem filVerts_sound (Xt Yt Zt D : ℕ) (hD : 0 < D) :
    ∀ (xs : List (ℤ × ℤ × ℤ)) (gs : List ℕ), (∀ p ∈ xs, trOK p) →
      ∀ z ∈ List.zip xs (filVerts (mkCD Xt Yt Zt D) (xs.map mkVt) gs), VRok Xt Yt Zt D z.1 z.2
  | [], _, _ => by simp [filVerts]
  | p :: xs, g :: gs, h => by
    intro z hz
    simp only [List.map_cons, filVerts, List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact vertStep_sound Xt Yt Zt D hD (h p (by simp)) g
    · exact filVerts_sound Xt Yt Zt D hD xs gs (fun q hq => h q (by simp [hq])) z hz
  | p :: xs, [], h => by
    intro z hz
    simp only [List.map_cons, filVerts, List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact vertStep_sound Xt Yt Zt D hD (h p (by simp)) _
    · exact filVerts_sound Xt Yt Zt D hD xs [] (fun q hq => h q (by simp [hq])) z hz

/-- Membership in a zip of rotated lists. -/
theorem mem_zip_rot1 {α β : Type} {xs : List α} {ys : List β} (h : xs.length = ys.length) {z : α ×
    β}
    (hz : z ∈ List.zip (rot1 xs) (rot1 ys)) : z ∈ List.zip xs ys := by
  cases xs with
  | nil => simp [rot1] at hz
  | cons x xs =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [rot1] at hz
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zip_append (by simp [h])] at hz
      simp only [List.mem_append, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact List.mem_cons_of_mem _ hz
      · simp

/-- The semantic record of one segment at a corner: current, endpoints, vertex results. -/
abbrev SRec := ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × VR × VR

/-- The checker triple of a semantic record. -/
@[expose] def srTriple (o : Offs) (z : SRec) : Seg × VR × VR := (mkSeg o z.1 z.2.1 z.2.2.1, z.2.2.2)

/-- The semantic records of one filament walk. -/
@[expose] def filRecs (K : ℤ) (xs : List (ℤ × ℤ × ℤ)) (vs : List VR) : List SRec :=
  (List.zip (List.zip xs (rot1 xs)) (List.zip vs (rot1 vs))).map fun w => (K, w.1.1, w.1.2, w.2.1,
      w.2.2)

/-- The walk list of a filament is the map of its semantic records. -/
theorem filWalk_list (o : Offs) (K : ℤ) (xs : List (ℤ × ℤ × ℤ)) (vs : List VR) :
    List.zip (mkFil o K xs).sgs (List.zip vs (rot1 vs)) = (filRecs K xs vs).map (srTriple o) := by
  simp only [mkFil, filRecs, List.map_map]
  rw [List.zip_map_left]
  simp [Function.comp, srTriple]

/-- The segments of a semantic record list are the polygon segments. -/
theorem filRecs_segs (K : ℤ) (xs : List (ℤ × ℤ × ℤ)) (vs : List VR) (h : vs.length = xs.length) :
    (filRecs K xs vs).map (fun z => (z.1, z.2.1, z.2.2.1)) =
      (List.zip xs (rot1 xs)).map (fun pq => (K, pq.1, pq.2)) := by
  simp only [filRecs, List.map_map]
  have hl : (List.zip xs (rot1 xs)).length ≤ (List.zip vs (rot1 vs)).length := by
    simp [rot1_length, h]
  rw [show ((fun z : SRec => (z.1, z.2.1, z.2.2.1)) ∘ fun w : ((ℤ × ℤ × ℤ) × ℤ × ℤ × ℤ) × VR × VR =>
      ((K, w.1.1, w.1.2, w.2.1, w.2.2) : SRec)) = (fun pq => (K, pq.1, pq.2)) ∘ Prod.fst from rfl,
    ← List.map_map, List.map_fst_zip hl]

/-- Pairing in a zip of zips. -/
theorem mem_zip_zip {α β γ δ : Type} {A : List α} {A' : List β} {B : List γ} {B' : List δ}
    {w : (α × β) × γ × δ} (hw : w ∈ List.zip (List.zip A A') (List.zip B B')) :
    (w.1.1, w.2.1) ∈ List.zip A B ∧ (w.1.2, w.2.2) ∈ List.zip A' B' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
  simp only [List.length_zip] at hi
  have h1 : i < A.length := by omega
  have h2 : i < A'.length := by omega
  have h3 : i < B.length := by omega
  have h4 : i < B'.length := by omega
  simp only [List.getElem_zip]
  constructor
  · exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp [List.getElem_zip]⟩
  · exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp [List.getElem_zip]⟩

/-- Membership of segment endpoints. -/
theorem mem_zip_rot_pair {α β : Type} {xs : List α} {ys : List β} {w : (α × α) × β × β}
    (h : xs.length = ys.length)
    (hw : w ∈ List.zip (List.zip xs (rot1 xs)) (List.zip ys (rot1 ys))) :
    (w.1.1, w.2.1) ∈ List.zip xs ys ∧ (w.1.2, w.2.2) ∈ List.zip xs ys ∧
      (w.1.1, w.1.2) ∈ List.zip xs (rot1 xs) := by
  obtain ⟨h1, h2⟩ := mem_zip_zip hw
  refine ⟨h1, mem_zip_rot1 h h2, ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
  simp only [List.length_zip] at hi
  exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp [List.getElem_zip]⟩

/-- Validity of the records of one filament walk. -/
theorem filRecs_sound (Xt Yt Zt D : ℕ) {K : ℤ} {xs : List (ℤ × ℤ × ℤ)} {vs : List VR}
    (hl : xs.length = vs.length) (hv : ∀ w ∈ List.zip xs vs, VRok Xt Yt Zt D w.1 w.2) :
    ∀ z ∈ filRecs K xs vs, VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
      (z.2.1, z.2.2.1) ∈ List.zip xs (rot1 xs) ∧ z.1 = K := by
  intro z hz
  simp only [filRecs, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨h1, h2, h3⟩ := mem_zip_rot_pair hl hw
  exact ⟨hv _ h1, hv _ h2, h3, rfl⟩

/-- `allVerts` produces one list per filament. -/
theorem allVerts_length (c : CD) : ∀ (fs : List Fil) (gs : List (List ℕ)),
    (allVerts c fs gs).length = fs.length
  | [], _ => rfl
  | f :: fs, g :: gs => by simp [allVerts, allVerts_length c fs gs]
  | f :: fs, [] => by simp [allVerts, allVerts_length c fs []]

/-- The whole corner walk as one fold over semantic records. -/
@[expose] def allRecs (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (vss : List (List VR)) : List SRec :=
  (List.zip fils vss).flatMap fun fv => filRecs fv.1.1 fv.1.2 fv.2

/-- `walkL` over an appended list. -/
theorem walkL_append (D2 D3S : ℕ) (r : RC) (L1 L2 : List (Seg × VR × VR)) (acc : Acc) :
    walkL D2 D3S r (L1 ++ L2) acc = walkL D2 D3S r L2 (walkL D2 D3S r L1 acc) := by
  simp [walkL, List.foldl_append]

/-- **`allWalk` is the fold over all segment records.** -/
theorem allWalk_eq (o : Offs) (D2 D3S : ℕ) (r : RC) (c : CD) :
    ∀ (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (gs : List (List ℕ)) (acc : Acc),
      (∀ f ∈ fils, f.2 ≠ []) →
      allWalk D2 D3S r acc (fils.map fun f => mkFil o f.1 f.2)
          (allVerts c (fils.map fun f => mkFil o f.1 f.2) gs) =
        walkL D2 D3S r ((allRecs fils (allVerts c (fils.map fun f => mkFil o f.1 f.2) gs)).map
          (srTriple o)) acc
  | [], gs, acc, _ => by cases gs <;> simp [allWalk, allVerts, allRecs, walkL]
  | f :: fils, gs, acc, hne => by
    have hf : f.2 ≠ [] := hne f (by simp)
    have hlen : ∀ g, (mkFil o f.1 f.2).sgs.length = (filVerts c (mkFil o f.1 f.2).vts g).length ∧
        0 < (filVerts c (mkFil o f.1 f.2).vts g).length := by
      intro g
      constructor
      · simp [mkFil, filVerts_length, rot1_length]
      · simp only [mkFil, filVerts_length, List.length_map]
        exact List.length_pos_iff.mpr hf
    cases gs with
    | nil =>
      simp only [List.map_cons, allVerts, allWalk]
      rw [filWalk_eq _ _ _ _ _ _ (hlen []).1 (hlen []).2, allWalk_eq o D2 D3S r c fils [] _
        (fun g hg => hne g (List.mem_cons_of_mem _ hg))]
      simp only [allRecs, List.zip_cons_cons, List.flatMap_cons, List.map_append, walkL_append]
      rw [filWalk_list]
    | cons g gs =>
      simp only [List.map_cons, allVerts, allWalk]
      rw [filWalk_eq _ _ _ _ _ _ (hlen g).1 (hlen g).2, allWalk_eq o D2 D3S r c fils gs _
        (fun g hg => hne g (List.mem_cons_of_mem _ hg))]
      simp only [allRecs, List.zip_cons_cons, List.flatMap_cons, List.map_append, walkL_append]
      rw [filWalk_list]

/-! ## Validity of the segment data -/

/-- What `segOK` guarantees. -/
theorem segOK_spec {o : Offs} {K : ℤ} {p q : ℤ × ℤ × ℤ} (h : segOK o K p q = true) :
    trOK p ∧
    |K * (tr p.2.1 * (q.2.2 - p.2.2) - tr p.2.2 * (q.2.1 - p.2.1))| ≤ (o.c1x : ℤ) ∧
    |K * (tr p.2.2 * (q.1 - p.1) - tr p.1 * (q.2.2 - p.2.2))| ≤ (o.c1y : ℤ) ∧
    |K * (tr p.1 * (q.2.1 - p.2.1) - tr p.2.1 * (q.1 - p.1))| ≤ (o.c1z : ℤ) ∧
    |K * (q.1 - p.1)| ≤ (o.c2x : ℤ) ∧ |K * (q.2.1 - p.2.1)| ≤ (o.c2y : ℤ) ∧
    |K * (q.2.2 - p.2.2)| ≤ (o.c2z : ℤ) ∧
    o.c1x ≤ o.c1m ∧ o.c1y ≤ o.c1m ∧ o.c1z ≤ o.c1m ∧ o.c2x ≤ o.c2m ∧ o.c2y ≤ o.c2m ∧
    o.c2z ≤ o.c2m ∧
    0 < (q.1 - p.1) * (q.1 - p.1) + (q.2.1 - p.2.1) * (q.2.1 - p.2.1) + (q.2.2 - p.2.2) * (q.2.2 -
        p.2.2) ∧
    (q.1 - p.1) * (q.1 - p.1) + (q.2.1 - p.2.1) * (q.2.1 - p.2.1) + (q.2.2 - p.2.2) * (q.2.2 -
        p.2.2) ≤
      (sqrtUp ((q.1 - p.1) * (q.1 - p.1) + (q.2.1 - p.2.1) * (q.2.1 - p.2.1) +
        (q.2.2 - p.2.2) * (q.2.2 - p.2.2)).toNat : ℤ) *
      (sqrtUp ((q.1 - p.1) * (q.1 - p.1) + (q.2.1 - p.2.1) * (q.2.1 - p.2.1) +
        (q.2.2 - p.2.2) * (q.2.2 - p.2.2)).toNat : ℤ) := by
  simp only [segOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩, h16⟩, h17⟩ := h
  refine ⟨⟨h1, h2, h3⟩, ?_, ?_, ?_, ?_, ?_, ?_, h10, h11, h12, h13, h14, h15, h16, h17⟩ <;>
    (rw [Int.abs_eq_natAbs]; exact_mod_cast ‹_›)

/-! ## Sums with bracketed factors -/

/-- Replacing bracketed real factors `F` by their floors `f` in a weighted sum. -/
theorem sum_bracket {ι : Type} (L : List ι) (F : ι → ℝ) (f : ι → ℕ) (w : ι → ℝ) {u c : ℝ}
    (hu : 0 ≤ u) (hF : ∀ z ∈ L, F z ≤ f z + 1 ∧ (1 - 7 * u) * f z ≤ F z)
    (hw : ∀ z ∈ L, |w z| ≤ c) :
    |(L.map fun z => F z * w z).sum - (L.map fun z => (f z : ℝ) * w z).sum| ≤
      c * (7 * u * (L.map fun z => (f z : ℝ)).sum + L.length) := by
  induction L with
  | nil => simp
  | cons z L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := ih (fun y hy => hF y (by simp [hy])) (fun y hy => hw y (by simp [hy]))
    obtain ⟨hF1, hF2⟩ := hF z (by simp)
    have hwz := hw z (by simp)
    have hc : 0 ≤ c := (abs_nonneg _).trans hwz
    have hfz : (0 : ℝ) ≤ f z := Nat.cast_nonneg _
    have hd : |F z - f z| ≤ 7 * u * f z + 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have hterm : |F z * w z - f z * w z| ≤ c * (7 * u * f z + 1) := by
      rw [← sub_mul, abs_mul]
      calc |F z - f z| * |w z| ≤ (7 * u * f z + 1) * c :=
            mul_le_mul hd hwz (abs_nonneg _) (by positivity)
        _ = c * (7 * u * f z + 1) := by ring
    calc |F z * w z + (L.map fun z => F z * w z).sum - (f z * w z + (L.map fun z => (f z : ℝ) * w
        z).sum)|
        = |(F z * w z - f z * w z) + ((L.map fun z => F z * w z).sum -
            (L.map fun z => (f z : ℝ) * w z).sum)| := by ring_nf
      _ ≤ |F z * w z - f z * w z| + |(L.map fun z => F z * w z).sum -
            (L.map fun z => (f z : ℝ) * w z).sum| := abs_add_le _ _
      _ ≤ c * (7 * u * f z + 1) + c * (7 * u * (L.map fun z => (f z : ℝ)).sum + L.length) :=
          add_le_add hterm h1
      _ = c * (7 * u * (f z + (L.map fun z => (f z : ℝ)).sum) + (L.length + 1 : ℕ)) := by
          push_cast; ring

/-! ## The segments of the coil set -/

/-- All segments `(K, p, q)` of a list of closed polygonal filaments `(K, vertices)`. -/
@[expose] def allSegs (fils : List (ℤ × List (ℤ × ℤ × ℤ))) : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  fils.flatMap fun f => (List.zip f.2 (rot1 f.2)).map fun pq => (f.1, pq.1, pq.2)

/-- The closed-form field of all segments at `y`. -/
@[expose] def Bseg (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) : Space :=
  ((allSegs fils).map fun z => segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) y).sum

/-- The records of the corner walk cover exactly the segments. -/
theorem allRecs_segs (o : Offs) (c : CD) : ∀ (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (gs : List (List ℕ)),
    (allRecs fils (allVerts c (fils.map fun f => mkFil o f.1 f.2) gs)).map
      (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils
  | [], gs => by cases gs <;> simp [allRecs, allVerts, allSegs]
  | f :: fils, [] => by
    simp only [List.map_cons, allVerts, allRecs, List.zip_cons_cons, List.flatMap_cons,
      List.map_append]
    rw [filRecs_segs _ _ _ (by simp [mkFil, filVerts_length])]
    have := allRecs_segs o c fils []
    simp only [allRecs] at this
    rw [this]; simp [allSegs]
  | f :: fils, g :: gs => by
    simp only [List.map_cons, allVerts, allRecs, List.zip_cons_cons, List.flatMap_cons,
      List.map_append]
    rw [filRecs_segs _ _ _ (by simp [mkFil, filVerts_length])]
    have := allRecs_segs o c fils gs
    simp only [allRecs] at this
    rw [this]; simp [allSegs]

/-- Validity of all records of the corner walk. -/
theorem allRecs_sound (o : Offs) (Xt Yt Zt D : ℕ) (hD : 0 < D) :
    ∀ (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (gs : List (List ℕ)),
    (∀ f ∈ fils, filOK o f.1 f.2 = true) →
    ∀ z ∈ allRecs fils (allVerts (mkCD Xt Yt Zt D) (fils.map fun f => mkFil o f.1 f.2) gs),
      VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
        segOK o z.1 z.2.1 z.2.2.1 = true := by
  intro fils gs hok z hz
  induction fils generalizing gs with
  | nil => cases gs <;> simp [allRecs, allVerts] at hz
  | cons f fils ih =>
    have hf := hok f (by simp)
    have htr : ∀ p ∈ f.2, trOK p := by
      intro p hp
      unfold filOK at hf
      rw [List.all_eq_true] at hf
      -- `p` is the first point of some segment
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have hmem : (f.2[i], (rot1 f.2)[i]'(by simp [rot1_length]; omega)) ∈
          List.zip f.2 (rot1 f.2) :=
        List.mem_iff_getElem.mpr ⟨i, by simp [rot1_length]; omega, by simp [List.getElem_zip]⟩
      exact (segOK_spec (hf _ hmem)).1
    have key : ∀ g, ∀ z ∈ filRecs f.1 f.2 (filVerts (mkCD Xt Yt Zt D) (mkFil o f.1 f.2).vts g),
        VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
          segOK o z.1 z.2.1 z.2.2.1 = true := by
      intro g z hz
      have hvts : (mkFil o f.1 f.2).vts = f.2.map mkVt := rfl
      rw [hvts] at hz
      have hl : f.2.length = (filVerts (mkCD Xt Yt Zt D) (f.2.map mkVt) g).length := by
        simp [filVerts_length]
      obtain ⟨h1, h2, h3, h4⟩ := filRecs_sound Xt Yt Zt D hl
        (filVerts_sound Xt Yt Zt D hD f.2 g htr) z hz
      refine ⟨h1, h2, ?_⟩
      unfold filOK at hf
      rw [List.all_eq_true] at hf
      have := hf _ h3
      rw [h4]
      exact this
    cases gs with
    | nil =>
      simp only [List.map_cons, allVerts, allRecs, List.zip_cons_cons, List.flatMap_cons,
        List.mem_append] at hz
      rcases hz with hz | hz
      · exact key [] z hz
      · exact ih [] (fun g hg => hok g (List.mem_cons_of_mem _ hg)) (by simpa [allRecs] using hz)
    | cons g gs =>
      simp only [List.map_cons, allVerts, allRecs, List.zip_cons_cons, List.flatMap_cons,
        List.mem_append] at hz
      rcases hz with hz | hz
      · exact key g z hz
      · exact ih gs (fun g hg => hok g (List.mem_cons_of_mem _ hg)) (by simpa [allRecs] using hz)

/-! ## The corner bound -/

/-- Components of a list sum of vectors. -/
theorem list_sum_apply {ι : Type} (L : List ι) (W : ι → Space) (k : Fin 3) :
    (L.map W).sum k = (L.map fun z => W z k).sum := by
  induction L with
  | nil => simp
  | cons z L ih => simp [ih]

/-- The weight vectors of a record: `W₁ = K P'×V`, `W₂ = K V` (as real vectors). -/
@[expose] def W1R (z : SRec) : Space :=
  (z.1 : ℝ) • cross (vecZ (tr z.2.1.1) (tr z.2.1.2.1) (tr z.2.1.2.2))
    (vecZ (z.2.2.1.1 - z.2.1.1) (z.2.2.1.2.1 - z.2.1.2.1) (z.2.2.1.2.2 - z.2.1.2.2))

/-- See `W1R`. -/
@[expose] def W2R (z : SRec) : Space :=
  (z.1 : ℝ) • vecZ (z.2.2.1.1 - z.2.1.1) (z.2.2.1.2.1 - z.2.1.2.1) (z.2.2.1.2.2 - z.2.1.2.2)

/-- The exact scaled kernel factor of a record at the corner. -/
@[expose] def FR (Xt Yt Zt D : ℕ) (z : SRec) : ℝ :=
  segFac' (‖((D : ℝ) * S32) • (ptR z.2.1 - cornerR Xt Yt Zt D)‖)
    (‖((D : ℝ) * S32) • (ptR z.2.2.1 - cornerR Xt Yt Zt D)‖)
    ⟪((D : ℝ) * S32) • (ptR z.2.1 - cornerR Xt Yt Zt D),
      ((D : ℝ) * S32) • (ptR z.2.2.1 - cornerR Xt Yt Zt D)⟫ * ((D : ℝ) ^ 3 * ((two136 : ℕ) : ℝ))

/-- The closed form of one record, in its weights. -/
theorem segClosed_rec (Xt Yt Zt D : ℕ) (hD : 0 < D) (z : SRec) :
    ((D : ℝ) * ((two136 : ℕ) : ℝ)) •
      segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2.1) (cornerR Xt Yt Zt D) =
      (D : ℝ) • (FR Xt Yt Zt D z • W1R z) - S32 • cross (vecZ Xt Yt Zt) (FR Xt Yt Zt D z • W2R z)
          := by
  have h := segClosed_scaled Xt Yt Zt D hD z.1 z.2.1 z.2.2.1
  have e : segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2.1) (cornerR Xt Yt Zt D) =
      ((D : ℝ) ^ 2 * segFac' (‖((D : ℝ) * S32) • (ptR z.2.1 - cornerR Xt Yt Zt D)‖)
        (‖((D : ℝ) * S32) • (ptR z.2.2.1 - cornerR Xt Yt Zt D)‖)
        ⟪((D : ℝ) * S32) • (ptR z.2.1 - cornerR Xt Yt Zt D),
          ((D : ℝ) * S32) • (ptR z.2.2.1 - cornerR Xt Yt Zt D)⟫) •
      ((D : ℝ) • W1R z - S32 • cross (vecZ Xt Yt Zt) (W2R z)) := h
  rw [e, cross_smul_right]
  simp only [FR, smul_sub, smul_smul]
  congr 1 <;> congr 1 <;> ring

/-- The scaled closed-form field of a list of records. -/
theorem sum_segClosed_scaled (Xt Yt Zt D : ℕ) (hD : 0 < D) (R : List SRec) :
    ((D : ℝ) * ((two136 : ℕ) : ℝ)) •
      (R.map fun z => segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2.1) (cornerR Xt Yt Zt
          D)).sum =
      (D : ℝ) • (R.map fun z => FR Xt Yt Zt D z • W1R z).sum -
        S32 • cross (vecZ Xt Yt Zt) ((R.map fun z => FR Xt Yt Zt D z • W2R z).sum) := by
  induction R with
  | nil => simp [cross]
  | cons z R ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [smul_add, ih, segClosed_rec Xt Yt Zt D hD z, cross_add_right, smul_add, smul_add]
    abel

/-- **The closed-form field of the coil set at a corner**, scaled by `SE = D 2¹³⁶`. -/
theorem Bseg_scaled (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (R : List SRec)
    (hR : R.map (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils) (Xt Yt Zt D : ℕ) (hD : 0 < D) :
    ((D : ℝ) * ((two136 : ℕ) : ℝ)) • Bseg fils (cornerR Xt Yt Zt D) =
      (D : ℝ) • (R.map fun z => FR Xt Yt Zt D z • W1R z).sum -
        S32 • cross (vecZ Xt Yt Zt) ((R.map fun z => FR Xt Yt Zt D z • W2R z).sum) := by
  unfold Bseg
  rw [← hR, List.map_map]
  exact sum_segClosed_scaled Xt Yt Zt D hD R

/-- Weights of `mkSeg` as reals. -/
theorem mkSeg_weights {o : Offs} {K : ℤ} {p q : ℤ × ℤ × ℤ} (h : segOK o K p q = true) :
    let z : SRec := (K, p, q, ⟨0, 0, false, 0⟩, ⟨0, 0, false, 0⟩)
    ((mkSeg o K p q).w1x : ℝ) = W1R z 0 + o.c1x ∧ ((mkSeg o K p q).w1y : ℝ) = W1R z 1 + o.c1y ∧
    ((mkSeg o K p q).w1z : ℝ) = W1R z 2 + o.c1z ∧ ((mkSeg o K p q).w2x : ℝ) = W2R z 0 + o.c2x ∧
    ((mkSeg o K p q).w2y : ℝ) = W2R z 1 + o.c2y ∧ ((mkSeg o K p q).w2z : ℝ) = W2R z 2 + o.c2z ∧
    |W1R z 0| ≤ o.c1m ∧ |W1R z 1| ≤ o.c1m ∧ |W1R z 2| ≤ o.c1m ∧
    |W2R z 0| ≤ o.c2m ∧ |W2R z 1| ≤ o.c2m ∧ |W2R z 2| ≤ o.c2m ∧
    ((mkSeg o K p q).vv : ℝ) = ((q.1 - p.1 : ℤ) : ℝ) ^ 2 + ((q.2.1 - p.2.1 : ℤ) : ℝ) ^ 2 +
      ((q.2.2 - p.2.2 : ℤ) : ℝ) ^ 2 := by
  intro z
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _, _⟩ := segOK_spec h
  have ab : ∀ (x : ℤ) (c : ℕ), |x| ≤ (c : ℤ) → (((x + c).toNat : ℕ) : ℝ) = (x : ℝ) + c ∧
      |(x : ℝ)| ≤ c := by
    intro x c hx
    have hx' := abs_le.mp hx
    refine ⟨by rw [toNat_cast_real (by linarith)]; push_cast; ring, ?_⟩
    exact_mod_cast hx
  have w1x : W1R z 0 = ((K * (tr p.2.1 * (q.2.2 - p.2.2) - tr p.2.2 * (q.2.1 - p.2.1)) : ℤ) : ℝ) :=
      by
    simp [W1R, z, cross, crossProduct, vecZ]
  have w1y : W1R z 1 = ((K * (tr p.2.2 * (q.1 - p.1) - tr p.1 * (q.2.2 - p.2.2)) : ℤ) : ℝ) := by
    simp [W1R, z, cross, crossProduct, vecZ]
  have w1z : W1R z 2 = ((K * (tr p.1 * (q.2.1 - p.2.1) - tr p.2.1 * (q.1 - p.1)) : ℤ) : ℝ) := by
    simp [W1R, z, cross, crossProduct, vecZ]
  have w2x : W2R z 0 = ((K * (q.1 - p.1) : ℤ) : ℝ) := by simp [W2R, z, vecZ]
  have w2y : W2R z 1 = ((K * (q.2.1 - p.2.1) : ℤ) : ℝ) := by simp [W2R, z, vecZ]
  have w2z : W2R z 2 = ((K * (q.2.2 - p.2.2) : ℤ) : ℝ) := by simp [W2R, z, vecZ]
  have c1m : ((o.c1x : ℝ) ≤ o.c1m) ∧ ((o.c1y : ℝ) ≤ o.c1m) ∧ ((o.c1z : ℝ) ≤ o.c1m) :=
    ⟨by exact_mod_cast h7, by exact_mod_cast h8, by exact_mod_cast h9⟩
  have c2m : ((o.c2x : ℝ) ≤ o.c2m) ∧ ((o.c2y : ℝ) ≤ o.c2m) ∧ ((o.c2z : ℝ) ≤ o.c2m) :=
    ⟨by exact_mod_cast h10, by exact_mod_cast h11, by exact_mod_cast h12⟩
  obtain ⟨e1, b1⟩ := ab _ _ h1
  obtain ⟨e2, b2⟩ := ab _ _ h2
  obtain ⟨e3, b3⟩ := ab _ _ h3
  obtain ⟨e4, b4⟩ := ab _ _ h4
  obtain ⟨e5, b5⟩ := ab _ _ h5
  obtain ⟨e6, b6⟩ := ab _ _ h6
  simp only [mkSeg]
  rw [w1x, w1y, w1z, w2x, w2y, w2z]
  refine ⟨e1, e2, e3, e4, e5, e6, b1.trans c1m.1, b2.trans c1m.2.1, b3.trans c1m.2.2,
    b4.trans c2m.1, b5.trans c2m.2.1, b6.trans c2m.2.2, ?_⟩
  rw [toNat_cast_real (by positivity)]; push_cast; ring

/-- The real value of a `QQ`. -/
@[expose] def QQ.val (x : QQ) : ℝ := (x.num : ℝ) / x.den

/-- Floor and ceiling of `x · S` bracket the real value. -/
theorem QQ.floor_ceil (x : QQ) (hx : 0 < x.den) (S : ℕ) :
    ((x.floorMul S : ℤ) : ℝ) ≤ x.val * S ∧ x.val * S ≤ ((x.ceilMul S : ℤ) : ℝ) := by
  unfold QQ.floorMul QQ.ceilMul QQ.val
  constructor
  · have := fdiv_le_real (x.num * S) hx
    push_cast at this; rw [div_mul_eq_mul_div]; exact this
  · have := real_lt_fdiv_succ (-(x.num * S)) hx
    have h2 := fdiv_le_real (-(x.num * S)) hx
    push_cast at h2 ⊢
    rw [div_mul_eq_mul_div]
    have : -((x.num : ℝ) * S) / x.den = -((x.num : ℝ) * S / x.den) := by ring
    rw [this] at h2
    linarith

/-- One component of the corner bound. -/
theorem comp_bound {B T Rr hf hc helS m : ℝ} (hBT : |B - T| ≤ Rr) (hh1 : hf ≤ helS)
    (hh2 : helS ≤ hc) (hm1 : |T - Rr - hc| ≤ m) (hm2 : |T + Rr - hf| ≤ m) : |B - helS| ≤ m := by
  rw [abs_le] at *
  constructor <;> linarith [hBT.1, hBT.2, hm1.1, hm1.2, hm2.1, hm2.2]

/-- `nmax` of absolute values dominates both. -/
theorem nmax_natAbs (a b : ℤ) : |(a : ℝ)| ≤ (nmax a.natAbs b.natAbs : ℕ) ∧
    |(b : ℝ)| ≤ (nmax a.natAbs b.natAbs : ℕ) := by
  have ha : |(a : ℝ)| = (a.natAbs : ℝ) := by simp
  have hb : |(b : ℝ)| = (b.natAbs : ℝ) := by simp
  rw [ha, hb]
  exact ⟨by exact_mod_cast nmax_ge_left _ _, by exact_mod_cast nmax_ge_right _ _⟩

/-- From componentwise bounds to the norm bound with the square-root bracket. -/
theorem norm_from_comps {v : Space} {SE mx my mz sN : ℝ} (hSE : 0 < SE) {K : ℝ} (hK : 0 < K)
    (hx : |v 0 * SE| ≤ mx) (hy : |v 1 * SE| ≤ my) (hz : |v 2 * SE| ≤ mz)
    (hN : (mx ^ 2 + my ^ 2 + mz ^ 2) * K ^ 2 ≤ sN ^ 2) (hs : 0 ≤ sN) :
    ‖v‖ * K ≤ sN / SE := by
  rw [le_div_iff₀ hSE]
  have h0 : ‖v‖ ^ 2 * SE ^ 2 = (v 0 * SE) ^ 2 + (v 1 * SE) ^ 2 + (v 2 * SE) ^ 2 := by
    rw [norm_sq_coords]; ring
  have hx2 : (v 0 * SE) ^ 2 ≤ mx ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : (v 1 * SE) ^ 2 ≤ my ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hz2 : (v 2 * SE) ^ 2 ≤ mz ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have hsq : (‖v‖ * K * SE) ^ 2 ≤ sN ^ 2 := by
    calc (‖v‖ * K * SE) ^ 2 = (‖v‖ ^ 2 * SE ^ 2) * K ^ 2 := by ring
      _ ≤ (mx ^ 2 + my ^ 2 + mz ^ 2) * K ^ 2 := by
          rw [h0]; gcongr
      _ ≤ sN ^ 2 := hN
  have h1 : 0 ≤ ‖v‖ * K * SE := by positivity
  nlinarith [sq_nonneg (‖v‖ * K * SE - sN), sq_nonneg (‖v‖ * K * SE + sN)]

/-- **The final assembly of a corner.** If the true weighted sums `Σ₁`, `Σ₂` are within the
bracket errors of the accumulators, then `2⁴⁰ ‖B - hel‖ ≤ e`. -/
theorem cornerFinal_spec (o : Offs) (Xt Yt Zt D : ℕ) (hD : 0 < D) (acc : Acc) (h : QQ × QQ × QQ)
    (hh0 : 0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den) (B H S1v S2v : Space)
    (hB : ((D : ℝ) * ((two136 : ℕ) : ℝ)) • B = (D : ℝ) • S1v - S32 • cross (vecZ Xt Yt Zt) S2v)
    (hH : H = WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val]) (n : ℕ) (hn : n ≤ nSeg)
    (e1 : ℝ) (he1 : e1 = (o.c1m : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n))
    (e2 : ℝ) (he2 : e2 = (o.c2m : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n))
    (h1x : |S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf)| ≤ e1)
    (h1y : |S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf)| ≤ e1)
    (h1z : |S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf)| ≤ e1)
    (h2x : |S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)| ≤ e2)
    (h2y : |S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)| ≤ e2)
    (h2z : |S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)| ≤ e2)
    (hfin : (cornerFinal o Xt Yt Zt D (Nat.mul D two32) acc h).1 = true) :
    ‖B - H‖ * ((two40 : ℕ) : ℝ) ≤ (cornerFinal o Xt Yt Zt D (Nat.mul D two32) acc h).2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hS := S32_pos
  have h136 : (0 : ℝ) < ((two136 : ℕ) : ℝ) := by norm_num [two136]
  set SE : ℝ := (D : ℝ) * ((two136 : ℕ) : ℝ)
  have hSE : 0 < SE := mul_pos hD' h136
  have hSEn : ((Nat.mul D two136 : ℕ) : ℝ) = SE := by push_cast [Nat.mul_eq]; rfl
  -- components of `SE • B`
  have hBc : ∀ k : Fin 3, SE * B k = ((D : ℝ) • S1v - S32 • cross (vecZ Xt Yt Zt) S2v) k := by
    intro k; rw [← hB]; simp [SE]
  have hB0 : SE * B 0 = D * S1v 0 - S32 * (Yt * S2v 2 - Zt * S2v 1) := by
    rw [hBc 0]; simp [cross, crossProduct, vecZ]
  have hB1 : SE * B 1 = D * S1v 1 - S32 * (Zt * S2v 0 - Xt * S2v 2) := by
    rw [hBc 1]; simp [cross, crossProduct, vecZ]
  have hB2 : SE * B 2 = D * S1v 2 - S32 * (Xt * S2v 1 - Yt * S2v 0) := by
    rw [hBc 2]; simp [cross, crossProduct, vecZ]
  -- error radii
  have hE : ∀ (cm : ℕ), (cm : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n) ≤
      ((Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) cm) acc.sf) (Nat.mul D two32))
        (Nat.mul nSeg cm) : ℕ) : ℝ) := by
    intro cm
    have hlam0 : 0 < Nat.mul D two32 := Nat.mul_pos hD (by norm_num [two32])
    have hc := cdiv_ge (Nat.mul (Nat.mul (Nat.mul 70 KT) cm) acc.sf) hlam0
    push_cast [Nat.mul_eq, Nat.add_eq, two32_cast] at hc ⊢
    have hnn : (n : ℝ) ≤ nSeg := by exact_mod_cast hn
    have : (cm : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf) =
        70 * KT * cm * acc.sf / (D * S32) := by field_simp; ring
    nlinarith [Nat.cast_nonneg (α := ℝ) cm]
  have hE1 := hE o.c1m
  have hE2 := hE o.c2m
  rw [← he1] at hE1
  rw [← he2] at hE2
  have he20 : 0 ≤ e2 := (abs_nonneg _).trans h2x
  have hfl := fun (x : QQ) (hx : 0 < x.den) => QQ.floor_ceil x hx (Nat.mul D two136)
  obtain ⟨fx1, fx2⟩ := hfl h.1 hh0.1
  obtain ⟨fy1, fy2⟩ := hfl h.2.1 hh0.2.1
  obtain ⟨fz1, fz2⟩ := hfl h.2.2 hh0.2.2
  rw [hSEn] at fx1 fx2 fy1 fy2 fz1 fz2
  simp only [cornerFinal] at hfin ⊢
  simp only [Nat.ble_eq] at hfin
  -- name the checker quantities
  generalize hE1n : Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c1m) acc.sf) (Nat.mul D
      two32))
    (Nat.mul nSeg o.c1m) = E1n at hfin ⊢ hE1
  generalize hE2n : Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c2m) acc.sf) (Nat.mul D
      two32))
    (Nat.mul nSeg o.c2m) = E2n at hfin ⊢ hE2
  set Tx : ℤ := (D : ℤ) * unoff acc.sx o.c1x acc.sf -
    4294967296 * ((Yt : ℤ) * unoff acc.tz o.c2z acc.sf - (Zt : ℤ) * unoff acc.ty o.c2y acc.sf)
  set Ty : ℤ := (D : ℤ) * unoff acc.sy o.c1y acc.sf -
    4294967296 * ((Zt : ℤ) * unoff acc.tx o.c2x acc.sf - (Xt : ℤ) * unoff acc.tz o.c2z acc.sf)
  set Tz : ℤ := (D : ℤ) * unoff acc.sz o.c1z acc.sf -
    4294967296 * ((Xt : ℤ) * unoff acc.ty o.c2y acc.sf - (Yt : ℤ) * unoff acc.tx o.c2x acc.sf)
  set Rx : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Yt Zt) E2n)) : ℕ) : ℤ)
  set Ry : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Zt Xt) E2n)) : ℕ) : ℤ)
  set Rz : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Xt Yt) E2n)) : ℕ) : ℤ)
  have hun : ∀ x c : ℕ, ((unoff x c acc.sf : ℤ) : ℝ) = (x : ℝ) - c * acc.sf := by
    intro x c; simp [unoff]
  have hTx : (Tx : ℝ) = D * ((acc.sx : ℝ) - o.c1x * acc.sf) -
      S32 * (Yt * ((acc.tz : ℝ) - o.c2z * acc.sf) - Zt * ((acc.ty : ℝ) - o.c2y * acc.sf)) := by
    simp only [Tx]; push_cast [hun]; simp only [S32]
  have hTy : (Ty : ℝ) = D * ((acc.sy : ℝ) - o.c1y * acc.sf) -
      S32 * (Zt * ((acc.tx : ℝ) - o.c2x * acc.sf) - Xt * ((acc.tz : ℝ) - o.c2z * acc.sf)) := by
    simp only [Ty]; push_cast [hun]; simp only [S32]
  have hTz : (Tz : ℝ) = D * ((acc.sz : ℝ) - o.c1z * acc.sf) -
      S32 * (Xt * ((acc.ty : ℝ) - o.c2y * acc.sf) - Yt * ((acc.tx : ℝ) - o.c2x * acc.sf)) := by
    simp only [Tz]; push_cast [hun]; simp only [S32]
  have hRx : (Rx : ℝ) = D * E1n + S32 * ((Yt + Zt) * E2n) := by
    simp only [Rx]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hRy : (Ry : ℝ) = D * E1n + S32 * ((Zt + Xt) * E2n) := by
    simp only [Ry]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hRz : (Rz : ℝ) = D * E1n + S32 * ((Xt + Yt) * E2n) := by
    simp only [Rz]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hXt : (0 : ℝ) ≤ Xt := Nat.cast_nonneg _
  have hYt : (0 : ℝ) ≤ Yt := Nat.cast_nonneg _
  have hZt : (0 : ℝ) ≤ Zt := Nat.cast_nonneg _
  have cxb : ∀ (a b : ℝ) (P Q : ℝ), 0 ≤ P → 0 ≤ Q → |a| ≤ e2 → |b| ≤ e2 →
      |P * a - Q * b| ≤ (P + Q) * e2 := by
    intro a b P Q hP hQ ha hb
    calc |P * a - Q * b| ≤ |P * a| + |Q * b| := abs_sub _ _
      _ = P * |a| + Q * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_nonneg hQ]
      _ ≤ P * e2 + Q * e2 := by gcongr
      _ = (P + Q) * e2 := by ring
  have bx : |SE * B 0 - Tx| ≤ Rx := by
    rw [hB0, hTx, hRx]
    have h1 : |(D : ℝ) * (S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1x.trans hE1) hD'.le
    have h2 := cxb (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)) (S2v 1 - ((acc.ty : ℝ) - o.c2y *
        acc.sf))
      Yt Zt hYt hZt h2z h2y
    have h3 : |S32 * (Yt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)) -
        Zt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)))| ≤ S32 * ((Yt + Zt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 0 - S32 * (Yt * S2v 2 - Zt * S2v 1) - (D * ((acc.sx : ℝ) - o.c1x * acc.sf) -
          S32 * (Yt * ((acc.tz : ℝ) - o.c2z * acc.sf) - Zt * ((acc.ty : ℝ) - o.c2y * acc.sf)))|
        = |(D : ℝ) * (S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf)) - S32 * (Yt * (S2v 2 -
            ((acc.tz : ℝ) - o.c2z * acc.sf)) - Zt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)))| :=
                by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  have by' : |SE * B 1 - Ty| ≤ Ry := by
    rw [hB1, hTy, hRy]
    have h1 : |(D : ℝ) * (S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1y.trans hE1) hD'.le
    have h2 := cxb (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)) (S2v 2 - ((acc.tz : ℝ) - o.c2z *
        acc.sf))
      Zt Xt hZt hXt h2x h2z
    have h3 : |S32 * (Zt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)) -
        Xt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)))| ≤ S32 * ((Zt + Xt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 1 - S32 * (Zt * S2v 0 - Xt * S2v 2) - (D * ((acc.sy : ℝ) - o.c1y * acc.sf) -
          S32 * (Zt * ((acc.tx : ℝ) - o.c2x * acc.sf) - Xt * ((acc.tz : ℝ) - o.c2z * acc.sf)))|
        = |(D : ℝ) * (S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf)) - S32 * (Zt * (S2v 0 -
            ((acc.tx : ℝ) - o.c2x * acc.sf)) - Xt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)))| :=
                by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  have bz : |SE * B 2 - Tz| ≤ Rz := by
    rw [hB2, hTz, hRz]
    have h1 : |(D : ℝ) * (S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1z.trans hE1) hD'.le
    have h2 := cxb (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)) (S2v 0 - ((acc.tx : ℝ) - o.c2x *
        acc.sf))
      Xt Yt hXt hYt h2y h2x
    have h3 : |S32 * (Xt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)) -
        Yt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)))| ≤ S32 * ((Xt + Yt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 2 - S32 * (Xt * S2v 1 - Yt * S2v 0) - (D * ((acc.sz : ℝ) - o.c1z * acc.sf) -
          S32 * (Xt * ((acc.ty : ℝ) - o.c2y * acc.sf) - Yt * ((acc.tx : ℝ) - o.c2x * acc.sf)))|
        = |(D : ℝ) * (S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf)) - S32 * (Xt * (S2v 1 -
            ((acc.ty : ℝ) - o.c2y * acc.sf)) - Yt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)))| :=
                by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  -- the three component bounds
  have hH0 : H 0 = h.1.val := by rw [hH]; simp
  have hH1 : H 1 = h.2.1.val := by rw [hH]; simp
  have hH2 : H 2 = h.2.2.val := by rw [hH]; simp
  obtain ⟨mx1, mx2⟩ := nmax_natAbs (Tx - Rx - h.1.ceilMul (Nat.mul D two136))
    (Tx + Rx - h.1.floorMul (Nat.mul D two136))
  obtain ⟨my1, my2⟩ := nmax_natAbs (Ty - Ry - h.2.1.ceilMul (Nat.mul D two136))
    (Ty + Ry - h.2.1.floorMul (Nat.mul D two136))
  obtain ⟨mz1, mz2⟩ := nmax_natAbs (Tz - Rz - h.2.2.ceilMul (Nat.mul D two136))
    (Tz + Rz - h.2.2.floorMul (Nat.mul D two136))
  generalize nmax (Tx - Rx - h.1.ceilMul (Nat.mul D two136)).natAbs
    (Tx + Rx - h.1.floorMul (Nat.mul D two136)).natAbs = mx at mx1 mx2 hfin ⊢
  generalize nmax (Ty - Ry - h.2.1.ceilMul (Nat.mul D two136)).natAbs
    (Ty + Ry - h.2.1.floorMul (Nat.mul D two136)).natAbs = my at my1 my2 hfin ⊢
  generalize nmax (Tz - Rz - h.2.2.ceilMul (Nat.mul D two136)).natAbs
    (Tz + Rz - h.2.2.floorMul (Nat.mul D two136)).natAbs = mz at mz1 mz2 hfin ⊢
  push_cast at mx1 mx2 my1 my2 mz1 mz2
  have c0 : |(B - H) 0 * SE| ≤ mx := by
    rw [PiLp.sub_apply, hH0, sub_mul, mul_comm (B 0)]
    exact comp_bound bx fx1 fx2 mx1 mx2
  have c1 : |(B - H) 1 * SE| ≤ my := by
    rw [PiLp.sub_apply, hH1, sub_mul, mul_comm (B 1)]
    exact comp_bound by' fy1 fy2 my1 my2
  have c2 : |(B - H) 2 * SE| ≤ mz := by
    rw [PiLp.sub_apply, hH2, sub_mul, mul_comm (B 2)]
    exact comp_bound bz fz1 fz2 mz1 mz2
  generalize hsN : sqrtUpFrom (Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz)) (sq two40))
    (Nat.mul (Nat.add (Nat.add mx my) mz) two40) = sN at hfin ⊢
  have hN : ((mx : ℝ) ^ 2 + (my : ℝ) ^ 2 + (mz : ℝ) ^ 2) * ((two40 : ℕ) : ℝ) ^ 2 ≤ (sN : ℝ) ^ 2 :=
      by
    have := (by exact_mod_cast hfin : ((Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz))
      (sq two40) : ℕ) : ℝ) ≤ ((sq sN : ℕ) : ℝ))
    push_cast [Nat.mul_eq, Nat.add_eq, sq_cast] at this
    linarith
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hfinal := norm_from_comps hSE h40 c0 c1 c2 hN (Nat.cast_nonneg _)
  have hSEpos : 0 < Nat.mul D two136 := Nat.mul_pos hD (by norm_num [two136])
  have hcd := cdiv_ge sN hSEpos
  rw [hSEn] at hcd
  linarith

/-- **Soundness of one corner.** If `cornerEval` accepts, then
`2⁴⁰ ‖Σ_seg segClosed - hel‖ ≤ e` at the corner `y = cornerR Xt Yt Zt D` (given that the rationals
`h` are the components of `hel(y)`). -/
theorem cornerEval_sound (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hne : ∀ f ∈ fils, f.2 ≠ []) (hfok : ∀ f ∈ fils, filOK o f.1 f.2 = true)
    (hlen : (allSegs fils).length ≤ nSeg) (Xt Yt Zt D : ℕ) (hD : 0 < D) (h : QQ × QQ × QQ)
    (hh0 : 0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den)
    (hhel : hel (cornerR Xt Yt Zt D) = WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val])
    (r : RC) (gs : List (List ℕ))
    (hok : (cornerEval o (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h r gs).ok = true) :
    ‖Bseg fils (cornerR Xt Yt Zt D) - hel (cornerR Xt Yt Zt D)‖ * ((two40 : ℕ) : ℝ) ≤
      (cornerEval o (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h r gs).e := by
  set y := cornerR Xt Yt Zt D
  set fs := fils.map fun f => mkFil o f.1 f.2
  set c := mkCD Xt Yt Zt D with hc
  set vss := allVerts c fs gs
  set D3S := Nat.mul (Nat.mul (Nat.mul D D) D) two136
  set R := allRecs fils vss
  have hwalk := allWalk_eq o (Nat.mul D D) D3S r c fils gs ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ hne
  set acc := walkL (Nat.mul D D) D3S r (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have hce : cornerEval o fs Xt Yt Zt D h r gs =
      ⟨((acc.ok && (cornerFinal o Xt Yt Zt D (Nat.mul D two32) acc h).1) &&
          Nat.ble (Nat.mul 1000 KT) (Nat.mul D two32)) && (!r.doRem || Nat.ble r.rBD r.s0l),
        (cornerFinal o Xt Yt Zt D (Nat.mul D two32) acc h).2, acc.rem,
        vss.map (fun l => l.map VR.g)⟩ := by
    have hwalk' : allWalk (Nat.mul D D) (Nat.mul (Nat.mul (Nat.mul D D) D) two136) r
        ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ fs
        (allVerts ⟨D, Nat.mul D D, Nat.mul Xt two32, Nat.mul Yt two32, Nat.mul Zt two32,
          Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32))) (sq (Nat.mul Zt two32)),
          Nat.mul D two32⟩ fs gs) = acc := hwalk
    simp only [cornerEval]
    rw [hwalk']
    rfl
  rw [hce] at hok ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨⟨hacc, hfin⟩, hlamK⟩, -⟩ := hok
  obtain ⟨hsx, hsy, hsz, htx, hty, htz, hsf, -, hall⟩ :=
    fold_segStep (Nat.mul D D) D3S r (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have hchk := (hall hacc).2
  -- per-record facts
  have hrec := allRecs_sound o Xt Yt Zt D hD fils gs hfok
  have hRsegs : R.map (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils := allRecs_segs o c fils gs
  have hRlen : R.length ≤ nSeg := by
    have := congrArg List.length hRsegs; rw [List.length_map] at this; omega
  set f : SRec → ℕ := fun z => segF (Nat.mul D D) D3S (mkSeg o z.1 z.2.1 z.2.2.1) z.2.2.2.1
      z.2.2.2.2
  set u : ℝ := 10 * (KT : ℝ) / ((D : ℝ) * S32)
  have hlamR : (0 : ℝ) < D * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hu0 : 0 ≤ u := by positivity
  have hbr : ∀ z ∈ R, FR Xt Yt Zt D z ≤ f z + 1 ∧ (1 - 7 * u) * f z ≤ FR Xt Yt Zt D z := by
    intro z hz
    obtain ⟨ha, hb, hs⟩ := hrec z hz
    have hx := hchk (srTriple o z) (List.mem_map_of_mem hz)
    simp only [srTriple, segChk, segRT, Bool.and_eq_true, Nat.ble_eq] at hx
    obtain ⟨⟨⟨hoka, hokb⟩, hcmp⟩, -⟩ := hx
    have hw := mkSeg_weights hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvv⟩ := hw
    have hlam' : 1000 * KT ≤ D * two32 := by simpa [Nat.mul_eq] using hlamK
    have := segFactor_sound Xt Yt Zt D hD ha hb hoka hokb hlam' hvv
      (by simpa [Nat.mul_eq, Nat.add_eq] using hcmp)
    exact this
  -- accumulators as sums over records
  have hmem : ∀ z ∈ R, segOK o z.1 z.2.1 z.2.2.1 = true := fun z hz => (hrec z hz).2.2
  have hsum : ∀ (g : Seg → ℕ) (G : SRec → ℝ), (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) =
      G z) →
      (((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g x.1).sum : ℝ) =
        (R.map fun z => (f z : ℝ) * G z).sum := by
    intro g G hg
    rw [Nat.cast_list_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    simp only [Function.comp, srTriple, f]
    push_cast
    rw [hg z hz]
  have hwz : ∀ z ∈ R, ((mkSeg o z.1 z.2.1 z.2.2.1).w1x : ℝ) = W1R z 0 + o.c1x ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w1y : ℝ) = W1R z 1 + o.c1y ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w1z : ℝ) = W1R z 2 + o.c1z ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2x : ℝ) = W2R z 0 + o.c2x ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2y : ℝ) = W2R z 1 + o.c2y ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2z : ℝ) = W2R z 2 + o.c2z ∧
      |W1R z 0| ≤ o.c1m ∧ |W1R z 1| ≤ o.c1m ∧ |W1R z 2| ≤ o.c1m ∧
      |W2R z 0| ≤ o.c2m ∧ |W2R z 1| ≤ o.c2m ∧ |W2R z 2| ≤ o.c2m := by
    intro z hz
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, -⟩ := mkSeg_weights (hmem z hz)
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  have hsf' : ((acc.sf : ℕ) : ℝ) = (R.map fun z => (f z : ℝ)).sum := by
    rw [hsf]
    simp only [zero_add]
    rw [Nat.cast_list_sum, List.map_map, List.map_map]
    rfl
  -- the six weighted sums of the checker
  have key : ∀ (g : Seg → ℕ) (W : SRec → ℝ) (cw : ℕ),
      (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) = W z + cw) →
      (((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g x.1).sum : ℝ) -
        (cw : ℝ) * acc.sf = (R.map fun z => (f z : ℝ) * W z).sum := by
    intro g W cw hg
    rw [hsum g (fun z => W z + cw) hg, hsf']
    simp only [mul_add, List.sum_map_add]
    rw [List.sum_map_mul_right]
    ring
  have hux : u ≤ 1 / 100 := by
    have : (1000 * KT : ℝ) ≤ D * S32 := by
      have := (by exact_mod_cast hlamK : ((Nat.mul 1000 KT : ℕ) : ℝ) ≤ ((Nat.mul D two32 : ℕ) : ℝ))
      push_cast [Nat.mul_eq, two32_cast] at this; linarith
    simp only [u]; rw [div_le_iff₀ hlamR]; linarith
  have b1x := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 0) hu0 hbr (fun z hz => (hwz z
      hz).2.2.2.2.2.2.1)
  have b1y := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 1) hu0 hbr (fun z hz => (hwz z
      hz).2.2.2.2.2.2.2.1)
  have b1z := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 2) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.1)
  have b2x := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 0) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.1)
  have b2y := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 1) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.2.1)
  have b2z := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 2) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.2.2)
  rw [← hsf'] at b1x b1y b1z b2x b2y b2z
  have hacc0 : ∀ (g : Seg → ℕ) (W : SRec → ℝ) (cw : ℕ) (val : ℕ),
      val = 0 + ((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g
          x.1).sum →
      (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) = W z + cw) →
      (val : ℝ) - cw * acc.sf = (R.map fun z => (f z : ℝ) * W z).sum := by
    intro g W cw val hv hg
    rw [hv, zero_add]
    exact key g W cw hg
  have a1x := hacc0 Seg.w1x (fun z => W1R z 0) o.c1x acc.sx hsx (fun z hz => (hwz z hz).1)
  have a1y := hacc0 Seg.w1y (fun z => W1R z 1) o.c1y acc.sy hsy (fun z hz => (hwz z hz).2.1)
  have a1z := hacc0 Seg.w1z (fun z => W1R z 2) o.c1z acc.sz hsz (fun z hz => (hwz z hz).2.2.1)
  have a2x := hacc0 Seg.w2x (fun z => W2R z 0) o.c2x acc.tx htx (fun z hz => (hwz z hz).2.2.2.1)
  have a2y := hacc0 Seg.w2y (fun z => W2R z 1) o.c2y acc.ty hty (fun z hz => (hwz z hz).2.2.2.2.1)
  have a2z := hacc0 Seg.w2z (fun z => W2R z 2) o.c2z acc.tz htz
    (fun z hz => (hwz z hz).2.2.2.2.2.1)
  have l1 : ∀ k, (R.map fun z => FR Xt Yt Zt D z • W1R z).sum k =
      (R.map fun z => FR Xt Yt Zt D z * W1R z k).sum := by
    intro k; rw [list_sum_apply]; simp
  have l2 : ∀ k, (R.map fun z => FR Xt Yt Zt D z • W2R z).sum k =
      (R.map fun z => FR Xt Yt Zt D z * W2R z k).sum := by
    intro k; rw [list_sum_apply]; simp
  refine cornerFinal_spec o Xt Yt Zt D hD acc h hh0 (Bseg fils y) (hel y)
    (R.map fun z => FR Xt Yt Zt D z • W1R z).sum (R.map fun z => FR Xt Yt Zt D z • W2R z).sum
    (Bseg_scaled fils R hRsegs Xt Yt Zt D hD) hhel R.length hRlen _ rfl _ rfl ?_ ?_ ?_ ?_ ?_ ?_ hfin
  · rw [l1, a1x]; exact b1x
  · rw [l1, a1y]; exact b1y
  · rw [l1, a1z]; exact b1z
  · rw [l2, a2x]; exact b2x
  · rw [l2, a2y]; exact b2y
  · rw [l2, a2z]; exact b2z

end PlasmaLean.Design.PolygonCoil
