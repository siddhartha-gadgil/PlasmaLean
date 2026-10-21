/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCCyl

/-!
# Regularity of the guiding-centre field and a lower bound for `|B|`

For the guiding-centre field `gcField ρ = B + ρ ∇×b` of the rational stellarator `B = field (1/4)`:

* `field_contDiffOn_n`: `B` is `Cⁿ` on the domain `{r₂ > 0}` for every `n` (it is rational in the
  Cartesian coordinates; `Design/RationalStellarator` proves `C²`);
* `Qf_contDiffOn`, `gradient_Qf_contDiffOn`: `Q = |B|²` is `Cⁿ` and `∇Q` is `Cⁿ⁻¹`;
* **`gcField_contDiffOn`**: `gcField ρ` is `C²` on the open set `gcRegion = {r₂ > 0, B ≠ 0}`
  (`isOpen_gcRegion`), via the algebraic form `gcField_eq`
  `B̃ = B + (ρ/2) Q^{−3/2} B × ∇Q`;
* **`norm_field_ge`**: `|B| ≥ 1/10` in the closed tube `rt ≤ 3/10` about the magnetic axis
  (from `|B| ≥ D/R³` and `D ≥ 1/4` on the box `0.7 ≤ R ≤ 1.3`, `|z| ≤ 0.3`, `Dfun_ge`), so the tube
  lies in `gcRegion` (`tube_subset_gcRegion`);
* **`BstarPar_field`**: for the curl-free field `B`, `b · ∇×b = 0`, so the Littlejohn parallel
  field is exactly `B*_∥ = |B|` (every `m, q, v_∥`, every point).

**Sanity.** `field_zero_offDomain`: `B = 0` on the `z`-axis (Lean's `0⁻¹ = 0` convention), so the
identity `B*_∥ = |B|` also holds there.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn WithLp

/-! ## Smoothness of the field -/

/-- `1/r₂` is `Cⁿ` off the axis. -/
theorem contDiffAt_winv_n (n : WithTop ℕ∞) {x : Space} (hx : r2 x ≠ 0) :
    ContDiffAt ℝ n winv x := by
  have : ContDiff ℝ n r2 := by
    unfold r2
    have h0 : ContDiff ℝ n (fun y : Space => y 0) := (pr 0).contDiff
    have h1 : ContDiff ℝ n (fun y : Space => y 1) := (pr 1).contDiff
    fun_prop
  exact this.contDiffAt.inv hx

/-- **The field is `Cⁿ` on the domain**, for every `n`. -/
theorem field_contDiffOn_n (ε : ℝ) (n : WithTop ℕ∞) : ContDiffOn ℝ n (field ε) domain := by
  intro x hx
  have hx' : r2 x ≠ 0 := ne_of_gt hx
  refine ContDiffAt.contDiffWithinAt ?_
  have hw := contDiffAt_winv_n n hx'
  have h0 : ContDiffAt ℝ n (fun y : Space => y 0) x := (pr 0).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ n (fun y : Space => y 1) x := (pr 1).contDiff.contDiffAt
  have g0 : ContDiff ℝ n (fun y : Space => y 0) := (pr 0).contDiff
  have g1 : ContDiff ℝ n (fun y : Space => y 1) := (pr 1).contDiff
  have g2 : ContDiff ℝ n (fun y : Space => y 2) := (pr 2).contDiff
  have hHn : ContDiffAt ℝ n Hnum x := by
    unfold Hnum Aq Bq Xd Yp r2; fun_prop
  have hG : ∀ i, ContDiffAt ℝ n (G i) x := by
    intro i
    have hHd : ContDiffAt ℝ n (Hd i) x := by
      have k0 : ContDiff ℝ n H0 := by unfold H0 Aq Bq Xd Yp r2; fun_prop
      have k1 : ContDiff ℝ n H1 := by unfold H1 Aq Bq Xd Yp r2; fun_prop
      have k2 : ContDiff ℝ n H2 := by unfold H2 Bq Xd Yp r2; fun_prop
      fin_cases i
      exacts [k0.contDiffAt, k1.contDiffAt, k2.contDiffAt]
    have hcv : ContDiffAt ℝ n (cv i) x := by
      fin_cases i
      exacts [h0, h1, contDiffAt_const]
    unfold G; fun_prop
  refine (contDiffAt_piLp 2).mpr (fun i => ?_)
  fin_cases i
  · have e : (fun y => field ε y 0) = fun y => -y 1 * winv y + ε / 4 * G 0 y :=
      funext fun y => (field_apply ε y).1
    rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, e]
    have := hG 0
    fun_prop
  · have e : (fun y => field ε y 1) = fun y => y 0 * winv y + ε / 4 * G 1 y :=
      funext fun y => (field_apply ε y).2.1
    rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, e]
    have := hG 1
    fun_prop
  · have e : (fun y => field ε y 2) = fun y => ε / 4 * G 2 y :=
      funext fun y => (field_apply ε y).2.2
    rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, e]
    have := hG 2
    fun_prop

/-- `Q = |B|²` is `Cⁿ` on the domain. -/
theorem Qf_contDiffOn (n : WithTop ℕ∞) : ContDiffOn ℝ n Qf domain :=
  (contDiff_norm_sq ℝ).comp_contDiffOn (field_contDiffOn_n (1 / 4) n)

/-- `∇Q` is `Cⁿ` on the domain (`Q` is `Cⁿ⁺¹`). -/
theorem gradient_Qf_contDiffOn (n : ℕ) : ContDiffOn ℝ n (gradient Qf) domain := by
  have h := (Qf_contDiffOn ((n : WithTop ℕ∞) + 1)).fderiv_of_isOpen isOpen_domain le_rfl
  exact (InnerProductSpace.toDual ℝ Space).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn h

/-- The cross product is smooth. -/
theorem contDiff_cross (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : Space × Space => cross p.1 p.2) := by
  have e : (fun p : Space × Space => cross p.1 p.2) = fun p => toLp 2
      ![p.1 1 * p.2 2 - p.1 2 * p.2 1, p.1 2 * p.2 0 - p.1 0 * p.2 2,
        p.1 0 * p.2 1 - p.1 1 * p.2 0] := by
    funext p; simp only [cross, cross_apply]
  rw [e]
  refine contDiff_piLp 2 |>.mpr fun i => ?_
  have c : ∀ j : Fin 3, ContDiff ℝ n (fun p : Space × Space => p.1 j) := fun j =>
    ((pr j).contDiff).comp contDiff_fst
  have d : ∀ j : Fin 3, ContDiff ℝ n (fun p : Space × Space => p.2 j) := fun j =>
    ((pr j).contDiff).comp contDiff_snd
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    exact ((c _).mul (d _)).sub ((c _).mul (d _))

/-! ## The region `{r₂ > 0, B ≠ 0}` and the regularity of `gcField` -/

/-- The region where the guiding-centre field has its algebraic form: off the `z`-axis and where
`B ≠ 0`. -/
def gcRegion : Set Space := {x | x ∈ domain ∧ field (1 / 4) x ≠ 0}

/-- `gcRegion` is open. -/
theorem isOpen_gcRegion : IsOpen gcRegion :=
  (field_contDiffOn_n (1 / 4) 0).continuousOn.isOpen_inter_preimage isOpen_domain
    isOpen_compl_singleton

/-- On `gcRegion`, `Q > 0`. -/
theorem Qf_pos {x : Space} (hx : x ∈ gcRegion) : 0 < Qf x := by
  rw [Qf]; exact pow_pos (norm_pos_iff.2 hx.2) 2

/-- **The guiding-centre field is `C²`** on the open region `{r₂ > 0, B ≠ 0}`. -/
theorem gcField_contDiffOn (ρ : ℝ) : ContDiffOn ℝ 2 (gcField ρ) gcRegion := by
  have hsub : gcRegion ⊆ domain := fun x hx => hx.1
  have hB := (field_contDiffOn_n (1 / 4) 2).mono hsub
  have hQ := (Qf_contDiffOn 2).mono hsub
  have hg := (gradient_Qf_contDiffOn 2).mono hsub
  have hQr : ContDiffOn ℝ 2 (fun x => Qf x ^ (-(3 : ℝ) / 2)) gcRegion := fun x hx =>
    ((hQ x hx).contDiffAt (isOpen_gcRegion.mem_nhds hx)).rpow_const_of_ne
      (Qf_pos hx).ne' |>.contDiffWithinAt
  have hc : ContDiffOn ℝ 2 (fun x => cross (field (1 / 4) x) (gradient Qf x)) gcRegion :=
    (contDiff_cross 2).comp_contDiffOn (hB.prodMk hg)
  have hF : ContDiffOn ℝ 2 (fun x => field (1 / 4) x +
      (ρ / 2 * Qf x ^ (-(3 : ℝ) / 2)) • cross (field (1 / 4) x) (gradient Qf x)) gcRegion :=
    hB.add ((contDiffOn_const.mul hQr).smul hc)
  exact hF.congr fun x hx => gcField_eq ρ hx.1 hx.2

/-- `gcField ρ` is `C¹` on `gcRegion`. -/
theorem gcField_contDiffOn_one (ρ : ℝ) : ContDiffOn ℝ 1 (gcField ρ) gcRegion :=
  (gcField_contDiffOn ρ).of_le (by norm_num)

/-! ## A lower bound for `|B|` near the magnetic axis -/

/-- `D ≥ 1/4` on the box `0.7 ≤ R ≤ 1.3`, `|z| ≤ 0.3`. -/
theorem Dfun_ge {R z C S : ℝ} (hR0 : 7 / 10 ≤ R) (hR1 : R ≤ 13 / 10) (hz : |z| ≤ 3 / 10)
    (hC : |C| ≤ 1) (hS : |S| ≤ 1) : 1 / 4 ≤ Dfun R z C S := by
  have hz2 : z ^ 2 ≤ 9 / 100 := by
    have := sq_abs z; nlinarith [abs_nonneg z]
  have hR2 : |R ^ 2 - 1| ≤ 69 / 100 := by rw [abs_le]; constructor <;> nlinarith
  have hf : |sfun R z| ≤ 12 / 100 := by
    have h1 : (R ^ 2 - 1) ^ 2 ≤ (69 / 100) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hR2 2
    rw [sfun, abs_le]; constructor <;> nlinarith [sq_nonneg (R ^ 2 - 1), sq_nonneg z]
  have hg : |sgfun R z| ≤ 27 / 100 := by
    have h5 : |R ^ 2 - 5| ≤ 451 / 100 := by rw [abs_le]; constructor <;> nlinarith
    have hq : |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| ≤ 69 / 100 * (451 / 100) + 36 / 100 := by
      calc |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2|
          ≤ |(R ^ 2 - 1) * (R ^ 2 - 5)| + |4 * z ^ 2| := abs_sub _ _
        _ ≤ 69 / 100 * (451 / 100) + 36 / 100 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * z ^ 2)]
          gcongr
          linarith
    rw [sgfun, abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc |z| * |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| / 4
        ≤ 3 / 10 * (69 / 100 * (451 / 100) + 36 / 100) / 4 := by gcongr
      _ ≤ 27 / 100 := by norm_num
  have hprod1 : |sfun R z * S| ≤ 12 / 100 := by
    rw [abs_mul]; calc |sfun R z| * |S| ≤ 12 / 100 * 1 := by gcongr
      _ = 12 / 100 := by ring
  have hprod2 : |sgfun R z * C| ≤ 27 / 100 := by
    rw [abs_mul]; calc |sgfun R z| * |C| ≤ 27 / 100 * 1 := by gcongr
      _ = 27 / 100 := by ring
  rw [Dfun, eps]
  nlinarith [(abs_le.mp hprod1).1, (abs_le.mp hprod1).2, (abs_le.mp hprod2).1,
    (abs_le.mp hprod2).2]

/-- **`|B| ≥ 1/10` in the closed tube `rt ≤ 3/10`** about the magnetic axis. -/
theorem norm_field_ge {y : Space} (hy : rt y ≤ 3 / 10) : 1 / 10 ≤ ‖field (1 / 4) y‖ := by
  have hy' : rt y < 1 / 2 := by linarith
  have hyeq := eq_torPt hy'
  set r := rt y
  set α := θs y
  have hr0 : 0 ≤ r := rt_nonneg y
  have hc := abs_le.mp (abs_cos_le_one α)
  have hs := abs_le.mp (abs_sin_le_one α)
  have hR0 : 7 / 10 ≤ 1 + r * cos α := by nlinarith
  have hR1 : 1 + r * cos α ≤ 13 / 10 := by nlinarith
  have hz : |r * sin α| ≤ 3 / 10 := by
    rw [abs_mul, abs_of_nonneg hr0]
    calc r * |sin α| ≤ 3 / 10 * 1 := by gcongr; exact abs_sin_le_one α
      _ = 3 / 10 := by ring
  set R := 1 + r * cos α
  set z := r * sin α
  have hRpos : 0 < R := by linarith
  have hD := Dfun_ge (C := cos (2 * φs y)) (S := sin (2 * φs y)) hR0 hR1 hz (abs_cos_le_one _)
    (abs_sin_le_one _)
  have hQ : Qf y = qr R z (cos (2 * φs y)) (sin (2 * φs y)) / R ^ 8 := by
    conv_lhs => rw [hyeq, torPt]
    exact Qf_cylPt hRpos _ _
  have hq : R ^ 2 * Dfun R z (cos (2 * φs y)) (sin (2 * φs y)) ^ 2 ≤
      qr R z (cos (2 * φs y)) (sin (2 * φs y)) := by
    unfold qr; nlinarith [sq_nonneg (nRr R z (cos (2 * φs y)) (sin (2 * φs y))),
      sq_nonneg (nZr R z (cos (2 * φs y)) (sin (2 * φs y)))]
  have hQge : (1 / 10) ^ 2 ≤ Qf y := by
    rw [hQ, le_div_iff₀ (by positivity)]
    have hR6 : R ^ 6 ≤ (13 / 10) ^ 6 := pow_le_pow_left₀ hRpos.le hR1 6
    have hD2 : (1 / 4) ^ 2 ≤ Dfun R z (cos (2 * φs y)) (sin (2 * φs y)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hD 2
    nlinarith [pow_pos hRpos 2, pow_pos hRpos 6]
  rw [Qf] at hQge
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).mp hQge

/-- The closed tube `rt ≤ 3/10` lies in the region `{r₂ > 0, B ≠ 0}`. -/
theorem tube_subset_gcRegion {y : Space} (hy : rt y ≤ 3 / 10) : y ∈ gcRegion := by
  refine ⟨r2_pos_of_rt_lt (by linarith), fun h => ?_⟩
  have := norm_field_ge hy
  rw [h, norm_zero] at this
  norm_num at this

/-! ## `B*_∥ = |B|` -/

/-- **Sanity**: `B = 0` on the `z`-axis (Lean's `0⁻¹ = 0` convention). -/
theorem field_zero_offDomain (ε : ℝ) {x : Space} (hx : x ∉ domain) : field ε x = 0 := by
  have h2 : r2 x = 0 := by
    have : r2 x ≤ 0 := not_lt.mp hx
    have : 0 ≤ r2 x := by unfold r2; positivity
    linarith
  have hw : winv x = 0 := by simp [winv, h2]
  obtain ⟨f0, f1, f2⟩ := field_apply ε x
  rw [space_eq_zero_iff, f0, f1, f2]
  simp [G, hw]

/-- `b · ∇×b = 0` for the curl-free field `B = field (1/4)`. -/
theorem inner_bhat_curlb (x : Space) : ⟪bhat (field (1 / 4)) x, curlb (field (1 / 4)) x⟫ = 0 := by
  by_cases hB : field (1 / 4) x = 0
  · rw [bhat, hB]; simp
  have hx : x ∈ domain := by
    by_contra h; exact hB (field_zero_offDomain _ h)
  have h := gcField_eq 1 hx hB
  rw [gcField, modField, one_smul, add_right_inj] at h
  rw [h, bhat, inner_smul_left, inner_smul_right, PlasmaLean.Kinetic.inner_cross_self]
  simp

/-- **`B*_∥ = |B|`** for the rational stellarator field: the Littlejohn parallel field equals the
field strength at every point, for every `m, q, v_∥` (because `b · ∇×b = 0` for a curl-free
field). -/
theorem BstarPar_field (m q v : ℝ) (x : Space) :
    BstarPar m q (field (1 / 4)) v x = ‖field (1 / 4) x‖ := by
  rw [BstarPar, Bstar, inner_add_right, inner_smul_right, inner_bhat_curlb, mul_zero, add_zero,
    bhat, inner_smul_left, real_inner_self_eq_norm_sq]
  by_cases hB : field (1 / 4) x = 0
  · rw [hB]; simp
  have hn : ‖field (1 / 4) x‖ ≠ 0 := norm_ne_zero_iff.2 hB
  simp only [RCLike.conj_to_real]
  field_simp

end PlasmaLean.Design.RationalStellaratorGC
