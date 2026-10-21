/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamResidual
public import PlasmaLean.Theory.KAM.SampledBound

/-!
# Numerical lemmas for the sampled coil-KAM certificate

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). Kernel-computable integer sums
over the torus records and their real meaning:

* `modeN r = |k| + |m|`, `gA r = |a| + |a'|`, `gB r = |b| + |b'|`, and the weighted sum
  `wsumN En Ed N G recs = Σ G r En^{n_r} Ed^{N - n_r}`; `sum_weight_le`: for `e^ρ ≤ En/Ed` and
  `n_r ≤ N`, `Σ H_r G_r/D e^{ρ n_r} ≤ wsumN/(D Ed^N)` (`H_r = 1` or `n_r`), and
  `sum_weight_sub_one_le` for the displacement sums `Σ G_r/D (e^{ρ n_r} - 1)`;
* `zeroA`, `nzA` (and `B`): the mean coefficients and the `ℓ¹` mass of the non-constant modes;
  `abs_Rr_sub_le`, `abs_Zr_le`: `|R - c| ≤ |zeroA/D - c| + nzA/D`, `|z| ≤ |zeroB|/D + nzB/D`;
* `torusPt_realTube`: the real torus lies in `realTube (max s₁ s₂)`;
* elementary bounds `exp_le_inv_one_sub`, `cosh_le_of_exp`, `sinh_le_of_exp`;
* `Mcoil_ck_le`: `Mcoil (23/100) (12/100) (7/100) ≤ 45000`.

**Sanity.** `wsumN_nil`, `zeroA_nil`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open PlasmaLean.Theory.KAM PlasmaLean.Fields PlasmaLean.Design.CoilFieldComplex
  PlasmaLean.Design.PolygonCoil

/-- The mode size `|k| + |m|` of a record. -/
def modeN (r : TRec) : ℕ := r.k.natAbs + r.m.natAbs

/-- `|a| + |a'|`. -/
def gA (r : TRec) : ℕ := r.a.natAbs + r.a'.natAbs

/-- `|b| + |b'|`. -/
def gB (r : TRec) : ℕ := r.b.natAbs + r.b'.natAbs

/-- The weighted integer sum `Σ G r En^{n_r} Ed^{N - n_r}`. -/
def wsumN (En Ed N : ℕ) (G : TRec → ℕ) (recs : List TRec) : ℕ :=
  (recs.map fun r => G r * En ^ modeN r * Ed ^ (N - modeN r)).sum

/-- `e^{ρ(|k|+|m|)} ≤ E^{n_r}` for `e^ρ ≤ E`. -/
theorem weight_le_pow {ρ E : ℝ} (hE : Real.exp ρ ≤ E) (r : TRec) :
    weight ρ (r.k, r.m) ≤ E ^ modeN r := by
  unfold weight modeSize modeN
  have e : |((r.k : ℤ) : ℝ)| + |((r.m : ℤ) : ℝ)| = ((r.k.natAbs + r.m.natAbs : ℕ) : ℝ) := by
    push_cast; rw [natAbs_cast, natAbs_cast]
  simp only at e ⊢
  rw [e, mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hE _

theorem wsumN_cons (En Ed N : ℕ) (G : TRec → ℕ) (r : TRec) (rs : List TRec) :
    wsumN En Ed N G (r :: rs) = G r * En ^ modeN r * Ed ^ (N - modeN r) + wsumN En Ed N G rs := by
  simp [wsumN]

theorem wsum_eq {En Ed N : ℕ} (hEd : 0 < Ed) (G : TRec → ℕ) (D : ℕ) (hD : 0 < D) :
    ∀ recs : List TRec, (∀ r ∈ recs, modeN r ≤ N) →
      (recs.map fun r => (G r : ℝ) / D * ((En : ℝ) / Ed) ^ modeN r).sum =
        (wsumN En Ed N G recs : ℝ) / (D * Ed ^ N)
  | [], _ => by simp [wsumN]
  | r :: rs, h => by
    have hr := h r (by simp)
    have ih := wsum_eq (En := En) hEd G D hD rs fun r' hr' => h r' (by simp [hr'])
    rw [List.map_cons, List.sum_cons, ih, wsumN_cons, Nat.cast_add, add_div]
    congr 1
    have hEd' : (Ed : ℝ) ≠ 0 := by exact_mod_cast hEd.ne'
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    have hpow : (Ed : ℝ) ^ N = (Ed : ℝ) ^ modeN r * (Ed : ℝ) ^ (N - modeN r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [hpow, div_pow]
    field_simp

/-- **Weighted sums**: `Σ H_r G_r/D e^{ρ n_r} ≤ wsumN En Ed N (H·G)/(D Ed^N)`. -/
theorem sum_weight_le {ρ : ℝ} {En Ed N : ℕ} (hEd : 0 < Ed)
    (hE : Real.exp ρ ≤ (En : ℝ) / Ed) (H G : TRec → ℕ) (D : ℕ) (hD : 0 < D)
    (recs : List TRec) (hN : ∀ r ∈ recs, modeN r ≤ N) :
    (recs.map fun r => (H r : ℝ) * (G r : ℝ) / D * weight ρ (r.k, r.m)).sum ≤
      (wsumN En Ed N (fun r => H r * G r) recs : ℝ) / (D * Ed ^ N) := by
  rw [← wsum_eq hEd (fun r => H r * G r) D hD recs hN]
  apply list_sum_le_sum
  intro r _
  have hw := weight_le_pow hE r
  push_cast
  exact mul_le_mul_of_nonneg_left hw (by positivity)

theorem sum_mul_sub_one (D : ℕ) (G : TRec → ℕ) (w : TRec → ℝ) :
    ∀ l : List TRec, (l.map fun r => (G r : ℝ) / D * (w r - 1)).sum =
      (l.map fun r => (G r : ℝ) / D * w r).sum - ((l.map G).sum : ℝ) / D
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_mul_sub_one D G w l]
    push_cast; ring

/-- **Displacement sums**: `Σ G_r/D (e^{ρ n_r} - 1) ≤ wsumN/(D Ed^N) - Σ G_r/D`. -/
theorem sum_weight_sub_one_le {ρ : ℝ} {En Ed N : ℕ} (hEd : 0 < Ed)
    (hE : Real.exp ρ ≤ (En : ℝ) / Ed) (G : TRec → ℕ) (D : ℕ) (hD : 0 < D)
    (recs : List TRec) (hN : ∀ r ∈ recs, modeN r ≤ N) :
    (recs.map fun r => (1 : ℝ) * (G r : ℝ) / D * (weight ρ (r.k, r.m) - 1)).sum ≤
      (wsumN En Ed N G recs : ℝ) / (D * Ed ^ N) - ((recs.map G).sum : ℝ) / D := by
  have h := sum_weight_le hEd hE (fun _ => 1) G D hD recs hN
  simp only [Nat.cast_one, one_mul] at h ⊢
  have e : (recs.map fun r => (G r : ℝ) / D * (weight ρ (r.k, r.m) - 1)).sum =
      (recs.map fun r => (G r : ℝ) / D * weight ρ (r.k, r.m)).sum - ((recs.map G).sum : ℝ) / D :=
    sum_mul_sub_one D G (fun r => weight ρ (r.k, r.m)) recs
  rw [e]
  have : (wsumN En Ed N (fun r => 1 * G r) recs : ℝ) = (wsumN En Ed N G recs : ℝ) := by
    simp [wsumN]
  linarith

/-! ## The real torus -/

/-- The sum of the cosine coefficients of `R` over the constant modes. -/
def zeroA (recs : List TRec) : ℤ := (recs.map fun r => if r.k = 0 ∧ r.m = 0 then r.a else 0).sum
/-- The sum of the cosine coefficients of `z` over the constant modes. -/
def zeroB (recs : List TRec) : ℤ := (recs.map fun r => if r.k = 0 ∧ r.m = 0 then r.b else 0).sum
/-- The `ℓ¹` mass of `R` over the non-constant modes. -/
def nzA (recs : List TRec) : ℕ := (recs.map fun r => if r.k = 0 ∧ r.m = 0 then 0 else gA r).sum
/-- The `ℓ¹` mass of `z` over the non-constant modes. -/
def nzB (recs : List TRec) : ℕ := (recs.map fun r => if r.k = 0 ∧ r.m = 0 then 0 else gB r).sum

theorem abs_term_le (c c' : ℤ) (x : ℝ) (D : ℕ) :
    |((c : ℝ) * Real.cos x + c' * Real.sin x) / D| ≤ ((c.natAbs + c'.natAbs : ℕ) : ℝ) / D := by
  rw [abs_div, Nat.abs_cast]
  gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, Nat.cast_add, natAbs_cast, natAbs_cast]
  have := Real.abs_cos_le_one x
  have := Real.abs_sin_le_one x
  nlinarith [abs_nonneg (c : ℝ), abs_nonneg (c' : ℝ)]

/-- The real term of one record. -/
def termR (D : ℕ) (c c' : ℤ) (x : ℝ) : ℝ := ((c : ℝ) * Real.cos x + c' * Real.sin x) / D

theorem Rr_cons (D : ℕ) (r : TRec) (rs : List TRec) (θ ψ : ℝ) :
    Rr D (r :: rs) θ ψ = termR D r.a r.a' (r.ang θ ψ) + Rr D rs θ ψ ∧
      Zr D (r :: rs) θ ψ = termR D r.b r.b' (r.ang θ ψ) + Zr D rs θ ψ := by
  simp [Rr, Zr, termR]

theorem zero_cons (r : TRec) (rs : List TRec) :
    zeroA (r :: rs) = (if r.k = 0 ∧ r.m = 0 then r.a else 0) + zeroA rs ∧
    zeroB (r :: rs) = (if r.k = 0 ∧ r.m = 0 then r.b else 0) + zeroB rs ∧
    nzA (r :: rs) = (if r.k = 0 ∧ r.m = 0 then 0 else gA r) + nzA rs ∧
    nzB (r :: rs) = (if r.k = 0 ∧ r.m = 0 then 0 else gB r) + nzB rs := by
  simp [zeroA, zeroB, nzA, nzB]

theorem abs_Rr_sub_zero_le (D : ℕ) (θ ψ : ℝ) :
    ∀ recs : List TRec, |Rr D recs θ ψ - (zeroA recs : ℝ) / D| ≤ (nzA recs : ℝ) / D ∧
      |Zr D recs θ ψ - (zeroB recs : ℝ) / D| ≤ (nzB recs : ℝ) / D
  | [] => by simp [Rr, Zr, zeroA, zeroB, nzA, nzB]
  | r :: rs => by
    obtain ⟨ih1, ih2⟩ := abs_Rr_sub_zero_le D θ ψ rs
    obtain ⟨c1, c2⟩ := Rr_cons D r rs θ ψ
    obtain ⟨z1, z2, z3, z4⟩ := zero_cons r rs
    rw [c1, c2, z1, z2, z3, z4]
    by_cases h0 : r.k = 0 ∧ r.m = 0
    · have hang : r.ang θ ψ = 0 := by simp [TRec.ang, h0.1, h0.2]
      simp only [h0, and_self, ↓reduceIte, hang]
      simp only [termR, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero, Int.cast_add,
        zero_add, add_div]
      constructor
      · rw [show (r.a : ℝ) / D + Rr D rs θ ψ - ((r.a : ℝ) / D + (zeroA rs : ℝ) / D) =
          Rr D rs θ ψ - (zeroA rs : ℝ) / D by ring]
        exact ih1
      · rw [show (r.b : ℝ) / D + Zr D rs θ ψ - ((r.b : ℝ) / D + (zeroB rs : ℝ) / D) =
          Zr D rs θ ψ - (zeroB rs : ℝ) / D by ring]
        exact ih2
    · simp only [h0, ↓reduceIte]
      simp only [zero_add, Nat.cast_add, add_div]
      have t1 := abs_term_le r.a r.a' (r.ang θ ψ) D
      have t2 := abs_term_le r.b r.b' (r.ang θ ψ) D
      constructor
      · rw [show termR D r.a r.a' (r.ang θ ψ) + Rr D rs θ ψ - (zeroA rs : ℝ) / D =
          termR D r.a r.a' (r.ang θ ψ) + (Rr D rs θ ψ - (zeroA rs : ℝ) / D) by ring]
        exact (abs_add_le _ _).trans (add_le_add t1 ih1)
      · rw [show termR D r.b r.b' (r.ang θ ψ) + Zr D rs θ ψ - (zeroB rs : ℝ) / D =
          termR D r.b r.b' (r.ang θ ψ) + (Zr D rs θ ψ - (zeroB rs : ℝ) / D) by ring]
        exact (abs_add_le _ _).trans (add_le_add t2 ih2)

/-- `|R - c| ≤ |zeroA/D - c| + nzA/D`. -/
theorem abs_Rr_sub_le (D : ℕ) (recs : List TRec) (θ ψ c : ℝ) :
    |Rr D recs θ ψ - c| ≤ |(zeroA recs : ℝ) / D - c| + (nzA recs : ℝ) / D := by
  have h := (abs_Rr_sub_zero_le D θ ψ recs).1
  calc |Rr D recs θ ψ - c| =
      |(Rr D recs θ ψ - (zeroA recs : ℝ) / D) + ((zeroA recs : ℝ) / D - c)| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- `|z| ≤ |zeroB|/D + nzB/D`. -/
theorem abs_Zr_le (D : ℕ) (recs : List TRec) (θ ψ : ℝ) :
    |Zr D recs θ ψ| ≤ |(zeroB recs : ℝ) / D| + (nzB recs : ℝ) / D := by
  have h := (abs_Rr_sub_zero_le D θ ψ recs).2
  calc |Zr D recs θ ψ| = |(Zr D recs θ ψ - (zeroB recs : ℝ) / D) + (zeroB recs : ℝ) / D| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- The real torus lies in the tube. -/
theorem torusPt_realTube {D : ℕ} {recs : List TRec} {s₁ s₂ : ℝ}
    (hs₁ : ∀ θ ψ : ℝ, |Rr D recs θ ψ - 1| ≤ s₁) (hs₂ : ∀ θ ψ : ℝ, |Zr D recs θ ψ| ≤ s₂)
    (hs₁1 : s₁ < 1) (θ ψ : ℝ) : torusPt D recs θ ψ ∈ realTube (max s₁ s₂) := by
  have hR₀ := hs₁ θ ψ
  refine ⟨?_, ?_⟩
  · simp only [torusPt, FourierSumHolo.cylR]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hpos : 0 < Rr D recs θ ψ := by
      have := (abs_le.1 hR₀).1; linarith
    have e : Real.sqrt ((Rr D recs θ ψ * Real.cos ψ) ^ 2 + (Rr D recs θ ψ * Real.sin ψ) ^ 2) =
        Rr D recs θ ψ := by
      rw [show (Rr D recs θ ψ * Real.cos ψ) ^ 2 + (Rr D recs θ ψ * Real.sin ψ) ^ 2 =
        Rr D recs θ ψ ^ 2 by linear_combination Rr D recs θ ψ ^ 2 * Real.cos_sq_add_sin_sq ψ,
        Real.sqrt_sq hpos.le]
    rw [e]; exact hR₀.trans (le_max_left _ _)
  · simp only [torusPt, FourierSumHolo.cylR]
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact (hs₂ θ ψ).trans (le_max_right _ _)

/-! ## Elementary bounds -/

theorem exp_le_inv_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : Real.exp x ≤ 1 / (1 - x) :=
  Real.exp_bound_div_one_sub_of_interval h0 h1

theorem exp_neg_le {x : ℝ} (h0 : 0 ≤ x) : Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])

theorem cosh_le_of_exp {x E : ℝ} (h0 : 0 ≤ x) (hE : Real.exp x ≤ E) :
    Real.cosh x ≤ (E + 1 / (1 + x)) / 2 := by
  rw [Real.cosh_eq]
  have := exp_neg_le h0
  linarith

theorem sinh_le_of_exp {x E : ℝ} (hE : Real.exp x ≤ E) :
    Real.sinh x ≤ (E - 1 / E) / 2 := by
  rw [Real.sinh_eq]
  have h : 1 / E ≤ Real.exp (-x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos x) hE
  linarith

/-- The neighbourhood constant of the coarse certificate. -/
theorem Mcoil_ck_le : Mcoil (23 / 100) (12 / 100) (7 / 100) ≤ 45000 := by
  unfold Mcoil Tpoly Taxis κ0
  have hS : S32 = 4294967296 := rfl
  have hs1 : Real.sqrt ((4 + 2 * (23 / 100 : ℝ)) ^ 2 + (7 / 100) ^ 2) ≤ 44607 / 10000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hm : ((12 / 100 : ℝ) ^ 2 - (7 / 100) ^ 2) = 19 / 2000 := by norm_num
  have hs2 : (9746 / 100000 : ℝ) ≤ Real.sqrt (19 / 2000) := Real.le_sqrt_of_sq_le (by norm_num)
  have hden : (19 / 2000 : ℝ) * (9746 / 100000) ≤
      ((12 / 100 : ℝ) ^ 2 - (7 / 100) ^ 2) ^ (3 / 2 : ℝ) := by
    rw [hm, rpow_three_halves (by norm_num)]; gcongr
  have hP : 90485364 / S32 * (23 / 10) * Real.sqrt ((4 + 2 * (23 / 100 : ℝ)) ^ 2 + (7 / 100) ^ 2) /
      ((12 / 100 : ℝ) ^ 2 - (7 / 100) ^ 2) ^ (3 / 2 : ℝ) ≤
      90485364 / 4294967296 * (23 / 10) * (44607 / 10000) / ((19 / 2000) * (9746 / 100000)) := by
    rw [hS]; gcongr
  have hk0 : (1 - (7 / 100 : ℝ) ^ 2 / (1 - 23 / 100) ^ 2) = 5880 / 5929 := by norm_num
  have hsk : (9958 / 10000 : ℝ) ≤ Real.sqrt (5880 / 5929) := Real.le_sqrt_of_sq_le (by norm_num)
  have hA : (1 - (7 / 100 : ℝ) ^ 2 / (1 - 23 / 100) ^ 2) ^ (-(3 / 2) : ℝ) ≤
      ((5880 / 5929) * (9958 / 10000))⁻¹ := by
    rw [hk0, Real.rpow_neg (by norm_num), rpow_three_halves (by norm_num)]
    gcongr
  have hA0 : 0 ≤ (1 / (1 - 23 / 100) + (7 / 100 : ℝ) / (1 - 23 / 100) ^ 2) := by norm_num
  have hAx := mul_le_mul_of_nonneg_right hA hA0
  norm_num at hP hAx ⊢
  linarith

/-! ## Sanity -/

/-- The empty weighted sum. -/
theorem wsumN_nil (En Ed N : ℕ) (G : TRec → ℕ) : wsumN En Ed N G [] = 0 := rfl

/-- The empty mean. -/
theorem zeroA_nil : zeroA [] = 0 := rfl

end PlasmaLean.Design.CoilKam
