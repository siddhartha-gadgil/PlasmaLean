/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Drift of a Lipschitz label across the integral curves of a vector field

Let `L` be constant on the integral curves of a `C¹` vector field `V` inside an open set `U`, and
locally Lipschitz there with constant `K`. A path with velocity `λ(t) V(X) + w(t)` then changes
`L` at a rate of at most `K ‖w‖`:

* `displacement_le`: if `K ‖w(t)‖ ≤ c` on `[0, T]` and the path stays in `U`, then
  `|L(X(t)) − L(X(0))| ≤ c t`.

No derivative of `L` is used. This fits labels defined through a flow (the point where the
integral curve meets a section): a two-sided Grönwall estimate gives a Lipschitz constant for
such a label, while differentiability of the flow in the initial point is not needed.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.LipschitzLabel
open Set Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `L` is constant on every integral curve of `V` that stays in `U`. -/
def InvariantOn (V : E → E) (L : E → ℝ) (U : Set E) : Prop :=
  ∀ (γ : ℝ → E) (a b : ℝ), a ≤ b → (∀ τ ∈ Icc a b, γ τ ∈ U) →
    (∀ τ ∈ Icc a b, HasDerivAt γ (V (γ τ)) τ) → L (γ a) = L (γ b)

variable {V : E → E} {L : E → ℝ} {U : Set E} {K : ℝ≥0}

omit [CompleteSpace E] in
/-- Sanity: for a constant field, a continuous linear functional that vanishes on the field
direction is an invariant label (with Lipschitz constant its norm). -/
theorem invariantOn_linear (v : E) (ℓ : E →L[ℝ] ℝ) (hv : ℓ v = 0) (U : Set E) :
    InvariantOn (fun _ => v) ℓ U := by
  intro γ a b hab _ hγ
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ => ℓ (γ τ)) (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun τ hτ => by
      have h := (ℓ.hasFDerivAt.comp_hasDerivAt τ (hγ τ hτ)).hasDerivWithinAt (s := Icc a b)
      rw [hv] at h
      exact h)
    (fun _ _ => by simp) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  have : ℓ (γ b) - ℓ (γ a) = 0 := by simpa using h
  linarith

/-- Just after time `t` the label has moved by at most `(K ‖w‖ + η)` times the elapsed time. -/
theorem eventually_abs_sub_le (hU : IsOpen U) (inv : InvariantOn V L U) {X : ℝ → E}
    {t lam η : ℝ} {w : E} (mem : X t ∈ U) (smooth : ContDiffAt ℝ 1 V (X t))
    (lip : ∃ W ∈ 𝓝 (X t), LipschitzOnWith K L W)
    (ode : HasDerivAt X (lam • V (X t) + w) t) (hη : 0 < η) :
    ∀ᶠ z in 𝓝[>] t, |L (X z) - L (X t)| ≤ (K * ‖w‖ + η) * (z - t) := by
  obtain ⟨γ, γ0, ε, hε, hγ⟩ :=
    smooth.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  obtain ⟨W, hW, hL⟩ := lip
  have γd : HasDerivAt γ (V (X t)) 0 := by simpa [γ0] using hγ 0 (by simp [hε])
  -- the comparison point on the integral curve
  let p : ℝ → E := fun z => γ (lam * (z - t))
  have pd : HasDerivAt p (lam • V (X t)) t := by
    have inner : HasDerivAt (fun z : ℝ => lam * (z - t)) lam t := by
      simpa using ((hasDerivAt_id t).sub_const t).const_mul lam
    exact HasDerivAt.scomp t (by simpa using γd) inner
  have gd : HasDerivAt (fun z => X z - p z) w t := by
    have h := ode.sub pd
    rw [add_sub_cancel_left] at h
    exact h
  have g0 : X t - p t = 0 := by simp [p, γ0]
  have slope_lim := (hasDerivAt_iff_tendsto_slope.mp gd).mono_left (nhdsGT_le_nhdsNE t)
  have near : ∀ᶠ z in 𝓝[>] t, ‖slope (fun z => X z - p z) t z‖ < ‖w‖ + η / (K + 1) :=
    slope_lim.norm.eventually_lt_const (by
      have : 0 < η / ((K : ℝ) + 1) := by positivity
      linarith)
  -- eventually both points are in the Lipschitz neighbourhood and the curve stays in `U`
  have inner_cont : ContinuousAt (fun z : ℝ => lam * (z - t)) t := by fun_prop
  have small : ∀ᶠ z in 𝓝 t, |lam * (z - t)| < ε := by
    exact inner_cont.abs.eventually_lt_const (by simpa using hε)
  have γU : ∀ᶠ τ in 𝓝 (0 : ℝ), γ τ ∈ U := γd.continuousAt.eventually_mem (by
    simpa [γ0] using hU.mem_nhds mem)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.eventually_nhds_iff.mp γU
  have small' : ∀ᶠ z in 𝓝 t, |lam * (z - t)| < ρ := by
    exact inner_cont.abs.eventually_lt_const (by simpa using hρ)
  have XW : ∀ᶠ z in 𝓝 t, X z ∈ W := ode.continuousAt.eventually_mem hW
  have pW : ∀ᶠ z in 𝓝 t, p z ∈ W := pd.continuousAt.eventually_mem (by
    simpa [p, γ0] using hW)
  have all := (((small.and small').and (XW.and pW)).filter_mono nhdsWithin_le_nhds).and
    (near.and self_mem_nhdsWithin)
  filter_upwards [all] with z hz
  obtain ⟨⟨⟨hε', hρ'⟩, hXW, hpW⟩, hnear, hzt⟩ := hz
  have dz : 0 < z - t := sub_pos.mpr hzt
  -- the label is constant along the integral curve from `0` to `lam * (z - t)`
  have const : L (p z) = L (X t) := by
    have curve (a b : ℝ) (hab : a ≤ b) (ha : |a| < ε ∧ |a| < ρ) (hb : |b| < ε ∧ |b| < ρ) :
        L (γ a) = L (γ b) := by
      refine inv γ a b hab (fun τ hτ => hρU ?_) (fun τ hτ => hγ τ ?_)
      · rw [Real.dist_eq, sub_zero]
        exact abs_lt.mpr ⟨by linarith [(abs_lt.mp ha.2).1, hτ.1], by
          linarith [(abs_lt.mp hb.2).2, hτ.2]⟩
      · exact ⟨by linarith [(abs_lt.mp ha.1).1, hτ.1], by linarith [(abs_lt.mp hb.1).2, hτ.2]⟩
    have zero : |(0 : ℝ)| < ε ∧ |(0 : ℝ)| < ρ := by simp [hε, hρ]
    rcases le_total 0 (lam * (z - t)) with h | h
    · simpa [p, γ0] using (curve 0 _ h zero ⟨hε', hρ'⟩).symm
    · simpa [p, γ0] using curve _ 0 h ⟨hε', hρ'⟩ zero
  have gap : ‖X z - p z‖ ≤ (‖w‖ + η / (K + 1)) * (z - t) := by
    have h := hnear.le
    rw [slope_def_module, g0, sub_zero, norm_smul, norm_inv, Real.norm_of_nonneg dz.le,
      inv_mul_le_iff₀ dz] at h
    linarith [mul_comm (z - t) (‖w‖ + η / ((K : ℝ) + 1))]
  calc |L (X z) - L (X t)| = |L (X z) - L (p z)| := by rw [const]
    _ ≤ K * ‖X z - p z‖ := by
      simpa [Real.dist_eq, dist_eq_norm] using hL.dist_le_mul _ hXW _ hpW
    _ ≤ K * ((‖w‖ + η / (K + 1)) * (z - t)) := by gcongr
    _ ≤ (K * ‖w‖ + η) * (z - t) := by
      have frac : (K : ℝ) * (η / (K + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [K.coe_nonneg, hη]
      nlinarith [dz, frac]

/-- **Lipschitz label drift.** A path whose velocity differs from a multiple of `V` by `w`
changes an invariant `K`-Lipschitz label by at most `c t` when `K ‖w‖ ≤ c`. -/
theorem displacement_le (hU : IsOpen U) (smooth : ∀ x ∈ U, ContDiffAt ℝ 1 V x)
    (lip : ∀ x ∈ U, ∃ W ∈ 𝓝 x, LipschitzOnWith K L W) (inv : InvariantOn V L U)
    {X : ℝ → E} {lam : ℝ → ℝ} {w : ℝ → E} {c T : ℝ}
    (inU : ∀ t ∈ Icc 0 T, X t ∈ U)
    (ode : ∀ t ∈ Icc 0 T, HasDerivAt X (lam t • V (X t) + w t) t)
    (small : ∀ t ∈ Icc 0 T, K * ‖w t‖ ≤ c) :
    ∀ t ∈ Icc 0 T, |L (X t) - L (X 0)| ≤ c * t := by
  have cont : ContinuousOn (fun s => L (X s)) (Icc 0 T) := by
    intro s hs
    obtain ⟨W, hW, hL⟩ := lip _ (inU s hs)
    have hc : ContinuousAt L (X s) := hL.continuousOn.continuousAt hW
    exact (hc.comp (ode s hs).continuousAt).continuousWithinAt
  have slope_bound (σ : ℝ) (hσ : |σ| = 1) : ∀ s ∈ Ico 0 T, ∀ r, c < r →
      ∃ᶠ z in 𝓝[>] s, slope (fun s => σ * L (X s)) s z < r := by
    intro s hs r hr
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have ev := eventually_abs_sub_le hU inv (inU s hs') (smooth _ (inU s hs'))
      (lip _ (inU s hs')) (ode s hs') (half_pos (sub_pos.mpr hr))
    refine (ev.and self_mem_nhdsWithin).frequently.mono ?_
    rintro z ⟨hz, hzs⟩
    have dz : 0 < z - s := sub_pos.mpr hzs
    rw [slope_def_field, div_lt_iff₀ dz, ← mul_sub]
    have h1 : σ * (L (X z) - L (X s)) ≤ |L (X z) - L (X s)| := by
      rcases (abs_eq (zero_le_one' ℝ)).mp hσ with h | h
      · rw [h, one_mul]
        exact le_abs_self _
      · rw [h, neg_one_mul]
        exact neg_le_abs _
    nlinarith [small s hs', hz, dz]
  intro t ht
  have line (b : ℝ) (s : ℝ) (_ : s ∈ Ico 0 T) :
      HasDerivWithinAt (fun s => b + c * s) c (Ici s) s := by
    simpa using (((hasDerivAt_id s).const_mul c).const_add b).hasDerivWithinAt
  have lc (b : ℝ) : ContinuousOn (fun s => b + c * s) (Icc 0 T) := by fun_prop
  have up := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun s => (1 : ℝ) * L (X s)) (by simpa using cont)
    (B := fun s => L (X 0) + c * s) (B' := fun _ => c) (by simp) (lc _) (line _)
    (slope_bound 1 (by simp)) ht
  have down := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun s => (-1 : ℝ) * L (X s)) (by simpa using cont.neg)
    (B := fun s => -L (X 0) + c * s) (B' := fun _ => c) (by simp) (lc _) (line _)
    (slope_bound (-1) (by simp)) ht
  simp only [one_mul, neg_mul] at up down
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end PlasmaLean.Fields.LipschitzLabel
