/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusATwist
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The average torsion of torus A (KAM route, K3 lemma 5, part 3)

The twist constant of the K3 plan (H-twist, `notes/theory/kam-k3-plan.md` §2) is the average of
the torsion over the torus,

  `⟨T₀⟩ = (2π²)⁻¹ ∫₀^π ∫₀^{2π} T₀(θ, φ) dθ dφ`  (`torusAvg`; `θ` has period `2π`, `φ` period `π`).

**Main result** (`torusA_twist`): `⟨T₀⟩ ≥ 3/10 > 0`. (Numerically `⟨T₀⟩ ≈ 0.39864`.)

Proof: `T₀ + g > 3/10` pointwise (`torusA_torsion_shifted`), and `∫∫ g = 0` (`integral_gF`)
because `g` is a trigonometric polynomial without constant term (`tG_centre`): every mode
`cos(kθ + m ψ)`, `(k, m) ≠ 0`, integrates to zero over the torus (`integral_cos_mode`).
Continuity of `T₀` (`continuous_T0`) gives the integrability needed for the monotonicity of the
iterated integral.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA.Frame

open Finset PlasmaLean.Certificates.KronExpr Real intervalIntegral

/-- The average over the torus `θ ∈ [0, 2π]`, `φ ∈ [0, π]` (one field period). -/
def torusAvg (f : ℝ → ℝ → ℝ) : ℝ := (∫ φ in (0)..π, ∫ θ in (0)..(2 * π), f θ φ) / (2 * π ^ 2)

/-- Sanity check of the normalization: the average of a constant is the constant. -/
theorem torusAvg_const (c : ℝ) : torusAvg (fun _ _ => c) = c := by
  have hpi : 0 < π := Real.pi_pos
  simp only [torusAvg, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

/-! ## Integrals of the Fourier modes -/

/-- `∫₀^{2π} cos(kθ + c) dθ = 0` for an integer `k ≠ 0`. -/
theorem integral_cos_int_mul (k : ℤ) (hk : k ≠ 0) (c : ℝ) :
    ∫ θ in (0)..(2 * π), Real.cos ((k : ℝ) * θ + c) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) hk', integral_cos]
  have : Real.sin ((k : ℝ) * (2 * π) + c) = Real.sin c := by
    rw [add_comm]; exact Real.sin_add_int_mul_two_pi c k
  simp [this]

/-- The `θ`-integral of a mode. -/
theorem integral_ang_θ (i j : ℕ) (φ : ℝ) :
    ∫ θ in (0)..(2 * π), Real.cos (ang i j θ φ) =
      if i = N then 2 * π * Real.cos (((j : ℝ) - M) * psi φ) else 0 := by
  split_ifs with h
  · subst h; simp [ang]
  · have := integral_cos_int_mul ((i : ℤ) - N) (by omega) (((j : ℝ) - M) * psi φ)
    simpa [ang] using this

/-- The `φ`-integral of a `ψ`-mode, `ψ = 2φ − π/2`. -/
theorem integral_psi_mode (j : ℕ) :
    ∫ φ in (0)..π, Real.cos (((j : ℝ) - M) * psi φ) = if j = M then π else 0 := by
  split_ifs with h
  · subst h; simp
  · have hm : ((j : ℤ) - M) ≠ 0 := by omega
    have hm' : (2 * (((j : ℤ) - M : ℤ) : ℝ)) ≠ 0 := by
      have : (((j : ℤ) - M : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hm
      positivity
    have e : ∀ φ, ((j : ℝ) - M) * psi φ =
        (2 * (((j : ℤ) - M : ℤ) : ℝ)) * φ + (-(((j : ℤ) - M : ℤ) : ℝ) * (π / 2)) := by
      intro φ; simp only [psi]; push_cast; ring
    simp_rw [e]
    rw [intervalIntegral.integral_comp_mul_add (fun x => Real.cos x) hm', integral_cos]
    have key : Real.sin (2 * (((j : ℤ) - M : ℤ) : ℝ) * π + (-(((j : ℤ) - M : ℤ) : ℝ) * (π / 2))) =
        Real.sin (-(((j : ℤ) - M : ℤ) : ℝ) * (π / 2)) := by
      rw [show 2 * (((j : ℤ) - M : ℤ) : ℝ) * π + (-(((j : ℤ) - M : ℤ) : ℝ) * (π / 2)) =
        (-(((j : ℤ) - M : ℤ) : ℝ) * (π / 2)) + (((j : ℤ) - M : ℤ) : ℝ) * (2 * π) by ring]
      exact Real.sin_add_int_mul_two_pi _ _
    rw [mul_zero, zero_add, key, sub_self, smul_zero]

/-- **Every non-constant mode has zero mean over the torus.** -/
theorem integral_cos_mode (i j : ℕ) :
    ∫ φ in (0)..π, ∫ θ in (0)..(2 * π), Real.cos (ang i j θ φ) =
      if i = N ∧ j = M then 2 * π ^ 2 else 0 := by
  simp_rw [integral_ang_θ]
  by_cases hi : i = N
  · simp only [hi, ite_true, true_and, intervalIntegral.integral_const_mul, integral_psi_mode]
    split_ifs <;> ring
  · simp [hi]

/-- Continuity of a Fourier mode on the torus. -/
theorem continuous_mode (i j : ℕ) : Continuous fun p : ℝ × ℝ => Real.cos (ang i j p.1 p.2) := by
  unfold ang psi; fun_prop

/-- **`g` has zero mean**: `∫∫ g = 0`. -/
theorem integral_gF : ∫ φ in (0)..π, ∫ θ in (0)..(2 * π), gF θ φ = 0 := by
  have hint : ∀ (φ : ℝ) (i j : ℕ), IntervalIntegrable
      (fun θ => (tG i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)) MeasureTheory.volume 0 (2 * π) :=
    fun φ i j => by
      apply Continuous.intervalIntegrable; unfold ang psi; fun_prop
  have hθ : ∀ φ, ∫ θ in (0)..(2 * π), gF θ φ = ∑ i ∈ range (2 * N + 1),
      ∑ j ∈ range (2 * M + 1), (tG i j : ℝ) / 2 ^ pS *
        (if i = N then 2 * π * Real.cos (((j : ℝ) - M) * psi φ) else 0) := by
    intro φ
    unfold gF
    rw [intervalIntegral.integral_finsetSum (f := fun i θ => ∑ j ∈ range (2 * M + 1),
      (tG i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)) fun i _ => by
        apply Continuous.intervalIntegrable; unfold ang psi; fun_prop]
    refine sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun j θ =>
      (tG i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)) fun j _ => hint φ i j]
    refine sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_ang_θ]
  simp_rw [hθ]
  have hint2 : ∀ (i j : ℕ), IntervalIntegrable (fun φ => (tG i j : ℝ) / 2 ^ pS *
      (if i = N then 2 * π * Real.cos (((j : ℝ) - M) * psi φ) else 0))
      MeasureTheory.volume 0 π := fun i j => by
    apply Continuous.intervalIntegrable
    split_ifs
    · unfold psi; fun_prop
    · fun_prop
  rw [intervalIntegral.integral_finsetSum (f := fun i φ => ∑ j ∈ range (2 * M + 1),
    (tG i j : ℝ) / 2 ^ pS * (if i = N then 2 * π * Real.cos (((j : ℝ) - M) * psi φ) else 0))
    fun i _ => by
      apply Continuous.intervalIntegrable
      by_cases hi : i = N <;> simp only [hi, ite_true, ite_false]
      · unfold psi; fun_prop
      · fun_prop]
  refine sum_eq_zero fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun j φ => (tG i j : ℝ) / 2 ^ pS *
    (if i = N then 2 * π * Real.cos (((j : ℝ) - M) * psi φ) else 0)) fun j _ => hint2 i j]
  refine sum_eq_zero fun j _ => ?_
  rw [intervalIntegral.integral_const_mul]
  by_cases hi : i = N
  · subst hi
    simp only [ite_true, intervalIntegral.integral_const_mul, integral_psi_mode]
    by_cases hj : j = M
    · subst hj; simp [tG_centre]
    · simp [hj]
  · simp [hi]

/-! ## Continuity of the torsion -/

section Continuity
variable {X : Type*} [TopologicalSpace X] {f g : X → ℝ}

/-- Continuity of `R` along continuous angles. -/
theorem continuous_torusR' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => torusR (f x) (g x) := by unfold torusR ang psi; fun_prop
/-- Continuity of `z` along continuous angles. -/
theorem continuous_torusZ' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => torusZ (f x) (g x) := by unfold torusZ ang psi; fun_prop
/-- Continuity of `∂_θ R` along continuous angles. -/
theorem continuous_torusRθ' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => torusRθ (f x) (g x) := by unfold torusRθ ang psi; fun_prop
/-- Continuity of `∂_θ z` along continuous angles. -/
theorem continuous_torusZθ' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => torusZθ (f x) (g x) := by unfold torusZθ ang psi; fun_prop
/-- Continuity of `g` along continuous angles. -/
theorem continuous_gF' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => gF (f x) (g x) := by unfold gF ang psi; fun_prop

/-- Continuity of the atoms on the torus. -/
theorem continuous_aval' (k : ℕ) (hf : Continuous f) (hg : Continuous g) : Continuous fun x =>
    aval k (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x)) (Real.sin (2 * g x)) := by
  unfold aval
  refine Ex.continuous_eval (fun i => ?_) (atom k)
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp only [xB, envB]
  · exact (continuous_torusR' hf hg).sub continuous_const
  · exact continuous_torusZ' hf hg
  · fun_prop
  · fun_prop
  all_goals exact continuous_const

/-- Continuity of `D` on the torus. -/
theorem continuous_Dfun' (hf : Continuous f) (hg : Continuous g) : Continuous fun x =>
    Dfun (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x)) (Real.sin (2 * g x)) := by
  have h := continuous_aval' 0 hf hg
  simp only [aval_Dl] at h
  have e : (fun x => Dfun (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
      (Real.sin (2 * g x))) = fun x => (16 * Dfun (torusR (f x) (g x)) (torusZ (f x) (g x))
      (Real.cos (2 * g x)) (Real.sin (2 * g x))) / 16 := by
    funext x; ring
  rw [e]; exact h.div_const 16

/-- **The torsion density is continuous** (composed with continuous angle functions). -/
theorem continuous_T0' (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => T0 (f x) (g x) := by
  have hA : ∀ k, Continuous fun x => aval k (torusR (f x) (g x)) (torusZ (f x) (g x))
      (Real.cos (2 * g x)) (Real.sin (2 * g x)) := fun k => continuous_aval' k hf hg
  have h0 : ∀ x, aval 0 (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
      (Real.sin (2 * g x)) ≠ 0 := fun x => (aval0_torus_pos (f x) (g x)).ne'
  have h02 : ∀ x, aval 0 (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
      (Real.sin (2 * g x)) ^ 2 ≠ 0 := fun x => pow_ne_zero 2 (h0 x)
  have hden : ∀ x, Dfun (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
      (Real.sin (2 * g x)) / torusR (f x) (g x) ^ 3 * (torusRθ (f x) (g x) * torusZ (f x) (g x) -
        torusZθ (f x) (g x) * (torusR (f x) (g x) - 1)) ^ 2 ≠ 0 := by
    intro x
    have hw := wdens_pos (f x) (g x)
    have hW : torusRθ (f x) (g x) * torusZ (f x) (g x) -
        torusZθ (f x) (g x) * (torusR (f x) (g x) - 1) = -wind (f x) (g x) := by unfold wind; ring
    rw [hW]
    have := wind_pos (f x) (g x)
    exact mul_ne_zero hw.ne' (pow_ne_zero 2 (by linarith))
  have hR := continuous_torusR' hf hg
  have hZ := continuous_torusZ' hf hg
  have hdX : ∀ k l m, Continuous fun x =>
      (aval k (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x)) (Real.sin (2 * g x)) *
          aval 0 (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
            (Real.sin (2 * g x)) -
        aval l (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x)) (Real.sin (2 * g x)) *
          aval m (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
            (Real.sin (2 * g x))) /
        aval 0 (torusR (f x) (g x)) (torusZ (f x) (g x)) (Real.cos (2 * g x))
          (Real.sin (2 * g x)) ^ 2 :=
    fun k l m => Continuous.div (((hA k).mul (hA 0)).sub ((hA l).mul (hA m))) ((hA 0).pow 2) h02
  unfold T0 torsion XR XZ dXRR dXRz dXZR dXZz
  refine Continuous.div ?_ ?_ hden
  · refine Continuous.sub (Continuous.mul (Continuous.sub ((hA 3).div (hA 0) h0)
      (Continuous.add (Continuous.mul ?_ (hR.sub continuous_const))
        (Continuous.mul ?_ hZ))) hZ)
      (Continuous.mul (Continuous.sub ((hA 6).div (hA 0) h0)
      (Continuous.add (Continuous.mul ?_ (hR.sub continuous_const))
        (Continuous.mul ?_ hZ))) (hR.sub continuous_const))
    all_goals exact hdX _ _ _
  · refine Continuous.mul ((continuous_Dfun' hf hg).div (hR.pow 3) fun x => ?_) ?_
    · exact pow_ne_zero 3 (by linarith [(torusR_bounds (f x) (g x)).1])
    · exact (((continuous_torusRθ' hf hg).mul hZ).sub ((continuous_torusZθ' hf hg).mul
        (hR.sub continuous_const))).pow 2

end Continuity

/-- The torsion density is continuous on the torus. -/
theorem continuous_T0 : Continuous fun p : ℝ × ℝ => T0 p.1 p.2 :=
  continuous_T0' continuous_fst continuous_snd

/-! ## The twist -/

/-- **The twist of torus A**: the average torsion of the symplectic frame satisfies
`⟨T₀⟩ ≥ 3/10`, in particular the non-degeneracy condition `⟨T₀⟩ ≠ 0` holds with a positive sign.
-/
theorem torusA_twist : 3 / 10 ≤ torusAvg T0 := by
  have hpi : 0 < π := Real.pi_pos
  have hcθ : ∀ φ : ℝ, Continuous fun θ => T0 θ φ := fun φ =>
    continuous_T0' continuous_id continuous_const
  have hgθ : ∀ φ : ℝ, Continuous fun θ => gF θ φ := fun φ =>
    continuous_gF' continuous_id continuous_const
  have hinner : ∀ φ, ∫ θ in (0)..(2 * π), (3 / 10 - gF θ φ) ≤
      ∫ θ in (0)..(2 * π), T0 θ φ := by
    intro φ
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ fun θ _ => ?_
    · exact (continuous_const.sub (hgθ φ)).intervalIntegrable _ _
    · exact (hcθ φ).intervalIntegrable _ _
    · linarith [torusA_torsion_shifted θ φ]
  have hcT : Continuous fun φ => ∫ θ in (0)..(2 * π), T0 θ φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun φ θ => T0 θ φ) (continuous_T0' continuous_snd continuous_fst) _ _
  have hG2 : Continuous fun p : ℝ × ℝ => 3 / 10 - gF p.2 p.1 :=
    continuous_const.sub (continuous_gF' continuous_snd continuous_fst)
  have hcG : Continuous fun φ => ∫ θ in (0)..(2 * π), (3 / 10 - gF θ φ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun φ θ => 3 / 10 - gF θ φ) hG2 _ _
  have hmono : ∫ φ in (0)..π, ∫ θ in (0)..(2 * π), (3 / 10 - gF θ φ) ≤
      ∫ φ in (0)..π, ∫ θ in (0)..(2 * π), T0 θ φ :=
    intervalIntegral.integral_mono_on hpi.le (hcG.intervalIntegrable _ _)
      (hcT.intervalIntegrable _ _) fun φ _ => hinner φ
  have hlow : ∫ φ in (0)..π, ∫ θ in (0)..(2 * π), (3 / 10 - gF θ φ) = 3 / 10 * (2 * π ^ 2) := by
    have e : ∀ φ, ∫ θ in (0)..(2 * π), (3 / 10 - gF θ φ) =
        3 / 10 * (2 * π) - ∫ θ in (0)..(2 * π), gF θ φ := by
      intro φ
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((hgθ φ).intervalIntegrable _ _), intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    simp_rw [e]
    have hcg : Continuous fun φ => ∫ θ in (0)..(2 * π), gF θ φ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun φ θ => gF θ φ) (continuous_gF' continuous_snd continuous_fst) _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcg.intervalIntegrable _ _),
      integral_gF]
    simp; ring
  unfold torusAvg
  rw [le_div_iff₀ (by positivity)]
  linarith

end PlasmaLean.Design.KamTorusA.Frame
