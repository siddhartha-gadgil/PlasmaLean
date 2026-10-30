/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.MercierGeneral
public import PlasmaLean.Theory.Stability.BallooningReduction
public import PlasmaLean.Theory.Stability.ScrewPinchModes

/-!
# Strict model audit: Mercier index, ballooning line data, Newcomb mode energy

Added by the first strict audit of the model layer outside `Kernel/` (finding H-1 of
`notes/audit/2026-10-30-repository-audit.md`; record in `notes/audit/2026-10-30-model-audit.md`,
commit `cda8bd0`).

**Mercier** (`Stability.MercierGeneral.mercierIndex`, Landreman–Jorge 2020 eq. (3.1))
* symmetry: the index is invariant under reversal of the field (`sG, sψ, ι', μ₀p'` change sign,
  `V''` and the three surface integrals do not), `mercierIndex_reverseField`; the cylindrical
  reduction in the source module only tests `sG = sψ = 1`;
* counterexample: a magnetic hill with no shear and no `Ξ` is unstable (`mercier_hill_unstable`);
* regression (finding MA-L4): `MercierSurfaceData` does not constrain the signs, so the
  unphysical datum `∫B²/|∇ψ|³ < 0` turns the same hill into "Mercier stable"
  (`mercier_negative_B2_stable`), and `sG = 0` deletes the shear term (`mercier_sG_zero`).

**Ballooning** (`Stability.BallooningReduction.ballooningP/Q`, `LineData`)
* bad curvature has the destabilizing sign: with `μ₀∇p = g (B × k)` and `κ = c (B × k)`,
  `Q = −2ℓ g c |B × k|⁴/|B|⁴` (`ballooningQ_binormal`), so `Q < 0` iff `g c > 0`
  (`ballooningQ_neg_of_bad`, `ballooningQ_pos_of_good`);
* eikonal normalization: `P` and `Q` are both quadratic in `k` (`ballooningP_smul`,
  `ballooningQ_smul`);
* regression (finding MA-L5): `LineData` does not require `k ⊥ B`; a parallel component of `k`
  raises `P` (stabilizing) and leaves `Q` unchanged (`ballooningP_add_parallel`,
  `ballooningQ_add_parallel`). Both downstream lines prove `k ⊥ B` (`family2Line_k_perp`,
  `lnB_inner_lnEik`);
* counterexample: an explicit sheared line with constant bad-curvature drive is not
  `LineData.Stable` (`badLine_not_stable`).

**Newcomb** (`Stability.ScrewPinchModes.ModeStable`, `NewcombReduction`)
* symmetry: `ModeStable` is invariant under `B ↦ −B` (`modeStable_reverseField`);
* regression (finding MA-L6): `ModeStable` does not include radial force balance; a profile
  with `B = 0` and `μ₀ p' = 1` (no equilibrium) is "stable" (`modeStable_nonequilibrium`);
* counterexample: with `B = 0`, `μ₀ p' = −1` the mode `(1, 1)` has negative reduced energy
  (`modeStable_pressure_drive_fails`);
* regression (finding MA-L7): `NewcombReduction` with an empty admissible class holds even for
  the energy `W ≡ −1` (`newcombReduction_empty`), so the interface constrains nothing unless
  the admissible class is the full class of displacements of the mode.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditModel
open Real Set PlasmaLean.Fields PlasmaLean.Stability

/-! ### Mercier index -/

section Mercier
open PlasmaLean.Stability.MercierGeneral

/-- The surface data after reversing the magnetic field (`B, J ↦ −B, −J`): the toroidal flux
`ψ`, `G` and the current function `I` change sign, so `sG, sψ, ι' = dι/dψ` and `μ₀ dp/dψ`
change sign, while `V''`, `B·Ξ`, `|Ξ|²` and `B²` (with `Ξ ↦ −Ξ`) do not. -/
@[expose] def reverseField (d : MercierSurfaceData) : MercierSurfaceData :=
  ⟨-d.sG, -d.sψ, -d.iotaPrime, -d.muPprime, d.Vpp, d.intBXi, d.intXi2, d.intB2⟩

/-- **Field-reversal invariance** of the Mercier index. -/
theorem mercierIndex_reverseField (d : MercierSurfaceData) :
    mercierIndex (reverseField d) = mercierIndex d := by
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket reverseField
  ring

/-- Counterexample: a magnetic hill (`s_ψ μ₀ p' V'' = −1`) without shear and without `Ξ` is
Mercier unstable. -/
theorem mercier_hill_unstable : mercierIndex ⟨1, 1, 0, -1, 1, 0, 0, 1⟩ < 0 := by
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket
  have : 0 < (2 * π) ^ 6 := by positivity
  apply div_neg_of_neg_of_pos _ this
  norm_num

/-- Regression (MA-L4): with the unphysical value `∫ B² dS/|∇ψ|³ = −1` the same hill is
"Mercier stable"; `MercierSurfaceData` imposes no sign condition, so the caller must
establish `intB2 > 0` and `intXi2 ≥ 0`. -/
theorem mercier_negative_B2_stable : MercierStable ⟨1, 1, 0, -1, 1, 0, 0, -1⟩ := by
  unfold MercierStable mercierIndex MercierSurfaceData.shearBracket
    MercierSurfaceData.wellBracket
  have : 0 < (2 * π) ^ 6 := by positivity
  apply div_pos _ this
  norm_num

/-- Regression (MA-L4): `sG = 0` (not a sign) deletes the shear term: the vacuum surface with
shear `ι' = 1` is not Mercier stable, whereas with `sG = 1` it is (`mercierIndex_vacuum`). -/
theorem mercier_sG_zero :
    ¬ MercierStable ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ ∧ MercierStable ⟨1, 1, 1, 0, 0, 0, 0, 1⟩ := by
  refine ⟨fun h => ?_, ?_⟩
  · unfold MercierStable mercierIndex MercierSurfaceData.shearBracket
      MercierSurfaceData.wellBracket at h
    norm_num at h
  · unfold MercierStable
    rw [mercierIndex_vacuum 1 1 1 0 1 (by norm_num)]
    have := pi_pos
    positivity

end Mercier

/-! ### Ballooning coefficients and line data -/

section Ballooning
open PlasmaLean.Stability.BallooningReduction PlasmaLean.Stability.BallooningInfinite

/-- `B × (k + a B) = B × k`. -/
theorem cross_add_parallel (B k : Space) (a : ℝ) : cross B (k + a • B) = cross B k := by
  apply space_ext <;> simp [cross, cross_apply] <;> ring

/-- `B × (c k) = c (B × k)`. -/
theorem cross_smul_right (B k : Space) (c : ℝ) : cross B (c • k) = c • cross B k := by
  apply space_ext <;> simp [cross, cross_apply]

/-- Regression (MA-L5): a component of `k` along `B` increases the bending coefficient `P`. -/
theorem ballooningP_add_parallel {ℓ a : ℝ} {B k : Space} (hℓ : 0 < ℓ) (hB : B ≠ 0) (ha : a ≠ 0)
    (hkB : ⟪k, B⟫ = 0) : ballooningP ℓ B k < ballooningP ℓ B (k + a • B) := by
  have hn : 0 < ‖B‖ := norm_pos_iff.2 hB
  unfold ballooningP
  rw [norm_add_sq_real, inner_smul_right, hkB, norm_smul, Real.norm_eq_abs]
  apply div_lt_div_of_pos_right _ (by positivity)
  have : 0 < (|a| * ‖B‖) ^ 2 := by
    have : 0 < |a| := abs_pos.2 ha
    positivity
  linarith

/-- Regression (MA-L5): the drive `Q` ignores a component of `k` along `B`. -/
theorem ballooningQ_add_parallel (ℓ a : ℝ) (B k gp κ : Space) :
    ballooningQ ℓ B (k + a • B) gp κ = ballooningQ ℓ B k gp κ := by
  rw [ballooningQ, ballooningQ, cross_add_parallel]

/-- `P` is quadratic in the eikonal gradient. -/
theorem ballooningP_smul (ℓ c : ℝ) (B k : Space) :
    ballooningP ℓ B (c • k) = c ^ 2 * ballooningP ℓ B k := by
  unfold ballooningP
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- `Q` is quadratic in the eikonal gradient. -/
theorem ballooningQ_smul (ℓ c : ℝ) (B k gp κ : Space) :
    ballooningQ ℓ B (c • k) gp κ = c ^ 2 * ballooningQ ℓ B k gp κ := by
  unfold ballooningQ
  rw [cross_smul_right, real_inner_smul_left, real_inner_smul_left]
  ring

/-- **Drive for curvature and pressure gradient along the binormal `B × k`**:
`Q = −2ℓ g c |B × k|⁴/|B|⁴` for `μ₀∇p = g (B × k)` and `κ = c (B × k)`. -/
theorem ballooningQ_binormal (ℓ g c : ℝ) (B k : Space) :
    ballooningQ ℓ B k (g • cross B k) (c • cross B k) =
      -(2 * ℓ * g * c * ‖cross B k‖ ^ 4) / ‖B‖ ^ 4 := by
  unfold ballooningQ
  rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- **Bad curvature is destabilizing**: if the curvature and the pressure gradient point the
same way along the binormal (`g c > 0`, i.e. `κ · ∇p > 0`), then `Q < 0`. -/
theorem ballooningQ_neg_of_bad {ℓ g c : ℝ} {B k : Space} (hℓ : 0 < ℓ) (hBk : cross B k ≠ 0)
    (hgc : 0 < g * c) : ballooningQ ℓ B k (g • cross B k) (c • cross B k) < 0 := by
  rw [ballooningQ_binormal]
  have h1 : 0 < ‖cross B k‖ := norm_pos_iff.2 hBk
  have hB : B ≠ 0 := by rintro rfl; exact hBk (by simp [cross])
  have h2 : 0 < ‖B‖ := norm_pos_iff.2 hB
  apply div_neg_of_neg_of_pos _ (by positivity)
  have : 0 < 2 * ℓ * (g * c) * ‖cross B k‖ ^ 4 := by positivity
  linarith

/-- **Good curvature is stabilizing**: `g c < 0` gives `Q > 0`. -/
theorem ballooningQ_pos_of_good {ℓ g c : ℝ} {B k : Space} (hℓ : 0 < ℓ) (hBk : cross B k ≠ 0)
    (hgc : g * c < 0) : 0 < ballooningQ ℓ B k (g • cross B k) (c • cross B k) := by
  rw [ballooningQ_binormal]
  have h1 : 0 < ‖cross B k‖ := norm_pos_iff.2 hBk
  have hB : B ≠ 0 := by rintro rfl; exact hBk (by simp [cross])
  have h2 : 0 < ‖B‖ := norm_pos_iff.2 hB
  apply div_pos _ (by positivity)
  have : 0 < 2 * ℓ * (-(g * c)) * ‖cross B k‖ ^ 4 := by
    have : 0 < -(g * c) := by linarith
    positivity
  linarith

/-- An explicit sheared ballooning line: `ℓ = 1`, `B = e_z`, `k(t) = e_x − t e_y` (secular
growth), and `μ₀∇p = κ = e_y` (bad curvature). -/
@[expose] def badLine : LineData where
  ℓ _ := 1
  B _ := basis 2
  k t := basis 0 - t • basis 1
  gp _ := basis 1
  κ _ := basis 1
  ℓ_pos _ := one_pos
  B_ne _ := by
    intro h
    have := congrArg (fun w : Space => w 2) h
    simp at this
  k_ne t := by
    intro h
    have := congrArg (fun w : Space => w 0) h
    simp at this
  ℓ_cont := continuous_const
  B_cont := continuous_const
  k_cont := continuous_const.sub (continuous_id.smul continuous_const)
  gp_cont := continuous_const
  κ_cont := continuous_const

/-- Bending coefficient of `badLine`: `P = 1 + t²`. -/
theorem badLine_P (t : ℝ) : badLine.P t = 1 + t ^ 2 := by
  simp only [LineData.P, badLine, ballooningP]
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right]
  simp [EuclideanSpace.inner_single_left]

/-- Drive of `badLine`: `Q = −2`. -/
theorem badLine_Q (t : ℝ) : badLine.Q t = -2 := by
  simp only [LineData.Q, badLine, ballooningQ]
  have h1 : ⟪cross (basis 2) (basis 0 - t • basis 1), basis 1⟫ = 1 := by
    simp [cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [h1]
  simp

/-- Counterexample: `badLine` is not ballooning stable (a compactly supported mode far out on
the line has negative energy, since `P ≤ 2t²` and `Q = −2` with `2 + 4·(−2) < 0`). -/
theorem badLine_not_stable : ¬ badLine.Stable := by
  intro hs
  obtain ⟨ξ, ξ', a, b, -, hadm, hneg⟩ := tail_unstable (F := 2) (G := -2) (Θ := 1)
    badLine.P_cont badLine.Q_cont two_pos (by norm_num) one_pos
    (fun x hx => by rw [badLine_P]; nlinarith) (fun x _ => by rw [badLine_Q])
  exact (hs ξ ξ' a b hadm).not_gt hneg

end Ballooning

/-! ### Newcomb mode energy -/

section Newcomb
open PlasmaLean.Stability.ScrewPinchModes

/-- `f` is invariant under `B ↦ −B`. -/
theorem coefF_reverseField (m k : ℝ) (Bz b : ℝ → ℝ) :
    coefF m k (fun r => -Bz r) (fun r => -b r) = coefF m k Bz b := by
  funext r; unfold coefF kpar; ring

/-- `g` is invariant under `B ↦ −B`. -/
theorem coefG_reverseField (μ₀ m k : ℝ) (p' Bz b : ℝ → ℝ) :
    coefG μ₀ m k p' (fun r => -Bz r) (fun r => -b r) = coefG μ₀ m k p' Bz b := by
  funext r; unfold coefG kpar; ring

/-- **Field-reversal invariance** of `ModeStable`. -/
theorem modeStable_reverseField {μ₀ a m k : ℝ} {p' Bz b : ℝ → ℝ} :
    ModeStable μ₀ a m k p' (fun r => -Bz r) (fun r => -b r) ↔ ModeStable μ₀ a m k p' Bz b := by
  unfold ModeStable; rw [coefF_reverseField, coefG_reverseField]

/-- Regression (MA-L6): `ModeStable` holds for the profile `B = 0`, `μ₀ p' = 1`, which violates
radial force balance `p' + (2 Bθ Bθ' + S')/(2μ₀) + Bθ²/(μ₀ r) = 0` (the left side is `1`). -/
theorem modeStable_nonequilibrium {m k : ℝ} (hm : m ≠ 0) :
    ModeStable 1 1 m k (fun _ => 1) (fun _ => 0) (fun _ => 0) ∧
      ∀ r : ℝ, (1 : ℝ) + (2 * 0 * 0 + 0) / (2 * 1) + 0 ^ 2 / (1 * r) ≠ 0 := by
  refine ⟨modeStable_of_g_nonneg hm zero_le_one fun r hr => ?_, fun r => by norm_num⟩
  have := muSq_pos hm k r
  have := hr.1
  simp only [coefG, kpar, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, mul_one, sub_zero]
  positivity

/-- Counterexample: with `B = 0` and `μ₀ p' = −1` the mode `(m, k) = (1, 1)` has negative
reduced energy for `ξ = 1 − r` on `[0, 1]`, so it is not `ModeStable`. -/
theorem modeStable_pressure_drive_fails :
    ¬ ModeStable 1 1 1 1 (fun _ => -1) (fun _ => 0) (fun _ => 0) := by
  intro h
  have hC : PlasmaLean.Stability.C1On (fun r : ℝ => 1 - r) (fun _ => -1) 0 1 :=
    ⟨fun x _ => by simpa using (hasDerivAt_id x).const_sub 1, continuousOn_const⟩
  have h0 := h _ _ hC (by norm_num)
  have hfun : (fun x : ℝ => coefF 1 1 (fun _ => 0) (fun _ => 0) x * (fun _ : ℝ => (-1 : ℝ)) x ^ 2 +
      coefG 1 1 1 (fun _ => -1) (fun _ => 0) (fun _ => 0) x * (fun r : ℝ => 1 - r) x ^ 2) =
      fun x => -(2 * x ^ 2 / (1 + x ^ 2) * (1 - x) ^ 2) := by
    funext x
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    simp only [coefF, coefG, kpar, muSq]
    field_simp
    ring
  have hpos : 0 < ∫ x in (0 : ℝ)..1, 2 * x ^ 2 / (1 + x ^ 2) * (1 - x) ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) zero_lt_one
    · refine Continuous.intervalIntegrable ?_ _ _
      refine Continuous.mul (Continuous.div (by fun_prop) (by fun_prop) fun x => ?_) (by fun_prop)
      positivity
    · have h1 : 0 < x := hx.1
      have h2 : 0 < 1 - x := by linarith [hx.2]
      positivity
  unfold newcombForm at h0
  rw [hfun, intervalIntegral.integral_neg] at h0
  linarith

/-- Regression (MA-L7): with an empty admissible class, `NewcombReduction` holds for the energy
`W ≡ −1`; the interface has content only for the full class of mode displacements. -/
theorem newcombReduction_empty (μ₀ a m k : ℝ) (p' Bz b : ℝ → ℝ) :
    NewcombReduction (fun _ : Unit => (-1 : ℝ)) (fun _ => False) (fun _ => (0, 0)) μ₀ a m k p'
      Bz b where
  scale_pos := ⟨1, one_pos, fun _ hd => hd.elim⟩
  regular _ hd := hd.elim
  wall _ hd := hd.elim

end Newcomb

end PlasmaLean.Sanity.AuditModel
