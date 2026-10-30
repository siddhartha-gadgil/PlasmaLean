/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import PlasmaLean.Design.LandremanFamily2FluxLabels

/-!
# Landreman family 2 carries a positive net toroidal current; it fails clause C1 (Q-18)

Family 2 of M. Landreman, arXiv:2609.26742 v2, §3 (`ε = 1/4`, `S = 4`, parameter `λ > 0`), in
the coordinates `(k, χ, ζ)` of `LandremanFamily2Coords` (`ψ = k²/2`).

* `torCurrent_eq_netToroidalCurrent`: the compiled `torCurrent μ₀ λ k₀` (current of
  `J = (∇ × B)/μ₀` through the toroidal cross-section `ζ = 0` inside the surface `ψ = k₀²/2`)
  **is** the contract quantity `netToroidalCurrent μ₀ (field (1/4) 4 λ) (coordMap λ) 0 k₀`
  (`rfl`).
* `curK_pos`: `curK λ (1/4) 4 k₀ = ∫₀^{k₀} κ (F₁/2 + E/λ²)/(2π) dκ > 0` for `0 < k₀ < 1`
  (`F1_pos`, `Eint_pos`). `curK_ge_curInf`: `curK ≥ curInf k₀ = ∫₀^{k₀} κ F₁/(4π) dκ > 0`,
  a lower bound independent of `λ` (the current does not vanish as `λ → ∞`).
* `family2_net_current_pos` (`μ₀ > 0`, `λ > 0`, `0 < k₀ < 19/20`): `I_tor(k₀) > 0`, with
  `I_tor = 2π curK/μ₀` (`torCurrent_eq'`) and `I_tor ≥ 2π curInf/μ₀` (`family2_net_current_ge`).
* `family2_not_currentFree`, `family2_not_currentFreeTransform`: family 2 is not current-free
  on any surface `0 < k₀ < 19/20`, so it fails C1 for every `I_max < I_tor(k₀)`, in particular
  for `I_max = 0`, whatever tori and transforms are supplied.

Not done: family 1 (its net current is not computed; `LandremanEquilibrium.current` is
available), and the ratio of `I_tor` to the field-producing current.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanNetCurrent

open Real Set PlasmaLean.Contract PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Labels PlasmaLean.Design.LandremanFamily2FluxLabels
open PlasmaLean.Design.LandremanFamily2Coords

/-- The compiled family-2 toroidal current is the contract's net toroidal current through the
section `ζ = 0` of the coordinate map `coordMap λ`. -/
theorem torCurrent_eq_netToroidalCurrent (μ₀ lam k₀ : ℝ) :
    torCurrent μ₀ lam k₀ = netToroidalCurrent μ₀ (field (1 / 4) 4 lam) (coordMap lam) 0 k₀ :=
  rfl

/-- The `λ`-independent part of the current label: `curInf k₀ = ∫₀^{k₀} κ F₁(κ)/(4π) dκ`. -/
@[expose] def curInf (k₀ : ℝ) : ℝ := ∫ κ in (0 : ℝ)..k₀, κ * (F1 (1 / 4) 4 κ / 2) / (2 * π)

/-- The integrand of `curK` is continuous on `(-1, 1)`. -/
theorem continuousOn_curK_integrand (lam : ℝ) :
    ContinuousOn (fun κ => κ * (F1 (1 / 4) 4 κ / 2 + Eint κ / lam ^ 2) / (2 * π))
      (Ioo (-1 : ℝ) 1) :=
  (continuousOn_id.mul (((continuousOn_F1 (by norm_num)).div_const _).add
    (continuousOn_Eint.div_const _))).div_const _

/-- The integrand of `curInf` is continuous on `(-1, 1)`. -/
theorem continuousOn_curInf_integrand :
    ContinuousOn (fun κ => κ * (F1 (1 / 4) 4 κ / 2) / (2 * π)) (Ioo (-1 : ℝ) 1) :=
  (continuousOn_id.mul ((continuousOn_F1 (by norm_num)).div_const _)).div_const _

/-- `[0, k₀] ⊆ (-1, 1)` for `0 ≤ k₀ < 1`. -/
theorem uIcc_sub {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk1 : k₀ < 1) : uIcc 0 k₀ ⊆ Ioo (-1 : ℝ) 1 := by
  rw [uIcc_of_le hk0]
  exact fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- `curInf k₀ > 0` for `0 < k₀ < 1`. -/
theorem curInf_pos {k₀ : ℝ} (hk0 : 0 < k₀) (hk1 : k₀ < 1) : 0 < curInf k₀ := by
  unfold curInf
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuousOn_curInf_integrand.mono (uIcc_sub hk0.le hk1)).intervalIntegrable)
    (fun κ hκ => ?_) hk0
  have hF := F1_pos (ε := 1 / 4) (S := 4) (by norm_num)
    (k := κ) ⟨by linarith [hκ.1], by linarith [hκ.2]⟩
  have := hκ.1
  positivity

/-- **`curK ≥ curInf`**: the current label is bounded below independently of `λ`. -/
theorem curK_ge_curInf (lam : ℝ) {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk1 : k₀ < 1) :
    curInf k₀ ≤ curK lam (1 / 4) 4 k₀ := by
  unfold curInf curK
  refine intervalIntegral.integral_mono_on hk0
    ((continuousOn_curInf_integrand.mono (uIcc_sub hk0 hk1)).intervalIntegrable)
    ((continuousOn_curK_integrand lam).mono (uIcc_sub hk0 hk1)).intervalIntegrable
    (fun κ hκ => ?_)
  have hκ0 := hκ.1
  have hE : 0 ≤ Eint κ / lam ^ 2 :=
    div_nonneg (Eint_pos ⟨by linarith [hκ.1], by linarith [hκ.2]⟩).le (sq_nonneg _)
  have h2 : 0 < 2 * π := by positivity
  rw [div_le_div_iff_of_pos_right h2]
  nlinarith

/-- **`curK > 0`** for `0 < k₀ < 1` (every `λ`). -/
theorem curK_pos (lam : ℝ) {k₀ : ℝ} (hk0 : 0 < k₀) (hk1 : k₀ < 1) :
    0 < curK lam (1 / 4) 4 k₀ :=
  (curInf_pos hk0 hk1).trans_le (curK_ge_curInf lam hk0.le hk1)

/-- The net toroidal current of family 2 in closed form: `I_tor = 2π curK/μ₀`. -/
theorem torCurrent_eq' {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : μ₀ ≠ 0) (hk0 : 0 ≤ k₀)
    (hk1 : k₀ < 19 / 20) : torCurrent μ₀ lam k₀ = 2 * π * curK lam (1 / 4) 4 k₀ / μ₀ := by
  have h := torCurrent_eq hl hμ hk0 hk1
  field_simp at h ⊢
  linarith

/-- **Q-18: the net toroidal current of Landreman family 2 is positive** on every surface
`ψ = k₀²/2`, `0 < k₀ < 19/20` (`μ₀ > 0`, `λ > 0`). -/
theorem family2_net_current_pos {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀) (hk0 : 0 < k₀)
    (hk1 : k₀ < 19 / 20) : 0 < torCurrent μ₀ lam k₀ := by
  rw [torCurrent_eq' hl hμ.ne' hk0.le hk1]
  have := curK_pos lam hk0 (by linarith)
  positivity

/-- The net toroidal current of family 2 is at least `2π curInf(k₀)/μ₀`, uniformly in `λ > 0`. -/
theorem family2_net_current_ge {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀) (hk0 : 0 ≤ k₀)
    (hk1 : k₀ < 19 / 20) : 2 * π * curInf k₀ / μ₀ ≤ torCurrent μ₀ lam k₀ := by
  rw [torCurrent_eq' hl hμ.ne' hk0 hk1]
  have := curK_ge_curInf lam hk0 (by linarith)
  gcongr

/-- **Family 2 is not current-free** on any family of surfaces containing some
`0 < k₀ < 19/20`. -/
theorem family2_not_currentFree {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀) {K : Set ℝ}
    (hk : k₀ ∈ K) (hk0 : 0 < k₀) (hk1 : k₀ < 19 / 20) :
    ¬ CurrentFree μ₀ (field (1 / 4) 4 lam) (coordMap lam) 0 K := by
  intro h
  have h0 := currentFree_iff.1 h k₀ hk
  rw [← torCurrent_eq_netToroidalCurrent] at h0
  exact (family2_net_current_pos hl hμ hk0 hk1).ne' h0

/-- **Family 2 fails clause C1**: for any family `S` of surfaces containing one whose current is
measured through the family-2 section `ζ = 0` up to `0 < k₀ < 19/20`, C1 fails for every
`I_max < I_tor(k₀)` (in particular `I_max = 0`) and every `ι_min`, whatever tori and transforms are
supplied. -/
theorem family2_not_currentFreeTransform {lam μ₀ Imax ιmin : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀)
    {S : Set SurfaceData} {s : SurfaceData} (hs : s ∈ S) (hX : s.X = coordMap lam)
    (hζ : s.ζ₀ = 0) (hk0 : 0 < s.k₀) (hk1 : s.k₀ < 19 / 20)
    (hI : Imax < torCurrent μ₀ lam s.k₀) :
    ¬ CurrentFreeTransform μ₀ (field (1 / 4) 4 lam) S Imax ιmin := by
  refine not_currentFreeTransform_of_current hs ?_
  rw [hX, hζ, ← torCurrent_eq_netToroidalCurrent,
    abs_of_pos (family2_net_current_pos hl hμ hk0 hk1)]
  exact hI

/-- Special case `I_max = 0`: family 2 is never a current-free (C1) candidate. -/
theorem family2_not_currentFreeTransform_zero {lam μ₀ ιmin : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀)
    {S : Set SurfaceData} {s : SurfaceData} (hs : s ∈ S) (hX : s.X = coordMap lam)
    (hζ : s.ζ₀ = 0) (hk0 : 0 < s.k₀) (hk1 : s.k₀ < 19 / 20) :
    ¬ CurrentFreeTransform μ₀ (field (1 / 4) 4 lam) S 0 ιmin :=
  family2_not_currentFreeTransform hl hμ hs hX hζ hk0 hk1
    (family2_net_current_pos hl hμ hk0 hk1)

end PlasmaLean.Design.LandremanNetCurrent
