/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.SectionStokes
public import PlasmaLean.Design.LandremanFamily2FluxLabels

/-!
# Landreman family 2 carries a positive net toroidal current; it fails clause C1 (Q-18)

Family 2 of M. Landreman, arXiv:2609.26742 v2, §3 (`ε = 1/4`, `S = 4`, parameter `λ > 0`), in
the coordinates `(k, χ, ζ)` of `LandremanFamily2Coords` (`ψ = k²/2`).

Section flux:
* `torCurrent_eq_netToroidalCurrent`: the compiled `torCurrent μ₀ λ k₀` (flux of
  `J = (∇ × B)/μ₀` through the toroidal cross-section `ζ = 0` inside the surface `ψ = k₀²/2`) is
  the contract's section flux `netToroidalCurrent μ₀ (field (1/4) 4 λ) (coordMap λ) 0 k₀`
  (`rfl`).
* `curK_pos`: `curK λ (1/4) 4 k₀ = ∫₀^{k₀} κ (F₁/2 + E/λ²)/(2π) dκ > 0` for `0 < k₀ < 1`
  (`F1_pos`, `Eint_pos`). `curK_ge_curInf`: `curK ≥ curInf k₀ = ∫₀^{k₀} κ F₁/(4π) dκ > 0`,
  a lower bound independent of `λ` (the current does not vanish as `λ → ∞`).
* `family2_net_current_pos` (`μ₀ > 0`, `λ > 0`, `0 < k₀ < 19/20`): `I_tor(k₀) > 0`, with
  `I_tor = 2π curK/μ₀` (`torCurrent_eq'`) and `I_tor ≥ 2π curInf/μ₀` (`family2_net_current_ge`);
  `family2_not_currentFree` (section-flux notion).

Clause C1 (Ampère circulation, `loopCurrent`):
* smoothness: `contDiffAt_coordMap` (the coordinate map is `C²` on `0 ≤ k ≤ 19/20`, including the
  magnetic axis `k = 0`) and `contDiffAt_field` (the field is `C¹` on `𝒰`);
* `torCurrent_eq_lineIntegral`: by Stokes' theorem for the regular coordinate section
  (`Theory/Contract/SectionStokes`; matched seams, the inner edge is the axis point),
  `I_tor(k₀) = μ₀⁻¹ ∮ B · dl` around the family-2 loop `loop2 λ k₀ : χ ↦ x(k₀, χ, 0)`, which is
  the poloidal loop at `φ₀ = 0` of the profiles `(loopR, loopZ)` (`poloidalLoop_loopR_loopZ`);
* `family2_loopCurrent_eq`, `family2_loopCurrent_pos`: the C1 current around that loop is
  `I_tor(k₀) > 0`;
* `family2_not_currentFreeTransform(_zero)`: family 2 fails C1 for every `I_max < I_tor(k₀)`, in
  particular `I_max = 0`, on every family containing a surface whose poloidal loop is the
  family-2 loop on some `0 < k₀ < 19/20`, whatever tori and transforms are supplied.

Not done: family 1 (its net current is not computed; `LandremanEquilibrium.current` is
available), the ratio of `I_tor` to the field-producing current, and invariant tori of family 2 in
the cylindrical form of the contract.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanNetCurrent

open Real Set PlasmaLean.Contract PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Labels PlasmaLean.Design.LandremanFamily2FluxLabels
open PlasmaLean.Design.LandremanFamily2Coords
open PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2Surface

/-- The compiled family-2 toroidal current is the contract's section flux through the section
`ζ = 0` of the coordinate map `coordMap λ`. -/
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
`ψ = k₀²/2`, `0 < k₀ < 19/20` (`μ₀ > 0`, `λ > 0`): positive flux through the coordinate section,
equal to the Ampère circulation around the family-2 loop (`family2_loopCurrent_eq`). -/
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

/-- **Family 2 is not section-current-free**: positive section flux through the family-2
coordinate section on any family of sections containing some `0 < k₀ < 19/20` (a section-flux
statement; the C1 statement is `family2_not_currentFreeTransform`). -/
theorem family2_not_currentFree {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀) {K : Set ℝ}
    (hk : k₀ ∈ K) (hk0 : 0 < k₀) (hk1 : k₀ < 19 / 20) :
    ¬ CurrentFree μ₀ (field (1 / 4) 4 lam) (coordMap lam) 0 K := by
  intro h
  have h0 := currentFree_iff.1 h k₀ hk
  rw [← torCurrent_eq_netToroidalCurrent] at h0
  exact (family2_net_current_pos hl hμ hk0 hk1).ne' h0

/-! ## Smoothness of the family-2 coordinates and field -/

/-- `|sin(σ − S)| < 1` on `0 ≤ k ≤ 19/20` (including the axis `k = 0`, where it is `0`). -/
theorem sA_sq_lt_one {p : Space} (hk0 : 0 ≤ p 0) (hk1 : p 0 ≤ 19 / 20) :
    sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ^ 2 < 1 := by
  rcases hk0.lt_or_eq with h | h
  · exact (show Good p from ⟨h, hk1⟩).sA_sq
  · rw [← h]
    simp [sA, Xc, Yc]

/-- `σ(k, χ, ζ)` is `C²` on `0 ≤ k ≤ 19/20` (including the magnetic axis). -/
theorem contDiffAt_sigP {p : Space} (hk0 : 0 ≤ p 0) (hk1 : p 0 ≤ 19 / 20) :
    ContDiffAt ℝ 2 sigP p := by
  have hk : p 0 ^ 2 < 1 := by nlinarith
  have hY : ContDiffAt ℝ 2 (fun q : Space => Yc (q 0) (Real.sin (q 1))) p := by
    unfold Yc; fun_prop
  have hX : ContDiffAt ℝ 2 (fun q : Space => Xc (q 0) (Real.cos (q 1))) p := by
    unfold Xc; fun_prop
  have hch : ContDiffAt ℝ 2 (fun q : Space => chc (1 / 4) (Real.sin (2 * q 2))) p := by
    unfold chc nuc; fun_prop
  have hsh : ContDiffAt ℝ 2 (fun q : Space => shc (1 / 4) (Real.sin (2 * q 2))) p := by
    unfold shc nuc; fun_prop
  have hk0' : ContDiffAt ℝ 2 (fun q : Space => q 0) p := by fun_prop
  have hcc : ContDiffAt ℝ 2 (fun q : Space => cc (q 0) (Real.sin (q 1))) p := by
    refine (contDiffAt_const.sub (hY.pow 2)).sqrt ?_
    have := cc_sq (k := p 0) (Real.sin_sq_add_cos_sq (p 1)) hk
    have := cc_pos (k := p 0) (Real.sin_sq_add_cos_sq (p 1)) hk
    exact (by nlinarith : (0 : ℝ) < 1 - Yc (p 0) (Real.sin (p 1)) ^ 2).ne'
  have hT : ContDiffAt ℝ 2 (fun q : Space => Tc (1 / 4) (q 0) (Real.sin (2 * q 2))) p := by
    refine ((hch.pow 2).sub (hk0'.pow 2)).sqrt ?_
    have := one_le_chc (ε := 1 / 4) (s2 := Real.sin (2 * p 2))
    exact (by nlinarith : (0 : ℝ) < chc (1 / 4) (Real.sin (2 * p 2)) ^ 2 - p 0 ^ 2).ne'
  have hT0 : ContDiffAt ℝ 2
      (fun q : Space => T0c (1 / 4) (q 0) (Real.sin (q 1)) (Real.sin (2 * q 2))) p :=
    (hch.pow 2).sub (hY.pow 2)
  have hA : ContDiffAt ℝ 2
      (fun q : Space => sA (1 / 4) (q 0) (Real.sin (q 1)) (Real.cos (q 1))
        (Real.sin (2 * q 2))) p :=
    (((hcc.mul hch).mul hX).add ((hY.mul hsh).mul hT)).div hT0
      (T0_pos (Real.sin_sq_add_cos_sq (p 1)) hk).ne'
  have hsA := sA_sq_lt_one hk0 hk1
  have hne1 : sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ≠ -1 := by
    intro h; rw [h] at hsA; norm_num at hsA
  have hne2 : sA (1 / 4) (p 0) (Real.sin (p 1)) (Real.cos (p 1)) (Real.sin (2 * p 2)) ≠ 1 := by
    intro h; rw [h] at hsA; norm_num at hsA
  have h := ContDiffAt.comp (g := Real.arcsin) p (Real.contDiffAt_arcsin (n := 2) hne1 hne2) hA
  exact contDiffAt_const.add h

/-- `a_c(σ)` and `b_c(σ)` are `C²` for `σ > 0`. -/
theorem contDiffAt_aC_bC {σ : ℝ} (hσ : 0 < σ) :
    ContDiffAt ℝ 2 (aC (1 / 4)) σ ∧ ContDiffAt ℝ 2 (bC (1 / 4)) σ := by
  have hh : ContDiffAt ℝ 2 (hC (1 / 4)) σ := by
    change ContDiffAt ℝ 2 (fun S : ℝ => √(4 * S ^ 2 + (1 / 4 : ℝ) ^ 2)) σ
    exact (by fun_prop : ContDiffAt ℝ 2 (fun S : ℝ => 4 * S ^ 2 + (1 / 4 : ℝ) ^ 2) σ).sqrt
      (by positivity)
  have hgt := hC_gt (ε := 1 / 4) hσ
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hgt
  refine ⟨?_, ?_⟩
  · change ContDiffAt ℝ 2 (fun S : ℝ => √((hC (1 / 4) S - 1 / 4) / 2)) σ
    exact ((hh.sub contDiffAt_const).div_const 2).sqrt (by linarith)
  · change ContDiffAt ℝ 2 (fun S : ℝ => √((hC (1 / 4) S + 1 / 4) / 2)) σ
    exact ((hh.add contDiffAt_const).div_const 2).sqrt (by linarith)

/-- **The family-2 coordinate map is `C²`** on `0 ≤ k ≤ 19/20`, including the magnetic axis. -/
theorem contDiffAt_coordMap (lam : ℝ) {p : Space} (hk0 : 0 ≤ p 0) (hk1 : p 0 ≤ 19 / 20) :
    ContDiffAt ℝ 2 (coordMap lam) p := by
  have hσ := contDiffAt_sigP hk0 hk1
  obtain ⟨ha, hb⟩ := contDiffAt_aC_bC (sigP_pos p)
  have hks : |p 0 * Real.sin (p 1)| < 1 := by
    rw [abs_mul, abs_of_nonneg hk0]
    nlinarith [Real.abs_sin_le_one (p 1), abs_nonneg (Real.sin (p 1))]
  have hne1 : p 0 * Real.sin (p 1) ≠ -1 := fun h => by rw [h] at hks; norm_num at hks
  have hne2 : p 0 * Real.sin (p 1) ≠ 1 := fun h => by rw [h] at hks; norm_num at hks
  refine (contDiffAt_piLp 2).2 fun i => ?_
  fin_cases i
  · change ContDiffAt ℝ 2 (fun q : Space => aC (1 / 4) (sigP q) * Real.cos (q 2)) p
    exact (ha.comp p hσ).mul (by fun_prop)
  · change ContDiffAt ℝ 2 (fun q : Space => bC (1 / 4) (sigP q) * Real.sin (q 2)) p
    exact (hb.comp p hσ).mul (by fun_prop)
  · change ContDiffAt ℝ 2 (fun q : Space => -Real.arcsin (q 0 * Real.sin (q 1)) / lam) p
    exact (ContDiffAt.comp (g := Real.arcsin) p (Real.contDiffAt_arcsin (n := 2) hne1 hne2)
      (by fun_prop : ContDiffAt ℝ 2 (fun q : Space => q 0 * Real.sin (q 1)) p)).neg.div_const lam

/-- **The family-2 field is `C¹`** on the smooth region `𝒰`. -/
theorem contDiffAt_field (lam : ℝ) {x : Space} (hx : x ∈ U (1 / 4)) :
    ContDiffAt ℝ 1 (field (1 / 4) 4 lam) x := by
  have hZr : ContDiffAt ℝ 1 (Zr (1 / 4)) x := by
    change ContDiffAt ℝ 1 (fun y : Space => (y 0 ^ 2 + y 1 ^ 2) ^ 2 + 1 / 4 * (y 0 ^ 2 - y 1 ^ 2)) x
    fun_prop
  have hZi : ContDiffAt ℝ 1 (Zi (1 / 4)) x := by
    change ContDiffAt ℝ 1 (fun y : Space => 2 * (1 / 4) * y 0 * y 1) x
    fun_prop
  have hMo : ContDiffAt ℝ 1 (Mo (1 / 4)) x := by
    change ContDiffAt ℝ 1 (fun y => √(Zr (1 / 4) y ^ 2 + Zi (1 / 4) y ^ 2)) x
    refine ((hZr.pow 2).add (hZi.pow 2)).sqrt ?_
    have h := Mo_pos hx
    exact (Real.sqrt_pos.1 h).ne'
  have hsg : ContDiffAt ℝ 1 (sg (1 / 4)) x := by
    change ContDiffAt ℝ 1 (fun y => √((Mo (1 / 4) y + Zr (1 / 4) y) / 2)) x
    refine ((hMo.add hZr).div_const 2).sqrt ?_
    have : 0 < Mo (1 / 4) x + Zr (1 / 4) x := hx
    exact (by linarith : (0 : ℝ) < (Mo (1 / 4) x + Zr (1 / 4) x) / 2).ne'
  have hnu : ContDiffAt ℝ 1 (nu (1 / 4)) x := by
    change ContDiffAt ℝ 1 (fun y : Space => 1 / 4 * y 0 * y 1 / sg (1 / 4) y) x
    exact (by fun_prop : ContDiffAt ℝ 1 (fun y : Space => 1 / 4 * y 0 * y 1) x).div hsg
      (sg_pos hx).ne'
  have hcz : ContDiffAt ℝ 1 (cz lam) x := by unfold cz; fun_prop
  have hsz : ContDiffAt ℝ 1 (sz lam) x := by unfold sz; fun_prop
  have huR : ContDiffAt ℝ 1 (uR (1 / 4) 4 lam) x := by unfold uR; fun_prop
  have huI : ContDiffAt ℝ 1 (uI (1 / 4) 4 lam) x := by unfold uI; fun_prop
  have hvR : ContDiffAt ℝ 1 (vR (1 / 4) 4 lam) x := by unfold vR; fun_prop
  have hal : ContDiffAt ℝ 1 (al (1 / 4)) x := by unfold al; fun_prop
  have hbe : ContDiffAt ℝ 1 (be (1 / 4)) x := by unfold be; fun_prop
  have hMq : ContDiffAt ℝ 1 (Mq (1 / 4)) x := by unfold Mq; fun_prop
  have h2Mq : (2 * Mq (1 / 4) x) ≠ 0 := by have := Mq_pos hx; positivity
  refine (contDiffAt_piLp 2).2 fun i => ?_
  fin_cases i
  · change ContDiffAt ℝ 1 (fun y => -(uR (1 / 4) 4 lam y * be (1 / 4) y +
      uI (1 / 4) 4 lam y * al (1 / 4) y) / (2 * Mq (1 / 4) y)) x
    exact (by fun_prop : ContDiffAt ℝ 1 (fun y => -(uR (1 / 4) 4 lam y * be (1 / 4) y +
      uI (1 / 4) 4 lam y * al (1 / 4) y)) x).div (by fun_prop) h2Mq
  · change ContDiffAt ℝ 1 (fun y => (uR (1 / 4) 4 lam y * al (1 / 4) y -
      uI (1 / 4) 4 lam y * be (1 / 4) y) / (2 * Mq (1 / 4) y)) x
    exact (by fun_prop : ContDiffAt ℝ 1 (fun y => uR (1 / 4) 4 lam y * al (1 / 4) y -
      uI (1 / 4) 4 lam y * be (1 / 4) y) x).div (by fun_prop) h2Mq
  · change ContDiffAt ℝ 1 (fun y => -vR (1 / 4) 4 lam y / lam) x
    exact hvR.neg.div_const lam

/-! ## The family-2 loop current (Ampère circulation) and clause C1 -/

/-- The **family-2 poloidal loop** on the surface `ψ = k₀²/2` in the section `ζ = 0`:
`χ ↦ x(k₀, χ, 0)`. -/
@[expose] def loop2 (lam k₀ χ : ℝ) : Space := coordMap lam (coordPt k₀ χ 0)

/-- The cylindrical radius of the family-2 loop (the section `ζ = 0` lies in the half-plane
`y = 0`, `x > 0`). -/
@[expose] def loopR (lam k₀ χ _φ : ℝ) : ℝ := coordMap lam (coordPt k₀ χ 0) 0

/-- The height of the family-2 loop. -/
@[expose] def loopZ (lam k₀ χ _φ : ℝ) : ℝ := coordMap lam (coordPt k₀ χ 0) 2

/-- The family-2 loop is the poloidal loop, at `φ₀ = 0`, of the profiles `(loopR, loopZ)`; so
surface data with this loop exist. -/
theorem poloidalLoop_loopR_loopZ (lam k₀ : ℝ) :
    poloidalLoop (loopR lam k₀) (loopZ lam k₀) 0 = loop2 lam k₀ := by
  funext χ
  ext i
  fin_cases i <;> simp [poloidalLoop, cylPoint, loopR, loopZ, loop2, coordPt]

/-- **Stokes for family 2**: the section flux `torCurrent μ₀ λ k₀` through the coordinate section
`ζ = 0` equals `μ₀⁻¹ ∮ B · dl` around the family-2 loop (`0 ≤ k₀ ≤ 19/20`; the section is regular:
`C²` up to the axis, seams matched, the inner edge is the axis point). -/
theorem torCurrent_eq_lineIntegral (μ₀ lam : ℝ) {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk1 : k₀ ≤ 19 / 20) :
    torCurrent μ₀ lam k₀ = lineIntegral (field (1 / 4) 4 lam) (loop2 lam k₀) (-π) π / μ₀ := by
  rw [torCurrent_eq_netToroidalCurrent]
  refine netToroidalCurrent_eq_lineIntegral_div hk0 (fun k hk χ _ => ?_)
    (fun k _ χ _ => contDiffAt_field lam (coordMap_mem_U lam _)) (fun k => ?_) (fun χ => ?_)
  · exact contDiffAt_coordMap lam (by simpa [coordPt] using hk.1)
      (by simpa [coordPt] using hk.2.trans hk1)
  · simp [coordMap_eq, sigP, zP, coordPt]
  · simp [coordMap_eq, sigP, sigc, sA, Xc, Yc, zP, coordPt]

/-- **The C1 current of family 2**: the net toroidal current `μ₀⁻¹ ∮ B · dl` enclosed by any
poloidal loop equal to the family-2 loop on `ψ = k₀²/2` is the closed form `torCurrent μ₀ λ k₀`. -/
theorem family2_loopCurrent_eq {μ₀ lam k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk1 : k₀ ≤ 19 / 20)
    {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ} (hloop : poloidalLoop R z φ₀ = loop2 lam k₀) :
    loopCurrent μ₀ (field (1 / 4) 4 lam) R z φ₀ = torCurrent μ₀ lam k₀ := by
  rw [torCurrent_eq_lineIntegral μ₀ lam hk0 hk1, loopCurrent, poloidalCirculation, hloop]

/-- **Family 2 encloses a positive net toroidal current**: `μ₀⁻¹ ∮ B · dl > 0` around the
family-2 loop on every surface `0 < k₀ < 19/20`. -/
theorem family2_loopCurrent_pos {lam μ₀ k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀) (hk0 : 0 < k₀)
    (hk1 : k₀ < 19 / 20) :
    0 < loopCurrent μ₀ (field (1 / 4) 4 lam) (loopR lam k₀) (loopZ lam k₀) 0 := by
  rw [family2_loopCurrent_eq hk0.le hk1.le (poloidalLoop_loopR_loopZ lam k₀)]
  exact family2_net_current_pos hl hμ hk0 hk1

/-- **Family 2 fails clause C1**: for any family `S` containing a surface whose poloidal loop is
the family-2 loop on `ψ = k₀²/2`, `0 < k₀ < 19/20`, C1 fails for every `I_max < I_tor(k₀)` (in
particular `I_max = 0`) and every `ι_min`, whatever tori and transforms are supplied. -/
theorem family2_not_currentFreeTransform {lam μ₀ Imax ιmin k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀)
    {S : Set SurfaceData} {s : SurfaceData} (hs : s ∈ S) (hloop : s.loop = loop2 lam k₀)
    (hk0 : 0 < k₀) (hk1 : k₀ < 19 / 20) (hI : Imax < torCurrent μ₀ lam k₀) :
    ¬ CurrentFreeTransform μ₀ (field (1 / 4) 4 lam) S Imax ιmin := by
  refine not_currentFreeTransform_of_current hs ?_
  rw [SurfaceData.current, family2_loopCurrent_eq hk0.le hk1.le hloop,
    abs_of_pos (family2_net_current_pos hl hμ hk0 hk1)]
  exact hI

/-- Special case `I_max = 0`: family 2 is never a current-free (C1) candidate. -/
theorem family2_not_currentFreeTransform_zero {lam μ₀ ιmin k₀ : ℝ} (hl : 0 < lam) (hμ : 0 < μ₀)
    {S : Set SurfaceData} {s : SurfaceData} (hs : s ∈ S) (hloop : s.loop = loop2 lam k₀)
    (hk0 : 0 < k₀) (hk1 : k₀ < 19 / 20) :
    ¬ CurrentFreeTransform μ₀ (field (1 / 4) 4 lam) S 0 ιmin :=
  family2_not_currentFreeTransform hl hμ hs hloop hk0 hk1 (family2_net_current_pos hl hμ hk0 hk1)

end PlasmaLean.Design.LandremanNetCurrent
