/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuExact
public import PlasmaLean.Certificates.KernelFact

/-!
# Perturbation in the gyro-length: the `μ > 0` passing fields of a two-parameter box

The `μ > 0` passing guiding-centre field `gcFlowMu ρ λ` (`Design/RationalStellaratorGCMuFlow`) is
**affine in the gyro-length** `ρ = ρ_E` (`ρ_E = m√(2E/m)/(q B₀R₀)` in model units):
`D̃ = D + ρ F Y_D`, `ñ_R = n_R + ρ F Y_R`, `ñ_z = n_z + ρ F Y_z` with `F = F(λ)` and
`Y = ½ W³ κ`. So the fields at `ρ` and at `ρ₀ = 1/256` (where the pitch-angle family
`Design/RationalStellaratorGCMu*` is certified) differ by `(ρ − ρ₀)` times the correction
`F Y` (`eval_gcDM_sub`, `pdS_gcDM_sub`, …, `resR_gcFlowMu_sub`, `resZ_gcFlowMu_sub`).

This module provides:

* the **box half-width** `dRhoB = 2⁻⁸⁶` and the box `rhoBox = [1/256 − 2⁻⁸⁶, 1/256]` of
  gyro-lengths (relative width `2⁻⁷⁸`);
* uniform strip bounds of the corrections `F Y_D, F Y_R, F Y_z` and of their `u`- and
  `z`-derivatives at every torus whose variables are bounded by `a ≤ aTQ`, for every
  `|λ| ≤ 1/16` (`Bd_corr_eval`, `Bd_corr_deriv`, rational majorants evaluated by the kernel:
  `‖F Y_D‖ ≤ 177`, …, `‖∂_u (F Y_z)‖ ≤ 30768`);
* the bookkeeping predicate `DBd r x x' B d` (`‖x‖ ≤ B`, `‖x' − x‖ ≤ d`) with its sum, difference
  and product rules, used to propagate the perturbation through the torsion numerator.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `eval_gcDM_sub_self`: at `ρ = 1/256` the difference vanishes; `DBd.of_eq`: a pair
of equal elements has difference bound `0`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex

/-! ## The box -/

/-- The half-width of the box of gyro-lengths, `2⁻⁸⁶`. -/
def dRhoB : ℝ := 1 / 2 ^ 86

/-- **The box of gyro-lengths** `[1/256 − 2⁻⁸⁶, 1/256]` (model units). -/
def rhoBox : Set ℝ := Set.Icc (1 / 256 - dRhoB) (1 / 256)

/-- Points of the box are within `dRhoB` of `1/256`. -/
theorem abs_sub_le_of_rhoBox {ρ : ℝ} (h : ρ ∈ rhoBox) : |ρ - 1 / 256| ≤ dRhoB := by
  obtain ⟨h1, h2⟩ := h
  rw [abs_le]; constructor <;> linarith

/-- Points of the box have `|ρ| ≤ 1/256`. -/
theorem abs_le_of_rhoBox {ρ : ℝ} (h : ρ ∈ rhoBox) : |ρ| ≤ 1 / 256 := by
  obtain ⟨h1, h2⟩ := h
  have : (0 : ℝ) ≤ 1 / 256 - dRhoB := by norm_num [dRhoB]
  rw [abs_of_nonneg (by linarith)]; exact h2

/-- **Sanity**: `1/256` lies in the box. -/
theorem rho0_mem_rhoBox : (1 / 256 : ℝ) ∈ rhoBox :=
  ⟨by norm_num [dRhoB], le_rfl⟩

/-! ## The corrections and the affine dependence on `ρ` -/

/-- The correction `F Y_D` of `D̃` per unit `ρ`. -/
def eYDF (lm : ℝ) : PolyExprS ℂ (Fin 6) := .mul (eF lm) eYD

/-- The correction `F Y_R` of `ñ_R` per unit `ρ`. -/
def eYRF (lm : ℝ) : PolyExprS ℂ (Fin 6) := .mul (eF lm) eYR

/-- The correction `F Y_z` of `ñ_z` per unit `ρ`. -/
def eYZF (lm : ℝ) : PolyExprS ℂ (Fin 6) := .mul (eF lm) eYZ

/-- The scalar `(ρ − 1/256)` in `𝔸`. -/
def dA (ρ : ℝ) : FA := algebraMap ℂ FA ((ρ - 1 / 256 : ℝ) : ℂ)

/-- `‖ρ − 1/256‖ = |ρ − 1/256|`. -/
theorem Bd_dA (r ρ : ℝ) : Bd r (dA ρ) |ρ - 1 / 256| := by
  have h := Bd_algebraMap r ((ρ - 1 / 256 : ℝ) : ℂ)
  rwa [Complex.norm_real, Real.norm_eq_abs] at h

/-- `((ρ − 1/256 : ℝ) : ℂ) = ρ − (1/256 : ℝ)`. -/
theorem cast_sub_256 (ρ : ℝ) : ((ρ - 1 / 256 : ℝ) : ℂ) = (ρ : ℂ) - ((1 / 256 : ℝ) : ℂ) := by
  push_cast; ring

/-- `D̃(ρ) − D̃(1/256) = (ρ − 1/256) F Y_D`. -/
theorem eval_gcDM_sub (ρ lm : ℝ) (x : Fin 6 → FA) :
    PolyExprS.eval x (gcDM ρ lm) - PolyExprS.eval x (gcDM (1 / 256) lm) =
      dA ρ * PolyExprS.eval x (eYDF lm) := by
  simp only [gcDM, eYDF, dA, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- **Sanity**: at `ρ = 1/256` the difference vanishes. -/
theorem eval_gcDM_sub_self (lm : ℝ) (x : Fin 6 → FA) : dA (1 / 256) *
    PolyExprS.eval x (eYDF lm) = 0 := by
  simp [dA]

/-- `ñ_R(ρ) − ñ_R(1/256) = (ρ − 1/256) F Y_R`. -/
theorem eval_gcNRM_sub (ρ lm : ℝ) (x : Fin 6 → FA) :
    PolyExprS.eval x (gcNRM ρ lm) - PolyExprS.eval x (gcNRM (1 / 256) lm) =
      dA ρ * PolyExprS.eval x (eYRF lm) := by
  simp only [gcNRM, eYRF, dA, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- `ñ_z(ρ) − ñ_z(1/256) = (ρ − 1/256) F Y_z`. -/
theorem eval_gcNZM_sub (ρ lm : ℝ) (x : Fin 6 → FA) :
    PolyExprS.eval x (gcNZM ρ lm) - PolyExprS.eval x (gcNZM (1 / 256) lm) =
      dA ρ * PolyExprS.eval x (eYZF lm) := by
  simp only [gcNZM, eYZF, dA, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- The derivatives: `∂D̃(ρ) − ∂D̃(1/256) = (ρ − 1/256) ∂(F Y_D)`. -/
theorem pdS_gcDM_sub (ρ lm : ℝ) (x : Fin 6 → FA) (i : Fin 6) :
    pdS x i (gcDM ρ lm) - pdS x i (gcDM (1 / 256) lm) = dA ρ * pdS x i (eYDF lm) := by
  simp only [pdS, gcDM, eYDF, dA, PolyExprS.deriv, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- `∂ñ_R(ρ) − ∂ñ_R(1/256) = (ρ − 1/256) ∂(F Y_R)`. -/
theorem pdS_gcNRM_sub (ρ lm : ℝ) (x : Fin 6 → FA) (i : Fin 6) :
    pdS x i (gcNRM ρ lm) - pdS x i (gcNRM (1 / 256) lm) = dA ρ * pdS x i (eYRF lm) := by
  simp only [pdS, gcNRM, eYRF, dA, PolyExprS.deriv, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- `∂ñ_z(ρ) − ∂ñ_z(1/256) = (ρ − 1/256) ∂(F Y_z)`. -/
theorem pdS_gcNZM_sub (ρ lm : ℝ) (x : Fin 6 → FA) (i : Fin 6) :
    pdS x i (gcNZM ρ lm) - pdS x i (gcNZM (1 / 256) lm) = dA ρ * pdS x i (eYZF lm) := by
  simp only [pdS, gcNZM, eYZF, dA, PolyExprS.deriv, PolyExprS.eval]
  rw [cast_sub_256, map_sub]; ring

/-- **The residual is affine in `ρ`** (`R`-component). -/
theorem resR_gcFlowMu_sub (ρ lm ι : ℝ) (u z : FA) :
    (gcFlowMu ρ lm).resR ι u z - (gcFlowMu (1 / 256) lm).resR ι u z =
      dA ρ * (PolyExprS.eval (xB u z) (eYDF lm) * Lt ι u -
        PolyExprS.eval (xB u z) (eYRF lm)) := by
  rw [FlowFieldS.resR_eq, FlowFieldS.resR_eq]
  have h1 := eval_gcDM_sub ρ lm (xB u z)
  have h2 := eval_gcNRM_sub ρ lm (xB u z)
  simp only [FlowFieldS.Dof, gcFlowMu] at h1 h2 ⊢
  linear_combination Lt ι u * h1 - h2

/-- **The residual is affine in `ρ`** (`z`-component). -/
theorem resZ_gcFlowMu_sub (ρ lm ι : ℝ) (u z : FA) :
    (gcFlowMu ρ lm).resZ ι u z - (gcFlowMu (1 / 256) lm).resZ ι u z =
      dA ρ * (PolyExprS.eval (xB u z) (eYDF lm) * Lt ι z -
        PolyExprS.eval (xB u z) (eYZF lm)) := by
  rw [FlowFieldS.resZ_eq, FlowFieldS.resZ_eq]
  have h1 := eval_gcDM_sub ρ lm (xB u z)
  have h2 := eval_gcNZM_sub ρ lm (xB u z)
  simp only [FlowFieldS.Dof, gcFlowMu] at h1 h2 ⊢
  linear_combination Lt ι z * h1 - h2

/-! ## Uniform bounds of the corrections -/

/-- The validity bounds of the pitch-angle family. -/
local notation "aTμ" => RationalStellaratorGCMu.aTQ
/-- The node bound of the pitch-angle family. -/
local notation "gμ" => RationalStellaratorGCMu.gQ

section Corr

open RationalStellaratorGCMu PQS

/-- The validity bounds `aTμ` are nonnegative (rational form). -/
theorem aTQ_nonnegQ : ∀ i, (0 : ℚ) ≤ aTμ i := by kernel_fact

/-- The node bound is nonnegative (rational form). -/
theorem gQ_nonnegQ : (0 : ℚ) ≤ gμ := by kernel_fact

/-- **Strip bound of a tree through a rational mirror**: if `e` is `ConstLe` the embedding of the
mirror `P` and the nodes of `P` are controlled at `aTμ`, then at every input bounded by
`0 ≤ a ≤ aTμ`, `‖e(x)‖ ≤ mQ aTμ gμ P`. -/
theorem Bd_eval_mirror {r : ℝ} (hr : 0 ≤ r) {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa : ∀ i, a i ≤ (aTμ i : ℝ)) {x : Fin 6 → FA} (hx : ∀ i, Bd r (x i) (a i))
    {e : PolyExprS ℂ (Fin 6)} {P : PQS (Fin 6)} (hc : PolyExprS.ConstLe e P.toS)
    (hn : NodesOK (fun i => (aTμ i : ℝ)) (gμ : ℝ) P.toS) :
    Bd r (PolyExprS.eval x e) (mQ aTμ gμ P) := by
  have hv' := valid_of_nodesOK hn
  have hva := hv'.mono ha haa
  have hve := hc.valid ha hva
  refine (PolyExprS.Bd.evalS hr hx hve).le ?_
  calc PolyExprS.maj a e ≤ PolyExprS.maj a P.toS := hc.maj_le ha hva
    _ ≤ PolyExprS.maj (fun i => (aTμ i : ℝ)) P.toS := PolyExprS.maj_mono ha haa hv'
    _ ≤ (mQ aTμ gμ P : ℝ) := PQS.maj_le aTQ_nonnegQ gQ_nonnegQ P hn

/-- **Strip bound of a derivative through a rational mirror** (directions bounded by `b`). -/
theorem Bd_deriv_mirror {r : ℝ} (hr : 0 ≤ r) {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
    (haa : ∀ i, a i ≤ (aTμ i : ℝ)) {x h : Fin 6 → FA} (hx : ∀ i, Bd r (x i) (a i))
    {b : Fin 6 → ℚ} (hb : ∀ i, 0 ≤ b i) (hh : ∀ i, Bd r (h i) (b i))
    {e : PolyExprS ℂ (Fin 6)} {P : PQS (Fin 6)} (hc : PolyExprS.ConstLe e P.toS)
    (hn : NodesOK (fun i => (aTμ i : ℝ)) (gμ : ℝ) P.toS) :
    Bd r (PolyExprS.deriv x h e) (mDQ aTμ b gμ P) := by
  have hv' := valid_of_nodesOK hn
  have hva := hv'.mono ha haa
  have hve := hc.valid ha hva
  have hb' : ∀ i, (0 : ℝ) ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
  refine (PolyExprS.Bd.derivS hr hx hh hve).le ?_
  calc PolyExprS.majD a (fun i => (b i : ℝ)) e ≤ PolyExprS.majD a (fun i => (b i : ℝ)) P.toS :=
        hc.majD_le ha hb' hva
    _ ≤ PolyExprS.majD (fun i => (aTμ i : ℝ)) (fun i => (b i : ℝ)) P.toS :=
        PolyExprS.majD_mono ha hb' haa (fun _ => le_rfl) hv'
    _ ≤ (mDQ aTμ b gμ P : ℝ) := PQS.majD_le aTQ_nonnegQ hb gQ_nonnegQ P hn

/-- The direction `∂_u`. -/
def bU : Fin 6 → ℚ := ![1, 0, 0, 0, 0, 0]

/-- The direction `∂_z`. -/
def bZ : Fin 6 → ℚ := ![0, 1, 0, 0, 0, 0]

/-- The unit directions are bounded by `bU`. -/
theorem Bd_single_bU (r : ℝ) : ∀ i, Bd r ((Pi.single 0 1 : Fin 6 → FA) i) (bU i) := by
  intro i; fin_cases i <;> simp [bU, Bd_one, Bd_zero]

/-- The unit directions are bounded by `bZ`. -/
theorem Bd_single_bZ (r : ℝ) : ∀ i, Bd r ((Pi.single 1 1 : Fin 6 → FA) i) (bZ i) := by
  intro i; fin_cases i <;> simp [bZ, Bd_one, Bd_zero]

/-- The mirror of `F Y_D`. -/
def eYDFQ : PQS (Fin 6) := .mul eFQ eYDQ
/-- The mirror of `F Y_R`. -/
def eYRFQ : PQS (Fin 6) := .mul eFQ eYRQ
/-- The mirror of `F Y_z`. -/
def eYZFQ : PQS (Fin 6) := .mul eFQ eYZQ

set_option maxRecDepth 100000 in
/-- The corrections at `λ` are `ConstLe` the mirrors (`|λ| ≤ 1/16`). -/
theorem constLe_corr {lm : ℝ} (h : |lm| ≤ lam1) :
    PolyExprS.ConstLe (eYDF lm) eYDFQ.toS ∧ PolyExprS.ConstLe (eYRF lm) eYRFQ.toS ∧
      PolyExprS.ConstLe (eYZF lm) eYZFQ.toS := by
  have hF := constLe_eF h
  rw [← eFQ_toS] at hF
  refine ⟨?_, ?_, ?_⟩
  · simp only [eYDF, eYDFQ, toS, eYDQ_toS]; exact .mul hF (PolyExprS.constLe_refl _)
  · simp only [eYRF, eYRFQ, toS, eYRQ_toS]; exact .mul hF (PolyExprS.constLe_refl _)
  · simp only [eYZF, eYZFQ, toS, eYZQ_toS]; exact .mul hF (PolyExprS.constLe_refl _)

set_option maxRecDepth 100000 in
/-- The nodes of the mirrors are controlled at `aTμ`. -/
theorem nodesOK_corr : NodesOK (fun i => (aTμ i : ℝ)) (gμ : ℝ) eYDFQ.toS ∧
    NodesOK (fun i => (aTμ i : ℝ)) (gμ : ℝ) eYRFQ.toS ∧
    NodesOK (fun i => (aTμ i : ℝ)) (gμ : ℝ) eYZFQ.toS := by
  obtain ⟨hD, hR, hZ⟩ := nodesOK_eY
  have hF := nodesOK_eF
  rw [← eFQ_toS] at hF
  refine ⟨?_, ?_, ?_⟩
  · rw [show eYDFQ.toS = .mul eFQ.toS eYDQ.toS from rfl, eYDQ_toS]; exact ⟨hF, hD⟩
  · rw [show eYRFQ.toS = .mul eFQ.toS eYRQ.toS from rfl, eYRQ_toS]; exact ⟨hF, hR⟩
  · rw [show eYZFQ.toS = .mul eFQ.toS eYZQ.toS from rfl, eYZQ_toS]; exact ⟨hF, hZ⟩

set_option maxRecDepth 100000 in
/-- **The kernel majorants of the corrections**: values, `u`-derivatives and `z`-derivatives. -/
theorem corr_majQ :
    mQ aTμ gμ eYDFQ ≤ 177 ∧ mQ aTμ gμ eYRFQ ≤ 91 ∧ mQ aTμ gμ eYZFQ ≤ 1113 ∧
    mDQ aTμ bU gμ eYDFQ ≤ 4997 ∧ mDQ aTμ bZ gμ eYDFQ ≤ 1620 ∧
    mDQ aTμ bU gμ eYRFQ ≤ 2623 ∧ mDQ aTμ bZ gμ eYRFQ ≤ 861 ∧
    mDQ aTμ bU gμ eYZFQ ≤ 30768 ∧ mDQ aTμ bZ gμ eYZFQ ≤ 6181 := by
  kernel_fact

end Corr

/-- The constants of the correction bounds: `(F Y_D, ∂_u, ∂_z, F Y_R, ∂_u, ∂_z, F Y_z, ∂_u, ∂_z)`.
-/
def corrM : Fin 9 → ℝ := ![177, 4997, 1620, 91, 2623, 861, 1113, 30768, 6181]

section CorrBounds

open RationalStellaratorGCMu

variable {r : ℝ} (hr : 0 ≤ r) {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i)
  (haa : ∀ i, a i ≤ (aTμ i : ℝ)) {x : Fin 6 → FA} (hx : ∀ i, Bd r (x i) (a i)) {lm : ℝ}
  (hlm : |lm| ≤ lam1)
include hr ha haa hx hlm

/-- **Uniform bounds of the corrections** at every input bounded by `0 ≤ a ≤ aTμ`. -/
theorem Bd_corr :
    Bd r (PolyExprS.eval x (eYDF lm)) 177 ∧ Bd r (pdS x 0 (eYDF lm)) 4997 ∧
    Bd r (pdS x 1 (eYDF lm)) 1620 ∧
    Bd r (PolyExprS.eval x (eYRF lm)) 91 ∧ Bd r (pdS x 0 (eYRF lm)) 2623 ∧
    Bd r (pdS x 1 (eYRF lm)) 861 ∧
    Bd r (PolyExprS.eval x (eYZF lm)) 1113 ∧ Bd r (pdS x 0 (eYZF lm)) 30768 ∧
    Bd r (pdS x 1 (eYZF lm)) 6181 := by
  obtain ⟨cD, cR, cZ⟩ := constLe_corr hlm
  obtain ⟨nD, nR, nZ⟩ := nodesOK_corr
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := corr_majQ
  have hbU : ∀ i, (0 : ℚ) ≤ bU i := by kernel_fact
  have hbZ : ∀ i, (0 : ℚ) ≤ bZ i := by kernel_fact
  have q : ∀ {X : FA} {s t : ℚ}, Bd r X (s : ℝ) → s ≤ t → Bd r X (t : ℝ) :=
    fun h hst => h.le (by exact_mod_cast hst)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast q (Bd_eval_mirror hr ha haa hx cD nD) m1
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbU (Bd_single_bU r) cD nD) m4
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbZ (Bd_single_bZ r) cD nD) m5
  · exact_mod_cast q (Bd_eval_mirror hr ha haa hx cR nR) m2
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbU (Bd_single_bU r) cR nR) m6
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbZ (Bd_single_bZ r) cR nR) m7
  · exact_mod_cast q (Bd_eval_mirror hr ha haa hx cZ nZ) m3
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbU (Bd_single_bU r) cZ nZ) m8
  · exact_mod_cast q (Bd_deriv_mirror hr ha haa hx hbZ (Bd_single_bZ r) cZ nZ) m9

end CorrBounds

/-! ## Pairs with a difference bound -/

/-- `DBd r x x' B d`: `‖x‖_r ≤ B` and `‖x' − x‖_r ≤ d`. -/
def DBd (r : ℝ) (x x' : FA) (B d : ℝ) : Prop := Bd r x B ∧ Bd r (x' - x) d

namespace DBd

variable {r B C d e : ℝ} {x x' y y' : FA}

/-- **Sanity**: equal elements have difference bound `0`. -/
theorem of_eq (h : Bd r x B) : DBd r x x B 0 := ⟨h, by rw [sub_self]; exact Bd_zero r⟩

/-- The perturbed element is bounded by `B + d`. -/
theorem bd' (h : DBd r x x' B d) : Bd r x' (B + d) := by
  have := h.1.add h.2; rwa [add_sub_cancel] at this

/-- Sums. -/
theorem add (hx : DBd r x x' B d) (hy : DBd r y y' C e) : DBd r (x + y) (x' + y') (B + C) (d + e) :=
  ⟨hx.1.add hy.1, by
    have := hx.2.add hy.2; rwa [show x' - x + (y' - y) = x' + y' - (x + y) by ring] at this⟩

/-- Differences. -/
theorem sub (hx : DBd r x x' B d) (hy : DBd r y y' C e) : DBd r (x - y) (x' - y') (B + C) (d + e) :=
  ⟨hx.1.sub hy.1, by
    have := hx.2.sub hy.2; rwa [show x' - x - (y' - y) = x' - y' - (x - y) by ring] at this⟩

/-- Products. -/
theorem mul (hr : 0 ≤ r) (hx : DBd r x x' B d) (hy : DBd r y y' C e) :
    DBd r (x * y) (x' * y') (B * C) (d * (C + e) + B * e) :=
  ⟨hx.1.mul hr hy.1, by
    have := (hx.2.mul hr hy.bd').add (hx.1.mul hr hy.2)
    rwa [show (x' - x) * y' + x * (y' - y) = x' * y' - x * y by ring] at this⟩

/-- Monotonicity in the bounds. -/
theorem le (h : DBd r x x' B d) (hB : B ≤ C) (hd : d ≤ e) : DBd r x x' C e :=
  ⟨h.1.le hB, h.2.le hd⟩

end DBd

end PlasmaLean.Design.RationalStellaratorGC
