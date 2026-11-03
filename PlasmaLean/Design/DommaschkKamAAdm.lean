/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAAdmOut
public import PlasmaLean.Design.DommaschkKamCAdmFrame

/-!
# Admissibility of the Newton step near Dommaschk torus A (N-33 plan item 8)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamAAdm` (about 45 CPU-min on the laptop, peak 5.2 GB in the
two tail-check modules); axioms are checked in `scripts/check_axioms_heavy.lean`.

**Main theorem `dk_adm`.** Every analytic torus `(u, z)` that is `μ`-close (`Close`, `μ ≤ 10⁻¹²`)
to the data torus `(u₀A, z₀A)` (`Design/DommaschkKamATorus`) satisfies the admissibility bounds
`FlowFieldG.AdmBoundsG c ι_A ρ u z` of the generalised KAM step (`Design/KamFlowIterationG`) for the
Dommaschk field with the moving centre `dkFieldTC`, on every strip `0 < ρ ≤ 0.045`, for any
constants `c : SCG` dominating the certified ones (`ConstsOK`): frame (units and analytic inverses
of `D`, `R`, `W₀`), torus bounds, field bounds, inverse bounds, torsion and twist.

**Route.** All quantities are evaluated in the oracle angle (`AdmO`, `AdmO.toG` of
`Design/DommaschkKamCAdmFrame`) at the rotated torus `rotψi (u, z)`:
* the low-resolution chain (`Design/DommaschkKamAAdmChain`) gives balls of every quantity at the
  surrogate torus `(xA 4, xA 5)` (`valA_le`, the norm nodes `nA_*`);
* the surrogate is close to the data torus (`Design/DommaschkKamAAdmTail`), so every admissible
  torus is within `μ + t` of the surrogate (`inputs_close`);
* the field polynomials move by at most their Lipschitz majorants (`Bd_ev_sub`, `lipQ`); `W₀` and
  the torsion numerator by the product rule (`Bd.eval_add_sub` on `Qp`);
* the inverses come from the approximate inverses `qD`, `qW`, `qR` of the chain
  (`inv_of_approx`), and the torsion from `T₀ = Y Z`, `Y = R⁷ P qD³ qW²`,
  `Z = (qD D)⁻³ (qW W₀)⁻²` near `1` (`torsion_bounds`).

**Sanity.** `consts_sharp`: the certified twist is `≥ 13.99`, the torsion `≤ 2202`;
`dkIotaA_abs_le` (concrete).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall WEll1Z2 Complex

/-! ## Generic helpers -/

/-- A bound near a bounded element. -/
theorem Bd_near {ρ a h : ℝ} {x y : FA} (hx : Bd ρ x a) (hh : Bd ρ (y - x) h) : Bd ρ y (a + h) := by
  have := hx.add hh; rwa [add_sub_cancel] at this

/-- A kernel-checked rational inequality, cast to `ℝ`. -/
theorem qleA {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h

/-- `|ι_A| ≤ 0.2387`. -/
theorem dkIotaA_abs_le : |DommaschkKamDio.dkIotaA| ≤ ((2387 / 10000 : ℚ) : ℝ) := by
  have h5 : √5 ≤ 2.2361 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h0 : 0 ≤ √5 := Real.sqrt_nonneg 5
  rw [DommaschkKamDio.dkIotaA, abs_neg, abs_of_nonneg (by positivity)]
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-! ## The R-form substitution in the strip algebra -/

/-- `Rl` is `R₀ + u`. -/
theorem ev_Rl_A (x : Fin 6 → FA) : DkPoly.ev x Rl = algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0 := by
  simp only [Rl, DkPoly.ev_cons, DkPoly.ev_nil, DkPoly.Tm.ev]
  simp

/-- `RpowL n` is `(R₀ + u)ⁿ`. -/
theorem ev_RpowL_A (x : Fin 6 → FA) :
    ∀ n, DkPoly.ev x (RpowL n) = (algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0) ^ n
  | 0 => by simp [RpowL, DkPoly.Tm.ev]
  | n + 1 => by rw [RpowL, DkPoly.ev_mul, ev_RpowL_A x n, ev_Rl_A, pow_succ, mul_comm]

/-- **The substitution** `R = R₀ + u` in the strip algebra. -/
theorem ev_substR_A (x : Fin 6 → FA) (p : DkPoly.SP) :
    DkPoly.ev x (substR p) =
      DkPoly.ev ![algebraMap ℂ FA ((R0q : ℚ) : ℂ) + x 0, x 1, x 2, x 3, 0, 0] p := by
  induction p with
  | nil => simp [substR]
  | cons t p ih =>
    simp only [substR, List.foldr_cons] at ih ⊢
    rw [DkPoly.ev_merge, ih, DkPoly.ev_mulMono, ev_RpowL_A, DkPoly.ev_cons]
    simp only [DkPoly.Tm.ev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, pow_zero, one_mul]
    ring

/-- `∂_u D` in R-form (kernel check). -/
theorem subst_Du : substR (DkPoly.dU dDR) = DkPoly.dU dD := by kernel_fact
/-- `∂_z D` in R-form (kernel check). -/
theorem subst_Dz : substR (DkPoly.dZ dDR) = DkPoly.dZ dD := by kernel_fact
/-- `∂_u n_R` in R-form (kernel check). -/
theorem subst_nRu : substR (DkPoly.dU (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)) = DkPoly.dU dnR := by
  kernel_fact
/-- `∂_z n_R` in R-form (kernel check). -/
theorem subst_nRz : substR (DkPoly.dZ (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)) = DkPoly.dZ dnR := by
  kernel_fact
/-- `∂_u n_z` in R-form (kernel check). -/
theorem subst_nZu : substR (DkPoly.dU dnZR) = DkPoly.dU dnZ := by kernel_fact
/-- `∂_z n_z` in R-form (kernel check). -/
theorem subst_nZz : substR (DkPoly.dZ dnZR) = DkPoly.dZ dnZ := by kernel_fact

/-- The R-form point of the surrogate is `xRo`. -/
theorem xRo_eq : ![algebraMap ℂ FA ((R0q : ℚ) : ℂ) + xBo (xA 4) (xA 5) 0, xBo (xA 4) (xA 5) 1,
    xBo (xA 4) (xA 5) 2, xBo (xA 4) (xA 5) 3, 0, 0] = xRo := by
  funext i; fin_cases i <;> rfl

/-- A u-form field polynomial at the surrogate is the R-form value `fA k`. -/
theorem Fo_surr {k : ℕ} {pu : DkPoly.SP} (h : substR (polyA k) = pu) :
    Fo pu (xA 4) (xA 5) = fA k := by
  rw [Fo, ← h, ev_substR_A, xRo_eq]; rfl

/-! ## The surrogate quantities -/

section Surrogate

variable {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16)
include hr hq

/-- A chain value bound. -/
theorem sA (i : ℕ) (hi : i < 195) : Bd r (XA i) ((BA i + EA i : ℚ) : ℝ) := valA_le hr hq i hi

end Surrogate

/-- `∂_θ` of the surrogate `U`. -/
theorem dTh_xA4 : dTh (xA 4) = xA 6 := by
  rw [show dTh (xA 4) = dS (((1 : ℕ) : ℤ) : ℂ) (((0 : ℕ) : ℤ) : ℂ) (xA 4) by simp [dTh]]
  exact dS_ctr_grid SA NA MA 0 (gA 4) _ _

/-- `∂_θ` of the surrogate `z`. -/
theorem dTh_xA5 : dTh (xA 5) = xA 7 := by
  rw [show dTh (xA 5) = dS (((1 : ℕ) : ℤ) : ℂ) (((0 : ℕ) : ℤ) : ℂ) (xA 5) by simp [dTh]]
  exact dS_ctr_grid SA NA MA 1 (gA 5) _ _

/-- `∂_ψ` of the surrogate `U`. -/
theorem dPs_xA4 : dS 0 1 (xA 4) = xA 8 := by
  rw [show dS 0 1 (xA 4) = dS (((0 : ℕ) : ℤ) : ℂ) (((1 : ℕ) : ℤ) : ℂ) (xA 4) by simp]
  exact dS_ctr_grid SA NA MA 0 (gA 4) _ _

/-- `∂_ψ` of the surrogate `z`. -/
theorem dPs_xA5 : dS 0 1 (xA 5) = xA 9 := by
  rw [show dS 0 1 (xA 5) = dS (((0 : ℕ) : ℤ) : ℂ) (((1 : ℕ) : ℤ) : ℂ) (xA 5) by simp]
  exact dS_ctr_grid SA NA MA 1 (gA 5) _ _

/-- The surrogate is analytic. -/
theorem ana_xA (i : ℕ) : Ana (xA i) := by
  rcases lt_or_ge i 4 with h | h
  · interval_cases i
    · rw [xA_t]; exact ⟨1, 1, one_pos, Bd_one 1⟩
    · rw [xA_V]; exact ⟨1, 1, one_pos, Bd_one 1⟩
    · rw [xA_C, cSo_eq]; exact ana_sS
    · rw [xA_S, sSo_eq]; exact ana_cS.neg
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact ana_ctr_grid _ _ _ _ _

/-- The centre polynomials at the surrogate frame. -/
theorem cenO_eq {p : DkPoly.SP} (hp : DkPoly.AO p = true) : cenO p = DkPoly.ev xRo p :=
  DkPoly.ev_congr_AO hp rfl rfl

/-- `V₀_R` at the surrogate. -/
theorem V0Ro_surr : V0Ro (xA 4) = XA iV0R := by
  rw [V0Ro, cenO_eq cenR_AO]; rfl

/-- `V₀_z` at the surrogate. -/
theorem V0Zo_surr : V0Zo (xA 5) = XA iV0Z := by
  rw [V0Zo, cenO_eq cenZ_AO]; rfl

/-- `W₀` at the surrogate. -/
theorem W0o_surr : W0o (xA 4) (xA 5) = XA iW0 := by
  rw [W0o, dTh_xA4, dTh_xA5, V0Ro_surr, V0Zo_surr]; rfl

/-- `a_R'` at the surrogate frame. -/
theorem AR1_surr : cenO (DkPoly.phiS cenR) = XA iAR1 := by
  rw [cenO_eq (DkPoly.AO_phiS cenR_AO)]; rfl

/-- `a_z'` at the surrogate frame. -/
theorem AZ1_surr : cenO (DkPoly.phiS cenZ) = XA iAZ1 := by
  rw [cenO_eq (DkPoly.AO_phiS cenZ_AO)]; rfl

/-- `R = R₀ + U` at the surrogate. -/
theorem R_surr : RofG dkR0 (xA 4) = XA iR := by
  change RofG dkR0 (xA 4) = RvA
  rw [RofG, RvA, R0q_cast]

/-- The 13 torsion quantities at the surrogate. -/
theorem yP_surr : yP (xA 4) (xA 5) = ![XA iD, XA inR, XA inZ, XA iDu, XA iDz, XA inRu, XA inRz,
    XA inZu, XA inZz, XA iV0R, XA iV0Z, XA iAR1, XA iAZ1] := by
  have e0 : Fo dD (xA 4) (xA 5) = XA iD := Fo_surr subst_D
  have e1 : Fo dnR (xA 4) (xA 5) = XA inR := Fo_surr subst_nR
  have e2 : Fo dnZ (xA 4) (xA 5) = XA inZ := Fo_surr subst_nZ
  have e3 : Fo (DkPoly.dU dD) (xA 4) (xA 5) = XA iDu := Fo_surr subst_Du
  have e4 : Fo (DkPoly.dZ dD) (xA 4) (xA 5) = XA iDz := Fo_surr subst_Dz
  have e5 : Fo (DkPoly.dU dnR) (xA 4) (xA 5) = XA inRu := Fo_surr subst_nRu
  have e6 : Fo (DkPoly.dZ dnR) (xA 4) (xA 5) = XA inRz := Fo_surr subst_nRz
  have e7 : Fo (DkPoly.dU dnZ) (xA 4) (xA 5) = XA inZu := Fo_surr subst_nZu
  have e8 : Fo (DkPoly.dZ dnZ) (xA 4) (xA 5) = XA inZz := Fo_surr subst_nZz
  rw [yP, e0, e1, e2, e3, e4, e5, e6, e7, e8, V0Ro_surr, V0Zo_surr, AR1_surr, AZ1_surr]

/-- The torsion numerator at the surrogate. -/
theorem Pofo_surr : Pofo (xA 4) (xA 5) = XA iP := by
  rw [Pofo_eq, yP_surr]
  change _ = Pa
  simp only [Qp, PolyExpr.eval, Pa, YRa, YZa, G1a, G2a, G3a, DDa]
  simp only [Matrix.cons_val, Fin.isValue]
  rfl


/-! ## The closeness inputs -/

/-- `𝓛 = ι ∂_θ + 2 ∂_ψ`. -/
theorem Lt_split (ι : ℝ) {x : FA} (hx : Ana x) : Lt ι x = (ι : ℂ) • dTh x + (2 : ℂ) • dS 0 1 x := by
  have h1 := dS_add_symbol (ι : ℂ) 0 0 2 hx
  have h2 := dS_smul_symbol 1 0 (ι : ℂ) hx
  have h3 := dS_smul_symbol 0 1 (2 : ℂ) hx
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2 h3
  rw [Lt, h1, h2, h3]; rfl

/-- `∂_θ (Uo − xA 4)` as a grid centre. -/
theorem dTh_tailU : dTh Uo - xA 6 = ctr Sc Nc Mc (1, 0, 3) (gridPolyNM Nc Mc (wGc 1 0 dGU)) := by
  rw [← dTh_xA4, show dTh Uo - dTh (xA 4) = dTh (Uo - xA 4) from
    (dS_sub 1 0 ana_Uo (ana_xA 4)).symm, Uo_sub_xA,
    show dTh (ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc dGU)) =
      dS (((1 : ℕ) : ℤ) : ℂ) (((0 : ℕ) : ℤ) : ℂ) (ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc dGU))
      by simp [dTh]]
  exact dS_ctr_grid Sc Nc Mc 0 dGU _ _

/-- `∂_θ (Zo − xA 5)` as a grid centre. -/
theorem dTh_tailZ : dTh Zo - xA 7 = ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc (wGc 1 0 dGZ)) := by
  rw [← dTh_xA5, show dTh Zo - dTh (xA 5) = dTh (Zo - xA 5) from
    (dS_sub 1 0 ana_Zo (ana_xA 5)).symm, Zo_sub_xA,
    show dTh (ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc dGZ)) =
      dS (((1 : ℕ) : ℤ) : ℂ) (((0 : ℕ) : ℤ) : ℂ) (ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc dGZ))
      by simp [dTh]]
  exact dS_ctr_grid Sc Nc Mc 1 dGZ _ _

/-- `∂_ψ (Uo − xA 4)` as a grid centre. -/
theorem dPs_tailU : dS 0 1 Uo - xA 8 = ctr Sc Nc Mc (1, 0, 3) (gridPolyNM Nc Mc (wGc 0 1 dGU)) := by
  rw [← dPs_xA4, ← dS_sub 0 1 ana_Uo (ana_xA 4), Uo_sub_xA,
    show dS 0 1 (ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc dGU)) =
      dS (((0 : ℕ) : ℤ) : ℂ) (((1 : ℕ) : ℤ) : ℂ) (ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc dGU))
      by simp]
  exact dS_ctr_grid Sc Nc Mc 0 dGU _ _

/-- `∂_ψ (Zo − xA 5)` as a grid centre. -/
theorem dPs_tailZ : dS 0 1 Zo - xA 9 = ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc (wGc 0 1 dGZ)) := by
  rw [← dPs_xA5, ← dS_sub 0 1 ana_Zo (ana_xA 5), Zo_sub_xA,
    show dS 0 1 (ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc dGZ)) =
      dS (((0 : ℕ) : ℤ) : ℂ) (((1 : ℕ) : ℤ) : ℂ) (ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc dGZ))
      by simp]
  exact dS_ctr_grid Sc Nc Mc 1 dGZ _ _

/-- The transport of the tail: `‖𝓛 (Uo − xA 4)‖ ≤ |ι| t_θ + 2 t_ψ`. -/
theorem Lt_tail {r ι : ℝ} (hι : |ι| ≤ ((2387 / 10000 : ℚ) : ℝ)) {X x xθ xψ : FA} (hX : Ana X)
    (hx : Ana x) {tθ tψ : ℚ} (hθ : Bd r (dTh X - xθ) tθ) (hψ : Bd r (dS 0 1 X - xψ) tψ)
    (eθ : dTh x = xθ) (eψ : dS 0 1 x = xψ) :
    Bd r (Lt ι (X - x)) (((2387 / 10000 : ℚ) : ℝ) * tθ + 2 * tψ) := by
  rw [Lt_split ι (hX.sub hx), show dTh (X - x) = dTh X - xθ by
    rw [← eθ]; exact dS_sub 1 0 hX hx, dS_sub 0 1 hX hx, eψ]
  refine ((hθ.smul _).add (hψ.smul _)).le ?_
  rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
  have : 0 ≤ (tθ : ℝ) := hθ.nonneg
  nlinarith

/-! ## The constants -/

/-- **The admissibility constants of `c` dominate the certified ones.** -/
def ConstsOK (c : SCG) : Prop :=
  (auC : ℝ) ≤ c.au ∧ (azC : ℝ) ≤ c.az ∧ (avRC : ℝ) ≤ c.avR ∧ (avZC : ℝ) ≤ c.avZ ∧
  (aRC : ℝ) ≤ c.aR ∧ (aRtC : ℝ) ≤ c.aRt ∧ (aztC : ℝ) ≤ c.azt ∧ (aLRC : ℝ) ≤ c.aLR ∧
  (aLzC : ℝ) ≤ c.aLz ∧ (bDC : ℝ) ≤ c.bD ∧ (bDuC : ℝ) ≤ c.bDu ∧ (bDzC : ℝ) ≤ c.bDz ∧
  (bnRC : ℝ) ≤ c.bnR ∧ (bnRuC : ℝ) ≤ c.bnRu ∧ (bnRzC : ℝ) ≤ c.bnRz ∧ (bnZC : ℝ) ≤ c.bnZ ∧
  (bnZuC : ℝ) ≤ c.bnZu ∧ (bnZzC : ℝ) ≤ c.bnZz ∧ (sDC : ℝ) ≤ c.sD ∧ (sRC : ℝ) ≤ c.sR ∧
  (sWC : ℝ) ≤ c.sW ∧ (tTC : ℝ) ≤ c.tT ∧ c.τ ≤ (tauC : ℝ)

/-- **Sanity**: the certified twist is at least `13.99` and the torsion at most `2202`. -/
theorem consts_sharp : (1399 / 100 : ℚ) ≤ tauC ∧ tTC ≤ 2202 := by
  constructor <;> norm_num [tauC, tTC]

/-! ## Field polynomials near the surrogate -/

/-- **A field polynomial at a torus near the surrogate.** -/
theorem field_near {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {p : DkPoly.SP}
    {i : ℕ} (hi : i < 195) (hs : Fo p (xA 4) (xA 5) = XA i) {dl : ℚ}
    (hdl : lipQ (BA 4) (BA 5) (muq + tU) (muq + tZ) ((68553 : ℕ) / 2 ^ 16) p ≤ dl) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo p uo zo - Fo p (xA 4) (xA 5)) (dl : ℝ) ∧
      Bd r (Fo p uo zo) ((BA i + EA i + dl : ℚ) : ℝ) := by
  have h := Bd_ev_sub (x := xBo (xA 4) (xA 5)) (y := xBo uo zo) hr rfl rfl
    (normA hq 4 (by norm_num)) (normA hq 5 (by norm_num)) hU hZ (Bd_cSo_q hq) (Bd_sSo_q hq) p
  rw [lipR_cast] at h
  have h1 : Bd r (Fo p uo zo - Fo p (xA 4) (xA 5)) (dl : ℝ) := h.le (qleA hdl)
  refine ⟨h1, ?_⟩
  have hb := sA hr hq i hi
  rw [← hs] at hb
  have h2 := Bd_near hb h1
  exact h2.le (le_of_eq (by push_cast; ring))

/-- **An approximate inverse at a nearby point**: `‖q d − 1‖ ≤ e + B_q δ`. -/
theorem approx_near {r : ℝ} (hr : 0 ≤ r) {q d d0 : FA} {Bq e dl : ℚ} (hq0 : Bd r q Bq)
    (he0 : Bd r (q * d0 - 1) e) (hdl : Bd r (d - d0) dl) :
    Bd r (q * d - 1) ((e + Bq * dl : ℚ) : ℝ) := by
  have h := he0.add (hq0.mul hr hdl)
  rw [show q * d0 - 1 + q * (d - d0) = q * d - 1 by ring] at h
  exact h.le (le_of_eq (by push_cast; ring))


/-- A quotient bound cast from `ℚ`. -/
theorem div_cast_le {a b e : ℚ} (h : a / (1 - e) ≤ b) : (a : ℝ) / (1 - (e : ℝ)) ≤ b := by
  exact_mod_cast h

/-! ## The majorant derivative of the torsion structure -/

/-- Product rule on (majorant, derivative majorant) pairs. -/
def pmQ (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 * y.1, x.2 * y.1 + x.1 * y.2)

/-- Sum rule on (majorant, derivative majorant) pairs. -/
def paQ (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 + y.1, x.2 + y.2)

/-- The rational `(maj, majD)` of `Qp` (mirror of `PolyExpr.maj`, `PolyExpr.majD`). -/
def mQp (a b : Fin 13 → ℚ) : ℚ × ℚ :=
  let v := fun i => (a i, b i)
  let Y (n nu nz ap : ℚ × ℚ) : ℚ × ℚ :=
    paQ (paQ (paQ (pmQ n (v 0)) (pmQ (v 0) (paQ (pmQ nu (v 9)) (pmQ nz (v 10)))))
      (pmQ n (paQ (pmQ (v 3) (v 9)) (pmQ (v 4) (v 10))))) (pmQ (pmQ (v 0) (v 0)) ap)
  paQ (pmQ (Y (v 1) (v 5) (v 6) (v 11)) (v 10)) (pmQ (Y (v 2) (v 7) (v 8) (v 12)) (v 9))

/-- The real `majD` of `Qp` is the rational mirror. -/
theorem majD_Qp (a b : Fin 13 → ℚ) :
    PolyExpr.majD (fun i => ((a i : ℚ) : ℝ)) (fun i => ((b i : ℚ) : ℝ)) Qp = ((mQp a b).2 : ℝ) := by
  simp only [Qp, PolyExpr.majD, PolyExpr.maj, mQp, pmQ, paQ]
  push_cast
  ring

/-- The norm bounds of the 13 torsion quantities at the surrogate. -/
def aQd : Fin 13 → ℚ := ![BA iD + EA iD, BA inR + EA inR, BA inZ + EA inZ, BA iDu + EA iDu,
    BA iDz + EA iDz, BA inRu + EA inRu, BA inRz + EA inRz, BA inZu + EA inZu, BA inZz + EA inZz,
    BA iV0R + EA iV0R, BA iV0Z + EA iV0Z, BA iAR1 + EA iAR1, BA iAZ1 + EA iAZ1]

/-- The deviations of the 13 torsion quantities. -/
def bQd : Fin 13 → ℚ := ![dlD, dlnR, dlnZ, dlDu, dlDz, dlnRu, dlnRz, dlnZu, dlnZz, muq + tU,
    muq + tZ, 0, 0]

/-- The norm node `eD`. -/
theorem eval_eD : Ex.eval XA trA_eD = xA iqD * Fo dD (xA 4) (xA 5) - 1 := by
  rw [Fo_surr (k := 0) subst_D]
  simp only [trA_eD, Ex.eval]
  rw [show XA 0 = 1 from rfl, one_mul]; rfl

/-- The norm node `eW`. -/
theorem eval_eW : Ex.eval XA trA_eW = xA iqW * W0o (xA 4) (xA 5) - 1 := by
  rw [W0o_surr]
  simp only [trA_eW, Ex.eval]
  rw [show XA 0 = 1 from rfl, one_mul]; rfl

/-- The norm node `eR`. -/
theorem eval_eR : Ex.eval XA trA_eR = xA iqR * RofG dkR0 (xA 4) - 1 := by
  rw [R_surr]
  simp only [trA_eR, Ex.eval]
  rw [show XA 0 = 1 from rfl, one_mul]; rfl

set_option maxRecDepth 100000 in
/-- The field quantity `D` near the surrogate. -/
theorem fld_D {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo dD uo zo - Fo dD (xA 4) (xA 5)) (dlD : ℝ) ∧
      Bd r (Fo dD uo zo) ((BA iD + EA iD + dlD : ℚ) : ℝ) :=
  field_near hr hq (i := iD) (by norm_num) (Fo_surr (k := 0) subst_D) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `Du` near the surrogate. -/
theorem fld_Du {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dU dD) uo zo - Fo (DkPoly.dU dD) (xA 4) (xA 5)) (dlDu : ℝ) ∧
      Bd r (Fo (DkPoly.dU dD) uo zo) ((BA iDu + EA iDu + dlDu : ℚ) : ℝ) :=
  field_near hr hq (i := iDu) (by norm_num) (Fo_surr (k := 1) subst_Du) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `Dz` near the surrogate. -/
theorem fld_Dz {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dZ dD) uo zo - Fo (DkPoly.dZ dD) (xA 4) (xA 5)) (dlDz : ℝ) ∧
      Bd r (Fo (DkPoly.dZ dD) uo zo) ((BA iDz + EA iDz + dlDz : ℚ) : ℝ) :=
  field_near hr hq (i := iDz) (by norm_num) (Fo_surr (k := 2) subst_Dz) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nR` near the surrogate. -/
theorem fld_nR {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo dnR uo zo - Fo dnR (xA 4) (xA 5)) (dlnR : ℝ) ∧
      Bd r (Fo dnR uo zo) ((BA inR + EA inR + dlnR : ℚ) : ℝ) :=
  field_near hr hq (i := inR) (by norm_num) (Fo_surr (k := 3) subst_nR) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nRu` near the surrogate. -/
theorem fld_nRu {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dU dnR) uo zo - Fo (DkPoly.dU dnR) (xA 4) (xA 5)) (dlnRu : ℝ) ∧
      Bd r (Fo (DkPoly.dU dnR) uo zo) ((BA inRu + EA inRu + dlnRu : ℚ) : ℝ) :=
  field_near hr hq (i := inRu) (by norm_num) (Fo_surr (k := 4) subst_nRu) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nRz` near the surrogate. -/
theorem fld_nRz {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dZ dnR) uo zo - Fo (DkPoly.dZ dnR) (xA 4) (xA 5)) (dlnRz : ℝ) ∧
      Bd r (Fo (DkPoly.dZ dnR) uo zo) ((BA inRz + EA inRz + dlnRz : ℚ) : ℝ) :=
  field_near hr hq (i := inRz) (by norm_num) (Fo_surr (k := 5) subst_nRz) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nZ` near the surrogate. -/
theorem fld_nZ {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo dnZ uo zo - Fo dnZ (xA 4) (xA 5)) (dlnZ : ℝ) ∧
      Bd r (Fo dnZ uo zo) ((BA inZ + EA inZ + dlnZ : ℚ) : ℝ) :=
  field_near hr hq (i := inZ) (by norm_num) (Fo_surr (k := 6) subst_nZ) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nZu` near the surrogate. -/
theorem fld_nZu {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dU dnZ) uo zo - Fo (DkPoly.dU dnZ) (xA 4) (xA 5)) (dlnZu : ℝ) ∧
      Bd r (Fo (DkPoly.dU dnZ) uo zo) ((BA inZu + EA inZu + dlnZu : ℚ) : ℝ) :=
  field_near hr hq (i := inZu) (by norm_num) (Fo_surr (k := 7) subst_nZu) (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The field quantity `nZz` near the surrogate. -/
theorem fld_nZz {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {uo zo : FA}
    (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd r (Fo (DkPoly.dZ dnZ) uo zo - Fo (DkPoly.dZ dnZ) (xA 4) (xA 5)) (dlnZz : ℝ) ∧
      Bd r (Fo (DkPoly.dZ dnZ) uo zo) ((BA inZz + EA inZz + dlnZz : ℚ) : ℝ) :=
  field_near hr hq (i := inZz) (by norm_num) (Fo_surr (k := 8) subst_nZz) (by kernel_fact) hU hZ

/-- The 13 torsion quantities at the surrogate are bounded by `aQd`. -/
theorem hx_surr {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) :
    ∀ i, Bd r (yP (xA 4) (xA 5) i) ((aQd i : ℚ) : ℝ) := by
  rw [yP_surr]
  intro i
  fin_cases i
  · exact sA hr hq iD (by norm_num)
  · exact sA hr hq inR (by norm_num)
  · exact sA hr hq inZ (by norm_num)
  · exact sA hr hq iDu (by norm_num)
  · exact sA hr hq iDz (by norm_num)
  · exact sA hr hq inRu (by norm_num)
  · exact sA hr hq inRz (by norm_num)
  · exact sA hr hq inZu (by norm_num)
  · exact sA hr hq inZz (by norm_num)
  · exact sA hr hq iV0R (by norm_num)
  · exact sA hr hq iV0Z (by norm_num)
  · exact sA hr hq iAR1 (by norm_num)
  · exact sA hr hq iAZ1 (by norm_num)

/-- A lower bound of a mean from a centre and two deviations. -/
theorem mean_lower {A B C : ℂ} {m e1 e2 : ℝ} (hA : ‖A‖ = m) (hB : ‖B‖ ≤ e1) (hC : ‖C‖ ≤ e2) :
    m - e1 - e2 ≤ ‖A + B + C‖ := by
  have h1 := norm_sub_le (A + B + C) (B + C)
  have h2 := norm_add_le B C
  rw [show A + B + C - (B + C) = A by ring, hA] at h1
  linarith

/-- The transport of the surrogate `U` from the `ι_q` norm node. -/
theorem Lt_xA4 (ι : ℝ) : Lt ι (xA 4) =
    ((2 : ℂ) ^ 128)⁻¹ • Ex.eval XA trA_LU + ((ι - iotaqA : ℝ) : ℂ) • xA 6 := by
  rw [Lt_split ι (ana_xA 4), dTh_xA4, dPs_xA4]
  simp only [trA_LU, Ex.eval, iotaqA, Iqc, Qc]
  rw [show XA 8 = xA 8 from rfl, show XA 6 = xA 6 from rfl]
  simp only [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ]
  module

/-- The transport of the surrogate `z` from the `ι_q` norm node. -/
theorem Lt_xA5 (ι : ℝ) : Lt ι (xA 5) =
    ((2 : ℂ) ^ 128)⁻¹ • Ex.eval XA trA_LZ + ((ι - iotaqA : ℝ) : ℂ) • xA 7 := by
  rw [Lt_split ι (ana_xA 5), dTh_xA5, dPs_xA5]
  simp only [trA_LZ, Ex.eval, iotaqA, Iqc, Qc]
  rw [show XA 9 = xA 9 from rfl, show XA 7 = xA 7 from rfl]
  simp only [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ]
  module

/-- The bound of `𝓛 xA 4`. -/
theorem Lt_xA4_bd {r ι : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16)
    (hι : |ι - iotaqA| ≤ 1 / 2 ^ Qc) :
    Bd r (Lt ι (xA 4)) (((bLU / 2 ^ 128 + BA 6 / 2 ^ 128 : ℚ) : ℝ)) := by
  rw [Lt_xA4]
  refine (((nA_LU hr hq).smul _).add ((normA hq 6 (by norm_num)).smul _)).le ?_
  rw [norm_inv, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  have hB : (0 : ℝ) ≤ BA 6 := (normA hq 6 (by norm_num)).nonneg
  have hι' : |ι - iotaqA| ≤ 1 / 2 ^ 128 := by simpa [Qc] using hι
  have := mul_le_mul_of_nonneg_right hι' hB
  push_cast [bLU] at this ⊢
  linarith

/-- The bound of `𝓛 xA 5`. -/
theorem Lt_xA5_bd {r ι : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16)
    (hι : |ι - iotaqA| ≤ 1 / 2 ^ Qc) :
    Bd r (Lt ι (xA 5)) (((bLZ / 2 ^ 128 + BA 7 / 2 ^ 128 : ℚ) : ℝ)) := by
  rw [Lt_xA5]
  refine (((nA_LZ hr hq).smul _).add ((normA hq 7 (by norm_num)).smul _)).le ?_
  rw [norm_inv, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  have hB : (0 : ℝ) ≤ BA 7 := (normA hq 7 (by norm_num)).nonneg
  have hι' : |ι - iotaqA| ≤ 1 / 2 ^ 128 := by simpa [Qc] using hι
  have := mul_le_mul_of_nonneg_right hι' hB
  push_cast [bLZ] at this ⊢
  linarith

/-! ## The oracle-frame admissibility near the surrogate -/

set_option maxHeartbeats 4000000 in
-- one long proof assembling about 40 bounds
set_option maxRecDepth 100000 in
set_option linter.style.longLine false in
/-- **Admissibility in the oracle frame** at every torus within the closeness radii of the
surrogate. -/
theorem admO_near {r : ℝ} (hr : 0 < r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) {ι : ℝ}
    (hι : |ι - iotaqA| ≤ 1 / 2 ^ Qc) {c : SCG} (hc : ConstsOK c) {uo zo : FA} (hu : Ana uo)
    (hz : Ana zo) (hU : Bd r (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd r (zo - xA 5) ((muq + tZ : ℚ) : ℝ))
    (hA : Bd r (dTh uo - xA 6) ((muq + tAU : ℚ) : ℝ))
    (hB : Bd r (dTh zo - xA 7) ((muq + tAZ : ℚ) : ℝ))
    (hLU : Bd r (Lt ι uo - Lt ι (xA 4)) ((muq + 2387 / 10000 * tAU + 2 * tPU : ℚ) : ℝ))
    (hLZ : Bd r (Lt ι zo - Lt ι (xA 5)) ((muq + 2387 / 10000 * tAZ + 2 * tPZ : ℚ) : ℝ)) :
    AdmO c ι r uo zo := by
  have hr0 := hr.le
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23⟩ := hc
  -- the field polynomials
  obtain ⟨dD', bD'⟩ := fld_D hr0 hq hU hZ
  obtain ⟨dDu', bDu'⟩ := fld_Du hr0 hq hU hZ
  obtain ⟨dDz', bDz'⟩ := fld_Dz hr0 hq hU hZ
  obtain ⟨dnR', bnR'⟩ := fld_nR hr0 hq hU hZ
  obtain ⟨dnRu', bnRu'⟩ := fld_nRu hr0 hq hU hZ
  obtain ⟨dnRz', bnRz'⟩ := fld_nRz hr0 hq hU hZ
  obtain ⟨dnZ', bnZ'⟩ := fld_nZ hr0 hq hU hZ
  obtain ⟨dnZu', bnZu'⟩ := fld_nZu hr0 hq hU hZ
  obtain ⟨dnZz', bnZz'⟩ := fld_nZz hr0 hq hU hZ
  -- frame vectors and W₀
  have eVR : V0Ro uo - V0Ro (xA 4) = uo - xA 4 := by simp only [V0Ro]; ring
  have eVZ : V0Zo zo - V0Zo (xA 5) = zo - xA 5 := by simp only [V0Zo]; ring
  have bVR0 : Bd r (V0Ro (xA 4)) ((BA iV0R + EA iV0R : ℚ) : ℝ) := by
    rw [V0Ro_surr]; exact sA hr0 hq _ (by norm_num)
  have bVZ0 : Bd r (V0Zo (xA 5)) ((BA iV0Z + EA iV0Z : ℚ) : ℝ) := by
    rw [V0Zo_surr]; exact sA hr0 hq _ (by norm_num)
  have bVR : Bd r (V0Ro uo) (((BA iV0R + EA iV0R : ℚ) : ℝ) + ((muq + tU : ℚ) : ℝ)) :=
    Bd_near bVR0 (by rw [eVR]; exact hU)
  have bVZ : Bd r (V0Zo zo) (((BA iV0Z + EA iV0Z : ℚ) : ℝ) + ((muq + tZ : ℚ) : ℝ)) :=
    Bd_near bVZ0 (by rw [eVZ]; exact hZ)
  have eW : W0o uo zo - W0o (xA 4) (xA 5) = (dTh uo - xA 6) * V0Zo zo +
      xA 6 * (V0Zo zo - V0Zo (xA 5)) - ((dTh zo - xA 7) * V0Ro uo +
      xA 7 * (V0Ro uo - V0Ro (xA 4))) := by
    rw [W0o, W0o, dTh_xA4, dTh_xA5]; ring
  have bW : Bd r (W0o uo zo - W0o (xA 4) (xA 5)) (dWq : ℝ) := by
    rw [eW, eVZ, eVR]
    refine (((hA.mul hr0 bVZ).add ((normA hq 6 (by norm_num)).mul hr0 hZ)).sub
      ((hB.mul hr0 bVR).add ((normA hq 7 (by norm_num)).mul hr0 hU))).le ?_
    have := qleA (show (muq + tAU) * (BA iV0Z + EA iV0Z + (muq + tZ)) + BA 6 * (muq + tZ) +
      ((muq + tAZ) * (BA iV0R + EA iV0R + (muq + tU)) + BA 7 * (muq + tU)) ≤ dWq by kernel_fact)
    push_cast at this ⊢; linarith
  -- the approximate inverses at the surrogate
  have heD : Bd r (xA iqD * Fo dD (xA 4) (xA 5) - 1) (epsD : ℝ) := by
    have h := nA_eD hr0 hq
    rw [eval_eD] at h
    exact h
  have heW : Bd r (xA iqW * W0o (xA 4) (xA 5) - 1) (epsW : ℝ) := by
    have h := nA_eW hr0 hq
    rw [eval_eW] at h
    exact h
  have heR : Bd r (xA iqR * RofG dkR0 (xA 4) - 1) (epsR : ℝ) := by
    have h := nA_eR hr0 hq
    rw [eval_eR] at h
    exact h
  have eR : RofG dkR0 uo - RofG dkR0 (xA 4) = uo - xA 4 := by simp only [RofG]; ring
  -- the inverses at the torus
  have aD := approx_near hr0 (normA hq iqD (by norm_num)) heD dD'
  have aW := approx_near hr0 (normA hq iqW (by norm_num)) heW bW
  have aR := approx_near hr0 (normA hq iqR (by norm_num)) heR (by rw [eR]; exact hU)
  obtain ⟨uD, anD, sD', zD, kD⟩ := inv_of_approx hr (normA hq iqD (by norm_num)) aD
    (by exact_mod_cast (show epsD + BA iqD * dlD < 1 by kernel_fact))
  obtain ⟨uW, anW, sW', zW, kW⟩ := inv_of_approx hr (normA hq iqW (by norm_num)) aW
    (by exact_mod_cast (show epsW + BA iqW * dWq < 1 by kernel_fact))
  obtain ⟨uR, anR, sR', -, -⟩ := inv_of_approx hr (normA hq iqR (by norm_num)) aR
    (by exact_mod_cast (show epsR + BA iqR * (muq + tU) < 1 by kernel_fact))
  -- the torsion numerator
  have hx := hx_surr hr0 hq
  have hh : ∀ i, Bd r ((fun i => yP uo zo i - yP (xA 4) (xA 5) i) i) ((bQd i : ℚ) : ℝ) := by
    intro i
    fin_cases i
    · exact dD'
    · exact dnR'
    · exact dnZ'
    · exact dDu'
    · exact dDz'
    · exact dnRu'
    · exact dnRz'
    · exact dnZu'
    · exact dnZz'
    · change Bd r (V0Ro uo - V0Ro (xA 4)) _; rw [eVR]; exact hU
    · change Bd r (V0Zo zo - V0Zo (xA 5)) _; rw [eVZ]; exact hZ
    · change Bd r (cenO _ - cenO _) _; rw [sub_self]; exact (Bd_zero r).le (by norm_num [bQd])
    · change Bd r (cenO _ - cenO _) _; rw [sub_self]; exact (Bd_zero r).le (by norm_num [bQd])
  have hP := Bd.eval_add_sub hr0 hx hh Qp
  rw [show (yP (xA 4) (xA 5) + fun i => yP uo zo i - yP (xA 4) (xA 5) i) = yP uo zo by
    funext i; simp, ← Pofo_eq, ← Pofo_eq,
    show ((fun i => ((aQd i : ℚ) : ℝ)) + fun i => ((bQd i : ℚ) : ℝ)) =
      fun i => (((aQd + bQd) i : ℚ) : ℝ) by funext i; simp, majD_Qp] at hP
  have dP : Bd r (Pofo uo zo - Pofo (xA 4) (xA 5)) (dPq : ℝ) :=
    hP.le (qleA (by kernel_fact))
  -- the torsion centre at the torus
  have bR0 : Bd r (RofG dkR0 (xA 4)) ((BA iR + EA iR : ℚ) : ℝ) := by
    rw [R_surr]; exact sA hr0 hq _ (by norm_num)
  have dR7 := Bd_pow_sub hr0 bR0 (by rw [eR]; exact hU) 7
  have bR7 : Bd r (RofG dkR0 (xA 4) ^ 7) ((BA iR7 + EA iR7 : ℚ) : ℝ) := by
    have h := sA hr0 hq iR7 (by norm_num)
    rw [show XA iR7 = RvA ^ 7 * zvA ^ 0 from rfl, pow_zero, mul_one,
      show RvA = RofG dkR0 (xA 4) from R_surr.symm] at h
    exact h
  have bP0 : Bd r (Pofo (xA 4) (xA 5)) ((BA iP + EA iP : ℚ) : ℝ) := by
    rw [Pofo_surr]; exact sA hr0 hq _ (by norm_num)
  have bPu : Bd r (Pofo uo zo) (((BA iP + EA iP : ℚ) : ℝ) + dPq) := Bd_near bP0 dP
  have dRP := (dR7.mul hr0 bPu).add (bR7.mul hr0 dP)
  rw [show (RofG dkR0 uo ^ 7 - RofG dkR0 (xA 4) ^ 7) * Pofo uo zo +
      RofG dkR0 (xA 4) ^ 7 * (Pofo uo zo - Pofo (xA 4) (xA 5)) =
      RofG dkR0 uo ^ 7 * Pofo uo zo - RofG dkR0 (xA 4) ^ 7 * Pofo (xA 4) (xA 5) by ring] at dRP
  have bqDW : Bd r (xA iqD ^ 3 * xA iqW ^ 2) ((BA iqDW + EA iqDW : ℚ) : ℝ) := by
    have h := sA hr0 hq iqDW (by norm_num)
    rw [show XA iqDW = qDWa from rfl, qDWa, qD3a, qW2a, qD2a] at h
    rw [show xA iqD ^ 3 * xA iqW ^ 2 = xA iqD * xA iqD * xA iqD * (xA iqW * xA iqW) by ring]
    exact h
  set Yu := RofG dkR0 uo ^ 7 * Pofo uo zo * (xA iqD ^ 3 * xA iqW ^ 2) with hYu
  have eY : Yu - XA iY = (RofG dkR0 uo ^ 7 * Pofo uo zo -
      RofG dkR0 (xA 4) ^ 7 * Pofo (xA 4) (xA 5)) * (xA iqD ^ 3 * xA iqW ^ 2) := by
    have hP' : Pofo (xA 4) (xA 5) = Pa := Pofo_surr
    have hR' : RofG dkR0 (xA 4) = RvA := R_surr
    change Yu - Ya = _
    rw [Ya, PRa, qDWa, qD3a, qW2a, qD2a, hP', hR', hYu]; ring
  have dY := dRP.mul hr0 bqDW
  rw [← eY] at dY
  set δY : ℚ := (((BA iR + EA iR) + (muq + tU)) ^ 7 - (BA iR + EA iR) ^ 7) *
    ((BA iP + EA iP) + dPq) + (BA iR7 + EA iR7) * dPq with hδY
  have dY' : Bd r (Yu - XA iY) (((δY * (BA iqDW + EA iqDW) : ℚ) : ℝ)) :=
    dY.le (le_of_eq (by rw [hδY]; push_cast; ring))
  have bY0 := sA hr0 hq iY (by norm_num)
  have bYu : Bd r Yu (((BA iY + EA iY : ℚ) : ℝ) + ((δY * (BA iqDW + EA iqDW) : ℚ) : ℝ)) :=
    Bd_near bY0 dY'
  have mYu : ((16213491557858100427 / 2 ^ 60 : ℚ) : ℝ) - EA iY -
      ((δY * (BA iqDW + EA iqDW) : ℚ) : ℝ) ≤ ‖avg Yu‖ := by
    have h1 : ‖avg (XA iY) - avg (xA iY)‖ ≤ EA iY := by
      rw [← avg_sub]; exact (ballA_all hr0 hq iY (by norm_num)).norm_avg_le hr0
    have h2 : ‖avg Yu - avg (XA iY)‖ ≤ ((δY * (BA iqDW + EA iqDW) : ℚ) : ℝ) := by
      rw [← avg_sub]; exact dY'.norm_avg_le hr0
    have h3 : avg Yu = avg (xA iY) + (avg (XA iY) - avg (xA iY)) + (avg Yu - avg (XA iY)) := by
      ring
    rw [h3]
    exact mean_lower (by rw [avg_xA_Y, Complex.norm_ratCast, abs_of_pos (by norm_num)]) h1 h2
  -- the factor near `1`
  have zZ := Bd_mul_one_sub hr0 (Bd_pow_one_sub hr0 zD 3) (Bd_pow_one_sub hr0 zW 2)
  obtain ⟨hT1, hT2⟩ := torsion_bounds hr0 bYu mYu zZ
  have eT : Talgo uo zo = Yu * (Ring.inverse (xA iqD * Fo dD uo zo) ^ 3 *
      Ring.inverse (xA iqW * W0o uo zo) ^ 2) := by
    rw [Talgo, kD, kW, hYu]; ring
  -- the transport
  have bLt : Bd r (Lt ι uo) (((bLU / 2 ^ 128 + BA 6 / 2 ^ 128 +
      (muq + 2387 / 10000 * tAU + 2 * tPU) : ℚ)) : ℝ) := by
    have h := Bd_near (Lt_xA4_bd hr0 hq hι) hLU
    exact h.le (le_of_eq (by push_cast; ring))
  have bLz : Bd r (Lt ι zo) (((bLZ / 2 ^ 128 + BA 7 / 2 ^ 128 +
      (muq + 2387 / 10000 * tAZ + 2 * tPZ) : ℚ)) : ℝ) := by
    have h := Bd_near (Lt_xA5_bd hr0 hq hι) hLZ
    exact h.le (le_of_eq (by push_cast; ring))
  have fin : ∀ {X : FA} {a b : ℚ} {cc : ℝ}, Bd r X (a : ℝ) → a ≤ b → (b : ℝ) ≤ cc → Bd r X cc :=
    fun h hab hb => h.le ((qleA hab).trans hb)
  refine
  { ana_u := hu
    ana_z := hz
    unit_D := uD
    unit_R := uR
    unit_W := uW
    ana_Di := anD
    ana_Ri := anR
    ana_Wi := anW
    hu := fin (a := BA 4 + (muq + tU)) ((Bd_near (normA hq 4 (by norm_num)) hU).le (by push_cast; linarith)) (by kernel_fact) c1
    hz := fin (a := BA 5 + (muq + tZ)) ((Bd_near (normA hq 5 (by norm_num)) hZ).le (by push_cast; linarith)) (by kernel_fact) c2
    hV0R := fin (a := BA iV0R + EA iV0R + (muq + tU)) (bVR.le (by push_cast; linarith)) (by kernel_fact) c3
    hV0Z := fin (a := BA iV0Z + EA iV0Z + (muq + tZ)) (bVZ.le (by push_cast; linarith)) (by kernel_fact) c4
    hR := fin (a := BA iR + EA iR + (muq + tU)) ((Bd_near bR0 (by rw [eR]; exact hU)).le (by push_cast; linarith)) (by kernel_fact) c5
    hRt := fin (a := BA 6 + (muq + tAU)) ((Bd_near (normA hq 6 (by norm_num)) hA).le (by push_cast; linarith)) (by kernel_fact) c6
    hzt := fin (a := BA 7 + (muq + tAZ)) ((Bd_near (normA hq 7 (by norm_num)) hB).le (by push_cast; linarith)) (by kernel_fact) c7
    hLR := fin bLt (by kernel_fact) c8
    hLz := fin bLz (by kernel_fact) c9
    hbD := fin bD' (by kernel_fact) c10
    hbDu := fin bDu' (by kernel_fact) c11
    hbDz := fin bDz' (by kernel_fact) c12
    hbnR := fin bnR' (by kernel_fact) c13
    hbnRu := fin bnRu' (by kernel_fact) c14
    hbnRz := fin bnRz' (by kernel_fact) c15
    hbnZ := fin bnZ' (by kernel_fact) c16
    hbnZu := fin bnZu' (by kernel_fact) c17
    hbnZz := fin bnZz' (by kernel_fact) c18
    hsD := sD'.le ((div_cast_le (show BA iqD / (1 - (epsD + BA iqD * dlD)) ≤ sDC by kernel_fact)).trans
      c19)
    hsR := sR'.le ((div_cast_le
      (show BA iqR / (1 - (epsR + BA iqR * (muq + tU))) ≤ sRC by kernel_fact)).trans c20)
    hsW := sW'.le ((div_cast_le (show BA iqW / (1 - (epsW + BA iqW * dWq)) ≤ sWC by kernel_fact)).trans
      c21)
    hT := by
      rw [eT]
      refine hT1.le (le_trans ?_ c22)
      have := qleA (show (BA iY + EA iY + δY * (BA iqDW + EA iqDW)) *
        (1 + ((1 + (1 / (1 - (epsD + BA iqD * dlD)) - 1)) ^ 3 *
          (1 + (1 / (1 - (epsW + BA iqW * dWq)) - 1)) ^ 2 - 1)) ≤ tTC by kernel_fact)
      push_cast at this ⊢
      linarith
    hτ := by
      rw [eT]
      refine le_trans c23 (le_trans ?_ hT2)
      have := qleA (show tauC ≤ (16213491557858100427 / 2 ^ 60 - EA iY - δY * (BA iqDW + EA iqDW)) -
        (BA iY + EA iY + δY * (BA iqDW + EA iqDW)) *
        ((1 + (1 / (1 - (epsD + BA iqD * dlD)) - 1)) ^ 3 *
          (1 + (1 / (1 - (epsW + BA iqW * dWq)) - 1)) ^ 2 - 1) by kernel_fact)
      push_cast at this ⊢
      linarith }


/-! ## The main theorem -/

set_option maxRecDepth 100000 in
set_option linter.style.longLine false in
/-- **Admissibility near torus A (N-33 item 8).** Every analytic torus `(u, z)` that is
`μ`-close (`μ ≤ 10⁻¹²`) to the data torus `(u₀A, z₀A)` on a strip `0 < ρ ≤ 0.045` satisfies the
admissibility bounds `AdmBoundsG c ι_A ρ u z` of `dkFieldTC`, for every `c` dominating the certified
constants. -/
theorem dk_adm {c : SCG} (hc : ConstsOK c) {μ ρ : ℝ} (hμ : μ ≤ (muq : ℝ)) (hρ : 0 < ρ)
    (hρr : ρ ≤ 9 / 200) {u z : FA} (hu : Ana u) (hz : Ana z)
    (hC : Close ρ DommaschkKamDio.dkIotaA u z u₀A z₀A μ) :
    dkFieldTC.AdmBoundsG c DommaschkKamDio.dkIotaA ρ u z := by
  have hq : Real.exp ρ ≤ (68553 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hρr).trans exp_dk_le
  have hr0 := hρ.le
  set ι := DommaschkKamDio.dkIotaA
  have hu' := ana_rotψi hu
  have hz' := ana_rotψi hz
  have eU0 : rotψi u₀A = Uo := rotψi_rotψ Uo
  have eZ0 : rotψi z₀A = Zo := rotψi_rotψ Zo
  -- closeness in the oracle frame
  have cU : Bd ρ (rotψi u - Uo) μ := by rw [← eU0, ← rotψi_sub]; exact Bd_rotψi hC.du
  have cZ : Bd ρ (rotψi z - Zo) μ := by rw [← eZ0, ← rotψi_sub]; exact Bd_rotψi hC.dz
  have cA : Bd ρ (dTh (rotψi u) - dTh Uo) μ := by
    have h := Bd_rotψi hC.dut
    rw [rotψi_sub] at h
    change Bd ρ (dS 1 0 (rotψi u) - dS 1 0 Uo) μ
    rw [dS_rotψi 1 0 hu, ← eU0, dS_rotψi 1 0 ana_u₀A]; exact h
  have cB : Bd ρ (dTh (rotψi z) - dTh Zo) μ := by
    have h := Bd_rotψi hC.dzt
    rw [rotψi_sub] at h
    change Bd ρ (dS 1 0 (rotψi z) - dS 1 0 Zo) μ
    rw [dS_rotψi 1 0 hz, ← eZ0, dS_rotψi 1 0 ana_z₀A]; exact h
  have cLU : Bd ρ (Lt ι (rotψi u) - Lt ι Uo) μ := by
    have h := Bd_rotψi hC.duL
    rw [rotψi_sub] at h
    change Bd ρ (dS ι 2 (rotψi u) - dS ι 2 Uo) μ
    rw [dS_rotψi _ _ hu, ← eU0, dS_rotψi _ _ ana_u₀A]; exact h
  have cLZ : Bd ρ (Lt ι (rotψi z) - Lt ι Zo) μ := by
    have h := Bd_rotψi hC.dzL
    rw [rotψi_sub] at h
    change Bd ρ (dS ι 2 (rotψi z) - dS ι 2 Zo) μ
    rw [dS_rotψi _ _ hz, ← eZ0, dS_rotψi _ _ ana_z₀A]; exact h
  -- the tails
  have gtU := Bd_tg_U hq
  have gtZ := Bd_tg_Z hq
  have gtAU := Bd_tg_AU hq
  have gtAZ := Bd_tg_AZ hq
  have gtPU := Bd_tg_PU hq
  have gtPZ := Bd_tg_PZ hq
  rw [← Uo_sub_xA] at gtU
  rw [← Zo_sub_xA] at gtZ
  rw [← dTh_tailU] at gtAU
  rw [← dTh_tailZ] at gtAZ
  rw [← dPs_tailU] at gtPU
  rw [← dPs_tailZ] at gtPZ
  have inp : ∀ {X Y W : FA} {t : ℚ}, Bd ρ (X - Y) μ → Bd ρ (Y - W) (t : ℝ) →
      Bd ρ (X - W) ((muq + t : ℚ) : ℝ) := fun h1 h2 => by
    have := h1.add h2
    rw [sub_add_sub_cancel] at this
    exact this.le (by push_cast; linarith)
  have hLt : ∀ {X x xθ xψ : FA} {tθ tψ : ℚ}, Ana X → Ana x → Bd ρ (dTh X - xθ) tθ →
      Bd ρ (dS 0 1 X - xψ) tψ → dTh x = xθ → dS 0 1 x = xψ →
      Bd ρ (Lt ι (X) - Lt ι x) ((2387 / 10000 * tθ + 2 * tψ : ℚ) : ℝ) :=
    fun hX hx hθ hψ eθ eψ => by
      have := Lt_tail dkIotaA_abs_le hX hx hθ hψ eθ eψ
      rw [show Lt ι (_ - _) = Lt ι _ - Lt ι _ from dS_sub _ _ hX hx] at this
      exact this.le (le_of_eq (by push_cast; ring))
  have hLU : Bd ρ (Lt ι (rotψi u) - Lt ι (xA 4)) ((muq + 2387 / 10000 * tAU + 2 * tPU : ℚ) : ℝ) := by
    have h := inp cLU (hLt ana_Uo (ana_xA 4) gtAU gtPU dTh_xA4 dPs_xA4)
    exact h.le (le_of_eq (by simp only [tAU, tPU]; push_cast; ring))
  have hLZ : Bd ρ (Lt ι (rotψi z) - Lt ι (xA 5)) ((muq + 2387 / 10000 * tAZ + 2 * tPZ : ℚ) : ℝ) := by
    have h := inp cLZ (hLt ana_Zo (ana_xA 5) gtAZ gtPZ dTh_xA5 dPs_xA5)
    exact h.le (le_of_eq (by simp only [tAZ, tPZ]; push_cast; ring))
  have hι : |ι - iotaqA| ≤ 1 / 2 ^ Qc := by rw [abs_sub_comm]; exact iotaqA_close
  have h := admO_near hρ hq hι hc hu' hz' (inp cU gtU) (inp cZ gtZ) (inp cA gtAU) (inp cB gtAZ)
    hLU hLZ
  have := h.toG
  rwa [rotψ_rotψi, rotψ_rotψi] at this

/-- **The admissibility hypothesis `hadm` of `FlowFieldG.KamHG`** for torus A, for any constants
`c` with strip `c.ρ ≤ 0.045`, `c.ρ − 6δ₀ > 0` and closeness `μ ≤ 10⁻¹²`. -/
theorem dk_hadm {c : SCG} (hc : ConstsOK c) {μ : ℝ} (hμ : μ ≤ (muq : ℝ)) (hρ : c.ρ ≤ 9 / 200)
    (hρ6 : 0 < c.ρ - 6 * c.δ0) :
    ∀ ρ u z, c.ρ - 6 * c.δ0 ≤ ρ → ρ ≤ c.ρ → Ana u → Ana z →
      Close ρ DommaschkKamDio.dkIotaA u z u₀A z₀A μ →
      dkFieldTC.AdmBoundsG c DommaschkKamDio.dkIotaA ρ u z :=
  fun _ _ _ h1 h2 hu hz hC => dk_adm hc hμ (by linarith) (by linarith) hu hz hC

end PlasmaLean.Design.DommaschkKamA
