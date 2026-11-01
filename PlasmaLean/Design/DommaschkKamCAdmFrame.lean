/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCKronW
public import PlasmaLean.Design.DommaschkKamIdentCheck
public import PlasmaLean.Design.KamFlowIterationG

/-!
# Torus-C admissibility: the oracle frame and the transfer lemmas

The admissibility bounds `FlowFieldG.AdmBoundsG` of the Dommaschk field with the moving centre of
torus C (`dkFieldTC`, `Design/DommaschkKamCTorus`) are certified in the oracle angle `ψₒ = 2φ`
(the angle of the data and of the low-resolution chain `Design/DommaschkKamCAdm*`) and transferred
to every torus close to the data torus. This file provides the infrastructure, independently of the
data:

* **the inverse rotation** `rotψi = rotψ³` (`rotψ_rotψi`, `rotψi_rotψ`), and the behaviour of `rotψ`
  under `Bd`, `Ring.inverse`, `avg`, constants;
* **oracle-frame quantities** `Fo p u z = ev (xBo u z) p` (the field polynomials), `V0Ro`, `V0Zo`,
  `W0o`, `Pofo`, `Talgo`, and the identities `dkFieldTC.Dof (rotψ u) (rotψ z) = rotψ (Fo dD u z)`
  etc. (`Dof_rot`, …, `Talg_rot`);
* **`AdmO`**: the oracle-frame admissibility bounds, and `AdmO.toG`: they give `AdmBoundsG` for the
  rotated torus;
* **Lipschitz bounds** of sparse polynomials (`Bd_pow_sub`, `Bd_mono_sub`, `Bd_ev_sub`: the rational
  majorant `lipQ`, `lipR_cast`);
* **approximate inverses** (`inv_of_approx`: from `‖q d − 1‖ ≤ ε < 1`, `d` is a unit with
  `‖d⁻¹‖ ≤ ‖q‖/(1 − ε)`) and products near `1` (`Bd_mul_one_sub`, `Bd_pow_one_sub`);
* **the torsion numerator** as a polynomial `Qp` in 13 quantities (`Pofo_eq`).

**Sanity.** `rotψi_one` (degenerate), `lipQ_nil`, `Bd_pow_sub_zero`, and `Qp` at the zero point.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex

/-! ## The inverse rotation -/

/-- `rotψ⁴ = id`. -/
theorem rotψ4 (x : FA) : rotψ (rotψ (rotψ (rotψ x))) = x := by
  refine ext_coeff fun n => ?_
  simp only [coeff_rotψ]
  have h : I ^ n.2 * (I ^ n.2 * (I ^ n.2 * I ^ n.2)) = 1 := by
    rw [← zpow_add₀ I_ne_zero, ← zpow_add₀ I_ne_zero, ← zpow_add₀ I_ne_zero,
      show n.2 + (n.2 + (n.2 + n.2)) = 4 * n.2 by ring, zpow_mul]
    simp
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  rw [show I ^ n.2 * I ^ n.2 * I ^ n.2 * I ^ n.2 =
    I ^ n.2 * (I ^ n.2 * (I ^ n.2 * I ^ n.2)) by ring, h, one_mul]

/-- The inverse rotation `ψ ↦ ψ − π/2`. -/
def rotψi (x : FA) : FA := rotψ (rotψ (rotψ x))

/-- `rotψ ∘ rotψi = id`. -/
theorem rotψ_rotψi (x : FA) : rotψ (rotψi x) = x := rotψ4 x

/-- `rotψi ∘ rotψ = id`. -/
theorem rotψi_rotψ (x : FA) : rotψi (rotψ x) = x := rotψ4 x

/-- **Sanity (degenerate)**: `rotψi 1 = 1`. -/
theorem rotψi_one : rotψi 1 = 1 := by simp [rotψi, rotψ_one]

/-- `rotψi` preserves strip bounds. -/
theorem Bd_rotψi {ρ B : ℝ} {x : FA} (h : Bd ρ x B) : Bd ρ (rotψi x) B :=
  Bd_rotψ (Bd_rotψ (Bd_rotψ h))

/-- `rotψi` preserves analyticity. -/
theorem ana_rotψi {x : FA} (h : Ana x) : Ana (rotψi x) := ana_rotψ (ana_rotψ (ana_rotψ h))

/-- `rotψi` is subtractive. -/
theorem rotψi_sub (x y : FA) : rotψi (x - y) = rotψi x - rotψi y := by
  simp only [rotψi, rotψ_sub]

/-- `rotψi` commutes with the derivatives. -/
theorem dS_rotψi (a b : ℂ) {x : FA} (hx : Ana x) : dS a b (rotψi x) = rotψi (dS a b x) := by
  rw [rotψi, dS_rotψ a b (ana_rotψ (ana_rotψ hx)), dS_rotψ a b (ana_rotψ hx), dS_rotψ a b hx]
  rfl

/-- Bounds of a rotated element. -/
theorem Bd_of_rotψ {ρ B : ℝ} {x : FA} (h : Bd ρ x B) : Bd ρ (rotψ x) B := Bd_rotψ h

/-- `rotψ` fixes constants. -/
theorem rotψ_algebraMap (c : ℂ) : rotψ (algebraMap ℂ FA c) = algebraMap ℂ FA c :=
  rotψHom.commutes c

/-- `rotψ` commutes with inverses of units. -/
theorem rotψ_inverse {y : FA} (hy : IsUnit y) : rotψ (Ring.inverse y) = Ring.inverse (rotψ y) :=
  map_ringInverse rotψHom hy

/-- `rotψ` preserves units. -/
theorem isUnit_rotψ {y : FA} (hy : IsUnit y) : IsUnit (rotψ y) := hy.map rotψHom

/-- `rotψ` commutes with powers. -/
theorem rotψ_pow (x : FA) (n : ℕ) : rotψ (x ^ n) = rotψ x ^ n := map_pow rotψHom x n

/-- `rotψ` preserves the mean. -/
theorem avg_rotψ (y : FA) : avg (rotψ y) = avg y := by
  simp [avg, coeff_rotψ]

/-! ## Oracle-frame quantities -/

/-- The torus point in the oracle angle: `(u, z, cos ψₒ, sin ψₒ, 0, 0)`. -/
def xBo (u z : FA) : Fin 6 → FA := ![u, z, cSo, sSo, 0, 0]

/-- The strip-frame torus point of a rotated torus is the rotated oracle point. -/
theorem xB_rot (u z : FA) : xB (rotψ u) (rotψ z) = fun i => rotψ (xBo u z i) := by
  funext i
  fin_cases i <;> simp [xB, xBo, rotψ_cSo, rotψ_sSo, rotψ_zero]

/-- Sparse polynomials commute with `rotψ`. -/
theorem ev_rot (x : Fin 6 → FA) (p : DkPoly.SP) :
    DkPoly.ev (fun i => rotψ (x i)) p = rotψ (DkPoly.ev x p) := by
  rw [← DkPoly.eval_toPE, ← DkPoly.eval_toPE, rotψ_eval]

/-- A field polynomial in the oracle frame. -/
def Fo (p : DkPoly.SP) (u z : FA) : FA := DkPoly.ev (xBo u z) p

/-- An angle-only polynomial in the oracle frame. -/
def cenO (p : DkPoly.SP) : FA := DkPoly.ev (xBo 0 0) p

/-- `V₀_R = u − a_R` in the oracle frame. -/
def V0Ro (u : FA) : FA := u - cenO cenR

/-- `V₀_z = z − a_z` in the oracle frame. -/
def V0Zo (z : FA) : FA := z - cenO cenZ

/-- `W₀` in the oracle frame. -/
def W0o (u z : FA) : FA := dTh u * V0Zo z - dTh z * V0Ro u

/-- The torsion numerator in the oracle frame. -/
def Pofo (u z : FA) : FA := PolyExpr.eval (xBo u z) (Pp cenR cenZ)

/-- The torsion `T₀ = R⁷ D⁻³ W₀⁻² P` in the oracle frame. -/
def Talgo (u z : FA) : FA :=
  RofG dkR0 u ^ 7 * Ring.inverse (Fo dD u z) ^ 3 * Ring.inverse (W0o u z) ^ 2 * Pofo u z

/-- Angle-only polynomials do not see the torus. -/
theorem ev_AO_xBo {p : DkPoly.SP} (hp : DkPoly.AO p = true) (u z : FA) :
    DkPoly.ev (xBo u z) p = cenO p :=
  DkPoly.ev_congr_AO hp rfl rfl

/-- The field polynomial `D` of a rotated torus. -/
theorem Dof_rot (u z : FA) : dkFieldTC.Dof (rotψ u) (rotψ z) = rotψ (Fo dD u z) := by
  change PolyExpr.eval (xB (rotψ u) (rotψ z)) (DkPoly.toPE dD) = _
  rw [xB_rot, DkPoly.eval_toPE, ev_rot]; rfl

/-- A polynomial evaluated at a rotated torus. -/
theorem evPE_rot (u z : FA) (p : DkPoly.SP) :
    PolyExpr.eval (xB (rotψ u) (rotψ z)) (DkPoly.toPE p) = rotψ (Fo p u z) := by
  rw [xB_rot, DkPoly.eval_toPE, ev_rot]; rfl

/-- A `u`-derivative at a rotated torus. -/
theorem pdU_rot (u z : FA) (p : DkPoly.SP) :
    pd (xB (rotψ u) (rotψ z)) 0 (DkPoly.toPE p) = rotψ (Fo (DkPoly.dU p) u z) := by
  rw [DkPoly.pd_toPE_U, xB_rot, ev_rot]; rfl

/-- A `z`-derivative at a rotated torus. -/
theorem pdZ_rot (u z : FA) (p : DkPoly.SP) :
    pd (xB (rotψ u) (rotψ z)) 1 (DkPoly.toPE p) = rotψ (Fo (DkPoly.dZ p) u z) := by
  rw [DkPoly.pd_toPE_Z, xB_rot, ev_rot]; rfl

/-- The centre polynomials of a rotated frame. -/
theorem cen_rot (p : DkPoly.SP) : cen (DkPoly.toPE p) = rotψ (cenO p) := by
  have h := evPE_rot 0 0 p
  rw [rotψ_zero] at h
  exact h

/-- `R = R₀ + u` of a rotated torus. -/
theorem R_rot (u : FA) : dkFieldTC.R (rotψ u) = rotψ (RofG dkR0 u) := by
  change RofG dkR0 (rotψ u) = _
  simp only [RofG]
  rw [rotψ_add, rotψ_algebraMap]

/-- `V₀_R` of a rotated torus. -/
theorem V0R_rot (u : FA) : dkFieldTC.V0R (rotψ u) = rotψ (V0Ro u) := by
  change rotψ u - cen (DkPoly.toPE cenR) = _
  rw [cen_rot, V0Ro, rotψ_sub]

/-- `V₀_z` of a rotated torus. -/
theorem V0Z_rot (z : FA) : dkFieldTC.V0Z (rotψ z) = rotψ (V0Zo z) := by
  change rotψ z - cen (DkPoly.toPE cenZ) = _
  rw [cen_rot, V0Zo, rotψ_sub]

/-- `∂_θ` of a rotated torus. -/
theorem dTh_rot {u : FA} (hu : Ana u) : dTh (rotψ u) = rotψ (dTh u) := dS_rotψ 1 0 hu

/-- `𝓛` of a rotated torus. -/
theorem Lt_rot (ι : ℝ) {u : FA} (hu : Ana u) : Lt ι (rotψ u) = rotψ (Lt ι u) := dS_rotψ _ _ hu

/-- `W₀` of a rotated torus. -/
theorem W0_rot {u z : FA} (hu : Ana u) (hz : Ana z) :
    dkFieldTC.W0 (rotψ u) (rotψ z) = rotψ (W0o u z) := by
  change dTh (rotψ u) * dkFieldTC.V0Z (rotψ z) - dTh (rotψ z) * dkFieldTC.V0R (rotψ u) = _
  rw [dTh_rot hu, dTh_rot hz, V0Z_rot, V0R_rot, W0o, rotψ_sub, rotψ_mul, rotψ_mul]

/-- The torsion numerator of a rotated torus. -/
theorem Pof_rot (u z : FA) : dkFieldTC.Pof (rotψ u) (rotψ z) = rotψ (Pofo u z) := by
  change PolyExpr.eval (xB (rotψ u) (rotψ z)) (DommaschkKam.Pp cenR cenZ) = _
  rw [xB_rot, ← rotψ_eval]; rfl

/-! ## The oracle-frame admissibility bounds -/

/-- **The admissibility bounds in the oracle frame** (the fields of `AdmBoundsG` for the
oracle-frame quantities). -/
structure AdmO (c : SCG) (ι ρ : ℝ) (u z : FA) : Prop where
  /-- Analyticity. -/
  ana_u : Ana u
  /-- Analyticity. -/
  ana_z : Ana z
  /-- `D` is a unit. -/
  unit_D : IsUnit (Fo dD u z)
  /-- `R` is a unit. -/
  unit_R : IsUnit (RofG dkR0 u)
  /-- `W₀` is a unit. -/
  unit_W : IsUnit (W0o u z)
  /-- `D⁻¹` is analytic. -/
  ana_Di : Ana (Ring.inverse (Fo dD u z))
  /-- `R⁻¹` is analytic. -/
  ana_Ri : Ana (Ring.inverse (RofG dkR0 u))
  /-- `W₀⁻¹` is analytic. -/
  ana_Wi : Ana (Ring.inverse (W0o u z))
  /-- Torus bound. -/
  hu : Bd ρ u c.au
  /-- Torus bound. -/
  hz : Bd ρ z c.az
  /-- Frame vector. -/
  hV0R : Bd ρ (V0Ro u) c.avR
  /-- Frame vector. -/
  hV0Z : Bd ρ (V0Zo z) c.avZ
  /-- `R`. -/
  hR : Bd ρ (RofG dkR0 u) c.aR
  /-- `∂_θ u`. -/
  hRt : Bd ρ (dTh u) c.aRt
  /-- `∂_θ z`. -/
  hzt : Bd ρ (dTh z) c.azt
  /-- `𝓛 u`. -/
  hLR : Bd ρ (Lt ι u) c.aLR
  /-- `𝓛 z`. -/
  hLz : Bd ρ (Lt ι z) c.aLz
  /-- Field bound. -/
  hbD : Bd ρ (Fo dD u z) c.bD
  /-- Field bound. -/
  hbDu : Bd ρ (Fo (DkPoly.dU dD) u z) c.bDu
  /-- Field bound. -/
  hbDz : Bd ρ (Fo (DkPoly.dZ dD) u z) c.bDz
  /-- Field bound. -/
  hbnR : Bd ρ (Fo dnR u z) c.bnR
  /-- Field bound. -/
  hbnRu : Bd ρ (Fo (DkPoly.dU dnR) u z) c.bnRu
  /-- Field bound. -/
  hbnRz : Bd ρ (Fo (DkPoly.dZ dnR) u z) c.bnRz
  /-- Field bound. -/
  hbnZ : Bd ρ (Fo dnZ u z) c.bnZ
  /-- Field bound. -/
  hbnZu : Bd ρ (Fo (DkPoly.dU dnZ) u z) c.bnZu
  /-- Field bound. -/
  hbnZz : Bd ρ (Fo (DkPoly.dZ dnZ) u z) c.bnZz
  /-- Inverse bound. -/
  hsD : Bd ρ (Ring.inverse (Fo dD u z)) c.sD
  /-- Inverse bound. -/
  hsR : Bd ρ (Ring.inverse (RofG dkR0 u)) c.sR
  /-- Inverse bound. -/
  hsW : Bd ρ (Ring.inverse (W0o u z)) c.sW
  /-- Torsion bound. -/
  hT : Bd ρ (Talgo u z) c.tT
  /-- Twist. -/
  hτ : c.τ ≤ ‖avg (Talgo u z)‖

/-- The torsion of a rotated torus. -/
theorem Talg_rot {u z : FA} (hu : Ana u) (hz : Ana z) (hD : IsUnit (Fo dD u z))
    (hW : IsUnit (W0o u z)) : dkFieldTC.Talg (rotψ u) (rotψ z) = rotψ (Talgo u z) := by
  change dkFieldTC.R (rotψ u) ^ 7 * Ring.inverse (dkFieldTC.Dof (rotψ u) (rotψ z)) ^ 3 *
    Ring.inverse (dkFieldTC.W0 (rotψ u) (rotψ z)) ^ 2 * dkFieldTC.Pof (rotψ u) (rotψ z) = _
  rw [R_rot, Dof_rot, W0_rot hu hz, Pof_rot, ← rotψ_inverse hD, ← rotψ_inverse hW, Talgo]
  simp only [rotψ_mul, rotψ_pow]

/-- **The oracle-frame bounds give the admissibility bounds** of the rotated torus. -/
theorem AdmO.toG {c : SCG} {ι ρ : ℝ} {u z : FA} (h : AdmO c ι ρ u z) :
    dkFieldTC.AdmBoundsG c ι ρ (rotψ u) (rotψ z) := by
  have hu := h.ana_u
  have hz := h.ana_z
  have eD := Dof_rot u z
  have eR := R_rot u
  have eW := W0_rot hu hz
  refine
  { frame := ⟨ana_rotψ hu, ana_rotψ hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
    hu := Bd_rotψ h.hu
    hz := Bd_rotψ h.hz
    hV0R := by rw [V0R_rot]; exact Bd_rotψ h.hV0R
    hV0Z := by rw [V0Z_rot]; exact Bd_rotψ h.hV0Z
    hR := by rw [eR]; exact Bd_rotψ h.hR
    hRt := by change Bd ρ (dTh (rotψ u)) _; rw [dTh_rot hu]; exact Bd_rotψ h.hRt
    hzt := by change Bd ρ (dTh (rotψ z)) _; rw [dTh_rot hz]; exact Bd_rotψ h.hzt
    hLR := by change Bd ρ (Lt ι (rotψ u)) _; rw [Lt_rot ι hu]; exact Bd_rotψ h.hLR
    hLz := by change Bd ρ (Lt ι (rotψ z)) _; rw [Lt_rot ι hz]; exact Bd_rotψ h.hLz
    hbD := by rw [eD]; exact Bd_rotψ h.hbD
    hbDu := by change Bd ρ (pd _ 0 (DkPoly.toPE dD)) _; rw [pdU_rot]; exact Bd_rotψ h.hbDu
    hbDz := by change Bd ρ (pd _ 1 (DkPoly.toPE dD)) _; rw [pdZ_rot]; exact Bd_rotψ h.hbDz
    hbnR := by
      change Bd ρ (PolyExpr.eval _ (DkPoly.toPE dnR)) _; rw [evPE_rot]; exact Bd_rotψ h.hbnR
    hbnRu := by change Bd ρ (pd _ 0 (DkPoly.toPE dnR)) _; rw [pdU_rot]; exact Bd_rotψ h.hbnRu
    hbnRz := by change Bd ρ (pd _ 1 (DkPoly.toPE dnR)) _; rw [pdZ_rot]; exact Bd_rotψ h.hbnRz
    hbnZ := by
      change Bd ρ (PolyExpr.eval _ (DkPoly.toPE dnZ)) _; rw [evPE_rot]; exact Bd_rotψ h.hbnZ
    hbnZu := by change Bd ρ (pd _ 0 (DkPoly.toPE dnZ)) _; rw [pdU_rot]; exact Bd_rotψ h.hbnZu
    hbnZz := by change Bd ρ (pd _ 1 (DkPoly.toPE dnZ)) _; rw [pdZ_rot]; exact Bd_rotψ h.hbnZz
    hsD := by
      change Bd ρ (Ring.inverse (dkFieldTC.Dof _ _)) _
      rw [eD, ← rotψ_inverse h.unit_D]; exact Bd_rotψ h.hsD
    hsR := by
      change Bd ρ (Ring.inverse (RofG dkR0 (rotψ u))) _
      rw [show RofG dkR0 (rotψ u) = dkFieldTC.R (rotψ u) from rfl, eR,
        ← rotψ_inverse h.unit_R]; exact Bd_rotψ h.hsR
    hsW := by
      change Bd ρ (Ring.inverse (dkFieldTC.W0 _ _)) _
      rw [eW, ← rotψ_inverse h.unit_W]; exact Bd_rotψ h.hsW
    hT := by rw [Talg_rot hu hz h.unit_D h.unit_W]; exact Bd_rotψ h.hT
    hτ := by rw [Talg_rot hu hz h.unit_D h.unit_W, avg_rotψ]; exact h.hτ }
  · rw [eD]; exact isUnit_rotψ h.unit_D
  · rw [eR]; exact isUnit_rotψ h.unit_R
  · rw [eW]; exact isUnit_rotψ h.unit_W
  · rw [eD, ← rotψ_inverse h.unit_D]; exact ana_rotψ h.ana_Di
  · change Ana (Ring.inverse (dkFieldTC.R (rotψ u)))
    rw [eR, ← rotψ_inverse h.unit_R]; exact ana_rotψ h.ana_Ri
  · rw [eW, ← rotψ_inverse h.unit_W]; exact ana_rotψ h.ana_Wi

/-! ## Lipschitz bounds of sparse polynomials -/

/-- **Powers**: `‖yⁿ − xⁿ‖ ≤ (A + h)ⁿ − Aⁿ` from `‖x‖ ≤ A`, `‖y − x‖ ≤ h`. -/
theorem Bd_pow_sub {ρ A h : ℝ} (hρ : 0 ≤ ρ) {x y : FA} (hx : Bd ρ x A) (hh : Bd ρ (y - x) h) :
    ∀ n : ℕ, Bd ρ (y ^ n - x ^ n) ((A + h) ^ n - A ^ n)
  | 0 => by simpa using Bd_zero ρ
  | n + 1 => by
    have hy : Bd ρ y (A + h) := by
      have := hx.add hh; rwa [add_sub_cancel] at this
    have h1 := ((Bd_pow_sub hρ hx hh n).mul hρ hy).add ((hx.pow hρ n).mul hρ hh)
    rw [show (y ^ n - x ^ n) * y + x ^ n * (y - x) = y ^ (n + 1) - x ^ (n + 1) by ring] at h1
    exact h1.le (le_of_eq (by ring))

/-- **Sanity (degenerate)**: the zeroth power has no deviation. -/
theorem Bd_pow_sub_zero {ρ A h : ℝ} (hρ : 0 ≤ ρ) {x y : FA} (hx : Bd ρ x A)
    (hh : Bd ρ (y - x) h) : Bd ρ (y ^ 0 - x ^ 0) 0 := by
  have := Bd_pow_sub hρ hx hh 0; simpa using this

/-- **Monomials** `u^a z^b`. -/
theorem Bd_mono_sub {ρ A0 A1 h0 h1 : ℝ} (hρ : 0 ≤ ρ) {x0 x1 y0 y1 : FA} (hx0 : Bd ρ x0 A0)
    (hx1 : Bd ρ x1 A1) (hh0 : Bd ρ (y0 - x0) h0) (hh1 : Bd ρ (y1 - x1) h1) (a b : ℕ) :
    Bd ρ (y0 ^ a * y1 ^ b - x0 ^ a * x1 ^ b)
      ((A0 + h0) ^ a * (A1 + h1) ^ b - A0 ^ a * A1 ^ b) := by
  have hy1 : Bd ρ y1 (A1 + h1) := by
    have := hx1.add hh1; rwa [add_sub_cancel] at this
  have h := ((Bd_pow_sub hρ hx0 hh0 a).mul hρ (hy1.pow hρ b)).add
    ((hx0.pow hρ a).mul hρ (Bd_pow_sub hρ hx1 hh1 b))
  rw [show (y0 ^ a - x0 ^ a) * y1 ^ b + x0 ^ a * (y1 ^ b - x1 ^ b) =
    y0 ^ a * y1 ^ b - x0 ^ a * x1 ^ b by ring] at h
  exact h.le (le_of_eq (by ring))

/-- The real Lipschitz majorant of a sparse polynomial in `(u, z)` (angle variables fixed). -/
def lipR (A0 A1 h0 h1 C : ℝ) (p : DkPoly.SP) : ℝ :=
  (p.map fun t => |((t.q : ℚ) : ℝ)| * (((A0 + h0) ^ t.a * (A1 + h1) ^ t.b - A0 ^ t.a * A1 ^ t.b) *
    C ^ (t.c + t.d))).sum

/-- The rational Lipschitz majorant (kernel-computable). -/
def lipQ (A0 A1 h0 h1 C : ℚ) (p : DkPoly.SP) : ℚ :=
  (p.map fun t => |t.q| * (((A0 + h0) ^ t.a * (A1 + h1) ^ t.b - A0 ^ t.a * A1 ^ t.b) *
    C ^ (t.c + t.d))).sum

/-- **Sanity (degenerate)**: the empty polynomial. -/
theorem lipQ_nil (A0 A1 h0 h1 C : ℚ) : lipQ A0 A1 h0 h1 C [] = 0 := rfl

/-- The rational majorant is the real one. -/
theorem lipR_cast (A0 A1 h0 h1 C : ℚ) (p : DkPoly.SP) :
    lipR A0 A1 h0 h1 C p = ((lipQ A0 A1 h0 h1 C p : ℚ) : ℝ) := by
  induction p with
  | nil => simp [lipR, lipQ]
  | cons t p ih =>
    simp only [lipR, lipQ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- **Lipschitz bound of a sparse polynomial** in the torus variables `(u, z)` (the angle
variables unchanged). -/
theorem Bd_ev_sub {ρ A0 A1 h0 h1 C : ℝ} (hρ : 0 ≤ ρ) {x y : Fin 6 → FA} (h2 : y 2 = x 2)
    (h3 : y 3 = x 3) (hx0 : Bd ρ (x 0) A0) (hx1 : Bd ρ (x 1) A1) (hh0 : Bd ρ (y 0 - x 0) h0)
    (hh1 : Bd ρ (y 1 - x 1) h1) (hx2 : Bd ρ (x 2) C) (hx3 : Bd ρ (x 3) C) :
    ∀ p : DkPoly.SP, Bd ρ (DkPoly.ev y p - DkPoly.ev x p) (lipR A0 A1 h0 h1 C p)
  | [] => by simpa [lipR] using Bd_zero ρ
  | t :: p => by
    have ih := Bd_ev_sub hρ h2 h3 hx0 hx1 hh0 hh1 hx2 hx3 p
    have hm := Bd_mono_sub hρ hx0 hx1 hh0 hh1 t.a t.b
    have hcs : Bd ρ (x 2 ^ t.c * x 3 ^ t.d) (C ^ (t.c + t.d)) := by
      rw [pow_add]; exact (hx2.pow hρ _).mul hρ (hx3.pow hρ _)
    have hq := Bd_algebraMap ρ ((t.q : ℚ) : ℂ)
    have ht := (hq.mul hρ (hm.mul hρ hcs)).add ih
    have e : DkPoly.ev y (t :: p) - DkPoly.ev x (t :: p) =
        algebraMap ℂ FA ((t.q : ℚ) : ℂ) * ((y 0 ^ t.a * y 1 ^ t.b - x 0 ^ t.a * x 1 ^ t.b) *
          (x 2 ^ t.c * x 3 ^ t.d)) + (DkPoly.ev y p - DkPoly.ev x p) := by
      simp only [DkPoly.ev_cons, DkPoly.Tm.ev, h2, h3]; ring
    rw [e]
    refine ht.le (le_of_eq ?_)
    simp only [lipR, List.map_cons, List.sum_cons]
    rw [Complex.norm_ratCast]

/-! ## Approximate inverses and products near `1` -/

/-- **Approximate inverse**: from `‖q‖ ≤ B_q` and `‖q d − 1‖ ≤ ε < 1`, `d` is a unit, `d⁻¹` is
analytic, `‖d⁻¹‖ ≤ B_q/(1 − ε)`, `‖(q d)⁻¹ − 1‖ ≤ 1/(1 − ε) − 1` and `d⁻¹ = (q d)⁻¹ q`. -/
theorem inv_of_approx {ρ : ℝ} (hρ : 0 < ρ) {q d : FA} {Bq ε : ℝ} (hq : Bd ρ q Bq)
    (he : Bd ρ (q * d - 1) ε) (hε : ε < 1) :
    IsUnit d ∧ Ana (Ring.inverse d) ∧ Bd ρ (Ring.inverse d) (Bq / (1 - ε)) ∧
      Bd ρ (Ring.inverse (q * d) - 1) (1 / (1 - ε) - 1) ∧
      Ring.inverse d = Ring.inverse (q * d) * q := by
  have he' : Bd ρ (q * d - algebraMap ℂ FA 1) ε := by rwa [map_one]
  obtain ⟨hu, hb⟩ := Bd.inverse hρ.le he' (by rw [norm_one]; exact hε)
  rw [norm_one] at hb
  have hd : IsUnit d := isUnit_of_mul_isUnit_right hu
  have key : Ring.inverse d = Ring.inverse (q * d) * q := by
    have := (Ring.inverse_mul_eq_iff_eq_mul d 1 (Ring.inverse (q * d) * q) hd).2 (by
      rw [show d * (Ring.inverse (q * d) * q) = (q * d) * Ring.inverse (q * d) by ring,
        Ring.mul_inverse_cancel _ hu])
    rwa [mul_one] at this
  have h1 : Bd ρ (Ring.inverse d) (Bq / (1 - ε)) := by
    rw [key]; refine (hb.mul hρ.le hq).le (le_of_eq ?_); ring
  have h2 : Bd ρ (Ring.inverse (q * d) - 1) (1 / (1 - ε) - 1) := by
    have e : Ring.inverse (q * d) - 1 = Ring.inverse (q * d) * (-(q * d - 1)) := by
      linear_combination Ring.mul_inverse_cancel _ hu
    rw [e]
    have hε0 : 0 ≤ ε := he.nonneg
    refine (hb.mul hρ.le he.neg).le (le_of_eq ?_)
    rw [div_sub_one (show (1 - ε) ≠ 0 by linarith)]
    ring
  exact ⟨hd, ⟨ρ, _, hρ, h1⟩, h1, h2, key⟩

/-- Products near `1`: `‖ab − 1‖ ≤ (1 + α)(1 + β) − 1`. -/
theorem Bd_mul_one_sub {ρ α β : ℝ} (hρ : 0 ≤ ρ) {a b : FA} (ha : Bd ρ (a - 1) α)
    (hb : Bd ρ (b - 1) β) : Bd ρ (a * b - 1) ((1 + α) * (1 + β) - 1) := by
  have hb' : Bd ρ b (1 + β) := by
    have := (Bd_one ρ).add hb; rwa [add_sub_cancel] at this
  have h := (ha.mul hρ hb').add hb
  rw [show (a - 1) * b + (b - 1) = a * b - 1 by ring] at h
  exact h.le (le_of_eq (by ring))

/-- Powers near `1`: `‖aⁿ − 1‖ ≤ (1 + α)ⁿ − 1`. -/
theorem Bd_pow_one_sub {ρ α : ℝ} (hρ : 0 ≤ ρ) {a : FA} (ha : Bd ρ (a - 1) α) (n : ℕ) :
    Bd ρ (a ^ n - 1) ((1 + α) ^ n - 1) := by
  have := Bd_pow_sub hρ (Bd_one ρ) ha n
  simpa using this

/-- **Torsion and twist from a centre and a factor near `1`**: `‖Y Z‖ ≤ n_Y (1 + ζ)` and
`|⟨Y Z⟩| ≥ m_Y − n_Y ζ`. -/
theorem torsion_bounds {ρ nY mY ζ : ℝ} (hρ : 0 ≤ ρ) {Y Z : FA} (hY : Bd ρ Y nY)
    (hm : mY ≤ ‖avg Y‖) (hZ : Bd ρ (Z - 1) ζ) :
    Bd ρ (Y * Z) (nY * (1 + ζ)) ∧ mY - nY * ζ ≤ ‖avg (Y * Z)‖ := by
  have hZ' : Bd ρ Z (1 + ζ) := by
    have := (Bd_one ρ).add hZ; rwa [add_sub_cancel] at this
  refine ⟨hY.mul hρ hZ', ?_⟩
  have e : Y * Z = Y + Y * (Z - 1) := by ring
  rw [e, avg_add]
  have h1 := (hY.mul hρ hZ).norm_avg_le hρ
  have h2 := norm_sub_norm_le (avg Y) (-avg (Y * (Z - 1)))
  rw [sub_neg_eq_add, norm_neg] at h2
  linarith

/-! ## The torsion numerator as a polynomial in 13 quantities -/

/-- The torsion formula `P = Y_R V₀_z − Y_z V₀_R` as a polynomial in
`(D, n_R, n_z, D_u, D_z, n_R,u, n_R,z, n_z,u, n_z,z, V₀_R, V₀_z, a_R', a_z')` (the structure of
`DommaschkKam.Pp`). -/
def Qp : PolyExpr ℂ (Fin 13) :=
  let D := PolyExpr.var 0
  let Du := PolyExpr.var 3
  let Dz := PolyExpr.var 4
  let vR := PolyExpr.var 9
  let vZ := PolyExpr.var 10
  let Y (n nu nz a' : PolyExpr ℂ (Fin 13)) : PolyExpr ℂ (Fin 13) :=
    .sub (.add (.sub (.mul n D) (.mul D (.add (.mul nu vR) (.mul nz vZ))))
      (.mul n (.add (.mul Du vR) (.mul Dz vZ)))) (.mul (.mul D D) a')
  .sub (.mul (Y (.var 1) (.var 5) (.var 6) (.var 11)) vZ)
    (.mul (Y (.var 2) (.var 7) (.var 8) (.var 12)) vR)

/-- The 13 quantities of the torsion formula at a torus (oracle frame). -/
def yP (u z : FA) : Fin 13 → FA :=
  ![Fo dD u z, Fo dnR u z, Fo dnZ u z, Fo (DkPoly.dU dD) u z, Fo (DkPoly.dZ dD) u z,
    Fo (DkPoly.dU dnR) u z, Fo (DkPoly.dZ dnR) u z, Fo (DkPoly.dU dnZ) u z,
    Fo (DkPoly.dZ dnZ) u z, V0Ro u, V0Zo z, cenO (DkPoly.phiS cenR), cenO (DkPoly.phiS cenZ)]

/-- **The torsion numerator is `Qp` of the 13 quantities.** -/
theorem Pofo_eq (u z : FA) : Pofo u z = PolyExpr.eval (yP u z) Qp := by
  have hR := ev_AO_xBo (DkPoly.AO_phiS cenR_AO) u z
  have hZ := ev_AO_xBo (DkPoly.AO_phiS cenZ_AO) u z
  have hR0 := ev_AO_xBo cenR_AO u z
  have hZ0 := ev_AO_xBo cenZ_AO u z
  simp only [Pofo, DommaschkKam.Pp, Qp, PolyExpr.eval, DkPoly.eval_toPE, yP, Fo, V0Ro, V0Zo,
    DommaschkKam.Dp, hR, hZ, hR0, hZ0]
  simp [xBo]

/-- **Sanity (degenerate)**: `Qp` vanishes when all quantities vanish. -/
theorem Qp_zero : PolyExpr.eval (fun _ => (0 : FA)) Qp = 0 := by
  simp [Qp, PolyExpr.eval]

end PlasmaLean.Design.DommaschkKamC
