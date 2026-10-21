/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Surface

/-!
# Family 2 surface integrands in the ridge-aligned frame

On the flux surface `ψ = k²/2` of Landreman's family 2 (`ε = 1/4`, `S = 4`) the Mercier
surface integrands `f dS/|∇ψ_t|³` are, in the coordinates `(χ, ζ)` of
`PlasmaLean.Design.LandremanFamily2Surface`, of the form `H/gp2` with `H` smooth and
`gp2 = |∇ψ|² = X² gX2 + λ² T² uI²`. For large `λ` the factor `λ² T² uI²` makes `1/gp2` sharply
peaked (width `O(1/λ)`) near the two "tips" of the flat poloidal cross-section, where
`uI = 0`. This module

* defines the integrands `HB`, `HX`, `HZ` (numerators of `∫ B² w`, `∫ B·Ξ w`, `∫ |Ξ|² w`) and
  the Jacobian factor `JacR = G/(λ h T cc)`;
* rotates the poloidal angle by `φ` with `sin φ = cosh ν sinh ν/R`, `cos φ = T/R`,
  `R = √(T² + cosh²ν sinh²ν)`, so that in the rotated angle `χ' = χ - φ`
  `uI = k (sin χ' R - corr)/T₀` with a small correction `corr = s₁ T Y²/(1 + cc)`
  (`uIc_rot`); hence `gp2 = a² + P (sin χ' R - corr)²` exactly (`gp2_rot`), with
  `a² = X² gX2`, `P = λ² T² k²/T₀²`. The peak is then at `sin χ' ≈ 0` for every `ζ`, and it
  is integrated exactly (Lorentzian kernel) by the validated quadrature of
  `LandremanFamily2Quad`;
* proves continuity of all integrands along continuous parametrizations of the circle
  (`continuous_closed`), needed for the substitution lemmas.

Everything here is exact algebra on the closed forms; no numerics.
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Rotated

open Real PlasmaLean.Design.LandremanFamily2Surface

/-! ## Integrand numerators -/

/-- Jacobian factor `G/(λ h T cc)` of `dV = Jac dψ dχ dζ` (paper (3.18)). -/
@[expose] def JacR (lam k s1 c1 s2 c2 : ℝ) : ℝ :=
  Gc (1 / 4) 4 k s1 c1 s2 c2 /
    (lam * hc (1 / 4) 4 k s1 c1 s2 * Tc (1 / 4) k s2 * cc k s1)

/-- Numerator of `∫ B² dS/|∇ψ|³`: `B² · Jac`. -/
@[expose] def HB (lam k s1 c1 s2 c2 : ℝ) : ℝ :=
  Bsq (1 / 4) 4 lam k s1 c1 s2 c2 * JacR lam k s1 c1 s2 c2

/-- Numerator of `∫ B·Ξ dS/|∇ψ|³`: `(dI B² + B·Δ) Jac`, `dI = λ - I'`. -/
@[expose] def HX (lam dI k s1 c1 s2 c2 : ℝ) : ℝ :=
  (dI * Bsq (1 / 4) 4 lam k s1 c1 s2 c2 + BD (1 / 4) 4 lam k s1 c1 s2 c2) *
    JacR lam k s1 c1 s2 c2

/-- Numerator of `∫ |Ξ|² dS/|∇ψ|³`: `(dI (dI B² + 2 B·Δ) + |Δ|²) Jac`. -/
@[expose] def HZ (lam dI k s1 c1 s2 c2 : ℝ) : ℝ :=
  (dI * (dI * Bsq (1 / 4) 4 lam k s1 c1 s2 c2 + 2 * BD (1 / 4) 4 lam k s1 c1 s2 c2) +
    gX2 (1 / 4) 4 k s1 c1 s2 c2 / lam ^ 2) * JacR lam k s1 c1 s2 c2

/-- `a² = X² gX2`. -/
@[expose] def aSq (k s1 c1 s2 c2 : ℝ) : ℝ := Xc k c1 ^ 2 * gX2 (1 / 4) 4 k s1 c1 s2 c2

/-- `P = λ² T² k²/T₀²`. -/
@[expose] def PR (lam k s1 s2 : ℝ) : ℝ :=
  lam ^ 2 * Tc (1 / 4) k s2 ^ 2 * k ^ 2 / T0c (1 / 4) k s1 s2 ^ 2

/-! ## The ridge-aligned rotation -/

/-- `ρ = cosh ν sinh ν / T`. -/
@[expose] def rhoR (k s2 : ℝ) : ℝ := chc (1 / 4) s2 * shc (1 / 4) s2 / Tc (1 / 4) k s2

/-- `D = √((1+ρ²)² - 4k²ρ²)`. -/
@[expose] def DR (k s2 : ℝ) : ℝ := √((1 + rhoR k s2 ^ 2) ^ 2 - 4 * k ^ 2 * rhoR k s2 ^ 2)

/-- `w = √(2/(1 + ρ² + D))`. -/
@[expose] def wR (k s2 : ℝ) : ℝ := √(2 / (1 + rhoR k s2 ^ 2 + DR k s2))

/-- `sin φ = ρ w`: the root of `k² s⁴ - (1+ρ²) s² + ρ² = 0` of the sign of `ρ`; the ridge
(`uI = 0`) of every flux surface lies at `χ = φ` and `χ = φ + π`. -/
@[expose] def sphr (k s2 : ℝ) : ℝ := rhoR k s2 * wR k s2

/-- `cos φ = √(1 - sin²φ)`. -/
@[expose] def cphr (k s2 : ℝ) : ℝ := √(1 - sphr k s2 ^ 2)

/-- `C = √(1 - k² sin²φ)` (`cos λz` at the ridge). -/
@[expose] def Cphr (k s2 : ℝ) : ℝ := √(1 - k ^ 2 * sphr k s2 ^ 2)

/-- `sin χ = sin χ' cos φ + cos χ' sin φ`. -/
@[expose] def s1r (k sp cp s2 : ℝ) : ℝ := sp * cphr k s2 + cp * sphr k s2

/-- `cos χ = cos χ' cos φ - sin χ' sin φ`. -/
@[expose] def c1r (k sp cp s2 : ℝ) : ℝ := cp * cphr k s2 - sp * sphr k s2

/-- The ridge function `f = s₁ cc T - c₁ cosh ν sinh ν` (so that `uI = k f/T₀`). -/
@[expose] def fR (k sp cp s2 : ℝ) : ℝ :=
  s1r k sp cp s2 * cc k (s1r k sp cp s2) * Tc (1 / 4) k s2 -
    c1r k sp cp s2 * chc (1 / 4) s2 * shc (1 / 4) s2

/-- The factor `g` with `f = sin χ' · g` on the half `cos χ' > -1`. -/
@[expose] def gAR (k sp cp s2 : ℝ) : ℝ :=
  Tc (1 / 4) k s2 / cphr k s2 * (cphr k s2 ^ 2 * cc k (s1r k sp cp s2) +
    sphr k s2 ^ 2 * Cphr k s2 + cp * sphr k s2 * cphr k s2 * k ^ 2 *
      (sphr k s2 * sp / (1 + cp) - cphr k s2) * (sphr k s2 + s1r k sp cp s2) /
        (cc k (s1r k sp cp s2) + Cphr k s2))

/-- The factor `g` with `f = sin χ' · g` on the half `cos χ' < 1`. -/
@[expose] def gBR (k sp cp s2 : ℝ) : ℝ :=
  Tc (1 / 4) k s2 / cphr k s2 * (cphr k s2 ^ 2 * cc k (s1r k sp cp s2) +
    sphr k s2 ^ 2 * Cphr k s2 + cp * sphr k s2 * cphr k s2 * k ^ 2 *
      (sphr k s2 - s1r k sp cp s2) * (sphr k s2 * sp / (1 - cp) + cphr k s2) /
        (cc k (s1r k sp cp s2) + Cphr k s2))

section Rot
variable {k sp cp s2 : ℝ}

/-- `D² = (1+ρ²)² - 4k²ρ² ≥ 0`. -/
theorem DR_sq (hk : k ^ 2 < 1) :
    DR k s2 ^ 2 = (1 + rhoR k s2 ^ 2) ^ 2 - 4 * k ^ 2 * rhoR k s2 ^ 2 := by
  unfold DR
  refine Real.sq_sqrt ?_
  have h := sq_nonneg (rhoR k s2)
  nlinarith [sq_nonneg (1 - rhoR k s2 ^ 2), mul_le_mul_of_nonneg_right hk.le h]

/-- `D ≥ 0`. -/
theorem DR_nonneg : 0 ≤ DR k s2 := Real.sqrt_nonneg _

/-- `w² = 2/(1 + ρ² + D)`. -/
theorem wR_sq : wR k s2 ^ 2 = 2 / (1 + rhoR k s2 ^ 2 + DR k s2) := by
  unfold wR
  have := DR_nonneg (k := k) (s2 := s2)
  exact Real.sq_sqrt (by positivity)

/-- `D > |1 - ρ²|`-type bound: `1 + ρ² + D > 2ρ²` for `k² < 1`. -/
theorem den_gt (hk : k ^ 2 < 1) : 2 * rhoR k s2 ^ 2 < 1 + rhoR k s2 ^ 2 + DR k s2 := by
  have hD := DR_sq (s2 := s2) hk
  have hD0 := DR_nonneg (k := k) (s2 := s2)
  have hr := sq_nonneg (rhoR k s2)
  by_contra hcon
  push Not at hcon
  have h1 : DR k s2 ≤ rhoR k s2 ^ 2 - 1 := by linarith
  have h2 : 0 ≤ rhoR k s2 ^ 2 - 1 := le_trans hD0 h1
  have h3 : DR k s2 ^ 2 ≤ (rhoR k s2 ^ 2 - 1) ^ 2 := pow_le_pow_left₀ hD0 h1 2
  rw [hD] at h3
  have : 0 < rhoR k s2 ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right hk this]

/-- `sin² φ < 1`. -/
theorem sphr_sq_lt (hk : k ^ 2 < 1) : sphr k s2 ^ 2 < 1 := by
  have hD0 := DR_nonneg (k := k) (s2 := s2)
  have hpos : 0 < 1 + rhoR k s2 ^ 2 + DR k s2 := by positivity
  unfold sphr
  rw [mul_pow, wR_sq, ← mul_div_assoc, div_lt_one hpos]
  linarith [den_gt (s2 := s2) hk]

/-- `cos φ > 0`. -/
theorem cphr_pos (hk : k ^ 2 < 1) : 0 < cphr k s2 :=
  Real.sqrt_pos.2 (by linarith [sphr_sq_lt (s2 := s2) hk])

/-- `cos² φ = 1 - sin² φ`. -/
theorem cphr_sq (hk : k ^ 2 < 1) : cphr k s2 ^ 2 = 1 - sphr k s2 ^ 2 :=
  Real.sq_sqrt (by linarith [sphr_sq_lt (s2 := s2) hk])

/-- `sin² φ + cos² φ = 1`. -/
theorem sphr_sq_add_cphr_sq (hk : k ^ 2 < 1) : sphr k s2 ^ 2 + cphr k s2 ^ 2 = 1 := by
  rw [cphr_sq hk]; ring

/-- `C > 0`. -/
theorem Cphr_pos (hk : k ^ 2 < 1) : 0 < Cphr k s2 := by
  have h := sphr_sq_lt (s2 := s2) hk
  have := sq_nonneg (sphr k s2)
  exact Real.sqrt_pos.2 (by nlinarith)

/-- `C² = 1 - k² sin² φ`. -/
theorem Cphr_sq (hk : k ^ 2 < 1) : Cphr k s2 ^ 2 = 1 - k ^ 2 * sphr k s2 ^ 2 := by
  have h := sphr_sq_lt (s2 := s2) hk
  have := sq_nonneg (sphr k s2)
  exact Real.sq_sqrt (by nlinarith)

/-- `w C = cos φ`. -/
theorem wR_mul_Cphr (hk : k ^ 2 < 1) : wR k s2 * Cphr k s2 = cphr k s2 := by
  have hD := DR_sq (s2 := s2) hk
  have hD0 := DR_nonneg (k := k) (s2 := s2)
  have hpos : 0 < 1 + rhoR k s2 ^ 2 + DR k s2 := by positivity
  have key : (wR k s2 * Cphr k s2) ^ 2 = cphr k s2 ^ 2 := by
    rw [mul_pow, Cphr_sq hk, cphr_sq hk]
    unfold sphr
    rw [mul_pow, wR_sq]
    field_simp
    linear_combination (-1 : ℝ) * hD
  have h1 : 0 ≤ wR k s2 * Cphr k s2 := mul_nonneg (Real.sqrt_nonneg _) (Cphr_pos hk).le
  exact (pow_left_inj₀ h1 (cphr_pos hk).le two_ne_zero).mp key

/-- **Ridge identity**: `sin φ · C · T = cos φ · cosh ν sinh ν`. -/
theorem ridge (hk : k ^ 2 < 1) :
    sphr k s2 * Cphr k s2 * Tc (1 / 4) k s2 = cphr k s2 * (chc (1 / 4) s2 * shc (1 / 4) s2) := by
  have hT := (T_pos (ε := 1 / 4) (s2 := s2) hk).ne'
  unfold sphr
  rw [mul_assoc (rhoR k s2), wR_mul_Cphr hk]
  unfold rhoR
  field_simp

/-- The rotated angle stays on the unit circle. -/
theorem s1r_sq_add_c1r_sq (hk : k ^ 2 < 1) (h : sp ^ 2 + cp ^ 2 = 1) :
    s1r k sp cp s2 ^ 2 + c1r k sp cp s2 ^ 2 = 1 := by
  have := sphr_sq_add_cphr_sq (s2 := s2) hk
  unfold s1r c1r
  linear_combination (sphr k s2 ^ 2 + cphr k s2 ^ 2) * h + this

/-- `uI = k f/T₀` in the rotated angle. -/
theorem uIc_rot : uIc (1 / 4) k (s1r k sp cp s2) (c1r k sp cp s2) s2 =
    k * fR k sp cp s2 / T0c (1 / 4) k (s1r k sp cp s2) s2 := by
  unfold uIc fR Yc Xc; ring

/-- **`|∇ψ|²` in the rotated frame:** `gp2 = a² + P f²`. -/
theorem gp2_rot (lam : ℝ) (hk : k ^ 2 < 1) (h : sp ^ 2 + cp ^ 2 = 1) (c2 : ℝ) :
    gp2 (1 / 4) 4 lam k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2 =
      aSq k (s1r k sp cp s2) (c1r k sp cp s2) s2 c2 +
        PR lam k (s1r k sp cp s2) s2 * fR k sp cp s2 ^ 2 := by
  have h1 := s1r_sq_add_c1r_sq (s2 := s2) hk h
  have hT0 := (T0_pos (ε := 1 / 4) (s2 := s2) h1 hk).ne'
  unfold gp2 aSq PR
  rw [uIc_rot]
  field_simp

/-- Algebraic core of the factorizations. -/
theorem fact_core (k sp cp s c C T chsh cc s1 c1 : ℝ) (hc0 : c ≠ 0)
    (hC : C ^ 2 = 1 - k ^ 2 * s ^ 2) (hcc : cc ^ 2 = 1 - k ^ 2 * s1 ^ 2) (hccC : cc + C ≠ 0)
    (hE : s * C * T = c * chsh) (hs1 : s1 = sp * c + cp * s) (hc1 : c1 = cp * c - sp * s) :
    s1 * cc * T - c1 * chsh = T / c * (sp * (c ^ 2 * cc + s ^ 2 * C) +
      cp * s * c * k ^ 2 * (s - s1) * (s + s1) / (cc + C)) := by
  have e2 : k ^ 2 * (s - s1) * (s + s1) / (cc + C) = cc - C := by
    rw [div_eq_iff hccC]
    linear_combination hC - hcc
  have hchsh : chsh = s * C * T / c := by field_simp; linarith
  rw [show cp * s * c * k ^ 2 * (s - s1) * (s + s1) / (cc + C) =
    cp * s * c * (k ^ 2 * (s - s1) * (s + s1) / (cc + C)) by ring, e2, hchsh, hs1, hc1]
  field_simp
  ring

/-- **Factorization on the half `cos χ' > -1`:** `f = sin χ' · g_A`. -/
theorem fR_eq_A (hk : k ^ 2 < 1) (h : sp ^ 2 + cp ^ 2 = 1) (hcp : 1 + cp ≠ 0) :
    fR k sp cp s2 = sp * gAR k sp cp s2 := by
  have h1 := s1r_sq_add_c1r_sq (s2 := s2) hk h
  have hcc := cc_sq (k := k) h1 hk
  have hccp := cc_pos (k := k) h1 hk
  have hC := Cphr_pos (s2 := s2) hk
  have hc := (cphr_pos (s2 := s2) hk).ne'
  have key := fact_core k sp cp (sphr k s2) (cphr k s2) (Cphr k s2) (Tc (1 / 4) k s2)
    (chc (1 / 4) s2 * shc (1 / 4) s2) (cc k (s1r k sp cp s2)) (s1r k sp cp s2) (c1r k sp cp s2)
    hc (Cphr_sq hk) (by rw [hcc]; unfold Yc; ring) (by positivity) (ridge hk) rfl rfl
  have hsm : sphr k s2 - s1r k sp cp s2 = sp * (sphr k s2 * sp / (1 + cp) - cphr k s2) := by
    unfold s1r; field_simp; linear_combination (-(sphr k s2)) * h
  unfold fR gAR
  rw [show s1r k sp cp s2 * cc k (s1r k sp cp s2) * Tc (1 / 4) k s2 -
    c1r k sp cp s2 * chc (1 / 4) s2 * shc (1 / 4) s2 = s1r k sp cp s2 * cc k (s1r k sp cp s2) *
    Tc (1 / 4) k s2 - c1r k sp cp s2 * (chc (1 / 4) s2 * shc (1 / 4) s2) by ring, key, hsm]
  ring

/-- **Factorization on the half `cos χ' < 1`:** `f = sin χ' · g_B`. -/
theorem fR_eq_B (hk : k ^ 2 < 1) (h : sp ^ 2 + cp ^ 2 = 1) (hcp : 1 - cp ≠ 0) :
    fR k sp cp s2 = sp * gBR k sp cp s2 := by
  have h1 := s1r_sq_add_c1r_sq (s2 := s2) hk h
  have hcc := cc_sq (k := k) h1 hk
  have hccp := cc_pos (k := k) h1 hk
  have hC := Cphr_pos (s2 := s2) hk
  have hc := (cphr_pos (s2 := s2) hk).ne'
  have key := fact_core k sp cp (sphr k s2) (cphr k s2) (Cphr k s2) (Tc (1 / 4) k s2)
    (chc (1 / 4) s2 * shc (1 / 4) s2) (cc k (s1r k sp cp s2)) (s1r k sp cp s2) (c1r k sp cp s2)
    hc (Cphr_sq hk) (by rw [hcc]; unfold Yc; ring) (by positivity) (ridge hk) rfl rfl
  have hsp : sphr k s2 + s1r k sp cp s2 = sp * (sphr k s2 * sp / (1 - cp) + cphr k s2) := by
    unfold s1r; field_simp; linear_combination (-(sphr k s2)) * h
  unfold fR gBR
  rw [show s1r k sp cp s2 * cc k (s1r k sp cp s2) * Tc (1 / 4) k s2 -
    c1r k sp cp s2 * chc (1 / 4) s2 * shc (1 / 4) s2 = s1r k sp cp s2 * cc k (s1r k sp cp s2) *
    Tc (1 / 4) k s2 - c1r k sp cp s2 * (chc (1 / 4) s2 * shc (1 / 4) s2) by ring, key, hsp]
  ring

end Rot

/-! ## Continuity along continuous parametrizations -/

section Cont
variable {X : Type*} [TopologicalSpace X] {s1 c1 s2 c2 : X → ℝ} {k lam dI : ℝ}

/-- Hypotheses on a parametrization `x ↦ (s1, c1, s2, c2)`: continuity, `(s1, c1)` on the unit
circle, `|c2| ≤ 1`, and `0 < k < 1`. -/
structure ParamOK (s1 c1 s2 c2 : X → ℝ) (k : ℝ) : Prop where
  hs1 : Continuous s1
  hc1 : Continuous c1
  hs2 : Continuous s2
  hc2 : Continuous c2
  h1 : ∀ x, s1 x ^ 2 + c1 x ^ 2 = 1
  hb2 : ∀ x, |c2 x| ≤ 1
  hk0 : 0 < k
  hk : k ^ 2 < 1

/-- Continuity of the elementary closed forms along a parametrization. -/
theorem cont_basic (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => Yc k (s1 x)) ∧ Continuous (fun x => Xc k (c1 x)) ∧
      Continuous (fun x => cc k (s1 x)) ∧ Continuous (fun x => chc (1 / 4) (s2 x)) ∧
      Continuous (fun x => shc (1 / 4) (s2 x)) ∧ Continuous (fun x => Tc (1 / 4) k (s2 x)) ∧
      Continuous (fun x => T0c (1 / 4) k (s1 x) (s2 x)) ∧
      Continuous (fun x => nuc (1 / 4) (s2 x)) := by
  have := P.hs1; have := P.hc1; have := P.hs2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Yc, Xc, cc, chc, shc, Tc, T0c, nuc] <;> fun_prop

/-- Continuity of `sin(σ - S)`. -/
theorem cont_sA (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => sA (1 / 4) k (s1 x) (c1 x) (s2 x)) := by
  obtain ⟨hY, hX, hcc, hch, hsh, hT, hT0, -⟩ := cont_basic (k := k) P
  exact (((hcc.mul hch).mul hX).add ((hY.mul hsh).mul hT)).div hT0
    (fun x => (T0_pos (P.h1 x) P.hk).ne')

/-- Continuity of `Im u`. -/
theorem cont_uIc (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => uIc (1 / 4) k (s1 x) (c1 x) (s2 x)) := by
  obtain ⟨hY, hX, hcc, hch, hsh, hT, hT0, -⟩ := cont_basic (k := k) P
  exact (((hY.mul hcc).mul hT).sub ((hch.mul hsh).mul hX)).div hT0
    (fun x => (T0_pos (P.h1 x) P.hk).ne')

/-- Continuity of `σ`. -/
theorem cont_sig (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => sigc (1 / 4) 4 k (s1 x) (c1 x) (s2 x)) :=
  continuous_const.add (Real.continuous_arcsin.comp (cont_sA P))

/-- Continuity of `h`. -/
theorem cont_h (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => hc (1 / 4) 4 k (s1 x) (c1 x) (s2 x)) := by
  have := cont_sig P
  simp only [hc]; fun_prop

/-- Continuity of `m`, `G`, `q`. -/
theorem cont_mGq (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => mc (1 / 4) 4 k (s1 x) (c1 x) (s2 x) (c2 x)) ∧
      Continuous (fun x => Gc (1 / 4) 4 k (s1 x) (c1 x) (s2 x) (c2 x)) ∧
      Continuous (fun x => qc (1 / 4) 4 k (s1 x) (c1 x) (s2 x)) := by
  have hh := cont_h P
  have hs := cont_sig P
  have hn := (cont_basic (k := k) P).2.2.2.2.2.2.2
  have := P.hc2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [mc, Gc, qc] <;> fun_prop

/-- Continuity of `r`. -/
theorem cont_r (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => rc (1 / 4) 4 k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨hm, -, hq⟩ := cont_mGq P
  exact (hm.pow 2).div hq (fun x => (q_pos (by norm_num)).ne')

/-- Continuity of `B²`. -/
theorem cont_Bsq (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => Bsq (1 / 4) 4 lam k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨-, hX, -, -, -, hT, -, -⟩ := cont_basic (k := k) P
  obtain ⟨hm, -, hq⟩ := cont_mGq P
  have hu := cont_uIc P
  have hmq := hm.div hq (fun x => (q_pos (by norm_num)).ne')
  exact (((hT.pow 2).add (hu.pow 2)).mul hmq).div_const _ |>.add ((hX.pow 2).div_const _)

/-- Continuity of `gX2`. -/
theorem cont_gX2 (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => gX2 (1 / 4) 4 k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨-, -, -, -, -, hT, -, -⟩ := cont_basic (k := k) P
  obtain ⟨hm, -, hq⟩ := cont_mGq P
  have hu := cont_uIc P
  have hr := cont_r P
  exact (hq.div hm (fun x => (m_pos (by norm_num) (P.hb2 x)).ne')).mul
    (((hT.pow 2).mul ((continuous_const.add hr).pow 2)).add
      ((hu.pow 2).mul ((continuous_const.sub hr).pow 2)))

/-- Continuity of `|∇ψ|²`. -/
theorem cont_gp2 (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => gp2 (1 / 4) 4 lam k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨-, hX, -, -, -, hT, -, -⟩ := cont_basic (k := k) P
  have hu := cont_uIc P
  have hg := cont_gX2 P
  exact ((hX.pow 2).mul hg).add ((continuous_const.mul (hT.pow 2)).mul (hu.pow 2))

/-- Continuity of `B·Δ`. -/
theorem cont_BD (P : ParamOK s1 c1 s2 c2 k) :
    Continuous (fun x => BD (1 / 4) 4 lam k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨-, -, -, -, -, hT, -, -⟩ := cont_basic (k := k) P
  have hu := cont_uIc P
  have hr := cont_r P
  exact (((hT.pow 2).mul (continuous_const.add hr)).sub
    ((hu.pow 2).mul (continuous_const.sub hr))).div_const _

/-- Continuity of the Jacobian factor. -/
theorem cont_JacR (P : ParamOK s1 c1 s2 c2 k) (hl : lam ≠ 0) :
    Continuous (fun x => JacR lam k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  obtain ⟨-, -, hcc, -, -, hT, -, -⟩ := cont_basic (k := k) P
  obtain ⟨-, hG, -⟩ := cont_mGq P
  have hh := cont_h P
  refine hG.div (((continuous_const.mul hh).mul hT).mul hcc) (fun x => ?_)
  have := hc_pos (ε := 1 / 4) (k := k) (s1 := s1 x) (c1 := c1 x) (s2 := s2 x)
    (by norm_num : (2 : ℝ) ≤ 4)
  have := T_pos (ε := 1 / 4) (s2 := s2 x) P.hk
  have := cc_pos (P.h1 x) P.hk
  positivity

/-- **Continuity of all integrands** along a continuous parametrization of the circle. -/
theorem continuous_closed (P : ParamOK s1 c1 s2 c2 k) (hl : lam ≠ 0) :
    Continuous (fun x => HB lam k (s1 x) (c1 x) (s2 x) (c2 x)) ∧
      Continuous (fun x => HX lam dI k (s1 x) (c1 x) (s2 x) (c2 x)) ∧
      Continuous (fun x => HZ lam dI k (s1 x) (c1 x) (s2 x) (c2 x)) ∧
      Continuous (fun x => gp2 (1 / 4) 4 lam k (s1 x) (c1 x) (s2 x) (c2 x)) := by
  have hB := cont_Bsq (lam := lam) P
  have hD := cont_BD (lam := lam) P
  have hg := cont_gX2 P
  have hJ := cont_JacR P hl
  refine ⟨hB.mul hJ, ((continuous_const.mul hB).add hD).mul hJ, ?_,
    cont_gp2 P⟩
  exact ((continuous_const.mul ((continuous_const.mul hB).add (continuous_const.mul hD))).add
    (hg.div_const _)).mul hJ

/-- `gp2 > 0` along the parametrization. -/
theorem gp2_pos_param (P : ParamOK s1 c1 s2 c2 k) (hl : lam ≠ 0) (x : X) :
    0 < gp2 (1 / 4) 4 lam k (s1 x) (c1 x) (s2 x) (c2 x) :=
  gp2_pos (P.h1 x) (by norm_num) (P.hb2 x) P.hk0 P.hk hl

end Cont

end PlasmaLean.Design.LandremanFamily2Rotated
