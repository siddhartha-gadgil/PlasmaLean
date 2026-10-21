/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicKernel
public import PlasmaLean.Design.PolygonCoilCubicCheck
public import PlasmaLean.Design.PolygonCoilSoundB

/-!
# Geometry of the cubic certificate: the rational circle parametrisation

The grid lines of the cubic certificate are the circles `t ↦ faceSigma kind (φ t) w` with
`φ t = π/2 + 2 arctan t` (`phiT`), i.e. the rational curve

`circ ρ ζ t = (-2ρt/(1 + t²), ρ(1 - t²)/(1 + t²), ζ)` (`faceSigma_phiT`).

* `hasDerivAt_circ`, `hasDerivAt_U1`, …, `hasDerivAt_U3`: its first four derivatives
  `U₁, …, U₄` (explicit rational vectors);
* `norm_U1`, `U1_perp`, `norm_U2perp`, `norm_U2_le`, `norm_U3_le`, `norm_U4_le`: with
  `α = -2t/(1 + t²)`, `|U₁| = 2ρ/(1 + t²)`, `U₂ - αU₁ ⊥ U₁`, `|U₂ - αU₁| = 4ρ/(1 + t²)²`,
  `|U₂| ≤ 4ρ`, `|U₃| ≤ 12ρ`, `|U₄| ≤ 48ρ` (from `|Uₖ|² = cₖ²ρ²/(1 + t²)^{k+1}`);
* `circ_dist`: `|circ ρ ζ t - circ ρ₀ ζ₀ t₀|² ≤ (ρ - ρ₀)² + (ζ - ζ₀)² + 4 max(ρ, ρ₀)² (t - t₀)²`;
* `cornerR_cornerXYZ4`, `helAt_corner4`: the checker's corners and `hel` values are the points
  `faceSigma kind (φ (m/4096)) (wn/wd)` and `hel` there.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-! ## The angle -/

/-- The grid angle `φ(t) = π/2 + 2 arctan t`. -/
@[expose] def phiT (t : ℝ) : ℝ := π / 2 + 2 * arctan t

/-- `cos φ(t) = -2t/(1 + t²)` for `φ(t) = π/2 + 2 arctan t`. -/
theorem cos_phiT (t : ℝ) : cos (phiT t) = -2 * t / (1 + t ^ 2) := by
  unfold phiT
  rw [cos_add, cos_pi_div_two, sin_pi_div_two, sin_two_mul, cos_arctan, sin_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  have hs : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2) = 1 + t ^ 2 := mul_self_sqrt h.le
  calc 0 * cos (2 * arctan t) - 1 * (2 * (t / sqrt (1 + t ^ 2)) * (1 / sqrt (1 + t ^ 2)))
      = -2 * t / (sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2)) := by ring
    _ = _ := by rw [hs]

/-- `sin φ(t) = (1 - t²)/(1 + t²)` for `φ(t) = π/2 + 2 arctan t`. -/
theorem sin_phiT (t : ℝ) : sin (phiT t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  unfold phiT
  rw [sin_add, cos_pi_div_two, sin_pi_div_two, cos_two_mul, cos_arctan]
  have h : 0 < 1 + t ^ 2 := by positivity
  rw [div_pow, one_pow, sq_sqrt h.le]
  field_simp
  ring

/-! ## Rational functions and their derivatives -/

/-- Derivative of a quintic polynomial in monomial form. -/
theorem hasDerivAt_quintic (a0 a1 a2 a3 a4 a5 y : ℝ) :
    HasDerivAt (fun y => a0 + a1 * y + a2 * y ^ 2 + a3 * y ^ 3 + a4 * y ^ 4 + a5 * y ^ 5)
      (a1 + 2 * a2 * y + 3 * a3 * y ^ 2 + 4 * a4 * y ^ 3 + 5 * a5 * y ^ 4) y := by
  have h5 := (hasDerivAt_pow 5 y).const_mul a5
  have := HasDerivAt.fun_add (hasDerivAt_quartic a0 a1 a2 a3 a4 y) h5
  exact this.congr_deriv (by push_cast; ring)

/-- Derivative of `p(t)/(1 + t²)ⁿ`. -/
theorem hasDerivAt_ratn {p : ℝ → ℝ} {p' t : ℝ} (n : ℕ) (hp : HasDerivAt p p' t) :
    HasDerivAt (fun s => p s / (1 + s ^ 2) ^ n)
      ((p' * (1 + t ^ 2) - 2 * n * t * p t) / (1 + t ^ 2) ^ (n + 1)) t := by
  have hq : HasDerivAt (fun s => (1 + s ^ 2) ^ n) (n * (1 + t ^ 2) ^ (n - 1) * (2 * t)) t := by
    have h1 : HasDerivAt (fun s => 1 + s ^ 2) (2 * t) t := by
      have := (hasDerivAt_pow 2 t).const_add 1
      exact this.congr_deriv (by push_cast; ring)
    exact h1.pow n
  have hne : (1 + t ^ 2) ^ n ≠ 0 := by positivity
  refine (hp.div hq hne).congr_deriv ?_
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rcases n with _ | n
  · simp; field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- The component functions `Aₖ`, `Bₖ` (`circ = ρ(A₀, B₀, ·)`, `Uₖ = ρ(Aₖ, Bₖ, 0)`). -/
@[expose] def cA0 (t : ℝ) : ℝ := -2 * t / (1 + t ^ 2)
/-- `B₀`. -/
@[expose] def cB0 (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
/-- `A₁`. -/
@[expose] def cA1 (t : ℝ) : ℝ := -2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2
/-- `B₁`. -/
@[expose] def cB1 (t : ℝ) : ℝ := -4 * t / (1 + t ^ 2) ^ 2
/-- `A₂`. -/
@[expose] def cA2 (t : ℝ) : ℝ := 4 * (3 * t - t ^ 3) / (1 + t ^ 2) ^ 3
/-- `B₂`. -/
@[expose] def cB2 (t : ℝ) : ℝ := -4 * (1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3
/-- `A₃`. -/
@[expose] def cA3 (t : ℝ) : ℝ := 12 * (1 - 6 * t ^ 2 + t ^ 4) / (1 + t ^ 2) ^ 4
/-- `B₃`. -/
@[expose] def cB3 (t : ℝ) : ℝ := 12 * (4 * t - 4 * t ^ 3) / (1 + t ^ 2) ^ 4
/-- `A₄`. -/
@[expose] def cA4 (t : ℝ) : ℝ := -48 * (5 * t - 10 * t ^ 3 + t ^ 5) / (1 + t ^ 2) ^ 5
/-- `B₄`. -/
@[expose] def cB4 (t : ℝ) : ℝ := 48 * (1 - 10 * t ^ 2 + 5 * t ^ 4) / (1 + t ^ 2) ^ 5

/-- A rational function given by a quintic numerator. -/
theorem hasDerivAt_rat5 (a0 a1 a2 a3 a4 a5 : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => (a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4 + a5 * s ^ 5) /
      (1 + s ^ 2) ^ n)
      (((a1 + 2 * a2 * t + 3 * a3 * t ^ 2 + 4 * a4 * t ^ 3 + 5 * a5 * t ^ 4) * (1 + t ^ 2) -
        2 * n * t * (a0 + a1 * t + a2 * t ^ 2 + a3 * t ^ 3 + a4 * t ^ 4 + a5 * t ^ 5)) /
        (1 + t ^ 2) ^ (n + 1)) t :=
  hasDerivAt_ratn n (hasDerivAt_quintic a0 a1 a2 a3 a4 a5 t)

/-- Derivative of `cA0`. -/
theorem hasDerivAt_cA0 (t : ℝ) : HasDerivAt cA0 (cA1 t) t := by
  have h := hasDerivAt_rat5 0 (-2) 0 0 0 0 1 t
  have e : cA0 = fun s => (0 + -2 * s + 0 * s ^ 2 + 0 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 1 := by funext s; unfold cA0; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cA1; field_simp; ring

/-- Derivative of `cB0`. -/
theorem hasDerivAt_cB0 (t : ℝ) : HasDerivAt cB0 (cB1 t) t := by
  have h := hasDerivAt_rat5 1 0 (-1) 0 0 0 1 t
  have e : cB0 = fun s => (1 + 0 * s + -1 * s ^ 2 + 0 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 1 := by funext s; unfold cB0; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cB1; field_simp; ring

/-- Derivative of `cA1`. -/
theorem hasDerivAt_cA1 (t : ℝ) : HasDerivAt cA1 (cA2 t) t := by
  have h := hasDerivAt_rat5 (-2) 0 2 0 0 0 2 t
  have e : cA1 = fun s => (-2 + 0 * s + 2 * s ^ 2 + 0 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 2 := by funext s; unfold cA1; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cA2; field_simp; ring

/-- Derivative of `cB1`. -/
theorem hasDerivAt_cB1 (t : ℝ) : HasDerivAt cB1 (cB2 t) t := by
  have h := hasDerivAt_rat5 0 (-4) 0 0 0 0 2 t
  have e : cB1 = fun s => (0 + -4 * s + 0 * s ^ 2 + 0 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 2 := by funext s; unfold cB1; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cB2; field_simp; ring

/-- Derivative of `cA2`. -/
theorem hasDerivAt_cA2 (t : ℝ) : HasDerivAt cA2 (cA3 t) t := by
  have h := hasDerivAt_rat5 0 12 0 (-4) 0 0 3 t
  have e : cA2 = fun s => (0 + 12 * s + 0 * s ^ 2 + -4 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 3 := by funext s; unfold cA2; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cA3; field_simp; ring

/-- Derivative of `cB2`. -/
theorem hasDerivAt_cB2 (t : ℝ) : HasDerivAt cB2 (cB3 t) t := by
  have h := hasDerivAt_rat5 (-4) 0 12 0 0 0 3 t
  have e : cB2 = fun s => (-4 + 0 * s + 12 * s ^ 2 + 0 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 3 := by funext s; unfold cB2; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cB3; field_simp; ring

/-- Derivative of `cA3`. -/
theorem hasDerivAt_cA3 (t : ℝ) : HasDerivAt cA3 (cA4 t) t := by
  have h := hasDerivAt_rat5 12 0 (-72) 0 12 0 4 t
  have e : cA3 = fun s => (12 + 0 * s + -72 * s ^ 2 + 0 * s ^ 3 + 12 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 4 := by funext s; unfold cA3; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cA4; field_simp; ring

/-- Derivative of `cB3`. -/
theorem hasDerivAt_cB3 (t : ℝ) : HasDerivAt cB3 (cB4 t) t := by
  have h := hasDerivAt_rat5 0 48 0 (-48) 0 0 4 t
  have e : cB3 = fun s => (0 + 48 * s + 0 * s ^ 2 + -48 * s ^ 3 + 0 * s ^ 4 + 0 * s ^ 5) /
      (1 + s ^ 2) ^ 4 := by funext s; unfold cB3; ring
  rw [e]; refine h.congr_deriv ?_
  unfold cB4; field_simp; ring

/-! ## The circle and its derivatives -/

/-- The rational circle `(-2ρt/(1 + t²), ρ(1 - t²)/(1 + t²), ζ)`. -/
@[expose] def circ (ρ ζ t : ℝ) : Space := (ρ * cA0 t) • eV 0 + (ρ * cB0 t) • eV 1 + ζ • eV 2
/-- First derivative of the circle. -/
@[expose] def U1 (ρ t : ℝ) : Space := (ρ * cA1 t) • eV 0 + (ρ * cB1 t) • eV 1
/-- Second derivative of the circle. -/
@[expose] def U2 (ρ t : ℝ) : Space := (ρ * cA2 t) • eV 0 + (ρ * cB2 t) • eV 1
/-- Third derivative of the circle. -/
@[expose] def U3 (ρ t : ℝ) : Space := (ρ * cA3 t) • eV 0 + (ρ * cB3 t) • eV 1
/-- Fourth derivative of the circle. -/
@[expose] def U4 (ρ t : ℝ) : Space := (ρ * cA4 t) • eV 0 + (ρ * cB4 t) • eV 1

/-- Derivative of `ρ a(t) e₀ + ρ b(t) e₁ + c`. -/
theorem hasDerivAt_pair {a b : ℝ → ℝ} {a' b' t : ℝ} (ρ : ℝ) (c : Space) (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => (ρ * a s) • eV 0 + (ρ * b s) • eV 1 + c)
      ((ρ * a') • eV 0 + (ρ * b') • eV 1) t := by
  have := (((ha.const_mul ρ).smul_const (eV 0)).add ((hb.const_mul ρ).smul_const (eV 1))).add_const
      c
  convert this using 1

/-- The first derivative of the circle is `U1`. -/
theorem hasDerivAt_circ (ρ ζ t : ℝ) : HasDerivAt (circ ρ ζ) (U1 ρ t) t := by
  have := hasDerivAt_pair ρ (ζ • eV 2) (hasDerivAt_cA0 t) (hasDerivAt_cB0 t)
  exact this

/-- The derivative of `U1` is `U2`. -/
theorem hasDerivAt_U1 (ρ t : ℝ) : HasDerivAt (U1 ρ) (U2 ρ t) t := by
  have := hasDerivAt_pair ρ 0 (hasDerivAt_cA1 t) (hasDerivAt_cB1 t)
  simp only [add_zero] at this
  exact this

/-- The derivative of `U2` is `U3`. -/
theorem hasDerivAt_U2 (ρ t : ℝ) : HasDerivAt (U2 ρ) (U3 ρ t) t := by
  have := hasDerivAt_pair ρ 0 (hasDerivAt_cA2 t) (hasDerivAt_cB2 t)
  simp only [add_zero] at this
  exact this

/-- The derivative of `U3` is `U4`. -/
theorem hasDerivAt_U3 (ρ t : ℝ) : HasDerivAt (U3 ρ) (U4 ρ t) t := by
  have := hasDerivAt_pair ρ 0 (hasDerivAt_cA3 t) (hasDerivAt_cB3 t)
  simp only [add_zero] at this
  exact this

/-- Norm squared of a planar vector. -/
theorem norm_pair_sq (a b : ℝ) : ‖a • eV 0 + b • eV 1‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_coords]; simp [eV]

/-- Inner product of planar vectors. -/
theorem inner_pair (a b c d : ℝ) : ⟪a • eV 0 + b • eV 1, c • eV 0 + d • eV 1⟫ = a * c + b * d := by
  rw [inner_coords]; simp [eV]

/-- A norm determined by its square. -/
theorem norm_of_sq {v : Space} {c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ^ 2 = c ^ 2) : ‖v‖ = c :=
  (pow_left_inj₀ (norm_nonneg _) hc two_ne_zero).mp h

/-- A norm bound from a bound on its square. -/
theorem norm_le_of_sq {v : Space} {c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ^ 2 ≤ c ^ 2) : ‖v‖ ≤ c :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).mp h

/-- The speed of the circle: `‖U1‖ = 2ρ/(1 + t²)`. -/
theorem norm_U1 {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : ‖U1 ρ t‖ = 2 * ρ / (1 + t ^ 2) := by
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  apply norm_of_sq (by positivity)
  unfold U1; rw [norm_pair_sq]; unfold cA1 cB1; field_simp; ring

/-- The tangential coefficient `α = -2t/(1 + t²)` of `U₂`. -/
@[expose] def alT (t : ℝ) : ℝ := -2 * t / (1 + t ^ 2)

/-- The component of `U2` orthogonal to `U1`. -/
theorem U1_perp (ρ t : ℝ) : ⟪U1 ρ t, U2 ρ t - alT t • U1 ρ t⟫ = 0 := by
  have e : U2 ρ t - alT t • U1 ρ t = (ρ * cA2 t - alT t * (ρ * cA1 t)) • eV 0 +
      (ρ * cB2 t - alT t * (ρ * cB1 t)) • eV 1 := by
    unfold U1 U2; rw [smul_add, smul_smul, smul_smul]; module
  rw [e]; unfold U1; rw [inner_pair]
  unfold cA1 cB1 cA2 cB2 alT
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp; ring

/-- Norm of the component of `U2` orthogonal to `U1`. -/
theorem norm_U2perp {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) :
    ‖U2 ρ t - alT t • U1 ρ t‖ = 4 * ρ / (1 + t ^ 2) ^ 2 := by
  have e : U2 ρ t - alT t • U1 ρ t = (ρ * cA2 t - alT t * (ρ * cA1 t)) • eV 0 +
      (ρ * cB2 t - alT t * (ρ * cB1 t)) • eV 1 := by
    unfold U1 U2; rw [smul_add, smul_smul, smul_smul]; module
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [e]; apply norm_of_sq (by positivity); rw [norm_pair_sq]
  unfold cA1 cB1 cA2 cB2 alT
  field_simp; ring

/-- `‖U2‖ ≤ 4ρ`. -/
theorem norm_U2_le {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : ‖U2 ρ t‖ ≤ 4 * ρ := by
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ (1 + t ^ 2) ^ 3 := one_le_pow₀ (by nlinarith)
  apply norm_le_of_sq (by positivity); unfold U2; rw [norm_pair_sq]
  have e : (ρ * cA2 t) ^ 2 + (ρ * cB2 t) ^ 2 = 16 * ρ ^ 2 / (1 + t ^ 2) ^ 3 := by
    unfold cA2 cB2; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ρ]

/-- `‖U3‖ ≤ 12ρ`. -/
theorem norm_U3_le {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : ‖U3 ρ t‖ ≤ 12 * ρ := by
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ (1 + t ^ 2) ^ 4 := one_le_pow₀ (by nlinarith)
  apply norm_le_of_sq (by positivity); unfold U3; rw [norm_pair_sq]
  have e : (ρ * cA3 t) ^ 2 + (ρ * cB3 t) ^ 2 = 144 * ρ ^ 2 / (1 + t ^ 2) ^ 4 := by
    unfold cA3 cB3; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ρ]

/-- `‖U4‖ ≤ 48ρ`. -/
theorem norm_U4_le {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : ‖U4 ρ t‖ ≤ 48 * ρ := by
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ (1 + t ^ 2) ^ 5 := one_le_pow₀ (by nlinarith)
  apply norm_le_of_sq (by positivity); unfold U4; rw [norm_pair_sq]
  have e : (ρ * cA4 t) ^ 2 + (ρ * cB4 t) ^ 2 = 2304 * ρ ^ 2 / (1 + t ^ 2) ^ 5 := by
    unfold cA4 cB4; field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ρ]

/-! ## Faces in the new parametrisation -/

/-- The radius of a face point. -/
@[expose] def faceRho (kind : ℕ) (w : ℝ) : ℝ := if kind < 2 then (cylR kind : ℝ) / 181 else w
/-- The height of a face point. -/
@[expose] def faceZeta (kind : ℕ) (w : ℝ) : ℝ := if kind < 2 then w else planeZ kind

/-- **The faces in the rational parametrisation.** -/
theorem faceSigma_phiT (kind : ℕ) (t w : ℝ) :
    faceSigma kind (phiT t) w = circ (faceRho kind w) (faceZeta kind w) t := by
  rw [faceSigma_polar, polarPt_eq, cos_phiT, sin_phiT]
  unfold circ cA0 cB0 faceRho faceZeta
  rfl

/-- Chord bound on the circle: `|circ ρ ζ t - circ ρ₀ ζ₀ t₀|² ≤ (ρ - ρ₀)² + (ζ - ζ₀)² +
4 ρρ₀ (t - t₀)²` for `ρ, ρ₀ ≥ 0`. -/
theorem circ_dist_sq {ρ ρ0 : ℝ} (hρ : 0 ≤ ρ) (hρ0 : 0 ≤ ρ0) (ζ ζ0 t t0 : ℝ) :
    ‖circ ρ ζ t - circ ρ0 ζ0 t0‖ ^ 2 ≤
      (ρ - ρ0) ^ 2 + (ζ - ζ0) ^ 2 + 4 * (ρ * ρ0) * (t - t0) ^ 2 := by
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have h1 : (0 : ℝ) < 1 + t0 ^ 2 := by positivity
  rw [norm_sq_coords]
  simp only [Fin.isValue, circ, eV, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_eq_same, smul_eq_mul, mul_one, ne_eq, zero_ne_one, not_false_eq_true,
    PiLp.single_eq_of_ne, mul_zero, add_zero, Fin.reduceEq, one_ne_zero, zero_add, ge_iff_le]
  -- `|c(t) - c(t₀)|² = 4(t - t₀)²/((1 + t²)(1 + t₀²)) ≤ 4(t - t₀)²`
  have key : (ρ * cA0 t - ρ0 * cA0 t0) ^ 2 + (ρ * cB0 t - ρ0 * cB0 t0) ^ 2 =
      (ρ - ρ0) ^ 2 + ρ * ρ0 * (4 * (t - t0) ^ 2 / ((1 + t ^ 2) * (1 + t0 ^ 2))) := by
    unfold cA0 cB0; field_simp; ring
  have hle : 4 * (t - t0) ^ 2 / ((1 + t ^ 2) * (1 + t0 ^ 2)) ≤ 4 * (t - t0) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (t - t0), sq_nonneg t, sq_nonneg t0, mul_nonneg (sq_nonneg t) (sq_nonneg
        t0)]
  have hρρ : 0 ≤ ρ * ρ0 := mul_nonneg hρ hρ0
  nlinarith [mul_le_mul_of_nonneg_left hle hρρ]

/-! ## Corners and `hel` at corners -/

/-- Validity of a cubic face: kind `< 4` and a positive denominator. -/
@[expose] def Face4Valid (F : Face4) : Prop := F.kind < 4 ∧ 0 < F.wd

/-- **The grid corners of the cubic checker lie on the faces.** -/
theorem cornerR_cornerXYZ4 (F : Face4) (hwd : 0 < F.wd) (m : ℤ) (wn : ℤ)
    (hok : (cornerXYZ4 F m wn).2 = true) :
    cornerR (cornerXYZ4 F m wn).1.1 (cornerXYZ4 F m wn).1.2.1 (cornerXYZ4 F m wn).1.2.2.1
      (cornerXYZ4 F m wn).1.2.2.2 = faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn : ℝ) / F.wd) ∧
      0 < (cornerXYZ4 F m wn).1.2.2.2 := by
  have hq : (0 : ℝ) < 4096 ^ 2 + (m : ℝ) ^ 2 := by positivity
  simp only [cornerXYZ4, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨hX, hY⟩, hZ⟩ := hok
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  rw [faceSigma_phiT]
  by_cases hc : F.kind < 2
  · simp only [faceRZ4, hc, ite_true] at hX hY hZ ⊢
    have hD : (0 : ℤ) < ((181 : ℕ) : ℤ) * ((qT : ℤ) * qT + m * m) * (F.wd : ℤ) * 1024 := by
      have hm := mul_self_nonneg m
      have : (0 : ℤ) < (qT : ℤ) * qT + m * m := by simp only [qT]; push_cast; linarith
      positivity
    refine ⟨?_, by omega⟩
    simp only [cornerR]
    rw [toNat_cast_real hX, toNat_cast_real hY, toNat_cast_real hZ, toNat_cast_real hD.le]
    simp only [circ, faceRho, faceZeta, hc, ite_true, cA0, cB0, qT]
    ext i; fin_cases i <;> simp [eV] <;> field_simp <;> ring
  · simp only [faceRZ4, hc, ite_false] at hX hY hZ ⊢
    have hD : (0 : ℤ) < (F.wd : ℤ) * ((qT : ℤ) * qT + m * m) * ((32761 : ℕ) : ℤ) * 1024 := by
      have hm := mul_self_nonneg m
      have : (0 : ℤ) < (qT : ℤ) * qT + m * m := by simp only [qT]; push_cast; linarith
      positivity
    refine ⟨?_, by omega⟩
    simp only [cornerR]
    rw [toNat_cast_real hX, toNat_cast_real hY, toNat_cast_real hZ, toNat_cast_real hD.le]
    simp only [circ, faceRho, faceZeta, hc, ite_false, cA0, cB0, qT, planeZ, aF]
    by_cases h2 : F.kind = 2
    · simp only [h2, ite_true]
      ext i; fin_cases i <;> simp [eV] <;> field_simp <;> ring
    · simp only [h2, ite_false]
      ext i; fin_cases i <;> simp [eV] <;> field_simp <;> ring

/-- **The checker's `hel` at a grid corner of the cubic checker is `hel` there.** -/
theorem helAt_corner4 (F : Face4) (hF : Face4Valid F) (m : ℤ) (wn : ℤ)
    (hρ : F.kind < 2 ∨ 0 < wn) :
    let h := helAt (helCoef (faceRZ4 F wn).1 (faceRZ4 F wn).2) (trigOf4 m)
    (0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den) ∧
    hel (faceSigma F.kind (phiT ((m : ℝ) / 4096)) ((wn : ℝ) / F.wd)) =
      WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val] := by
  intro h
  obtain ⟨hk, hwd⟩ := hF
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  set q : ℤ := (qT : ℤ)
  set t : ℝ := (m : ℝ) / 4096
  have hcd : 0 < ((q * q + m * m).toNat) := by
    have hm := mul_self_nonneg m
    have : 0 < q * q + m * m := by simp only [q, qT]; push_cast; linarith
    omega
  have hcdR : (((q * q + m * m).toNat : ℕ) : ℝ) = 4096 ^ 2 + (m : ℝ) ^ 2 := by
    have hm := mul_self_nonneg m
    rw [toNat_cast_real (by simp only [q, qT]; push_cast; linarith)]; simp [q, qT]; ring
  have hc : ((-(2 * m * q) : ℤ) : ℝ) / (((q * q + m * m).toNat : ℕ) : ℝ) = cos (phiT t) := by
    rw [hcdR, cos_phiT]; simp only [t, q, qT]; push_cast; field_simp
  have hs : ((q * q - m * m : ℤ) : ℝ) / (((q * q + m * m).toNat : ℕ) : ℝ) = sin (phiT t) := by
    rw [hcdR, sin_phiT]; simp only [t, q, qT]; push_cast; field_simp; ring
  have htrig : trigOf4 m = mkTrig ⟨-(2 * m * q), (q * q + m * m).toNat⟩
      ⟨q * q - m * m, (q * q + m * m).toNat⟩ := rfl
  obtain ⟨ρn, ρd, ζn, ζd, hρn, hρd, hζd, hrz, hρv, hζv⟩ : ∃ ρn ρd ζn ζd, 0 < ρn ∧ 0 < ρd ∧ 0 < ζd ∧
      faceRZ4 F wn = (⟨ρn, ρd⟩, ⟨ζn, ζd⟩) ∧
      (ρn : ℝ) / ρd = faceRho F.kind ((wn : ℝ) / F.wd) ∧
      (ζn : ℝ) / ζd = faceZeta F.kind ((wn : ℝ) / F.wd) := by
    by_cases hc2 : F.kind < 2
    · refine ⟨cylR F.kind, 181, wn, F.wd, by unfold cylR; split_ifs <;> norm_num, by norm_num, hwd,
        by simp [faceRZ4, hc2], by simp [faceRho, hc2], by simp [faceZeta, hc2]⟩
    · have hwpos : 0 < wn := hρ.resolve_left hc2
      by_cases h2 : F.kind = 2
      · refine ⟨wn, F.wd, 3420, 32761, hwpos, hwd, by norm_num, by simp [faceRZ4, h2],
          by simp [faceRho, hc2], ?_⟩
        simp [faceZeta, planeZ, h2, aF]
      · refine ⟨wn, F.wd, -3420, 32761, hwpos, hwd, by norm_num, by simp [faceRZ4, hc2, h2],
          by simp [faceRho, hc2], ?_⟩
        simp [faceZeta, hc2, planeZ, h2, aF]; ring
  have hρpos : (0 : ℝ) < (ρn : ℝ) / ρd := by
    have : (0 : ℝ) < ρn := by exact_mod_cast hρn
    have : (0 : ℝ) < ρd := by exact_mod_cast hρd
    positivity
  simp only [h, hrz, htrig]
  obtain ⟨hden, h1, h2, h3⟩ := helAt_val ρn ζn (-(2 * m * q)) (q * q - m * m) ρd ζd
    ((q * q + m * m).toNat) ((q * q + m * m).toNat) hρn hρd hζd hcd hcd
  refine ⟨hden, ?_⟩
  rw [faceSigma_polar, show (if F.kind < 2 then (cylR F.kind : ℝ) / 181 else (wn : ℝ) / F.wd) =
    faceRho F.kind ((wn : ℝ) / F.wd) from rfl, show (if F.kind < 2 then (wn : ℝ) / F.wd else
    planeZ F.kind) = faceZeta F.kind ((wn : ℝ) / F.wd) from rfl, ← hρv, ← hζv, hel_polar hρpos]
  rw [h1, h2, h3, hc, hs]
  have hcs : cos (phiT t) ^ 2 + sin (phiT t) ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq _
  ext i; fin_cases i
  · simp [helP, cos_three_mul, sin_three_mul]
  · simp [helP, cos_three_mul, sin_three_mul]
  · simp only [helP, sin_two_mul, cos_two_mul, Fin.reduceFinMk, Fin.isValue,
      Nat.succ_eq_add_one, Nat.reduceAdd, neg_mul, Matrix.cons_val]
    have : 2 * cos (phiT t) ^ 2 - 1 = cos (phiT t) ^ 2 - sin (phiT t) ^ 2 := by linarith
    rw [this]; ring

end PlasmaLean.Design.PolygonCoil
