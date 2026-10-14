/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.Suydam

/-!
# Picone–Riccati certificates for variable-coefficient radial forms (Newcomb)

For a single Fourier mode of a cylindrical screw pinch, the ideal-MHD energy reduces
(Newcomb 1960) to a one-dimensional quadratic form

  Q(ξ) = ∫_{x₀}^{x₁} (f ξ'² + g ξ²) dx,   f ≥ 0,

with radial displacement `ξ` vanishing at the ends. Newcomb's sufficient condition is
the classical Jacobi/Picone argument: a solution of the Riccati inequality certifies a
lower bound. This module proves it in a form that permits `f` to vanish (as it does,
quadratically, at a resonant surface).

Certificate data: a C¹ function `φ` (playing the role of `f w`, with `w = u'/u` for a
Jacobi field `u`), its derivative `h`, and a constant `c`, such that pointwise

  `h + c ≤ g`  and  `φ² ≤ f (g − c − h)`.

Then `Q(ξ) ≥ c ∫ ξ²` (`picone_certificate`). Proof: the Picone identity
`f ξ'² + g ξ² = c ξ² + (φ ξ²)' + [f ξ'² − 2 φ ξ ξ' + (g − c − h) ξ²]`; the bracket is a
nonnegative quadratic form and `(φ ξ²)'` integrates to zero.

Corollaries: the Riccati version `riccati_certificate` (`(f w)' + f w² ≤ g − c`), the
Jacobi supersolution version `jacobi_certificate`, recovery of the constant-coefficient
Suydam bound across the resonant point (`suydam_from_picone`), sanity cases and an
exact certificate with non-constant `f`.

Scope: this is a sufficient criterion for the model radial form with continuous
coefficients and C¹ displacements vanishing at both ends. Newcomb's necessity
(oscillation theorem), the reduction from full 3-D δW, singular coefficients at the
magnetic axis and free-boundary terms are NOT covered. The coefficients `f, g` of an
actual equilibrium are supplied inputs here.
-/
public section

noncomputable section
namespace PlasmaLean.Stability
open intervalIntegral Set

/-- The variable-coefficient radial quadratic form `∫ (f ξ'² + g ξ²)`. -/
@[expose] def newcombForm (f g : ℝ → ℝ) (x₀ x₁ : ℝ) (ξ ξ' : ℝ → ℝ) : ℝ :=
  ∫ x in x₀..x₁, (f x * ξ' x ^ 2 + g x * ξ x ^ 2)

/-- A nonnegative binary quadratic form: if `f ≥ 0`, `a ≥ 0` and `φ² ≤ f a`, then
`f p² − 2 φ p q + a q² ≥ 0`. The case `f = 0` forces `φ = 0`. -/
theorem quadratic_nonneg {f a φ p q : ℝ} (hf : 0 ≤ f) (ha : 0 ≤ a) (hd : φ ^ 2 ≤ f * a) :
    0 ≤ f * p ^ 2 - 2 * φ * p * q + a * q ^ 2 := by
  rcases hf.eq_or_lt with h0 | hpos
  · subst h0
    have : φ = 0 := by nlinarith [sq_nonneg φ]
    subst this
    nlinarith [sq_nonneg q]
  · have key : f * (f * p ^ 2 - 2 * φ * p * q + a * q ^ 2) =
        (f * p - φ * q) ^ 2 + (f * a - φ ^ 2) * q ^ 2 := by ring
    have : 0 ≤ f * (f * p ^ 2 - 2 * φ * p * q + a * q ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (f * p - φ * q), sq_nonneg q]
    exact nonneg_of_mul_nonneg_right (by linarith) hpos

/-- Integrability of the form's integrand for continuous coefficients. -/
theorem newcomb_integrable {f g ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hξ : C1On ξ ξ' x₀ x₁)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁)) :
    IntervalIntegrable (fun x => f x * ξ' x ^ 2 + g x * ξ x ^ 2) MeasureTheory.volume x₀ x₁ :=
  ((hf.mul (hξ.cont.pow 2)).add (hg.mul (hξ.continuousOn.pow 2))).intervalIntegrable

/-- **Picone certificate (Newcomb sufficiency).** If `φ` is C¹ with derivative `h`,
`f ≥ 0`, `h + c ≤ g` and `φ² ≤ f (g − c − h)` on `[x₀, x₁]`, then every C¹ displacement
vanishing at both endpoints satisfies `c ∫ ξ² ≤ Q(ξ)`. -/
theorem picone_certificate {f g φ h ξ ξ' : ℝ → ℝ} {x₀ x₁ c : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁))
    (hφ : ∀ x ∈ uIcc x₀ x₁, HasDerivAt φ (h x) x) (hh : ContinuousOn h (uIcc x₀ x₁))
    (hfn : ∀ x ∈ uIcc x₀ x₁, 0 ≤ f x) (hgap : ∀ x ∈ uIcc x₀ x₁, h x + c ≤ g x)
    (hdisc : ∀ x ∈ uIcc x₀ x₁, φ x ^ 2 ≤ f x * (g x - c - h x)) :
    c * ∫ x in x₀..x₁, ξ x ^ 2 ≤ newcombForm f g x₀ x₁ ξ ξ' := by
  have hφc : ContinuousOn φ (uIcc x₀ x₁) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  -- Derivative of the boundary term `φ ξ²`.
  have hP : ∀ x ∈ uIcc x₀ x₁, HasDerivAt (fun y => φ y * ξ y ^ 2)
      (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x)) x := by
    intro x hx
    have := (hφ x hx).mul ((hξ.deriv x hx).pow 2)
    convert this using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat]; ring
  have hPi : IntervalIntegrable (fun x => h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x))
      MeasureTheory.volume x₀ x₁ :=
    ((hh.mul (hξ.continuousOn.pow 2)).add
      (hφc.mul ((continuousOn_const.mul hξ.continuousOn).mul hξ.cont))).intervalIntegrable
  have hftc : ∫ x in x₀..x₁, (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x)) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt hP hPi, h₀, h₁]; ring
  have hmono : ∫ x in x₀..x₁, (c * ξ x ^ 2 + (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x))) ≤
      newcombForm f g x₀ x₁ ξ ξ' := by
    apply integral_mono_on hle ((hξ.int_sq.const_mul c).add hPi)
      (newcomb_integrable hξ hf hg)
    intro x hx
    have hx' : x ∈ uIcc x₀ x₁ := Icc_subset_uIcc hx
    have q := quadratic_nonneg (p := ξ' x) (q := ξ x) (hfn x hx')
      (by linarith [hgap x hx']) (hdisc x hx')
    nlinarith [q]
  rw [integral_add (hξ.int_sq.const_mul c) hPi, integral_const_mul, hftc, add_zero] at hmono
  exact hmono

/-- With `c = 0` the certificate proves nonnegativity of the form. -/
theorem picone_nonneg {f g φ h ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁))
    (hφ : ∀ x ∈ uIcc x₀ x₁, HasDerivAt φ (h x) x) (hh : ContinuousOn h (uIcc x₀ x₁))
    (hfn : ∀ x ∈ uIcc x₀ x₁, 0 ≤ f x) (hgap : ∀ x ∈ uIcc x₀ x₁, h x ≤ g x)
    (hdisc : ∀ x ∈ uIcc x₀ x₁, φ x ^ 2 ≤ f x * (g x - h x)) :
    0 ≤ newcombForm f g x₀ x₁ ξ ξ' := by
  have := picone_certificate (c := 0) hle hξ h₀ h₁ hf hg hφ hh hfn
    (fun x hx => by simpa using hgap x hx) (fun x hx => by simpa using hdisc x hx)
  simpa using this

/-- **Riccati certificate.** If `w` satisfies `(f w)' + f w² ≤ g − c` (with `(f w)'`
supplied as `h`, continuous, and `f w²` continuous), then `c ∫ ξ² ≤ Q(ξ)`. -/
theorem riccati_certificate {f g w h ξ ξ' : ℝ → ℝ} {x₀ x₁ c : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁))
    (hfw : ∀ x ∈ uIcc x₀ x₁, HasDerivAt (fun y => f y * w y) (h x) x)
    (hh : ContinuousOn h (uIcc x₀ x₁)) (hfn : ∀ x ∈ uIcc x₀ x₁, 0 ≤ f x)
    (hric : ∀ x ∈ uIcc x₀ x₁, h x + f x * w x ^ 2 ≤ g x - c) :
    c * ∫ x in x₀..x₁, ξ x ^ 2 ≤ newcombForm f g x₀ x₁ ξ ξ' := by
  refine picone_certificate hle hξ h₀ h₁ hf hg hfw hh hfn (fun x hx => ?_) (fun x hx => ?_)
  · nlinarith [hric x hx, mul_nonneg (hfn x hx) (sq_nonneg (w x))]
  · have := mul_le_mul_of_nonneg_left (hric x hx) (hfn x hx)
    nlinarith [this]

/-- **Jacobi supersolution certificate.** A positive C¹ function `u` with `f u'` C¹ and
`(f u')' ≤ (g − c) u` certifies `c ∫ ξ² ≤ Q(ξ)` (take `w = u'/u` in the Riccati form). -/
theorem jacobi_certificate {f g u u' k ξ ξ' : ℝ → ℝ} {x₀ x₁ c : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁))
    (hfn : ∀ x ∈ uIcc x₀ x₁, 0 ≤ f x)
    (hu : ∀ x ∈ uIcc x₀ x₁, HasDerivAt u (u' x) x) (hu' : ContinuousOn u' (uIcc x₀ x₁))
    (hpos : ∀ x ∈ uIcc x₀ x₁, 0 < u x)
    (hk : ∀ x ∈ uIcc x₀ x₁, HasDerivAt (fun y => f y * u' y) (k x) x)
    (hkc : ContinuousOn k (uIcc x₀ x₁))
    (hsuper : ∀ x ∈ uIcc x₀ x₁, k x ≤ (g x - c) * u x) :
    c * ∫ x in x₀..x₁, ξ x ^ 2 ≤ newcombForm f g x₀ x₁ ξ ξ' := by
  have huc : ContinuousOn u (uIcc x₀ x₁) :=
    fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hne : ∀ x ∈ uIcc x₀ x₁, u x ≠ 0 := fun x hx => (hpos x hx).ne'
  refine riccati_certificate (w := fun x => u' x / u x)
    (h := fun x => k x / u x - f x * (u' x / u x) ^ 2) hle hξ h₀ h₁ hf hg
    (fun x hx => ?_) ?_ hfn (fun x hx => ?_)
  · have hd := (hk x hx).div (hu x hx) (hne x hx)
    have hfun : (fun y => f y * (u' y / u y)) = fun y => (f y * u' y) / u y := by
      funext y; ring
    rw [hfun]
    convert hd using 1
    have := hne x hx
    field_simp
  · exact (hkc.div huc hne).sub (hf.mul ((hu'.div huc hne).pow 2))
  · have hux := hpos x hx
    have : k x / u x ≤ g x - c := by
      rw [div_le_iff₀ hux]; exact hsuper x hx
    linarith

/-- Monotonicity in the potential: increasing `g` increases the form. -/
theorem newcombForm_mono_g {f g₁ g₂ ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (hf : ContinuousOn f (uIcc x₀ x₁))
    (hg₁ : ContinuousOn g₁ (uIcc x₀ x₁)) (hg₂ : ContinuousOn g₂ (uIcc x₀ x₁))
    (hg : ∀ x ∈ uIcc x₀ x₁, g₁ x ≤ g₂ x) :
    newcombForm f g₁ x₀ x₁ ξ ξ' ≤ newcombForm f g₂ x₀ x₁ ξ ξ' := by
  apply integral_mono_on hle (newcomb_integrable hξ hf hg₁) (newcomb_integrable hξ hf hg₂)
  intro x hx
  nlinarith [hg x (Icc_subset_uIcc hx), sq_nonneg (ξ x)]

/-- The zero displacement has zero energy. -/
theorem newcombForm_zero (f g : ℝ → ℝ) (x₀ x₁ : ℝ) :
    newcombForm f g x₀ x₁ (fun _ => 0) (fun _ => 0) = 0 := by
  simp [newcombForm]

/-- Sanity: the pure kinetic form `∫ ξ'²` (`f = 1`, `g = 0`) is nonnegative, certified
by the trivial certificate `φ = 0`. -/
theorem dirichlet_form_nonneg {ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    0 ≤ newcombForm (fun _ => 1) (fun _ => 0) x₀ x₁ ξ ξ' :=
  picone_nonneg (φ := fun _ => 0) (h := fun _ => 0) hle hξ h₀ h₁ continuousOn_const
    continuousOn_const (fun x _ => hasDerivAt_const x 0) continuousOn_const
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) (fun _ _ => by norm_num)

/-- The Newcomb form with Suydam coefficients `f = F x²`, `g = G` is the Suydam form. -/
theorem newcombForm_suydam (F G x₀ x₁ : ℝ) (ξ ξ' : ℝ → ℝ) :
    newcombForm (fun x => F * x ^ 2) (fun _ => G) x₀ x₁ ξ ξ' = suydamForm F G x₀ x₁ ξ ξ' := by
  rfl

/-- **Suydam recovered.** The certificate `φ = −F x / 2` (i.e. `w = −1/(2x)`, whose
singularity at the resonant point cancels in `φ = f w`) reproduces the sharp
constant-coefficient bound `(G + F/4) ∫ ξ² ≤ Q(ξ)`, on any interval, including one
containing the resonant point `x = 0`. -/
theorem suydam_from_picone {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hF : 0 ≤ F) (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    (G + F / 4) * ∫ x in x₀..x₁, ξ x ^ 2 ≤ suydamForm F G x₀ x₁ ξ ξ' := by
  rw [← newcombForm_suydam]
  refine picone_certificate (φ := fun x => -(F / 2) * x) (h := fun _ => -(F / 2)) hle hξ
    h₀ h₁ (continuousOn_const.mul (continuousOn_id.pow 2)) continuousOn_const
    (fun x _ => ?_) continuousOn_const (fun x _ => by positivity)
    (fun x _ => by linarith) (fun x _ => by ring_nf; rfl)
  simpa using (hasDerivAt_id x).const_mul (-(F / 2))

/-! ## An exact certificate with non-constant shear weight -/

/-- Example: with shear weight `f = 1 + x²` and a destabilizing drive `g = −1/2` on
`[0, 1]`, the polynomial certificate `φ = 1 − 2x` proves `Q(ξ) ≥ (1/2) ∫ ξ²`: the
field-line bending energy overcomes the drive with an explicit margin. -/
theorem example_variable_shear {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' 0 1) (h₀ : ξ 0 = 0)
    (h₁ : ξ 1 = 0) :
    (1 / 2) * ∫ x in (0 : ℝ)..1, ξ x ^ 2 ≤
      newcombForm (fun x => 1 + x ^ 2) (fun _ => -(1 / 2)) 0 1 ξ ξ' := by
  refine picone_certificate (φ := fun x => 1 - 2 * x) (h := fun _ => -2) zero_le_one hξ
    h₀ h₁ (continuousOn_const.add (continuousOn_id.pow 2)) continuousOn_const
    (fun x _ => ?_) continuousOn_const (fun x _ => by positivity)
    (fun x _ => by norm_num) (fun x hx => ?_)
  · simpa using ((hasDerivAt_id x).const_mul 2).const_sub 1
  · rw [uIcc_of_le zero_le_one] at hx
    obtain ⟨h0, h1⟩ := hx
    nlinarith

/-- Corollary of the example: every displacement with positive L² mass has strictly
positive energy, despite the destabilizing drive `g = −1/2`. -/
theorem example_variable_shear_pos {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' 0 1) (h₀ : ξ 0 = 0)
    (h₁ : ξ 1 = 0) (hmass : 0 < ∫ x in (0 : ℝ)..1, ξ x ^ 2) :
    0 < newcombForm (fun x => 1 + x ^ 2) (fun _ => -(1 / 2)) 0 1 ξ ξ' := by
  have := example_variable_shear hξ h₀ h₁
  linarith

end PlasmaLean.Stability
