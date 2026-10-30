/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Hodge period inequality on a flat torus (constant metric)

Model case of note N-3 (`notes/theory/flux-surface-holonomy.md`, §3 (P2)) and plan §11.6.
A flat torus `T² = ℝ²/(ℤω₁ + ℤω₂)` is described in lattice coordinates `(x, y) ∈ ℝ²/ℤ²`,
`z = x ω₁ + y ω₂`, with a **constant** metric `E dx² + 2F dx dy + G dy²` (`ConstMetric`,
`E > 0`, `EG − F² > 0`). Its conformal modulus is `τ = (F + i√(EG − F²))/E` (`ConstMetric.tau`);
for the lattice metric `E = |ω₁|²`, `F = Re(ω̄₁ω₂)`, `G = |ω₂|²` this is `ω₂/ω₁`
(`latticeMetric_tau`).

A 1-form is `α = f dx + g dy` with `f, g` 1-periodic in both variables. It is **closed** when
`∂_y f = ∂_x g`; we record the common partial derivative `d` (`ClosedPeriodicForm`). Its periods
are the line integrals `a = ∮_{γ_p} α = ∫₀¹ f(x, y) dx` (along `ω₁`) and
`b = ∮_{γ_t} α = ∫₀¹ g(x, y) dy` (along `ω₂`); closedness and periodicity make them independent of
the base point (`periodP_eq`, `periodT_eq`) and equal to the averages over the fundamental square
(`avg_f`, `avg_g`). The energy is `∫_{T²} |α|²_g dA = ∫∫_{[0,1]²} (G f² − 2F fg + E g²)/√(EG − F²)`
(`energy`).

Results.

* (a) `periodBound_eq`: `|b − aτ|²/Im τ = (G a² − 2F ab + E b²)/√(EG − F²)`;
  `energy_constForm`: the harmonic (constant) form with periods `(a, b)` has energy
  `|b − aτ|²/Im τ`.
  `periodBound_shift`: invariance under `(b, τ) ↦ (b + k a, τ + k)`.
* (b) `integral_dens_decomp`: for any probability measure,
  `∫ Q(f, g) = Q(∫f, ∫g) + ∫ Q(f − ∫f, g − ∫g)`
  (the cross term vanishes). `energy_eq_add`, `energy_ge`: every closed periodic form has energy
  `≥ |b − aτ|²/Im τ`; `energy_eq_iff`: equality iff the form is constant.
* (c) `fieldLine_energy_ge`: for the field-line form `β = i_Bσ` with periods `(−Φ_t′, Φ_p′)` and
  `ι = Φ_p′/Φ_t′`, energy `≥ Φ_t′² |ι + τ|²/Im τ`; `fieldLine_energy_ge_normalized` (`ψ = Φ_t`);
  `currentForm_energy_ge`: for `α = B♭` with periods `(μ₀I, μ₀G)`, energy `≥ μ₀²|G − τI|²/Im τ`.
  **Scope:** the metric is constant in the chosen angles (the model case of the note). For a
  non-constant metric one needs uniformization of the induced metric, which is not formalized.
* Sanity: `squareMetric_tau` (`τ = i`), `energy_constForm_square` (`a² + b²`) and
  `cosForm_energy_gt` (the closed non-constant form `(a + cos 2πx) dx + b dy` has strictly larger
  energy).
-/

open MeasureTheory Set intervalIntegral

public section
noncomputable section
namespace PlasmaLean.Geometry.TorusHodge

/-! ### Constant metrics, the modulus and the period bound -/

/-- A constant (flat) metric `E dx² + 2F dx dy + G dy²` on the lattice coordinates of a torus. -/
structure ConstMetric where
  /-- Coefficient of `dx²`. -/
  E : ℝ
  /-- Coefficient of `dx dy` (halved). -/
  F : ℝ
  /-- Coefficient of `dy²`. -/
  G : ℝ
  /-- Positivity of `E`. -/
  E_pos : 0 < E
  /-- Positivity of the determinant. -/
  det_pos : 0 < E * G - F ^ 2

namespace ConstMetric

variable (m : ConstMetric)

/-- The determinant `EG − F²`. -/
@[expose] def det : ℝ := m.E * m.G - m.F ^ 2

/-- The conformal modulus `τ = (F + i√(EG − F²))/E`. -/
@[expose] def tau : ℂ := ⟨m.F / m.E, √m.det / m.E⟩

/-- The (unnormalized) energy density `G u² − 2F uv + E v²` of the constant form `u dx + v dy`;
the pointwise energy is `dens/√det` (`|α|²_g · √det`). -/
@[expose] def dens (u v : ℝ) : ℝ := m.G * u ^ 2 - 2 * m.F * u * v + m.E * v ^ 2

/-- The Hodge period bound `|b − aτ|²/Im τ`. -/
@[expose] def periodBound (a b : ℝ) : ℝ := Complex.normSq ((b : ℂ) - a * m.tau) / m.tau.im

theorem det_pos' : 0 < m.det := m.det_pos

/-- `Im τ > 0`. -/
theorem tau_im_pos : 0 < m.tau.im := by
  simp only [tau]
  exact div_pos (Real.sqrt_pos.2 m.det_pos) m.E_pos

/-- `E · Q(u, v) = (Ev − Fu)² + det · u²`. -/
theorem E_mul_dens (u v : ℝ) : m.E * m.dens u v = (m.E * v - m.F * u) ^ 2 + m.det * u ^ 2 := by
  simp only [dens, det]; ring

/-- The energy density is nonnegative. -/
theorem dens_nonneg (u v : ℝ) : 0 ≤ m.dens u v := by
  have h := m.E_mul_dens u v
  have h1 : 0 ≤ (m.E * v - m.F * u) ^ 2 + m.det * u ^ 2 := by
    have := m.det_pos'; positivity
  nlinarith [m.E_pos]

/-- The energy density vanishes only at `0`. -/
theorem dens_eq_zero_iff (u v : ℝ) : m.dens u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h1 := m.E_mul_dens u v
    rw [h, mul_zero] at h1
    have hd := m.det_pos'
    have hu2 : u ^ 2 = 0 := by nlinarith [sq_nonneg (m.E * v - m.F * u), sq_nonneg u]
    have hu : u = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hu2
    subst hu
    have : (m.E * v) ^ 2 = 0 := by nlinarith [sq_nonneg (m.E * v)]
    exact ⟨rfl, (mul_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)).resolve_left
      m.E_pos.ne'⟩
  · rintro ⟨rfl, rfl⟩; simp [dens]

/-- **(a) The τ/energy identity**: `|b − aτ|²/Im τ = (G a² − 2F ab + E b²)/√(EG − F²)`. -/
theorem periodBound_eq (a b : ℝ) : m.periodBound a b = m.dens a b / √m.det := by
  have hE := m.E_pos
  have hs : √m.det ^ 2 = m.E * m.G - m.F ^ 2 := Real.sq_sqrt m.det_pos'.le
  have hs0 : 0 < √m.det := Real.sqrt_pos.2 m.det_pos'
  simp only [periodBound, tau, dens, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  generalize √m.det = s at hs hs0 ⊢
  rw [div_eq_div_iff (by positivity) hs0.ne']
  field_simp
  linear_combination (a ^ 2) * hs

/-- The period bound is invariant under the change of toroidal cycle `γ_t ↦ γ_t + kγ_p`,
which sends `b ↦ b + k a` and `τ ↦ τ + k`. -/
theorem periodBound_shift (a b k : ℝ) :
    Complex.normSq (((b + k * a : ℝ) : ℂ) - a * (m.tau + k)) / (m.tau + k).im =
      m.periodBound a b := by
  simp only [periodBound]
  congr 1
  · congr 1; push_cast; ring
  · simp

end ConstMetric

/-- The metric induced on `ℂ/(ℤω₁ + ℤω₂)` in the lattice coordinates `z = x ω₁ + y ω₂`:
`E = |ω₁|²`, `F = Re(ω̄₁ω₂)`, `G = |ω₂|²`. The hypothesis `Im(ω̄₁ω₂) > 0` is the orientation
`Im(ω₂/ω₁) > 0`. -/
@[expose] def latticeMetric (ω₁ ω₂ : ℂ) (h : 0 < (starRingEnd ℂ ω₁ * ω₂).im) : ConstMetric where
  E := Complex.normSq ω₁
  F := (starRingEnd ℂ ω₁ * ω₂).re
  G := Complex.normSq ω₂
  E_pos := by
    rcases eq_or_ne ω₁ 0 with rfl | h1
    · simp at h
    · exact Complex.normSq_pos.2 h1
  det_pos := by
    have : Complex.normSq ω₁ * Complex.normSq ω₂ - (starRingEnd ℂ ω₁ * ω₂).re ^ 2 =
        (starRingEnd ℂ ω₁ * ω₂).im ^ 2 := by
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]; ring
    rw [this]; positivity

/-- The modulus of the lattice metric is `τ = ω₂/ω₁`. -/
theorem latticeMetric_tau (ω₁ ω₂ : ℂ) (h : 0 < (starRingEnd ℂ ω₁ * ω₂).im) :
    (latticeMetric ω₁ ω₂ h).tau = ω₂ / ω₁ := by
  have hdet : (latticeMetric ω₁ ω₂ h).det = (starRingEnd ℂ ω₁ * ω₂).im ^ 2 := by
    simp only [ConstMetric.det, latticeMetric, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  have h1 : ω₁ ≠ 0 := by rintro rfl; simp at h
  have hn : Complex.normSq ω₁ ≠ 0 := (Complex.normSq_pos.2 h1).ne'
  rw [ConstMetric.tau, hdet, Real.sqrt_sq h.le]
  apply Complex.ext <;>
  · simp only [latticeMetric, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    field_simp
    ring

/-! ### The orthogonal decomposition of the energy (any probability measure) -/

/-- **Cross term vanishes.** For a probability measure, `∫ Q(f, g) = Q(∫f, ∫g) +
∫ Q(f − ∫f, g − ∫g)`. -/
theorem integral_dens_decomp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (m : ConstMetric) {f g : X → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ)
    (hq : Integrable (fun p => m.dens (f p - ∫ q, f q ∂μ) (g p - ∫ q, g q ∂μ)) μ) :
    ∫ p, m.dens (f p) (g p) ∂μ =
      m.dens (∫ q, f q ∂μ) (∫ q, g q ∂μ) +
        ∫ p, m.dens (f p - ∫ q, f q ∂μ) (g p - ∫ q, g q ∂μ) ∂μ := by
  set a := ∫ q, f q ∂μ with ha
  set b := ∫ q, g q ∂μ with hb
  have key : ∀ p, m.dens (f p) (g p) = (m.dens a b + (2 * (m.G * a - m.F * b)) * (f p - a) +
      (2 * (m.E * b - m.F * a)) * (g p - b)) + m.dens (f p - a) (g p - b) := by
    intro p; simp only [ConstMetric.dens]; ring
  have i1 : Integrable (fun p => f p - a) μ := hf.sub (integrable_const a)
  have i2 : Integrable (fun p => g p - b) μ := hg.sub (integrable_const b)
  have z1 : ∫ p, (f p - a) ∂μ = 0 := by rw [integral_sub hf (integrable_const a)]; simp [← ha]
  have z2 : ∫ p, (g p - b) ∂μ = 0 := by rw [integral_sub hg (integrable_const b)]; simp [← hb]
  simp_rw [key]
  rw [integral_add _ hq, integral_add _ (i2.const_mul _), integral_add (integrable_const _)
    (i1.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, z1, z2]
  · simp
  · exact (integrable_const _).add (i1.const_mul _)
  · exact ((integrable_const _).add (i1.const_mul _)).add (i2.const_mul _)

/-! ### The fundamental square -/

/-- Lebesgue measure on the fundamental square `[0,1]²`, as a product measure. -/
@[expose] def unitSquare : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

instance : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

instance : IsProbabilityMeasure unitSquare := by
  unfold unitSquare; infer_instance

/-- `unitSquare` is Lebesgue measure restricted to `[0,1] ×ˢ [0,1]`. -/
theorem unitSquare_eq : unitSquare = volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  rw [unitSquare, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- Continuous functions are integrable on the fundamental square. -/
theorem integrable_unitSquare {h : ℝ × ℝ → ℝ} (hc : Continuous h) : Integrable h unitSquare := by
  rw [unitSquare_eq]
  exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

/-- **Closed forms have well-defined periods.** If `∂_y F = D = ∂_x G` with `D` continuous and
`G(1, y) = G(0, y)`, then `y ↦ ∫₀¹ F(x, y) dx` is constant (Fubini plus the fundamental theorem
of calculus). -/
theorem lineIntegral_const {F G D : ℝ → ℝ → ℝ}
    (hF : ∀ x y, HasDerivAt (fun t => F x t) (D x y) y)
    (hG : ∀ x y, HasDerivAt (fun s => G s y) (D x y) x)
    (hFc : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hGper : ∀ y, G 1 y = G 0 y) (y₀ y₁ : ℝ) :
    ∫ x in (0 : ℝ)..1, F x y₁ = ∫ x in (0 : ℝ)..1, F x y₀ := by
  have hDy : ∀ x, Continuous (D x) := fun x => hD.uncurry_left x
  have hDx : ∀ y, Continuous (fun x => D x y) := fun y => hD.uncurry_right y
  have h1 : ∀ x, F x y₁ - F x y₀ = ∫ t in y₀..y₁, D x t := fun x =>
    (integral_eq_sub_of_hasDerivAt (fun t _ => hF x t) ((hDy x).intervalIntegrable _ _)).symm
  have h2 : ∀ y, ∫ x in (0 : ℝ)..1, D x y = 0 := fun y => by
    rw [integral_eq_sub_of_hasDerivAt (fun s _ => hG s y) ((hDx y).intervalIntegrable _ _),
      hGper, sub_self]
  have hint : IntegrableOn (Function.uncurry D) (uIoc 0 1 ×ˢ uIoc y₀ y₁) :=
    (hD.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [← sub_eq_zero, ← integral_sub ((hFc.uncurry_right y₁).intervalIntegrable _ _)
    ((hFc.uncurry_right y₀).intervalIntegrable _ _)]
  simp_rw [h1]
  rw [intervalIntegral_intervalIntegral_swap hint]
  simp [h2]

/-- The average over `[0,1]²` of a continuous function whose `x`-line integrals all equal `a`. -/
theorem avg_of_lineX {h : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry h)) {a : ℝ}
    (hl : ∀ y, ∫ x in (0 : ℝ)..1, h x y = a) : ∫ p, h p.1 p.2 ∂unitSquare = a := by
  have hi := integrable_unitSquare (h := fun p : ℝ × ℝ => h p.1 p.2) hc
  rw [unitSquare] at hi
  rw [unitSquare, integral_prod_symm _ hi]
  have : ∀ y, ∫ x in Icc (0 : ℝ) 1, h x y = a := fun y => by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hl]
  simp [this]

/-- The average over `[0,1]²` of a continuous function whose `y`-line integrals all equal `b`. -/
theorem avg_of_lineY {h : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry h)) {b : ℝ}
    (hl : ∀ x, ∫ y in (0 : ℝ)..1, h x y = b) : ∫ p, h p.1 p.2 ∂unitSquare = b := by
  have hi := integrable_unitSquare (h := fun p : ℝ × ℝ => h p.1 p.2) hc
  rw [unitSquare] at hi
  rw [unitSquare, integral_prod _ hi]
  have : ∀ x, ∫ y in Icc (0 : ℝ) 1, h x y = b := fun x => by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hl]
  simp [this]

/-- A function 1-periodic in both variables is determined by its values on `[0,1)²`. -/
theorem periodic_fract {h : ℝ → ℝ → ℝ} (hx : ∀ x y, h (x + 1) y = h x y)
    (hy : ∀ x y, h x (y + 1) = h x y) (x y : ℝ) : h (Int.fract x) (Int.fract y) = h x y := by
  have px : Function.Periodic (fun s => h s (Int.fract y)) 1 := fun s => hx s _
  have py : Function.Periodic (fun t => h x t) 1 := fun t => hy x t
  have e1 := px.sub_int_mul_eq (x := x) ⌊x⌋
  have e2 := py.sub_int_mul_eq (x := y) ⌊y⌋
  simp only [mul_one] at e1 e2
  exact e1.trans e2

/-! ### Closed periodic 1-forms -/

/-- A closed 1-form `α = f dx + g dy` on the torus `ℝ²/ℤ²` (lattice coordinates): `f, g` are
continuous and 1-periodic in both variables, and `∂_y f = ∂_x g = d` with `d` continuous
(`dα = (∂_x g − ∂_y f) dx ∧ dy = 0`). -/
structure ClosedPeriodicForm where
  /-- The `dx` coefficient. -/
  f : ℝ → ℝ → ℝ
  /-- The `dy` coefficient. -/
  g : ℝ → ℝ → ℝ
  /-- The common partial derivative `∂_y f = ∂_x g`. -/
  d : ℝ → ℝ → ℝ
  /-- `∂_y f = d`. -/
  hasDerivAt_f : ∀ x y, HasDerivAt (fun t => f x t) (d x y) y
  /-- `∂_x g = d` (closedness). -/
  hasDerivAt_g : ∀ x y, HasDerivAt (fun s => g s y) (d x y) x
  /-- Continuity of `f`. -/
  continuous_f : Continuous (Function.uncurry f)
  /-- Continuity of `g`. -/
  continuous_g : Continuous (Function.uncurry g)
  /-- Continuity of `d`. -/
  continuous_d : Continuous (Function.uncurry d)
  /-- Periodicity of `f` in `x`. -/
  f_per_x : ∀ x y, f (x + 1) y = f x y
  /-- Periodicity of `f` in `y`. -/
  f_per_y : ∀ x y, f x (y + 1) = f x y
  /-- Periodicity of `g` in `x`. -/
  g_per_x : ∀ x y, g (x + 1) y = g x y
  /-- Periodicity of `g` in `y`. -/
  g_per_y : ∀ x y, g x (y + 1) = g x y

namespace ClosedPeriodicForm

variable (α : ClosedPeriodicForm)

/-- The period along the cycle `γ_p` (the generator `ω₁`): `∫₀¹ f(x, 0) dx`. -/
@[expose] def periodP : ℝ := ∫ x in (0 : ℝ)..1, α.f x 0

/-- The period along the cycle `γ_t` (the generator `ω₂`): `∫₀¹ g(0, y) dy`. -/
@[expose] def periodT : ℝ := ∫ y in (0 : ℝ)..1, α.g 0 y

/-- The `γ_p`-period does not depend on the base point. -/
theorem periodP_eq (y : ℝ) : ∫ x in (0 : ℝ)..1, α.f x y = α.periodP :=
  lineIntegral_const α.hasDerivAt_f α.hasDerivAt_g α.continuous_f α.continuous_d
    (fun y => by simpa using α.g_per_x 0 y) 0 y

/-- The `γ_t`-period does not depend on the base point. -/
theorem periodT_eq (x : ℝ) : ∫ y in (0 : ℝ)..1, α.g x y = α.periodT :=
  lineIntegral_const (F := fun x y => α.g y x) (G := fun s y => α.f y s) (D := fun x y => α.d y x)
    (fun x y => α.hasDerivAt_g y x) (fun x y => α.hasDerivAt_f y x)
    (α.continuous_g.comp continuous_swap) (α.continuous_d.comp continuous_swap)
    (fun y => by simpa using α.f_per_y y 0) 0 x

/-- The `γ_p`-period is the average of `f` over the fundamental square. -/
theorem avg_f : ∫ p, α.f p.1 p.2 ∂unitSquare = α.periodP :=
  avg_of_lineX α.continuous_f α.periodP_eq

/-- The `γ_t`-period is the average of `g` over the fundamental square. -/
theorem avg_g : ∫ p, α.g p.1 p.2 ∂unitSquare = α.periodT :=
  avg_of_lineY α.continuous_g α.periodT_eq

/-- The energy `∫_{T²} |α|²_g dA = ∫∫_{[0,1]²} (G f² − 2F fg + E g²) dx dy / √(EG − F²)`. -/
@[expose] def energy (m : ConstMetric) : ℝ :=
  (∫ p, m.dens (α.f p.1 p.2) (α.g p.1 p.2) ∂unitSquare) / √m.det

/-- Continuity of the excess density `Q(f − a, g − b)`. -/
theorem continuous_excess (m : ConstMetric) :
    Continuous (fun p : ℝ × ℝ => m.dens (α.f p.1 p.2 - α.periodP) (α.g p.1 p.2 - α.periodT)) := by
  have hf : Continuous (fun p : ℝ × ℝ => α.f p.1 p.2) := α.continuous_f
  have hg : Continuous (fun p : ℝ × ℝ => α.g p.1 p.2) := α.continuous_g
  simp only [ConstMetric.dens]
  fun_prop

/-- **Energy decomposition**: energy = harmonic energy + excess `∫ Q(f − a, g − b)/√det`. -/
theorem energy_eq_add (m : ConstMetric) :
    α.energy m = m.periodBound α.periodP α.periodT +
      (∫ p, m.dens (α.f p.1 p.2 - α.periodP) (α.g p.1 p.2 - α.periodT) ∂unitSquare) / √m.det := by
  have hf : Continuous (fun p : ℝ × ℝ => α.f p.1 p.2) := α.continuous_f
  have hg : Continuous (fun p : ℝ × ℝ => α.g p.1 p.2) := α.continuous_g
  have hd := integral_dens_decomp unitSquare m (integrable_unitSquare hf)
    (integrable_unitSquare hg)
    (by rw [α.avg_f, α.avg_g]; exact integrable_unitSquare (α.continuous_excess m))
  rw [energy, hd, α.avg_f, α.avg_g, m.periodBound_eq, add_div]

/-- **(b) Hodge period inequality** (constant metric): a closed periodic 1-form with periods
`(a, b)` has energy `≥ |b − aτ|²/Im τ`. -/
theorem energy_ge (m : ConstMetric) : m.periodBound α.periodP α.periodT ≤ α.energy m := by
  rw [α.energy_eq_add m]
  have h1 : 0 ≤ ∫ p, m.dens (α.f p.1 p.2 - α.periodP) (α.g p.1 p.2 - α.periodT) ∂unitSquare :=
    integral_nonneg fun p => m.dens_nonneg _ _
  have := div_nonneg h1 (Real.sqrt_nonneg m.det)
  linarith

/-- **Equality case**: the energy equals `|b − aτ|²/Im τ` iff the form is constant (harmonic). -/
theorem energy_eq_iff (m : ConstMetric) :
    α.energy m = m.periodBound α.periodP α.periodT ↔
      ∀ x y, α.f x y = α.periodP ∧ α.g x y = α.periodT := by
  rw [α.energy_eq_add m]
  have hs0 : 0 < √m.det := Real.sqrt_pos.2 m.det_pos'
  set h := fun p : ℝ × ℝ => m.dens (α.f p.1 p.2 - α.periodP) (α.g p.1 p.2 - α.periodT) with hh
  have hc : Continuous h := α.continuous_excess m
  constructor
  · intro heq
    have hz : ∫ p, h p ∂unitSquare = 0 := by
      have : (∫ p, h p ∂unitSquare) / √m.det = 0 := by linarith
      exact (div_eq_zero_iff.1 this).resolve_right hs0.ne'
    rw [integral_eq_zero_iff_of_nonneg (fun p => m.dens_nonneg _ _) (integrable_unitSquare hc),
      unitSquare_eq] at hz
    have hU : h =ᵐ[volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)] 0 :=
      ae_restrict_of_ae_restrict_of_subset (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hz
    have hEq : EqOn h 0 (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
      Measure.eqOn_open_of_ae_eq hU (isOpen_Ioo.prod isOpen_Ioo) hc.continuousOn
        continuous_const.continuousOn
    have hcl : EqOn h 0 (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
      have := hEq.closure hc continuous_const
      rwa [closure_prod_eq, closure_Ioo zero_ne_one] at this
    intro x y
    have hp : h (Int.fract x, Int.fract y) = 0 :=
      hcl ⟨⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩,
        ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩⟩
    obtain ⟨h1, h2⟩ := (m.dens_eq_zero_iff _ _).1 hp
    rw [periodic_fract α.f_per_x α.f_per_y] at h1
    rw [periodic_fract α.g_per_x α.g_per_y] at h2
    exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩
  · intro hconst
    have : ∀ p, h p = 0 := fun p => by
      simp only [hh, (hconst p.1 p.2).1, (hconst p.1 p.2).2, sub_self]
      exact (m.dens_eq_zero_iff 0 0).2 ⟨rfl, rfl⟩
    rw [show h = 0 from funext this]; simp

end ClosedPeriodicForm

/-! ### (a) The harmonic representative -/

/-- The constant (harmonic) 1-form `a dx + b dy`. -/
@[expose] def constForm (a b : ℝ) : ClosedPeriodicForm where
  f := fun _ _ => a
  g := fun _ _ => b
  d := fun _ _ => 0
  hasDerivAt_f := fun _ y => hasDerivAt_const y a
  hasDerivAt_g := fun x _ => hasDerivAt_const x b
  continuous_f := continuous_const
  continuous_g := continuous_const
  continuous_d := continuous_const
  f_per_x := fun _ _ => rfl
  f_per_y := fun _ _ => rfl
  g_per_x := fun _ _ => rfl
  g_per_y := fun _ _ => rfl

/-- The periods of `a dx + b dy` are `(a, b)`. -/
theorem constForm_periods (a b : ℝ) :
    (constForm a b).periodP = a ∧ (constForm a b).periodT = b := by
  simp [ClosedPeriodicForm.periodP, ClosedPeriodicForm.periodT, constForm]

/-- **(a)** The harmonic form with periods `(a, b)` has energy `|b − aτ|²/Im τ`
`= (G a² − 2F ab + E b²)/√(EG − F²)`. -/
theorem energy_constForm (m : ConstMetric) (a b : ℝ) :
    (constForm a b).energy m = m.periodBound a b := by
  obtain ⟨ha, hb⟩ := constForm_periods a b
  have := ((constForm a b).energy_eq_iff m).2 (fun _ _ => ⟨ha.symm, hb.symm⟩)
  rwa [ha, hb] at this

/-! ### (c) Physics corollaries (constant metric only) -/

/-- **Field-line form bound** (model case: constant metric in the angles). For the field-line
form `β = i_Bσ` on a flux torus, with periods `(−Φ_t′, Φ_p′)` (note N-3, §2 orientations) and
`ι = Φ_p′/Φ_t′`, the energy `∫_Σ |B|²/|∇ψ|² dA` is at least `Φ_t′² |ι + τ|²/Im τ`. -/
theorem fieldLine_energy_ge (m : ConstMetric) (β : ClosedPeriodicForm) {Φt' Φp' : ℝ}
    (hΦ : Φt' ≠ 0) (hP : β.periodP = -Φt') (hT : β.periodT = Φp') :
    Φt' ^ 2 * Complex.normSq (((Φp' / Φt' : ℝ) : ℂ) + m.tau) / m.tau.im ≤ β.energy m := by
  have h := β.energy_ge m
  rw [hP, hT] at h
  convert h using 2
  simp only [ConstMetric.periodBound]
  have : ((Φp' : ℝ) : ℂ) - ((-Φt' : ℝ) : ℂ) * m.tau =
      (Φt' : ℂ) * (((Φp' / Φt' : ℝ) : ℂ) + m.tau) := by
    have : (Φt' : ℂ) ≠ 0 := by exact_mod_cast hΦ
    push_cast; field_simp; ring
  rw [this, Complex.normSq_mul, Complex.normSq_ofReal]; ring

/-- Normalized field-line bound (`ψ = Φ_t`, periods `(−1, ι)`): energy `≥ |ι + τ|²/Im τ`. -/
theorem fieldLine_energy_ge_normalized (m : ConstMetric) (β : ClosedPeriodicForm) {ι : ℝ}
    (hP : β.periodP = -1) (hT : β.periodT = ι) :
    Complex.normSq ((ι : ℂ) + m.tau) / m.tau.im ≤ β.energy m := by
  simpa using fieldLine_energy_ge m β one_ne_zero hP hT

/-- **Current-form bound** (constant metric, needs `J·∇ψ = 0` for closedness of `α = B♭|_Σ`):
with periods `(μ₀I, μ₀G)`, energy `∫_Σ |B|² dA ≥ μ₀² |G − τI|²/Im τ`. -/
theorem currentForm_energy_ge (m : ConstMetric) (α : ClosedPeriodicForm) {μ₀ I G : ℝ}
    (hP : α.periodP = μ₀ * I) (hT : α.periodT = μ₀ * G) :
    μ₀ ^ 2 * Complex.normSq ((G : ℂ) - m.tau * I) / m.tau.im ≤ α.energy m := by
  have h := α.energy_ge m
  rw [hP, hT] at h
  convert h using 2
  simp only [ConstMetric.periodBound]
  have : ((μ₀ * G : ℝ) : ℂ) - ((μ₀ * I : ℝ) : ℂ) * m.tau = (μ₀ : ℂ) * ((G : ℂ) - m.tau * I) := by
    push_cast; ring
  rw [this, Complex.normSq_mul, Complex.normSq_ofReal]; ring

/-! ### Sanity checks -/

/-- The square torus metric `dx² + dy²`. -/
@[expose] def squareMetric : ConstMetric where
  E := 1
  F := 0
  G := 1
  E_pos := one_pos
  det_pos := by norm_num

/-- The square torus has modulus `τ = i`. -/
theorem squareMetric_tau : squareMetric.tau = Complex.I := by
  apply Complex.ext <;> simp [ConstMetric.tau, ConstMetric.det, squareMetric]

/-- On the square torus the harmonic form with periods `(a, b)` has energy `a² + b²`. -/
theorem energy_constForm_square (a b : ℝ) :
    (constForm a b).energy squareMetric = a ^ 2 + b ^ 2 := by
  rw [energy_constForm, ConstMetric.periodBound_eq]
  simp [ConstMetric.dens, ConstMetric.det, squareMetric]

/-- The closed, non-constant form `(a + cos 2πx) dx + b dy`. -/
@[expose] def cosForm (a b : ℝ) : ClosedPeriodicForm where
  f := fun x _ => a + Real.cos (2 * Real.pi * x)
  g := fun _ _ => b
  d := fun _ _ => 0
  hasDerivAt_f := fun x y => hasDerivAt_const y _
  hasDerivAt_g := fun x _ => hasDerivAt_const x b
  continuous_f := by
    change Continuous (fun p : ℝ × ℝ => a + Real.cos (2 * Real.pi * p.1)); fun_prop
  continuous_g := continuous_const
  continuous_d := continuous_const
  f_per_x := fun x _ => by
    simp only [mul_add, mul_one, Real.cos_add_two_pi]
  f_per_y := fun _ _ => rfl
  g_per_x := fun _ _ => rfl
  g_per_y := fun _ _ => rfl

/-- The periods of `cosForm a b` are `(a, b)`. -/
theorem cosForm_periods (a b : ℝ) : (cosForm a b).periodP = a ∧ (cosForm a b).periodT = b := by
  refine ⟨?_, by simp [ClosedPeriodicForm.periodT, cosForm]⟩
  simp only [ClosedPeriodicForm.periodP, cosForm]
  have hc : Continuous (fun x : ℝ => Real.cos (2 * Real.pi * x)) := by fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable _ _),
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (by positivity), integral_cos]
  simp

/-- **Strict inequality** for a non-constant closed form: on any constant metric,
`cosForm a b` has energy strictly larger than the harmonic bound `|b − aτ|²/Im τ`. -/
theorem cosForm_energy_gt (m : ConstMetric) (a b : ℝ) :
    m.periodBound a b < (cosForm a b).energy m := by
  obtain ⟨ha, hb⟩ := cosForm_periods a b
  have hge := (cosForm a b).energy_ge m
  rw [ha, hb] at hge
  refine lt_of_le_of_ne hge fun heq => ?_
  have := (((cosForm a b).energy_eq_iff m).1 (by rw [ha, hb]; exact heq.symm) 0 0).1
  rw [ha] at this
  simp [cosForm] at this

end PlasmaLean.Geometry.TorusHodge
