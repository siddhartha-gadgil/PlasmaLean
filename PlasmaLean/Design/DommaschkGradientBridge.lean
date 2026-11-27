/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRegionFieldBounds

/-!
# The gradient of the QA2R field strength in terms of the field polynomials

With `D = R⁷ B_φ`, `n_R = R⁸ B_R`, `n_z = R⁸ B_z` the sparse polynomials of the QA2R field in
`(u, z, c, s) = (R − R₀, z, cos 2φ, sin 2φ)`, the squared field strength is
`|B|² = (D / R⁷)² + (n_R / R⁸)² + (n_z / R⁸)²`, and its three partial derivatives in cylindrical
coordinates are `numR / R¹⁷`, `numT / R¹⁶`, `numZ / R¹⁶` with polynomial numerators.

* `mulR`, `radial`, with `evR_mulR`, `evR_radial`: the sparse polynomials `R p` and
  `R ∂_u p − k p`; `evR_merge`, `evR_scale`, `evR_mulMono`, `evR_phiS`: real evaluation of the
  operations on sparse polynomials.
* `hasDerivAt_angle`: the formal angular derivative `phiS p` is the derivative of
  `φ ↦ p (u, z, cos 2φ, sin 2φ)`.
* `numR`, `numT`, `numZ`: the three numerators at a point `(u, z, c, s)`;
  `norm_sq_mul`: `R¹⁶ |B|² = R² D² + n_R² + n_z²`.
* `gradAbsB_sq`: at positive radius, where the field does not vanish,
  `4 R¹⁸ (R² D² + n_R² + n_z²) ‖∇|B|‖² = numR² + numT² + R² numZ²`.

**Sanity.** `mulR_fixture`, `radial_fixture`: the two polynomial operations on a monomial, and
`radial_power`: `R ∂_u − k` annihilates `Rᵏ` (here `k = 1`).
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkGradientBridge
open Fields Contract Set Real
open DommaschkBounceField DommaschkKam DommaschkCartesianAngleFlow DkPoly
open DommaschkRegionEnclosure Kinetic.GCLittlejohn
open scoped RealInnerProductSpace Topology

/-! ## Real evaluation of the operations on sparse polynomials -/

theorem evR_scale (k : ℚ) (p : SP) (u z c s : ℝ) :
    evR u z c s (scale k p) = (k : ℝ) * evR u z c s p := by
  induction p with
  | nil => simp [scale, evR]
  | cons t p ih =>
    simp only [scale, List.map_cons, evR_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem evR_mulMono (t : Tm) (p : SP) (u z c s : ℝ) :
    evR u z c s (mulMono t p) =
      (t.q : ℝ) * (u ^ t.a * z ^ t.b * c ^ t.c * s ^ t.d) * evR u z c s p := by
  induction p with
  | nil => simp [mulMono, evR]
  | cons m p ih =>
    simp only [mulMono, List.map_cons, evR_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem evR_merge (p q : SP) (u z c s : ℝ) :
    evR u z c s (merge p q) = evR u z c s p + evR u z c s q := by
  apply Complex.ofReal_injective
  rw [← ev_ofReal, ev_merge, ev_ofReal, ev_ofReal]
  push_cast
  rfl

/-- The sparse polynomial `R p`, with `R = u + R₀`. -/
def mulR (p : SP) : SP := merge (mulMono ⟨1, 1, 0, 0, 0⟩ p) (scale (29 / 32) p)

theorem evR_mulR (p : SP) (u z c s : ℝ) :
    evR u z c s (mulR p) = (u + dkR0) * evR u z c s p := by
  rw [mulR, evR_merge, evR_mulMono, evR_scale]
  simp only [dkR0]
  push_cast
  ring

/-- The sparse polynomial `R ∂_u p − k p`: `R^(k+1)` times the radial derivative of `p / Rᵏ`. -/
def radial (k : ℚ) (p : SP) : SP := merge (mulR (dU p)) (scale (-k) p)

theorem evR_radial (k : ℚ) (p : SP) (u z c s : ℝ) :
    evR u z c s (radial k p) = (u + dkR0) * evR u z c s (dU p) - k * evR u z c s p := by
  rw [radial, evR_merge, evR_mulR, evR_scale]
  push_cast
  ring

theorem evR_phiS (p : SP) (u z c s : ℝ) :
    evR u z c s (phiS p) = -2 * s * evR u z c s (dC p) + 2 * c * evR u z c s (dS p) := by
  rw [phiS, evR_merge, evR_mulMono, evR_mulMono]
  push_cast
  ring

/-- **Sanity**: `R · u = u² + (29/32) u`. -/
theorem mulR_fixture : mulR [⟨1, 1, 0, 0, 0⟩] = [⟨29 / 32, 1, 0, 0, 0⟩, ⟨1, 2, 0, 0, 0⟩] := by
  with_unfolding_all rfl

/-- **Sanity**: `(R ∂_u − 3) u = −2u + 29/32`. -/
theorem radial_fixture :
    radial 3 [⟨1, 1, 0, 0, 0⟩] = [⟨29 / 32, 0, 0, 0, 0⟩, ⟨-2, 1, 0, 0, 0⟩] := by
  with_unfolding_all rfl

/-- **Sanity**: `R ∂_u − 1` annihilates `R = u + 29/32`. -/
theorem radial_power : radial 1 [⟨29 / 32, 0, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0⟩] = [] := by
  with_unfolding_all rfl

/-! ## The angular derivative -/

/-- Derivative of a sparse polynomial along a curve in the last two variables. -/
theorem hasDerivAt_cs (p : SP) (u z : ℝ) {c s : ℝ → ℝ} {c' s' t : ℝ} (hc : HasDerivAt c c' t)
    (hs : HasDerivAt s s' t) :
    HasDerivAt (fun τ => evR u z (c τ) (s τ) p)
      (evR u z (c t) (s t) (dC p) * c' + evR u z (c t) (s t) (dS p) * s') t := by
  induction p with
  | nil => simpa [evR, dC, dS] using hasDerivAt_const t (0 : ℝ)
  | cons m p ih =>
    have key : HasDerivAt (fun τ => (m.q : ℝ) * (u ^ m.a * z ^ m.b * c τ ^ m.c * s τ ^ m.d))
        (evR u z (c t) (s t) (Tm.dC m) * c' + evR u z (c t) (s t) (Tm.dS m) * s') t := by
      have h := ((hc.pow m.c).mul (hs.pow m.d)).const_mul ((m.q : ℝ) * (u ^ m.a * z ^ m.b))
      convert h using 1
      · funext τ
        simp only [Pi.mul_apply, Pi.pow_apply]
        ring
      · cases hc' : m.c <;> cases hd' : m.d <;>
          simp [Tm.dC, Tm.dS, hc', hd', evR] <;> ring
    simp only [evR_cons, dC, dS, List.flatMap_cons, evR_append]
    convert key.add ih using 1
    simp only [dC, dS]
    ring

/-- **The formal angular derivative** `phiS p = 2 (c ∂_s − s ∂_c) p` is the derivative of
`φ ↦ p (u, z, cos 2φ, sin 2φ)`. -/
theorem hasDerivAt_angle (p : SP) (u z t : ℝ) :
    HasDerivAt (fun τ => evR u z (cos (2 * τ)) (sin (2 * τ)) p)
      (evR u z (cos (2 * t)) (sin (2 * t)) (phiS p)) t := by
  have h2 : HasDerivAt (fun τ : ℝ => 2 * τ) 2 t := by
    simpa using (hasDerivAt_id' t).const_mul (2 : ℝ)
  have h := hasDerivAt_cs p u z h2.cos h2.sin
  convert h using 1
  rw [evR_phiS]
  ring

/-! ## The numerators of the gradient of the squared strength -/

/-- `R ∂_u D − 7 D = R⁸ ∂_R B_φ`. -/
def pDR : SP := radial 7 dD
/-- `R ∂_u n_R − 8 n_R = R⁹ ∂_R B_R`. -/
def pPR : SP := radial 8 dnR
/-- `R ∂_u n_z − 8 n_z = R⁹ ∂_R B_z`. -/
def pQR : SP := radial 8 dnZ
/-- `∂_φ D`. -/
def pDT : SP := phiS dD
/-- `∂_φ n_R`. -/
def pPT : SP := phiS dnR
/-- `∂_φ n_z`. -/
def pQT : SP := phiS dnZ
/-- `∂_z D`. -/
def pDZ : SP := dZ dD
/-- `∂_z n_R`. -/
def pPZ : SP := dZ dnR
/-- `∂_z n_z`. -/
def pQZ : SP := dZ dnZ

/-- The numerator `2 (R² D x + n_R y + n_z w)` built from three polynomials `x`, `y`, `w`. -/
def num (x y w : SP) (u z c s : ℝ) : ℝ :=
  2 * ((u + dkR0) ^ 2 * evR u z c s dD * evR u z c s x + evR u z c s dnR * evR u z c s y +
    evR u z c s dnZ * evR u z c s w)

/-- `R¹⁷ ∂_R |B|²`. -/
def numR (u z c s : ℝ) : ℝ := num pDR pPR pQR u z c s
/-- `R¹⁶ ∂_φ |B|²`. -/
def numT (u z c s : ℝ) : ℝ := num pDT pPT pQT u z c s
/-- `R¹⁶ ∂_z |B|²`. -/
def numZ (u z c s : ℝ) : ℝ := num pDZ pPZ pQZ u z c s

/-- The squared strength in the cylindrical variables. -/
def strengthSq (R t z : ℝ) : ℝ :=
  (atPoint dD R t z / R ^ 7) ^ 2 + (atPoint dnR R t z / R ^ 8) ^ 2 + (atPoint dnZ R t z / R ^ 8) ^ 2

theorem norm_sq_eq {R : ℝ} (hR : 0 < R) (t z : ℝ) :
    ‖B (cylPoint R t z)‖ ^ 2 = strengthSq R t z := by
  obtain ⟨d, nr, nz⟩ := field_id hR t z
  have sq := DommaschkKamC.norm_field_sq R t z
  change ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R t z)‖ ^ 2 = _
  rw [sq, strengthSq, d, nr, nz]
  field_simp
  ring

/-- `R¹⁶ |B|² = R² D² + n_R² + n_z²` at positive radius. -/
theorem norm_sq_mul {R : ℝ} (hR : 0 < R) (t z : ℝ) :
    R ^ 16 * ‖B (cylPoint R t z)‖ ^ 2 =
      R ^ 2 * atPoint dD R t z ^ 2 + atPoint dnR R t z ^ 2 + atPoint dnZ R t z ^ 2 := by
  rw [norm_sq_eq hR, strengthSq]
  field_simp

private theorem ratio7 {f : ℝ → ℝ} {f' R : ℝ} (hf : HasDerivAt f f' R) (hR : R ≠ 0) :
    HasDerivAt (fun r => (f r / r ^ 7) ^ 2) (2 * f R * (R * f' - 7 * f R) / R ^ 15) R := by
  have h := (hf.div (hasDerivAt_pow 7 R) (pow_ne_zero 7 hR)).pow 2
  convert h using 1
  simp only [Pi.div_apply]
  norm_num
  field_simp

private theorem ratio8 {f : ℝ → ℝ} {f' R : ℝ} (hf : HasDerivAt f f' R) (hR : R ≠ 0) :
    HasDerivAt (fun r => (f r / r ^ 8) ^ 2) (2 * f R * (R * f' - 8 * f R) / R ^ 17) R := by
  have h := (hf.div (hasDerivAt_pow 8 R) (pow_ne_zero 8 hR)).pow 2
  convert h using 1
  simp only [Pi.div_apply]
  norm_num
  field_simp

private theorem fixed {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (a : ℝ) :
    HasDerivAt (fun r => (f r / a) ^ 2) (2 * f x * f' / a ^ 2) x := by
  have h := (hf.div_const a).pow 2
  convert h using 1
  ring

/-- The radial derivative of the squared strength. -/
theorem hasDerivAt_strength_R {R : ℝ} (hR : 0 < R) (t z : ℝ) :
    HasDerivAt (fun r => strengthSq r t z)
      (numR (R - dkR0) z (cos (2 * t)) (sin (2 * t)) / R ^ 17) R := by
  have d (p : SP) : HasDerivAt (fun r => atPoint p r t z)
      (evR (R - dkR0) z (cos (2 * t)) (sin (2 * t)) (dU p)) R :=
    HasDerivAt.comp_sub_const R dkR0 (hasDerivAt_u p (R - dkR0) z (cos (2 * t)) (sin (2 * t)))
  have h : HasDerivAt (fun r => strengthSq r t z) _ R :=
    ((ratio7 (d dD) hR.ne').add (ratio8 (d dnR) hR.ne')).add (ratio8 (d dnZ) hR.ne')
  convert h using 1
  simp only [numR, num, pDR, pPR, pQR, evR_radial, atPoint, sub_add_cancel]
  field_simp
  push_cast
  ring

/-- The angular derivative of the squared strength. -/
theorem hasDerivAt_strength_T (R t z : ℝ) :
    HasDerivAt (fun τ => strengthSq R τ z)
      (numT (R - dkR0) z (cos (2 * t)) (sin (2 * t)) / R ^ 16) t := by
  rcases eq_or_ne R 0 with rfl | hR
  · simpa [strengthSq] using hasDerivAt_const t (0 : ℝ)
  have d (p : SP) := hasDerivAt_angle p (R - dkR0) z t
  have h : HasDerivAt (fun τ => strengthSq R τ z) _ t :=
    ((fixed (d dD) (R ^ 7)).add (fixed (d dnR) (R ^ 8))).add (fixed (d dnZ) (R ^ 8))
  convert h using 1
  simp only [numT, num, pDT, pPT, pQT, sub_add_cancel]
  field_simp

/-- The vertical derivative of the squared strength. -/
theorem hasDerivAt_strength_Z (R t z : ℝ) :
    HasDerivAt (fun ζ => strengthSq R t ζ)
      (numZ (R - dkR0) z (cos (2 * t)) (sin (2 * t)) / R ^ 16) z := by
  rcases eq_or_ne R 0 with rfl | hR
  · simpa [strengthSq] using hasDerivAt_const z (0 : ℝ)
  have d (p : SP) := hasDerivAt_z p (R - dkR0) z (cos (2 * t)) (sin (2 * t))
  have h : HasDerivAt (fun ζ => strengthSq R t ζ) _ z :=
    ((fixed (d dD) (R ^ 7)).add (fixed (d dnR) (R ^ 8))).add (fixed (d dnZ) (R ^ 8))
  convert h using 1
  simp only [numZ, num, pDZ, pPZ, pQZ, sub_add_cancel]
  field_simp

/-! ## The gradient of the strength -/

private theorem sq_deriv {f S : ℝ → ℝ} {f' S' x : ℝ} (hf : HasDerivAt f f' x)
    (hS : HasDerivAt S S' x) (e : S =ᶠ[𝓝 x] fun r => f r ^ 2) : 2 * f x * f' = S' := by
  have h2 : HasDerivAt (fun r => f r ^ 2) (2 * f x * f') x := by
    convert hf.pow 2 using 1
    simp
  exact (h2.congr_of_eventuallyEq e).unique hS

private theorem curve {f : ℝ → Fin 3 → ℝ} {f' : Fin 3 → ℝ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun r => (WithLp.toLp 2 (f r) : Space)) (WithLp.toLp 2 f') x :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt x h

private theorem inner3 (g : Space) (a b c : ℝ) :
    ⟪g, (WithLp.toLp 2 ![a, b, c] : Space)⟫ = g 0 * a + g 1 * b + g 2 * c := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

set_option maxRecDepth 8000 in
/-- **The gradient of the field strength in terms of the field polynomials.** At positive
radius, where the field does not vanish,
`4 R¹⁸ (R² D² + n_R² + n_z²) ‖∇|B|‖² = numR² + numT² + R² numZ²`. -/
theorem gradAbsB_sq {R : ℝ} (hR : 0 < R) (t z : ℝ) (h0 : B (cylPoint R t z) ≠ 0) :
    4 * R ^ 18 * (R ^ 2 * atPoint dD R t z ^ 2 + atPoint dnR R t z ^ 2 + atPoint dnZ R t z ^ 2) *
        ‖gradAbsB B (cylPoint R t z)‖ ^ 2 =
      numR (R - dkR0) z (cos (2 * t)) (sin (2 * t)) ^ 2 +
        numT (R - dkR0) z (cos (2 * t)) (sin (2 * t)) ^ 2 +
        R ^ 2 * numZ (R - dkR0) z (cos (2 * t)) (sin (2 * t)) ^ 2 := by
  set g := gradAbsB B (cylPoint R t z) with hg
  have dom : cylPoint R t z ∈ CylAlgebra.domain := by
    change 0 < CylAlgebra.r2 _
    rw [radial_at]
    positivity
  have hB : DifferentiableAt ℝ B (cylPoint R t z) :=
    (DommaschkRegionRegularity.contDiffAt_domain dom).differentiableAt (by norm_num)
  have hd : DifferentiableAt ℝ (fun y => ‖B y‖) (cylPoint R t z) := hB.norm ℝ h0
  have hF : HasFDerivAt (fun y => ‖B y‖) (InnerProductSpace.toDual ℝ Space g) (cylPoint R t z) :=
    hasGradientAt_iff_hasFDerivAt.mp hd.hasGradientAt
  -- the three coordinate curves
  have cR : HasDerivAt (fun r => cylPoint r t z) (WithLp.toLp 2 ![cos t, sin t, 0]) R := by
    apply curve
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (hasDerivAt_id' R).mul_const (cos t)
    · simpa using (hasDerivAt_id' R).mul_const (sin t)
    · simpa using hasDerivAt_const R z
  have cT : HasDerivAt (fun τ => cylPoint R τ z)
      (WithLp.toLp 2 ![R * (-sin t), R * cos t, 0]) t := by
    apply curve
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (hasDerivAt_cos t).const_mul R
    · simpa using (hasDerivAt_sin t).const_mul R
    · simpa using hasDerivAt_const t z
  have cZ : HasDerivAt (fun ζ => cylPoint R t ζ) (WithLp.toLp 2 ![0, 0, 1]) z := by
    apply curve
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const z (R * cos t)
    · simpa using hasDerivAt_const z (R * sin t)
    · simpa using hasDerivAt_id' z
  -- derivatives of the strength along the curves, from the gradient
  have dR : HasDerivAt (fun r => ‖B (cylPoint r t z)‖) (g 0 * cos t + g 1 * sin t) R := by
    have h := hF.comp_hasDerivAt R cR
    rw [InnerProductSpace.toDual_apply_apply, inner3] at h
    exact HasDerivAt.congr_deriv h (by ring)
  have dT : HasDerivAt (fun τ => ‖B (cylPoint R τ z)‖) (R * (g 1 * cos t - g 0 * sin t)) t := by
    have h := hF.comp_hasDerivAt t cT
    rw [InnerProductSpace.toDual_apply_apply, inner3] at h
    exact HasDerivAt.congr_deriv h (by ring)
  have dZ : HasDerivAt (fun ζ => ‖B (cylPoint R t ζ)‖) (g 2) z := by
    have h := hF.comp_hasDerivAt z cZ
    rw [InnerProductSpace.toDual_apply_apply, inner3] at h
    exact HasDerivAt.congr_deriv h (by ring)
  have eR := sq_deriv dR (hasDerivAt_strength_R hR t z) (by
    filter_upwards [lt_mem_nhds hR] with r hr
    exact (norm_sq_eq hr t z).symm)
  have eT := sq_deriv dT (hasDerivAt_strength_T R t z)
    (Filter.Eventually.of_forall fun τ => (norm_sq_eq hR τ z).symm)
  have eZ := sq_deriv dZ (hasDerivAt_strength_Z R t z)
    (Filter.Eventually.of_forall fun ζ => (norm_sq_eq hR t ζ).symm)
  have nsq : ‖g‖ ^ 2 = g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
  have h17 : R ^ 17 ≠ 0 := pow_ne_zero 17 hR.ne'
  have h16 : R ^ 16 ≠ 0 := pow_ne_zero 16 hR.ne'
  rw [eq_div_iff h17] at eR
  rw [eq_div_iff h16] at eT eZ
  rw [← eR, ← eT, ← eZ, ← norm_sq_mul hR t z, nsq]
  linear_combination (-(4 * R ^ 34 * ‖B (cylPoint R t z)‖ ^ 2 * (g 0 ^ 2 + g 1 ^ 2))) *
    Real.sin_sq_add_cos_sq t

end PlasmaLean.Design.DommaschkGradientBridge
