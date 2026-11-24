/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorTubeCrossing
public import PlasmaLean.Design.DommaschkPhysicalJacobian

/-! # Outward derivative of the squared field strength on an actual QA2R trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorStrengthSlope
open DommaschkKam DkPoly DommaschkBounceField
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing

private def value (m : Tm) (u z c s : ℝ) : ℝ :=
  (m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * s ^ m.d)

private theorem cons_ev (m : Tm) (p : SP) (u z c s : ℝ) :
    evR u z c s (m :: p) = value m u z c s + evR u z c s p := by simp [evR, value]

private theorem append_ev (p q : SP) (u z c s : ℝ) :
    evR u z c s (p ++ q) = evR u z c s p + evR u z c s q := by simp [evR]

private theorem term_partials (m : Tm) (u z c s : ℝ) :
    evR u z c s m.dU = (m.q : ℝ) * (m.a * u ^ (m.a-1) * z ^ m.b * c ^ m.c * s ^ m.d) ∧
    evR u z c s m.dZ = (m.q : ℝ) * (u ^ m.a * (m.b * z ^ (m.b-1)) * c ^ m.c * s ^ m.d) ∧
    evR u z c s m.dC = (m.q : ℝ) * (u ^ m.a * z ^ m.b * (m.c * c ^ (m.c-1)) * s ^ m.d) ∧
    evR u z c s m.dS = (m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * (m.d * s ^ (m.d-1))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : m.a <;> simp [Tm.dU, h, evR]
    ring
  · cases h : m.b <;> simp [Tm.dZ, h, evR]
    ring
  · cases h : m.c <;> simp [Tm.dC, h, evR]
    ring
  · cases h : m.d <;> simp [Tm.dS, h, evR]
    ring

private theorem term_path (m : Tm) {u z c s : ℝ → ℝ} {U Z C S t : ℝ}
    (hu : HasDerivAt u U t) (hz : HasDerivAt z Z t) (hc : HasDerivAt c C t)
    (hs : HasDerivAt s S t) :
    HasDerivAt (fun a => value m (u a) (z a) (c a) (s a))
      (evR (u t) (z t) (c t) (s t) m.dU * U + evR (u t) (z t) (c t) (s t) m.dZ * Z +
       evR (u t) (z t) (c t) (s t) m.dC * C + evR (u t) (z t) (c t) (s t) m.dS * S) t := by
  obtain ⟨au, az, ac, as'⟩ := term_partials m (u t) (z t) (c t) (s t)
  rw [au,az,ac,as']
  convert ((((hu.pow m.a).mul (hz.pow m.b)).mul (hc.pow m.c)).mul (hs.pow m.d)).const_mul
    (m.q : ℝ) using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.pow_apply]
    ring

/-- Full sparse derivative along a differentiable curve in the four input coordinates. -/
theorem sparse_path (p : SP) {u z c s : ℝ → ℝ} {U Z C S t : ℝ}
    (hu : HasDerivAt u U t) (hz : HasDerivAt z Z t) (hc : HasDerivAt c C t)
    (hs : HasDerivAt s S t) :
    HasDerivAt (fun a => evR (u a) (z a) (c a) (s a) p)
      (evR (u t) (z t) (c t) (s t) (dU p) * U + evR (u t) (z t) (c t) (s t) (dZ p) * Z +
       evR (u t) (z t) (c t) (s t) (dC p) * C + evR (u t) (z t) (c t) (s t) (dS p) * S) t := by
  induction p with
  | nil => simpa [evR,dU,dZ,dC,dS] using (hasDerivAt_const t (0 : ℝ))
  | cons m p ih =>
    simp only [cons_ev]
    convert (term_path m hu hz hc hs).add ih using 1
    simp only [dU,dZ,dC,dS,List.flatMap_cons,append_ev]
    ring

/-- The denominator times the material derivative in the positive azimuthal direction. -/
def material (u z c s : ℝ) (p : SP) : ℝ :=
  let v := evR u z c s
  v dnR * v (dU p) + v dnZ * v (dZ p) + v dD * (2 * (c * v (dS p) - s * v (dC p)))

/-- Numerator of the physical squared-strength derivative, with denominator R¹⁷D. -/
def numerator (R z c s : ℝ) : ℝ :=
  let v := evR (R-dkR0) z c s
  let m := material (R-dkR0) z c s
  let d := v dD
  let r := v dnR
  let w := v dnZ
  let rd := R*d
  let U := rd*rd + r*r + w*w
  let W := 2*(rd*(r*d + R*m dD) + r*m dnR + w*m dnZ)
  R*W - 16*(r*U)

private theorem material_path (p : SP) {R Z : ℝ → ℝ} {t : ℝ}
    (hd : atPoint dD (R t) t (Z t) ≠ 0)
    (hr : HasDerivAt R (atPoint dnR (R t) t (Z t) / atPoint dD (R t) t (Z t)) t)
    (hz : HasDerivAt Z (atPoint dnZ (R t) t (Z t) / atPoint dD (R t) t (Z t)) t) :
    HasDerivAt (fun a => atPoint p (R a) a (Z a))
      (material (R t - dkR0) (Z t) (Real.cos (2 * t)) (Real.sin (2 * t)) p /
        atPoint dD (R t) t (Z t)) t := by
  have clock := (hasDerivAt_id t).const_mul (2 : ℝ)
  have h := sparse_path p (hr.sub_const dkR0) hz clock.cos clock.sin
  unfold atPoint at hd hr hz ⊢
  convert h using 1
  · rfl
  · unfold material
    simp only [id_eq, mul_one, atPoint]
    field_simp [hd]
    ring

private theorem quotient_path {R D N Z : ℝ → ℝ} {t d' n' z' : ℝ}
    (hr : HasDerivAt R (N t / D t) t) (hd : HasDerivAt D (d' / D t) t)
    (hn : HasDerivAt N (n' / D t) t) (hz : HasDerivAt Z (z' / D t) t)
    (rpos : R t ≠ 0) (dpos : D t ≠ 0) :
    let U := (R t*D t)^2+(N t)^2+(Z t)^2
    let W := 2*(R t*D t*(N t*D t+R t*d')+N t*n'+Z t*z')
    HasDerivAt (fun a => ((R a*D a)^2+(N a)^2+(Z a)^2)/(R a)^16)
      ((R t*W-16*(N t*U))/(R t^17*D t)) t := by
  dsimp only
  convert (((((hr.mul hd).pow 2).add (hn.pow 2)).add (hz.pow 2)).div (hr.pow 16)
    (pow_ne_zero _ rpos)) using 1
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply]
  field_simp [rpos,dpos]
  ring

/-- A forward physical solution has the certified rational squared-strength derivative. -/
theorem forward_derivative {R Z : ℝ → ℝ} {t : ℝ} (rpos : 0 < R t)
    (dpos : 0 < atPoint dD (R t) t (Z t))
    (hr : HasDerivAt R (atPoint dnR (R t) t (Z t) / atPoint dD (R t) t (Z t)) t)
    (hz : HasDerivAt Z (atPoint dnZ (R t) t (Z t) / atPoint dD (R t) t (Z t)) t) :
    HasDerivAt (fun a => ‖DommaschkQA2R.field DommaschkQA2R.candidate
        (Contract.cylPoint (R a) a (Z a))‖ ^ 2)
      (numerator (R t) (Z t) (Real.cos (2 * t)) (Real.sin (2 * t)) /
        (R t^17 * atPoint dD (R t) t (Z t))) t := by
  have hp := material_path (R := R) (Z := Z) (t := t)
  have q := quotient_path hr (hp dD dpos.ne' hr hz) (hp dnR dpos.ne' hr hz)
    (hp dnZ dpos.ne' hr hz) rpos.ne' dpos.ne'
  simp only [pow_two] at q
  apply q.congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (lt_mem_nhds rpos)] with x hx
  rw [norm_sq_eq_strengthSq hx]
  unfold Certificates.RadialSlabs.strengthSq
  field_simp [hx.ne']
  ring

/-- Strict outward slope along the original physical flow on the positive clock. -/
theorem forward_of_physical {y : ℝ → DommaschkBounceField.State} {t k : ℝ}
    (flow : HasDerivAt y (physicalFlow 0 1 t (y t)) t) (rpos : 0 < y t 0)
    (dpos : 0 < atPoint dD (y t 0) t (y t 1))
    (num : k * ((y t 0) ^ 17 * atPoint dD (y t 0) t (y t 1)) <
      numerator (y t 0) (y t 1) (Real.cos (2 * t)) (Real.sin (2 * t))) :
    ∃ v > k, HasDerivAt (fun a => ‖DommaschkQA2R.field DommaschkQA2R.candidate
      (Contract.cylPoint (y a 0) a (y a 1))‖ ^ 2) v t := by
  have eq := ratio_eq_physical 0 1 t (y t) rpos
    (by simpa [clockPoly] using dpos.ne')
  rw [← eq] at flow
  have hr := hasDerivAt_pi.mp flow 0
  have hz := hasDerivAt_pi.mp flow 1
  simp only [ratioFlow,clockPoly,Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one,zero_add,one_mul] at hr hz
  exact ⟨_,(lt_div_iff₀ (mul_pos (pow_pos rpos _) dpos)).mpr num,forward_derivative rpos dpos hr hz⟩

/-- Reflection identifies the negative outbound clock with the same forward field
and squared strength. Both spatial coordinates here belong to the original path. -/
theorem backward_of_physical {y : ℝ → DommaschkBounceField.State} {t k : ℝ}
    (flow : HasDerivAt y (physicalFlow 0 (-1) t (y t)) t) (rpos : 0 < y t 0)
    (dpos : 0 < atPoint dD (y t 0) t (-(y t 1)))
    (num : k * ((y t 0) ^ 17 * atPoint dD (y t 0) t (-(y t 1))) <
      numerator (y t 0) (-(y t 1)) (Real.cos (2 * t)) (Real.sin (2 * t))) :
    ∃ v > k, HasDerivAt (fun a => ‖DommaschkQA2R.field DommaschkQA2R.candidate
      (Contract.cylPoint (y a 0) (-a) (y a 1))‖ ^ 2) v t := by
  let x := DommaschkSectionReflection.reflect (y t)
  have ref : DommaschkSectionReflection.reflect x = y t := by
    funext k
    fin_cases k <;> simp [x,DommaschkSectionReflection.reflect]
  have R : 0 < x 0 := rpos
  have eq := DommaschkSectionReflection.flow_reflect t x R
  rw [ref] at eq
  have orig := ratio_eq_physical 0 1 t x R (by simpa [clockPoly,x,
    DommaschkSectionReflection.reflect] using dpos.ne')
  rw [eq,← orig] at flow
  have hr := hasDerivAt_pi.mp flow 0
  have hz := (hasDerivAt_pi.mp flow 1).neg
  simp only [ratioFlow,clockPoly,DommaschkSectionReflection.reflect,x,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,zero_add,one_mul,neg_neg] at hr hz
  refine ⟨_,(lt_div_iff₀ (mul_pos (pow_pos rpos 17) dpos)).mpr num,?_⟩
  apply (forward_derivative (R := fun a => y a 0) (Z := fun a => -(y a 1)) rpos dpos hr hz
    ).congr_of_eventuallyEq
  filter_upwards [hr.continuousAt.eventually (lt_mem_nhds rpos)] with a ha
  exact congrArg (· ^ 2) (by simpa using strength_reflected ha a (-(y a 1)))

/-- A lower slope bound for a squared nonnegative observable gives a quantitative
transverse crossing at every positive level it attains. -/
theorem at_positive_level {f : ℝ → ℝ} {k h t : ℝ} (nonneg : ∀ a, 0 ≤ f a)
    (hp : 0 < h) (hit : f t = h)
    (hs : ∃ v > k, HasDerivAt (fun a => (f a) ^ 2) v t) :
    ∃ v > k / (2 * h), HasDerivAt f v t := by
  obtain ⟨v, lower, derivative⟩ := hs
  refine ⟨v / (2 * h), div_lt_div_of_pos_right lower (by positivity), ?_⟩
  have positive : f t ≠ 0 := hit.trans_ne hp.ne'
  simpa only [Real.sqrt_sq (nonneg _), hit, Real.sqrt_sq hp.le] using
    derivative.sqrt (pow_ne_zero 2 positive)

end PlasmaLean.Design.DommaschkMirrorStrengthSlope
