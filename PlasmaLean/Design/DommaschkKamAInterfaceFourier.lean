/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamATorus
public import PlasmaLean.Design.DommaschkKamCContract
public import PlasmaLean.Theory.Stability.InterfaceFourierTaylor

/-!
# Finite Fourier interpretation of the Dommaschk interface seed

The coefficients are the same packed integers as in the torus A KAM certificate.
The oracle angle is twice the geometric toroidal angle. The quarter-period shift
in the analytic representation cancels when the profiles are evaluated.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamAInterfaceFourier

open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Certificates.KronBall
open PlasmaLean.Design.DommaschkKamC PlasmaLean.Design.KamNewton Complex

/-- All poloidal and toroidal Fourier modes of a stored rectangular grid. -/
def modes (N M : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) N) ×ˢ (Finset.Icc (-(M : ℤ)) M)

/-- The real amplitude attached to a mode of the symmetrically completed packed grid. -/
def amplitude (S N M : ℕ) (g : ℕ → ℕ → ℤ) (p : ℤ × ℤ) : ℝ :=
  (g (p.1 + N).toNat (p.2 + M).toNat : ℝ) / 2 ^ S

private theorem mem_modes {N M : ℕ} {km : ℤ × ℤ} :
    km ∈ modes N M ↔ |km.1| ≤ N ∧ |km.2| ≤ M := by
  simp [modes, abs_le]

private theorem real_mode (S p : ℕ) (v : ℤ) (x : ℝ) :
    (((2 : ℂ)^S * I^p)⁻¹ * v * Complex.exp ((x : ℂ)*I)).re =
      ((v : ℝ) / 2^S) * Real.cos (x - p*(Real.pi/2)) := by
  have hp := exp_quarter (p : ℤ)
  push_cast at hp
  rw [zpow_natCast] at hp
  rw [mul_inv_rev, ← hp, ← Complex.exp_neg]
  have e : Complex.exp (-((p : ℂ) * ((Real.pi : ℂ)/2) * I)) *
      ((2 : ℂ)^S)⁻¹ * v * Complex.exp ((x : ℂ)*I) =
      (((v : ℝ)/2^S : ℝ) : ℂ) *
      Complex.exp (((x - p*(Real.pi/2) : ℝ) : ℂ)*I) := by
    push_cast
    rw [sub_mul, Complex.exp_sub]
    simp [Complex.exp_neg, div_eq_mul_inv]
    ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The finite trigonometric sum represented by a real or imaginary-phase packed grid,
in geometric radian angles. -/
theorem grid_eq_sum (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (θ φ : ℝ) :
    (eval (ctr S N M (1,0,p) (gridPolyNM N M g)) θ (2*φ)).re =
    ∑ k ∈ modes N M, amplitude S N M g k *
      Real.cos (k.1*θ + (2*k.2)*φ - p*(Real.pi/2)) := by
  unfold eval fourierSum
  rw [tsum_eq_sum (s := modes N M) (fun km h => by
    have hn := mt mem_modes.mpr h
    simp [coeff_ctr_grid, hn])]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro km hkm
  simp only [coeff_ctr_grid, mem_modes.mp hkm, and_self, ↓reduceIte, fourierMode]
  simpa only [amplitude, mul_left_comm, mul_assoc] using
    real_mode S p (g (km.1+N).toNat (km.2+M).toNat) (km.1*θ + km.2*(2*φ))

/-- A mixed physical-angle derivative of the stored grid. Differentiating a cosine
advances its phase by a quarter turn and multiplies by the corresponding frequency. -/
def gridJet (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (θ φ : ℝ) : ℝ :=
  ∑ k ∈ modes N M, amplitude S N M g k * (k.1 : ℝ)^a * (2*k.2 : ℝ)^b *
    Real.cos (k.1*θ + (2*k.2)*φ + ((a : ℝ)+b-p)*(Real.pi/2))

/-- The physical grid evaluates to its zeroth angular jet. -/
theorem zeroJet (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (θ φ : ℝ) :
    (eval (ctr S N M (1,0,p) (gridPolyNM N M g)) θ (2*φ)).re =
    gridJet S N M p g 0 0 θ φ := by
  simpa [gridJet, sub_eq_add_neg] using grid_eq_sum S N M p g θ φ

/-- Radial profile of the actual packed A seed, in geometric angles. -/
theorem radius_seed_eq (θ φ : ℝ) :
    RofC DommaschkKamA.u₀A θ φ = 29/32 +
      gridJet DommaschkKamA.Sc DommaschkKamA.Nc DommaschkKamA.Mc 0 DommaschkKamA.gU 0 0 θ φ := by
  unfold RofC DommaschkKam.dkR0 Zof
  rw [DommaschkKamA.eval_u₀A, KamTorusA.psi, sub_add_cancel]
  exact congrArg (fun x : ℝ => 29/32+x) (zeroJet _ _ _ _ _ _ _)

/-- Vertical profile of the actual packed A seed, in geometric angles. -/
theorem height_seed_eq (θ φ : ℝ) :
    Zof DommaschkKamA.z₀A θ φ =
      gridJet DommaschkKamA.Sc DommaschkKamA.Nc DommaschkKamA.Mc 1 DommaschkKamA.gZ 0 0 θ φ := by
  unfold Zof
  rw [DommaschkKamA.eval_z₀A, KamTorusA.psi, sub_add_cancel]
  exact zeroJet _ _ _ _ _ _ _

private theorem derivative_term {f : ℝ → ℝ} {w t d c h : ℝ}
    (hf : HasDerivAt f w t) (hd : d = c * w) (he : h = f t + Real.pi / 2) :
    HasDerivAt (fun x => c * Real.cos (f x)) (d * Real.cos h) t := by
  convert (hf.cos.const_mul c) using 1
  rw [hd, he, Real.cos_add_pi_div_two]
  ring

/-- The poloidal derivative of a packed Fourier jet. -/
theorem gridJet_poloidal (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (θ φ : ℝ) :
    HasDerivAt (fun t => gridJet S N M p g a b t φ)
      (gridJet S N M p g (a+1) b θ φ) θ := by
  unfold gridJet
  apply HasDerivAt.fun_sum
  intro k _
  apply derivative_term
  · exact ((((hasDerivAt_id θ).const_mul _).add_const _).add_const _)
  · rw [pow_succ]
    ring
  · push_cast
    ring

/-- The geometric toroidal derivative of a packed Fourier jet; the stored frequency is doubled. -/
theorem gridJet_toroidal (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (θ φ : ℝ) :
    HasDerivAt (fun t => gridJet S N M p g a b θ t)
      (gridJet S N M p g a (b+1) θ φ) φ := by
  unfold gridJet
  apply HasDerivAt.fun_sum
  intro k _
  apply derivative_term
  · exact (HasDerivAt.const_add _ ((hasDerivAt_id φ).const_mul _)).add_const _
  · rw [pow_succ]
    ring
  · push_cast
    ring

/-- Amplitudes of the one-dimensional jet, summed over the transverse modes at θ = 0. -/
def sliceAmplitude (S N M : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (m : ℤ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) N, amplitude S N M g (k,m) *
    (k : ℝ)^a * (2*m : ℝ)^b

/-- Exact integer numerator of a collapsed jet coefficient. -/
def sliceNumerator (N M : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (m : ℤ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) N, g (k+N).toNat (m+M).toNat * k^a * (2*m)^b

/-- Dividing the integer numerator by the packing scale gives the physical Fourier amplitude. -/
theorem sliceAmplitude_eq_numerator (S N M : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (m : ℤ) :
    sliceAmplitude S N M g a b m = (sliceNumerator N M g a b m : ℝ) / 2^S := by
  unfold sliceAmplitude amplitude sliceNumerator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- At θ = 0 the differentiated packed grid becomes a single toroidal Fourier series. -/
theorem gridJet_slice (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (φ : ℝ) :
    gridJet S N M p g a b 0 φ =
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, sliceAmplitude S N M g a b m *
      Real.cos (((a : ℝ)+b-p)*(Real.pi/2) + (2*m)*φ) := by
  unfold gridJet modes sliceAmplitude
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp [add_comm]

open PlasmaLean.Stability.InterfaceFourierTaylor in
/-- A Taylor enclosure on the actual packed grid slice. The remaining numerical inputs are
its five signed polynomial moments and its absolute fifth moment, all finite sums. -/
theorem gridJet_slice_taylor (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℕ) (φ : ℝ) :
    |gridJet S N M p g a b 0 φ -
      ∑ m ∈ Finset.Icc (-(M : ℤ)) M, sliceAmplitude S N M g a b m *
        cosTaylorFour (((a : ℝ)+b-p)*(Real.pi/2)) ((2*m)*φ)| ≤
    (∑ m ∈ Finset.Icc (-(M : ℤ)) M, |sliceAmplitude S N M g a b m| * |(2*m : ℝ)|^5) *
      (|φ|^5/120) := by
  rw [gridJet_slice]
  exact sum_cosTaylorFour_error _ _ _ _ _

end PlasmaLean.Design.DommaschkKamAInterfaceFourier
