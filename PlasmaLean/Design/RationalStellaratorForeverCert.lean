/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusA

/-!
# Torus A is star-shaped with respect to its own poloidal angle (KAM route, K3 geometry)

A small certificate used by `Design/RationalStellaratorForever`: on torus A of
`Design/KamTorusA`, the radial vector `(R − 1, z)` from the exact magnetic axis has a positive
component along the direction `(cos θ, sin θ)` of the flow angle `θ`:

  `(R − 1) cos θ + z sin θ ≥ 1/20`  for all real `θ, φ`  (`torusA_radial_ge`).

Equivalently `w = ((R − 1) + i z) e^{−iθ}` has `Re w ≥ 1/20`, so `arg w` has a smooth branch
`arctan (Im w / Re w)` and the polar angle of `(R − 1, z)` about the axis has the smooth lift
`θ + arg w` (numerically `Re w ∈ [0.088, 0.19]`, mean `0.1397`).

**Method** (as for the winding rate in `Design/KamTorusA`): with `u = e^{iθ}`, `v = e^{iψ}` and the
grid polynomials `R̂ = t R`, `Ẑ = t (i z)` (`t = σ uᴺ vᴹ`),

  `Ŵ = (R̂ − t + Ẑ) + (R̂ − t − Ẑ) u²  =  2σ uᴺ⁺¹ vᴹ · ((R − 1) cos θ + z sin θ)`

(`evalC_radPoly`), so the value is at least `(c₀ − ‖Ŵ − c₀ uᴺ⁺¹vᴹ‖₁)/(2σ)`, where the centre
coefficient `c₀ = 2 (cA_{N+1,M} + cB_{N+1,M})` (`c0W`) and the `ℓ¹` norm (an exact Kronecker digit
sum, `l1_radSub`) are computed in the kernel (`check_rad`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Finset Polynomial PlasmaLean.Certificates.Kron2

/-- The radial form `(R̂ − t + Ẑ) + (R̂ − t − Ẑ) U` over any commutative ring. -/
def radForm {α : Type*} [CommRing α] (Rh Zh t U : α) : α := (Rh - t + Zh) + (Rh - t - Zh) * U

/-- `radForm` commutes with ring homomorphisms. -/
theorem radForm_map {α β : Type*} [CommRing α] [CommRing β] (f : α →+* β) (Rh Zh t U : α) :
    f (radForm Rh Zh t U) = radForm (f Rh) (f Zh) (f t) (f U) := by
  simp [radForm]

/-- The monomial `u²`. -/
noncomputable def uSqP : P2 := monomial 0 (monomial 2 1)

/-- The radial polynomial `Ŵ` of torus A. -/
noncomputable def radPoly : P2 := radForm (gridPoly gR) (gridPoly gZ) tP uSqP

/-- The centre coefficient of `Ŵ` (at `u^{N+1} vᴹ`). -/
def c0W : ℤ := 2 * (cA (N + 1) M + cB (N + 1) M)

/-- The centre monomial `c0W u^{N+1} vᴹ`. -/
noncomputable def radMono : P2 := monomial M (monomial (N + 1) c0W)

/-- Integer value of `Ŵ` under Kronecker substitution (computed by the kernel). -/
def radInt (b W : ℕ) : ℤ :=
  radForm (packGrid b W gR (2 * M + 1)) (packGrid b W gZ (2 * M + 1))
    ((sig * 2 ^ (b * (N + W * M)) : ℕ) : ℤ) ((2 ^ (b * 2) : ℕ) : ℤ)

/-- A priori bound for `Ŵ − c0W · mono`: below `2^191`, so digit sums are exact. -/
theorem apriori_rad : 2 * (gridL1 gR + sig + gridL1 gZ) + c0W.natAbs < 2 ^ (192 - 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖Ŵ − c0W u^{N+1} vᴹ‖₁ ≤ L` with `(c0W − L)/(2σ) ≥ 1/20`. -/
theorem check_rad :
    20 * (l1Kron 192 13
        (radInt 192 129 - c0W * ((pow2 (192 * ((N + 1) + 129 * M)) : ℕ) : ℤ)) : ℤ) +
        2 * (sig : ℤ) ≤ 20 * c0W := by
  decide +kernel

/-- Kronecker image of `u²`. -/
theorem kron_uSqP (b W : ℕ) : kron b W uSqP = ((2 ^ (b * 2) : ℕ) : ℤ) := by
  rw [uSqP, kron_monomial]; push_cast; ring_nf

/-- The exact `ℓ¹` norm of `Ŵ − c0W u^{N+1} vᴹ` is the kernel digit sum. -/
theorem l1_radSub : l1 (radPoly - radMono) =
    l1Kron 192 13 (radInt 192 129 - c0W * ((pow2 (192 * ((N + 1) + 129 * M)) : ℕ) : ℤ)) := by
  have hk : kron 192 129 (radPoly - radMono) =
      radInt 192 129 - c0W * ((pow2 (192 * ((N + 1) + 129 * M)) : ℕ) : ℤ) := by
    have e : ((pow2 (192 * ((N + 1) + 129 * M)) : ℕ) : ℤ) =
        (2 : ℤ) ^ (192 * ((N + 1) + 129 * M)) := by
      rw [pow2_eq, Nat.cast_pow, Nat.cast_ofNat]
    rw [map_sub, radPoly, radForm_map, kron_gridPoly, kron_gridPoly, kron_tP, kron_uSqP, radMono,
      kron_monomial, radInt, e]
  rw [← hk]
  have hU : InBox uSqP 2 0 := InBox.monomial _ _ _
  have hA : InBox (gridPoly gR - tP + gridPoly gZ) (2 * N) (2 * M) :=
    ((box_gridPoly _).sub (box_tP.mono (by omega) (by omega))).add (box_gridPoly _)
  have hB : InBox (gridPoly gR - tP - gridPoly gZ) (2 * N) (2 * M) :=
    ((box_gridPoly _).sub (box_tP.mono (by omega) (by omega))).sub (box_gridPoly _)
  refine l1_eq_l1Kron (a := 2 * N + 2) (J := 2 * M) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · unfold radPoly radForm
    exact InBox.sub (InBox.add (hA.mono (by omega) le_rfl) ((hB.mul hU).mono le_rfl (by omega)))
      ((InBox.monomial _ _ _).mono (by omega) (by omega))
  · have hR := l1_gridPoly_le gR
    have hZ := l1_gridPoly_le gZ
    have hAl : l1 (gridPoly gR - tP + gridPoly gZ) ≤ gridL1 gR + sig + gridL1 gZ :=
      l1_add' (l1_sub' hR l1_tP) hZ
    have hBl : l1 (gridPoly gR - tP - gridPoly gZ) ≤ gridL1 gR + sig + gridL1 gZ :=
      l1_sub' (l1_sub' hR l1_tP) hZ
    have hUl : l1 uSqP ≤ 1 := by rw [uSqP, l1_monomial]; simp
    have hW : l1 radPoly ≤ 2 * (gridL1 gR + sig + gridL1 gZ) := by
      unfold radPoly radForm
      have := l1_add' hAl (l1_mul' hBl hUl)
      omega
    have hM : l1 radMono ≤ c0W.natAbs := by rw [radMono, l1_monomial]
    exact (l1_sub' hW hM).trans_lt apriori_rad

/-- `((R − 1) + i z) + ((R − 1) − i z) u² = 2 u ((R − 1) cos θ + z sin θ)` for `u = e^{iθ}`. -/
theorem rad_identity (θ a z : ℝ) :
    ((a : ℂ) + Complex.I * z) + ((a : ℂ) - Complex.I * z) * uu θ ^ 2 =
      ((2 * (a * Real.cos θ + z * Real.sin θ) : ℝ) : ℂ) * uu θ := by
  have hu : uu θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [uu, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [hu, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  generalize (Real.cos θ : ℂ) = c at hcs ⊢
  generalize (Real.sin θ : ℂ) = s at hcs ⊢
  linear_combination (-(a : ℂ) - Complex.I * z) * hcs +
    ((a : ℂ) * s ^ 2 - 2 * (z : ℂ) * c * s - Complex.I * z * s ^ 2) * Complex.I_sq

/-- `Ŵ` evaluated on the unit torus. -/
theorem evalC_radPoly (θ φ : ℝ) : evalC (uu θ) (vv φ) radPoly =
    (((2 * (sig : ℝ)) * ((torusR θ φ - 1) * Real.cos θ + torusZ θ φ * Real.sin θ) : ℝ) : ℂ) *
      (uu θ ^ (N + 1) * vv φ ^ M) := by
  rw [radPoly, radForm_map, evalC_Rh, evalC_Zh, evalC_tP, uSqP, evalC_monomial, tt, ww]
  have h := rad_identity θ (torusR θ φ - 1) (torusZ θ φ)
  simp only [radForm]
  push_cast at h ⊢
  linear_combination ((sig : ℂ) * uu θ ^ N * vv φ ^ M) * h

/-- **Torus A is star-shaped in its flow angle**: `(R − 1) cos θ + z sin θ ≥ 1/20`. -/
theorem torusA_radial_ge (θ φ : ℝ) :
    1 / 20 ≤ (torusR θ φ - 1) * Real.cos θ + torusZ θ φ * Real.sin θ := by
  have hκ : (0 : ℝ) < 2 * (sig : ℝ) := by have := sig_pos; positivity
  have hlow := le_of_evalC (norm_uu θ) (norm_vv φ) hκ c0W (evalC_radPoly θ φ)
  rw [show (monomial M (monomial (N + 1) c0W) : P2) = radMono from rfl, l1_radSub] at hlow
  have c : 20 * ((l1Kron 192 13
      (radInt 192 129 - c0W * ((pow2 (192 * ((N + 1) + 129 * M)) : ℕ) : ℤ)) : ℕ) : ℝ) +
      2 * (sig : ℝ) ≤ 20 * (c0W : ℝ) := by exact_mod_cast check_rad
  refine le_trans ?_ hlow
  rw [le_div_iff₀ hκ]; linarith

end PlasmaLean.Design.KamTorusA
