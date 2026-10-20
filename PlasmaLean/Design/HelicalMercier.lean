/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalEquilibrium
public import PlasmaLean.Theory.Stability.MercierGeneral

/-!
# Local interchange (Mercier) stability of the exact helical equilibria — a negative result

Criterion used. For a helically symmetric (straight, periodic) equilibrium the local
interchange criterion is Mercier's criterion, which in helical symmetry is a 1-D condition
in the flux label: every term of the general index `D_Merc`
(`PlasmaLean.Stability.MercierGeneral.mercierIndex`, Landreman–Jorge 2020 eq. (3.1), supplied
formula) is a function of the surface only, and in helical symmetry the surface integrals
reduce to line integrals over one cross-section times the period. No separate "helical
Suydam" formula is needed: the general formula specializes to Suydam in the cylinder
(`MercierGeneral.mercierIndex_cylinder`, proved).

## Rigorous results (`a = 0` member: exact uniform-current screw pinch)

The helical family `HelicalEquilibrium.eqField a` at `a = 0` is
`B = (-2 x₁, 2 x₀, 4)` exactly (`eqField_zero`): a uniform axial field `Bz = 4` and a
uniform axial current (`Bθ = 2r`), with `ψ = r²` and `μ₀ p = p₀ - 4 r²`. Proved here:

* `zero_radialBalance`: the screw-pinch radial force balance of
  `PlasmaLean.Equilibrium.ScrewPinch` holds for these profiles (consistent with the kernel
  law `force_balance` already proved for every `a`);
* `zero_shearless`: the safety factor is constant (`shearRatio = 0` on every surface; the field
  lines have `dθ/dz = 1/2` everywhere — `zero_pitch`);
* `zero_suydam_fails`: Suydam fails on EVERY surface `r > 0` (`suydamQuantity = p' < 0`);
* `zero_mercier_unstable`: the general Mercier index is negative on every surface, for any
  period length — the `a = 0` equilibrium is Mercier (interchange) unstable throughout.

## The `a = 1/4` equilibrium (the reactor-scale instance): numerical finding, NOT certified

Untrusted oracle `scripts/helical_mercier_oracle.py` (exact symbolic `B`, `J = ∇ × B`, force
balance checked to 1e-15; flux-surface integrals by the trapezoidal rule on 2000 points of the
cross-section curve `R = r²(u)` solving the quadratic `ψ = c`; derivatives by central
differences) gives, with period `ℓ = π` and the toroidal-flux label:

| `ψ_h = c` | `ι` | `dι/dψ` | `μ₀p'V''` | `∫|Ξ|²/|∇ψ|³` | `X²/∫B²/|∇ψ|³` | `D_Merc` |
| --- | --- | --- | --- | --- | --- | --- |
| 0.001 | 0.2580 | 0.0089 | -0.309 | 1.157 | 0.00052 | -0.114 |
| 0.01 | 0.2581 | 0.0090 | -0.316 | 1.160 | 0.0052 | -0.0115 |
| 0.03 | 0.2585 | 0.0092 | -0.332 | 1.168 | 0.016 | -0.0039 |
| 0.05 | 0.2589 | 0.0095 | -0.349 | 1.176 | 0.027 | -0.0024 |
| 0.08 = ψ_b | 0.2595 | 0.0099 | -0.375 | 1.190 | 0.044 | -0.0015 |

So the helical equilibrium has a magnetic HILL (`V'' > 0`) and very weak shear; the hill
condition of `MercierGeneral.mercierIndex_neg_of_hill` holds with a margin of about
27× (edge) to 2200× (near axis),
i.e. the equilibrium is Mercier UNSTABLE on every computed surface of the plasma, like its
`a = 0` limit. (The `a = 0` run of the same oracle reproduces the exact shearless values,
`ι = 1/4`, `ι' = 0`, `V'' = 0`, and its `D_Merc` agrees to 1e-6 relative with the exact Lean
value `mercierIndex_cylinder = -1/(1024 π² r²)` (`-0.001237` at `c = 0.08`); this check is
asserted in the script.) `oracle_surface_unstable` records that the rounded edge-surface
numbers satisfy the hypotheses of `mercierIndex_neg_of_hill`; this is a fixture showing how a
certificate would close, NOT a proof about the equilibrium: rigorous enclosures of the
surface integrals and of `ι'`, `V''` are not available (they need validated quadrature on
non-circular surfaces).

Consequence for the design ladder: the exact helical equilibrium of `HelicalEquilibrium`
should not be used as an MHD-stable M0/M2 geometry; a stable straight-helical equilibrium
needs strong shear or a helical magnetic axis (axis curvature is what produces a well in
near-axis theory, Landreman–Jorge 2020 §4).

Scope: local ideal interchange only (necessary condition). Straight helical model, no toroidal
curvature; `μ₀ = 1` dimensionless units as in `HelicalEquilibrium` for the `a = 0` profiles
(`μ₀` kept general where harmless).
-/

public section
noncomputable section
namespace PlasmaLean.Design.HelicalMercier
open Set Real PlasmaLean.Fields PlasmaLean.Design.HelicalFamily
  PlasmaLean.Design.HelicalEquilibrium PlasmaLean.Equilibrium.ScrewPinch
  PlasmaLean.Stability.MercierGeneral WithLp

/-! ## The `a = 0` member is the uniform-current screw pinch -/

/-- At `a = 0` the helical flux function is `ψ = r²`. -/
theorem eqPsi_zero (x : Space) : eqPsi 0 x = x 0 ^ 2 + x 1 ^ 2 := by
  simp [eqPsi, psi, amp, r2]

/-- At `a = 0` the equilibrium field is exactly `B = (-2 x₁, 2 x₀, 4)`: uniform axial field
`4` and uniform axial current density (`Bθ = 2r`). -/
theorem eqField_zero (x : Space) : eqField 0 x = toLp 2 ![-2 * x 1, 2 * x 0, 4] := by
  have hD := (D_pos x).ne'
  unfold D r2 at hD
  ext i
  fin_cases i <;>
    simp [eqField, field, Dinv, D, r2, N0, N1, N2, G0, G1, G2, Fv, psi, amp, P0, P1] <;>
    field_simp <;> ring

/-- At `a = 0` the pressure is `(p₀ - 4 r²)/μ₀`. -/
theorem pressure_zero (μ₀ p₀ : ℝ) (x : Space) :
    pressure μ₀ p₀ 0 x = (p₀ - 4 * (x 0 ^ 2 + x 1 ^ 2)) / μ₀ := by
  rw [pressure, eqPsi_zero]

/-- Poloidal field profile `Bθ(r) = 2r` of the `a = 0` member. -/
@[expose] def zBθ (r : ℝ) : ℝ := 2 * r
/-- Its derivative. -/
@[expose] def zBθ' (_ : ℝ) : ℝ := 2
/-- Squared axial field `S = Bz² = 16`. -/
@[expose] def zS (_ : ℝ) : ℝ := 16
/-- Its derivative. -/
@[expose] def zS' (_ : ℝ) : ℝ := 0
/-- Pressure profile `p(r) = (p₀ - 4 r²)/μ₀`. -/
@[expose] def zp (μ₀ p₀ r : ℝ) : ℝ := (p₀ - 4 * r ^ 2) / μ₀
/-- Pressure gradient `p'(r) = -8r/μ₀`. -/
@[expose] def zp' (μ₀ r : ℝ) : ℝ := -8 * r / μ₀

/-- The profiles are those of the 3-D field: on the ray `(r, 0, z)` the field is
`(0, Bθ(r), √S)` and the pressure is `p(r)`. -/
theorem zero_profiles (μ₀ p₀ r z : ℝ) :
    eqField 0 (toLp 2 ![r, 0, z]) = toLp 2 ![0, zBθ r, Real.sqrt (zS r)] ∧
      pressure μ₀ p₀ 0 (toLp 2 ![r, 0, z]) = zp μ₀ p₀ r := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [eqField_zero]; ext i; fin_cases i <;> simp [zBθ, zS, h16]
  · rw [pressure_zero]; simp [zp]

/-- The `a = 0` profiles satisfy the screw-pinch radial force balance on every `(0, a]`. -/
theorem zero_radialBalance {μ₀ a p₀ : ℝ} (hμ : 0 < μ₀) (ha : 0 < a) :
    RadialBalance μ₀ a (zp μ₀ p₀) zBθ zS (zp' μ₀) zBθ' zS' where
  permeability_pos := hμ
  radius_pos := ha
  pressure_deriv r _ := by
    have := (((hasDerivAt_id' r).pow 2).const_mul 4).const_sub p₀ |>.div_const μ₀
    convert this using 1
    · funext s; simp [zp]
    · simp [zp']; ring
  poloidal_deriv r _ := by
    change HasDerivAt (fun y : ℝ => 2 * y) 2 r
    simpa using (hasDerivAt_id' r).const_mul (2 : ℝ)
  axial_deriv r _ := by
    change HasDerivAt (fun _ : ℝ => (16 : ℝ)) 0 r
    exact hasDerivAt_const r 16
  axial_pos _ _ := by norm_num [zS]
  balance r hr := by
    have := hr.1.ne'
    simp only [zp', zBθ, zBθ', zS']
    field_simp
    ring

/-- Field-line pitch: `dθ/dz = Bθ/(r Bz) = 1/2` on every surface (constant rotational
transform). -/
theorem zero_pitch {r : ℝ} (hr : r ≠ 0) : zBθ r / (r * Real.sqrt (zS r)) = 1 / 2 := by
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  simp only [zBθ, zS, h16]
  field_simp
  ring

/-- The `a = 0` equilibrium is shearless: `q'/q = 0` on every surface `r ≠ 0`. -/
theorem zero_shearless {r : ℝ} (hr : r ≠ 0) : shearRatio zBθ zS zBθ' zS' r = 0 := by
  simp only [shearRatio, zBθ, zS, zBθ', zS']
  field_simp
  ring

/-- **Suydam fails on every surface** of the `a = 0` equilibrium: `suydamQuantity = p' < 0`. -/
theorem zero_suydam_fails {μ₀ r : ℝ} (hμ : 0 < μ₀) (hr : 0 < r) :
    suydamQuantity μ₀ (zp' μ₀) zBθ zS zBθ' zS' r < 0 := by
  rw [suydamQuantity, zero_shearless hr.ne']
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    zero_add, zp']
  exact div_neg_of_neg_of_pos (by linarith) hμ

/-- Equivalently, the cylindrical Greene–Johnson index cannot be certified: Suydam stability
fails on every `(0, a]`. -/
theorem zero_not_suydamStableOn {μ₀ a : ℝ} (hμ : 0 < μ₀) (ha : 0 < a) :
    ¬ SuydamStableOn μ₀ a (zp' μ₀) zBθ zS zBθ' zS' := fun h =>
  absurd (h a ⟨ha, le_rfl⟩) (not_le.mpr (zero_suydam_fails hμ ha))

/-- **General Mercier index negative on every surface** of the `a = 0` equilibrium, for every
period length `ℓ ≠ 0` (exact cylinder data, `Bz = 4`, `Bz' = 0`, `Bθ = 2r`, `Bθ' = 2`,
`p_r = -8r/μ₀`). -/
theorem zero_mercier_unstable {μ₀ ℓ r : ℝ} (hμ : 0 < μ₀) (hℓ : ℓ ≠ 0) (hr : 0 < r) :
    mercierIndex (cylinderData μ₀ ℓ r (2 * r) 4 2 0 (-8 * r / μ₀)) < 0 := by
  apply cylinder_mercier_neg_of_shearless hμ hℓ hr (by norm_num) (by positivity)
  · field_simp; ring
  · field_simp; ring
  · exact div_neg_of_neg_of_pos (by linarith) hμ

/-- The same statement through the library's `suydamQuantity` link: on every surface
`D_Merc = (positive) · suydamQuantity < 0`. -/
theorem zero_not_mercierStable {μ₀ ℓ r : ℝ} (hμ : 0 < μ₀) (hℓ : ℓ ≠ 0) (hr : 0 < r) :
    ¬ MercierStable (cylinderData μ₀ ℓ r (zBθ r) 4 (zBθ' r) 0 (zp' μ₀ r)) := by
  rw [cylinder_mercier_pos_iff_suydam (S := zS) (S' := zS') (Bθ := zBθ) hμ hℓ hr (by norm_num)
    (mul_ne_zero two_ne_zero hr.ne')
    (by norm_num [zS]) (by norm_num [zS']) ((zero_radialBalance (p₀ := 0) hμ hr).balance r
      ⟨hr, le_rfl⟩)]
  exact not_lt.mpr (zero_suydam_fails hμ hr).le

/-! ## `a = 1/4`: oracle fixture (numerical, not a proof about the equilibrium) -/

/-- Rounded oracle data on the edge surface `ψ_h = ψ_b = 0.08` of the `a = 1/4` equilibrium
(period `π`): `ι' ≈ 0.0099`, `μ₀ p' ≈ -4/ψ_c`, `μ₀p'V'' ≈ -0.375`, `∫|Ξ|²/|∇ψ|³ ≈ 1.19`.
Only `shearBracket² / intB2 ≈ 0.044` and the signs matter; `intB2` and `intBXi` are chosen
consistently with that ratio. NUMERICAL, from `scripts/helical_mercier_oracle.py`. -/
@[expose] def oracleEdge : MercierSurfaceData where
  sG := 1
  sψ := 1
  iotaPrime := 0
  muPprime := -15 / 4
  Vpp := 1 / 10
  intBXi := 66 / 100
  intXi2 := 119 / 100
  intB2 := 10

/-- Fixture: the rounded oracle edge data satisfy the hill hypotheses of
`mercierIndex_neg_of_hill`, so `D_Merc < 0` for them. This certifies the reasoning step only;
the inputs are NOT rigorous enclosures for the equilibrium. -/
theorem oracle_surface_unstable : mercierIndex oracleEdge < 0 := by
  apply mercierIndex_neg_of_hill <;>
    norm_num [oracleEdge, MercierSurfaceData.shearBracket]

end PlasmaLean.Design.HelicalMercier
