/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.Mercier

/-!
# The general (3-D) Mercier index from flux-surface data, and its cylindrical reduction

**Source (supplied formula).** M. Landreman and R. Jorge, *Magnetic well and Mercier
stability of stellarators near the magnetic axis*, J. Plasma Phys. 86, 905860510 (2020),
arXiv:2006.14881v2 (retrieved 2026-10-20), eq. (3.1) (labelled `eq:mercric` in the source):

  `(2π)⁶ D_Merc = [s_G 2π² ι' - ∫ B·Ξ dS/|∇ψ|³]² + [s_ψ μ₀ p' V'' - ∫ |Ξ|² dS/|∇ψ|³] ∫ B² dS/|∇ψ|³`,

with `2πψ` the toroidal flux, `' = d/dψ`, `Ξ = μ₀ J - I'(ψ) B` (`I` the Boozer covariant
poloidal component, i.e. `μ₀/(2π)` times the enclosed toroidal current), `V(ψ)` the enclosed
volume, `s_G, s_ψ = ±1` the signs of `G` and `ψ`, and surface integrals over one flux surface.
The source states this is Mercier's criterion (C. Mercier, Nucl. Fusion Suppl. 1962, eq. (37),
multiplied by `ι⁶`) and is equivalent to the Bauer–Betancourt–Garabedian (1984) form
`D_Shear + D_Curr + D_Well + D_Geod` reported by VMEC. **Mercier stability requires
`D_Merc > 0`**; `D_Merc < 0` on a surface means localized interchange instability there
(necessary condition for ideal-MHD stability; the asymptotic derivation from `δW` is NOT
formalized — this file treats the formula as a supplied interface).

`MercierSurfaceData` collects the eight real numbers entering the formula on one surface;
`mercierIndex` is `D_Merc`. Computing these numbers for an actual equilibrium (flux-surface
integrals, derivatives in `ψ`) is the responsibility of the caller, and every use states how
they were obtained.

**Consistency check of the supplied formula (proved).** For a straight periodic screw pinch of
length `ℓ` the surface data are exact closed forms (`cylinderData`), and
`mercierIndex_cylinder` proves, using only the radial force balance,

  `D_Merc = ℓ² μ₀ Bθ² / (8 π⁴ r⁵ Bz⁶) · (r Bz² (q'/q)²/(8μ₀) + p')`,

i.e. a positive multiple of the library's `suydamQuantity` (`mercierIndex_cylinder_eq_suydam`).
So signs and normalizations of the supplied formula agree with Suydam's criterion
(`PlasmaLean.Equilibrium.ScrewPinch`) and with `Mercier.mercierDI`
(`cylinder_mercier_pos_iff_mercierDI_neg`).

**General sufficient conditions (proved, algebraic).**
* `mercierIndex_pos_of_well`: a magnetic well dominating the `|Ξ|²` term,
  `∫|Ξ|²/|∇ψ|³ < s_ψ μ₀ p' V''`, gives `D_Merc > 0` (stable);
* `mercierIndex_neg_of_hill`: a magnetic hill (`s_ψ μ₀ p' V'' ≤ 0`) plus weak shear,
  `X² < ∫|Ξ|²/|∇ψ|³ · ∫B²/|∇ψ|³` where `X = s_G 2π² ι' - ∫ B·Ξ/|∇ψ|³`, gives `D_Merc < 0`.

Scope: local interchange criterion only; no ballooning, global, resistive or kinetic statement.
-/

public section
noncomputable section
namespace PlasmaLean.Stability.MercierGeneral
open Real PlasmaLean.Equilibrium.ScrewPinch PlasmaLean.Stability.Mercier

/-- Flux-surface data entering the general Mercier index on one surface (toroidal-flux label
`ψ`, `2πψ` = toroidal flux). All integrals are over the whole flux surface. -/
structure MercierSurfaceData where
  /-- Sign of the Boozer covariant toroidal component `G` (`±1`). -/
  sG : ℝ
  /-- Sign of `ψ` (`±1`). -/
  sψ : ℝ
  /-- Magnetic shear `dι/dψ`. -/
  iotaPrime : ℝ
  /-- `μ₀ dp/dψ`. -/
  muPprime : ℝ
  /-- `d²V/dψ²`. -/
  Vpp : ℝ
  /-- `∫ B·Ξ dS/|∇ψ|³`. -/
  intBXi : ℝ
  /-- `∫ |Ξ|² dS/|∇ψ|³`. -/
  intXi2 : ℝ
  /-- `∫ B² dS/|∇ψ|³`. -/
  intB2 : ℝ

namespace MercierSurfaceData

/-- The shear/current bracket `X = s_G 2π² ι' - ∫ B·Ξ dS/|∇ψ|³`. -/
@[expose] def shearBracket (d : MercierSurfaceData) : ℝ :=
  d.sG * (2 * π ^ 2) * d.iotaPrime - d.intBXi

/-- The well bracket `W = s_ψ μ₀ p' V'' - ∫ |Ξ|² dS/|∇ψ|³`. -/
@[expose] def wellBracket (d : MercierSurfaceData) : ℝ :=
  d.sψ * d.muPprime * d.Vpp - d.intXi2

end MercierSurfaceData

/-- The general Mercier index `D_Merc` (Landreman–Jorge 2020, eq. (3.1)); stability requires
`D_Merc > 0`. -/
@[expose] def mercierIndex (d : MercierSurfaceData) : ℝ :=
  (d.shearBracket ^ 2 + d.wellBracket * d.intB2) / (2 * π) ^ 6

/-- Mercier stability on a surface: `D_Merc > 0`. -/
@[expose] def MercierStable (d : MercierSurfaceData) : Prop := 0 < mercierIndex d

/-- A dominant magnetic well gives Mercier stability. -/
theorem mercierIndex_pos_of_well {d : MercierSurfaceData} (hB : 0 < d.intB2)
    (hw : d.intXi2 < d.sψ * d.muPprime * d.Vpp) : MercierStable d := by
  unfold MercierStable mercierIndex MercierSurfaceData.wellBracket
  have : 0 < (d.sψ * d.muPprime * d.Vpp - d.intXi2) * d.intB2 := mul_pos (by linarith) hB
  positivity

/-- A magnetic hill with weak shear gives Mercier instability (`D_Merc < 0`). -/
theorem mercierIndex_neg_of_hill {d : MercierSurfaceData} (hB : 0 < d.intB2)
    (hhill : d.sψ * d.muPprime * d.Vpp ≤ 0)
    (hX : d.shearBracket ^ 2 < d.intXi2 * d.intB2) : mercierIndex d < 0 := by
  unfold mercierIndex MercierSurfaceData.wellBracket
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith

/-- Sanity: with no pressure gradient, no `Ξ` (current-free and `I' = 0`) and nonzero shear the
index is the pure shear term `ι'²/(16π²) > 0` (the vacuum value). -/
theorem mercierIndex_vacuum (sG sψ ι' V'' B2 : ℝ) (hs : sG ^ 2 = 1) :
    mercierIndex ⟨sG, sψ, ι', 0, V'', 0, 0, B2⟩ = ι' ^ 2 / (16 * π ^ 2) := by
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  linear_combination 16 * ι' ^ 2 * hs

/-! ## Cylindrical reduction (consistency check of the supplied formula) -/

/-- Exact flux-surface data of a straight periodic screw pinch of length `ℓ` on the surface of
radius `r`, from the pointwise profile values `Bθ = bt`, `Bz = bz > 0`, derivatives `bt'`,
`bz'` and `p_r = pr` (SI). Here `dψ/dr = r Bz`, `ι = ℓ Bθ/(2π r Bz)`, `dV/dψ = 2πℓ/Bz`,
`I = r Bθ`, `Ξ = (μ₀ p_r / Bz) e_θ` (by force balance), `dS = r dθ dz`, `|∇ψ| = r Bz`.
The signs `s_G = s_ψ = 1` and `|∇ψ| = r Bz` assume `Bz > 0` and `r > 0`; the algebraic
identities below hold for `bz ≠ 0`, but the data are the physical ones only for `bz > 0`. -/
@[expose] def cylinderData (μ₀ ℓ r bt bz bt' bz' pr : ℝ) : MercierSurfaceData where
  sG := 1
  sψ := 1
  iotaPrime := ℓ / (2 * π) * (bt' * r * bz - bt * (bz + r * bz')) / (r * bz) ^ 2 / (r * bz)
  muPprime := μ₀ * pr / (r * bz)
  Vpp := -(2 * π * ℓ * bz' / (bz ^ 2 * (r * bz)))
  intBXi := 2 * π * r * ℓ * (μ₀ * bt * pr / bz) / (r * bz) ^ 3
  intXi2 := 2 * π * r * ℓ * (μ₀ ^ 2 * pr ^ 2 / bz ^ 2) / (r * bz) ^ 3
  intB2 := 2 * π * r * ℓ * (bt ^ 2 + bz ^ 2) / (r * bz) ^ 3

/-- **Cylindrical reduction.** Under the radial force balance
`μ₀ p_r + Bz Bz' + Bθ (Bθ + r Bθ')/r = 0`, the general Mercier index of a screw pinch is
`ℓ² μ₀ Bθ²/(8π⁴ r⁵ Bz⁶)` times the Suydam quantity `r Bz² (q'/q)²/(8μ₀) + p_r`, with
`q'/q = 1/r + Bz'/Bz - Bθ'/Bθ`. -/
theorem mercierIndex_cylinder {μ₀ ℓ r bt bz bt' bz' pr : ℝ} (hμ : μ₀ ≠ 0) (hr : r ≠ 0)
    (hbz : bz ≠ 0) (hbt : bt ≠ 0)
    (hfb : μ₀ * pr + bz * bz' + bt * (bt + r * bt') / r = 0) :
    mercierIndex (cylinderData μ₀ ℓ r bt bz bt' bz' pr) =
      ℓ ^ 2 * μ₀ * bt ^ 2 / (8 * π ^ 4 * r ^ 5 * bz ^ 6) *
        (r * bz ^ 2 * (1 / r + bz' / bz - bt' / bt) ^ 2 / (8 * μ₀) + pr) := by
  have hfb' : μ₀ * pr * r + bz * bz' * r + bt * (bt + r * bt') = 0 := by
    have := congrArg (· * r) hfb
    simp only [add_mul, zero_mul] at this
    rw [div_mul_cancel₀ _ hr] at this
    linarith
  have hbz' : bz' = -(μ₀ * pr + bt * (bt + r * bt') / r) / bz := by
    field_simp; linear_combination hfb'
  have hπ : π ≠ 0 := pi_ne_zero
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket
    cylinderData
  simp only
  rw [hbz']
  field_simp
  ring

/-- The cylindrical reduction in terms of the library's screw-pinch quantities
(`S = Bz²`, `S' = 2 Bz Bz'`, `RadialBalance`-type pointwise balance): `D_Merc` is a positive
multiple of `suydamQuantity`. -/
theorem mercierIndex_cylinder_eq_suydam {μ₀ ℓ r bz bz' : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : μ₀ ≠ 0) (hr : r ≠ 0) (hbz : bz ≠ 0) (hbt : Bθ r ≠ 0) (hS : S r = bz ^ 2)
    (hS' : S' r = 2 * bz * bz')
    (hbal : p' r + (2 * Bθ r * Bθ' r + S' r) / (2 * μ₀) + Bθ r ^ 2 / (μ₀ * r) = 0) :
    mercierIndex (cylinderData μ₀ ℓ r (Bθ r) bz (Bθ' r) bz' (p' r)) =
      ℓ ^ 2 * μ₀ * Bθ r ^ 2 / (8 * π ^ 4 * r ^ 5 * bz ^ 6) *
        suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  have hfb : μ₀ * p' r + bz * bz' + Bθ r * (Bθ r + r * Bθ' r) / r = 0 := by
    rw [hS'] at hbal
    field_simp at hbal ⊢
    linear_combination hbal
  rw [mercierIndex_cylinder hμ hr hbz hbt hfb]
  congr 1
  unfold suydamQuantity shearRatio
  rw [hS, hS']
  field_simp

/-- Positivity of the cylindrical prefactor. -/
theorem cylinder_prefactor_pos {μ₀ ℓ r bt bz : ℝ} (hμ : 0 < μ₀) (hℓ : ℓ ≠ 0) (hr : 0 < r)
    (hbz : bz ≠ 0) (hbt : bt ≠ 0) :
    0 < ℓ ^ 2 * μ₀ * bt ^ 2 / (8 * π ^ 4 * r ^ 5 * bz ^ 6) := by
  have := pi_pos
  have h1 : 0 < ℓ ^ 2 := by positivity
  have h2 : 0 < bt ^ 2 := by positivity
  have h3 : 0 < bz ^ 6 := by positivity
  positivity

/-- **Cylindrical Mercier = Suydam** for the general formula: on a surface with `r > 0`,
`Bθ ≠ 0`, the general index is positive iff Suydam holds strictly. -/
theorem cylinder_mercier_pos_iff_suydam {μ₀ ℓ r bz bz' : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hℓ : ℓ ≠ 0) (hr : 0 < r) (hbz : bz ≠ 0) (hbt : Bθ r ≠ 0)
    (hS : S r = bz ^ 2) (hS' : S' r = 2 * bz * bz')
    (hbal : p' r + (2 * Bθ r * Bθ' r + S' r) / (2 * μ₀) + Bθ r ^ 2 / (μ₀ * r) = 0) :
    MercierStable (cylinderData μ₀ ℓ r (Bθ r) bz (Bθ' r) bz' (p' r)) ↔
      0 < suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  unfold MercierStable
  rw [mercierIndex_cylinder_eq_suydam hμ.ne' hr.ne' hbz hbt hS hS' hbal]
  exact ⟨fun h => pos_of_mul_pos_right h (cylinder_prefactor_pos hμ hℓ hr hbz hbt).le,
    fun h => mul_pos (cylinder_prefactor_pos hμ hℓ hr hbz hbt) h⟩

/-- Link to the cylindrical Greene–Johnson index of `Mercier`: with nonzero shear,
`D_Merc > 0 ⟺ D_I < 0`. -/
theorem cylinder_mercier_pos_iff_mercierDI_neg {μ₀ ℓ r bz bz' : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hℓ : ℓ ≠ 0) (hr : 0 < r) (hbz : bz ≠ 0) (hbt : Bθ r ≠ 0)
    (hS : S r = bz ^ 2) (hS' : S' r = 2 * bz * bz')
    (hbal : p' r + (2 * Bθ r * Bθ' r + S' r) / (2 * μ₀) + Bθ r ^ 2 / (μ₀ * r) = 0)
    (hsh : shearRatio Bθ S Bθ' S' r ≠ 0) :
    MercierStable (cylinderData μ₀ ℓ r (Bθ r) bz (Bθ' r) bz' (p' r)) ↔
      mercierDI μ₀ p' Bθ S Bθ' S' r < 0 := by
  rw [cylinder_mercier_pos_iff_suydam hμ hℓ hr hbz hbt hS hS' hbal,
    mercier_lt_iff_suydam hμ hr (by rw [hS]; positivity) hsh]

/-- Sanity (shearless pinch): with zero shear (`q'/q = 0`) and an outward-decreasing pressure
the general index is negative — Mercier instability, as for Suydam. -/
theorem cylinder_mercier_neg_of_shearless {μ₀ ℓ r bt bz bt' bz' pr : ℝ} (hμ : 0 < μ₀)
    (hℓ : ℓ ≠ 0) (hr : 0 < r) (hbz : bz ≠ 0) (hbt : bt ≠ 0)
    (hfb : μ₀ * pr + bz * bz' + bt * (bt + r * bt') / r = 0)
    (hsh : 1 / r + bz' / bz - bt' / bt = 0) (hp : pr < 0) :
    mercierIndex (cylinderData μ₀ ℓ r bt bz bt' bz' pr) < 0 := by
  rw [mercierIndex_cylinder hμ.ne' hr.ne' hbz hbt hfb, hsh]
  have := cylinder_prefactor_pos hμ hℓ hr hbz hbt
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    zero_add]
  exact mul_neg_of_pos_of_neg this hp

end PlasmaLean.Stability.MercierGeneral
