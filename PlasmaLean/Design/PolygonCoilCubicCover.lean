/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicCells0
public import PlasmaLean.Design.PolygonCoilCubicCells1
public import PlasmaLean.Design.PolygonCoilCubicCells2
public import PlasmaLean.Design.PolygonCoilCubicCells3
public import PlasmaLean.Design.PolygonCoilCubicConfined

/-!
# Confinement over 52 transits for the concrete cubic-certified coil set

Assembles the four face covers `faceCovC_F` (`Design/PolygonCoilCubicCellsF`) into `coversC` and
applies `coil_confined_of_coversC` (`Design/PolygonCoilCubicConfined`).
-/

public section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF
  PlasmaLean.Design.RationalStellarator.Confined Set Real

/-- **The four face covers** (kernel certificates, `η = etaC·2⁻⁴⁰`). -/
theorem coversC : CoversC := ⟨faceCovC_0, faceCovC_1, faceCovC_2, faceCovC_3⟩

/-- **Confinement over 52 transits in the field of a concrete polygonal coil set.** Every field
line of the coil field `tfField + polyCoilFieldC` (the closed TF filament plus the 8 closed
polygonal helical filaments `filsC`, 192 straight segments, `Design/PolygonCoilCubicData`) on
`[0, 8·52]` starting in the start tube stays in the confinement tube `T` and its toroidal angle
advances by at least `2π·52` (52 transits).

Conditional on the field line: `γ` is assumed to solve the field-line equation on `[0, 8·52]`
(existence is not proved here). The certified winding error on the frontier is
`etaRC = etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶` (0.016 % margin against the 52-transit budget). The coil
geometry comes from untrusted design scripts (`scripts/rational_stellarator_coils/`); only the
certificate is trusted. -/
theorem coil_stellarator_confined_concrete_N {γ : ℝ → Space}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (8 * 52), HasDerivAt γ (coilField polyCoilFieldC (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Icc (0 : ℝ) (8 * 52), γ s ∈ tubeT) ∧
      2 * π * 52 ≤ ∫ u in (0 : ℝ)..(8 * 52), phiRateOf (coilField polyCoilFieldC) (γ u) :=
  coil_confined_of_coversC coversC hγ h0

end PlasmaLean.Design.PolygonCoil
