/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Basic
public import PlasmaLean.Kernel.Equilibrium
public import PlasmaLean.Kernel.Slab
public import PlasmaLean.Kernel.ThermalSlab
public import PlasmaLean.Sanity.Equilibrium
public import PlasmaLean.Sanity.NeutralMode
public import PlasmaLean.Sanity.ProbeEscape
public import PlasmaLean.Theory.Equilibrium.Slab
public import PlasmaLean.Theory.Fields.BiotSavart
public import PlasmaLean.Theory.Fields.CircularLoop
public import PlasmaLean.Theory.Fields.InverseCube
public import PlasmaLean.Theory.Fields.FieldVariation
public import PlasmaLean.Theory.Fields.CoilPerturbation
public import PlasmaLean.Theory.Fields.FieldDerivative
public import PlasmaLean.Theory.Geometry.ParametricBounds
public import PlasmaLean.Theory.Geometry.CircularCoil
public import PlasmaLean.Theory.Geometry.CoilTube
public import PlasmaLean.Theory.Geometry.PlacedCircle
public import PlasmaLean.Theory.Stability.AbstractEnergy
public import PlasmaLean.Theory.Stability.BlockBounds
public import PlasmaLean.Theory.Stability.YoungBounds
public import PlasmaLean.Theory.Kinetic.ApproximateInvariant
public import PlasmaLean.Theory.Engineering.SlabHeat
public import PlasmaLean.Certificates.RationalIntervals
public import PlasmaLean.Certificates.BlockBounds
public import PlasmaLean.Certificates.Contraction
public import PlasmaLean.Bridge.Contracts
public import PlasmaLean.Design.ScalarRoot
public import PlasmaLean.Design.SlabExample
public import PlasmaLean.Design.VacuumPair
public import PlasmaLean.Design.VacuumTolerance
public import PlasmaLean.Design.VacuumDerivative

/-!
# PlasmaLean public library

Explicit model laws, sanity checks, analytic building blocks, exact certificate
soundness, and labelled synthetic examples. This entry point does not assert a
practical stellarator design; see the dated progress and assumption ledger.
-/
