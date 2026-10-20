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
public import PlasmaLean.Theory.Equilibrium.ScrewPinch
public import PlasmaLean.Theory.Fields.BiotSavart
public import PlasmaLean.Theory.Fields.CircularLoop
public import PlasmaLean.Theory.Fields.InverseCube
public import PlasmaLean.Theory.Fields.FieldVariation
public import PlasmaLean.Theory.Fields.CoilPerturbation
public import PlasmaLean.Theory.Fields.FieldDerivative
public import PlasmaLean.Theory.Fields.Maxwell
public import PlasmaLean.Theory.Fields.FirstIntegral
public import PlasmaLean.Theory.Fields.ClebschDivergence
public import PlasmaLean.Theory.Geometry.ParametricBounds
public import PlasmaLean.Theory.Geometry.CircularCoil
public import PlasmaLean.Theory.Geometry.CoilTube
public import PlasmaLean.Theory.Geometry.PlacedCircle
public import PlasmaLean.Theory.Stability.AbstractEnergy
public import PlasmaLean.Theory.Stability.BlockBounds
public import PlasmaLean.Theory.Stability.YoungBounds
public import PlasmaLean.Theory.Stability.Suydam
public import PlasmaLean.Theory.Stability.Newcomb
public import PlasmaLean.Theory.Stability.ScrewPinchModes
public import PlasmaLean.Theory.Kinetic.ApproximateInvariant
public import PlasmaLean.Theory.Kinetic.FullOrbit
public import PlasmaLean.Theory.Kinetic.CanonicalMomentum
public import PlasmaLean.Theory.Kinetic.Noether
public import PlasmaLean.Theory.Engineering.SlabHeat
public import PlasmaLean.Certificates.RationalIntervals
public import PlasmaLean.Certificates.BlockBounds
public import PlasmaLean.Certificates.Contraction
public import PlasmaLean.Certificates.PolyInterval
public import PlasmaLean.Bridge.Contracts
public import PlasmaLean.Design.ScalarRoot
public import PlasmaLean.Design.SlabExample
public import PlasmaLean.Design.VacuumPair
public import PlasmaLean.Design.VacuumTolerance
public import PlasmaLean.Design.VacuumDerivative
public import PlasmaLean.Design.ClebschTorus
public import PlasmaLean.Design.ClebschTorusDivergence
public import PlasmaLean.Design.PolyTokamak
public import PlasmaLean.Design.Solovev
public import PlasmaLean.Design.HelicalStellarator
public import PlasmaLean.Design.HelicalDivergence
public import PlasmaLean.Design.HelicalEquilibrium
public import PlasmaLean.Design.HelicalReactorScale
public import PlasmaLean.Design.ScrewPinchExample
public import PlasmaLean.Design.ScrewPinchModes
public import PlasmaLean.SubsetSum
public import PlasmaLean.Kernel.Fusion
public import PlasmaLean.Kernel.Transport
public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Sanity.Fusion
public import PlasmaLean.Sanity.Transport
public import PlasmaLean.Sanity.Vacuum
public import PlasmaLean.Theory.Transport.PowerBalance
public import PlasmaLean.Theory.Transport.Comparison
public import PlasmaLean.Theory.Fields.Subharmonic
public import PlasmaLean.Theory.Stability.Elsasser
public import PlasmaLean.Theory.Kinetic.AvailableEnergy
public import PlasmaLean.Certificates.SBP
public import PlasmaLean.Design.BurnWindow

/-!
# PlasmaLean public library

Explicit model laws, sanity checks, analytic building blocks, exact certificate
soundness, and labelled synthetic examples. This entry point does not assert a
practical stellarator design; see the dated progress and assumption ledger.
-/
