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
public import PlasmaLean.Theory.Fields.FilamentSmooth
public import PlasmaLean.Sanity.FilamentVacuum
public import PlasmaLean.Theory.Fields.CurvatureObstruction
public import PlasmaLean.Sanity.CurvatureObstruction
public import PlasmaLean.Certificates.DiscreteMaxPrinciple
public import PlasmaLean.Certificates.SBPGeneral
public import PlasmaLean.Theory.Stability.Ballooning
public import PlasmaLean.Theory.Stability.Mercier
public import PlasmaLean.Design.ScrewPinchModesHighM
public import PlasmaLean.Sanity.BoschHaleInstance
public import PlasmaLean.Theory.Transport.ConfinementScaling
public import PlasmaLean.Design.BurnWindowScaling
public import PlasmaLean.Theory.Transport.BarrierCheck
public import PlasmaLean.Design.TransportBarrier
public import PlasmaLean.Theory.Kinetic.GuidingCentre
public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import PlasmaLean.Design.NearAxisQA
public import PlasmaLean.Design.SolovevAlpha
public import PlasmaLean.Theory.Kinetic.GyroNoether
public import PlasmaLean.Theory.Kinetic.OscillatoryAveraging
public import PlasmaLean.Design.BurnWindowStellarator
public import PlasmaLean.Theory.Stability.BallooningInfinite
public import PlasmaLean.Theory.Stability.SturmNecessity
public import PlasmaLean.Certificates.WeightedEll1
public import PlasmaLean.Certificates.RadiiPolynomial
public import PlasmaLean.Design.ValidatedBVP
public import PlasmaLean.Theory.Transport.FluxGeometry
public import PlasmaLean.Design.HelicalFluxGeometry
public import PlasmaLean.Design.HelicalTransportBarrier
public import PlasmaLean.Theory.Geometry.SurfaceCover
public import PlasmaLean.Design.VacuumPairVolumeError
public import PlasmaLean.Certificates.FourierRegularity
public import PlasmaLean.Design.ValidatedBVPClassical
public import PlasmaLean.Certificates.ConvAlgebra
public import PlasmaLean.Design.ValidatedSlabData
public import PlasmaLean.Design.ValidatedSlabEquilibrium
public import PlasmaLean.Theory.Stability.MercierGeneral
public import PlasmaLean.Design.HelicalMercier
public import PlasmaLean.Design.SolovevMercier
public import PlasmaLean.Theory.Kinetic.AveragedTrapping
public import PlasmaLean.Design.NearAxisQAAveraged

/-!
# PlasmaLean public library

Explicit model laws, sanity checks, analytic building blocks, exact certificate
soundness, and labelled synthetic examples. This entry point does not assert a
practical stellarator design; see the dated progress and assumption ledger.
-/
