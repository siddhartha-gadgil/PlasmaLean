# PlasmaLean Rosetta Stone: stellarator physics, geometry and Lean 4

This reference maps magnetic-confinement terminology to topology, differential geometry and complex geometry, and says for each concept what exists in the `PlasmaLean` library. Every declaration named below was checked against the source (30 October 2026). Entries marked *not in the library* show an illustrative sketch (a proposed signature) that does not compile.

14 concepts. Status counts: in the library: 5, partly in the library: 8, not in the library: illustrative sketch: 1.

## Magnetic flux surface (ψ = const)

*Topology & Foliations.* A surface onto which the magnetic field lines are everywhere tangent (B · ∇ψ = 0). Whether a given equilibrium actually has nested flux surfaces is a theorem to prove, not an assumption: in general it need not (Grad's question).

**Geometry.** Level set Σ_c = ψ⁻¹(c) of a first integral ψ of B (ℒ_B ψ = 0). If Σ_c is a compact, connected, orientable regular level set and B is nowhere zero on it, then χ(Σ_c) = 0 by Poincaré–Hopf, so Σ_c is a 2-torus. Nothing forces a general magnetohydrostatic field to have such a first integral.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/FirstIntegral.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/FirstIntegral.lean).

```lean
-- PlasmaLean/Theory/Fields/FirstIntegral.lean (namespace PlasmaLean.Fields)
def FirstIntegralOn (B : Space → Space) (ψ : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ fderiv ℝ ψ x (B x) = 0

-- PlasmaLean/Design/LandremanGradCounterexample.lean
theorem fluxSurface_homeo_torus ... :
  ∃ h : Circle × Circle ≃ₜ {x : Space // x ∈ U a b ∧ psi a b x = c},
    ∀ p, (h p : Space) = torusMap a b c p.1 p.2
-- (the level sets of Landreman family 1 are tori, via the explicit torusMap)
```

## Solenoidal magnetic field (∇ · B = 0)

*Differential Geometry.* No magnetic monopoles: the magnetic flux through any closed surface vanishes.

**Geometry.** The flux 2-form ω_B = ι_B vol is closed (dω_B = 0); equivalently β = B♭ is co-closed. On a domain with H² = 0, ω_B = dα for a vector potential α. If B is tangent to the level sets of ψ, ω_B pulls back to zero on each level set.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Kernel/Vacuum.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Vacuum.lean).

```lean
-- PlasmaLean/Kernel/Vacuum.lean (namespace PlasmaLean.Vacuum)
def fieldDiv (B : Euclid3 → Euclid3) (x : Euclid3) : ℝ := divOp (fderiv ℝ B x)

-- PlasmaLean/Theory/Fields/FluxSurfaceTwoForm.lean (namespace PlasmaLean.Fields)
def magneticTwoForm (B u v : Space) : ℝ := ⟪B, cross u v⟫
theorem magneticTwoForm_flux_surface ... :
    magneticTwoForm (B x) u v = 0

-- Not in the library: differential forms on a general manifold (only ℝ³ vectors).
```

## Vacuum magnetic field (∇ · B = 0, ∇ × B = 0)

*Differential & Complex Geometry.* The field in a current-free region (J = 0), produced by external coil currents.

**Geometry.** A harmonic 1-form β (dβ = 0, d*β = 0) on a Riemannian 3-manifold with boundary. By the Hodge–Morrey–Friedrichs decomposition, the harmonic fields tangent to the boundary form a space isomorphic to H¹_dR(M; ℝ) (dimension 1 for a solid torus).

**Lean status: In the library.** Module: [`PlasmaLean/Kernel/Vacuum.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Vacuum.lean).

```lean
-- PlasmaLean/Kernel/Vacuum.lean (kernel law, namespace PlasmaLean.Vacuum)
structure VacuumField (Ω : Set Euclid3) (B : Euclid3 → Euclid3) : Prop where
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 2 B Ω
  div_eq_zero : ∀ x ∈ Ω, fieldDiv B x = 0
  curl_eq_zero : ∀ x ∈ Ω, fieldCurl B x = 0

-- Audit V-1: VacuumField ∅ B holds for every B (Sanity/AuditVacuum.vacuumField_empty).
-- Not in the library: boundary conditions, Hodge decomposition.
```

## Rotational transform ι and safety factor q = 1/ι

*Topology & Dynamical Systems.* Average number of poloidal turns of a field line per toroidal turn on a flux surface. A current-free axisymmetric field has ι = 0; a stellarator gets ι > 0 from the 3-D shape of the external field.

**Geometry.** The Poincaré rotation number of the circle map induced by the field-line return map on an invariant torus. A Diophantine ι supports KAM persistence of the torus; a rational ι = n/m permits island chains.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Design/RationalStellaratorFieldLines.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/RationalStellaratorFieldLines.lean).

```lean
-- No general rotation-number definition yet (planned: Q-21 / G-11).
-- Adjacent compiled pieces:
-- PlasmaLean/Theory/KAM/Diophantine.lean (namespace PlasmaLean.Theory.KAM)
def Diophantine (ω γ : ℝ) (τ : ℕ) : Prop :=
  ∀ k m : ℤ, k ≠ 0 → γ / |(k : ℝ)| ^ τ ≤ |(k : ℝ) * ω - m|

-- PlasmaLean/Design/RationalStellaratorFieldLines.lean
theorem rationalStellarator_confined_forever_exists : ...
-- every field line of the exact vacuum field starting inside the
-- KAM-certified torus A (ι ≈ 0.137) exists and stays inside for all time.
-- ι also appears as a field of BoozerField (Theory/Kinetic/BoozerGuidingCentre).
```

## Magnetohydrostatic (MHS) equilibrium (J × B = ∇p)

*Differential & Symplectic Geometry.* Static force balance: the Lorentz force balances the pressure gradient.

**Geometry.** With β = B♭ and J = ⋆dβ, the equation reads ι_J ι_B vol = dp. B and J are tangent to the level sets of p. When ∇p = 0 and J is parallel to B it reduces to a Beltrami field ⋆dβ = λβ (a contact form when λ ≠ 0).

**Lean status: In the library.** Module: [`PlasmaLean/Kernel/Equilibrium.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Equilibrium.lean).

```lean
-- PlasmaLean/Kernel/Equilibrium.lean (kernel law, namespace PlasmaLean)
class ForceBalance (B J g : Vec3) : Prop where
  balance : J ⨯₃ B = g

theorem field_tangency (B J g : Vec3) [ForceBalance B J g] : B ⬝ᵥ g = 0

-- g is supplied data. Audit E-1: ForceBalance B J (J ⨯₃ B) holds for any B, J,
-- so a claim must also prove g = ∇p and J = (∇ × B)/μ₀, e.g.
-- PlasmaLean/Design/ForceBalanceGradient.lean: solovev_force_balance_gradient
```

## Boozer coordinates (ψ, θ_B, φ_B)

*Differential Geometry.* Flux coordinates in which field lines are straight and the covariant representation of B has surface-function coefficients.

**Geometry.** A chart adapted to the foliation by ψ in which ω_B = dψ ∧ (dθ_B − ι(ψ) dφ_B) and β = I(ψ) dθ_B + G(ψ) dφ_B + ν dψ.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Kinetic/BoozerGuidingCentre.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Kinetic/BoozerGuidingCentre.lean).

```lean
-- The existence of Boozer charts is not in the library.
-- What is there: vacuum Boozer field DATA, used by the guiding-centre model.
-- PlasmaLean/Theory/Kinetic/BoozerGuidingCentre.lean (namespace PlasmaLean.Kinetic.Boozer)
structure BoozerField where
  B : ℝ → ℝ → ℝ → ℝ        -- |B|(ψ, θ, φ)
  Bψ Bθ Bφ : ℝ → ℝ → ℝ → ℝ  -- its partial derivatives
  ψp : ℝ → ℝ                -- poloidal flux
  ι : ℝ → ℝ                 -- rotational transform
  G : ℝ                     -- covariant toroidal component (vacuum: I = 0)
  ...
-- Audit MA-L3: BoozerField allows G = 0 and B ≤ 0.
```

## Quasisymmetry (QA, QH)

*Differential & Symplectic Geometry.* |B| depends on the Boozer angles only through one helical combination Mθ − Nφ. Quasisymmetry is one special case of omnigeneity (contract clause C2); quasi-isodynamic fields are another.

**Geometry.** Weak quasisymmetry (Constantin–Drivas–Ginsberg): a nonvanishing divergence-free vector field ξ with B × ξ = −∇ψ and ξ · ∇|B| = 0. It gives a conserved momentum for guiding-centre motion.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/WeakQuasisymmetry.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/WeakQuasisymmetry.lean).

```lean
-- PlasmaLean/Theory/Fields/WeakQuasisymmetry.lean (namespace PlasmaLean.Fields)
structure WeakQS (B ξ : Space → Space) (ψ : Space → ℝ) (T : Set Space) : Prop where
  ...
  xi_ne : ∀ x ∈ T, ξ x ≠ 0
  div_free : ∀ x ∈ T, divergence (fderiv ℝ ξ x) = 0
  cross_eq : ∀ x ∈ T, cross (B x) (ξ x) = -gradient ψ x
  qs : ∀ x ∈ T, qsError B ξ x = 0

def qsDefect (B ξ : Space → Space) (T : Set Space) : ℝ≥0∞ :=
  ⨆ x ∈ T, ENNReal.ofReal |qsError B ξ x|

-- PlasmaLean/Design/LandremanNotQS.lean: family1_not_weakQS, family2_not_weakQS
```

## Near-axis expansion (Garren–Boozer, Landreman–Sengupta)

*Differential Geometry of Curves.* Asymptotic expansion of a field or equilibrium in powers of the distance r from a closed magnetic-axis curve.

**Geometry.** Jet expansion in tubular coordinates around a closed curve with curvature κ and torsion τ. First-order quasisymmetry reduces to a periodic Riccati-type ODE for the rotating elliptical cross-section.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Design/NearAxisQA.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/NearAxisQA.lean).

```lean
-- A truncated second-order near-axis |B| model (formal asymptotics, no
-- remainder bound) fitted to the 'precise QA' configuration:
-- PlasmaLean/Design/NearAxisQA.lean (namespace PlasmaLean.Design.NearAxisQA)
theorem nearAxis_symmetryDefect ...  -- ξB = −2 b₁ r² sin 2φ exactly
theorem nearAxis_epsQS ...           -- ε_QS(r) = 2|b₁| r²

-- Not in the library: a magnetic-axis curve structure, the Riccati (σ) equation,
-- or convergence of the near-axis series.
```

## Guiding-centre drift motion

*Symplectic & Poisson Geometry.* The averaged motion of a charged particle gyrating around field lines, with ∇B and curvature drifts.

**Geometry.** A Hamiltonian system on M × ℝ (position and v∥) with Littlejohn's non-canonical symplectic form Ω = q dA* (A* = A + (m v∥/q) b) and Hamiltonian H = ½ m v∥² + μ|B|. The bounce invariant J∥ = ∮ v∥ dl is the action of trapped orbits.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Kinetic/GuidingCentreLittlejohn.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Kinetic/GuidingCentreLittlejohn.lean).

```lean
-- The equations of motion (supplied model; static B, E = 0):
-- PlasmaLean/Theory/Kinetic/GuidingCentreLittlejohn.lean
-- (namespace PlasmaLean.Kinetic.GCLittlejohn)
structure LittlejohnOrbit (m q μ : ℝ) (B : Space → Space)
    (X : ℝ → Space) (v : ℝ → ℝ) : Prop where
  hX : ∀ t, HasDerivAt X ((BstarPar m q B (v t) (X t))⁻¹ • (...)) t
  hv : ∀ t, HasDerivAt v (-(μ / m) * (BstarPar m q B (v t) (X t))⁻¹ * ...) t

theorem hamiltonian_hasDerivAt ...  -- energy is conserved along orbits

-- Not in the library: the symplectic form itself, J∥, bounce averages.
```

## Ideal MHD stability: energy principle and Mercier criterion

*Spectral Geometry & Calculus of Variations.* An equilibrium is linearly stable to ideal modes if the potential energy δ²W(ξ, ξ) is positive for every admissible displacement. Local criteria (Mercier interchange, ballooning) are necessary conditions.

**Geometry.** Positivity of the Hessian δ²W(ξ, ξ) = −½ ∫ ⟨ξ, F(ξ)⟩ of the energy, F a formally self-adjoint second-order operator. The Mercier index D_Merc > 0 is the local interchange condition on one surface.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Stability/MercierGeneral.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Stability/MercierGeneral.lean).

```lean
-- No δ²W functional or MHD force operator in the library.
-- PlasmaLean/Theory/Stability/MercierGeneral.lean
-- (namespace PlasmaLean.Stability.MercierGeneral)
def mercierIndex (d : MercierSurfaceData) : ℝ :=
  (d.shearBracket ^ 2 + d.wellBracket * d.intB2) / (2 * π) ^ 6
def MercierStable (d : MercierSurfaceData) : Prop := 0 < mercierIndex d

-- PlasmaLean/Design/LandremanFamily2MercierDerived.lean:
--   family2_mercier_stable_derived (a certified Mercier-stable band; the index
--   is supplied by Landreman–Jorge, and family 2 carries net toroidal current).
-- Abstract conserved energy: Theory/Stability/AbstractEnergy.energy_conserved
```

## Non-overlapping flux surfaces and positive Jacobian (√g > 0)

*Complex Geometry & Harmonic Mappings.* Nested surfaces given by double Fourier series R(s,θ,φ), Z(s,θ,φ) must not self-intersect or fold inside the plasma.

**Geometry.** det(DΦ) > 0 for Φ : D² × S¹ → M. Slice by slice in φ this is univalence of a planar harmonic map of the disk (Radó–Kneser–Choquet, ℓ¹ coefficient criteria).

**Lean status: Not in the library: illustrative sketch.**

```lean
-- Illustrative sketch, not in the library (proposed signature):
def ValidFluxCoordinateMap (Φ : PolarToroidalDomain → ℝ³) : Prop :=
  Function.Injective Φ ∧ ∀ x ∈ interiorDomain, jacobianDet Φ x > 0

-- See Challenge 5 (lean_stubs/Challenge5_HarmonicUnivalence.lean).
```

## Biot–Savart law and field derivatives for filament coils

*Integral Geometry & Operator Calculus.* The field of filamentary current loops, and its spatial derivatives and its sensitivity to coil-shape errors.

**Geometry.** B(x) = (μ₀ I / 4π) ∮ γ'(s) × (x − γ(s)) / |x − γ(s)|³ ds, smooth (indeed harmonic) away from the curve. The circulation of B around a second closed curve is μ₀ I times the Gauss linking number.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/BiotSavart.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/BiotSavart.lean).

```lean
-- PlasmaLean/Theory/Fields/BiotSavart.lean (namespace PlasmaLean.Fields)
def filamentKernel (c : ℝ → Space) (t : ℝ) (x : Space) : Space := ...
def filamentField (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space) : Space :=
  (μ₀ * I / (4 * Real.pi)) • ∫ t in a..b, filamentKernel c t x

-- Theory/Fields/FieldDerivative.lean:   filamentField_derivative,
--                                       filamentField_derivative_bound
-- Theory/Fields/CoilPerturbation.lean:  filamentField_perturbation
-- Sanity/Vacuum.lean:                   filamentField_vacuumField
-- Not in the library: the Gauss linking number (Challenge 2).
```

## Coil clearance and winding-pack envelopes

*Metric & Submanifold Geometry.* Engineering constraints: coils must keep a minimum distance from each other and from the plasma, and be windable (bounded curvature).

**Geometry.** Tubular neighbourhoods of radius r of the coil curves; disjointness follows from a centreline separation d > r₁ + r₂. Embeddedness of the tube needs r below the reach of the curve (Federer), which is controlled by curvature.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Geometry/CoilTube.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/CoilTube.lean).

```lean
-- PlasmaLean/Theory/Geometry/CoilTube.lean (namespace PlasmaLean.Geometry)
def CoilTube (c : ℝ → Space) (r : ℝ) : Set Space := ...
theorem tube_clearance (c₁ c₂ : ℝ → Space) {d r₁ r₂ : ℝ}
    (sep : ∀ t u, d ≤ dist (c₁ t) (c₂ u)) {x y : Space}
    (hx : x ∈ CoilTube c₁ r₁) (hy : y ∈ CoilTube c₂ r₂) :
    d - r₁ - r₂ ≤ dist x y

-- Design/VacuumTolerance.lean: manufactured_tube_clearance (two-loop fixture)
-- Not in the library: a general curvature/reach contract for coil sets.
```

## Flux-surface metric and conformal modulus

*Complex Geometry (Riemann Surfaces).* The geometry of one toroidal surface relates the poloidal and toroidal fluxes and currents to the energy of the field on that surface.

**Geometry.** The induced metric makes each torus a Riemann surface ℂ / (ℤ + τℤ) with modulus τ in the upper half-plane. The energy of a closed 1-form with periods (a, b) is at least |b − aτ|² / Im τ, with equality exactly for the harmonic form.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Geometry/TorusHodge.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/TorusHodge.lean).

```lean
-- Constant-metric (flat torus) case only.
-- PlasmaLean/Theory/Geometry/TorusHodge.lean (namespace PlasmaLean.Geometry.TorusHodge)
structure ConstMetric  -- E dx² + 2F dx dy + G dy², E > 0, EG − F² > 0
def ConstMetric.tau : ℂ := ⟨m.F / m.E, √m.det / m.E⟩
theorem latticeMetric_tau ...   -- the lattice metric has τ = ω₂/ω₁
theorem periodBound_eq (a b : ℝ) :
    m.periodBound a b = m.dens a b / √m.det
theorem energy_ge (m : ConstMetric) :
    m.periodBound α.periodP α.periodT ≤ α.energy m

-- Not in the library: a non-constant metric (needs uniformization).
```
