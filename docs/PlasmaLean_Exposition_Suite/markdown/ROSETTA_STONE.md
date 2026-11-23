# PlasmaLean Rosetta Stone: stellarator physics, geometry and Lean 4

This reference maps magnetic-confinement terminology to topology, differential geometry, symplectic and contact geometry and complex geometry, and says for each concept what exists in the `PlasmaLean` library. Every declaration named below was checked against the source (16 November 2026). Entries marked *not in the library* show an illustrative sketch (a proposed signature) that does not compile. The geometric formulations follow the cited literature; each entry lists its sources.

29 concepts. Status counts: in the library: 14, partly in the library: 12, not in the library: illustrative sketch: 3.

## Magnetic flux surface (ψ = const)

*Topology & Foliations.* A surface onto which the magnetic field lines are everywhere tangent (B · ∇ψ = 0). Whether a given equilibrium actually has nested flux surfaces is a theorem to prove, not an assumption: in general it need not (Grad's question).

**Geometry.** Level set Σ_c = ψ⁻¹(c) of a first integral ψ of B (ℒ_B ψ = dψ(B) = 0); equivalently the flux form ω_B = ι_B vol pulls back to zero on Σ_c. If Σ_c is a compact, connected, orientable regular level set and B is nowhere zero on it, then χ(Σ_c) = 0 by Poincaré–Hopf, so Σ_c is a 2-torus. A divergence-free field tangent to such a torus preserves the area form ι_B vol / dψ on it; when it has no zeros and a Diophantine winding it is conjugate to a linear flow. Nothing forces a general magnetohydrostatic field to have a first integral.

**Sources.** Arnold, Ann. Inst. Fourier 16 (1966) 319; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998); MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150; Perrella, Pfefferlé & Stoyanov, Partial Differ. Equ. Appl. 3 (2022), doi:10.1007/s42985-022-00182-3, arXiv:2203.04137; Perrella, Duignan & Pfefferlé, J. Math. Phys. (2023), arXiv:2303.03191.

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

-- In form language (ι_B dψ = 0, B the vector of the flux form ω):
-- PlasmaLean/Theory/Fields/FormBridges.lean (namespace PlasmaLean.Forms)
def FormFirstIntegralOn (ω : Space → Form 2) (ψ : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ formGrad ψ x ![flux.symm (ω x)] = 0
theorem formFirstIntegralOn_flux_iff :
    FormFirstIntegralOn (fluxField B) ψ U ↔ FirstIntegralOn B ψ U

-- The contract's parametrised tori as embedded surfaces:
-- PlasmaLean/Theory/Fields/FormFluxSurfaceEmbedded.lean (namespace PlasmaLean.Forms)
structure EmbeddedTorus (R z : ℝ → ℝ → ℝ) : Prop extends PeriodicC2Torus R z where
  injective : InjectiveModPeriods R z
  immersion : ∀ p, Function.Injective (fderiv ℝ (torusMap R z) p)
theorem EmbeddedTorus.isSmoothEmbedding_torusEmb (h : EmbeddedTorus R z) :
    Manifold.IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2 (torusEmb R z)
theorem EmbeddedTorus.of_sections ...   -- R > 0, sections injective mod 2π, (∂_θR, ∂_θz) ≠ 0
-- A FieldTorus need not be embedded (the doubly covered torus: dbl_not_embeddedTorus).
```

## Clebsch representation B = ∇ψ × ∇α and flux coordinates

*Differential & Symplectic Geometry.* A divergence-free field written with two scalar potentials: a flux label ψ and a field-line label α. Both are constant along field lines.

**Geometry.** ω_B = dψ ∧ dα. Near any point where B ≠ 0 the closed 2-form ω_B has this normal form (Darboux theorem for a closed 2-form of rank 2), and ψ, α are local first integrals. Globally on a family of flux tori α is multivalued: α = θ − ι(ψ)φ in straight-field-line angles, which is the contravariant (Boozer or Hamada) form ω_B = dψ ∧ (dθ − ι dφ). (ψ, α) are canonically conjugate coordinates on the space of field lines.

**Sources.** MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150; Boozer, Rev. Mod. Phys. 76 (2004) 1071; D'haeseleer, Hitchon, Callen & Shohet, Flux Coordinates and Magnetic Field Structure (Springer, 1991).

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/FirstIntegral.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/FirstIntegral.lean).

```lean
-- PlasmaLean/Theory/Fields/FirstIntegral.lean (namespace PlasmaLean.Fields)
def clebschField (ψ χ : Space → ℝ) (x : Space) : Space :=
  cross (gradient ψ x) (gradient χ x)
theorem clebsch_firstIntegral_left (ψ χ : Space → ℝ) (U : Set Space)
    (hψ : ∀ x ∈ U, DifferentiableAt ℝ ψ x) : FirstIntegralOn (clebschField ψ χ) ψ U
theorem clebsch_sublevel_confined (ψ χ : Space → ℝ) (hψ : Differentiable ℝ ψ) (c : ℝ) :
    FieldLineConfined (clebschField ψ χ) {x | ψ x ≤ c}

-- PlasmaLean/Theory/Fields/ClebschDivergence.lean
theorem clebsch_divergence_free {ψ χ : Space → ℝ} {x : Space}
    (hψ : ContDiffAt ℝ 2 ψ x) (hχ : ContDiffAt ℝ 2 χ x) :
    divergence (fderiv ℝ (clebschField ψ χ) x) = 0

-- Not in the library: the local existence of Clebsch potentials (Darboux).
```

## Solenoidal magnetic field (∇ · B = 0)

*Differential Geometry.* No magnetic monopoles: the magnetic flux through any closed surface vanishes.

**Geometry.** The flux 2-form ω_B = ι_B vol is closed (dω_B = 0); equivalently β = B♭ is co-closed. On a domain with H² = 0, ω_B = dα for a vector potential α. If B is tangent to the level sets of ψ, ω_B pulls back to zero on each level set.

**Sources.** MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150; Cantarella, DeTurck & Gluck, Amer. Math. Monthly 109 (2002) 409.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Kernel/Vacuum.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Vacuum.lean).

```lean
-- PlasmaLean/Kernel/Vacuum.lean (namespace PlasmaLean.Vacuum)
def fieldDiv (B : Euclid3 → Euclid3) (x : Euclid3) : ℝ := divOp (fderiv ℝ B x)

-- PlasmaLean/Theory/Fields/FluxSurfaceTwoForm.lean (namespace PlasmaLean.Fields)
def magneticTwoForm (B u v : Space) : ℝ := ⟪B, cross u v⟫
theorem magneticTwoForm_flux_surface ... :
    magneticTwoForm (B x) u v = 0

-- PlasmaLean/Kernel/Forms.lean (namespace PlasmaLean.Forms; added 16 November 2026)
def flux : Euclid3 ≃ₗ[ℝ] Form 2            -- v ↦ ι_v vol, with explicit inverse
theorem extDeriv_flux (B : Euclid3 → Euclid3) (x : Euclid3) :
    extDeriv (fun y => flux (B y)) x = density (fieldDiv B x)   -- dω_B = (∇ · B) vol

-- PlasmaLean/Theory/Fields/FormBridges.lean (namespace PlasmaLean.Forms)
theorem flux_apply_eq_magneticTwoForm (B u v : Space) :
    flux B ![u, v] = magneticTwoForm B u v

-- Not in the library: differential forms on a manifold other than ℝ³.

-- Vector potential on a star-convex region (TauCeti's Poincaré lemma; 23 November 2026):
-- PlasmaLean/Theory/Fields/FormCalculus.lean (namespace PlasmaLean.Forms)
theorem VacuumForm.exists_vectorPotential (h : VacuumForm Ω ω) (hs : StarConvex ℝ x₀ Ω) :
    ∃ A : Space → Form 1, ContDiffOn ℝ 2 A Ω ∧ A x₀ = 0 ∧ ∀ x ∈ Ω, extDeriv A x = ω x
theorem VacuumField.exists_vectorPotential ... : ∃ A, A x₀ = 0 ∧ ∀ x ∈ Ω, B x = fieldCurl A x
-- Only dω = 0 is used, but the statement is made for vacuum fields.
```

## Magnetic field lines as a Hamiltonian system; Poincaré sections

*Symplectic Geometry & Dynamical Systems.* Field lines of a divergence-free field behave like trajectories of a Hamiltonian system with one and a half degrees of freedom, the toroidal angle playing the role of time. Poincaré plots show surfaces, island chains and chaotic regions.

**Geometry.** Field lines are the characteristic foliation (the kernel) of the closed 2-form ω_B = ι_B vol = dα. On a cross-section Σ transverse to B, ω_B restricts to an area form and the first-return map preserves it (an exact symplectic twist map when α is single valued and the shear is nonzero). Equivalently, field lines are the extremals of the action ∫ α (Cary–Littlejohn), so Noether's theorem, KAM theory and Aubry–Mather theory apply to them.

**Sources.** Cary & Littlejohn, Ann. Phys. 151 (1983) 1; Boozer, Rev. Mod. Phys. 76 (2004) 1071; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150; Meiss, Rev. Mod. Phys. 64 (1992) 795.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Fields/InvariantBarrier.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/InvariantBarrier.lean).

```lean
-- Field lines as solutions of an ODE, and invariant regions:
-- PlasmaLean/Theory/Fields/InvariantBarrier.lean (namespace PlasmaLean.Fields)
def IsFieldLine (B : Space → Space) (γ : ℝ → Space) : Prop :=
  ∀ t, HasDerivAt γ (B (γ t)) t
theorem invariantBarrier_forever ... (hγ : IsFieldLine B γ) (h0 : γ 0 ∈ Ω) :
    ∀ t, γ t ∈ Ω

-- PlasmaLean/Theory/Fields/FirstIntegral.lean
def FieldLineConfined (B : Space → Space) (S : Set Space) : Prop :=
  ∀ γ : ℝ → Space, IsForwardFieldLine B γ → γ 0 ∈ S → ∀ t, 0 ≤ t → γ t ∈ S

-- PlasmaLean/Theory/Fields/FieldLineExistence.lean (namespace PlasmaLean.Fields.ODEGlobal)
theorem exists_global ... : ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t

-- Not in the library: the return map on a section and its area preservation,
-- the field-line action principle.
```

## Vacuum magnetic field (∇ · B = 0, ∇ × B = 0)

*Differential & Complex Geometry.* The field in a current-free region (J = 0), produced by external coil currents.

**Geometry.** A harmonic field: the 1-form β = B♭ is closed and co-closed (dβ = 0, d⋆β = 0); equivalently the flux 2-form ω = ⋆β is closed and co-closed. Locally β = dΦ with ΔΦ = 0. On a compact domain M with B tangent to the boundary, the Hodge–Morrey–Friedrichs decomposition identifies such fields with H¹_dR(M; ℝ): dimension 1 for a solid torus (the field of a current along the hole), 0 for a ball.

**Sources.** Cantarella, DeTurck & Gluck, Amer. Math. Monthly 109 (2002) 409; Schwarz, Hodge Decomposition (Springer LNM 1607, 1995); Dommaschk, Comput. Phys. Commun. 40 (1986) 203; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

**Lean status: In the library.** Module: [`PlasmaLean/Kernel/Vacuum.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Vacuum.lean).

```lean
-- PlasmaLean/Kernel/Vacuum.lean (kernel law, namespace PlasmaLean.Vacuum)
structure VacuumField (Ω : Set Euclid3) (B : Euclid3 → Euclid3) : Prop where
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 2 B Ω
  div_eq_zero : ∀ x ∈ Ω, fieldDiv B x = 0
  curl_eq_zero : ∀ x ∈ Ω, fieldCurl B x = 0

-- Audit V-1: VacuumField ∅ B holds for every B (Sanity/AuditVacuum.vacuumField_empty).

-- The same law in form language, for the flux 2-form ω = ι_B vol (β = ⋆ω):
-- PlasmaLean/Kernel/Forms.lean (kernel file, namespace PlasmaLean.Forms; 16 November 2026)
structure VacuumForm (Ω : Set Euclid3) (ω : Euclid3 → Form 2) : Prop where
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 2 ω Ω
  closed : ∀ x ∈ Ω, extDeriv ω x = 0                              -- Gauss
  coclosed : ∀ x ∈ Ω, extDeriv (fun y => hodge (ω y)) x = 0       -- Ampère, J = 0
theorem vacuumForm_flux_iff : VacuumForm Ω (fluxField B) ↔ VacuumField Ω B
theorem vacuumField_fluxSymm_iff : VacuumField Ω (fluxField.symm ω) ↔ VacuumForm Ω ω

-- Harmonic potentials in cylindrical coordinates (Dommaschk-type):
-- PlasmaLean/Theory/Fields/CylAlgebra.lean (namespace PlasmaLean.Fields.CylAlgebra)
theorem gradField_vacuum {f : CylPoly} (h : nf (lap f) = []) :
    VacuumField domain (gradField f)

-- Not in the library: boundary conditions, Hodge decomposition, de Rham cohomology.

-- Potentials and topology (23 November 2026; TauCeti v4.36.0):
-- PlasmaLean/Theory/Fields/FormCalculus.lean: star-convex regions (Poincaré lemma)
theorem VacuumField.exists_scalarPotential (h : VacuumField Ω B) (hs : StarConvex ℝ x₀ Ω) :
    ∃ φ : Space → ℝ, ContDiffOn ℝ 2 φ Ω ∧ φ x₀ = 0 ∧ ∀ x ∈ Ω, B x = gradient φ x
-- PlasmaLean/Theory/Fields/FormTopology.lean: the bridge to forms on the manifold U
def onOpens (U : Opens Space) (β : Space → Form k) : RoughForm 𝓘(ℝ, Space) U ℝ k
theorem VacuumField.exists_scalarPotential_of_simplyConnected [SimplyConnectedSpace U]
    (h : VacuumField U B) : ∃ φ, ContDiffOn ℝ 2 φ U ∧ ∀ x ∈ U, B x = gradient φ x
-- PlasmaLean/Sanity/FormTopology.lean: the field of a straight wire has no potential,
-- so the complement of a line is not simply connected
theorem wireField_no_potential : ¬ ∃ φ, DifferentiableOn ℝ φ wireRegion ∧
    ∀ x ∈ wireRegion, wireField x = gradient φ x
theorem wireRegion_not_simplyConnected : ¬ SimplyConnectedSpace wireOpens
-- A region that is simply connected but not star-convex about any point (below z = x²):
theorem bentSet_not_starConvex (c : Space) : ¬ StarConvex ℝ c bentSet
theorem hyperbolic_scalarPotential_bent : ∃ φ, ContDiffOn ℝ 2 φ bentSet ∧
    ∀ x ∈ bentSet, hyperbolicField x = gradient φ x
-- Not in Lean: H¹_dR of a solid torus, the Hodge–Morrey–Friedrichs decomposition.

-- The anti-self-dual lift to ℝ³ × ℝ (23 November 2026):
-- PlasmaLean/Theory/Fields/FormHYMLift.lean (namespace PlasmaLean.Forms)
def hymLift (w : Space → Form 2) (p : Space × ℝ) : (Space × ℝ) [⋀^Fin 2]→L[ℝ] ℝ
  -- ℱ = π^*ω − π^*(⋆ω) ∧ dτ, independent of τ
theorem extDeriv_hymLift_eq_zero_iff (w : Space → Form 2) (x : Space) (τ : ℝ) :
    extDeriv (hymLift w) (x, τ) = 0 ↔
      extDeriv w x = 0 ∧ extDeriv (fun y => hodge (w y)) x = 0
theorem hymLift_closed_iff_vacuumField (hΩ : IsOpen Ω) (hB : ContDiffOn ℝ 2 B Ω) :
    (∀ p ∈ Ω ×ˢ Set.univ, extDeriv (hymLift (fluxField B)) p = 0) ↔ VacuumField Ω B
theorem hymLift_isAntiSelfDual (w : Space → Form 2) (p : Space × ℝ) :
    IsAntiSelfDual (hymLift w p)        -- ℱ(eᵢ, e_τ) = −ℱ(eⱼ, eₖ), written in components
-- The Hodge star on 2-forms of ℝ³ × ℝ (PlasmaLean/Theory/Fields/FormHYMStar.lean):
def liftStar : LiftForm 2 ≃ₗ[ℝ] LiftForm 2     -- ⋆(π^*a + π^*e ∧ dτ) = π^*(⋆⁻¹e) + π^*(⋆a) ∧ dτ
theorem euclidForm_liftStar (F : LiftForm 2) :
    euclidForm (liftStar F) = liftOrientation.formHodgeStar _ (euclidForm F)  -- TauCeti's star
theorem isAntiSelfDual_iff_liftStar (F : LiftForm 2) : IsAntiSelfDual F ↔ liftStar F = -F
theorem liftStar_eq_neg_iff_exists (F : LiftForm 2) :
    liftStar F = -F ↔ ∃ b : Form 2, F = hymLiftAt b     -- every anti-self-dual form is a lift
theorem isCompl_selfDualForms_antiSelfDualForms : IsCompl selfDualForms antiSelfDualForms
def hymLiftCircle (ℓ : ℝ) (w : Space → Form 2) (p : Space × AddCircle ℓ) : LiftForm 2
theorem mpullback_hymLiftCircleForm ... : pullback along Space × ℝ → Space × AddCircle ℓ
    of the form on the circle product is hymLift w
-- On the manifold Ω × S¹ (PlasmaLean/Theory/Fields/FormHYMCircle.lean):
theorem isSmoothForm_hymLiftCircleForm_iff (w : Space → Form 2) :
    IsSmoothForm _ n (hymLiftCircleForm ℓ w) ↔ ContDiff ℝ n w
theorem hymLiftRegionForm_closed_iff_vacuumField (U : Opens Space) (hB : ContDiffOn ℝ 2 B U) :
    mextDeriv (hymLiftRegionForm ℓ U (fluxField B)) = 0 ↔ VacuumField U B
theorem integral_liftInner_hymLiftCircle (B : Space → Space) (Ω : Set Space) :
    ∫ p in Ω ×ˢ univ, liftInner (hymLiftCircle ℓ (fluxField B) p) (...) = 2 * ℓ * ∫ x in Ω, ‖B x‖ ^ 2

-- PlasmaLean/Theory/Fields/FormHYMComplex.lean   (J(u, s) = (n × u − s n, ⟪n, u⟫), ‖n‖ = 1)
theorem liftStar_eq_neg_iff_isType11_and_isPrimitive (hn : ‖n‖ = 1) (F : LiftForm 2) :
    liftStar F = -F ↔ IsType11 n F ∧ IsPrimitive n F
theorem isType11_and_isPrimitive_hymLift ...   -- the lift is (1,1) and primitive
theorem VacuumForm.hymLiftRegionForm_closed ...  -- closed on U × S¹, no regularity hypothesis

-- PlasmaLean/Theory/Fields/FormHYMEnergy.lean   (a : C¹ 1-form, compact support in Ω × ℝ)
theorem VacuumForm.integral_energy_hymLift_perturbation (h : VacuumForm Ω w) ... :
    ∫ p, (liftInner (ℱ p + extDeriv a p) (ℱ p + extDeriv a p) - liftInner (ℱ p) (ℱ p)) =
      ∫ p, liftInner (extDeriv a p) (extDeriv a p)        -- ≥ 0, and = 0 iff da = 0
theorem VacuumForm.exists_liftConnection (h : VacuumForm Ω w) (hs : StarConvex ℝ x₀ Ω) :
    ∃ A φ, ... ∀ x ∈ Ω, ∀ τ, extDeriv (liftConnection A φ) (x, τ) = hymLift w (x, τ)
-- Not in Lean: the line bundle and its Chern class; the energy statement on Ω × S¹
-- (TauCeti has no bundle-from-curvature construction or Chern class).
```

## Net toroidal current, Ampère's law and the current-free condition (contract clause C1)

*Topology (de Rham periods).* The current through a surface equals the circulation of B around its edge divided by μ₀. A stellarator needs rotational transform with zero (or small) net toroidal plasma current; a tokamak does not have it.

**Geometry.** μ₀ I(S) = ∫_S dβ = ∮_∂S β for β = B♭ (Stokes). In a current-free region β is closed, and its periods over the cycles of a flux torus are topological invariants: μ₀ I_tor over the poloidal cycle and μ₀ I_pol over the toroidal cycle (Boozer's I and G). Zero net toroidal current says the period of β over every poloidal loop vanishes. A purely toroidal (axisymmetric, current-free) field has ι = 0, so ι ≠ 0 at I_tor = 0 forces a non-axisymmetric field.

**Sources.** Cantarella, DeTurck & Gluck, Amer. Math. Monthly 109 (2002) 409; Helander, Rep. Prog. Phys. 77 (2014) 087001; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Contract/StellaratorContract.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Contract/StellaratorContract.lean).

```lean
-- PlasmaLean/Theory/Contract/StellaratorContract.lean (namespace PlasmaLean.Contract)
def lineIntegral (B : Space → Space) (γ : ℝ → Space) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ⟪B (γ t), deriv γ t⟫
def loopCurrent (μ₀ : ℝ) (B : Space → Space) (R z : ℝ → ℝ → ℝ) (φ₀ : ℝ) : ℝ :=
  poloidalCirculation B R z φ₀ / μ₀
structure CurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (S : Set SurfaceData)
    (Imax ιmin : ℝ) : Prop where ...
  torus : ∀ s ∈ S, IotaOnTorus B s.R s.z s.iota
  current_le : ∀ s ∈ S, |s.current μ₀ B| ≤ Imax
  iota_ge : ∀ s ∈ S, ιmin ≤ |s.iota|
theorem not_currentFreeTransform_of_purelyToroidal ...

-- Stokes on a poloidal section:
-- PlasmaLean/Theory/Contract/SectionStokes.lean
theorem netToroidalCurrent_eq_loopCurrent ... :
    netToroidalCurrent μ₀ B X ζ₀ k₀ = loopCurrent μ₀ B R z φ₀

-- PlasmaLean/Design/RationalStellaratorContract.lean
theorem rationalStellarator_currentFreeTransform {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData, CurrentFreeTransform μ₀ (field (1 / 4)) S 0 iota

-- Not in the library: de Rham cohomology classes; periods are defined loop by loop.

-- 23 November 2026: closed 1-forms on an open region can now be passed to TauCeti's de Rham
-- theory through PlasmaLean.Forms.onOpens (Theory/Fields/FormTopology), and the circulation is
-- a de Rham period:
-- PlasmaLean/Theory/Fields/FormPeriods.lean (namespace PlasmaLean.Forms)
theorem pathIntegral_onOpens_flat (U : Opens Space) (B : Space → Space) (c : ℝ → U) (a b : ℝ) :
    TauCeti.pathIntegral (onOpens U fun y => flat (B y)) c a b
      = lineIntegral B (fun t => (c t : Space)) a b
theorem periodHom_onOpens_flat (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hc : ContDiff ℝ 1 fun t => (c t : Space)) (hγ : ∀ t : unitInterval, γ t = c t) :
    TauCeti.periodHom (onOpens U fun y => flat (B y)) x (class of γ)
      = lineIntegral B (fun t => (c t : Space)) 0 1
-- PlasmaLean/Sanity/FormPeriods.lean: the wire field has period 2π on the unit circle
theorem wire_period : periodHom (onOpens wireOpens fun y => flat (wireField y)) (wireLoop 0)
    (class of the unit circle) = 2 * Real.pi
-- The contract's loop current is a period (PlasmaLean/Theory/Fields/FormLoopCurrent.lean):
theorem lineIntegral_comp_affine (B : Space → Space) (γ : ℝ → Space) (a b : ℝ) :
    lineIntegral B (fun t => γ (a + (b - a) * t)) 0 1 = lineIntegral B γ a b
theorem loopCurrent_eq_periodHom_div (μ₀ : ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ π = poloidalLoop R z φ₀ (-π)) :
    loopCurrent μ₀ B R z φ₀ = periodHom (onOpens U fun y => flat (B y)) _ (loop class) / μ₀
-- Topology forces zero net current:
theorem VacuumField.loopCurrent_eq_zero_of_simplyConnected [SimplyConnectedSpace U] (μ₀ : ℝ)
    (h : VacuumField U B) ... : loopCurrent μ₀ B R z φ₀ = 0

-- Loops that are C¹ only on [-π, π], and the contract's own structures
-- (PlasmaLean/Theory/Fields/FormLoopCurrentInterval.lean):
theorem lineIntegral_eq_periodHom (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hclosed : γ a = γ b) : lineIntegral B γ a b = periodHom (onOpens U ...) _ (loop class)
theorem CurrentFreeTransform.current_eq_zero_of_simplyConnected [SimplyConnectedSpace U]
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField U B) (hs : s ∈ S)
    (hU : ∀ θ ∈ Set.Icc (-π) π, s.loop θ ∈ U) : s.current μ₀ B = 0
-- Sanity: a poloidal loop around a straight wire has circulation and period 2π
-- (ring_poloidalCirculation, ring_period); the wire's complement is not simply connected.

-- Piecewise C¹ loops and polygons (PlasmaLean/Theory/Fields/FormPiecewisePeriod.lean):
theorem lineIntegral_eq_periodHom_piecewise (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (h : PiecewiseC1In U γ t n)
    (hclosed : γ (t 0) = γ (t n)) :
    lineIntegral B γ (t 0) (t n) = periodHom (onOpens U ...) _ (chainLoop h hclosed)
theorem sum_lineIntegral_segCurve_eq_periodHom ... :   -- closed polygons with edges in U
    ∑ i ∈ Finset.range n, lineIntegral B (segCurve (p i) (p (i + 1))) 0 1 = periodHom ...
-- Sanity: a square around the wire has circulation and period 2π (square_period).

-- The current allowance is 0 for fields that are vacuum on the meridian half-space (Stokes on
-- the planar cross-section; this excludes coil fields, whose coils lie in every half-space)
-- (PlasmaLean/Theory/Fields/FormConvexRegion.lean): a poloidal loop at angle φ₀ with R > 0
-- lies in the convex half-space meridianHalfSpace φ₀, which misses the z-axis.
theorem CurrentFreeTransform.imax_zero_of_meridianHalfSpace
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField Ω B)
    (hΩ : ∀ s ∈ S, (meridianHalfSpace s.φ₀ : Set Space) ⊆ Ω) :
    CurrentFreeTransform μ₀ B S 0 ιmin
-- The clause is assumed; only the allowance improves. Fixture with ι > 0 (a consistency
-- check: its source instance already had allowance 0): rationalStellarator_fixture.

-- PlasmaLean/Design/DommaschkKamLoopCurrent.lean   (on demand)
theorem exists_fieldTorus_loopCurrent_eq_zero ...   -- the two KAM tori of the Dommaschk
-- candidate, ι ≠ 0: loop current 0 by the topological route (second proof of a known fact)

-- PlasmaLean/Theory/Fields/FormFluxSurfacePeriods.lean   (C² surface; B C¹, curl-free near it)
theorem FieldTorus.poloidalCirculation_eq_of_curl_eq_zero ... (φ₀ φ₁ : ℝ) :
    poloidalCirculation B R z φ₀ = poloidalCirculation B R z φ₁
theorem PeriodicC2Torus.exists_periodic_potential_of_curl_eq_zero ... :
    ∃ g, (doubly 2π-periodic) ∧ ∀ p, HasFDerivAt g (torusForm B R z p
      - (poloidalPeriod B R z φ₀ / (2 * π)) • fst - (toroidalPeriod B R z θ₀ / (2 * π)) • snd) p
-- The class of B♭ on the surface is (P_θ/2π)[dθ] + (P_φ/2π)[dφ], stated on the parameter plane.
```

## Magnetic well and min-B: |B| in a vacuum field

*Differential Geometry (harmonic fields).* Stability and trapped-particle confinement favour a minimum of the field strength inside the plasma. In a vacuum region |B| can have an interior minimum but never an interior maximum.

**Geometry.** For a harmonic field in flat space the Bochner identity gives Δ|B|² = 2|∇B|² ≥ 0: |B|² is subharmonic and obeys the maximum principle. So |B| has no strict interior maximum, while strict interior minima exist. In vacuum the field-line curvature is κ = ∇_⊥ ln|B|, which obstructs |B| from being a local minimum at every point of a closed field line.

**Sources.** Bochner, Bull. Amer. Math. Soc. 52 (1946) 776; Helander, Rep. Prog. Phys. 77 (2014) 087001; PlasmaLean note N-1 (notes/theory/toroidal-min-b-obstruction.md).

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/Subharmonic.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/Subharmonic.lean).

```lean
-- PlasmaLean/Theory/Fields/Subharmonic.lean (namespace PlasmaLean.Vacuum)
theorem laplacian_normSqField_nonneg {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) : 0 ≤ Δ (normSqField B) x
theorem VacuumField.not_strict_local_max_normSq (hB : VacuumField Ω B) (hx : x ∈ Ω) :
    ¬ ∀ᶠ y in 𝓝[≠] x, normSqField B y < normSqField B x
theorem exists_vacuum_strict_interior_min ...

-- PlasmaLean/Theory/Fields/CurvatureObstruction.lean
theorem VacuumField.not_closed_fieldLine_minB (hV : VacuumField Ω B) ...
    (closed : γ T = γ 0) : ¬ ∀ s ∈ Icc 0 T, IsLocalMin (fun y => ‖B y‖) (γ s)

-- Not in the library: the magnetic well V″(ψ) of a toroidal equilibrium as a
-- geometric quantity (it is supplied data in MercierSurfaceData).
```

## Rotational transform ι and safety factor q = 1/ι

*Topology & Dynamical Systems.* Average number of poloidal turns of a field line per toroidal turn on a flux surface. A current-free axisymmetric field has ι = 0; a stellarator gets ι > 0 from the 3-D shape of the external field.

**Geometry.** On an invariant torus on which the field-line flow is conjugate to a linear flow (θ, φ) ↦ (θ + ιt, φ + t), ι is the slope; in general it is the Poincaré rotation number of the circle map induced by the return map, i.e. the asymptotic poloidal winding per toroidal turn. For nested surfaces ι = dΨ_pol/dΨ_tor, a ratio of periods of ω_B. A Diophantine ι supports KAM persistence; a rational ι = n/m permits island chains. With zero net toroidal current, ι ≠ 0 requires a non-axisymmetric field.

**Sources.** Boozer, Rev. Mod. Phys. 76 (2004) 1071; Cary & Littlejohn, Ann. Phys. 151 (1983) 1; Helander, Rep. Prog. Phys. 77 (2014) 087001; Imbert-Gérard, Paul & Wright, An Introduction to Stellarators (SIAM, 2024), arXiv:1908.05360.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Contract/StellaratorContract.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Contract/StellaratorContract.lean).

```lean
-- PlasmaLean/Theory/Contract/StellaratorContract.lean (namespace PlasmaLean.Contract)
structure FieldTorus (B : Space → Space) (R z : ℝ → ℝ → ℝ) (ι : ℝ) : Prop
  -- (θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ) is doubly periodic and carries the linear
  -- flow (θ + ιt, φ + t) to field lines of B (field `flow`)
def IotaOnTorus (B : Space → Space) (R z : ℝ → ℝ → ℝ) (ι : ℝ) : Prop :=
  FieldTorus B R z ι ∧ ∃ R₀ z₀ : ℝ → ℝ, ∃ Θ : ℝ → ℝ → ℝ, PoloidalAngle R z R₀ z₀ Θ
theorem IotaOnTorus.tendsto (h : IotaOnTorus B R z ι) (θ₀ : ℝ) : ... ∧
    Tendsto (fun s => (Θ (θ₀ + s * ι) s - Θ θ₀ 0) / s) atTop (𝓝 ι)
  -- ι is the asymptotic poloidal winding rate of the field line
theorem iota_eq_zero_of_purelyToroidal ...   -- a purely toroidal field has ι = 0

-- PlasmaLean/Theory/KAM/Diophantine.lean (namespace PlasmaLean.Theory.KAM)
def Diophantine (ω γ : ℝ) (τ : ℕ) : Prop :=
  ∀ k m : ℤ, k ≠ 0 → γ / |(k : ℝ)| ^ τ ≤ |(k : ℝ) * ω - m|

-- Not in the library: the rotation number of a general return map. Mathlib has the
-- translation number of a lifted circle map (CircleDeg1Lift.translationNumber);
-- it is not yet connected to field lines.
```

## Persistence of flux surfaces under perturbation (KAM)

*Topology & Dynamical Systems (KAM).* A non-axisymmetric field has no reason to have flux surfaces everywhere. Surfaces with sufficiently irrational rotational transform survive small perturbations; the others break into islands and chaotic layers.

**Geometry.** An invariant torus is an embedding K : 𝕋² → M whose image is tangent to B and on which the flow is conjugate to a linear one: DK · (ι ∂_θ + ∂_φ) is parallel to B ∘ K. For Diophantine ι and nonzero twist (shear), the linearized equation reduces to a cohomological equation over the rotation, solvable with a loss δ of analyticity width (Rüssmann estimate), and a Newton iteration converges. In a-posteriori form: an approximately invariant torus with small enough error is close to a true one.

**Sources.** Kolmogorov, Dokl. Akad. Nauk SSSR 98 (1954) 527; Moser, Nachr. Akad. Wiss. Göttingen II (1962) 1; Rüssmann, Lecture Notes in Physics 38 (1975) 598; de la Llave, González, Jorba & Villanueva, Nonlinearity 18 (2005) 855.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/KAM/KamSequence.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/KAM/KamSequence.lean).

```lean
-- Small divisors and the cohomological equation:
-- PlasmaLean/Theory/KAM/Cohomological.lean (namespace PlasmaLean.Theory.KAM)
theorem cohSol_estimate (hD : Diophantine ω γ τ) (hγ : 0 < γ) (hδ : 0 < δ)
    {f : ℤ × ℤ → ℂ} (hf : InWeighted r f) :
    InWeighted (r - δ) (cohSol ω f) ∧
      wnorm (r - δ) (cohSol ω f) ≤ russmannConst γ δ τ * wnorm r f

-- Quadratic convergence of the Newton errors:
-- PlasmaLean/Theory/KAM/KamSequence.lean
theorem kam_sequence ... (hrec : ∀ j, e (j + 1) ≤ κ * e j ^ 2 / kamDelta δ₀ j ^ 4)
    (hsmall : 32 * κ * e 0 / δ₀ ^ 4 ≤ 1) : ... ∧ Tendsto e atTop (𝓝 0) ∧ ...

-- A-posteriori theorem for polynomial field data in cylindrical coordinates:
-- PlasmaLean/Design/KamFlowIteration.lean (namespace PlasmaLean.Design.KamNewton)
theorem FlowField.KamH.kam_flow_torus (K : F.KamH c ι u₀ z₀ e₀ μ) : ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
    F.resR ι u z = 0 ∧ F.resZ ι u z = 0 ∧ Close (rInf c) ι u z u₀ z₀ μ

-- PlasmaLean/Design/RationalStellaratorFieldLines.lean
theorem rationalStellarator_confined_forever_exists : ...
-- (field lines inside a certified torus of an exact vacuum field stay inside for all time)

-- Not in the library: a KAM theorem for general smooth fields; island chains.
```

## Stellarator symmetry

*Topology & Dynamical Systems (reversing symmetry).* Most stellarator designs are invariant under a half-turn about a horizontal axis combined with reversal of the field direction. It halves the Fourier data of the boundary and of the field.

**Geometry.** An involution S of space, the rotation by π about a line through the axis of the torus, in cylindrical terms (R, φ, z) ↦ (R, −φ, −z), with S_* B = −B. It is a reversing (time-reversal) symmetry of the field-line flow: S maps field lines to field lines traversed backwards, and maps flux surfaces to flux surfaces. It is a discrete ℤ₂ symmetry, compatible with having no continuous symmetry.

**Sources.** Dewar & Hudson, Physica D 112 (1998) 275; Lamb & Roberts, Physica D 112 (1998) 1.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Fields/CylAlgebra.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/CylAlgebra.lean).

```lean
-- PlasmaLean/Theory/Fields/CylAlgebra.lean (namespace PlasmaLean.Fields.CylAlgebra)
def stellRefl (y : Space) : Space := toLp 2 ![y 0, -y 1, -y 2]
theorem gradField_stellRefl {f : CylPoly} (h : parityCheck 1 f = true) (y : Space) :
    gradField f (stellRefl y) = -stellRefl (gradField f y)

-- Not in the library: consequences for the return map (symmetric periodic orbits).
```

## Magnetohydrostatic (MHS) equilibrium (J × B = ∇p)

*Differential & Symplectic Geometry.* Static force balance: the Lorentz force balances the pressure gradient.

**Geometry.** With ω_B = ι_B vol, β = B♭ and current 2-form ω_J = dβ/μ₀, force balance reads ι_B ω_J = dp. Hence dp(B) = dp(J) = 0 and, where dp ≠ 0, [B, J] = 0: B and J are commuting fields tangent to the level sets of p (Arnold). When dp = 0 and J is parallel to B it reduces to a Beltrami field dβ = λ⋆β. Equilibria are the critical points of the energy ∫(|B|²/2μ₀ − p) under ideal (flux-preserving) variations (Kruskal–Kulsrud).

**Sources.** Arnold, Ann. Inst. Fourier 16 (1966) 319; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998); Kruskal & Kulsrud, Phys. Fluids 1 (1958) 265; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

**Lean status: In the library.** Module: [`PlasmaLean/Kernel/Equilibrium.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Kernel/Equilibrium.lean).

```lean
-- PlasmaLean/Kernel/Equilibrium.lean (kernel law, namespace PlasmaLean)
class ForceBalance (B J g : Vec3) : Prop where
  balance : J ⨯₃ B = g

theorem field_tangency (B J g : Vec3) [ForceBalance B J g] : B ⬝ᵥ g = 0

-- g is supplied data. Audit E-1: ForceBalance B J (J ⨯₃ B) holds for any B, J,
-- so a claim must also prove g = ∇p and J = (∇ × B)/μ₀, e.g.
-- PlasmaLean/Design/ForceBalanceGradient.lean: solovev_force_balance_gradient

-- The same law in form language (ω_B, ω_J flux 2-forms, dp a 1-form): ι_B ω_J = dp.
-- PlasmaLean/Kernel/Forms.lean (kernel file, namespace PlasmaLean.Forms; 16 November 2026)
class FormForceBalance (ωB ωJ : Form 2) (dp : Form 1) : Prop where
  balance : ωJ.curryLeft (flux.symm ωB) = dp
theorem formForceBalance_iff :
    FormForceBalance (flux (vec B)) (flux (vec J)) (flat (vec g)) ↔ ForceBalance B J g
```

## Existence of three-dimensional equilibria: Arnold's structure theorem and Grad's conjecture

*Topology & Foliations.* Do smooth toroidal equilibria with nested flux surfaces and a pressure gradient exist without a continuous symmetry? Grad conjectured that they do not; counterexamples were found in 2026.

**Geometry.** Arnold: for a smooth equilibrium whose B and J are not everywhere parallel, the compact regular level sets of p are tori, B and J commute on them, and B is conjugate to a linear flow on each. Known existence results: axisymmetric and helical families (Grad–Shafranov); tori near axisymmetry with stepped pressure (Bruno–Laurence); piecewise-smooth equilibria in toroidal domains far from symmetry (Enciso–Luque–Peralta-Salas); and a generalized Grad–Shafranov equation expressing a hidden symmetry of smooth equilibria (Burby–Kallinikos–MacKay). Grad's conjecture is now disproved: smooth equilibria on solid tori whose Euclidean symmetry group is only a finite cyclic group exist (Gómez-Serrano–Liehr–Taylor, 2026, with a Lean certification), and explicit closed-form non-symmetric families are known (Landreman; Issan et al.).

**Sources.** Arnold, Ann. Inst. Fourier 16 (1966) 319; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998); Grad, Phys. Fluids 10 (1967) 137; Bruno & Laurence, Comm. Pure Appl. Math. 49 (1996) 717; Enciso, Luque & Peralta-Salas, J. Eur. Math. Soc. 27 (2025) 2251, arXiv:2104.08149; Burby, Kallinikos & MacKay, Phys. Plasmas 27 (2020) 102504, arXiv:2005.13664; Gómez-Serrano, Liehr & Taylor, arXiv:2609.24739 (2026); Landreman, arXiv:2609.26742 (2026); Issan, José, Landreman, Citrin & Tracey, arXiv:2611.07672 (2026).

**Lean status: In the library.** Module: [`PlasmaLean/Design/LandremanGradCounterexample.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/LandremanGradCounterexample.lean).

```lean
-- An explicit family with nested toroidal level sets and no rotation, translation or
-- screw symmetry (Landreman family 1; it has ι ≡ 2 and net toroidal current):
-- PlasmaLean/Design/LandremanGradCounterexample.lean
theorem family1_grad_counterexample {ε δ μ₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ : δ < (1 - ε) ^ 2 / 4) (hμ : 0 < μ₀) : ...
  -- 1. field, current and pressure are smooth on the domain
  -- 2. divergence-free and ForceBalance with the Ampère current
  -- 3. ψ is a first integral; level sets ≃ₜ Circle × Circle; the axis ≃ₜ Circle
  -- 4. the pressure is not constant
  -- 5. no nonzero Killing field (rotation, translation, screw) preserves the field
-- Scope: plane reflections are not excluded (note N-28). The first Lean-certified
-- counterexample is that of Gómez-Serrano, Liehr and Taylor, in their own repository.

-- Not in the library: Arnold's structure theorem; any general existence theorem.
```

## Force-free (Beltrami) fields: ∇ × B = λB

*Contact Geometry.* With no pressure gradient the current flows along the field. Constant λ gives the relaxed (Taylor) states.

**Geometry.** dβ = λ ⋆β for β = B♭. If B is nowhere zero and λ is nowhere zero, β ∧ dβ = λ|B|² vol ≠ 0: β is a contact form and B is a positive multiple of its Reeb field. Conversely every Reeb field is a Beltrami field for some metric (Etnyre–Ghrist), so contact topology gives theorems about force-free fields, for instance closed field lines on the 3-sphere and on solid tori. Beltrami fields can have field lines of arbitrary knot type and chaotic regions, unlike equilibria with dp ≠ 0.

**Sources.** Etnyre & Ghrist, Nonlinearity 13 (2000) 441, arXiv:dg-ga/9708011; Cardona, Miranda & Peralta-Salas, Phil. Trans. R. Soc. A 377 (2019) 20190034, arXiv:1902.00039; Enciso & Peralta-Salas, Ann. of Math. 175 (2012) 345; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998).

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Fields/FormBridges.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/FormBridges.lean).

```lean
-- PlasmaLean/Theory/Fields/FormBridges.lean (namespace PlasmaLean.Forms)
def IsBeltramiOn (B : Space → Space) (lam : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ B x ∧ fieldCurl B x = lam x • B x
  -- the curl equation only: ∇ · B = 0 is not part of it
def FormBeltramiOn (β : Space → Form 1) (lam : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ β x ∧ extDeriv β x = lam x • hodge.symm (β x)   -- dβ = λ ⋆β
theorem formBeltramiOn_flat_iff :
    FormBeltramiOn (fun x => flat (B x)) lam U ↔ IsBeltramiOn B lam U

def wedge12 (a : Form 1) (b : Form 2) : Form 3 := density ⟪flat.symm a, flux.symm b⟫
theorem wedge12_apply (a : Form 1) (b : Form 2) (u v w : Space) :
    wedge12 a b ![u, v, w] =
      a ![u] * b ![v, w] - a ![v] * b ![u, w] + a ![w] * b ![u, v]
def IsContactAt (β : Space → Form 1) (x : Space) : Prop :=
  wedge12 (β x) (extDeriv β x) ≠ 0                              -- β ∧ dβ ≠ 0
theorem isContactAt_of_beltrami (h : IsBeltramiOn B lam U) (hx : x ∈ U)
    (hl : lam x ≠ 0) (hB : B x ≠ 0) : IsContactAt (fun y => flat (B y)) x
theorem IsBeltramiOn.formForceBalance (h : IsBeltramiOn B lam U) (hx : x ∈ U) :
    FormForceBalance (flux (B x)) (flux (fieldCurl B x)) 0        -- force-free: ι_B ω_J = 0
theorem not_isContactAt_of_vacuumField (hV : VacuumField Ω B) (hx : x ∈ Ω) :
    ¬ IsContactAt (fun y => flat (B y)) x

-- Example: (cos z, sin z, 0), the slab field Equilibrium.helicalSlab on ℝ³
theorem helicalField_beltrami : IsBeltramiOn helicalField (fun _ => -1) Set.univ
theorem helicalField_contact (x : Space) : IsContactAt (fun y => flat (helicalField y)) x

-- PlasmaLean/Kernel/Equilibrium.lean
theorem gradient_zero_iff_force_free (B J g : Vec3) [ForceBalance B J g] :
    g = 0 ↔ J ⨯₃ B = 0

-- Not in the library: the Reeb field; the converse (a metric making a given Reeb
-- field Beltrami); contact topology; three-dimensional toroidal Beltrami fields.

-- Links to TauCeti v4.36.0 (23 November 2026):
-- PlasmaLean/Theory/Fields/FormContact.lean (namespace PlasmaLean.Forms)
theorem wedge12_eq_wedge (a : Form 1) (b : Form 2) :
    wedge12 a b = ContinuousAlternatingMap.wedge a b        -- TauCeti's wedge product
theorem isContactAt_iff_nondegenerate (β : Space → Form 1) (x : Space) :
    IsContactAt β x ↔ β x ≠ 0 ∧ ∀ v, β x ![v] = 0 →
      (∀ w, β x ![w] = 0 → extDeriv β x ![v, w] = 0) → v = 0   -- dβ nondegenerate on ker β
theorem IsBeltramiOn.reeb (h : IsBeltramiOn B lam U) (hx : x ∈ U) (hB : B x ≠ 0) :
    flat (B x) ![(‖B x‖ ^ 2)⁻¹ • B x] = 1 ∧
      (extDeriv (fun y => flat (B y)) x).curryLeft ((‖B x‖ ^ 2)⁻¹ • B x) = 0
theorem IsBeltramiOn.reeb_unique (h : IsBeltramiOn B lam U) (hx : x ∈ U) (hl : lam x ≠ 0)
    (hB : B x ≠ 0) (h1 : flat (B x) ![R] = 1)
    (h2 : (extDeriv (fun y => flat (B y)) x).curryLeft R = 0) : R = (‖B x‖ ^ 2)⁻¹ • B x
-- So for λ ≠ 0 the Reeb vector of β = B♭ is B/|B|².
-- TauCeti's bundled contact forms (PlasmaLean/Theory/Fields/FormContactManifold.lean):
def flatSmoothForm (B : Space → Space) (hB : ContDiff ℝ ∞ B) : SmoothForm 𝓘(ℝ, Space) Space ℝ 1
theorem isContactForm_flatSmoothForm_iff (B : Space → Space) (hB : ContDiff ℝ ∞ B) :
    (flatSmoothForm B hB).IsContactForm ↔ ∀ x, IsContactAt (fun y => flat (B y)) x
theorem IsBeltramiOn.reebVectorField_flatSmoothForm (h : IsBeltramiOn B lam Set.univ)
    (hB : ContDiff ℝ ∞ B) (hl : ∀ x, lam x ≠ 0) (hne : ∀ x, B x ≠ 0) (x : Space) :
    (flatSmoothForm B hB).reebVectorField x = (‖B x‖ ^ 2)⁻¹ • B x
-- On an open subset U (PlasmaLean/Theory/Fields/FormContactOpens.lean):
theorem isContactForm_flatSmoothFormOn_iff (U : Opens Space) (B : Space → Space)
    (hB : ContDiffOn ℝ ∞ B U) :
    (flatSmoothFormOn U B hB).IsContactForm ↔ ∀ x ∈ U, IsContactAt (fun y => flat (B y)) x
theorem IsBeltramiOn.reebVectorField_flatSmoothFormOn ... (x : U) :
    (flatSmoothFormOn U B hB).reebVectorField x = (‖B x‖ ^ 2)⁻¹ • B x
-- Sanity: (0, x²/2, 1) is a contact form on the half-space x > 0 and not on ℝ³.
```

## Magnetic helicity and Taylor relaxation

*Topology (linking) & Contact Geometry.* Helicity measures the linkage of magnetic flux. It is conserved by ideal MHD and approximately conserved during turbulent relaxation, which drives the plasma to a force-free state.

**Geometry.** H = ∫ α ∧ dα where ω_B = dα (gauge invariant when B is tangent to the boundary; relative helicity otherwise). It is the asymptotic Hopf invariant: the average asymptotic linking number of pairs of field lines (Arnold), and for thin flux tubes the sum of linking numbers weighted by fluxes (Moffatt). It is invariant under volume-preserving diffeomorphisms and bounds the energy from below. Minimizing energy at fixed helicity gives Beltrami fields (Woltjer; Taylor).

**Sources.** Woltjer, Proc. Natl. Acad. Sci. 44 (1958) 489; Moffatt, J. Fluid Mech. 35 (1969) 117; Arnold, Sel. Math. Sov. 5 (1986) 327; Taylor, Phys. Rev. Lett. 33 (1974) 1139; Cantarella, DeTurck & Gluck, J. Math. Phys. 42 (2001) 876; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998).

**Lean status: Not in the library: illustrative sketch.**

```lean
-- Illustrative sketch, not in the library (proposed signature):
def helicity (A B : Space → Space) (Ω : Set Space) : ℝ := ∫ x in Ω, ⟪A x, B x⟫
theorem helicity_gauge_invariant ...   -- B tangent to ∂Ω, Ω simply connected

-- In the library there are only the algebraic cross-helicity identity and, for Sullivan's
-- finite-dimensional Eulerian ODEs, EulerianODE.helicity_conserved (Theory/Fluids/EulerianODE);
-- the cross-helicity identity is
-- (PlasmaLean/Theory/Stability/Elsasser.lean: cross_helicity_identity). Since 23 November 2026
-- a vector potential exists for vacuum fields on star-convex regions
-- (Theory/Fields/FormCalculus: VacuumForm.exists_vectorPotential); the helicity integral
-- itself is still not defined.
```

## Ideal MHD: frozen-in flux

*Differential Geometry (Lie transport).* In a perfectly conducting plasma the field lines move with the fluid. Field-line topology cannot change without resistivity.

**Geometry.** The ideal induction equation is ∂_t ω_B + ℒ_v ω_B = 0: the flux 2-form is transported by the flow. Hence fluxes through co-moving surfaces, the field-line foliation and the helicity are conserved (Alfvén). The dynamics is Lie–Poisson (Morrison–Greene); an equilibrium is a critical point of the energy on the orbit of ω_B under the flow maps, and the energy principle is the second variation there.

**Sources.** Alfvén, Nature 150 (1942) 405; Morrison & Greene, Phys. Rev. Lett. 45 (1980) 790; Holm, Marsden, Ratiu & Weinstein, Phys. Rep. 123 (1985) 1; Arnold & Khesin, Topological Methods in Hydrodynamics (Springer, 1998).

**Lean status: Not in the library: illustrative sketch.**

```lean
-- Illustrative sketch, not in the library (proposed signature; lieDerivForm is
-- TauCeti.lieDerivForm, Form is PlasmaLean.Forms.Form):
def FrozenIn (v : ℝ → Space → Space) (ω : ℝ → Space → Form 2) : Prop :=
  ∀ t x, deriv (fun s => ω s x) t + lieDerivForm (v t) (ω t) x = 0

-- In the library, adjacent only: abstract Elsässer identities
-- (PlasmaLean/Theory/Stability/Elsasser.lean) and the abstract conserved energy
-- (PlasmaLean/Theory/Stability/AbstractEnergy.lean: energy_conserved).
-- There is no time-dependent MHD model.

-- 23 November 2026: TauCeti v4.36.0 has the Lie derivative of forms on a normed space
-- (TauCeti.lieDerivForm, Cartan's formula) and the flow formula
-- ∂ₜ(ψₜ^* ωₜ) = ψₜ^*(∂ₜωₜ + L_X ωₜ)
-- (TauCeti.compContinuousLinearMap_fderiv_eq_of_deriv_add_lieDerivForm_eq_zero).
-- The frozen-in law ∂ₜω_B + L_v ω_B = 0 can be stated with them; it is not yet in the library.
```

## Boozer coordinates (ψ, θ_B, φ_B)

*Differential Geometry.* Flux coordinates in which field lines are straight and the covariant representation of B has surface-function coefficients.

**Geometry.** A chart adapted to the foliation by ψ in which ω_B = dψ ∧ (dθ_B − ι(ψ) dφ_B) (straight field lines: B is linearized on every torus) and β = I(ψ) dθ_B + G(ψ) dφ_B + ν dψ (the tangential part of β has constant coefficients on each torus). Existence on one invariant torus is a linearization problem for two commuting fields; for a divergence-free field tangent to a torus it holds when the winding is Diophantine or when a second commuting field (such as J) is available. Near the axis the charts are a normal form at an elliptic closed orbit.

**Sources.** Boozer, Phys. Fluids 24 (1981) 1999; Hamada, Nucl. Fusion 2 (1962) 23; Perrella, Pfefferlé & Stoyanov, Partial Differ. Equ. Appl. 3 (2022), doi:10.1007/s42985-022-00182-3, arXiv:2203.04137; Burby, Duignan & Meiss, J. Math. Phys. 62 (2021) 122901, arXiv:2103.02888.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Contract/BoozerModel.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Contract/BoozerModel.lean).

```lean
-- The definition of a Boozer chart is in the library; an existence theorem is not.
-- PlasmaLean/Theory/Contract/BoozerModel.lean (namespace PlasmaLean.Contract)
structure BoozerChart (B : Space → Space) (Ω : Set Space) (c : ℝ) (F : BoozerField)
  -- x : ℝ × ℝ × ℝ → Space, periodic in θ and φ, injective modulo the periods,
  -- nonzero Jacobian, image Ω; `contra`: chartJac • B = ι • ∂_θ x + ∂_φ x;
  -- `cov_psi`, `cov_theta`, `cov_phi`: the covariant components; `modB`: |B| = F.B
def BoozerModelOf (B : Space → Space) (Ω : Set Space) (c : ℝ) (F : BoozerField) : Prop :=
  Nonempty (BoozerChart B Ω c F)

-- The field data used by the guiding-centre model:
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

**Geometry.** A nonvanishing vector field u with ℒ_u ω_B = 0, div u = 0 and ℒ_u|B| = 0 (Burby–Kallinikos–MacKay); then ι_u ω_B is closed, and where it is exact, ι_u ω_B = −dψ, so ψ is a flux function and u is tangent to the flux surfaces. This is exactly the condition for u to generate a Noether symmetry of the first-order guiding-centre Hamiltonian system, giving a conserved momentum. Weak quasisymmetry (Rodríguez–Helander–Bhattacharjee; Constantin–Drivas–Ginsberg) keeps B × ξ = −∇ψ, div ξ = 0 and ξ · ∇|B| = 0. A quasisymmetry is not required to be an isometry, nor a symmetry of the equilibrium equations.

**Sources.** Burby, Kallinikos & MacKay, J. Math. Phys. 61 (2020) 093503, arXiv:1912.06468; Rodríguez, Helander & Bhattacharjee, Phys. Plasmas 27 (2020) 062501, arXiv:2004.11431; Constantin, Drivas & Ginsberg, J. Plasma Phys. 87 (2021) 905870111, arXiv:2009.08860; Nührenberg & Zille, Phys. Lett. A 129 (1988) 113; Helander, Rep. Prog. Phys. 77 (2014) 087001.

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

-- In form language: d(ι_ξ vol) = 0, ι_ξ ω_B = −dψ, d|B|(ξ) = 0.
-- PlasmaLean/Theory/Fields/FormBridges.lean (namespace PlasmaLean.Forms)
structure FormWeakQS (ω : Space → Form 2) (ξ : Space → Space) (ψ : Space → ℝ)
    (T : Set Space) : Prop where
  ...
  div_free : ∀ x ∈ T, extDeriv (fun y => flux (ξ y)) x = 0
  interior : ∀ x ∈ T, (ω x).curryLeft (ξ x) = -formGrad ψ x
  qs : ∀ x ∈ T, formGrad (fun y => ‖flux.symm (ω y)‖) x ![ξ x] = 0
theorem formWeakQS_flux_iff : FormWeakQS (fluxField B) ξ ψ T ↔ WeakQS B ξ ψ T

-- Invariance of the flux form under the generator (23 November 2026):
-- PlasmaLean/Theory/Fields/FormCalculus.lean, using TauCeti's Cartan formula
theorem WeakQS.lieDerivForm_flux_eq_zero (h : WeakQS B ξ ψ T) (hT : IsOpen T)
    (hB : ∀ x ∈ T, DifferentiableAt ℝ B x) (hdiv : ∀ x ∈ T, fieldDiv B x = 0)
    (hψ : ∀ x ∈ T, ContDiffAt ℝ 2 ψ x) (hx : x ∈ T) :
    TauCeti.lieDerivForm ξ (fluxField B) x = 0              -- L_ξ ω_B = 0

theorem lieDerivForm_flux (ξ B : Space → Space) (x : Space) :
    TauCeti.lieDerivForm ξ (fluxField B) x
      = flux (VectorField.lieBracket ℝ ξ B x + fieldDiv ξ x • B x)
theorem WeakQS.lieBracket_eq_zero ... : VectorField.lieBracket ℝ ξ B x = 0   -- [ξ, B] = 0
```

## Continuous symmetry and the conserved canonical momentum

*Symplectic Geometry (Noether, momentum map).* In an axisymmetric or helically symmetric field the canonical momentum of a charged particle is conserved, which confines its orbit to a band of flux surfaces.

**Geometry.** Let K be a Killing field with ℒ_K ω_B = 0. Then ι_K ω_B is closed; where it is exact, ι_K ω_B = −dψ and ψ is a flux function. K is then a Hamiltonian symmetry of the Lorentz flow for the magnetic symplectic form dp ∧ dq + q π*ω_B, with momentum map m⟨K, v⟩ + qψ. Quasisymmetry is the same statement for the guiding-centre system, where K need only preserve ω_B and |B|.

**Sources.** Cary & Littlejohn, Ann. Phys. 151 (1983) 1; Burby, Kallinikos & MacKay, J. Math. Phys. 61 (2020) 093503, arXiv:1912.06468; Rodríguez, Helander & Bhattacharjee, Phys. Plasmas 27 (2020) 062501, arXiv:2004.11431; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Kinetic/Noether.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Kinetic/Noether.lean).

```lean
-- PlasmaLean/Theory/Kinetic/Noether.lean (namespace PlasmaLean.Kinetic)
structure IsKilling (K : Space → Space) (DK : Space → Space →L[ℝ] Space) : Prop
def SymmetricFlux (B G K : Space → Space) : Prop :=
  ∀ x v : Space, ⟪K x, cross v (B x)⟫ = -⟪G x, v⟫        -- G = ∇ψ
theorem noetherMomentum_conserved (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hK : IsKilling K DK) (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y)
    (hB : SymmetricFlux B G K) (s t : ℝ) :
    noetherMomentum m q K ψ x v s = noetherMomentum m q K ψ x v t

-- Guiding centres in an exactly quasisymmetric Boozer field:
-- PlasmaLean/Theory/Kinetic/BoozerGuidingCentre.lean
theorem helicalMomentum_conserved ... (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (s t : ℝ) :
    helicalMomentum F q N M ψ ρ s = helicalMomentum F q N M ψ ρ t

-- In form language: ι_K ω_B = −dψ.
-- PlasmaLean/Theory/Fields/FormBridges.lean (namespace PlasmaLean.Forms)
def FormSymmetricFlux (ω : Space → Form 2) (γ : Space → Form 1) (K : Space → Space) : Prop :=
  ∀ x, (ω x).curryLeft (K x) = -γ x
theorem formSymmetricFlux_iff :
    FormSymmetricFlux (fluxField B) (fun x => flat (G x)) K ↔ Kinetic.SymmetricFlux B G K

-- Not in the library: the symplectic form and the momentum map as such.

-- From TauCeti's general Noether theorem (23 November 2026):
-- PlasmaLean/Theory/Kinetic/NoetherLagrangian.lean (namespace PlasmaLean.Kinetic)
def lorentzLagrangian (m q : ℝ) (A : Space → Space) (_t : ℝ) (p : Space × Space) : ℝ :=
  m / 2 * ‖p.2‖ ^ 2 + q * ⟪A p.1, p.2⟫
theorem lorentzOrbit_eulerLagrange (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (fun u => lorentzLagrangian m q A s (x s, u)) (v s))
      (fderiv ℝ (fun y => lorentzLagrangian m q A t (y, v t)) (x t)) t
theorem noetherMomentum_translation_conserved ... (hinv : ∀ y s, A (y + s • e) = A y) (s t : ℝ) :
    noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫) x v s
      = noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫) x v t
-- Rotations and gauge terms (PlasmaLean/Theory/Kinetic/NoetherRotation.lean):
theorem noetherMomentum_linear_gauge_conserved (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hK : ∀ w, ⟪K w, w⟫ = 0) (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hχ : ∀ y, HasFDerivAt χ (innerSL ℝ (G y)) y)
    (hequiv : ∀ y, fderiv ℝ A y (K y) = K (A y) + G y) (s t : ℝ) :
    noetherMomentum m q (fun y => K y) (fun y => ⟪A y, K y⟫ - χ y) x v s = ... t
theorem canonicalMomentum_rotGenZ_conserved ... (hequiv : ∀ y,
    fderiv ℝ A y (rotGenZ y) = rotGenZ (A y)) (s t : ℝ) :
    canonicalMomentum m q (fun y => ⟪A y, rotGenZ y⟫) x v s = ... t
-- K is a skew linear generator; equivariance of A is the infinitesimal condition.
-- Finite symmetry and the link to the direct proofs
-- (PlasmaLean/Theory/Kinetic/NoetherSymmetryBridge.lean):
theorem fderiv_rotGenZ_of_rotZ_equivariant (hA : Differentiable ℝ A)
    (hequiv : ∀ s y, A (rotZ s y) = rotZ s (A y)) (y : Space) :
    fderiv ℝ A y (rotGenZ y) = rotGenZ (A y)
theorem symmetricFlux_symmetryFluxGrad_iff (hcurl : ∀ y, B y = fieldCurl A y) :
    SymmetricFlux B (symmetryFluxGrad A K) (fun y => K y)
      ↔ ∀ y, fderiv ℝ A y (K y) = K (A y)
theorem axisymmetricFlux_iff_symmetricFlux_rotGenZ (B G : Space → Space) :
    AxisymmetricFlux B G ↔ SymmetricFlux B G (fun y => rotGenZ y)
-- So the hypothesis of the direct proof is equivalent to equivariance of A, and each
-- conservation law has two independent proofs (Noether and direct).

-- Gauge terms and gauge invariance (PlasmaLean/Theory/Kinetic/NoetherGaugeBridge.lean):
theorem symmetricFlux_gauge_iff (hcurl : ∀ y, B y = fieldCurl A y) :
    SymmetricFlux B (fun y => symmetryFluxGrad A K y - G y) (fun y => K y)
      ↔ ∀ y, fderiv ℝ A y (K y) = K (A y) + G y
theorem noetherMomentum_add_gradient (m q : ℝ) (A H : Space → Space) (χ : Space → ℝ)
    (K : Space → Space) (x v : ℝ → Space) (t : ℝ) :
    noetherMomentum m q K (fun y => ⟪A y + H y, K y⟫ - (χ y + ⟪H y, K y⟫)) x v t
      = noetherMomentum m q K (fun y => ⟪A y, K y⟫ - χ y) x v t
-- The identity above is pure algebra (no hypotheses). The gauge-invariance content is that
-- χ + ⟪∇Λ, K x⟫ is an admissible gauge term for A + ∇Λ (equivariant_gauge_add_gradient,
-- hasFDerivAt_gauge_term_add_gradient), and that any admissible gauge term changes the
-- conserved momentum only by a constant (noetherMomentum_add_gradient_of_gauge_term).
-- For linear A: commuting with rotGenZ ⇔ equivariance under every rotZ s.
```

## Near-axis expansion (Garren–Boozer, Landreman–Sengupta)

*Differential Geometry of Curves.* Asymptotic expansion of a field or equilibrium in powers of the distance r from a closed magnetic-axis curve.

**Geometry.** Jet expansion in tubular coordinates around a closed curve with curvature κ and torsion τ (Frenet or Bishop frame). For the field-line flow this is the Birkhoff normal form at an elliptic closed orbit: the on-axis rotational transform is its rotation number, and integrability to all orders gives formal Boozer or Hamada coordinates. First-order quasisymmetry reduces to a periodic Riccati-type ODE for the rotating elliptical cross-section.

**Sources.** Mercier, Nucl. Fusion 4 (1964) 213; Garren & Boozer, Phys. Fluids B 3 (1991) 2805, 2822; Landreman & Sengupta, J. Plasma Phys. 84 (2018) 905840616; Duignan & Meiss, Phys. Plasmas 28 (2021) 122501, arXiv:2108.03337; Burby, Duignan & Meiss, J. Math. Phys. 62 (2021) 122901, arXiv:2103.02888.

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

**Sources.** Littlejohn, J. Plasma Phys. 29 (1983) 111; Cary & Brizard, Rev. Mod. Phys. 81 (2009) 693; Burby & Ellison, Phys. Plasmas 24 (2017), doi:10.1063/1.5004429, arXiv:1709.02867; MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

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

-- Not in the library: the symplectic form itself. For J∥ and bounce averages see the
-- omnigeneity entry (Theory/Kinetic/Omnigeneity.lean, AvailableEnergy.lean).
```

## Charged-particle motion in a magnetic field

*Symplectic Geometry (magnetic flows).* The Lorentz force bends a charged particle into a helix around a field line. Energy is conserved exactly and the magnetic moment almost exactly.

**Geometry.** The Hamiltonian flow of H = |p|²/2m on T*M for the twisted symplectic form dp ∧ dq + q π*ω_B (a magnetic geodesic flow); no vector potential is needed. The magnetic moment μ is the action of the fast gyration, an adiabatic invariant to all orders in the gyroradius (Kruskal). Reducing by the gyro-phase gives the guiding-centre system on M × ℝ.

**Sources.** Kruskal, J. Math. Phys. 3 (1962) 806; Novikov, Russ. Math. Surv. 37:5 (1982) 1; Littlejohn, J. Plasma Phys. 29 (1983) 111; Cary & Brizard, Rev. Mod. Phys. 81 (2009) 693.

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Kinetic/FullOrbit.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Kinetic/FullOrbit.lean).

```lean
-- PlasmaLean/Theory/Kinetic/FullOrbit.lean (namespace PlasmaLean.Kinetic)
structure LorentzOrbit (m q : ℝ) (E B : Space → Space) (x v : ℝ → Space) : Prop where
  position : ∀ t, HasDerivAt x (v t) t
  newton : ∀ t, ∃ a, HasDerivAt v a t ∧ m • a = q • (E (x t) + cross (v t) (B (x t)))
theorem energy_conserved (h : LorentzOrbit m q E B x v) (hΦ : IsPotential Φ E) (s t : ℝ) :
    orbitEnergy m q Φ x v s = orbitEnergy m q Φ x v t

-- PlasmaLean/Theory/Kinetic/LorentzExistence.lean
theorem lorentzOrbit_exists {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    (hB : ContDiff ℝ 1 B) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x v ∧ x 0 = x₀ ∧ v 0 = v₀

-- PlasmaLean/Theory/Kinetic/GuidingCentre.lean: magneticMoment, magneticMoment_drift
-- Not in the library: the twisted symplectic form; adiabatic invariance of μ to all orders.

-- 23 November 2026: TauCeti v4.36.0 has a large symplectic library (Hamiltonian vector
-- fields, Poisson brackets, Liouville–Arnold tori, magnetic translation of a cotangent
-- space). Used: Noether's theorem for the Lagrangian (m/2)|v|² + q A·v
-- (Theory/Kinetic/NoetherLagrangian, NoetherRotation), and the magnetic symplectic form:
-- PlasmaLean/Theory/Kinetic/MagneticSymplectic.lean (namespace PlasmaLean.Kinetic)
abbrev PhaseSpace : Type := Space × StrongDual ℝ Space
def kineticMomentumMap (q : ℝ) (A : Space → Space) (z : PhaseSpace) : PhaseSpace
  -- (x, p) ↦ (x, p − q A(x)♭): canonical to kinetic momentum (TauCeti's magnetic translation)
theorem canonicalForm_fderiv_kineticMomentumMap_flux (q : ℝ) (hA : DifferentiableAt ℝ A z.1)
    (v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap q A) z v)
        (fderiv ℝ (kineticMomentumMap q A) z w) =
      strongDualCotangentSymplecticForm v w + q * flux (fieldCurl A z.1) ![v.1, w.1]
  -- Ψ^*Ω = Ω + q π^*ω_B for Ψ : canonical → kinetic momentum; in this convention the
  -- magnetic form on kinetic phase space is Ω − q π^*ω_B (audit AV-H1)
theorem lorentzOrbit_hamilton (hm : m ≠ 0) (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y) (t : ℝ) :
    HasDerivAt (canonicalCurve m q A x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (magneticHamiltonian m q A) (canonicalCurve m q A x v t)) t
  -- Lorentz orbits are integral curves of the Hamiltonian field of |p♯ − qA|²/(2m)
-- With an electric field E = −∇Φ, and the converse
-- (PlasmaLean/Theory/Kinetic/MagneticHamiltonConverse.lean):
def emHamiltonian (m q : ℝ) (A : Space → Space) (Φ : Space → ℝ) (z : PhaseSpace) : ℝ :=
  magneticHamiltonian m q A z + q * Φ z.1
theorem lorentzOrbit_iff_emHamilton (hm : m ≠ 0) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (hΦ : IsPotential Φ E) (x v : ℝ → Space) :
    LorentzOrbit m q E B x v ↔
      ∀ t, HasDerivAt (canonicalCurve m q A x v)
        (hamiltonianVectorField (emHamiltonian m q A Φ) (canonicalCurve m q A x v t)) t
theorem emHamiltonian_conserved ... : emHamiltonian m q A Φ (z s) = emHamiltonian m q A Φ (z t)
-- The Lorentz equations and Hamilton's equations are equivalent.
-- E × B drift, existence and uniqueness (PlasmaLean/Theory/Kinetic/CrossedFieldOrbit.lean):
def driftVelocity (E₀ B₀ : ℝ) : Space := -(E₀ / B₀) • coordVec 1      -- (E × B)/|B|²
theorem crossedField_orbit (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ) (X : Space)
    (a b w : ℝ) :
    LorentzOrbit m q (fun _ => E₀ • coordVec 0) (fun _ => B₀ • coordVec 2)
      (crossedPosition m q E₀ B₀ X a b w) (crossedVelocity m q E₀ B₀ a b w)
theorem crossedPosition_period ... :   -- per gyro-period the position advances by
    crossedPosition ... (t + 2π/Ω) = crossedPosition ... t + (2π/Ω) • (driftVelocity E₀ B₀ + w • e_z)
theorem lorentzOrbit_unique (hm : m ≠ 0) (hA : ContDiff ℝ 2 A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) ... : x₁ = x₂ ∧ v₁ = v₂
theorem lorentzOrbit_existsUnique_uniform (hm : m ≠ 0) (q : ℝ) (Ev Bv x₀ v₀ : Space) :
    ∃ x v, LorentzOrbit m q (fun _ => Ev) (fun _ => Bv) x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ (unique)

-- PlasmaLean/Theory/Kinetic/LorentzGlobalExistence.lean   (B = ∇ × A, A of class C², E = −∇Φ)
theorem lorentzOrbit_existsUnique_of_linear_growth (hm : m ≠ 0) ... (hgrowth : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) :
    ∃ x v, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ (unique)
theorem lorentzOrbit_existsUnique_of_potential_bounded_below (hm : 0 < m) ... (hΦ : ∀ y, c ≤ q * Φ y) : ...

-- PlasmaLean/Theory/Kinetic/LorentzOrbitOpen.lean   (E, B of class C¹ on an open U; no potential)
theorem lorentzOrbitOn_exists_local_of_contDiffOn (hm : m ≠ 0) (hU : IsOpen U) ... (hx₀ : x₀ ∈ U) :
    ∃ ε > 0, ∃ x v, LorentzOrbitOn m q E B x v (Ioo (t₀ - ε) (t₀ + ε)) ∧ x t₀ = x₀ ∧ v t₀ = v₀ ∧ ...
theorem lorentzOrbitOn_unique_of_contDiffOn ...   -- orbits staying in U are unique
theorem lorentzOrbit_existsUnique_of_confined ... -- global, if positions stay in a compact K ⊆ U
-- Not proved: finite-time blow-up for repulsive potentials; maximal orbits and escape;
-- time-dependent potentials; the bundled symplectomorphism.
```

## Omnigeneity and the second adiabatic invariant J∥

*Symplectic Geometry (action variables).* Trapped particles bounce between mirror points and drift slowly across the field. In an omnigenous field the bounce-averaged radial drift vanishes for every trapped particle (contract clause C2).

**Geometry.** For a trapped particle the motion along a field line is a one-degree-of-freedom Hamiltonian system; its action J∥(ψ, α, E, μ) = ∮ m v∥ dl is an adiabatic invariant. In Clebsch coordinates (ψ, α), which are canonically conjugate for q dψ ∧ dα, J∥ generates the bounce-averaged drift: ⟨ψ̇⟩ ∝ ∂J∥/∂α. Omnigeneity is ∂J∥/∂α = 0, i.e. J∥ is constant on flux surfaces. Quasisymmetry implies it; quasi-isodynamic fields satisfy it without a symmetry of |B| (Cary–Shasharina).

**Sources.** Hall & McNamara, Phys. Fluids 18 (1975) 552; Cary & Shasharina, Phys. Rev. Lett. 78 (1997) 674; Helander, Rep. Prog. Phys. 77 (2014) 087001; Northrop, The Adiabatic Motion of Charged Particles (Interscience, 1963).

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Kinetic/Omnigeneity.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Kinetic/Omnigeneity.lean).

```lean
-- PlasmaLean/Theory/Kinetic/Omnigeneity.lean (namespace PlasmaLean.Kinetic.Boozer)
def bounceAvgDrift (ψ : ℝ → ℝ) (τ : ℝ) : ℝ := (ψ τ - ψ 0) / τ
def OmnigenousOn (F : BoozerField) (c : ℝ) : Prop :=
  ∀ (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (τ : ℝ), 0 < m → q ≠ 0 → 0 ≤ μ →
    TrappedBounce F m q μ c ψ θ φ ρ τ → ψ τ = ψ 0
theorem omnigenousOn_of_exactQS (hG : F.G ≠ 0) {N M c : ℝ}
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (hinj : InjOn (fun x => N * x - M * F.ψp x) (Ioc 0 c)) : OmnigenousOn F c

-- The bounce action, normalized:
-- PlasmaLean/Theory/Kinetic/AvailableEnergy.lean (namespace PlasmaLean.Kinetic.AvailableEnergy)
def NormalizedBounceAction (B : ℝ → ℝ → ℝ → ℝ) (lmin lmax ψ α lam : ℝ) : ℝ :=
  ∫ l in lmin..lmax, Real.sqrt (max 0 (1 - lam * B ψ α l))

-- Not in the library: J∥ as the Hamiltonian of the averaged drift; the effective
-- ripple ε_eff; quasi-isodynamic examples.
```

## Ideal MHD stability: energy principle and Mercier criterion

*Spectral Geometry & Calculus of Variations.* An equilibrium is linearly stable to ideal modes if the potential energy δ²W(ξ, ξ) is positive for every admissible displacement. Local criteria (Mercier interchange, ballooning) are necessary conditions.

**Geometry.** Positivity of the Hessian δ²W(ξ, ξ) = −½ ∫ ⟨ξ, F(ξ)⟩ of the energy at an equilibrium, F a formally self-adjoint second-order operator; equivalently the second variation of the energy restricted to the orbit of the equilibrium under ideal displacements (energy–Casimir picture). The Mercier index D_Merc > 0 is the local interchange condition on one surface: an indicial (Hardy-type) condition at a rational surface, combining shear and magnetic well V″.

**Sources.** Bernstein, Frieman, Kruskal & Kulsrud, Proc. R. Soc. A 244 (1958) 17; Mercier, Nucl. Fusion 1 (1960) 47; Greene & Johnson, Phys. Fluids 5 (1962) 510; Holm, Marsden, Ratiu & Weinstein, Phys. Rep. 123 (1985) 1.

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

## Suydam, Newcomb and ballooning criteria

*Spectral Geometry & Calculus of Variations (Jacobi fields).* The standard local stability tests reduce the energy principle to an ordinary differential equation along a radius or along a field line.

**Geometry.** Each test is the positivity of a one-dimensional quadratic form ∫ (f ξ′² + g ξ²). By Jacobi's criterion (the Morse index theorem in one dimension) this is the absence of conjugate points of the Euler–Lagrange (Jacobi) equation, and it is certified by a positive supersolution, a Riccati solution or a Picone identity. Suydam's and Mercier's criteria are the indicial conditions at a singular point (a Hardy inequality).

**Sources.** Suydam, Proc. 2nd UN Conf. Peaceful Uses of Atomic Energy 31 (1958) 157; Newcomb, Ann. Phys. 10 (1960) 232; Connor, Hastie & Taylor, Phys. Rev. Lett. 40 (1978) 396; Milnor, Morse Theory (Princeton, 1963).

**Lean status: In the library.** Module: [`PlasmaLean/Theory/Stability/Newcomb.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Stability/Newcomb.lean).

```lean
-- PlasmaLean/Theory/Stability/Newcomb.lean (namespace PlasmaLean.Stability)
def newcombForm (f g : ℝ → ℝ) (x₀ x₁ : ℝ) (ξ ξ' : ℝ → ℝ) : ℝ :=
  ∫ x in x₀..x₁, (f x * ξ' x ^ 2 + g x * ξ x ^ 2)
theorem picone_certificate ... (hdisc : ∀ x ∈ uIcc x₀ x₁, φ x ^ 2 ≤ f x * (g x - c - h x)) :
    c * ∫ x in x₀..x₁, ξ x ^ 2 ≤ newcombForm f g x₀ x₁ ξ ξ'
theorem jacobi_certificate ...

-- Necessity (a conjugate point excludes every certificate):
-- PlasmaLean/Theory/Stability/SturmNecessity.lean
structure ConjugatePoint (P Q W : ℝ → ℝ) (c a z : ℝ)
theorem no_jacobiData ...

-- PlasmaLean/Theory/Equilibrium/ScrewPinch.lean: SuydamStableOn
-- PlasmaLean/Theory/Stability/Ballooning.lean: BallooningOperator, BartaCertificate
-- Not in the library: the reduction of δ²W to these forms for a general equilibrium
-- (it is supplied; see NewcombReduction).
```

## Non-overlapping flux surfaces and positive Jacobian (√g > 0)

*Complex Geometry & Harmonic Mappings.* Nested surfaces given by double Fourier series R(s,θ,φ), Z(s,θ,φ) must not self-intersect or fold inside the plasma.

**Geometry.** det(DΦ) > 0 for Φ : D² × S¹ → M. Slice by slice in φ this is univalence of a planar harmonic map of the disk (Radó–Kneser–Choquet, ℓ¹ coefficient criteria).

**Sources.** Kneser, Jahresber. DMV 35 (1926) 123; Choquet, Bull. Sci. Math. 69 (1945) 156; Duren, Harmonic Mappings in the Plane (CUP, 2004); Hirshman & Whitson, Phys. Fluids 26 (1983) 3553.

**Lean status: Not in the library: illustrative sketch.**

```lean
-- Illustrative sketch, not in the library (proposed signature):
def ValidFluxCoordinateMap (Φ : PolarToroidalDomain → ℝ³) : Prop :=
  Function.Injective Φ ∧ ∀ x ∈ interiorDomain, jacobianDet Φ x > 0

-- See Challenge 5 (lean_stubs/Challenge5_HarmonicUnivalence.lean).
```

## Biot–Savart law and field derivatives for filament coils

*Integral Geometry & Operator Calculus.* The field of filamentary current loops, and its spatial derivatives and its sensitivity to coil-shape errors.

**Geometry.** B(x) = (μ₀ I / 4π) ∮ γ'(s) × (x − γ(s)) / |x − γ(s)|³ ds, smooth (indeed harmonic) away from the curve. Biot–Savart is the Green operator inverting curl on divergence-free fields: BS(J) is the unique decaying field with d(BS(J))♭ = μ₀ ω_J. The circulation of B around a second closed curve is μ₀ I times the Gauss linking number, and helicity is the quadratic form ⟨B, BS(B)⟩.

**Sources.** Cantarella, DeTurck & Gluck, J. Math. Phys. 42 (2001) 876; Cantarella, DeTurck & Gluck, Amer. Math. Monthly 109 (2002) 409; DeTurck & Gluck, J. Math. Phys. 49 (2008) 023504.

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

**Sources.** Federer, Trans. Amer. Math. Soc. 93 (1959) 418; Gonzalez & Maddocks, Proc. Natl. Acad. Sci. 96 (1999) 4769.

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

**Sources.** Ahlfors, Conformal Invariants (McGraw-Hill, 1973); MacKay, J. Plasma Phys. 86 (2020) 925860101, arXiv:1912.11150.

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

## Flux-surface average and the volume derivative V′(ψ)

*Integral Geometry (coarea formula).* Transport across flux surfaces is described by one-dimensional equations in the flux label, with geometric coefficients obtained by averaging over each surface.

**Geometry.** By the coarea formula ∫ f dvol = ∫ dψ ∫_{Σ_ψ} f dS/|∇ψ|. So V′(ψ) = ∫_{Σ_ψ} dS/|∇ψ| and ⟨f⟩ = (1/V′) ∫_{Σ_ψ} f dS/|∇ψ| is the average over the fibre of ψ for the pushed-forward volume measure. The divergence theorem becomes ⟨∇·Γ⟩ = (1/V′) d/dψ (V′ ⟨Γ·∇ψ⟩), which is what reduces transport to one radial dimension.

**Sources.** Federer, Trans. Amer. Math. Soc. 93 (1959) 418; Hinton & Hazeltine, Rev. Mod. Phys. 48 (1976) 239; Helander, Rep. Prog. Phys. 77 (2014) 087001.

**Lean status: Partly in the library.** Module: [`PlasmaLean/Theory/Transport/FluxGeometry.lean`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Transport/FluxGeometry.lean).

```lean
-- PlasmaLean/Theory/Transport/FluxGeometry.lean (namespace PlasmaLean.Transport)
structure FluxGeometry   -- Vp dVp g dg h : ℝ → ℝ   (V′, ⟨|∇ψ|²⟩, ⟨Δψ⟩ as supplied data)
class FluxGeometry.Laws (G : FluxGeometry) : Prop where ...
  gauss : ∀ s ∈ Icc (0 : ℝ) 1, G.dVp s * G.g s + G.Vp s * G.dg s = G.Vp s * G.h s
  -- the Gauss identity (V′ g)′ = V′ h

-- PlasmaLean/Kernel/Transport.lean: RadialCoefficients, RadialHeatTransport
-- Not in the library: the coarea formula for a flux function; the averages are
-- supplied data, not computed from a field.
```
