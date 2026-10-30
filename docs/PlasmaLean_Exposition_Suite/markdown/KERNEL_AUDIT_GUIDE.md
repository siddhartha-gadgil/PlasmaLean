# Audit the PlasmaLean kernel in 10 minutes

The PlasmaLean domain kernel is `PlasmaLean/Kernel/`: six modules, about 900 lines (`Equilibrium` 47, `Slab` 38, `ThermalSlab` 31, `Vacuum` 99, `Transport` 304, `Fusion` 381). It is a *domain* kernel, not an extension of Lean's logical kernel: its laws are `Prop`-valued classes and structures taken as hypotheses, never axioms. `#print axioms` on any theorem therefore shows only `[propext, Classical.choice, Quot.sound]`; whether the laws describe the physics is a separate question, answered by audit.

The first strict audit (30 October 2026, commit `cda8bd0`) reviewed all 52 kernel declarations. Full record: [notes/audit/2026-10-30-kernel-audit.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md).

This guide quotes the real kernel declarations (abridged where marked `...`) and the real sanity theorems.

---

## 1. Kernel/Equilibrium: algebraic force balance (Minutes 0–1)

```lean
-- PlasmaLean/Kernel/Equilibrium.lean (47 lines)
namespace PlasmaLean

/-- Cartesian three-component real data. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Pointwise static isotropic force balance, with SI magnetic/current/gradient data. -/
class ForceBalance (B J g : Vec3) : Prop where
  balance : J ⨯₃ B = g

theorem field_tangency (B J g : Vec3) [ForceBalance B J g] : B ⬝ᵥ g = 0
theorem current_tangency (B J g : Vec3) [ForceBalance B J g] : J ⬝ᵥ g = 0
theorem gradient_zero_iff_force_free (B J g : Vec3) [ForceBalance B J g] :
    g = 0 ↔ J ⨯₃ B = 0
```

**Sanity checks.**

```lean
-- PlasmaLean/Sanity/Equilibrium.lean
theorem zeroBalance : ForceBalance 0 0 0
theorem parallelBalance (B : Vec3) : ForceBalance B B 0
-- PlasmaLean/Sanity/AuditEquilibrium.lean (namespace PlasmaLean.Sanity.Audit)
forceBalance_rejects_perp       -- counterexample
pinch_force_inward              -- orientation
forceBalance_rejects_reversed   -- orientation
forceBalance_of_cross           -- E-1: ForceBalance B J (J ⨯₃ B) for every B, J
forceBalance_smul_field, forceBalance_smul_current  -- scaling
```

**Why it is stated this way.** `ForceBalance` is a *supplied law*: a `Prop`-valued class taken as a hypothesis, not an axiom. The vector `g` is free data; the kernel does not say that it is the gradient of a pressure, and it has no Ampère law and no $\mu_0$. That link is made downstream.

**Audit findings.** **E-1 (low, resolved downstream).** `forceBalance_of_cross` shows that `ForceBalance B J (J ⨯₃ B)` holds for every $B, J$, so the law alone constrains nothing. All 14 design users tie $g$ to an actual pressure gradient and use $J = \mu_0^{-1}\nabla\times B$; the module `Design/ForceBalanceGradient` restates them with Mathlib's `gradient p` (e.g. `solovev_force_balance_gradient`). A claim that cites `ForceBalance` must also cite the gradient theorem.

---

## 2. Kernel/Slab: one-coordinate static MHD (Minutes 1–2)

```lean
-- PlasmaLean/Kernel/Slab.lean (38 lines), namespace PlasmaLean.Equilibrium
def slabCurl (B : ℝ → Vec3) (z : ℝ) : Vec3 :=
  ![-deriv (fun t => B t 1) z, deriv (fun t => B t 0) z, 0]

class StaticSlab (B J : ℝ → Vec3) (p : ℝ → ℝ) (μ₀ : ℝ) : Prop where
  permeability_pos : 0 < μ₀
  field_differentiable : ∀ i, Differentiable ℝ (fun z => B z i)
  pressure_differentiable : Differentiable ℝ p
  balance : ∀ z, J z ⨯₃ B z = ![0, 0, deriv p z]
  divergence : ∀ z, deriv (fun t => B t 2) z = 0
  ampere : ∀ z, slabCurl B z = μ₀ • J z
```

**Sanity checks.**

```lean
-- PlasmaLean/Theory/Equilibrium/Slab.lean
uniform_slab, helicalSlab_equilibrium        -- instances
-- PlasmaLean/Sanity/AuditEquilibrium.lean
slab_rejects_compressive                     -- counterexample
slab_total_pressure_deriv                    -- p + |B⊥|²/2μ₀ is conserved
slab_negative_pressure                       -- S-1: negative pressure admitted
```

**Why it is stated this way.** Here the derivatives are real derivatives (`deriv`), and the slab law includes Ampère's law and $\nabla\cdot B = 0$. Because `deriv` is totalized (it returns $0$ where a function is not differentiable), the law requires differentiability explicitly.

**Audit findings.** **S-1 (low, recorded).** `StaticSlab` does not require $p \ge 0$: `slab_negative_pressure` exhibits $B = (0,z,0)$, $J = (-1,0,0)$, $\mu_0 = 1$, $p = -z^2/2$. The only design user, `Design/ValidatedSlabEquilibrium`, imposes $p > 0$ itself.

---

## 3. Kernel/ThermalSlab: steady slab heat conduction (Minutes 2–3)

```lean
-- PlasmaLean/Kernel/ThermalSlab.lean (31 lines), namespace PlasmaLean.Engineering
class SteadySlab (T dT : ℝ → ℝ) (Tc q Q h k hc : ℝ) : Prop where
  thickness_nonneg : 0 ≤ h
  conductivity_pos : 0 < k
  cooling_pos : 0 < hc
  temperature_derivative : ∀ x ∈ Set.Icc 0 h, HasDerivAt T (dT x) x
  flux_derivative : ∀ x ∈ Set.Icc 0 h, HasDerivAt dT (-Q / k) x
  hot_flux : k * dT h = q
  cold_flux : k * dT 0 = hc * (T 0 - Tc)
```

**Sanity checks.**

```lean
-- PlasmaLean/Theory/Engineering/SlabHeat.lean
slab_solution                    -- explicit solution (and uniqueness)
-- PlasmaLean/Sanity/AuditThermalSlab.lean
steadySlab_unloaded              -- degenerate case
steadySlab_rejects_isothermal    -- counterexample
steadySlab_energy_balance        -- hc (T(0) − Tc) = q + Q h
steadySlab_cold_face_ge          -- sign
steadySlab_zero_thickness        -- T-1
```

**Why it is stated this way.** Signs and units were checked in the audit: $-kT'' = Q$, the loaded face at $x = h$ receives $q$, the cooled face at $x = 0$ removes $h_c(T(0) - T_c)$. The global energy balance `steadySlab_energy_balance` confirms the orientation.

**Audit findings.** **T-1 (low, recorded).** `thickness_nonneg : 0 ≤ h` admits $h = 0$, where the law reduces to $h_c(T(0) - T_c) = q$ (`steadySlab_zero_thickness`). Not contradictory, but a degenerate witness; the design user uses $h > 0$.

---

## 4. Kernel/Vacuum: current-free magnetostatics (Minutes 3–5)

```lean
-- PlasmaLean/Kernel/Vacuum.lean (99 lines), namespace PlasmaLean.Vacuum
abbrev Euclid3 := EuclideanSpace ℝ (Fin 3)
abbrev coordVec (i : Fin 3) : Euclid3 := EuclideanSpace.single i (1 : ℝ)

def divOp (L : Euclid3 →L[ℝ] Euclid3) : ℝ := ∑ i : Fin 3, L (coordVec i) i
def curlOp (L : Euclid3 →L[ℝ] Euclid3) : Euclid3 := ...
def fieldDiv (B : Euclid3 → Euclid3) (x : Euclid3) : ℝ := divOp (fderiv ℝ B x)
def fieldCurl (B : Euclid3 → Euclid3) (x : Euclid3) : Euclid3 :=
  curlOp (fderiv ℝ B x)

structure VacuumField (Ω : Set Euclid3) (B : Euclid3 → Euclid3) : Prop where
  isOpen : IsOpen Ω
  contDiffOn : ContDiffOn ℝ 2 B Ω
  div_eq_zero : ∀ x ∈ Ω, fieldDiv B x = 0
  curl_eq_zero : ∀ x ∈ Ω, fieldCurl B x = 0
```

**Sanity checks.**

```lean
-- PlasmaLean/Sanity/Vacuum.lean (namespace PlasmaLean.Sanity)
zero_vacuum, const_vacuum              -- degenerate cases
hyperbolic_gradient_vacuum             -- instance
filamentField_vacuumField              -- closed C¹ filaments away from the coil
rotationField_not_vacuum               -- counterexample
-- PlasmaLean/Sanity/AuditVacuum.lean (namespace PlasmaLean.Sanity.Audit)
id_not_vacuum, fieldCurl_id, fieldDiv_rotationField  -- the two laws are independent
absField_not_vacuum                    -- the open-set and C² laws are load-bearing
vacuumField_empty                      -- V-1
```

**Why it is stated this way.** Divergence and curl are defined from Mathlib's Fréchet derivative, and their agreement with the theory-layer operators is proved in `Sanity/Vacuum` (`divOp_eq_divergence`, `curlOp_eq_curl`). Since `fderiv` is $0$ where $B$ is not differentiable, the law asks for $C^2$ on an open set; `absField_not_vacuum` shows these conditions matter.

**Audit findings.** **V-1 (low, recorded).** `VacuumField ∅ B` holds for every $B$ (`vacuumField_empty`). This is expected for a region-based law, but a theorem whose conclusion does not mention a point of $\Omega$ can be vacuous. Downstream statements (rational stellarator, polygon coils, the vacuum-pair volume error) must exhibit a nonempty region.

---

## 5. Kernel/Transport: radial heat transport (Minutes 5–7)

```lean
-- PlasmaLean/Kernel/Transport.lean (304 lines), namespace PlasmaLean.Transport
-- ∂ₜT = D T'' + (∂ψD + ∂TD T' + D V''/V') T' + R  on ψ ∈ [0,1]
class TransportLaws (c : RadialCoefficients) : Prop where
  Vp_pos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.Vp ψ
  D_nonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T
  D_axis : c.axis = .degenerate → ∀ T : ℝ, c.D 0 T = 0
  ...  -- derivative laws, regular axis, Tdom open, R continuous

class ClassicalRadialSolution (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop where
  tau_nonneg : 0 ≤ τ
  regular : u.Regular τ
  pde : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    u.Tt ψ t = c.op ψ (u.T ψ t) (u.Tψ ψ t) (u.Tψψ ψ t)
  axis : c.axis = .regular → ∀ t ∈ Icc 0 τ, u.Tψ 0 t = 0
  edge : ∀ t ∈ Icc 0 τ, u.T 1 t = Tedge t
```

**Sanity checks.**

```lean
-- PlasmaLean/Sanity/Transport.lean
constField_solution, cosMode_radialHeatTransport   -- instances
-- PlasmaLean/Sanity/AuditTransport.lean
mislabelled_not_transportLaws, constField_rejects_source,
cosMode_rejects_edge, slopeField_rejects_axis      -- counterexamples
fakeField_zero_duration, fakeField_not_solution    -- R-1
solution_outside_Tdom                              -- R-2
noDiffusion_frozen                                 -- R-3
```

**Why it is stated this way.** This is the 1-D (flux-surface averaged) transport model used by the Solov'ev temperature-band theorems. Solutions are *supplied*: there is no existence theorem in the kernel, and the headline results quantify over every supplied solution. At a degenerate axis no boundary condition is posed (a Fichera outflow boundary); the edge carries Dirichlet data.

**Audit findings.** **R-1, R-2, R-3 (low, recorded).** R-1: with $\tau = 0$ every value is a time derivative within $\{0\}$, so a false rate is admitted (`fakeField_zero_duration`). R-2: a solution need not stay in the source domain `Tdom` (`solution_outside_Tdom`). R-3: $D \equiv 0$ is allowed, which freezes profiles (`noDiffusion_frozen`). The headline results assume a solution for every $\tau \ge 0$ and barriers inside `Tdom`, so they are unaffected.

---

## 6. Kernel/Fusion: 0-D D-T burn (Minutes 7–9)

```lean
-- PlasmaLean/Kernel/Fusion.lean (381 lines), namespace PlasmaLean.Fusion
def QuasineutralComposition (p : DTPlasma) : Prop :=
  ∃ (k : ℕ) (Z c : Fin k → ℝ), (∀ i, 1 ≤ Z i) ∧ (∀ i, 0 ≤ c i) ∧
    p.fuelFraction + ∑ i, Z i * c i = 1 ∧
    p.fuelFraction + ∑ i, Z i ^ 2 * c i = p.Zeff ∧
    p.ionRatio = p.fuelFraction + ∑ i, c i

class PhysicalPlasma (p : DTPlasma) : Prop where
  n_pos : 0 < p.n
  V_pos : 0 < p.V
  fuel_pos : 0 < p.fuelFraction
  composition : QuasineutralComposition p

class PowerBalance (p : DTPlasma) (sv Paux τE T : ℝ → ℝ) : Prop where
  tauE_pos : ∀ t : ℝ, 0 ≤ t → 0 < τE t
  balance : ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => p.thermalEnergy (T s))
      (p.netHeating sv (Paux t) (τE t) (T t)) (Set.Ici 0) t
-- also: keV, alphaEnergy, bremsCoeff, boschHaleWindows (61 windows), BoschHaleDT
```

**Sanity checks.**

```lean
-- PlasmaLean/Sanity/BoschHaleInstance.lean: instance bhSv_boschHaleDT
-- PlasmaLean/Sanity/Fusion.lean: steady_state_iff, impurity_physical
-- PlasmaLean/Sanity/AuditFusion.lean
keV_eq, neutron_energy, bremsCoeff_matches_NRL   -- constants
boschHaleWindows_contiguous, boschHaleWindows_cover
purePlasma_physical, carbonHeliumPlasma_physical -- instances
inconsistentPlasma_not_physical                   -- F-1 regression
Zeff_ge_of_composition, carbon_values_Zeff_ge
powerBalance_zero_density                         -- F-2
lossPower_zero_tau, bremsPower_of_nonpos          -- F-3
```

**Why it is stated this way.** The constants are exact SI values or cited empirical fits (Bosch–Hale 1992, checked externally to 1 % over 61 windows). `PhysicalPlasma` now derives $Z_{\rm eff} \ge 1$ and the fuel and ion-ratio bounds from an explicit quasineutral species list instead of stating them separately.

**Audit findings.** **F-1 (medium, fixed 30 October).** The old `PhysicalPlasma` accepted fuel fraction 1 with $Z_{\rm eff} = 2$, overstating alpha heating; it now carries `composition : QuasineutralComposition p`, and the old counterexample is `inconsistentPlasma_not_physical`. No numeric result changed. **F-2, F-3 (low, recorded):** `PowerBalance` alone is satisfied by every trajectory when $n = 0$; `lossPower p 0 T = 0` (totalized division) outside `PowerBalance`.

---

## 7. The 30 October strict audit in one page (Minutes 9–10)

```lean
-- notes/audit/2026-10-30-kernel-audit.md (audited commit cda8bd0)
Scope       : PlasmaLean/Kernel/{Equilibrium, Slab, ThermalSlab,
              Transport, Vacuum, Fusion}.lean  (900 lines)
Inventory   : 52 declarations = 28 data definitions, 11 laws (48 fields),
              3 Prop predicates, 10 theorems. Nothing sampled.
Findings    : critical 0, high 0, medium 1 (F-1), low 9, informational 3
New sanity  : PlasmaLean/Sanity/Audit{Equilibrium, ThermalSlab, Vacuum,
              Transport, Fusion}.lean, standard axioms only, no sorry,
              no decide

Status after the 30 October follow-up
  F-1  medium  fixed (QuasineutralComposition in PhysicalPlasma)
  E-1  low     checked: all 14 design users prove g = ∇p
  S-1, T-1, V-1, R-1, R-2, R-3, F-2, F-3   low   recorded, regression theorems
  R-4  low     fixed (plain decide removed)
Model audit (repository finding H-1): definitions behind the headline
  claims re-derived against their sources; MA-M1, MA-M2 resolved
```

**Sanity checks.**

```lean
-- Axiom check over the whole library (after the follow-up):
lake env lean scripts/check_axioms.lean
-- "Axiom audit passed for 47015 PlasmaLean declarations"
-- every declaration depends only on [propext, Classical.choice, Quot.sound]
```

**Why it is stated this way.** The kernel is about 900 lines in six modules. Its laws are hypotheses (`Prop` classes and structures), not axioms, so `#print axioms` on a theorem shows only Lean's standard axioms; what it does *not* show is whether the supplied laws describe the physics. That is what the audit checks: each law is compared with its source, given an instance, a counterexample and risk-specific checks, and each defect gets a regression theorem. Read the full record: [notes/audit/2026-10-30-kernel-audit.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md).

**Audit findings.** **H-1 (high, repository audit; resolved by the model audit).** The model definitions behind the headline claims (`LittlejohnOrbit`, `BoozerField`, `mercierIndex`, `IsFieldLine` and others) were outside the kernel; they were re-derived against Littlejohn, Boozer, Landreman–Jorge and the other sources and match. **MA-M1** (guiding-centre orbits must stay off the magnetic axis) is resolved as far as the ψ > 0 chart allows: orbits exist on the full horizon for a band of births (`alpha_band_orbit_exists_005`) and proved limits show the rest needs coordinates through the axis. **MA-M2** is resolved: 3.5 MeV alpha orbits are constructed (`reactor_alpha_born_confined`, `reactor_alpha_confined_nonvacuous_35MeV`).
