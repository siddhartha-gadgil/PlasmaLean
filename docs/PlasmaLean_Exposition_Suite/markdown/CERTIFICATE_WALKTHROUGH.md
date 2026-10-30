# Anatomy of a field-error and clearance certificate: the two-loop calibration fixture

This walkthrough traces how PlasmaLean proves an engineering-style guarantee for a small **calibration fixture**: two coaxial circular filaments of radius 0.1 m in the planes z = ±0.2 m. It certifies field bounds, a field-error budget under manufacturing and current errors, and coil clearance. The loops are axisymmetric, so the fixture has no rotational transform and makes **no confinement claim**; it is not a toroidal confinement design. The coefficients are an invented exact test fixture, and the tolerance budget (1 mm position, 1 mm per radian tangent, 1 % current, 5 mm tubes) is a design input, not a measured capability.

Modules: [`Design/VacuumPair`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/VacuumPair.lean), [`Design/VacuumTolerance`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/VacuumTolerance.lean), [`Design/VacuumDerivative`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/VacuumDerivative.lean), [`Design/VacuumPairVolumeError`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/VacuumPairVolumeError.lean), [`Theory/Fields/BiotSavart`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/BiotSavart.lean), [`Theory/Fields/CoilPerturbation`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Fields/CoilPerturbation.lean), [`Theory/Geometry/CoilTube`](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/CoilTube.lean). All declarations below are real (abridged where marked `...`).

---

## Stage 1: Fixture geometry and clearance

The fixture is two coaxial circular filaments of radius $0.1$ m in the planes $z = \pm 0.2$ m, with currents $I, J$ and permeability $\mu_0$ kept as parameters. The observation region is the whole closed ball $\|x\| \le 0.05$ m (not a sample of points). The coils are closed, simple and regular, every pair of centreline points is at least $0.4$ m apart, and every observation point is at least $0.15$ m from either filament. The coefficients are an invented exact test fixture, not experimental data.

```lean
-- PlasmaLean/Design/VacuumPair.lean (namespace PlasmaLean.Design.VacuumPair)
def upperCoil : ℝ → Space := circularCoil (1 / 10) (1 / 5)
def lowerCoil : ℝ → Space := circularCoil (1 / 10) (-1 / 5)
def ObservationRegion (x : Space) : Prop := ‖x‖ ≤ 1 / 20
theorem origin_in_region : ObservationRegion 0
theorem closed_coils : Function.Periodic upperCoil (2 * Real.pi) ∧ ...
theorem simple_coils : Set.InjOn upperCoil (Set.Ico 0 (2 * Real.pi)) ∧ ...
theorem regular_coils (t : ℝ) : ‖deriv upperCoil t‖ = 1 / 10 ∧ ...
theorem coil_clearance (t u : ℝ) : 2 / 5 ≤ dist (upperCoil t) (lowerCoil u)
theorem source_clearance (x : Space) (hx : ObservationRegion x) (t : ℝ) :
    3 / 20 ≤ ‖x - upperCoil t‖ ∧ 3 / 20 ≤ ‖x - lowerCoil t‖
```

**Takeaway.** The clearance $\|x - \gamma(t)\| \ge 0.15$ m is proved for every point of the ball, so the Biot–Savart denominator never vanishes there and no division-by-zero convention ($x/0 = 0$ in Lean) can enter the field bounds. The region is nonempty (`origin_in_region`), so the bounds are not vacuous.

---

## Stage 2: Biot–Savart field, bounds and derivatives

The field is the sum of two filament integrals
$$B(x) = \frac{\mu_0 I}{4\pi}\int_0^{2\pi} \frac{\gamma'(t) \times (x - \gamma(t))}{\|x - \gamma(t)\|^3}\,dt + (\text{lower coil}).$$
Integrability is proved, not assumed. On the whole ball $\|B\| \le \tfrac{20}{9}(|\mu_0 I| + |\mu_0 J|)$, the midpoint field is computed exactly (an independent check of normalization and sign), and the field is differentiable with an explicit operator-norm bound on its derivative.

```lean
-- PlasmaLean/Theory/Fields/BiotSavart.lean (namespace PlasmaLean.Fields)
def filamentField (μ₀ I : ℝ) (c : ℝ → Space) (a b : ℝ) (x : Space) : Space :=
  (μ₀ * I / (4 * Real.pi)) • ∫ t in a..b, filamentKernel c t x
-- PlasmaLean/Design/VacuumPair.lean
def field (μ₀ I J : ℝ) (x : Space) : Space :=
  filamentField μ₀ I upperCoil 0 (2 * Real.pi) x +
    filamentField μ₀ J lowerCoil 0 (2 * Real.pi) x
theorem integrable_kernels (x : Space) (hx : ObservationRegion x) : ...
theorem field_bound (μ₀ I J : ℝ) (x : Space) (hx : ObservationRegion x) :
    ‖field μ₀ I J x‖ ≤ 20 / 9 * (|μ₀ * I| + |μ₀ * J|)
theorem midpoint_field (μ₀ I : ℝ) :
    field μ₀ I I 0 = axisPoint (μ₀ * I / (100 * Real.sqrt (1 / 20) ^ 3))
-- PlasmaLean/Theory/Fields/FieldDerivative.lean: filamentField_derivative
-- PlasmaLean/Design/VacuumDerivative.lean: manufactured_field_derivative
```

**Takeaway.** The derivative is a genuine Fréchet derivative, obtained by dominated differentiation under the integral; its bound uses the same clearance as Stage 1.

---

## Stage 3: Manufacturing envelope and field-error budget

An actual coil is within tolerance of a nominal one if it is $C^1$, closed, and within $1$ mm in position and $1$ mm per radian in tangent, at every parameter. For both coils manufactured at once, and currents within $1\,\%$ of $I$, the field error at *every* point of the $5$ cm ball is at most a quarter of $\mu_0 I$ (in tesla when $\mu_0 I$ is in T·m):
$$\|B_{\rm actual}(x) - B_{\rm nominal}(x)\| \le \tfrac14\,\mu_0 I.$$

```lean
-- PlasmaLean/Design/VacuumTolerance.lean
structure WithinTolerance (nominal actual : ℝ → Space) : Prop where
  differentiable : Differentiable ℝ actual
  tangent_continuous : Continuous (deriv actual)
  closed : Function.Periodic actual (2 * Real.pi)
  position : ∀ t, ‖actual t - nominal t‖ ≤ 1 / 1000
  tangent : ∀ t, ‖deriv actual t - deriv nominal t‖ ≤ 1 / 1000
theorem circle_within_tolerance ...   -- the envelope is nonempty
theorem manufacturing_error ... :
    ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ J₁ J₂ x‖ ≤
      135 / 1372 * (|μ₀ * J₁| + |μ₀ * J₂|)
theorem field_current_error ...
theorem combined_field_error {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I) ...
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100)
    (x : Space) (hx : ObservationRegion x) :
    ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤ (μ₀ * I) / 4
-- per-filament engine: Theory/Fields/CoilPerturbation.filamentField_perturbation
```

**Takeaway.** The quantifier is over every pair of $C^1$ coil curves in the envelope (an infinite-dimensional set), not over sampled perturbations. The budget numbers are design inputs, not measured manufacturing capabilities.

---

## Stage 4: From the boundary of a cube to its interior

Both the nominal and every manufactured field are vacuum fields (kernel `VacuumField`) on a ball around the cube $|x_k| < 2.5$ cm. The difference of two vacuum fields is a vacuum field, and $|B|^2$ of a vacuum field is subharmonic (Bochner identity), so a bound on the frontier of the cube holds throughout the closed cube (weak maximum principle). Bounds at $6(N+1)^2$ grid points on the faces, plus a certified Lipschitz constant, give a bound in the whole cube.

```lean
-- PlasmaLean/Theory/Fields/Subharmonic.lean
theorem VacuumField.error_le_of_frontier ...
-- PlasmaLean/Design/VacuumPairVolumeError.lean
theorem manufactured_vacuumField (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space) ...
theorem volume_error_of_frontier ... (hM : ∀ y ∈ frontier openCube,
      ‖manufacturedField μ₀ J₁ J₂ upper lower y - field μ₀ I I y‖ ≤ δ) :
    ∀ x ∈ closedCube, ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤ δ
theorem combined_volume_error ...
theorem volume_error_of_boundary_samples ...   -- ‖ΔB‖ ≤ m + L/(20N) in the cube
```

**Takeaway.** This turns finitely many boundary values (measured or separately certified) into a statement about every interior point, with the discretization error accounted for explicitly.

---

## Stage 5: What the assembled certificate says, and what it does not

For the same manufactured coils and calibrated currents: the axial field component is at least $\mu_0 I/4$, so the field is nonzero, throughout a $1$ mm probe ball; and with $5$ mm tube envelopes around both actual coils, every point of one tube is at least $388$ mm from every point of the other. The loops are axisymmetric: the fixture has no rotational transform and confines nothing. It is a calibration fixture for the field-error and clearance pipeline, not a toroidal confinement design.

```lean
-- PlasmaLean/Design/VacuumTolerance.lean
theorem robust_probe_field {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100)
    (x : Space) (hx : ‖x‖ ≤ 1 / 1000) :
    (μ₀ * I) / 4 ≤ (manufacturedField μ₀ J₁ J₂ upper lower x) 2 ∧
      manufacturedField μ₀ J₁ J₂ upper lower x ≠ 0
theorem manufactured_tube_clearance (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    {x y : Space} (hx : x ∈ CoilTube upper (1 / 200))
    (hy : y ∈ CoilTube lower (1 / 200)) : 97 / 250 ≤ dist x y
```

**Takeaway.** Not claimed: an invariant torus, a normal-field error on a plasma boundary, plasma confinement, finite-conductor or Maxwell (time-dependent) effects, embedded winding packs, or hardware qualification. Coil-produced confinement for a stellarator-type field is a separate, open goal (G-5).
