/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Constructions

/-!
# Radial (flux-surface-averaged) heat transport: KERNEL

**This is the kernel file for radial heat transport (implementation plan §2.1, track T3).**
It is a domain kernel, not an extension of Lean's logical kernel, and it adds no axioms.

## Model

The radial coordinate `ψ ∈ [0,1]` is a normalized flux label (for instance the normalized
toroidal flux), so that the volume derivative `V'(ψ)` is positive up to the magnetic axis
`ψ = 0`. The flux-surface-averaged temperature `T(ψ,t)` obeys the semilinear transport
equation `∂ₜT = N[T]`, where
`N[T] = (1/V') ∂ψ (V' D ∂ψ T) + R(ψ,T)`.
Here `D(ψ) ≥ 0` is a supplied (temperature-independent) diffusivity and
`R = heating − losses` is a supplied net source, posed for temperatures in an open set
`Tdom` (e.g. `T > 0`). The boundary conditions are:
* at the edge, Dirichlet data `T(1,t) = T_edge(t)`;
* at the axis, a condition that depends on the coordinate (`AxisKind`):
  - `regular`: the no-flux (Neumann/symmetry) condition `∂ψT(0,t) = 0`;
  - `degenerate`: `D(0) = 0` (as for `D = χ⟨|∇ψ|²⟩` when `ψ ∝ r²` near the axis) and **no**
    axis condition. Since `D ≥ 0` and `D(0) = 0`, the drift `D'(0) ≥ 0`, so the
    characteristics of the reduced equation `∂ₜT = D'(0) ∂ψT + R` at `ψ = 0` run toward the
    axis: it is an outflow boundary (Fichera), where no condition may be prescribed.

## Lean encoding

* `AxisKind` is the choice of axis condition, and `RadialCoefficients` bundles the data `V'`,
  `V''`, `D`, `D'`, `R`, the source domain `Tdom` and the axis kind. The operator is stored in
  *expanded* form
  `RadialCoefficients.op c ψ u uψ uψψ = D uψψ + (D' + D V''/V') uψ + R(ψ,u)`, evaluated at a
  value, slope and curvature. The sanity module proves that it agrees with the divergence form.
* `RadialField` bundles a space-time field together with its *supplied* partial derivatives
  `Tψ`, `Tψψ`, `Tₜ`. They are connected to `T` only by the hypotheses below.
* `RadialField.Regular τ u` asks for joint continuity on `[0,1] × [0,τ]`, two one-sided
  (within `[0,1]`) spatial derivatives and one (within `[0,τ]`) time derivative at every point
  of the closed rectangle. This is a classical solution up to the boundary. We do **not**
  require continuity of `Tψψ` or `Tₜ`; theorems using only these weaker hypotheses are stronger.
* `TransportLaws c` (a typeclass) records the coefficient laws: `V' > 0`, `D ≥ 0`, `D(0) = 0`
  for a degenerate axis, supplied derivatives of `V'` and `D`, `Tdom` open, and continuity of
  `R` on `[0,1] × Tdom`.
* `ClassicalRadialSolution c T_edge τ u` (a typeclass) records that `u` is a classical solution
  on `[0,1] × [0,τ]` with the edge condition, and with the Neumann axis condition when the axis
  is `regular`; `RadialHeatTransport` combines it with `TransportLaws`.

Existence of solutions is **not** asserted: solutions are supplied, and every theorem built
on this kernel is conditional on such a supplied solution. Derivatives of the coefficients at
`ψ = 0, 1` are one-sided (within `[0,1]`).

## Kernel change (2026-10-20)

Previous version: `RadialCoefficients` had a field `Dmin`, `TransportLaws` required
`0 < Dmin ≤ D` on `[0,1]` and `R` continuous on `[0,1] × ℝ`, and `ClassicalRadialSolution`
always imposed `∂ψT(0,t) = 0`. Changes, and why:

* **`D ≥ 0` replaces `D ≥ Dmin > 0`** (field `Dmin` removed; the old floor survives as the
  optional predicate `RadialCoefficients.UniformlyParabolic`). In the normalized toroidal
  flux `ψ ∝ r²` near the axis, `⟨|∇ψ|²⟩ ∝ ψ`, so `D = χ⟨|∇ψ|²⟩` vanishes at the axis and no
  floor `Dmin > 0` can hold: the old kernel excluded the physically standard coordinate (the
  M2 barrier of `Design.TransportBarrier` had to bypass it). All comparison proofs only use
  `D ≥ 0` (the floor matters for existence and strong maximum principles, which are not
  formalized).
* **Axis condition choice `AxisKind`** (new field `axis`). With `D(0) = 0` the Neumann
  condition is not the natural regularity condition (a smooth profile `T₀ − c r²` has
  `∂ψT(0) = −c a² ≠ 0`) and would over-determine the problem; the `degenerate` kind imposes
  `D(0) = 0` as a law and no axis condition on solutions. The `regular` kind keeps the old
  Neumann condition, so old models are recovered with `axis := .regular`.
* **Law `axis = regular → D(0) > 0`** (new), so the two kinds are distinguished by the
  coefficients and a degenerate coordinate cannot be mislabelled `regular`.
* **Source domain `Tdom`** (new field). Physical sources (alpha heating with a reactivity
  defined for `T > 0`, bremsstrahlung `∝ √T`) are only continuous for `T > 0`; requiring
  continuity on all of `ℝ` excluded them. Old models are recovered with `Tdom := univ`.
-/

public section

namespace PlasmaLean.Transport

open Set

/-- Choice of axis condition, determined by the radial coordinate.
* `regular`: the axis is a symmetry boundary; solutions satisfy `∂ψT(0,t) = 0`.
* `degenerate`: the diffusivity vanishes at the axis, `D(0) = 0` (e.g. `ψ ∝ r²`); no axis
  condition is imposed (outflow boundary). -/
inductive AxisKind where
  /-- Regular (symmetry) axis with the Neumann condition `∂ψT(0,t) = 0`. -/
  | regular
  /-- Degenerate axis `D(0) = 0`, no axis condition. -/
  | degenerate
  deriving DecidableEq

/-- Coefficient data of the radial transport operator: volume derivative `Vp = V'`, its
derivative `dVp = V''`, diffusivity `D`, its derivative `dD`, net source
`R(ψ,T) = heating − losses`, the open set `Tdom` of temperatures on which the source law is
posed, and the axis kind. -/
structure RadialCoefficients where
  /-- Volume derivative `V'(ψ)` of the flux coordinate. -/
  Vp : ℝ → ℝ
  /-- Supplied derivative `V''(ψ)`. -/
  dVp : ℝ → ℝ
  /-- Radial heat diffusivity `D(ψ)` (independent of the temperature: semilinear case). -/
  D : ℝ → ℝ
  /-- Supplied derivative `D'(ψ)`. -/
  dD : ℝ → ℝ
  /-- Net heating `R(ψ,T) = heating − losses`. -/
  R : ℝ → ℝ → ℝ
  /-- Temperatures for which the source law is posed (an open set, e.g. `T > 0`). -/
  Tdom : Set ℝ
  /-- The axis condition appropriate to the coordinate. -/
  axis : AxisKind

/-- The transport operator in expanded form, evaluated at the value `u`, slope `uψ` and
curvature `uψψ` of a profile at `ψ`:
`D uψψ + (D' + D V''/V') uψ + R(ψ,u)`, i.e. `(1/V') (V' D u')' + R(ψ,u)`. -/
@[expose] noncomputable def RadialCoefficients.op (c : RadialCoefficients) (ψ u uψ uψψ : ℝ) : ℝ :=
  c.D ψ * uψψ + (c.dD ψ + c.D ψ * c.dVp ψ / c.Vp ψ) * uψ + c.R ψ u

/-- Optional (not a kernel law): the diffusivity is bounded below by `Dmin > 0` on `[0,1]`.
This was a kernel law before the 2026-10-20 change; it fails for every coordinate with
`D(0) = 0`. -/
@[expose] def RadialCoefficients.UniformlyParabolic (c : RadialCoefficients) (Dmin : ℝ) : Prop :=
  0 < Dmin ∧ ∀ ψ ∈ Icc (0 : ℝ) 1, Dmin ≤ c.D ψ

/-- A space-time field `T(ψ,t)` with supplied partial derivatives `Tψ`, `Tψψ`, `Tt`. -/
structure RadialField where
  /-- The field `T(ψ,t)`. -/
  T : ℝ → ℝ → ℝ
  /-- Supplied first radial derivative. -/
  Tψ : ℝ → ℝ → ℝ
  /-- Supplied second radial derivative. -/
  Tψψ : ℝ → ℝ → ℝ
  /-- Supplied time derivative. -/
  Tt : ℝ → ℝ → ℝ

/-- Classical regularity of a field on the closed rectangle `[0,1] × [0,τ]`: joint continuity,
and the supplied partial derivatives are genuine one-sided derivatives (within `[0,1]` in `ψ`,
within `[0,τ]` in `t`) at every point of the rectangle. -/
structure RadialField.Regular (τ : ℝ) (u : RadialField) : Prop where
  /-- Joint continuity on the closed space-time rectangle. -/
  cont : ContinuousOn (fun p : ℝ × ℝ => u.T p.1 p.2) (Icc 0 1 ×ˢ Icc 0 τ)
  /-- `Tψ` is the radial derivative of `T`. -/
  deriv_ψ : ∀ t ∈ Icc 0 τ, ∀ ψ ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt (fun x => u.T x t) (u.Tψ ψ t) (Icc 0 1) ψ
  /-- `Tψψ` is the radial derivative of `Tψ`. -/
  deriv_ψψ : ∀ t ∈ Icc 0 τ, ∀ ψ ∈ Icc (0 : ℝ) 1,
    HasDerivWithinAt (fun x => u.Tψ x t) (u.Tψψ ψ t) (Icc 0 1) ψ
  /-- `Tt` is the time derivative of `T`. -/
  deriv_t : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    HasDerivWithinAt (fun s => u.T ψ s) (u.Tt ψ t) (Icc 0 τ) t

/-- Supplied laws for the transport coefficients on `[0,1]`: positive volume derivative,
nonnegative diffusivity vanishing at a degenerate axis and positive at a regular one, the
supplied coefficient derivatives are genuine (one-sided at the ends), and the net source is
jointly continuous on `[0,1] × Tdom` with `Tdom` open. (Kernel change 2026-10-20: `D ≥ 0` replaces
`D ≥ Dmin > 0`; see the module documentation.) -/
class TransportLaws (c : RadialCoefficients) : Prop where
  /-- `V' > 0` up to the axis. -/
  Vp_pos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.Vp ψ
  /-- `dVp` is the derivative of `Vp`. -/
  Vp_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c.Vp (c.dVp ψ) (Icc 0 1) ψ
  /-- `dD` is the derivative of `D`. -/
  D_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c.D (c.dD ψ) (Icc 0 1) ψ
  /-- `D ≥ 0` on `[0,1]` (degenerate diffusion allowed). -/
  D_nonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ
  /-- At a degenerate axis the diffusivity vanishes. -/
  D_axis : c.axis = .degenerate → c.D 0 = 0
  /-- At a regular axis the diffusivity is positive (so a coordinate with `D(0) = 0` cannot
  be declared `regular`, which would make the Neumann condition over-determine the problem). -/
  D_axis_regular : c.axis = .regular → 0 < c.D 0
  /-- The source domain is open. -/
  Tdom_open : IsOpen c.Tdom
  /-- The net source `R` is jointly continuous on `[0,1] × Tdom`. -/
  R_cont : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ c.Tdom)

/-- `u` is a supplied classical solution of `∂ₜT = N[T]` on `[0,1] × [0,τ]` with edge
Dirichlet data `T(1,t) = T_edge(t)` and, for a `regular` axis, the no-flux condition
`∂ψT(0,t) = 0` (no axis condition for a `degenerate` axis). -/
class ClassicalRadialSolution (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop where
  /-- The time horizon is nonnegative. -/
  tau_nonneg : 0 ≤ τ
  /-- Classical regularity on the closed rectangle. -/
  regular : u.Regular τ
  /-- The transport equation holds pointwise, including at the axis and the edge. -/
  pde : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    u.Tt ψ t = c.op ψ (u.T ψ t) (u.Tψ ψ t) (u.Tψψ ψ t)
  /-- No-flux condition at a regular magnetic axis. -/
  axis : c.axis = .regular → ∀ t ∈ Icc 0 τ, u.Tψ 0 t = 0
  /-- Edge Dirichlet condition. -/
  edge : ∀ t ∈ Icc 0 τ, u.T 1 t = Tedge t

/-- A supplied classical solution of the radial heat transport problem whose coefficients
obey the transport laws. -/
class RadialHeatTransport (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop extends TransportLaws c, ClassicalRadialSolution c Tedge τ u

/-- A uniformly parabolic diffusivity (the pre-2026-10-20 kernel law) is nonnegative. -/
theorem RadialCoefficients.UniformlyParabolic.D_nonneg {c : RadialCoefficients} {Dmin : ℝ}
    (h : c.UniformlyParabolic Dmin) : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ := fun ψ hψ =>
  h.1.le.trans (h.2 ψ hψ)

/-- A uniformly parabolic diffusivity does not vanish at the axis, so a degenerate axis
(`D(0) = 0`) is never uniformly parabolic. -/
theorem RadialCoefficients.UniformlyParabolic.D_axis_pos {c : RadialCoefficients} {Dmin : ℝ}
    (h : c.UniformlyParabolic Dmin) : 0 < c.D 0 :=
  h.1.trans_le (h.2 0 ⟨le_rfl, zero_le_one⟩)

end PlasmaLean.Transport
