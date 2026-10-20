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

The radial coordinate `ψ ∈ [0,1]` is the normalized toroidal flux, so that the volume
derivative `V'(ψ)` is positive and smooth up to the magnetic axis `ψ = 0`. The
flux-surface-averaged temperature `T(ψ,t)` obeys the semilinear transport equation
`∂ₜT = N[T]`, where
`N[T] = (1/V') ∂ψ (V' D ∂ψ T) + R(ψ,T)`.
Here `D(ψ) > 0` is a supplied (temperature-independent) diffusivity and `R = heating − losses`
is a supplied net source. The boundary conditions are:
* at the axis, the no-flux (Neumann/regularity) condition `∂ψT(0,t) = 0`;
* at the edge, Dirichlet data `T(1,t) = T_edge(t)`.

## Lean encoding

* `RadialCoefficients` bundles the data `V'`, `V''`, `D`, `D'`, `R` and a diffusivity floor
  `Dmin`. The operator is stored in *expanded* form
  `RadialCoefficients.op c ψ u uψ uψψ = D uψψ + (D' + D V''/V') uψ + R(ψ,u)`, evaluated at a
  value, slope and curvature. The sanity module proves that it agrees with the divergence form.
* `RadialField` bundles a space-time field together with its *supplied* partial derivatives
  `Tψ`, `Tψψ`, `Tₜ`. They are connected to `T` only by the hypotheses below.
* `RadialField.Regular τ u` asks for joint continuity on `[0,1] × [0,τ]`, two one-sided
  (within `[0,1]`) spatial derivatives and one (within `[0,τ]`) time derivative at every point
  of the closed rectangle. This is a classical solution up to the boundary. We do **not**
  require continuity of `Tψψ` or `Tₜ`; theorems using only these weaker hypotheses are stronger.
* `TransportLaws c` (a typeclass) records the coefficient laws: `V' > 0`, `D ≥ Dmin > 0`,
  supplied derivatives of `V'` and `D`, and continuity of `R`.
* `ClassicalRadialSolution c T_edge τ u` (a typeclass) records that `u` is a classical solution
  on `[0,1] × [0,τ]` with the axis and edge conditions; `RadialHeatTransport` combines it with
  `TransportLaws`.

Existence of solutions is **not** asserted: solutions are supplied, and every theorem built
on this kernel is conditional on such a supplied solution. Derivatives of the coefficients at
`ψ = 0, 1` are one-sided (within `[0,1]`).
-/

public section

namespace PlasmaLean.Transport

open Set

/-- Coefficient data of the radial transport operator: volume derivative `Vp = V'`, its
derivative `dVp = V''`, diffusivity `D`, its derivative `dD`, net source
`R(ψ,T) = heating − losses`, and a diffusivity floor `Dmin`. -/
structure RadialCoefficients where
  /-- Volume derivative `V'(ψ)` of the normalized toroidal flux coordinate. -/
  Vp : ℝ → ℝ
  /-- Supplied derivative `V''(ψ)`. -/
  dVp : ℝ → ℝ
  /-- Radial heat diffusivity `D(ψ)` (independent of the temperature: semilinear case). -/
  D : ℝ → ℝ
  /-- Supplied derivative `D'(ψ)`. -/
  dD : ℝ → ℝ
  /-- Net heating `R(ψ,T) = heating − losses`. -/
  R : ℝ → ℝ → ℝ
  /-- Lower bound for the diffusivity. -/
  Dmin : ℝ

/-- The transport operator in expanded form, evaluated at the value `u`, slope `uψ` and
curvature `uψψ` of a profile at `ψ`:
`D uψψ + (D' + D V''/V') uψ + R(ψ,u)`, i.e. `(1/V') (V' D u')' + R(ψ,u)`. -/
@[expose] noncomputable def RadialCoefficients.op (c : RadialCoefficients) (ψ u uψ uψψ : ℝ) : ℝ :=
  c.D ψ * uψψ + (c.dD ψ + c.D ψ * c.dVp ψ / c.Vp ψ) * uψ + c.R ψ u

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
diffusivity bounded below by `Dmin > 0`, the supplied coefficient derivatives are genuine
(one-sided at the ends), and the net source is jointly continuous. -/
class TransportLaws (c : RadialCoefficients) : Prop where
  /-- `V' > 0` up to the axis (normalized toroidal flux). -/
  Vp_pos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.Vp ψ
  /-- `dVp` is the derivative of `Vp`. -/
  Vp_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c.Vp (c.dVp ψ) (Icc 0 1) ψ
  /-- `dD` is the derivative of `D`. -/
  D_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c.D (c.dD ψ) (Icc 0 1) ψ
  /-- The diffusivity floor is positive. -/
  Dmin_pos : 0 < c.Dmin
  /-- `D ≥ Dmin` on `[0,1]`. -/
  D_lower : ∀ ψ ∈ Icc (0 : ℝ) 1, c.Dmin ≤ c.D ψ
  /-- The net source `R` is jointly continuous on `[0,1] × ℝ`. -/
  R_cont : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ univ)

/-- `u` is a supplied classical solution of `∂ₜT = N[T]` on `[0,1] × [0,τ]` with the axis
no-flux condition `∂ψT(0,t) = 0` and edge Dirichlet data `T(1,t) = T_edge(t)`. -/
class ClassicalRadialSolution (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop where
  /-- The time horizon is nonnegative. -/
  tau_nonneg : 0 ≤ τ
  /-- Classical regularity on the closed rectangle. -/
  regular : u.Regular τ
  /-- The transport equation holds pointwise, including at the axis and the edge. -/
  pde : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    u.Tt ψ t = c.op ψ (u.T ψ t) (u.Tψ ψ t) (u.Tψψ ψ t)
  /-- No-flux (regularity) condition at the magnetic axis. -/
  axis : ∀ t ∈ Icc 0 τ, u.Tψ 0 t = 0
  /-- Edge Dirichlet condition. -/
  edge : ∀ t ∈ Icc 0 τ, u.T 1 t = Tedge t

/-- A supplied classical solution of the radial heat transport problem whose coefficients
obey the transport laws. -/
class RadialHeatTransport (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop extends TransportLaws c, ClassicalRadialSolution c Tedge τ u

/-- Under the transport laws the diffusivity is nonnegative on `[0,1]`. -/
theorem TransportLaws.D_nonneg (c : RadialCoefficients) [TransportLaws c] :
    ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ := fun ψ hψ =>
  (TransportLaws.Dmin_pos (c := c)).le.trans (TransportLaws.D_lower ψ hψ)

end PlasmaLean.Transport
