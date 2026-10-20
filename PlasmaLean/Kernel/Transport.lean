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
`N[T] = (1/V') ∂ψ (V' D(ψ,T) ∂ψ T) + R(ψ,T)`.
Here `D(ψ,T) ≥ 0` is a supplied diffusivity that may depend on the temperature
(quasilinear transport, e.g. gyro-Bohm-like `χ ∝ T^{3/2}`; kernel change K2 below) and
`R = heating − losses` is a supplied net source, posed for temperatures in an open set
`Tdom` (e.g. `T > 0`). The boundary conditions are:
* at the edge, Dirichlet data `T(1,t) = T_edge(t)`;
* at the axis, a condition that depends on the coordinate (`AxisKind`):
  - `regular`: the no-flux (Neumann/symmetry) condition `∂ψT(0,t) = 0`;
  - `degenerate`: `D(0,T) = 0` for every `T` (as for `D = χ⟨|∇ψ|²⟩` when `ψ ∝ r²` near the
    axis) and **no** axis condition. Since `D ≥ 0` and `D(0,·) = 0`, the drift
    `∂ψD(0,T) ≥ 0` and `∂T D(0,T) = 0`, so the characteristics of the reduced equation
    `∂ₜT = ∂ψD(0,T) ∂ψT + R` at `ψ = 0` run toward the axis: it is an outflow boundary
    (Fichera), where no condition may be prescribed.

## Lean encoding

* `AxisKind` is the choice of axis condition, and `RadialCoefficients` bundles the data `V'`,
  `V''`, `D(ψ,T)`, its partial derivatives `∂ψD` (`dD`) and `∂T D` (`dDT`), `R`, the source
  domain `Tdom` and the axis kind. The operator is stored in *expanded* form
  `RadialCoefficients.op c ψ u uψ uψψ = D(ψ,u) uψψ + (∂ψD(ψ,u) + ∂TD(ψ,u) uψ + D(ψ,u) V''/V') uψ
  + R(ψ,u)`, evaluated at a value, slope and curvature (the chain rule
  `d/dψ D(ψ,T(ψ)) = ∂ψD + ∂TD · T'` produces the `∂TD · uψ` term). The sanity module proves
  that it agrees with the divergence form `(1/V')(V' D(ψ,T(ψ)) T')' + R` **whenever**
  `ψ ↦ D(ψ, T(ψ))` obeys the chain rule `∂ψD + ∂TD · T'` (`Sanity.op_divergence_form` takes
  this as a hypothesis; it holds for separable `D = a(ψ) b(T)` and for jointly `C¹` `D`, but
  the separate partial-derivative laws `D_deriv`, `DT_deriv` below do not imply it in general).
  `RadialCoefficients.semilinear` builds coefficients
  with a temperature-independent `D(ψ)` (the pre-K2 kernel), and `IsSemilinear` recognizes
  them.
* `RadialField` bundles a space-time field together with its *supplied* partial derivatives
  `Tψ`, `Tψψ`, `Tₜ`. They are connected to `T` only by the hypotheses below.
* `RadialField.Regular τ u` asks for joint continuity on `[0,1] × [0,τ]`, two one-sided
  (within `[0,1]`) spatial derivatives and one (within `[0,τ]`) time derivative at every point
  of the closed rectangle. This is a classical solution up to the boundary. We do **not**
  require continuity of `Tψψ` or `Tₜ`; theorems using only these weaker hypotheses are stronger.
* `TransportLaws c` (a typeclass) records the coefficient laws: `V' > 0`, `D ≥ 0`, `D(0,·) = 0`
  for a degenerate axis, supplied derivatives of `V'` and (both partial derivatives) of `D`,
  `Tdom` open, and continuity of `R` on `[0,1] × Tdom`.
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

## Kernel change (2026-10-20, K2): quasilinear diffusivity `D(ψ,T)`

Previous version (after the first 2026-10-20 change): `D dD : ℝ → ℝ` (temperature-independent,
semilinear operator `D uψψ + (D' + D V''/V') uψ + R`), laws `D_deriv`, `D_nonneg`, `D_axis`,
`D_axis_regular` stated for `D(ψ)`. Changes, and why (`notes/theory/transport-mhd-coupling.md`
§3.2–§4):

* **`D : ℝ → ℝ → ℝ`, `dD : ℝ → ℝ → ℝ` (= `∂ψD`), new field `dDT : ℝ → ℝ → ℝ` (= `∂TD`)**, and
  the operator gains the chain-rule term `∂TD(ψ,u) · uψ²`. With a temperature-independent `χ`
  every ignited configuration runs away, and a two-sided band (lower *and* upper barrier) with
  fixed `χ` forces `Q ≤ ≈ 6` (0-D obstruction, note §3.2 Finding 2); realistic transport
  (`χ` increasing with `T`, gyro-Bohm-like) is quasilinear.
* **Laws** now quantify over all temperatures: `D_nonneg : 0 ≤ D(ψ,T)`, `D_axis :
  D(0,T) = 0` (degenerate axis), `D_axis_regular : 0 < D(0,T)` (regular axis), `D_deriv`
  (the `ψ`-partial derivative, one-sided within `[0,1]`, for every `T`), and the new law
  `DT_deriv` (`dDT ψ T` is the `T`-derivative of `T ↦ D(ψ,T)`, so the `T`-dependence is
  differentiable, in particular continuous). These are separate partial derivatives: no joint
  regularity law is imposed (it would exclude the existing flux-geometry instances, whose
  `g'` is only a derivative), so the identification of the expanded operator with the
  divergence form needs the chain rule for `ψ ↦ D(ψ,T(ψ))` as an extra hypothesis
  (`Sanity.op_divergence_form`). Requiring `D ≥ 0` for *all* `T` (not only on
  `Tdom`) is harmless: a law posed for `T > 0` (e.g. `T^{3/2}`) is extended by any nonnegative
  continuation; the comparison argument evaluates `D` at values of the solution.
* **Comparison proofs are unchanged in substance**: at a first touching point `u = S`,
  `u_ψ = S_ψ`, so `D(ψ,u)`, `∂ψD(ψ,u)` and `∂TD(ψ,u) uψ` coincide for the two functions and
  only `D(ψ,u) (u_ψψ − S_ψψ) ≥ 0` remains; at a degenerate axis `D(0,·) ≡ 0` forces
  `∂TD(0,·) = 0` (`Comparison.DegenerateAxis`). The *margin* theorems need, in addition,
  continuity of the operator in the value argument along the barrier (automatic for
  semilinear coefficients; see `Comparison.OpShiftControl`).
* **Old models are recovered** with `RadialCoefficients.semilinear Vp dVp D dD R Tdom axis`
  (`D(ψ,T) := D ψ`, `∂ψD := dD ψ`, `∂TD := 0`), whose operator is literally the old one
  (`RadialCoefficients.semilinear_op`).
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
derivative `dVp = V''`, diffusivity `D(ψ,T)`, its partial derivatives `dD = ∂ψD` and
`dDT = ∂TD`, net source `R(ψ,T) = heating − losses`, the open set `Tdom` of temperatures on
which the source law is posed, and the axis kind. (Kernel change K2: `D` depends on `T`.) -/
structure RadialCoefficients where
  /-- Volume derivative `V'(ψ)` of the flux coordinate. -/
  Vp : ℝ → ℝ
  /-- Supplied derivative `V''(ψ)`. -/
  dVp : ℝ → ℝ
  /-- Radial heat diffusivity `D(ψ,T)` (quasilinear; temperature-independent in the
  semilinear case `RadialCoefficients.semilinear`). -/
  D : ℝ → ℝ → ℝ
  /-- Supplied partial derivative `∂ψD(ψ,T)`. -/
  dD : ℝ → ℝ → ℝ
  /-- Supplied partial derivative `∂TD(ψ,T)`. -/
  dDT : ℝ → ℝ → ℝ
  /-- Net heating `R(ψ,T) = heating − losses`. -/
  R : ℝ → ℝ → ℝ
  /-- Temperatures for which the source law is posed (an open set, e.g. `T > 0`). -/
  Tdom : Set ℝ
  /-- The axis condition appropriate to the coordinate. -/
  axis : AxisKind

/-- The transport operator in expanded form, evaluated at the value `u`, slope `uψ` and
curvature `uψψ` of a profile at `ψ`:
`D(ψ,u) uψψ + (∂ψD(ψ,u) + ∂TD(ψ,u) uψ + D(ψ,u) V''/V') uψ + R(ψ,u)`, i.e.
`(1/V') (V' D(ψ,u) u')' + R(ψ,u)` by the chain rule. -/
@[expose] noncomputable def RadialCoefficients.op (c : RadialCoefficients) (ψ u uψ uψψ : ℝ) : ℝ :=
  c.D ψ u * uψψ + (c.dD ψ u + c.dDT ψ u * uψ + c.D ψ u * c.dVp ψ / c.Vp ψ) * uψ + c.R ψ u

/-- **Semilinear coefficients** (the pre-K2 kernel): a temperature-independent diffusivity
`D(ψ)` with derivative `dD(ψ)`, so `D(ψ,T) := D ψ`, `∂ψD := dD ψ`, `∂TD := 0`. -/
@[expose] def RadialCoefficients.semilinear (Vp dVp D dD : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (Tdom : Set ℝ) (axis : AxisKind) : RadialCoefficients :=
  ⟨Vp, dVp, fun ψ _ => D ψ, fun ψ _ => dD ψ, fun _ _ => 0, R, Tdom, axis⟩

/-- The semilinear operator is the pre-K2 kernel operator `D uψψ + (D' + D V''/V') uψ + R`. -/
theorem RadialCoefficients.semilinear_op (Vp dVp D dD : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (Tdom : Set ℝ) (axis : AxisKind) (ψ u uψ uψψ : ℝ) :
    (RadialCoefficients.semilinear Vp dVp D dD R Tdom axis).op ψ u uψ uψψ =
      D ψ * uψψ + (dD ψ + D ψ * dVp ψ / Vp ψ) * uψ + R ψ u := by
  simp only [RadialCoefficients.op, RadialCoefficients.semilinear, zero_mul, add_zero]

/-- The coefficients are **semilinear** on `[0,1]`: `D` and `∂ψD` do not depend on the
temperature and `∂TD = 0`. Then the operator depends on the value argument only through `R`
(`RadialCoefficients.IsSemilinear.op_sub_op`). -/
@[expose] def RadialCoefficients.IsSemilinear (c : RadialCoefficients) : Prop :=
  ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T T' : ℝ, c.D ψ T = c.D ψ T' ∧ c.dD ψ T = c.dD ψ T' ∧ c.dDT ψ T = 0

/-- Coefficients built by `RadialCoefficients.semilinear` are semilinear. -/
theorem RadialCoefficients.semilinear_isSemilinear (Vp dVp D dD : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (Tdom : Set ℝ) (axis : AxisKind) :
    (RadialCoefficients.semilinear Vp dVp D dD R Tdom axis).IsSemilinear :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- For semilinear coefficients, changing only the value argument of the operator changes it
by the change of `R`. -/
theorem RadialCoefficients.IsSemilinear.op_sub_op {c : RadialCoefficients}
    (h : c.IsSemilinear) {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) (a a' b d : ℝ) :
    c.op ψ a b d - c.op ψ a' b d = c.R ψ a - c.R ψ a' := by
  obtain ⟨h1, h2, h3⟩ := h ψ hψ a a'
  have h4 := (h ψ hψ a' a).2.2
  unfold RadialCoefficients.op
  rw [h1, h2, h3, h4]; ring

/-- Optional (not a kernel law): the diffusivity is bounded below by `Dmin > 0` on `[0,1]`
(at every temperature). This was a kernel law before the 2026-10-20 change; it fails for every
coordinate with `D(0,·) = 0`. -/
@[expose] def RadialCoefficients.UniformlyParabolic (c : RadialCoefficients) (Dmin : ℝ) : Prop :=
  0 < Dmin ∧ ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, Dmin ≤ c.D ψ T

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
nonnegative diffusivity (at every temperature) vanishing at a degenerate axis and positive at
a regular one, the supplied coefficient derivatives are genuine (one-sided in `ψ` at the ends;
`∂TD` a genuine derivative in `T`), and the net source is jointly continuous on `[0,1] × Tdom`
with `Tdom` open. (Kernel change 2026-10-20: `D ≥ 0` replaces `D ≥ Dmin > 0`; kernel change
2026-10-20 K2: `D = D(ψ,T)` and the law `DT_deriv`; see the module documentation.) -/
class TransportLaws (c : RadialCoefficients) : Prop where
  /-- `V' > 0` up to the axis. -/
  Vp_pos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.Vp ψ
  /-- `dVp` is the derivative of `Vp`. -/
  Vp_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c.Vp (c.dVp ψ) (Icc 0 1) ψ
  /-- `dD` is the `ψ`-derivative of `D` at every temperature. -/
  D_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ,
    HasDerivWithinAt (fun x => c.D x T) (c.dD ψ T) (Icc 0 1) ψ
  /-- `dDT` is the `T`-derivative of `D` on every surface (K2). -/
  DT_deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, HasDerivAt (c.D ψ) (c.dDT ψ T) T
  /-- `D ≥ 0` on `[0,1]` at every temperature (degenerate diffusion allowed). -/
  D_nonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T
  /-- At a degenerate axis the diffusivity vanishes (at every temperature). -/
  D_axis : c.axis = .degenerate → ∀ T : ℝ, c.D 0 T = 0
  /-- At a regular axis the diffusivity is positive (so a coordinate with `D(0,·) = 0` cannot
  be declared `regular`, which would make the Neumann condition over-determine the problem). -/
  D_axis_regular : c.axis = .regular → ∀ T : ℝ, 0 < c.D 0 T
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
    (h : c.UniformlyParabolic Dmin) : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T :=
  fun ψ hψ T => h.1.le.trans (h.2 ψ hψ T)

/-- A uniformly parabolic diffusivity does not vanish at the axis, so a degenerate axis
(`D(0,·) = 0`) is never uniformly parabolic. -/
theorem RadialCoefficients.UniformlyParabolic.D_axis_pos {c : RadialCoefficients} {Dmin : ℝ}
    (h : c.UniformlyParabolic Dmin) (T : ℝ) : 0 < c.D 0 T :=
  h.1.trans_le (h.2 0 ⟨le_rfl, zero_le_one⟩ T)

end PlasmaLean.Transport
