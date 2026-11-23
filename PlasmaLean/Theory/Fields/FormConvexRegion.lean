/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormLoopCurrentInterval

/-!
# Convex vacuum regions: the simply connected corollaries with the topology discharged

`Theory/Fields/FormLoopCurrentInterval` proves that a vacuum field on a simply connected open
region has zero circulation around closed curves, and so zero loop current through poloidal
loops. This file supplies regions for which `SimplyConnectedSpace` is proved, and the resulting
statements with no topological hypothesis left.

* `simplyConnectedSpace_of_convex`: a nonempty convex open subset of `Space` is simply
  connected. Instances: all of space (`⊤`), open balls (`ballOpens`,
  `simplyConnectedSpace_ballOpens`), and the open half-space `meridianHalfSpace φ₀` of points
  `x` with `x₀ cos φ₀ + x₁ sin φ₀ > 0`.
* `VacuumField.lineIntegral_eq_zero_of_convex`,
  `VacuumField.poloidalCirculation_eq_zero_of_convex`, `VacuumField.loopCurrent_eq_zero_of_convex`:
  a vacuum field on a convex open region has zero circulation around every closed curve that is
  `C¹` on `[a, b]` and lies in the region there, and zero loop current through every such
  poloidal loop.
* **The meridian half-space.** A poloidal loop is a curve of constant geometric toroidal angle
  `φ₀`. If `R > 0` along it, it lies in `meridianHalfSpace φ₀`
  (`poloidalLoop_mem_meridianHalfSpace`), which is convex and does not meet the `z`-axis
  (`r2_pos_of_mem_meridianHalfSpace`). So for a field that is a vacuum field on a region
  containing that half-space (for example on the complement of the `z`-axis, which is not
  simply connected), every poloidal loop with `R > 0` carries zero current:
  `VacuumField.loopCurrent_eq_zero_of_meridianHalfSpace`.
* `FieldTorus.loopCurrent_eq_zero_of_meridianHalfSpace`: the same for the poloidal loops of a
  `FieldTorus` (`R > 0` and closure are part of the structure), for every rotation number `ι`.
* `CurrentFreeTransform.current_eq_zero_of_meridianHalfSpace`,
  `CurrentFreeTransform.poloidalCirculation_eq_zero_of_meridianHalfSpace`,
  `CurrentFreeTransform.imax_zero_of_meridianHalfSpace`: for a family satisfying the contract
  clause C1 with any current allowance `I_max`, if the field is a vacuum field on a region
  containing the meridian half-spaces of the surfaces, every surface has zero current and zero
  poloidal circulation, and the clause holds with `I_max = 0`.

The point of the half-space: the hypothesis "simply connected" is on the region that contains
the poloidal loop, not on the region where the field is a vacuum field. A stellarator vacuum
field is defined off the `z`-axis (or off its coils), and that region is not simply connected;
the poloidal loop still lies in a convex part of it. A non-zero rotational transform is
compatible with this: the transform is carried by toroidally varying terms of the field, not
by a net poloidal circulation.

What is not proved: nothing is said about regions that are simply connected without being
convex (use `FormLoopCurrentInterval` directly, with an instance of `SimplyConnectedSpace`), nor
about fields whose vacuum region does not contain a meridian half-space (coils or plasma
current threading the poloidal loop; the circulation is then the enclosed current).
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped Manifold RealInnerProductSpace

/-! ## Convex open sets are simply connected -/

/-- **A nonempty convex open subset of space is simply connected**: it is contractible. -/
theorem simplyConnectedSpace_of_convex {U : Opens Space} (hc : Convex ℝ (U : Set Space))
    (hne : (U : Set Space).Nonempty) : SimplyConnectedSpace U := by
  have : ContractibleSpace (U : Set Space) := hc.contractibleSpace hne
  exact inferInstanceAs (SimplyConnectedSpace (U : Set Space))

/-- All of space is simply connected. -/
instance simplyConnectedSpace_top : SimplyConnectedSpace (⊤ : Opens Space) :=
  simplyConnectedSpace_of_convex (by simpa using convex_univ) ⟨0, by simp⟩

/-- The open ball of centre `c` and radius `r`, as an open region. -/
noncomputable def ballOpens (c : Space) (r : ℝ) : Opens Space :=
  ⟨Metric.ball c r, Metric.isOpen_ball⟩

/-- Membership in `ballOpens`. -/
theorem mem_ballOpens {c : Space} {r : ℝ} {x : Space} : x ∈ ballOpens c r ↔ dist x c < r :=
  Iff.rfl

/-- **An open ball of positive radius is simply connected.** -/
theorem simplyConnectedSpace_ballOpens (c : Space) {r : ℝ} (hr : 0 < r) :
    SimplyConnectedSpace (ballOpens c r) :=
  simplyConnectedSpace_of_convex (convex_ball c r) ⟨c, Metric.mem_ball_self hr⟩

/-- The linear functional `x ↦ x₀ cos φ₀ + x₁ sin φ₀`: the component of `x` along the horizontal
unit vector of toroidal angle `φ₀`. -/
noncomputable def meridianCoord (φ₀ : ℝ) (x : Space) : ℝ :=
  x 0 * Real.cos φ₀ + x 1 * Real.sin φ₀

/-- The **meridian half-space** of toroidal angle `φ₀`: the open half-space
`x₀ cos φ₀ + x₁ sin φ₀ > 0`. It contains the half-plane of toroidal angle `φ₀` and does not
meet the `z`-axis. -/
def meridianHalfSpace (φ₀ : ℝ) : Opens Space :=
  ⟨{x | 0 < meridianCoord φ₀ x}, isOpen_lt continuous_const (by unfold meridianCoord; fun_prop)⟩

/-- Membership in the meridian half-space. -/
theorem mem_meridianHalfSpace {φ₀ : ℝ} {x : Space} :
    x ∈ meridianHalfSpace φ₀ ↔ 0 < x 0 * Real.cos φ₀ + x 1 * Real.sin φ₀ :=
  Iff.rfl

/-- The meridian half-space is convex. -/
theorem convex_meridianHalfSpace (φ₀ : ℝ) : Convex ℝ (meridianHalfSpace φ₀ : Set Space) :=
  convex_halfSpace_gt (f := meridianCoord φ₀)
    ⟨fun x y => by simp [meridianCoord]; ring, fun c x => by simp [meridianCoord]; ring⟩ 0

/-- A point with cylindrical coordinates `(R, φ₀, z)`, `R > 0`, lies in the meridian half-space
of `φ₀`. -/
theorem cylPoint_mem_meridianHalfSpace {R : ℝ} (hR : 0 < R) (φ₀ z : ℝ) :
    cylPoint R φ₀ z ∈ meridianHalfSpace φ₀ := by
  rw [mem_meridianHalfSpace]
  have h : cylPoint R φ₀ z 0 * Real.cos φ₀ + cylPoint R φ₀ z 1 * Real.sin φ₀ = R := by
    simp only [(cylPoint_coords R φ₀ z).1, (cylPoint_coords R φ₀ z).2.1]
    linear_combination R * Real.cos_sq_add_sin_sq φ₀
  rw [h]
  exact hR

/-- The meridian half-space is simply connected. -/
instance simplyConnectedSpace_meridianHalfSpace (φ₀ : ℝ) :
    SimplyConnectedSpace (meridianHalfSpace φ₀) :=
  simplyConnectedSpace_of_convex (convex_meridianHalfSpace φ₀)
    ⟨_, cylPoint_mem_meridianHalfSpace one_pos φ₀ 0⟩

/-- **The meridian half-space does not meet the `z`-axis**: on it `x₀² + x₁² > 0`. -/
theorem r2_pos_of_mem_meridianHalfSpace {φ₀ : ℝ} {x : Space} (hx : x ∈ meridianHalfSpace φ₀) :
    0 < x 0 ^ 2 + x 1 ^ 2 := by
  rw [mem_meridianHalfSpace] at hx
  by_contra h
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  rw [h0, h1] at hx
  simp at hx

/-- **A poloidal loop with `R > 0` lies in its meridian half-space.** -/
theorem poloidalLoop_mem_meridianHalfSpace {R z : ℝ → ℝ → ℝ} {φ₀ θ : ℝ} (hR : 0 < R θ φ₀) :
    poloidalLoop R z φ₀ θ ∈ meridianHalfSpace φ₀ :=
  cylPoint_mem_meridianHalfSpace hR φ₀ _

/-! ## Vacuum fields on convex regions -/

section Convex

variable {U : Opens Space} {B : Space → Space}

/-- **A vacuum field on a convex open region has no circulation.** For every curve `γ` that is
`C¹` on `[a, b]`, lies in the region there and closes up, `∫_a^b B · dl = 0`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.lineIntegral_eq_zero_of_convex
    (hc : Convex ℝ (U : Set Space)) (h : VacuumField U B) {γ : ℝ → Space} {a b : ℝ}
    (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hclosed : γ a = γ b) : lineIntegral B γ a b = 0 :=
  have := simplyConnectedSpace_of_convex hc ⟨γ a, hU a (Set.left_mem_Icc.2 hab.le)⟩
  h.lineIntegral_eq_zero_of_simplyConnected hab hU hγ hclosed

variable {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ}

/-- **A vacuum field on a convex open region has no poloidal circulation** around a poloidal
loop that is `C¹` on `[-π, π]`, lies in the region there and closes up. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalCirculation_eq_zero_of_convex
    (hc : Convex ℝ (U : Set Space)) (h : VacuumField U B)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    poloidalCirculation B R z φ₀ = 0 :=
  h.lineIntegral_eq_zero_of_convex hc neg_pi_lt_pi hU hγ hclosed

/-- **No net toroidal current through a poloidal loop in a convex vacuum region.** -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.loopCurrent_eq_zero_of_convex (μ₀ : ℝ)
    (hc : Convex ℝ (U : Set Space)) (h : VacuumField U B)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    loopCurrent μ₀ B R z φ₀ = 0 := by
  rw [loopCurrent, h.poloidalCirculation_eq_zero_of_convex hc hU hγ hclosed, zero_div]

end Convex

/-! ## The meridian half-space and the contract -/

section Meridian

variable {Ω : Set Space} {B : Space → Space} {R z : ℝ → ℝ → ℝ} {φ₀ ι : ℝ}

/-- A vacuum field on a region containing a meridian half-space is a vacuum field on that
half-space. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.restrict_meridianHalfSpace (h : VacuumField Ω B)
    (hΩ : (meridianHalfSpace φ₀ : Set Space) ⊆ Ω) :
    VacuumField (meridianHalfSpace φ₀ : Set Space) B :=
  ⟨(meridianHalfSpace φ₀).isOpen, h.contDiffOn.mono hΩ, fun x hx => h.div_eq_zero x (hΩ hx),
    fun x hx => h.curl_eq_zero x (hΩ hx)⟩

/-- **Poloidal loops off the axis carry no current in a vacuum field.** Let `B` be a vacuum
field on a region `Ω` containing the meridian half-space of `φ₀` (for example the complement of
the `z`-axis). Every poloidal loop at `φ₀` with `R > 0` that is `C¹` on `[-π, π]` and closes up
has zero loop current. Nothing is assumed about the topology of `Ω`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.loopCurrent_eq_zero_of_meridianHalfSpace (μ₀ : ℝ)
    (h : VacuumField Ω B) (hΩ : (meridianHalfSpace φ₀ : Set Space) ⊆ Ω)
    (hR : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, 0 < R θ φ₀)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    loopCurrent μ₀ B R z φ₀ = 0 :=
  (h.restrict_meridianHalfSpace hΩ).loopCurrent_eq_zero_of_simplyConnected_of_Icc μ₀
    (fun θ hθ => poloidalLoop_mem_meridianHalfSpace (hR θ hθ)) hγ hclosed

/-- **A `FieldTorus` of a vacuum field carries no net current, whatever its rotation number.**
The field is a vacuum field on a region containing the meridian half-space of `φ₀`, and the
poloidal loop at `φ₀` is `C¹` on `[-π, π]`. That `R > 0` and that the loop closes up are part
of `FieldTorus`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.loopCurrent_eq_zero_of_meridianHalfSpace
    (hT : FieldTorus B R z ι) (μ₀ : ℝ) (h : VacuumField Ω B)
    (hΩ : (meridianHalfSpace φ₀ : Set Space) ⊆ Ω)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi)) :
    loopCurrent μ₀ B R z φ₀ = 0 :=
  hT.loopCurrent_eq_zero_of_simplyConnected μ₀ (h.restrict_meridianHalfSpace hΩ)
    (fun θ _ => poloidalLoop_mem_meridianHalfSpace (hT.R_pos θ φ₀)) hγ

variable {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData}

/-- **Clause C1 for a vacuum field: every surface has zero current.** For a family satisfying
`CurrentFreeTransform` with any allowance `I_max`, if `B` is a vacuum field on a region
containing the meridian half-space of the surface `s`, the net current of `s` is zero. This is
`CurrentFreeTransform.current_eq_zero_of_simplyConnected` with the region chosen and its
hypotheses discharged. -/
theorem _root_.PlasmaLean.Contract.CurrentFreeTransform.current_eq_zero_of_meridianHalfSpace
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField Ω B) {s : SurfaceData}
    (hs : s ∈ S) (hΩ : (meridianHalfSpace s.φ₀ : Set Space) ⊆ Ω) : s.current μ₀ B = 0 :=
  hC.current_eq_zero_of_simplyConnected (h.restrict_meridianHalfSpace hΩ) hs
    fun θ _ => poloidalLoop_mem_meridianHalfSpace ((hC.torus s hs).1.R_pos θ s.φ₀)

/-- **Clause C1 for a vacuum field: zero poloidal circulation**, for any allowance `I_max`. -/
theorem
    _root_.PlasmaLean.Contract.CurrentFreeTransform.poloidalCirculation_eq_zero_of_meridianHalfSpace
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField Ω B) {s : SurfaceData}
    (hs : s ∈ S) (hΩ : (meridianHalfSpace s.φ₀ : Set Space) ⊆ Ω) :
    poloidalCirculation B s.R s.z s.φ₀ = 0 :=
  (h.restrict_meridianHalfSpace hΩ).poloidalCirculation_eq_zero_of_simplyConnected_of_Icc
    (fun θ _ => poloidalLoop_mem_meridianHalfSpace ((hC.torus s hs).1.R_pos θ s.φ₀))
    (contDiff_poloidalLoop (hC.loop_R s hs) (hC.loop_z s hs)).contDiffOn
    ((hC.torus s hs).1.poloidalLoop_closed s.φ₀)

/-- **For a vacuum field the current bound of C1 is automatic**: a family satisfying the clause
with some allowance `I_max` satisfies it with `I_max = 0`, when the field is a vacuum field on a
region containing the meridian half-space of every surface. -/
theorem _root_.PlasmaLean.Contract.CurrentFreeTransform.imax_zero_of_meridianHalfSpace
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField Ω B)
    (hΩ : ∀ s ∈ S, (meridianHalfSpace s.φ₀ : Set Space) ⊆ Ω) :
    CurrentFreeTransform μ₀ B S 0 ιmin where
  mu0_pos := hC.mu0_pos
  nonempty := hC.nonempty
  iotaMin_pos := hC.iotaMin_pos
  torus := hC.torus
  loop_R := hC.loop_R
  loop_z := hC.loop_z
  field_continuous := hC.field_continuous
  current_le s hs := by
    rw [hC.current_eq_zero_of_meridianHalfSpace h hs (hΩ s hs), abs_zero]
  iota_ge := hC.iota_ge

end Meridian

end PlasmaLean.Forms
