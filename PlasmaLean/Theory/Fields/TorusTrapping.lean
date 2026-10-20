/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.InvariantBarrier
public import PlasmaLean.Design.RationalStellarator
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# An invariant radial-graph torus traps field lines for all time (KAM route, stage K1)

Stage K1 of `notes/theory/kam-route.md` (§3, (B2) combined with (B1)).

**Tubular coordinates** (`TubeCoords`): an open tube `T` with a radial coordinate `r`,
continuous on `T` and differentiable where `r > 0` (the axis is `{r = 0}`), and two angle
functions `θ`, `φ` that are only required to have *local differentiable lifts* off the axis:
near every `x ∈ T` with `r x > 0` they agree, up to an integer multiple of `2π` (which may vary
from point to point), with a function differentiable at `x`. This is exactly what
`Complex.arg` of a smooth non-vanishing complex function provides (`exists_arg_lift`), and
it is all a `2π`-periodic `ρ` needs: `ρ(θ, φ)` is then differentiable off the axis
(`TubeCoords.differentiableAt_ρhat`). (The local-diffeomorphism property of `(r, θ, φ)` is
needed to *construct* `ρ` from a KAM parameterization, not to use it, so it is not assumed.)

**Torus** `S = {r = ρ(θ, φ)}` for a differentiable, doubly `2π`-periodic `ρ` with
`0 < ρ_min ≤ ρ ≤ R₁`, where the closed sub-tube `{x ∈ T | r x ≤ R₁}` is closed in space. The
inside is `inside = {x ∈ T | r x ≤ 0 ∨ r x < ρ(θ x, φ x)}` (the axis together with the points
below the graph). `inside` is open and its frontier lies on `S`, away from the axis
(`TubeCoords.isOpen_inside`, `TubeCoords.frontier_inside`).

**Invariance** (approximate or exact): with `G = r - ρ(θ, φ)`, the Grönwall condition
`|DG · B| ≤ L |G|` on a collar `{x ∈ T | r x > 0, |G x| < g₀}`. `L = 0` with `DG · B = 0` is
the exact case; tangency on `S` plus a Lipschitz bound gives `L > 0`
(`Fields.invariance_bound_of_tangent`).

**Theorem** (`torus_trapping_forward`, `torus_trapping_forever`): every field line starting
in `inside` stays in `inside` for all parameter values (forward, resp. forward and backward).
The axis need not be a field line for this.

**Application** (`RationalStellarator.rationalStellarator_confined_forever_of_torus`): for the
rational field `B_ε` with the explicit tube about the exact circular axis `R = 1, z = 0`
(`rt` = distance from the axis, `θs`, `φs` = poloidal and toroidal angles via `Complex.arg`),
*if* a function `ρ` satisfying the invariance condition exists (to be supplied by KAM, stages
K2/K3), *then* every field line starting inside the torus stays inside forever. The
hypotheses are satisfiable: for `ε = 0` every circular torus `rt = c` is exactly invariant
(`toroidal_invariance`), giving `rationalStellarator_eps0_confined_forever`; the exact axis
is a two-sided field line starting inside (`axis_isFieldLine`, `axis_inside`).
-/

public section
noncomputable section
namespace PlasmaLean.Fields
open Set Filter Topology Real

/-- Tubular coordinates `(r, θ, φ)` on an open tube `T` about an axis `{r = 0}`; the angles are
only required to have local differentiable lifts (modulo `2π`) off the axis. -/
structure TubeCoords where
  /-- The open tube. -/
  T : Set Space
  /-- Radial coordinate (distance from the axis); the axis is `{r = 0}`. -/
  r : Space → ℝ
  /-- Poloidal angle (any branch). -/
  θ : Space → ℝ
  /-- Toroidal angle (any branch). -/
  φ : Space → ℝ
  /-- The tube is open. -/
  isOpen_T : IsOpen T
  /-- `r` is continuous on the tube (including the axis). -/
  continuousOn_r : ContinuousOn r T
  /-- `r` is differentiable off the axis. -/
  differentiableAt_r : ∀ x ∈ T, 0 < r x → DifferentiableAt ℝ r x
  /-- `θ` has local differentiable lifts modulo `2π` off the axis. -/
  lift_θ : ∀ x ∈ T, 0 < r x → ∃ θ' : Space → ℝ, DifferentiableAt ℝ θ' x ∧
    ∀ᶠ y in 𝓝 x, ∃ k : ℤ, θ y = θ' y + 2 * π * k
  /-- `φ` has local differentiable lifts modulo `2π` off the axis. -/
  lift_φ : ∀ x ∈ T, 0 < r x → ∃ φ' : Space → ℝ, DifferentiableAt ℝ φ' x ∧
    ∀ᶠ y in 𝓝 x, ∃ k : ℤ, φ y = φ' y + 2 * π * k

/-- A torus profile: `ρ` is differentiable and `2π`-periodic in both angles. -/
structure TorusProfile (ρ : ℝ → ℝ → ℝ) : Prop where
  /-- `ρ` is differentiable as a function of both angles. -/
  differentiable : Differentiable ℝ (fun p : ℝ × ℝ => ρ p.1 p.2)
  /-- `2π`-periodic in the poloidal angle. -/
  periodic_left : ∀ a b, ρ (a + 2 * π) b = ρ a b
  /-- `2π`-periodic in the toroidal angle. -/
  periodic_right : ∀ a b, ρ a (b + 2 * π) = ρ a b

/-- A torus profile is invariant under integer shifts by `2π` in both angles. -/
theorem TorusProfile.shift {ρ : ℝ → ℝ → ℝ} (hρ : TorusProfile ρ) (a b : ℝ) (k m : ℤ) :
    ρ (a + 2 * π * k) (b + 2 * π * m) = ρ a b := by
  have h1 : Function.Periodic (fun a => ρ a (b + 2 * π * m)) (2 * π) :=
    fun a => hρ.periodic_left a _
  have h2 : Function.Periodic (fun b => ρ a b) (2 * π) := fun b => hρ.periodic_right a b
  have e1 := (h1.int_mul k) a
  have e2 := (h2.int_mul m) b
  rw [mul_comm (2 * π) (k : ℝ), e1, mul_comm (2 * π) (m : ℝ), e2]

namespace TubeCoords
variable (c : TubeCoords) (ρ : ℝ → ℝ → ℝ)

/-- The graph function `ρ(θ x, φ x)`. -/
@[expose] def ρhat (x : Space) : ℝ := ρ (c.θ x) (c.φ x)

/-- The level function `G = r - ρ(θ, φ)` of the torus. -/
@[expose] def G (x : Space) : ℝ := c.r x - c.ρhat ρ x

/-- The tube with the axis removed. -/
@[expose] def offAxis : Set Space := c.T ∩ c.r ⁻¹' Ioi 0

/-- The inside of the torus: the axis together with the points below the graph. -/
@[expose] def inside : Set Space := {x | x ∈ c.T ∧ (c.r x ≤ 0 ∨ c.r x < c.ρhat ρ x)}

/-- The torus `{r = ρ(θ, φ)}` (off the axis). -/
@[expose] def torus : Set Space := {x | x ∈ c.offAxis ∧ c.r x = c.ρhat ρ x}

/-- The collar `{x ∈ T | r x > 0, |G x| < g₀}` of the torus. -/
@[expose] def collar (g₀ : ℝ) : Set Space := c.offAxis ∩ c.G ρ ⁻¹' Ioo (-g₀) g₀

/-- The tube minus the axis is open. -/
theorem isOpen_offAxis : IsOpen c.offAxis :=
  c.continuousOn_r.isOpen_inter_preimage c.isOpen_T isOpen_Ioi

variable {c ρ}

/-- Off the axis, `ρ(θ, φ)` is differentiable. -/
theorem differentiableAt_ρhat (hρ : TorusProfile ρ) {x : Space} (hx : x ∈ c.offAxis) :
    DifferentiableAt ℝ (c.ρhat ρ) x := by
  obtain ⟨θ', hθ', hθe⟩ := c.lift_θ x hx.1 hx.2
  obtain ⟨φ', hφ', hφe⟩ := c.lift_φ x hx.1 hx.2
  have hd : DifferentiableAt ℝ (fun y => ρ (θ' y) (φ' y)) x :=
    (hρ.differentiable _).comp x (hθ'.prodMk hφ')
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hθe, hφe] with y ⟨k, hk⟩ ⟨m, hm⟩
  simp only [ρhat, hk, hm, hρ.shift]

/-- Off the axis, `G = r - ρ(θ, φ)` is differentiable. -/
theorem differentiableAt_G (hρ : TorusProfile ρ) {x : Space} (hx : x ∈ c.offAxis) :
    DifferentiableAt ℝ (c.G ρ) x :=
  (c.differentiableAt_r x hx.1 hx.2).sub (differentiableAt_ρhat hρ hx)

/-- `G` is continuous off the axis. -/
theorem continuousOn_G (hρ : TorusProfile ρ) : ContinuousOn (c.G ρ) c.offAxis :=
  fun _ hx => (differentiableAt_G hρ hx).continuousAt.continuousWithinAt

/-- The inside, written with a lower bound `0 < ρ_min ≤ ρ`, as a union of two open pieces. -/
theorem inside_eq {ρmin : ℝ} (hmin : 0 < ρmin) (hlo : ∀ a b, ρmin ≤ ρ a b) :
    c.inside ρ = (c.T ∩ c.r ⁻¹' Iio ρmin) ∪ (c.offAxis ∩ c.G ρ ⁻¹' Iio 0) := by
  ext x
  have hl := hlo (c.θ x) (c.φ x)
  simp only [inside, offAxis, G, ρhat, mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage,
    mem_Iio, mem_Ioi] at hl ⊢
  constructor
  · rintro ⟨hT, h | h⟩
    · exact Or.inl ⟨hT, by linarith⟩
    · rcases lt_or_ge (c.r x) ρmin with h' | h'
      · exact Or.inl ⟨hT, h'⟩
      · exact Or.inr ⟨⟨hT, by linarith⟩, by linarith⟩
  · rintro (⟨hT, h⟩ | ⟨⟨hT, _⟩, h⟩)
    · rcases le_or_gt (c.r x) 0 with h' | h'
      · exact ⟨hT, Or.inl h'⟩
      · exact ⟨hT, Or.inr (by linarith)⟩
    · exact ⟨hT, Or.inr (by linarith)⟩

/-- The inside of the torus is open. -/
theorem isOpen_inside (hρ : TorusProfile ρ) {ρmin : ℝ} (hmin : 0 < ρmin)
    (hlo : ∀ a b, ρmin ≤ ρ a b) : IsOpen (c.inside ρ) := by
  rw [inside_eq hmin hlo]
  exact (c.continuousOn_r.isOpen_inter_preimage c.isOpen_T isOpen_Iio).union
    ((continuousOn_G hρ).isOpen_inter_preimage c.isOpen_offAxis isOpen_Iio)

/-- The collar is open. -/
theorem isOpen_collar (hρ : TorusProfile ρ) (g₀ : ℝ) : IsOpen (c.collar ρ g₀) :=
  (continuousOn_G hρ).isOpen_inter_preimage c.isOpen_offAxis isOpen_Ioo

/-- The inside lies in the closed sub-tube `{x ∈ T | r x ≤ R₁}` when `0 ≤ R₁` and `ρ ≤ R₁`. -/
theorem inside_subset_closedTube {R₁ : ℝ} (hR₁ : 0 ≤ R₁) (hhi : ∀ a b, ρ a b ≤ R₁) :
    c.inside ρ ⊆ {x | x ∈ c.T ∧ c.r x ≤ R₁} := by
  rintro x ⟨hT, h | h⟩
  · exact ⟨hT, h.trans hR₁⟩
  · exact ⟨hT, h.le.trans (hhi _ _)⟩

/-- **The frontier of the inside lies on the torus**, provided the closed sub-tube
`{x ∈ T | r x ≤ R₁}` containing the torus is closed in space. -/
theorem frontier_inside (hρ : TorusProfile ρ) {ρmin R₁ : ℝ} (hmin : 0 < ρmin)
    (hlo : ∀ a b, ρmin ≤ ρ a b) (hhi : ∀ a b, ρ a b ≤ R₁)
    (hclosed : IsClosed {x | x ∈ c.T ∧ c.r x ≤ R₁}) :
    frontier (c.inside ρ) ⊆ c.torus ρ := by
  intro y hy
  have hR₁ : 0 ≤ R₁ := hmin.le.trans ((hlo 0 0).trans (hhi 0 0))
  rw [frontier, (isOpen_inside hρ hmin hlo).interior_eq] at hy
  obtain ⟨hcl, hnot⟩ := hy
  have hyK := (hclosed.closure_subset_iff.mpr (inside_subset_closedTube hR₁ hhi)) hcl
  have hyT : y ∈ c.T := hyK.1
  simp only [inside, mem_ofPred_eq, not_and, not_or, not_le, not_lt] at hnot
  obtain ⟨hr0, hge⟩ := hnot hyT
  have hoff : y ∈ c.offAxis := ⟨hyT, hr0⟩
  refine ⟨hoff, le_antisymm ?_ hge⟩
  -- `G y ≤ 0` by continuity of `G` at `y` and density of the inside near `y`
  by_contra hpos
  push Not at hpos
  have hGy : 0 < c.G ρ y := by simp only [G]; linarith
  have hGc : ContinuousAt (c.G ρ) y := (differentiableAt_G hρ hoff).continuousAt
  have hnb : c.offAxis ∩ c.G ρ ⁻¹' Ioi 0 ∈ 𝓝 y :=
    Filter.inter_mem (c.isOpen_offAxis.mem_nhds hoff) (hGc.preimage_mem_nhds (Ioi_mem_nhds hGy))
  obtain ⟨z, hzN, hzΩ⟩ := mem_closure_iff_nhds.mp hcl _ hnb
  obtain ⟨⟨_, hzr⟩, hzG⟩ := hzN
  simp only [mem_preimage, mem_Ioi, G] at hzr hzG
  rcases hzΩ.2 with h | h
  · linarith
  · linarith

end TubeCoords

open TubeCoords in
/-- **Torus trapping, forward.** Let `ρ` be a torus profile with `0 < ρ_min ≤ ρ ≤ R₁`, where the
closed sub-tube `{x ∈ T | r x ≤ R₁}` is closed in space, and suppose the torus `r = ρ(θ, φ)` is
invariant in the Grönwall sense `|DG · B| ≤ L |G|`, `G = r - ρ(θ, φ)`, on the collar
`{x ∈ T | r x > 0, |G x| < g₀}`. Then every forward field line starting inside the torus stays
inside for every parameter `s ≥ 0`. -/
theorem torus_trapping_forward {c : TubeCoords} {ρ : ℝ → ℝ → ℝ} {B : Space → Space}
    {ρmin R₁ g₀ L : ℝ} (hρ : TorusProfile ρ) (hmin : 0 < ρmin) (hlo : ∀ a b, ρmin ≤ ρ a b)
    (hhi : ∀ a b, ρ a b ≤ R₁) (hclosed : IsClosed {x | x ∈ c.T ∧ c.r x ≤ R₁}) (hg₀ : 0 < g₀)
    (hinv : ∀ x ∈ c.T, 0 < c.r x → |c.G ρ x| < g₀ → |fderiv ℝ (c.G ρ) x (B x)| ≤ L * |c.G ρ x|)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ c.inside ρ) :
    ∀ t, 0 ≤ t → γ t ∈ c.inside ρ := by
  refine invariantBarrier_forward (G := c.G ρ) (L := L) (C := c.collar ρ g₀)
    (isOpen_inside hρ hmin hlo) (isOpen_collar hρ g₀) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) hγ h0
  · obtain ⟨hoff, heq⟩ := frontier_inside hρ hmin hlo hhi hclosed hx
    have hG0 : c.G ρ x = 0 := by simp only [G]; linarith
    exact ⟨⟨hoff, by simp [hG0, hg₀]⟩, hG0⟩
  · obtain ⟨⟨hT, h | h⟩, ⟨_, hr⟩, _⟩ := hx
    · exact absurd h (not_le.mpr hr)
    · simp only [G]; linarith
  · obtain ⟨hoff, hGx⟩ := hx
    refine ⟨differentiableAt_G hρ hoff, hinv x hoff.1 hoff.2 ?_⟩
    simp only [mem_preimage, mem_Ioo] at hGx
    exact abs_lt.mpr hGx

open TubeCoords in
/-- **Torus trapping, all time.** Under the hypotheses of `torus_trapping_forward`, every
two-sided field line starting inside the torus stays inside for every real parameter. -/
theorem torus_trapping_forever {c : TubeCoords} {ρ : ℝ → ℝ → ℝ} {B : Space → Space}
    {ρmin R₁ g₀ L : ℝ} (hρ : TorusProfile ρ) (hmin : 0 < ρmin) (hlo : ∀ a b, ρmin ≤ ρ a b)
    (hhi : ∀ a b, ρ a b ≤ R₁) (hclosed : IsClosed {x | x ∈ c.T ∧ c.r x ≤ R₁}) (hg₀ : 0 < g₀)
    (hinv : ∀ x ∈ c.T, 0 < c.r x → |c.G ρ x| < g₀ → |fderiv ℝ (c.G ρ) x (B x)| ≤ L * |c.G ρ x|)
    {γ : ℝ → Space} (hγ : IsFieldLine B γ) (h0 : γ 0 ∈ c.inside ρ) :
    ∀ t, γ t ∈ c.inside ρ := by
  intro t
  rcases le_total 0 t with ht | ht
  · exact torus_trapping_forward hρ hmin hlo hhi hclosed hg₀ hinv hγ.forward h0 t ht
  · have h := torus_trapping_forward (B := fun x => -B x) hρ hmin hlo hhi hclosed hg₀
      (fun x hx hr hG => by rw [map_neg, abs_neg]; exact hinv x hx hr hG)
      hγ.reverse.forward (by simpa using h0) (-t) (by linarith)
    simpa using h

/-- Degenerate case: a constant profile `ρ ≡ c₀` is a torus profile. -/
theorem torusProfile_const (c₀ : ℝ) : TorusProfile (fun _ _ => c₀) :=
  ⟨differentiable_const _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Local lifts of `Complex.arg`.** If `w` is differentiable at `x` with `w x ≠ 0`, then
`arg ∘ w` agrees near `x`, modulo `2π`, with a function differentiable at `x`. -/
theorem exists_arg_lift {w : Space → ℂ} {x : Space} (hw : DifferentiableAt ℝ w x)
    (hx : w x ≠ 0) : ∃ θ' : Space → ℝ, DifferentiableAt ℝ θ' x ∧
      ∀ᶠ y in 𝓝 x, ∃ k : ℤ, Complex.arg (w y) = θ' y + 2 * π * k := by
  have hdarg : ∀ v : Space → ℂ, DifferentiableAt ℝ v x → v x ∈ Complex.slitPlane →
      DifferentiableAt ℝ (fun y => Complex.arg (v y)) x := by
    intro v hv hs
    have e : (fun y => Complex.arg (v y)) = fun y => Complex.imCLM (Complex.log (v y)) :=
      funext fun y => by simp [Complex.log_im]
    rw [e]
    exact Complex.imCLM.differentiableAt.comp x
      (((Complex.differentiableAt_log hs).restrictScalars ℝ).comp x hv)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hx with hs | hs
  · exact ⟨fun y => Complex.arg (w y), hdarg w hw hs,
      Filter.Eventually.of_forall fun y => ⟨0, by simp⟩⟩
  · refine ⟨fun y => Complex.arg (-w y) + π, (hdarg (fun y => -w y) hw.neg hs).add_const π, ?_⟩
    filter_upwards [hw.continuousAt.eventually_ne hx] with y hy
    have h := Complex.arg_neg_coe_angle (neg_ne_zero.mpr hy)
    rw [neg_neg, ← Real.Angle.coe_add] at h
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    exact ⟨k, by linarith⟩

end PlasmaLean.Fields

/-! ## Application: the rational stellarator -/

namespace PlasmaLean.Design.RationalStellarator
open PlasmaLean.Fields Set Filter Topology Real

/-- Cylindrical radius `R = √(x² + y²)`. -/
@[expose] def Rc (y : Space) : ℝ := √(r2 y)

/-- Distance from the exact magnetic axis `R = 1, z = 0`: `rt = √((R - 1)² + z²)`. -/
@[expose] def rt (y : Space) : ℝ := √((Rc y - 1) ^ 2 + y 2 ^ 2)

/-- The poloidal plane point `(R - 1) + i z`. -/
@[expose] def wθ (y : Space) : ℂ := ((Rc y - 1 : ℝ) : ℂ) + ((y 2 : ℝ) : ℂ) * Complex.I

/-- The horizontal point `x + i y`. -/
@[expose] def wφ (y : Space) : ℂ := ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I

/-- Poloidal angle about the axis (principal branch). -/
@[expose] def θs (y : Space) : ℝ := Complex.arg (wθ y)

/-- Toroidal angle (principal branch). -/
@[expose] def φs (y : Space) : ℝ := Complex.arg (wφ y)

/-- The function `(a, b) ↦ √((√a - 1)² + b²)`, so that `rt = rtF ∘ (r₂, z)`. -/
@[expose] def rtF (p : ℝ × ℝ) : ℝ := √((√p.1 - 1) ^ 2 + p.2 ^ 2)

/-- The map `y ↦ (r₂, z)`. -/
@[expose] def rzP (y : Space) : ℝ × ℝ := (r2 y, y 2)

/-- `rt` factors through `(r₂, z)`. -/
theorem rt_eq_comp : rt = rtF ∘ rzP := rfl

/-- `rt ≥ 0`. -/
theorem rt_nonneg (y : Space) : 0 ≤ rt y := Real.sqrt_nonneg _

/-- `rt` is continuous on all of space. -/
theorem continuous_rt : Continuous rt := by
  unfold rt Rc r2; fun_prop

/-- `rt² = (R - 1)² + z²`. -/
theorem rt_sq (y : Space) : rt y ^ 2 = (Rc y - 1) ^ 2 + y 2 ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Inside the tube `rt < 1/2` the point is off the `z`-axis. -/
theorem r2_pos_of_rt_lt {y : Space} (hy : rt y < 1 / 2) : 0 < r2 y := by
  by_contra h
  push Not at h
  have hR : Rc y = 0 := Real.sqrt_eq_zero'.mpr h
  have hsq := rt_sq y
  rw [hR] at hsq
  nlinarith [rt_nonneg y, sq_nonneg (y 2)]

/-- `rtF` is differentiable at `(r₂, z)` off the `z`-axis and off the magnetic axis. -/
theorem differentiableAt_rtF {y : Space} (hr2 : 0 < r2 y) (hrt : 0 < rt y) :
    DifferentiableAt ℝ rtF (rzP y) := by
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => √p.1) (rzP y) :=
    differentiableAt_fst.sqrt (ne_of_gt hr2)
  have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => (√p.1 - 1) ^ 2 + p.2 ^ 2) (rzP y) :=
    ((h1.sub_const 1).pow 2).add (differentiableAt_snd.pow 2)
  refine h2.sqrt ?_
  intro h0
  have : rt y = 0 := by
    change √((√(r2 y) - 1) ^ 2 + y 2 ^ 2) = 0
    simp only [rzP] at h0
    rw [h0, Real.sqrt_zero]
  linarith

/-- Derivative of `y ↦ (r₂, z)`. -/
theorem hasFDerivAt_rzP (y : Space) :
    HasFDerivAt rzP ((lin (2 * y 0) (2 * y 1) 0).prod (pr 2)) y :=
  (hasFDerivAt_r2 y).prodMk (hasFDerivAt_coord y 2)

/-- `rt` is differentiable off the `z`-axis and off the magnetic axis. -/
theorem differentiableAt_rt {y : Space} (hr2 : 0 < r2 y) (hrt : 0 < rt y) :
    DifferentiableAt ℝ rt y := by
  rw [rt_eq_comp]
  exact (differentiableAt_rtF hr2 hrt).comp y (hasFDerivAt_rzP y).differentiableAt

/-- Real-valued differentiable functions stay differentiable after coercion to `ℂ`. -/
theorem differentiableAt_ofReal {f : Space → ℝ} {y : Space} (hf : DifferentiableAt ℝ f y) :
    DifferentiableAt ℝ (fun x => (f x : ℂ)) y :=
  Complex.ofRealCLM.differentiableAt.comp y hf

/-- `a + b i ≠ 0` unless `a = b = 0`. -/
theorem mk_ne_zero {a b : ℝ} (h : ¬ (a = 0 ∧ b = 0)) : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simpa using And.intro h1 h2

/-- **Tubular coordinates about the exact axis** of the rational stellarator: tube `rt < 1/2`,
radius `rt`, poloidal angle `θs`, toroidal angle `φs`. -/
@[expose] def tube : TubeCoords where
  T := {y | rt y < 1 / 2}
  r := rt
  θ := θs
  φ := φs
  isOpen_T := isOpen_lt continuous_rt continuous_const
  continuousOn_r := continuous_rt.continuousOn
  differentiableAt_r := fun y hy hr => differentiableAt_rt (r2_pos_of_rt_lt hy) hr
  lift_θ := fun y hy hr => by
    have hr2 := r2_pos_of_rt_lt hy
    have hR : DifferentiableAt ℝ Rc y :=
      (hasFDerivAt_r2 y).differentiableAt.sqrt (ne_of_gt hr2)
    refine exists_arg_lift (w := wθ) ?_ ?_
    · exact (differentiableAt_ofReal (hR.sub_const 1)).add
        ((differentiableAt_ofReal (hasFDerivAt_coord y 2).differentiableAt).mul_const _)
    · refine mk_ne_zero fun ⟨h1, h2⟩ => ?_
      have : rt y = 0 := by
        change √((Rc y - 1) ^ 2 + y 2 ^ 2) = 0
        rw [h1, h2]; simp
      linarith
  lift_φ := fun y hy _ => by
    have hr2 := r2_pos_of_rt_lt hy
    refine exists_arg_lift (w := wφ) ?_ ?_
    · exact (differentiableAt_ofReal (hasFDerivAt_coord y 0).differentiableAt).add
        ((differentiableAt_ofReal (hasFDerivAt_coord y 1).differentiableAt).mul_const _)
    · refine mk_ne_zero fun ⟨h1, h2⟩ => ?_
      simp only [r2, h1, h2] at hr2
      norm_num at hr2

/-- The closed sub-tube `rt ≤ R₁` (`R₁ < 1/2`) is closed in space. -/
theorem isClosed_subTube {R₁ : ℝ} (hR₁ : R₁ < 1 / 2) :
    IsClosed {x | x ∈ tube.T ∧ tube.r x ≤ R₁} := by
  have e : {x | x ∈ tube.T ∧ tube.r x ≤ R₁} = {x | rt x ≤ R₁} := by
    ext x
    simp only [tube, mem_ofPred_eq, and_iff_right_iff_imp]
    intro h; linarith
  rw [e]
  exact isClosed_le continuous_rt continuous_const

/-- **Conditional all-time confinement for the rational stellarator.** Suppose a torus profile
`ρ(θ, φ)` with `0 < ρ_min ≤ ρ ≤ R₁ < 1/2` (a torus `rt = ρ(θs, φs)` about the exact axis) is
invariant for `B_ε` in the Grönwall sense on a collar: with `G = rt - ρ(θs, φs)`,
`|DG · B_ε| ≤ L |G|` wherever `0 < rt < 1/2` and `|G| < g₀` (for an exactly invariant torus
this follows from tangency, `Fields.invariance_bound_of_tangent`). Such a `ρ` is to be supplied
by KAM (stages K2/K3). Then every two-sided field line of `B_ε` starting on the axis or inside
the torus stays inside the torus (in particular within distance `R₁` of the axis) **for all
time**. -/
theorem rationalStellarator_confined_forever_of_torus (ε : ℝ) {ρ : ℝ → ℝ → ℝ}
    {ρmin R₁ g₀ L : ℝ} (hρ : TorusProfile ρ) (hmin : 0 < ρmin) (hlo : ∀ a b, ρmin ≤ ρ a b)
    (hhi : ∀ a b, ρ a b ≤ R₁) (hR₁ : R₁ < 1 / 2) (hg₀ : 0 < g₀)
    (hinv : ∀ y, rt y < 1 / 2 → 0 < rt y → |rt y - ρ (θs y) (φs y)| < g₀ →
      |fderiv ℝ (fun x => rt x - ρ (θs x) (φs x)) y (field ε y)| ≤
        L * |rt y - ρ (θs y) (φs y)|)
    {γ : ℝ → Space} (hγ : IsFieldLine (field ε) γ)
    (h0 : rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) :
    ∀ t, rt (γ t) ≤ R₁ ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  have hR₁0 : 0 ≤ R₁ := hmin.le.trans ((hlo 0 0).trans (hhi 0 0))
  have hin0 : γ 0 ∈ tube.inside ρ := by
    rcases h0 with h | h
    · exact ⟨show rt (γ 0) < 1 / 2 by linarith, Or.inl h.le⟩
    · exact ⟨show rt (γ 0) < 1 / 2 by linarith [hhi (θs (γ 0)) (φs (γ 0))], Or.inr h⟩
  have htrap := torus_trapping_forever (c := tube) (B := field ε) hρ hmin hlo hhi
    (isClosed_subTube hR₁) hg₀ (fun x hx hr hG => hinv x hx hr hG) hγ hin0
  intro t
  have ht := htrap t
  refine ⟨(TubeCoords.inside_subset_closedTube hR₁0 hhi ht).2, ?_⟩
  rcases ht.2 with h | h
  · exact Or.inl (le_antisymm h (rt_nonneg _))
  · exact Or.inr h

/-! ### Non-vacuity: the axisymmetric case `ε = 0` -/

/-- `B_0 = ∇φ` is tangent to every circular torus `rt = const`: `D rt · ∇φ = 0`. -/
theorem toroidal_invariance {y : Space} (hr2 : 0 < r2 y) (hrt : 0 < rt y) :
    fderiv ℝ rt y (toroidal y) = 0 := by
  have h := (differentiableAt_rtF hr2 hrt).hasFDerivAt.comp y (hasFDerivAt_rzP y)
  rw [← rt_eq_comp] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have hz : ((lin (2 * y 0) (2 * y 1) 0).prod (pr 2)) (toroidal y) = 0 := by
    ext
    · simp only [ContinuousLinearMap.prod_apply, lin_apply, toroidal, Prod.fst_zero]
      simp
      ring
    · simp [toroidal]
  rw [hz, map_zero]

/-- For `ε = 0` the invariance hypothesis of `rationalStellarator_confined_forever_of_torus`
holds exactly (`L = 0`) for every constant profile `ρ ≡ c₀`. -/
theorem eps0_invariance (c₀ : ℝ) (y : Space) (hy : rt y < 1 / 2) (hrt : 0 < rt y) :
    |fderiv ℝ (fun x => rt x - (fun _ _ => c₀) (θs x) (φs x)) y (field 0 y)| ≤
      0 * |rt y - (fun _ _ => c₀) (θs y) (φs y)| := by
  have hf : field 0 y = toroidal y := by simp [field]
  simp only [fderiv_sub_const, hf, toroidal_invariance (r2_pos_of_rt_lt hy) hrt, abs_zero,
    zero_mul, le_refl]

/-- **Non-vacuous instance** of the conditional theorem: for `ε = 0` and `0 < c₀ < 1/2`, every
two-sided field line of `B_0 = ∇φ` starting within distance `c₀` of the axis stays there for all
time (every hypothesis of `rationalStellarator_confined_forever_of_torus` is discharged). -/
theorem rationalStellarator_eps0_confined_forever {c₀ : ℝ} (hc : 0 < c₀) (hc' : c₀ < 1 / 2)
    {γ : ℝ → Space} (hγ : IsFieldLine (field 0) γ) (h0 : rt (γ 0) < c₀) :
    ∀ t, rt (γ t) < c₀ := by
  intro t
  have h := rationalStellarator_confined_forever_of_torus 0 (ρ := fun _ _ => c₀)
    (torusProfile_const c₀) hc (fun _ _ => le_rfl) (fun _ _ => le_rfl) hc' one_pos
    (fun y hy hr _ => eps0_invariance c₀ y hy hr) hγ (Or.inr h0) t
  rcases h.2 with h' | h'
  · rw [h']; exact hc
  · exact h'

/-- The exact axis is a two-sided field line of `B_ε` for every `ε`. -/
theorem axis_isFieldLine (ε : ℝ) : IsFieldLine (field ε) axis := by
  intro t
  rw [field_axis]
  have hγ : axis = fun s => Real.cos s • basis 0 + Real.sin s • basis 1 := by
    funext s; ext k; fin_cases k <;> simp [axis, basis]
  rw [hγ]
  have := ((Real.hasDerivAt_cos t).smul_const (basis 0)).add
    ((Real.hasDerivAt_sin t).smul_const (basis 1))
  convert this using 1
  ext k; fin_cases k <;> simp [basis]

/-- The axis lies on `rt = 0`, so it starts inside every admissible torus. -/
theorem axis_inside (t : ℝ) : rt (axis t) = 0 := by
  have hr : r2 (axis t) = 1 := by simp [r2, axis, Real.cos_sq_add_sin_sq]
  have hz : axis t 2 = 0 := by simp [axis]
  simp only [rt, Rc, hr, hz]
  norm_num

end PlasmaLean.Design.RationalStellarator

