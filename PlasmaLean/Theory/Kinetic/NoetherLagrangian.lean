/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.Noether
public import PlasmaLean.Theory.Fields.FormCalculus
public import TauCeti.Geometry.Symplectic.Hamiltonian.Noether

/-!
# The Noether momentum of a charged particle from TauCeti's Noether theorem

`Theory/Kinetic/Noether` proves conservation of `m⟪K, v⟫ + qψ` along Lorentz orbits by
differentiating directly. This file obtains one such law from the general Noether theorem of
TauCeti (`TauCeti.noetherCharge_eq_of_eulerLagrange`), for the Lagrangian of a charged particle

`L(x, v) = (m/2)‖v‖² + q⟪A(x), v⟫`

with vector potential `A` (`B = ∇ × A`).

* `lorentzOrbit_eulerLagrange`: a Lorentz orbit (with `E = 0`) solves the Euler–Lagrange
  equation of `L`, in the form TauCeti uses.
* `noetherMomentum_translation_conserved`: if `A` is invariant under translation along `e`, the
  canonical momentum `m⟪e, v⟫ + q⟪A(x), e⟫` is conserved. It is `noetherMomentum` with
  `K = e` and `ψ = ⟪A, e⟫`, and it is TauCeti's Noether charge for the symmetry `ξ = e` with
  zero gauge term.

Scope: translation symmetries only. Rotations (the axisymmetric case of
`canonicalMomentum_conserved`) need a linear generator and, in general, a gauge term; they are
not treated here.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms WithLp
open TauCeti Topology
open scoped RealInnerProductSpace

/-- The Lagrangian of a particle of mass `m` and charge `q` in the vector potential `A`:
`L(x, v) = (m/2)‖v‖² + q⟪A(x), v⟫` (no electric field; time-independent). -/
noncomputable def lorentzLagrangian (m q : ℝ) (A : Space → Space) (_t : ℝ)
    (p : Space × Space) : ℝ :=
  m / 2 * ‖p.2‖ ^ 2 + q * ⟪A p.1, p.2⟫

/-- The momentum `∂_v L = m v♭ + q A♭`. -/
theorem hasFDerivAt_lorentzLagrangian_velocity (m q : ℝ) (A : Space → Space) (t : ℝ)
    (y u : Space) :
    HasFDerivAt (fun w => lorentzLagrangian m q A t (y, w))
      (m • innerSL ℝ u + q • innerSL ℝ (A y)) u := by
  have h1 := ((hasStrictFDerivAt_norm_sq u).hasFDerivAt).const_mul (m / 2)
  have h2 := ((innerSL ℝ (A y)).hasFDerivAt (x := u)).const_mul q
  have h := h1.add h2
  have e : (m / 2) • (2 : ℕ) • innerSL ℝ u + q • innerSL ℝ (A y)
      = m • innerSL ℝ u + q • innerSL ℝ (A y) := by
    ext w
    simp
    ring
  rw [← e]
  exact h

/-- `∂_x L = q⟪DA(x) ·, v⟫`. -/
theorem hasFDerivAt_lorentzLagrangian_position (m q : ℝ) {A : Space → Space} (t : ℝ)
    {y : Space} (u : Space) (hA : DifferentiableAt ℝ A y) :
    HasFDerivAt (fun z => lorentzLagrangian m q A t (z, u))
      (q • (innerSL ℝ u).comp (fderiv ℝ A y)) y := by
  have h2 := (((innerSL ℝ u).hasFDerivAt (x := A y)).comp y hA.hasFDerivAt).const_mul q
  have h := (hasFDerivAt_const (m / 2 * ‖u‖ ^ 2) y).add h2
  convert h using 1
  · funext z
    simp [lorentzLagrangian, real_inner_comm]
  · simp

/-- `⟪v × (∇ × A), w⟫ = ⟪DA w, v⟫ − ⟪DA v, w⟫`. -/
theorem inner_cross_curlOp (D : Space →L[ℝ] Space) (v w : Space) :
    ⟪cross v (curlOp D), w⟫ = ⟪D w, v⟫ - ⟪D v, w⟫ := by
  obtain ⟨h0, h1, h2⟩ := cross_coords v (curlOp D)
  rw [inner_coords3, inner_coords3, inner_coords3, h0, h1, h2,
    clm_coords D w 0, clm_coords D w 1, clm_coords D w 2,
    clm_coords D v 0, clm_coords D v 1, clm_coords D v 2]
  simp [curlOp]
  ring

/-- **A Lorentz orbit solves the Euler–Lagrange equation** of `lorentzLagrangian`, when
`B = ∇ × A` and `A` is differentiable: `d/dt ∂_v L = ∂_x L` along the orbit. -/
theorem lorentzOrbit_eulerLagrange {m q : ℝ} {A B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (fun u => lorentzLagrangian m q A s (x s, u)) (v s))
      (fderiv ℝ (fun y => lorentzLagrangian m q A t (y, v t)) (x t)) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t
  have hx := h.position t
  have hfun : (fun s => fderiv ℝ (fun u => lorentzLagrangian m q A s (x s, u)) (v s))
      = fun s => m • innerSL ℝ (v s) + q • innerSL ℝ (A (x s)) :=
    funext fun s => (hasFDerivAt_lorentzLagrangian_velocity m q A s (x s) (v s)).fderiv
  rw [hfun, (hasFDerivAt_lorentzLagrangian_position m q t (v t) (hA (x t))).fderiv]
  have hv' : HasDerivAt (fun s => innerSL ℝ (v s)) (innerSL ℝ a) t :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t ha
  have hA' : HasDerivAt (fun s => innerSL ℝ (A (x s)))
      (innerSL ℝ (fderiv ℝ A (x t) (v t))) t :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      ((hA (x t)).hasFDerivAt.comp_hasDerivAt t hx)
  refine ((hv'.const_smul m).add (hA'.const_smul q)).congr_deriv ?_
  ext w
  have hid := inner_cross_curlOp (fderiv ℝ A (x t)) (v t) w
  have hma : m * ⟪a, w⟫ = q * ⟪cross (v t) (curlOp (fderiv ℝ A (x t))), w⟫ := by
    have := congrArg (fun z : Space => ⟪z, w⟫) hlaw
    simpa [inner_smul_left, hcurl, fieldCurl] using this
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hma, hid, real_inner_comm (fderiv ℝ A (x t) w) (v t)]
  ring

/-- **Canonical momentum along a translation symmetry, from TauCeti's Noether theorem.** If
`B = ∇ × A` with `A` differentiable and invariant under translation along `e`, then
`m⟪e, v⟫ + q⟪A(x), e⟫` is constant along every Lorentz orbit. -/
theorem noetherMomentum_translation_conserved {m q : ℝ} {A B : Space → Space}
    {x v : ℝ → Space} {e : Space} (h : LorentzOrbit m q (fun _ => 0) B x v)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hinv : ∀ (y : Space) (s : ℝ), A (y + s • e) = A y) (s t : ℝ) :
    noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫) x v s
      = noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫) x v t := by
  have hL : ∀ r, DifferentiableAt ℝ (lorentzLagrangian m q A r) (x r, v r) := fun r => by
    unfold lorentzLagrangian
    have hA1 : DifferentiableAt ℝ (fun p : Space × Space => A p.1) (x r, v r) :=
      (hA (x r)).comp (x r, v r) differentiableAt_fst
    exact ((differentiableAt_snd.norm_sq ℝ).const_mul _).add
      ((hA1.inner ℝ differentiableAt_snd).const_mul _)
  have key := noetherCharge_eq_of_eulerLagrange (L := lorentzLagrangian m q A)
    (ξ := fun _ => e) (B := fun _ => 0) (q := x) (v := v) isOpen_univ isPreconnected_univ
    (fun r _ => h.position r) (fun r _ => lorentzOrbit_eulerLagrange h hA hcurl r)
    (fun r _ => hL r) (fun _ _ => differentiableAt_const _) (fun _ _ => differentiableAt_const _)
    (fun r _ => by
      rw [lagrangianVariation_const_eq_zero (hL r)
        (Filter.Eventually.of_forall fun σ => by simp [lorentzLagrangian, hinv])]
      simp)
    (Set.mem_univ s) (Set.mem_univ t)
  have hch : ∀ r, noetherCharge (lorentzLagrangian m q A) (fun _ => e) (fun _ => 0) r (x r, v r)
      = noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫) x v r := fun r => by
    rw [noetherCharge_apply,
      (hasFDerivAt_lorentzLagrangian_velocity m q A r (x r) (v r)).fderiv, noetherMomentum]
    simp [real_inner_comm]
  rw [← hch s, ← hch t]
  exact key

end PlasmaLean.Kinetic
