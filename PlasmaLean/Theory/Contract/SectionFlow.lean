/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormFluxSurfaceEmbedded
public import PlasmaLean.Theory.Fields.VacuumBoozerTorus
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Propagation around a field torus

Normalizing the magnetic field by its toroidal angular velocity gives a vector field whose
time is geometric toroidal angle. Grönwall on the compact image bounds the change in every
chord after one turn. Coinciding points and vanishing angular tangents therefore propagate
without constructing a global Poincaré map.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Contract

open Set Real Filter Topology Asymptotics WithLp
open PlasmaLean.Fields PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Design.RationalStellarator (toroidal toroidal_vacuum domain)
open scoped RealInnerProductSpace

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- If a change of section increases chords by a bounded factor, an initially stationary
parameter curve still has derivative zero on the new section. -/
private theorem hasDerivAt_zero_of_chord_bound {f g : ℝ → Space} {C x : ℝ}
    (h : ∀ y, dist (g y) (g x) ≤ C * dist (f y) (f x)) (hf : HasDerivAt f 0 x) :
    HasDerivAt g 0 x := by
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  simp only [smul_zero, sub_zero] at hf ⊢
  apply IsBigO.trans_isLittleO _ hf
  apply IsBigO.of_bound C
  exact Eventually.of_forall fun y => by simpa only [dist_eq_norm] using h y

/-- The return of every angular section is Lipschitz in the chord distance on its image.
The constant is uniform in both starting angles. -/
theorem FieldTorus.section_return_chord (hT : FieldTorus B R z ι)
    (hB : ∀ θ φ, ContDiffAt ℝ 1 B (cylPoint (R θ φ) φ (z θ φ))) :
    ∃ C : ℝ, ∀ θ θ' φ : ℝ,
      dist (cylTorus R z (θ + 2 * π * ι) φ) (cylTorus R z (θ' + 2 * π * ι) φ) ≤
        C * dist (cylTorus R z θ φ) (cylTorus R z θ' φ) := by
  let F := fun x : Space => (⟪toroidal x, B x⟫ : ℝ)⁻¹ • B x
  let K := Set.range (torusMap R z)
  have hs (x : Space) (hx : x ∈ K) : ContDiffAt ℝ 1 F x := by
    obtain ⟨⟨θ, φ⟩, rfl⟩ := hx
    have hm : torusMap R z (θ, φ) ∈ domain := hT.axis_dist_pos (mem_range_self _)
    have ht := (toroidal_vacuum.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ _)).contDiffAt
      (toroidal_vacuum.isOpen.mem_nhds hm)
    have hb := hB θ φ
    exact ((ht.inner ℝ hb).inv (hT.toroidalComp_ne_zero θ φ)).smul hb
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hT.isCompact_range_torusMap (f := F) (fun x hx => by
      obtain ⟨L, u, hu, h⟩ := (hs x hx).exists_lipschitzOnWith
      exact ⟨L, u, mem_nhdsWithin_of_mem_nhds hu, h⟩)
  refine ⟨exp (L * (2 * π)), ?_⟩
  intro θ θ' φ
  let path := fun (a t : ℝ) => cylTorus R z (a - φ * ι + t * ι) t
  have hd (a t : ℝ) : HasDerivAt (path a) (F (path a t)) t := by
    obtain ⟨c, hc⟩ := hT.flow_at (a - φ * ι) t
    have hangle := inner_toroidal_of_hasDerivAt hc (hasDerivAt_id t)
      (hT.R_pos (a - φ * ι + t * ι) t)
    rw [inner_smul_right] at hangle
    rw [eq_inv_of_mul_eq_one_left hangle] at hc
    exact hc
  have hm (a t : ℝ) : path a t ∈ K := ⟨(a - φ * ι + t * ι, t), rfl⟩
  have hend : φ + 2 * π ∈ Icc φ (φ + 2 * π) := ⟨by linarith [pi_pos], le_rfl⟩
  have H := dist_le_of_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => K)
    (a := φ) (b := φ + 2 * π) (fun _ _ => hL)
    (fun t _ => (hd θ t).continuousAt.continuousWithinAt) (fun t _ => (hd θ t).hasDerivWithinAt)
    (fun t _ => hm _ t) (fun t _ => (hd θ' t).continuousAt.continuousWithinAt)
    (fun t _ => (hd θ' t).hasDerivWithinAt) (fun t _ => hm _ t) le_rfl _ hend
  have start (a : ℝ) : path a φ = cylTorus R z a φ := by
    simp [path]
  have stop (a : ℝ) : path a (φ + 2 * π) = cylTorus R z (a + 2 * π * ι) φ := by
    simp only [path, show a - φ * ι + (φ + 2 * π) * ι = a + 2 * π * ι by ring, cylTorus]
    simp [cylPoint, hT.per_φ_R, hT.per_φ_z]
  simpa only [stop, start, add_sub_cancel_left, mul_comm (dist _ _)] using H

/-- One turn propagates coinciding points and stationary tangents on every poloidal section.
The assumptions consist of profile regularity and local field regularity on the torus. -/
theorem FieldTorus.section_return (hT : FieldTorus B R z ι)
    (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2))
    (hB : ∀ θ φ, ContDiffAt ℝ 1 B (cylPoint (R θ φ) φ (z θ φ))) :
    (∀ θ θ' φ, R θ φ = R θ' φ → z θ φ = z θ' φ →
      R (θ + 2 * π * ι) φ = R (θ' + 2 * π * ι) φ ∧
      z (θ + 2 * π * ι) φ = z (θ' + 2 * π * ι) φ) ∧
    (∀ θ φ, deriv (fun t => R t φ) θ = 0 ∧ deriv (fun t => z t φ) θ = 0 →
      deriv (fun t => R t φ) (θ + 2 * π * ι) = 0 ∧
      deriv (fun t => z t φ) (θ + 2 * π * ι) = 0) := by
  obtain ⟨C, hC⟩ := hT.section_return_chord hB
  constructor
  · intro θ θ' φ heR hez
    have hstart : cylTorus R z θ φ = cylTorus R z θ' φ := by simp only [cylTorus, heR, hez]
    have h := hC θ θ' φ
    rw [hstart, dist_self, mul_zero, dist_le_zero] at h
    obtain ⟨hr, hv, _⟩ := (cylPoint_eq_iff_of_pos (hT.R_pos _ _) (hT.R_pos _ _)).mp h
    exact ⟨hr, hv⟩
  · intro θ φ ⟨hr0, hz0⟩
    let T := 2 * π * ι
    have hDr (a : ℝ) := ((hR.comp (contDiff_id.prodMk (contDiff_const (c := φ)))).differentiable
      (by norm_num) a).hasDerivAt
    have hDz (a : ℝ) := ((hz.comp (contDiff_id.prodMk (contDiff_const (c := φ)))).differentiable
      (by norm_num) a).hasDerivAt
    have hstart : HasDerivAt (fun u => cylTorus R z u φ) 0 θ := by
      have h := hasDerivAt_poloidalLoop (hDr θ) (hDz θ)
      have hv : WithLp.toLp 2 ![(0 : ℝ), 0, 0] = (0 : Space) := by
        ext i
        fin_cases i <;> rfl
      change HasDerivAt (poloidalLoop R z φ) 0 θ
      simpa [Function.comp_def, hr0, hz0, hv] using h
    have hend := hasDerivAt_zero_of_chord_bound (fun y => hC y θ φ) hstart
    have h' := HasDerivAt.comp_add_const (f := fun u => cylTorus R z u φ) θ T
      (hasDerivAt_poloidalLoop (hDr (θ + T)) (hDz (θ + T)))
    have he := h'.unique hend
    have h0 := congrArg (fun v : Space => v 0) he
    have h1 := congrArg (fun v : Space => v 1) he
    have h2 := congrArg (fun v : Space => v 2) he
    simp only [PiLp.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Function.comp_def, id_eq] at h0 h1 h2
    refine ⟨?_, h2⟩
    change deriv (fun t => R t φ) (θ + T) = 0
    linear_combination cos φ * h0 + sin φ * h1 -
      deriv (fun t => R t φ) (θ + T) * (sin_sq_add_cos_sq φ)

end PlasmaLean.Contract
