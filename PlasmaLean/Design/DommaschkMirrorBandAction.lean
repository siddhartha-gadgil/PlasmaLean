/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedMirrorBand
public import PlasmaLean.Design.DommaschkPhysicalArcTrace
public import PlasmaLean.Design.DommaschkSignedTraceDensity

/-! # Continuous, strictly increasing physical action for a full branch of first mirrors -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorBandAction

open DommaschkSignedTraceDomain DommaschkSignedTraceDensity DommaschkSignedObservable
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel
open Kinetic.MirrorHeightBand Kinetic.CylindricalActionSensitivity
open DommaschkFirstMirrorLaunchSign Set

abbrev Heights := Icc (height false : ℝ) (height true : ℝ)

abbrev Outward (y : ℝ → Plane) (sign : ℝ) :=
  Branch (fun t => strength (sign * t) (y (sign * t))) (316 / 64) (325 / 64)
    (height false) (height true) (1 / 400)

/-- True Cartesian action integrated between the two first mirrors at the chosen height. -/
def wellAction (y : ℝ → Plane) (p : Outward y 1) (m : Outward y (-1)) (h : Heights) : ℝ :=
  physicalAction (fun t => y t 0) (fun t => y t 1) (fun t => strength t (y t))
    (-m.time h) (p.time h) h

def ActionFamily (y : ℝ → Plane) : Prop :=
  ∃ (p : Outward y 1) (m : Outward y (-1)),
    Continuous (wellAction y p m) ∧ StrictMono (wellAction y p m) ∧
    ∀ h : Heights, wellAction y p m h = Kinetic.MirrorHeightAction.action
      (fun t => strength t (y t)) (fun t => arcDensity (y t 0) t (y t 1))
      (-(325 / 64)) (325 / 64) h

/-- The forbidden caps vanish in the clipped fixed-window integral, so this
identification does not require differentiating either moving mirror. -/
theorem family {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (branches : DommaschkSignedMirrorBand.Branches y) : ActionFamily y := by
  obtain ⟨⟨fp⟩, ⟨fm⟩⟩ := branches
  let p : Outward y 1 := by simpa only [Outward, one_mul] using fp
  let m : Outward y (-1) := by simpa only [Outward, neg_one_mul] using fm
  let F := fun t => strength t (y t)
  let W := fun t => arcDensity (y t 0) t (y t 1)
  let b : ℝ := 325 / 64
  have sz : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have within : Icc (-b) b ⊆ Icc (-(n : ℝ) / 64) (n / 64) := by
    apply Icc_subset_Icc <;> dsimp [b] <;> linarith
  have cy : ContinuousOn y (Icc (-b) b) :=
    (show ContinuousOn y (Icc (-(n : ℝ) / 64) (n / 64)) from
      fun t ht => (path.ode t ht).continuousWithinAt).mono within
  have pos (t : ℝ) (ht : t ∈ Icc (-b) b) : 0 < y t 0 := by
    linarith [(region t (within ht)).1.1]
  have cf : ContinuousOn F (Icc (-b) b) := by
    simpa only [F, one_mul] using continuousOn_strength cy 1 pos
  have cw : ContinuousOn W (Icc (-b) b) :=
    continuousOn_density_region cy (fun t ht => region t (within ht))
  have wp (t : ℝ) (ht : t ∈ Icc (-b) b) : 0 < W t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) (density_lower t (region t (within ht)))
  have expressed (h : Heights) : wellAction y p m h = Kinetic.MirrorHeightAction.action F W
      (-b) b (h : ℝ) := by
    have hp := p.interior_time h
    have hm := m.interior_time h
    have ordered : -m.time h ≤ p.time h := by linarith [hp.1, hm.1]
    have cap (sign : ℝ) (branch : Outward y sign) (t : ℝ)
        (ht : t ∈ Icc (branch.time h) b) : (h : ℝ) ≤ strength (sign*t) (y (sign*t)) := by
      rcases ht.1.eq_or_lt with eq | lt'
      · exact (eq ▸ branch.hit h).ge
      · exact (branch.after h t ⟨lt', ht.2⟩).le
    have eq := Kinetic.MirrorHeightAction.action_eq_between
      (show -b ≤ -m.time h from neg_le_neg hm.2.le) ordered hp.2.le cf cw
      (h := (h : ℝ)) (left := fun t ht => by
        simpa only [F, neg_one_mul, neg_neg] using
          cap (-1) m (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      (right := fun t ht => by simpa only [F, one_mul] using cap 1 p t ht)
    rw [eq]
    apply intervalIntegral.integral_congr_Ioo_of_le ordered
    intro t ht
    have signed : t ∈ Ioo (-(n : ℝ) / 64) (n / 64) := by
      have lo := hm.2
      have hi := hp.2
      constructor <;> linarith [ht.1, ht.2]
    have R := region t (Ioo_subset_Icc_self signed)
    have den := DommaschkSignedTraceDenominator.regular t R.1 R.2
    simp only [arcDensity_on_path path signed (by linarith [R.1.1]) (by linarith), F, W]
  have fixed : wellAction y p m = fun h : Heights =>
      Kinetic.MirrorHeightAction.action F W (-b) b h := funext expressed
  have h0 : (0 : ℝ) ∈ Icc (-b) b := by constructor <;> norm_num [b]
  let low : Heights := ⟨(height false : ℝ), le_rfl, by norm_num [height]⟩
  have pf := p.interior_time low
  have launch : F 0 < height false := by
    simpa only [F, low, one_mul] using p.before low 0 ⟨le_rfl, by linarith [pf.1]⟩
  refine ⟨p, m, ?_, ?_, expressed⟩
  · rw [fixed]
    exact (Kinetic.MirrorHeightAction.continuous_action (by norm_num [b]) cf cw).comp
      continuous_subtype_val
  · rw [fixed]
    intro h j hj
    exact Kinetic.MirrorHeightAction.strictMonoOn_action (by norm_num [b]) cf cw
      (fun t ht => (wp t ht).le) ⟨0, h0, launch, wp 0 h0⟩ h.2.1 j.2.1 hj

end PlasmaLean.Design.DommaschkMirrorBandAction
