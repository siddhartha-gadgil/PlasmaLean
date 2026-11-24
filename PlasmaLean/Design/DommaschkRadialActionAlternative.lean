/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeWellAction
public import PlasmaLean.Theory.Kinetic.FirstWellContinuation

/-! # A prescribed-action or grazing alternative across the first QA2R radial bracket -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialActionAlternative

open Set Kinetic.FirstWellContinuation Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkNativeWellAction Certificates.PositionFrameSlabs

abbrev Radius := Icc (47/100 : ℝ) (239/500)
def inner : Radius := ⟨47/100, by constructor <;> norm_num⟩
def outer : Radius := ⟨239/500, by constructor <;> norm_num⟩

/-- A prescribed first-well action at a strictly intermediate radius or a first mirror
which is a local maximum on its original field line. -/
def Alternative (Y : Radius → ℝ → Plane) : Prop :=
  (∃ (u : Radius) (l r : ℝ), (u : ℝ) ∈ Ioo (47/100) (239/500) ∧
    LaunchWell (field (Y u)) 0 level l r ∧
    action (field (Y u)) (density (Y u)) l r level = target) ∨
  ∃ u l r, LaunchWell (field (Y u)) 0 level l r ∧
    (IsLocalMax (field (Y u)) l ∨ IsLocalMax (field (Y u)) r)

/-- Only the intervening profiles, arclength densities and strict end caps remain to be
supplied once the two oriented action bounds are known. -/
def OnInterpolations (y z : ℝ → Plane) : Prop :=
  ∀ (Y : Radius → ℝ → Plane) (b : ℝ), Y inner = y → Y outer = z →
    CappedFamily (fun u => field (Y u)) (fun u => density (Y u)) (fun _ => level) b →
    Alternative Y

theorem of_endpoint_wells {y z : ℝ → Plane} {l r L R : ℝ}
    (pilot : LaunchWell (field y) 0 level l r) (neighbor : LaunchWell (field z) 0 level L R)
    (low : action (field y) (density y) l r level < target)
    (high : target < action (field z) (density z) L R level) : OnInterpolations y z := by
  intro Y b left right family
  let _ : PreconnectedSpace Radius := Subtype.preconnectedSpace isPreconnected_Icc
  have wl : LaunchWell (field (Y inner)) 0 level l r := left ▸ pilot
  have wr : LaunchWell (field (Y outer)) 0 level L R := right ▸ neighbor
  rcases family.target_or_localMax wl wr (left ▸ low) (right ▸ high) with
    ⟨u, i, o, chosen, value⟩ | grazing
  · left
    refine ⟨u, i, o, ⟨lt_of_le_of_ne u.property.1 ?_, lt_of_le_of_ne u.property.2 ?_⟩,
      chosen, value⟩
    · intro h
      have same : u = inner := Subtype.ext h.symm
      subst u
      obtain ⟨rfl, rfl⟩ := chosen.unique wl
      rw [left] at value
      exact low.ne value
    · intro h
      have same : u = outer := Subtype.ext h
      subst u
      obtain ⟨rfl, rfl⟩ := chosen.unique wr
      rw [right] at value
      exact high.ne' value
  · exact Or.inr grazing

end PlasmaLean.Design.DommaschkRadialActionAlternative
