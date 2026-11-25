/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOppositeMirrorBranches

/-! # Locating the two endpoint levels on the same transverse first-contact branch -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeMirrorLocalization
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign DommaschkPhysicalFirstMirrorValues
open DommaschkOppositeMirrorBranches
open DommaschkJacobian (euclideanFlow)
open Kinetic.MirrorHeightBand (Branch)

theorem between {f : ℝ → ℝ} {a b L U k l r : ℝ} (q : Branch f a b L U k) (h : Icc L U)
    (lb : l ≤ b) (hr : 0 ≤ r) (lo : f l < h) (hi : (h:ℝ) < f r) : q.time h ∈ Ioo l r := by
  constructor
  · by_contra! bad
    obtain eq | lt := bad.eq_or_lt
    · exact (ne_of_lt lo) (eq ▸ q.hit h)
    · exact (not_lt_of_ge lo.le) (q.after h l ⟨lt,lb⟩)
  · by_contra! bad
    obtain eq | lt := bad.eq_or_lt
    · exact (ne_of_gt hi) (eq.symm ▸ q.hit h)
    · exact (not_lt_of_ge hi.le) (q.before h r ⟨hr,lt⟩)

def lowLevel : Icc (height false : ℝ) (height true) :=
  ⟨height false, le_rfl, by norm_num [height]⟩

def highLevel : Icc (height false : ℝ) (height true) :=
  ⟨height true, by norm_num [height], le_rfl⟩

def OnClock (s : State) (back : Bool) (rs : List Step) (y : ℝ → Plane) : Prop :=
  ∀ v ∈ physicalSlabs s 0 rs, ∀ t ∈ Icc v.start v.stop, y (clock back t) ∈ v.tube t

theorem OnClock.prefix {s : State} {back : Bool} {rs tail : List Step} {y : ℝ → Plane}
    (enclosed : OnClock s back (rs++tail) y) : OnClock s back rs y := by
  intro v hv
  apply enclosed
  suffices ∀ (rr : List Step) (x : State) (t : ℝ),
      v ∈ physicalSlabs x t rr → v ∈ physicalSlabs x t (rr++tail) from this rs s 0 hv
  intro rr
  induction rr with
  | nil => simp [physicalSlabs]
  | cons r rest ih =>
    intro x t mem
    simp only [List.cons_append,physicalSlabs,List.mem_cons] at mem ⊢
    exact mem.imp_right (ih _ _)

theorem OnClock.at_node {s : State} {back : Bool} {rs : List Step} {y : ℝ → Plane}
    (enclosed : OnClock s back rs y) {i : ℕ} (hi : i < rs.length) {t : ℝ}
    (ht : t ∈ Icc ((i:ℝ)/64) ((i:ℝ)/64+1/64)) :
    ∃ prev, y (clock back t) ∈ (physicalSlab prev rs[i] (i/64)).tube t := by
  obtain ⟨prev,mem⟩ := DommaschkSignedObservable.slab_at s 0 hi
  rw [zero_add] at mem
  exact ⟨prev,enclosed _ mem t ht⟩

/-- The observed bounds are on elapsed time along each signed direction from the section. -/
def Located (e : MirrorEndpoint) (c : Checkpoint) (k j l r u v : ℕ)
    (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) : Prop :=
  let phase := azimuth e.opposite
  let T := (c.length : ℝ)/64
  ∃ y : ℝ → Plane, y (φ-phase) = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) T) t) ∧
    OnClock e.start false c.forwardRows y ∧ OnClock e.start true c.backwardRows y ∧
    ∀ back, ∃ q : Branch (profile phase y back) (k/64) (((j:ℝ)+1)/64)
      (height false) (height true) (1/256),
      q.time lowLevel ∈ Ioo ((l:ℝ)/64) ((r:ℝ)/64) ∧
      q.time highLevel ∈ Ioo ((u:ℝ)/64) ((v:ℝ)/64)

end PlasmaLean.Design.DommaschkOppositeMirrorLocalization
