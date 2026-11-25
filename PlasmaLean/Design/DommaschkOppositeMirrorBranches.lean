/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOppositeMirrorSlope

/-! # Two ordered first-mirror branches across the full height band on an opposite-section path -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeMirrorBranches
open Set Real Certificates PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign DommaschkOppositeMirrorSlope
open DommaschkPhysicalFirstMirrorValues
open DommaschkEndpointMirrorBranch (Growth branch)
open DommaschkJacobian (euclideanFlow)
open Kinetic.MirrorHeightBand (Branch)
set_option maxRecDepth 16000

def Window (entry : State) (back : Bool) (rs : List Step) (a b rate : ℝ) : Prop :=
  ∀ {y : ℝ → Plane} {T : ℝ}, b < T →
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow (π/2) 1 t (y t)) (Icc (-T) T) t) →
    (∀ v ∈ physicalSlabs entry 0 rs, ∀ t ∈ Icc v.start v.stop, y (clock back t) ∈ v.tube t) →
    Growth (profile (π/2) y back) a b rate

theorem Window.append {s : State} {back : Bool} {rs : List Step} {a b c rate : ℝ}
    (left : Window s back rs a b rate) (right : Window s back rs b c rate) (bc : b ≤ c) :
    Window s back rs a c rate := by
  intro y T hT ode box
  exact (left (bc.trans_lt hT) ode box).append (right hT ode box)

theorem Window.tail {s : State} {back : Bool} {rs : List Step} {a b k : ℝ}
    (verified : Window s back rs a b k) (tail : List Step) : Window s back (rs++tail) a b k := by
  intro y T room ode inside
  apply verified room ode
  intro v hv
  apply inside v
  suffices ∀ (rr : List Step) (x : State) (t : ℝ),
      v ∈ physicalSlabs x t rr → v ∈ physicalSlabs x t (rr++tail) from this rs s 0 hv
  intro rr
  induction rr with
  | nil => simp [physicalSlabs]
  | cons r rest ih =>
    intro x t mem
    simp only [List.cons_append,physicalSlabs,List.mem_cons] at mem ⊢
    exact mem.imp_right (ih _ _)

private theorem outward_ode {y : ℝ → Plane} {T t : ℝ} (back : Bool) (ht : t ∈ Ioo 0 T)
    (ode : ∀ u ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow (π/2) 1 u (y u)) (Icc (-T) T) u) :
    HasDerivAt (fun s => y (clock back s)) (euclideanFlow (π/2) (direction back) t (y (clock back t))) t := by
  cases back
  · have h : t ∈ Ioo (-T) T := ⟨by linarith [ht.1,ht.2],ht.2⟩
    exact (ode t (Ioo_subset_Icc_self h)).hasDerivAt (Icc_mem_nhds h.1 h.2)
  · have h : -t ∈ Ioo (-T) T := ⟨by linarith [ht.2],by linarith [ht.1,ht.2]⟩
    have d := (ode (-t) (Ioo_subset_Icc_self h)).hasDerivAt (Icc_mem_nhds h.1 h.2)
    have flip : -euclideanFlow (π/2) 1 (-t) (y (-t)) = euclideanFlow (π/2) (-1) t (y (-t)) := by
      ext j
      fin_cases j <;> simp [euclideanFlow,DommaschkBounceField.physicalFlow]
    simpa only [Function.comp_def,neg_one_smul,flip,clock,direction,↓reduceIte] using
      d.scomp t (hasDerivAt_neg t)

theorem row_window {rs : List Step} {s : State} {back : Bool} {i : ℕ} {k : ℝ}
    (hi : i < rs.length) (hp : 0 < i) (checked : SlabSlope back rs[i] (i/64) (((i:ℝ)+1)/64) k) :
    Window s back rs (i/64) (((i:ℝ)+1)/64) k := by
  intro y T room ode inside t ht
  obtain ⟨prev,mem⟩ := DommaschkSignedObservable.slab_at s 0 hi
  rw [zero_add] at mem
  have tube := inside _ mem t (show t ∈ Icc ((i:ℝ)/64) ((i:ℝ)/64+1/64) by
    rwa [show (i:ℝ)/64+1/64=(i+1:ℝ)/64 by ring])
  have pos : (0:ℝ) < i := by exact_mod_cast hp
  have he := checked t ht (fun a => y (clock back a)) prev tube
    (outward_ode back ⟨(by positivity : 0 < (i:ℝ)/64).trans_le ht.1,ht.2.trans_lt room⟩ ode)
  change DommaschkSignedMirrorBand.Rate (fun a => strength (π/2+clock back a) (y (clock back a))) k t
  cases back <;> simpa only [clock,direction,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] using he

def FirstBranches (e : MirrorEndpoint) (c : Checkpoint) (k j : ℕ)
    (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) : Prop :=
  let phase := azimuth e.opposite
  let T := (c.length : ℝ)/64
  ∃ y : ℝ → Plane, y (φ-phase) = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) T) t) ∧
    (∀ v ∈ physicalSlabs e.start 0 c.forwardRows, ∀ t ∈ Icc v.start v.stop, y t ∈ v.tube t) ∧
    (∀ v ∈ physicalSlabs e.start 0 c.backwardRows, ∀ t ∈ Icc v.start v.stop, y (-t) ∈ v.tube t) ∧
    ∀ back, Nonempty (Branch (profile phase y back) (k/64) (((j:ℝ)+1)/64)
      (height false) (height true) (1/256))

/-- Strict incoming signs, the high cap and the complete slope window pick out a
continuous, strictly ordered first-contact time at every intermediate mirror height. -/
theorem from_passage {e : MirrorEndpoint} {c : Checkpoint} {k j : ℕ} {uC zC uA zA : Theory.KAM.FA} {φ : ℝ}
    (path : c.Passage e uC zC uA zA φ) (phase : azimuth e.opposite = π/2)
    (fr : Side (azimuth e.opposite) e.start false k j c.forwardRows)
    (br : Side (azimuth e.opposite) e.start true k j c.backwardRows)
    (fw : Window e.start false c.forwardRows (k/64) (((j:ℝ)+1)/64) (1/256))
    (bw : Window e.start true c.backwardRows (k/64) (((j:ℝ)+1)/64) (1/256))
    (lf : c.forwardRows.length = c.length) (lb : c.backwardRows.length = c.length)
    (room : j+1 < c.length) (angle : |φ-azimuth e.opposite| ≤ 1/64) :
    FirstBranches e c k j uC zC uA zA φ := by
  obtain ⟨_,_,y,_,_,_,_,_,yb,_,_,ode,ft,bt,_⟩ :=
    DommaschkPhysicalFirstMirrorValues.from_passage path fr br lf lb angle
  refine ⟨y,yb,ode,ft,bt,?_⟩
  have room' : ((j:ℝ)+1)/64 < c.length/64 := by
    exact div_lt_div_of_pos_right (show (j:ℝ)+1 < c.length by exact_mod_cast room) (by norm_num)
  have ab : (k:ℝ)/64 < ((j:ℝ)+1)/64 := by
    have h : (k:ℝ) ≤ j := by exact_mod_cast fr.before
    linarith
  obtain ⟨_,fe,fc⟩ := fr.inputs ft
  obtain ⟨_,be,bc⟩ := br.inputs bt
  rw [phase] at ode ⊢ fe fc be bc
  intro back
  cases back
  · exact branch (by positivity) ab (by norm_num [height]) (by norm_num [height]) (by norm_num)
      (fun _ => norm_nonneg _) fe fc (fw room' ode ft)
  · exact branch (by positivity) ab (by norm_num [height]) (by norm_num [height]) (by norm_num)
      (fun _ => norm_nonneg _) be bc (bw room' ode bt)

end PlasmaLean.Design.DommaschkOppositeMirrorBranches
