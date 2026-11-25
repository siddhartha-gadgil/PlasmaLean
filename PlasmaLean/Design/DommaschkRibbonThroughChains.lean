/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkLowerActionPath
public import PlasmaLean.Design.DommaschkRadialFamilyContinuity
public import PlasmaLean.Design.DommaschkEndpointContinuation

/-! # A signed field line on a closed interior window of two outward chains -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRibbonThroughChains
open Set Certificates.PositionFrameSlabs DommaschkJacobian DommaschkEndpointSignedTrace
open DommaschkLowerActionPath DommaschkRadialFamilyContinuity DommaschkSignedTraceDomain

/-- The integer time indices and the recorded end state match exactly at both ends of a block. -/
inductive Steps (F : ℝ → Plane → Plane) : ℕ → State → ℕ → State → List Step → Prop where
  | nil (i : ℕ) (s : State) : Steps F i s i s []
  | cons {i j : ℕ} {s e : State} {r : Step} {rs : List Step}
      (head : Fields.TrajectorySlabs.Step F (physicalSlab s r (i / 64))
        (stateSet s) (stateSet (next r))) (tail : Steps F (i+1) (next r) j e rs) :
      Steps F i s j e (r::rs)

theorem Steps.append {F : ℝ → Plane → Plane} {i j k : ℕ} {s m e : State} {rs ss : List Step}
    (a : Steps F i s j m rs) (b : Steps F j m k e ss) : Steps F i s k e (rs++ss) := by
  induction a with
  | nil => exact b
  | cons head _ ih => exact .cons head (ih b)

theorem Steps.chain {F : ℝ → Plane → Plane} {i j : ℕ} {s e : State} {rs : List Step}
    (h : Steps F i s j e rs) :
    Fields.TrajectorySlabs.Chain F (i/64) (stateSet s) (j/64) (stateSet e)
      (physicalSlabs s (i/64) rs) := by
  induction h with
  | nil => exact .nil _ _
  | cons head _ ih => exact DommaschkEndpointContinuation.cons_step _ head ih

/-- Retain the individual stored row inclusions when joining at the section and restricting
to the interior of the through-going trace. Its derivative is ordinary at every row seam. -/
theorem from_chains {n : ℕ} {s : State} {fr br : List Step} {fe be : Set Plane}
    {x : Plane} {cap : ℝ} (nonempty : 0 < n) (interior : cap < n / (64 : ℝ))
    (lf : (fr.take n).length = n) (lb : (br.take n).length = n)
    (rf : (fr.take n).all packed = true) (rb : (br.take n).all packed = true)
    (f : Fields.TrajectorySlabs.Chain (euclideanFlow 0 1) 0 (stateSet s) (n / 64) fe
      (physicalSlabs s 0 (fr.take n)))
    (b : Fields.TrajectorySlabs.Chain (euclideanFlow 0 (-1)) 0 (stateSet s) (n / 64) be
      (physicalSlabs s 0 (br.take n))) (hx : x ∈ stateSet s) :
    ∃ y, y 0 = x ∧ Enclosed y (-cap) cap ∧ Tracks fr br n y := by
  obtain ⟨y,initial,trajectory⟩ := from_joined (of_chains f b hx)
  have region := regions trajectory.forward trajectory.backward nonempty lf lb rf rb
  refine ⟨y,initial,⟨?_,?_⟩,tracks_of_take trajectory.forward trajectory.backward⟩
  · intro t ht
    have middle : t ∈ Ioo (-((n : ℝ)/64)) (n / 64) :=
      ⟨lt_of_lt_of_le (neg_lt_neg interior) ht.1,ht.2.trans_lt interior⟩
    exact (trajectory.ode t (Ioo_subset_Icc_self middle)).hasDerivAt
      (Icc_mem_nhds middle.1 middle.2)
  · intro t ht
    apply region
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩

end PlasmaLean.Design.DommaschkRibbonThroughChains
