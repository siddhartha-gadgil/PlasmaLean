/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedMirrorBand
public import PlasmaLean.Design.DommaschkEndpointSignedTrace

/-! # Mirror-height branches on any phase-zero outward trace -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkEndpointMirrorBranch
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkJacobian
open DommaschkSignedMirrorBand DommaschkEndpointSignedTrace Kinetic.MirrorHeightBand Set

/-- Interior ODE evidence and the actual spatial enclosures on one outward branch. -/
structure Outward (entry : State) (rows : List Step) (sign T : ℝ) (y : ℝ → Plane) : Prop where
  ode : ∀ t ∈ Ioo 0 T, HasDerivAt y (euclideanFlow 0 sign t (y t)) t
  contained : ∀ s ∈ physicalSlabs entry 0 rows, ∀ t ∈ Icc s.start s.stop, y t ∈ s.tube t

private theorem mem_extend {pre post : List Step} {s : Fields.TrajectorySlabs.Slab Plane}
    {a : ℝ} {v : State} (inside : s ∈ physicalSlabs v a pre) :
    s ∈ physicalSlabs v a (pre ++ post) := by
  induction pre generalizing v a with
  | nil => simp [physicalSlabs] at inside
  | cons r rs ih =>
    simp only [List.cons_append,physicalSlabs,List.mem_cons] at inside ⊢
    exact inside.imp_right (fun hs => ih hs)

theorem Outward.prefix {entry : State} {pre post : List Step} {sign T : ℝ} {y : ℝ → Plane}
    (path : Outward entry (pre ++ post) sign T y) : Outward entry pre sign T y :=
  ⟨path.ode, fun s hs => path.contained s (mem_extend hs)⟩

/-- Both signed branches belong to the same path supplied by the physical chain. -/
theorem of_joined {entry : State} {fr br : List Step} {x : Plane} {fe be : Set Plane} {T : ℝ}
    (joined : Joined 0 T x fe be (physicalSlabs entry 0 fr) (physicalSlabs entry 0 br)) :
    ∃ y : ℝ → Plane, y 0 = x ∧ Outward entry fr 1 T y ∧
      Outward entry br (-1) T (fun t => y (-t)) := by
  obtain ⟨y, hy, _, _, ode, forward, backward⟩ := joined
  have both (t : ℝ) (ht : t ∈ Ioo 0 T) :
      t ∈ Ioo (-T) T ∧ -t ∈ Ioo (-T) T := by
    obtain ⟨lo,hi⟩ := ht
    constructor <;> constructor <;> linarith
  refine ⟨y,hy,⟨?_,forward⟩,⟨?_,backward⟩⟩
  · intro t ht
    have h := (both t ht).1
    exact (ode t (Ioo_subset_Icc_self h)).hasDerivAt (Icc_mem_nhds h.1 h.2)
  · intro t ht
    have h := (both t ht).2
    have d := (ode (-t) (Ioo_subset_Icc_self h)).hasDerivAt (Icc_mem_nhds h.1 h.2)
    have flip : -euclideanFlow 0 1 (-t) (y (-t)) = euclideanFlow 0 (-1) t (y (-t)) := by
      ext i
      fin_cases i <;> simp [euclideanFlow,DommaschkBounceField.physicalFlow]
    simpa only [Function.comp_def,neg_one_smul,flip] using d.scomp t (hasDerivAt_neg t)

theorem Outward.at_row {entry : State} {rows : List Step} {sign T : ℝ} {y : ℝ → Plane}
    (path : Outward entry rows sign T y) {i : ℕ} (hi : i < rows.length) :
    ∃ prev, ∀ t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64),
      y t ∈ (physicalSlab prev rows[i] (i / 64)).tube t := by
  obtain ⟨prev,mem⟩ := DommaschkSignedObservable.slab_at entry 0 hi
  rw [zero_add] at mem
  refine ⟨prev,fun t ht => path.contained _ mem t ?_⟩
  change t ∈ Icc ((i : ℝ) / 64) ((i : ℝ) / 64 + 1 / 64)
  rwa [show (i : ℝ) / 64 + 1 / 64 = (i + 1 : ℝ) / 64 by ring]

/-- Checked squared-strength rates on a closed interval, including internal slab boundaries. -/
def Growth (f : ℝ → ℝ) (a b k : ℝ) : Prop := ∀ t ∈ Icc a b, Rate f k t

theorem Growth.append {f : ℝ → ℝ} {a b c k : ℝ} (left : Growth f a b k)
    (right : Growth f b c k) : Growth f a c k := by
  intro t ht
  rcases le_total t b with he | he
  · exact left t ⟨ht.1,he⟩
  · exact right t ⟨he,ht.2⟩

theorem Outward.growth {entry : State} {rows : List Step} {sign T k : ℝ} {y : ℝ → Plane}
    (path : Outward entry rows sign T y) {i : ℕ} (hi : i < rows.length) (pos : 0 < i)
    (within : (i + 1 : ℝ) / 64 < T)
    (rate : SlabSlope rows[i] sign (i / 64) ((i + 1 : ℝ) / 64) k) :
    Growth (fun t => strength (sign * t) (y t)) (i / 64) ((i + 1 : ℝ) / 64) k := by
  obtain ⟨prev,h⟩ := path.at_row hi
  intro t ht
  apply rate t ht y prev (h t ht)
  apply path.ode t
  have hp : (0 : ℝ) < i := by exact_mod_cast pos
  exact ⟨(by positivity : 0 < (i : ℝ) / 64).trans_le ht.1,ht.2.trans_lt within⟩

/-- A certified common-height branch requires only the positive derivative of the squared
strength, the earlier strict bound, and one exterior upper cap. The derivative supplies
continuity of the nonnegative strength, also at both ends of the bracket. -/
theorem branch {f : ℝ → ℝ} {a b L U k : ℝ} (ha : 0 ≤ a) (ab : a < b) (hL : 0 < L)
    (levels : L ≤ U) (hk : 0 < k) (nn : ∀ t, 0 ≤ f t) (early : ∀ t ∈ Icc 0 a, f t < L)
    (last : U < f b) (growth : Growth f a b k) : Nonempty (Branch f a b L U k) := by
  have cont : ContinuousOn f (Icc a b) := by
    intro t ht
    obtain ⟨v, _, d⟩ := growth t ht
    simpa only [Real.sqrt_sq (nn _)] using d.continuousAt.sqrt.continuousWithinAt (s := Icc a b)
  apply exists_branch ha ab hL hk nn cont early
  · exact intermediate_value_Ioo ab.le cont ⟨(early a ⟨ha,le_rfl⟩).trans_le levels,last⟩
  · exact fun t ht => growth t (Ioo_subset_Icc_self ht)

end PlasmaLean.Design.DommaschkEndpointMirrorBranch
