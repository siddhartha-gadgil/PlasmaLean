/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameODE

/-! # A physical field line through a checked position-frame chain

Provide field bounds on the actual packed polynomials in their recorded order.
Each endpoint then lies in the physical entry set for the next slab, even when
the reference has a jump. The same trajectory solves the ODE at the joins.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameSlabs

open Set

/-- Put the stored polynomials and frames on consecutive intervals of angle 1/64. -/
def physicalSlabs : State → ℝ → List Step → List (Fields.TrajectorySlabs.Slab Plane)
  | _, _, [] => []
  | s, a, r :: rs => physicalSlab s r a :: physicalSlabs (next r) (a+1/64) rs

/-- Field estimates for the consecutive records of one trajectory. -/
def FieldBoundsOn (F : ℝ → Plane → Plane) (J : ℝ → Plane → Plane →L[ℝ] Plane) :
    State → ℝ → List Step → Prop
  | _, _, [] => True
  | s, a, r :: rs => FieldBounds s r a F J ∧ FieldBoundsOn F J (next r) (a+1/64) rs

private theorem run_append (lim : Limits) (l r : List Step) (s : State) :
    run lim s (l ++ r) =
      ((run lim s l).1 && (run lim (run lim s l).2 r).1, (run lim (run lim s l).2 r).2) := by
  induction l generalizing s with
  | nil => simp [run]
  | cons e l ih => simp [run, ih, Bool.and_assoc]

/-- Reading the arbitrarily chunked Lean proof as an ordered flat witness
preserves its initial and final data and the exact number of steps. -/
theorem Chain.flatten {lim : Limits} {s e : State} {blocks : List (List Step)} {n : ℕ}
    (h : Chain lim s blocks n e) :
    run lim s blocks.flatten = (true, e) ∧ blocks.flatten.length = n := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons ok _ ih =>
    simp only [List.flatten_cons, run_append, ok, ih.1, Bool.true_and, List.length_append, ih.2,
      and_self]

private theorem run_physical {lim : Limits} {s e : State} {a : ℝ} {rows : List Step}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : run lim s rows = (true, e)) (bounds : FieldBoundsOn F J s a rows) :
    Fields.TrajectorySlabs.Chain F a (stateSet s) (a + rows.length/64) (stateSet e)
      (physicalSlabs s a rows) := by
  induction rows generalizing s a with
  | nil =>
    change (true,s) = (true, e) at h
    cases h
    simpa only [List.length_nil, Nat.cast_zero, zero_div, add_zero, physicalSlabs] using
      Fields.TrajectorySlabs.Chain.nil (F := F) a (stateSet e)
  | cons r rs ih =>
    have check := congrArg Prod.fst h
    change (test lim s r && (run lim (next r) rs).1) = true at check
    obtain ⟨ok,tail⟩ := Bool.and_eq_true_iff.mp check
    have endState := congrArg Prod.snd h
    change (run lim (next r) rs).2 = e at endState
    have step := physical_step ok bounds.1
    have rest := ih (Prod.ext tail endState) bounds.2
    have time : (a+1/64) + rs.length/64 = a + (r::rs).length/64 := by
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [← time]
    exact .cons step rest

/-- When all analytic inputs have been discharged for the saved records, the
scalar chain proves one physical ODE chain on exactly n/64 units of angle. -/
theorem Chain.physical {lim : Limits} {s e : State} {blocks : List (List Step)} {n : ℕ} {a : ℝ}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Chain lim s blocks n e) (bounds : FieldBoundsOn F J s a blocks.flatten) :
    Fields.TrajectorySlabs.Chain F a (stateSet s) (a + n/64) (stateSet e)
      (physicalSlabs s a blocks.flatten) := by
  obtain ⟨ok,len⟩ := h.flatten
  simpa only [len] using run_physical ok bounds

/-- The physical launch stays in all recorded Euclidean enclosures through the
declared endpoint. Its derivative also agrees with the field at internal joins. -/
theorem Chain.trajectory {lim : Limits} {s e : State} {blocks : List (List Step)} {n : ℕ} {a : ℝ}
    {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Chain lim s blocks n e) (bounds : FieldBoundsOn F J s a blocks.flatten)
    {x : Plane} (entry : x ∈ stateSet s) :
    ∃ v : ℝ → Plane, v a = x ∧ v (a+n/64) ∈ stateSet e ∧
      (∀ t ∈ Icc a (a+n/64), HasDerivWithinAt v (F t (v t)) (Icc a (a+n/64)) t) ∧
      ∀ slab ∈ physicalSlabs s a blocks.flatten,
        ∀ t ∈ Icc slab.start slab.stop, v t ∈ slab.tube t :=
  (h.physical bounds).exists_trajectory entry

/-- The physical field code uses ordinary pairs of reals indexed by Fin 2. -/
abbrev coordinates : Plane ≃L[ℝ] (Fin 2 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ => ℝ)

/-- Use the Euclidean norm for the validated dynamics of the Cartesian field. -/
def euclideanField (F : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)) (t : ℝ) (v : Plane) : Plane :=
  coordinates.symm (F t (coordinates v))

/-- The same spatial Jacobian expressed on the Euclidean plane. -/
def euclideanJacobian (D : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) : Plane →L[ℝ] Plane :=
  coordinates.symm.toContinuousLinearMap.comp (D.comp coordinates.toContinuousLinearMap)

/-- A Cartesian spatial derivative gives the exact Jacobian required by the
Euclidean trial estimates. -/
theorem hasFDerivAt_euclideanField {F : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    {D : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)} {t : ℝ} {x : Plane}
    (h : HasFDerivAt (F t) D (coordinates x)) :
    HasFDerivAt (euclideanField F t) (euclideanJacobian D) x :=
  coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp x
    (h.comp x coordinates.toContinuousLinearMap.hasFDerivAt)

/-- Return the concatenated trajectory to the original Cartesian ODE and
retain its Euclidean error in every recorded tube. -/
theorem Chain.cartesian_trajectory {lim : Limits} {s e : State} {blocks : List (List Step)}
    {n : ℕ} {a : ℝ} {F : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)} {J : ℝ → Plane → Plane →L[ℝ] Plane}
    (h : Chain lim s blocks n e) (bounds : FieldBoundsOn (euclideanField F) J s a blocks.flatten)
    {x : Fin 2 → ℝ} (entry : coordinates.symm x ∈ stateSet s) :
    ∃ v : ℝ → (Fin 2 → ℝ), v a = x ∧ coordinates.symm (v (a+n/64)) ∈ stateSet e ∧
      (∀ t ∈ Icc a (a+n/64), HasDerivWithinAt v (F t (v t)) (Icc a (a+n/64)) t) ∧
      ∀ slab ∈ physicalSlabs s a blocks.flatten, ∀ t ∈ Icc slab.start slab.stop,
        coordinates.symm (v t) ∈ slab.tube t := by
  obtain ⟨v,hv,exit,ode,tube⟩ := h.trajectory bounds entry
  refine ⟨fun t => coordinates (v t),
    (congrArg coordinates hv).trans (coordinates.apply_symm_apply x),
    by simpa only [ContinuousLinearEquiv.symm_apply_apply],?_,?_⟩
  · intro t ht
    have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (ode t ht)
    apply d.congr_deriv
    exact coordinates.apply_symm_apply _
  · intro slab hs t ht
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using tube slab hs t ht

end PlasmaLean.Certificates.PositionFrameSlabs
