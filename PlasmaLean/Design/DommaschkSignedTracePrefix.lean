/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedObservable

/-! # Restriction of a signed physical path to an initial segment in both clocks -/

@[expose] public section
noncomputable section
open Set
namespace PlasmaLean.Certificates.PositionFrameSlabs

/-- At its right endpoint a moving frame depends only on the recorded final matrix. -/
theorem frameEquiv_at_end (l r : Frame) : frameEquiv l r 1 = frameEquiv r r 0 := by
  have entry_eq (a b : ℤ) : entry a b 1 = entry b b 0 := by simp [entry]; ring
  have det_eq : affineDet l r 1 = affineDet r r 0 := by simp only [affineDet, entry_eq]
  by_cases h : affineDet r r 0 ≠ 0
  · have left : affineDet l r 1 ≠ 0 := det_eq ▸ h
    apply ContinuousLinearEquiv.ext
    funext v
    change (frameEquiv l r 1).toContinuousLinearMap v =
      (frameEquiv r r 0).toContinuousLinearMap v
    rw [frameEquiv_forward left, frameEquiv_forward h]
    simp only [forward, entry_eq]
  · simp only [frameEquiv, det_eq, h, ↓reduceDIte]

/-- Tube membership at a slab's final angle supplies the stored exit state. -/
theorem exit_of_final_tube {a : ℝ} {s : State} {r : Step} {v : Plane}
    (inTube : v ∈ (physicalSlab s r a).tube (a + 1 / 64)) : v ∈ stateSet (next r) := by
  have end_coord : coord a (a + 1 / 64) = 1 := by unfold coord; ring
  simpa only [physicalSlab, moving, end_coord, frameEquiv_at_end, reference_end,
    stateSet, next] using inTube.1

theorem physicalSlabs_take (s : State) (a : ℝ) (rows : List Step) (k : ℕ) :
    physicalSlabs s a (rows.take k) = (physicalSlabs s a rows).take k := by
  induction rows generalizing s a k with
  | nil => simp [physicalSlabs]
  | cons r rs ih => cases k <;> simp [physicalSlabs, ih]

end PlasmaLean.Certificates.PositionFrameSlabs

namespace PlasmaLean.Design.DommaschkSignedObservable
open Certificates.PositionFrameSlabs

/-- Both initial row lists keep their physical trajectory, including the actual two
exit points. A downstream certificate for the shorter path can be applied verbatim. -/
theorem Path.take_through {n i : ℕ} {fs bs : State} {fr br : List Step} {x : Plane}
    {y : ℝ → Plane} (path : Path n fs bs fr br x y) (reach : i < n)
    (hf : i < fr.length) (hb : i < br.length) :
    Path (i + 1) (next fr[i]) (next br[i]) (fr.take (i + 1)) (br.take (i + 1)) x y := by
  have size : (i : ℝ) + 1 ≤ n := by exact_mod_cast reach
  have sub : Icc (-((i + 1 : ℕ) : ℝ) / 64) (((i + 1 : ℕ) : ℝ) / 64) ⊆
      Icc (-(n : ℝ) / 64) (n / 64) := by
    apply Icc_subset_Icc <;> push_cast <;> linarith
  have clock : ((i + 1 : ℕ) : ℝ) / 64 = (i : ℝ) / 64 + 1 / 64 := by push_cast; ring
  have at_end : (i : ℝ) / 64 + 1 / 64 ∈ Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨_, pf, fwd⟩ := path.at_row reach false hf
  obtain ⟨_, pb, back⟩ := path.at_row reach true hb
  refine ⟨path.starts, ?_, ?_, fun t ht => (path.ode t (sub ht)).mono sub, ?_, ?_⟩
  · rw [neg_div, clock]
    exact exit_of_final_tube (back _ at_end)
  · rw [clock]
    exact exit_of_final_tube (fwd _ at_end)
  · rw [physicalSlabs_take]
    exact fun u hu => path.forward u (List.mem_of_mem_take hu)
  · rw [physicalSlabs_take]
    exact fun u hu => path.backward u (List.mem_of_mem_take hu)

end PlasmaLean.Design.DommaschkSignedObservable
