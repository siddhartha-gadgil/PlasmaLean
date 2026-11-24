/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorEndpointSign
public import PlasmaLean.Design.DommaschkSignedObservable
public import PlasmaLean.Design.DommaschkPositionFramesFwd
public import PlasmaLean.Design.DommaschkPositionFramesBack

/-! # Uniform spatial bounds on both signed pilot archives -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedTraceDomain

open Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
open DommaschkSignedObservable Set

/-- Closed cylindrical envelope in the physical coordinates of the archived field line. -/
def Region (x : Plane) : Prop := (7 / 8 ≤ x 0 ∧ x 0 ≤ 1) ∧ |x 1| ≤ 5 / 64

/-- Exact bounds on the two polynomial ranges enlarged by the physical tube radius. -/
def packed (r : Step) : Bool :=
  leQ ((r.physicalOut : ℚ) / 2^80 + magnitude (difference (polynomial r 0) [15/16])) (1/16) &&
  leQ ((r.physicalOut : ℚ) / 2^80 + magnitude (difference (polynomial r 1) [0])) (5/64)

theorem region_of_mem {r : Step} {s : State} {a t : ℝ} {x : Plane} (check : packed r = true)
    (ht : t ∈ Icc a (a + 1 / 64)) (hx : x ∈ (physicalSlab s r a).tube t) : Region x := by
  have input (j : Fin 2) : (⟨polynomial r j, (r.physicalOut : ℚ) / 2^80⟩ : Model).Mem
      (coord a t) (x j) := by
    have e := DommaschkMirrorEndpointSign.coordinate hx j
    change |x j - Certificates.QPoly.eval (polynomial r j) (coord a t)| ≤ _ at e
    simpa only [Model.Mem, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using e
  obtain ⟨rad, vert⟩ := Bool.and_eq_true_iff.mp check
  have r0 := enclose (c := ⟨[15/16], 1/16⟩) (abs_coord_le ht) (input 0) (leQ_true.mp rad)
  have r1 := enclose (c := ⟨[0], 5/64⟩) (abs_coord_le ht) (input 1) (leQ_true.mp vert)
  norm_num [Model.Mem, Certificates.QPoly.eval_cons, Certificates.QPoly.eval_nil, abs_le] at r0 r1
  exact ⟨⟨by linarith [r0.1], by linarith [r0.2]⟩, abs_le.mpr r1⟩

theorem tubes {rows : List Step} (valid : ∀ r ∈ rows, packed r = true) (s : State) (a : ℝ) :
    OnTubes (fun _ p => Region p) s a rows := by
  induction rows generalizing s a with
  | nil => trivial
  | cons r rs ih =>
    exact ⟨fun _ ht _ hx => region_of_mem (valid _ List.mem_cons_self) ht hx,
      ih (fun q h => valid q (List.mem_cons_of_mem _ h)) _ _⟩

set_option maxRecDepth 2048 in
theorem forward_archive : DommaschkPositionFramesFwd.blocks.flatten.all packed = true := by
  with_unfolding_all rfl

set_option maxRecDepth 2048 in
theorem backward_archive : DommaschkPositionFramesBack.blocks.flatten.all packed = true := by
  with_unfolding_all rfl

/-- Both signed branches of any checked pilot prefix stay in the same closed envelope. -/
theorem on_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path n fs bs fr br x y) (hn : 0 < n)
    (frows : fr = DommaschkPositionFramesFwd.blocks.flatten.take n)
    (brows : br = DommaschkPositionFramesBack.blocks.flatten.take n)
    (lf : fr.length = n) (lb : br.length = n) :
    ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t) := by
  have f := tubes (rows := fr)
    (fun r hr => List.all_eq_true.mp forward_archive r (List.mem_of_mem_take (frows ▸ hr)))
    (DommaschkMirrorLaunch.MirrorEndpoint.start .q0r470) 0
  have b := tubes (rows := br)
    (fun r hr => List.all_eq_true.mp backward_archive r (List.mem_of_mem_take (brows ▸ hr)))
    (DommaschkMirrorLaunch.MirrorEndpoint.start .q0r470) 0
  have nonempty {rs : List Step} (len : rs.length = n) : rs ≠ [] := by
    rintro rfl
    simp at len
    omega
  have fp := f.on_nonempty_prefix (post := []) (y := y) (nonempty lf)
    (by simpa using path.forward)
  have bp := b.on_nonempty_prefix (post := []) (y := fun t => y (-t)) (nonempty lb)
    (by simpa using path.backward)
  simp only [lf, lb, zero_add] at fp bp
  intro t ht
  rcases le_total 0 t with hp | hm
  · exact fp t ⟨hp, ht.2⟩
  · simpa only [neg_neg] using bp (-t) ⟨neg_nonneg.mpr hm, by linarith [ht.1]⟩

end PlasmaLean.Design.DommaschkSignedTraceDomain
