/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPreMirrorSigns
public import PlasmaLean.Certificates.TrajectoryHarmonicPacket

/-! # One normalized Taylor model for a contiguous group of signed physical slabs -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkGroupedMirrorModels
open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkMirrorEndpointSign
open DommaschkMirrorTubeCrossing Set

/-- Directed change of clock from the unit interval of one row to a subinterval of the group. -/
def Fits (a b : ℚ) (src dst : Model) : Prop :=
  src.radius + magnitude (difference src.poly (TrajectoryTrig.affine a b dst.poly)) ≤ dst.radius

private theorem eval_change (a b : ℚ) (p : List ℚ) (s : ℝ) :
    QPoly.eval (TrajectoryTrig.affine a b p) s = QPoly.eval p ((a : ℝ) + b*s) := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [TrajectoryTrig.affine, ih, mul_comm]

theorem Fits.mem {a b : ℚ} {src dst : Model} (h : Fits a b src dst) {s x : ℝ}
    (hs : |s| ≤ 1) (hx : src.Mem s x) : dst.Mem ((a : ℝ) + b*s) x := by
  have hm := enclose (c := ⟨TrajectoryTrig.affine a b dst.poly, dst.radius⟩) hs hx h
  simpa only [Model.Mem,eval_change] using hm

/-- The unshifted cylindrical coordinates and the two angular inputs at a common group clock. -/
structure Group where
  radial : Model
  height : Model
  cosine : Model
  sine : Model

def Group.Below (g : Group) (h : ℝ) : Prop :=
  ∀ {s R z t : ℝ}, |s| ≤ 1 → 0 < R → g.radial.Mem s R → g.height.Mem s z →
    g.cosine.Mem s (Real.cos (2*t)) → g.sine.Mem s (Real.sin (2*t)) →
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R t z)‖ < h

def raw (back : Bool) (r : Step) (k : Fin 2) : Model :=
  ⟨if back then QPoly.scale (-1) (polynomial r k) else polynomial r k, r.physicalOut/2^80⟩

private theorem raw_mem {r : Step} {prev : State} {a t : ℝ} {x : Plane}
    (inside : x ∈ (physicalSlab prev r a).tube t) (back : Bool) (k : Fin 2) :
    (raw back r k).Mem (coord a t) (if back then -(x k) else x k) := by
  have h := coordinate inside k
  change |x k - QPoly.eval (polynomial r k) (coord a t)| ≤ _ at h
  cases back
  · simpa only [Model.Mem,raw,Bool.false_eq_true,↓reduceIte,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h
  · simp only [Model.Mem,raw,↓reduceIte,QPoly.eval_scale,Rat.cast_neg,Rat.cast_one,
      neg_one_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
    rwa [show -(x k) - -QPoly.eval (polynomial r k) (coord a t) =
      -(x k - QPoly.eval (polynomial r k) (coord a t)) by ring, abs_neg]

/-- A finite coefficient check binds a signed physical row, including its own output radius,
to the group's common polynomial clock. -/
structure Covers {i : ℕ} (p : TrajectoryHarmonicPacket.Packet i) (back : Bool)
    (r : Step) (a b : ℚ) (g : Group) : Prop where
  clock : |a| + |b| ≤ 1
  radial : Fits a b (raw false r 0) g.radial
  height : Fits a b (raw back r 1) g.height
  cosine : Fits a b ((p false 0).model false) g.cosine
  sine : Fits a b ((p false 0).model true) g.sine
  center : magnitude (difference (polynomial r 0) [1]) ≤ 1/2
  error : r.physicalOut ≤ 2^78

set_option maxRecDepth 8192 in
theorem Covers.below {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r : Step} {a b : ℚ} {g : Group} (h : Covers p back r a b g) {H : ℝ} (below : g.Below H)
    {prev : State} {t : ℝ} {x : Plane} (ht : t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64))
    (hx : x ∈ (physicalSlab prev r (i / 64)).tube t) :
    strength (if back then -t else t) x < H := by
  have hs : |coord (i/64) t| ≤ 1 := abs_coord_le (by
    rwa [show (i : ℝ)/64 + 1/64 = (i+1 : ℝ)/64 by ring])
  have cw : coord (i/64) t = 128*t-(2*i+1 : ℝ) := by unfold coord; ring
  have bound : |(a : ℝ) + b*coord (i/64) t| ≤ 1 := calc
    _ ≤ |(a : ℝ)| + |(b : ℝ)| * |coord (i/64) t| := by
      simpa [abs_mul] using abs_add_le (a : ℝ) ((b : ℝ)*coord (i/64) t)
    _ ≤ |(a : ℝ)| + |(b : ℝ)| :=
      add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast h.clock
  have pos := DommaschkMirrorBracketSlab.positive_radius
    (a := i/64) (by rwa [show (i : ℝ)/64 + 1/64 = (i+1 : ℝ)/64 by ring]) hx h.center h.error
  have c := TrajectoryHarmonicPacket.physical p false 0 false ht
  have s := TrajectoryHarmonicPacket.physical p false 0 true ht
  have cosine : ((p false 0).model false).Mem (coord (i/64) t) (Real.cos (2*t)) := by
    simpa [cw,TrajectoryTrig.wave] using c
  have sine : ((p false 0).model true).Mem (coord (i/64) t) (Real.sin (2*t)) := by
    simpa [cw,TrajectoryTrig.wave] using s
  have sign := below bound pos (h.radial.mem hs (raw_mem hx false 0))
    (h.height.mem hs (raw_mem hx back 1)) (h.cosine.mem hs cosine) (h.sine.mem hs sine)
  cases back
  · simpa only [Bool.false_eq_true,↓reduceIte,strength] using sign
  · have symmetry := strength_reflected pos t (-(x 1))
    rw [neg_neg] at symmetry
    simpa only [↓reduceIte,strength] using symmetry.trans_lt sign

end PlasmaLean.Design.DommaschkGroupedMirrorModels
