/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorSublevelQuadrature
public import PlasmaLean.Certificates.SublevelActionGrid

/-! # Counting every speed threshold in one scan of the time panels

At a branch, `high` counts the density of all samples sent to its right,
including samples equal to its cutoff. A threshold in the left subtree thus
inherits the entire right mass. Searching and updating use the same split.
-/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorSpeedHistogram
open MirrorActionQuadrature MirrorSublevelQuadrature

inductive Tree where
  | leaf
  | branch (cut high : ℕ) (lower upper : Tree)

namespace Tree

def clear : Tree → Tree
  | leaf => leaf
  | branch cut _ left right => branch cut 0 left.clear right.clear

def add (speed weight : ℕ) : Tree → Tree
  | leaf => leaf
  | branch cut high left right =>
    if speed < cut then branch cut high (left.add speed weight) right
    else branch cut (high + weight) left (right.add speed weight)

def contains (v : ℕ) : Tree → Bool
  | leaf => false
  | branch cut _ left right =>
    if v < cut then left.contains v else if cut < v then right.contains v else true

def tail (v : ℕ) : Tree → ℕ
  | leaf => 0
  | branch cut high left right =>
    if v < cut then left.tail v + high else if cut < v then right.tail v else high

@[simp] theorem contains_clear (t : Tree) (v : ℕ) : t.clear.contains v = t.contains v := by
  induction t <;> simp_all [clear, contains]

@[simp] theorem tail_clear (t : Tree) (v : ℕ) : t.clear.tail v = 0 := by
  induction t <;> simp_all [clear, tail]

@[simp] theorem contains_add (t : Tree) (v s w : ℕ) : (t.add s w).contains v = t.contains v := by
  induction t with
  | leaf => rfl
  | branch cut high left right hl hr =>
    by_cases hs : s < cut <;> simp [add, contains, hs, hl, hr]

theorem tail_add (t : Tree) (v s w : ℕ) (known : t.contains v = true) :
    (t.add s w).tail v = t.tail v + (if v ≤ s then w else 0) := by
  induction t with
  | leaf => simp [contains] at known
  | branch cut high left right hl hr =>
    by_cases hv : v < cut
    · have ih := hl (by simpa [contains, hv] using known)
      by_cases hs : s < cut
      · simp [add, tail, hs, hv, ih, Nat.add_right_comm]
      · simp [add, tail, hs, hv, show v ≤ s by omega, Nat.add_assoc]
    · by_cases hc : cut < v
      · have ih := hr (by simpa [contains, hv, hc] using known)
        by_cases hs : s < cut
        · simp [add, tail, hv, hc, hs, show ¬ v ≤ s by omega]
        · simp [add, tail, hv, hc, hs, ih]
      · have eq : v = cut := by omega
        subst v
        by_cases hs : s < cut <;> simp [add, tail, Nat.le_of_not_gt, *]

end Tree

/-- Decode each packed time cell once and put its density into the search tree. -/
def scanSlab : ℕ → ℕ → Tree → Tree
  | 0, _, t => t
  | n + 1, p, t => scanSlab n (p >>> 72) (t.add (speed p) (density p))

def scan {upper : Bool} : List (Block upper) → Tree → Tree
  | [], t => t
  | b :: bs, t => scan bs (scanSlab 48 b.packed t)

theorem slab_spec (n p : ℕ) (t : Tree) (v : ℕ) (known : t.contains v = true) :
    (scanSlab n p t).contains v = true ∧ (scanSlab n p t).tail v = t.tail v + slabTail v n p := by
  induction n generalizing p t with
  | zero => simp [scanSlab, slabTail, known]
  | succ n ih =>
    have step := ih (p >>> 72) (t.add (speed p) (density p)) (by simpa)
    simpa [scanSlab, slabTail, Tree.tail_add t v _ _ known, selectedDensity,
      Nat.add_assoc] using step

theorem scan_spec {upper : Bool} (bs : List (Block upper)) (t : Tree) (v : ℕ)
    (known : t.contains v = true) : (scan bs t).tail v = t.tail v + packetTail v bs := by
  induction bs generalizing t with
  | nil => simp [scan, packetTail]
  | cons b bs ih =>
    have step := slab_spec 48 b.packed t v known
    rw [scan, ih _ step.1, step.2]
    simp [packetTail, Nat.add_assoc]

/-- A single verified scan authenticates every closed-threshold query in its tree. -/
theorem packet_tail {upper : Bool} {bs : List (Block upper)} {hist : Tree}
    (checked : scan bs hist.clear = hist) {v : ℕ} (known : hist.contains v = true) :
    packetTail v bs = hist.tail v := by
  have replay := scan_spec bs hist.clear v (by simpa)
  simpa [checked] using replay.symm

/-- Integer speed at the appropriate end of a proposed adaptive cell. -/
def nodeTick (upper : Bool) (g : SublevelActionGrid.Table) (i : ℕ) : ℕ :=
  SublevelActionGrid.tick g (if upper then i else i + 1)

def agrees (hist : Tree) (upper : Bool) (g : SublevelActionGrid.Table) (i : ℕ) : Bool :=
  let v := nodeTick upper g i
  hist.contains v && (hist.tail v == (SublevelActionGrid.cell g i).height)

/-- Count proposed nodes that are missing from the histogram or have an incorrect arclength. -/
def failures (hist : Tree) (upper : Bool) (g : SublevelActionGrid.Table) : ℕ :=
  ∑ i ∈ Finset.range g.size, if agrees hist upper g i then 0 else 1

theorem exact_node {upper : Bool} {bs : List (Block upper)} {hist : Tree}
    (checked : scan bs hist.clear = hist) {g : SublevelActionGrid.Table}
    (ok : failures hist upper g = 0) {i : ℕ} (hi : i < g.size) :
    packetTail (nodeTick upper g i) bs = (SublevelActionGrid.cell g i).height := by
  have hle := Finset.single_le_sum
    (f := fun j => if agrees hist upper g j then 0 else 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  change (if agrees hist upper g i then 0 else 1) ≤ failures hist upper g at hle
  rw [ok] at hle
  have agree : agrees hist upper g i = true := by
    by_contra! bad
    simp [bad] at hle
  obtain ⟨known, val⟩ := Bool.and_eq_true_iff.mp agree
  exact (packet_tail checked known).trans (eq_of_beq val)

/-- Original angular panel enclosures imply every directed arclength node of a
verified grid at once. Lower grids sample strictly positive right endpoints. -/
theorem nodeBounds {upper : Bool} {bs : List (Block upper)} {hist : Tree}
    (checked : scan bs hist.clear = hist) {g : SublevelActionGrid.Table}
    (ok : failures hist upper g = 0)
    (wpos : ∀ i < g.size, 0 < (SublevelActionGrid.cell g i).width)
    {f w : ℝ → ℝ} {h L R : ℝ} (endpt : L + bs.length / 64 = R)
    (c : Covers upper w f h L bs) (hf : Measurable f) (hw : Measurable w)
    (hn : ∀ t ∈ Set.Icc L R, 0 ≤ w t) (hiw : MeasureTheory.IntegrableOn w (Set.Ioc L R)) :
    SublevelActionGrid.NodeBounds
      ((MeasureTheory.volume.restrict (Set.Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t)))
      f h g 1048576 3221225472 upper := by
  intro i hi
  have pos : upper = true ∨ 0 < nodeTick upper g i := by
    cases upper
    · right
      simp only [nodeTick, Bool.false_eq_true, ite_false, SublevelActionGrid.tick,
        Finset.sum_range_succ]
      exact Nat.add_pos_right _ (wpos i hi)
    · exact Or.inl rfl
  have hb := covers_sublevel pos endpt c hf hw hn hiw
  rw [exact_node checked ok hi] at hb
  cases upper <;>
    simpa only [MirrorActionQuadrature.Directed, nodeTick, SublevelActionGrid.speed,
      SublevelActionGrid.height, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat,
      show (3072 * 1048576 : ℝ) = 3221225472 by norm_num] using hb

/-- Combining the recovered sublevel lengths with the integer action certificate
gives the strict target in geometric-angle trace normalization. -/
theorem trace_action {upper : Bool} {g : SublevelActionGrid.Table} {p q : ℕ}
    (cert : SublevelActionGrid.Certified g 1048576 3221225472 upper p q)
    {f w : ℝ → ℝ} {h L R : ℝ} (hLR : L ≤ R) (hf : Measurable f) (hw : Measurable w)
    (floor : ∀ t ∈ Set.Ioc L R, h - 2 ≤ f t)
    (hw₀ : ∀ t ∈ Set.Ioc L R, 0 ≤ w t) (hi : MeasureTheory.IntegrableOn w (Set.Ioc L R))
    (nodes : SublevelActionGrid.NodeBounds
      ((MeasureTheory.volume.restrict (Set.Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t)))
      f h g 1048576 3221225472 upper) :
    if upper then Kinetic.MirrorHeightAction.action f w L R h < (p : ℝ) / q
    else (p : ℝ) / q < Kinetic.MirrorHeightAction.action f w L R h := by
  let μ := (MeasureTheory.volume.restrict (Set.Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t))
  let _ : MeasureTheory.IsFiniteMeasure μ := MeasureTheory.isFiniteMeasure_withDensity_ofReal hi.2
  have hfloor : ∀ᵐ t ∂μ, h - 2 ≤ f t := (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc floor)
  have bound := SublevelActionGrid.action_target μ hf.aemeasurable hfloor cert nodes
  rwa [show Kinetic.MirrorSublevelAction.action μ f h = Kinetic.MirrorHeightAction.action f w L R h
    from Kinetic.MirrorSublevelAction.action_trace hLR f w h hw hw₀] at bound

end PlasmaLean.Certificates.MirrorSpeedHistogram
