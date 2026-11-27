/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.ContinuousOn

/-!
# A tube described slab by slab is open

A tube around a traced curve is recorded on consecutive time slabs `[a + k h, a + (k+1) h]`,
each with its own gauge function `g k` (for instance the norm of the deviation in a frame of
that slab) and radius `ρ k`. The gauges need not agree at the nodes. If each gauge is continuous
on its closed slab and, at every node, the open set of the later slab lies in the open set of
the earlier one, then the union over the half-open slabs is open, except at the initial time,
where it is open relative to the half-space `a ≤ t`.

* `region_mem_nhdsWithin`: the relative statement at every point.
* `isOpen_region_inter`: the part after the initial time is open.
-/

@[expose] public section
namespace PlasmaLean.Fields.PiecewiseTube
open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-- Node times of the slabs. -/
def node (a h : ℝ) (k : ℕ) : ℝ := a + k * h

theorem node_zero (a h : ℝ) : node a h 0 = a := by simp [node]

theorem node_succ (a h : ℝ) (k : ℕ) : node a h (k + 1) = node a h k + h := by
  simp only [node, Nat.cast_add, Nat.cast_one]
  ring

/-- Points whose time lies in a half-open slab and whose gauge on that slab is below the radius
of the slab. -/
def region (a h : ℝ) (n : ℕ) (g : ℕ → ℝ × X → ℝ) (ρ : ℕ → ℝ) : Set (ℝ × X) :=
  {p | ∃ k < n, p.1 ∈ Ico (node a h k) (node a h (k + 1)) ∧ g k p < ρ k}

variable {a h : ℝ} {n : ℕ} {g : ℕ → ℝ × X → ℝ} {ρ : ℕ → ℝ}

/-- The slab-wise tube is a neighbourhood of each of its points within the half-space of times
not before the initial one. -/
theorem region_mem_nhdsWithin (hh : 0 < h)
    (cont : ∀ k < n, ContinuousOn (g k) (Icc (node a h k) (node a h (k + 1)) ×ˢ univ))
    (nest : ∀ k, k + 1 < n → ∀ x, g (k + 1) (node a h (k + 1), x) < ρ (k + 1) →
      g k (node a h (k + 1), x) < ρ k)
    {p : ℝ × X} (hp : p ∈ region a h n g ρ) :
    region a h n g ρ ∈ 𝓝[{q : ℝ × X | a ≤ q.1}] p := by
  obtain ⟨t, x⟩ := p
  obtain ⟨k, hk, ⟨hlo, hhi⟩, hg⟩ := hp
  change node a h k ≤ t at hlo
  change t < node a h (k + 1) at hhi
  have near (j : ℕ) (hj : j < n) (ht : t ∈ Icc (node a h j) (node a h (j + 1)))
      (hlt : g j (t, x) < ρ j) :
      ∀ᶠ q in 𝓝 (t, x), q ∈ Icc (node a h j) (node a h (j + 1)) ×ˢ (univ : Set X) →
        g j q < ρ j :=
    eventually_nhdsWithin_iff.mp
      ((cont j hj (t, x) ⟨ht, mem_univ x⟩).eventually_lt_const hlt)
  have time {lo hi : ℝ} (h₁ : lo < t) (h₂ : t < hi) :
      ∀ᶠ q : ℝ × X in 𝓝 (t, x), q.1 ∈ Ioo lo hi :=
    continuous_fst.continuousAt.eventually (Ioo_mem_nhds h₁ h₂)
  have right := near k hk ⟨hlo, hhi.le⟩ hg
  rcases hlo.eq_or_lt with heq | hlt
  · rcases k with _ | j
    · -- initial time: only the half-space is covered
      rw [node_zero] at heq
      have later : ∀ᶠ q : ℝ × X in 𝓝 (t, x), q.1 < node a h 1 :=
        continuous_fst.continuousAt.eventually (Iio_mem_nhds hhi)
      filter_upwards [nhdsWithin_le_nhds right, nhdsWithin_le_nhds later, self_mem_nhdsWithin]
        with q hr hl hq
      have hq' : a ≤ q.1 := hq
      refine ⟨0, hk, ⟨by rwa [node_zero], hl⟩, hr ⟨⟨by rwa [node_zero], hl.le⟩, mem_univ _⟩⟩
    · -- an interior node: the earlier slab covers the left side
      subst heq
      have step := node_succ a h j
      have left := near j (Nat.lt_of_succ_lt hk) ⟨by linarith, le_rfl⟩ (nest j hk x hg)
      have window := time (lo := node a h j) (hi := node a h (j + 1 + 1)) (by linarith) hhi
      apply nhdsWithin_le_nhds
      filter_upwards [left, right, window] with q hl hr hw
      by_cases side : q.1 < node a h (j + 1)
      · exact ⟨j, Nat.lt_of_succ_lt hk, ⟨hw.1.le, side⟩, hl ⟨⟨hw.1.le, side.le⟩, mem_univ _⟩⟩
      · have ge := not_lt.mp side
        exact ⟨j + 1, hk, ⟨ge, hw.2⟩, hr ⟨⟨ge, hw.2.le⟩, mem_univ _⟩⟩
  · apply nhdsWithin_le_nhds
    filter_upwards [right, time hlt hhi] with q hr hw
    exact ⟨k, hk, ⟨hw.1.le, hw.2⟩, hr ⟨⟨hw.1.le, hw.2.le⟩, mem_univ _⟩⟩

/-- After the initial time the slab-wise tube is open. -/
theorem isOpen_region_inter (hh : 0 < h)
    (cont : ∀ k < n, ContinuousOn (g k) (Icc (node a h k) (node a h (k + 1)) ×ˢ univ))
    (nest : ∀ k, k + 1 < n → ∀ x, g (k + 1) (node a h (k + 1), x) < ρ (k + 1) →
      g k (node a h (k + 1), x) < ρ k) :
    IsOpen (region a h n g ρ ∩ {q : ℝ × X | a < q.1}) := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hp, hlt⟩
  have half : {q : ℝ × X | a < q.1} ∈ 𝓝 p :=
    continuous_fst.continuousAt.eventually (Ioi_mem_nhds hlt)
  have rel := region_mem_nhdsWithin hh cont nest hp
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at rel
  obtain ⟨u, hu, sub⟩ := rel
  filter_upwards [hu, half] with q hq hq'
  exact ⟨sub ⟨hq, le_of_lt hq'⟩, hq'⟩

omit [TopologicalSpace X] in
/-- Sanity: a single slab with a continuous gauge. The region is the strip below the radius. -/
theorem region_one (g₀ : ℝ × X → ℝ) (r : ℝ) :
    region a h 1 (fun _ => g₀) (fun _ => r) = {p | p.1 ∈ Ico a (a + h) ∧ g₀ p < r} := by
  ext p
  simp [region, node]

end PlasmaLean.Fields.PiecewiseTube
