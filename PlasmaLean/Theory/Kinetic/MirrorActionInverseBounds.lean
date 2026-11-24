/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-! # Quantitative height inversion from two strict bounds on the action derivative -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionInverseBounds

open Set

/-- On two distinct ordered heights the action increment lies strictly between
the lower and upper multiples of the height change. -/
def Secants {L U : ℝ} (J : Icc L U → ℝ) (m M : ℝ) : Prop :=
  ∀ i j : Icc L U, i < j →
    m * ((j : ℝ) - i) < J j - J i ∧ J j - J i < M * ((j : ℝ) - i)

/-- Mean value applied directly to the action on the finite band. No continuity of
the derivative in height is needed. -/
theorem secants_of_derivatives {J T : ℝ → ℝ} {L U m M : ℝ}
    (d : ∀ h ∈ Icc L U, HasDerivAt J (T h) h) (rate : ∀ h ∈ Icc L U, m < T h ∧ T h < M) :
    Secants (fun h : Icc L U => J h) m M := by
  intro i j ij
  have sub : Icc (i : ℝ) (j : ℝ) ⊆ Icc L U := Icc_subset_Icc i.2.1 j.2.2
  have cont : ContinuousOn J (Icc (i : ℝ) j) := fun t ht =>
    (d t (sub ht)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, eq⟩ := exists_hasDerivAt_eq_slope J T ij cont
    (fun t ht => d t (sub (Ioo_subset_Icc_self ht)))
  have bounds := rate c (sub (Ioo_subset_Icc_self hc))
  rw [eq] at bounds
  have pos := sub_pos.mpr (show (i : ℝ) < j from ij)
  exact ⟨(lt_div_iff₀ pos).mp bounds.1, (div_lt_iff₀ pos).mp bounds.2⟩

/-- A two-sided inverse on the attainable actions with strict distortion bounds.
The modulus also covers equal or oppositely ordered observations. -/
def InverseBounds {L U : ℝ} (J : Icc L U → ℝ) (m M : ℝ) : Prop :=
  ∃ inv : range J → Icc L U,
    (∀ h : Icc L U, inv ⟨J h, ⟨h, rfl⟩⟩ = h) ∧
    (∀ u : range J, J (inv u) = u) ∧
    (∀ u v : range J, u < v →
      ((v : ℝ) - u) / M < (inv v : ℝ) - inv u ∧ (inv v : ℝ) - inv u < ((v : ℝ) - u) / m) ∧
    (∀ u v : range J, |(inv v : ℝ) - inv u| ≤ |(v : ℝ) - u| / m)

theorem inverse_of_secants {L U m M : ℝ} {J : Icc L U → ℝ} (hm : 0 < m) (hM : 0 < M)
    (bounds : Secants J m M) : InverseBounds J m M := by
  have mono : StrictMono J := by
    intro i j ij
    exact sub_pos.mp ((mul_pos hm (sub_pos.mpr ij)).trans (bounds i j ij).1)
  let inv (u : range J) : Icc L U := u.2.choose
  have right (u : range J) : J (inv u) = u := u.2.choose_spec
  have ordered {u v : range J} (uv : u < v) : inv u < inv v := by
    apply mono.lt_iff_lt.mp
    rwa [right, right]
  have diff {u v : range J} (uv : u < v) : 0 < (inv v : ℝ) - inv u :=
    sub_pos.mpr (ordered uv)
  have obs {u v : range J} (uv : u < v) : 0 < (v : ℝ) - u := sub_pos.mpr uv
  have sharp (u v : range J) (uv : u < v) :
      ((v : ℝ) - u) / M < (inv v : ℝ) - inv u ∧ (inv v : ℝ) - inv u < ((v : ℝ) - u) / m := by
    have h := bounds _ _ (ordered uv)
    rw [right, right] at h
    exact ⟨(div_lt_iff₀' hM).mpr h.2, (lt_div_iff₀' hm).mpr h.1⟩
  refine ⟨inv, fun h => mono.injective (right ⟨J h, ⟨h, rfl⟩⟩), right, sharp, ?_⟩
  intro u v
  rcases lt_trichotomy u v with uv | same | vu
  · rw [abs_of_pos (diff uv), abs_of_pos (obs uv)]
    exact (sharp u v uv).2.le
  · simp [same]
  · rw [abs_sub_comm, abs_sub_comm (v : ℝ) u, abs_of_pos (diff vu), abs_of_pos (obs vu)]
    exact (sharp v u vu).2.le

/-- The attainable action interval includes both endpoint observations. -/
theorem range_eq_interval {L U : ℝ} (ord : L ≤ U) {J : ℝ → ℝ}
    (cont : ContinuousOn J (Icc L U)) (mono : MonotoneOn J (Icc L U)) :
    range (fun h : Icc L U => J h) = Icc (J L) (J U) := by
  ext v
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨mono ⟨le_rfl, ord⟩ h.2 h.2.1, mono h.2 ⟨ord, le_rfl⟩ h.2.2⟩
  · intro hv
    obtain ⟨x, hx, eq⟩ := intermediate_value_Icc ord cont hv
    exact ⟨⟨x, hx⟩, eq⟩

end PlasmaLean.Kinetic.MirrorActionInverseBounds
