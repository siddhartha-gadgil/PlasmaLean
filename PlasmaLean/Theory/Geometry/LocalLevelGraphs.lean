/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.PeriodicOrientedCrossings

/-!
# Fixed-action graphs on local launch sets

The parameter space may be one phase patch or include several launch parameters.
Two disjoint radial brackets give a quantitative graph separation using only estimates
inside the individual brackets. A uniform lower secant bound converts an action residual
on either bracket into an error in its root radius.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.LocalLevelGraphs

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Strict face signs and a uniform positive secant bound on a closed radial bracket. -/
structure SecantBracket (J : X → ℝ → ℝ) (a b j m : ℝ) : Prop where
  ordered : a ≤ b
  positive : 0 < m
  continuous : ContinuousOn (fun p : X × ℝ => J p.1 p.2) (univ ×ˢ Icc a b)
  left : ∀ x, J x a < j
  right : ∀ x, j < J x b
  secant : ∀ x u, u ∈ Icc a b → ∀ v ∈ Icc a b, u ≤ v → m * (v - u) ≤ J x v - J x u

variable {J K : X → ℝ → ℝ} {a b c d j m n : ℝ}

/-- A joint continuous root on the launch set, unique in its own bracket. The
radius error for any trial point in the same bracket is at most its action residual
divided by the certified secant constant. -/
theorem SecantBracket.exists_graph (B : SecantBracket J a b j m) :
    ∃ u : X → ℝ, Continuous u ∧ ∀ x, u x ∈ Ioo a b ∧ J x (u x) = j ∧
      ∀ r ∈ Icc a b, (J x r = j ↔ r = u x) ∧ |r - u x| ≤ |J x r - j| / m := by
  have mono (x : X) : StrictMonoOn (J x) (Icc a b) := by
    intro u hu v hv huv
    exact sub_pos.mp ((mul_pos B.positive (sub_pos.mpr huv)).trans_le (B.secant x u hu v hv huv.le))
  have joint : Continuous (fun p : X × Icc a b => J p.1 p.2) := B.continuous.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨trivial, p.2.2⟩)
  have root (x : X) : ∃! r : Icc a b, J x r = j := by
    have hc : ContinuousOn (J x) (Icc a b) := B.continuous.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hr => ⟨trivial, hr⟩)
    obtain ⟨r, hr, e⟩ := intermediate_value_Icc B.ordered hc
      (show j ∈ Icc (J x a) (J x b) from ⟨(B.left x).le, (B.right x).le⟩)
    exact ⟨⟨r, hr⟩, e, fun q eq => Subtype.ext ((mono x).injOn q.2 hr (eq.trans e.symm))⟩
  obtain ⟨u, cu, hu⟩ := PeriodicLevelGraphs.exists_continuous_root_of_unique joint
    (continuous_const (y := j)) root
  refine ⟨fun x => u x, continuous_subtype_val.comp cu, fun x => ?_⟩
  have he := (hu x (u x)).mpr rfl
  change J x (u x) = j at he
  refine ⟨⟨(u x).2.1.lt_of_ne (fun eq => (B.left x).ne (eq ▸ he)),
    (u x).2.2.lt_of_ne (fun eq => (B.right x).ne (eq ▸ he.symm))⟩, he, fun r hr => ?_⟩
  refine ⟨(hu x ⟨r, hr⟩).trans Subtype.ext_iff, (le_div_iff₀ B.positive).mpr ?_⟩
  rcases le_total (u x : ℝ) r with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact (B.secant x _ (u x).2 _ hr h).trans (he ▸ le_abs_self _)
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, mul_comm]
    have hl := B.secant x _ hr _ (u x).2 h
    rw [he] at hl
    exact hl.trans (by rw [← abs_sub_comm]; exact le_abs_self _)

/-- For two mirror heights on a common patch, interval signs and radial action growth
on disjoint brackets yield ordered continuous graphs of the same target action. The
fixed gap between the two brackets is a strict lower bound throughout the patch. -/
theorem separated_graphs_of_local_secants (B : SecantBracket J a b j m)
    (C : SecantBracket K c d j n) (separate : b < c) :
    ∃ u v : X → ℝ, Continuous u ∧ Continuous v ∧ 0 < c - b ∧ ∀ x,
      u x ∈ Ioo a b ∧ v x ∈ Ioo c d ∧ c - b < v x - u x ∧ J x (u x) = j ∧ K x (v x) = j ∧
      (∀ r ∈ Icc a b, (J x r = j ↔ r = u x) ∧ |r - u x| ≤ |J x r - j| / m) ∧
      (∀ r ∈ Icc c d, (K x r = j ↔ r = v x) ∧ |r - v x| ≤ |K x r - j| / n) := by
  obtain ⟨u, cu, hu⟩ := B.exists_graph
  obtain ⟨v, cv, hv⟩ := C.exists_graph
  refine ⟨u, v, cu, cv, sub_pos.mpr separate, fun x => ?_⟩
  obtain ⟨hu', eu, uniqueU⟩ := hu x
  obtain ⟨hv', ev, uniqueV⟩ := hv x
  exact ⟨hu', hv', sub_lt_sub hv'.1 hu'.2, eu, ev, uniqueU, uniqueV⟩

/-- An identity radial profile with a target strictly between the faces supplies
a secant bracket with constant one for every choice of launch space. -/
theorem identity_fixture (ha : a < j) (hb : j < b) :
    SecantBracket (fun (_ : X) r => r) a b j 1 :=
  ⟨(ha.trans hb).le, zero_lt_one, continuous_snd.continuousOn, fun _ => ha, fun _ => hb,
    fun _ _ _ _ _ _ => by simp⟩

/-- At a populated phase patch, a zero-width bracket cannot have strict opposite face signs. -/
theorem no_zero_width [Nonempty X] : ¬ SecantBracket J a a j m := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  exact (h.left x).asymm (h.right x)

end PlasmaLean.LocalLevelGraphs
