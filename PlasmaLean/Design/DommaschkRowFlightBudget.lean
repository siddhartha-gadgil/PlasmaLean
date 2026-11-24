/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRowTimeClearance
public import PlasmaLean.Design.DommaschkFullBandFlightBounds

/-! # Integration of signed central row budgets on the same pilot trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRowFlightBudget

open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkSignedTraceDomain
open DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkSharpFlightBounds
open DommaschkSignedObservable DommaschkFirstMirrorLaunchSign Kinetic.MirrorActionEnvelope
open DommaschkFullBandFlightBounds DommaschkRowTimeClearance

abbrev integrand (y : ℝ → Plane) (h t : ℝ) :=
  arcDensity (y t 0) t (y t 1) / Real.sqrt (2 * (h - strength t (y t)))

abbrev paired (y : ℝ → Plane) (h t : ℝ) := integrand y h t + integrand y h (-t)

/-- Both directions are integrated over the same elapsed-angle window. The integer
budget is the sum of the local reciprocal-speed ceilings for one direction. -/
structure Budget (y : ℝ → Plane) (lo hi : ℝ) (total : ℕ) : Prop where
  ordered : lo ≤ hi
  bound : ∀ h ∈ Icc (height false : ℝ) (height true),
    (∀ t ∈ Icc (-b) b, Region (y t)) →
    IntervalIntegrable (paired y h) volume lo hi →
    (∫ t in lo..hi, paired y h t) ≤ 2 * ceiling * (total : ℝ) / 64

theorem Budget.append {y : ℝ → Plane} {u v w : ℝ} {m n : ℕ} (left : Budget y u v m)
    (right : Budget y v w n) : Budget y u w (m + n) := by
  have ord := left.ordered.trans right.ordered
  refine ⟨ord, fun h hh region finite => ?_⟩
  have l := finite.mono_set (by
    rw [uIcc_of_le left.ordered, uIcc_of_le ord]
    exact Icc_subset_Icc_right right.ordered)
  have r := finite.mono_set (by
    rw [uIcc_of_le right.ordered, uIcc_of_le ord]
    exact Icc_subset_Icc_left left.ordered)
  rw [← intervalIntegral.integral_add_adjacent_intervals l r, Nat.cast_add]
  linarith only [left.bound h hh region l, right.bound h hh region r]

private theorem atPoint {x : Plane} {q : ℕ} {t h : ℝ} (hq : 0 < q) (region : Region x)
    (hh : h ∈ Icc (height false : ℝ) (height true)) (under : strength t x < testHeight q) :
    arcDensity (x 0) t (x 1) / Real.sqrt (2 * (h - strength t x)) ≤ ceiling * q := by
  have inv := reciprocal_le hq hh.1 under
  have low : (testHeight q : ℝ) ≤ (height false : ℝ) := by
    push_cast [testHeight]
    linarith [show (0 : ℝ) ≤ 1 / (2 * (q : ℝ) ^ 2) by positivity]
  have density := DommaschkToroidalFieldBounds.density_upper region
    (under.le.trans (low.trans (hh.1.trans hh.2)))
  have pos : 0 ≤ arcDensity (x 0) t (x 1) :=
    (by norm_num : (0 : ℝ) ≤ 7 / 8).trans (DommaschkSignedTraceDensity.density_lower t region)
  rw [div_eq_mul_one_div]
  exact (mul_le_mul_of_nonneg_left inv pos).trans
    (mul_le_mul_of_nonneg_right density (Nat.cast_nonneg _))

def Row (r : Step) (sign p e : ℝ) (q : ℕ) : Prop :=
  ∀ {prev : State} {t : ℝ} {x : Plane}, t ∈ Icc p e → x ∈ (physicalSlab prev r p).tube t →
    strength (sign * t) x < testHeight q

/-- Consume the genuine two-direction physical tubes at this row of the path. -/
theorem from_row {i q : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path 325 fs bs fr br x y) (reach : i < 325) (hf : i < fr.length) (hb : i < br.length)
    (hq : 0 < q) (fw : Row fr[i] 1 (i / 64) (((i : ℝ) + 1) / 64) q)
    (bw : Row br[i] (-1) (i / 64) (((i : ℝ) + 1) / 64) q) :
    Budget y (i / 64) (((i : ℝ) + 1) / 64) q := by
  have size : (i : ℝ) + 1 ≤ 325 := by exact_mod_cast reach
  have ord : (i : ℝ) / 64 ≤ ((i : ℝ) + 1) / 64 := by linarith
  obtain ⟨_, pf, fwd⟩ := path.at_row reach false hf
  obtain ⟨_, pb, back⟩ := path.at_row reach true hb
  refine ⟨ord, fun h hh region finite => ?_⟩
  have point (t : ℝ) (ht : t ∈ Ioo ((i : ℝ) / 64) (((i : ℝ) + 1) / 64)) :
      paired y h t ≤ 2 * ceiling * q := by
    have within := Ioo_subset_Icc_self ht
    have s := fw within (fwd t within)
    have z := bw within (back t within)
    simp only [one_mul] at s
    simp only [neg_one_mul] at z
    have tt : t ∈ Icc (-b) b ∧ -t ∈ Icc (-b) b := by
      have n := Nat.cast_nonneg (α := ℝ) i
      dsimp [b]
      constructor <;> constructor <;> linarith [ht.1, ht.2]
    change integrand y h t + integrand y h (-t) ≤ _
    linarith only [atPoint hq (region t tt.1) hh s, atPoint hq (region (-t) tt.2) hh z]
  have it := intervalIntegral.integral_mono_on_of_le_Ioo ord finite intervalIntegrable_const point
  simpa only [intervalIntegral.integral_const, smul_eq_mul,
    show ((i : ℝ) + 1) / 64 - i / 64 = 1 / 64 by ring,
    show 1 / 64 * (2 * ceiling * q) = 2 * ceiling * q / 64 by ring] using it

/-- The complete normalized time for the true first well stays above 14 and below 264
at every height of the closed archive band. -/
def WholeTime (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-b) (-a), ∃ r ∈ Ioo a b, φ ∈ Ioo l r ∧
      LaunchWell (fun t => strength t (y t)) 0 h l r ∧
      IntervalIntegrable (integrand y h) volume l r ∧
      14 < (∫ t in l..r, integrand y h t) ∧ (∫ t in l..r, integrand y h t) < 264

theorem complete {y : ℝ → Plane} {φ : ℝ} (flight : BoundedFlight φ y)
    (region : ∀ t ∈ Icc (-b) b, Region (y t)) (budget : Budget y 0 a 5916) :
    WholeTime φ y := by
  intro h hh
  obtain ⟨l, hl, r, hr, atBirth, well, finite, collar, low, _⟩ := flight h hh
  have l0 := well.left_lt.le
  have r0 := well.lt_right.le
  have a0 : (0 : ℝ) ≤ a := by norm_num [a]
  have right : IntervalIntegrable (integrand y h) volume 0 a := finite.mono_set (by
    rw [uIcc_of_le a0, uIcc_of_le (l0.trans r0)]
    exact Icc_subset_Icc l0 hr.1.le)
  have left : IntervalIntegrable (integrand y h) volume (-a) 0 := finite.mono_set (by
    rw [uIcc_of_le (neg_nonpos.mpr a0), uIcc_of_le (l0.trans r0)]
    exact Icc_subset_Icc hl.2.le r0)
  have reflected : IntervalIntegrable (fun t => integrand y h (-t)) volume 0 a := by
    simpa only [zero_sub, sub_zero, neg_neg] using left.symm.comp_sub_left 0
  have main := budget.bound h hh region (right.add reflected)
  change (∫ t in 0..a, integrand y h t + integrand y h (-t)) ≤ _ at main
  rw [intervalIntegral.integral_add right reflected, intervalIntegral.integral_comp_neg,
    neg_zero] at main
  change (∫ t in l..r, integrand y h t) < (∫ t in (-a)..a, integrand y h t) + 40 at collar
  rw [← intervalIntegral.integral_add_adjacent_intervals left right] at collar
  refine ⟨l, hl, r, hr, atBirth, well, finite, low, ?_⟩
  have sum : 2 * ceiling * (5916 : ℕ) / 64 + 40 < 264 := by norm_num [ceiling, height]
  rw [add_comm (∫ t in (-a)..0, integrand y h t) (∫ t in 0..a, integrand y h t)] at collar
  exact collar.trans ((add_le_add_left main 40).trans_lt sum)

end PlasmaLean.Design.DommaschkRowFlightBudget
