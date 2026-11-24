/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCartesianAngleFlow
public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import PlasmaLean.Theory.Kinetic.MirrorLocalFlowPersistence

/-! # Open Cartesian position and height neighborhoods of the original QA2R pilot births -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCartesianMirrorBirth
open Set DommaschkCartesianAngleFlow DommaschkFirstMirrorWell DommaschkSignedTraceDomain
open DommaschkSignedObservable DommaschkSignedMirrorBand DommaschkFirstMirrorLaunchSign
open Kinetic.MirrorWellPersistence Kinetic.MirrorHeightBand
open Certificates.PositionFrameSlabs (Plane State Step)
set_option maxRecDepth 12000

/-- The cap may be chosen strictly inside the checked time domain, beyond the specified root. -/
private theorem outward {f : ℝ → ℝ} {a b L U k : ℝ} (br : Branch f a b L U k)
    (q : Icc L U) (rate : 0 < k / (2 * (q : ℝ))) :
    ∃ cap ∈ Ioo a b, (q : ℝ) < f cap ∧ (∀ t ∈ Icc 0 a, f t < q) ∧
      ∀ t ∈ Icc 0 cap, f t = q → ∃ v > 0, HasDerivAt f v t := by
  let r := br.time q
  obtain ⟨left, right⟩ := br.interior_time q
  change a < r at left
  change r < b at right
  let cap := (r + b) / 2
  have rc : r < cap := by dsimp [cap]; linarith
  have cb : cap < b := by dsimp [cap]; linarith
  refine ⟨cap, ⟨left.trans rc, cb⟩, br.after q cap ⟨rc, cb.le⟩,
    fun t ht => br.before q t ⟨ht.1, ht.2.trans_lt left⟩, ?_⟩
  intro t ht hit
  have atroot : t = r := by
    rcases lt_trichotomy t r with early | atroot | late
    · exact False.elim ((br.before q t ⟨ht.1, early⟩).ne hit)
    · exact atroot
    · exact False.elim ((br.after q t ⟨late, ht.2.trans cb.le⟩).ne' hit)
  obtain ⟨v, hv, d⟩ := br.transverse q
  exact ⟨v, rate.trans hv, atroot ▸ d⟩

/-- At any admitted angle and any height in the closed pilot band, the Cartesian
angular field has a physical bracket with strictly exterior caps on both sides. -/
theorem flow_bracket {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ h : ℝ} (p : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) (small : |φ| < 316 / 64)
    (height_mem : h ∈ Icc (height false : ℝ) (height true)) :
    ∃ a b, a < φ ∧ φ < b ∧
      FlowBracketIn velocity (fun q => ‖B q‖) regular a φ b (point y φ, h) := by
  let f := fun t => ‖B (point y t)‖
  obtain ⟨⟨bf⟩, ⟨bb⟩⟩ := band
  have hpos : 0 < h := lt_of_lt_of_le (by norm_num [height]) height_mem.1
  have rate : 0 < (1 / 400 : ℝ) / (2 * h) := by positivity
  obtain ⟨r, hr, highR, lowR, dr⟩ := outward bf ⟨h, height_mem⟩ rate
  obtain ⟨l, hl, highL, lowL, dl⟩ := outward bb ⟨h, height_mem⟩ rate
  change h < f (-l) at highL
  change h < f r at highR
  change ∀ t ∈ Icc 0 (316 / 64 : ℝ), f t < h at lowR
  change ∀ t ∈ Icc 0 (316 / 64 : ℝ), f (-t) < h at lowL
  change ∀ t ∈ Icc 0 r, f t = h → ∃ v > 0, HasDerivAt f v t at dr
  change ∀ t ∈ Icc 0 l, f (-t) = h → ∃ v > 0, HasDerivAt (fun s => f (-s)) v t at dl
  obtain ⟨phlo, phhi⟩ := abs_lt.mp small
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have inside (t : ℝ) (ht : t ∈ Icc (-l) r) : t ∈ Ioo (-(n : ℝ) / 64) (n / 64) :=
    ⟨by linarith [hl.2, ht.1], by linarith [hr.2, ht.2]⟩
  have center (t : ℝ) (lo : -(316 / 64) ≤ t) (hi : t ≤ 316 / 64) : f t < h := by
    rcases le_total 0 t with pos | neg
    · exact lowR t ⟨pos, hi⟩
    · simpa only [neg_neg] using lowL (-t) ⟨neg_nonneg.mpr neg, by linarith⟩
  refine ⟨-l, r, by linarith [hl.1], by linarith [hr.1], point y, rfl, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨le, ri⟩ := inside t ht
    exact cartesian_ode ((p.ode t ⟨le.le, ri.le⟩).hasDerivAt (Icc_mem_nhds le ri))
      (region t ⟨le.le, ri.le⟩)
  · change Bracket f (-l) φ r h
    refine Bracket.of_signs highL (center φ phlo.le phhi.le) highR ?_ ?_
    · intro t ht hit
      by_cases central : -(316 / 64) ≤ t
      · exact False.elim ((center t central (ht.2.trans phhi.le)).ne hit)
      obtain ⟨v, vp, d⟩ := dl (-t) ⟨by linarith, by linarith [ht.1]⟩ (by simpa only [neg_neg])
      have back := d.comp t (hasDerivAt_id t).neg
      have orig : HasDerivAt f (-v) t := by simpa only [Function.comp_def, id_eq, neg_neg,
        mul_neg_one] using back
      rw [orig.deriv]
      exact neg_neg_of_pos vp
    · intro t ht hit
      by_cases central : t ≤ 316 / 64
      · exact False.elim ((center t (phlo.le.trans ht.1) central).ne hit)
      obtain ⟨v, vp, d⟩ := dr t ⟨by linarith, ht.2⟩ hit
      rwa [d.deriv]
  · intro t ht
    exact in_regular (region t (Ioo_subset_Icc_self (inside t ht))) t

def regularBirths : Set (Fields.Space × ℝ) := {q | Contract.RegularMirrorBirth B q.1 q.2}

/-- The full Cartesian position-height regular-birth set contains a neighborhood
of each point of a physically enclosed pilot satisfying the certified two branches. -/
theorem neighborhood {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ h : ℝ} (p : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) (small : |φ| < 316 / 64)
    (height_mem : h ∈ Icc (height false : ℝ) (height true)) :
    (point y φ, h) ∈ interior regularBirths := by
  obtain ⟨a, b, af, fb, bracket⟩ := flow_bracket p reached region band small height_mem
  obtain ⟨W, op, here, subset⟩ := regular_birth_open_of_local isOpen_regular af fb
    (fun q hq => (velocity_smooth hq).contDiffWithinAt)
    (fun q hq => (strength_smooth hq).contDiffWithinAt)
    (fun q hq => (speed_smooth hq).continuousAt.continuousWithinAt)
    (fun q hq => ⟨rfl, speed_pos hq, field_ne_zero hq, aligned hq⟩) bracket
  exact interior_maximal subset op here

end PlasmaLean.Design.DommaschkCartesianMirrorBirth
