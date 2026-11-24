/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction
public import PlasmaLean.Design.DommaschkActionQ0R478
public import PlasmaLean.Design.DommaschkActionQ0R531
public import PlasmaLean.Design.DommaschkActionQ1R464
public import PlasmaLean.Design.DommaschkActionQ1R517
public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # Minimal symmetric lower-action windows for the four positive QA2R comparisons -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkLowerActionWindows
open Certificates.MirrorActionQuadrature Set

/-- Each label names its own signed chronological archive and its design height. -/
inductive Endpoint | q0r478 | q0r531 | q1r464 | q1r517

def archive : Endpoint → List (Block false)
  | .q0r478 => DommaschkActionQ0R478.slabs
  | .q0r531 => DommaschkActionQ0R531.slabs
  | .q1r464 => DommaschkActionQ1R464.slabs
  | .q1r517 => DommaschkActionQ1R517.slabs

def middle : Endpoint → ℕ
  | .q0r478 => 327 | .q0r531 => 325 | .q1r464 => 329 | .q1r517 => 328

def cutoff : Endpoint → ℕ
  | .q0r478 => 322 | .q0r531 => 321 | .q1r464 => 325 | .q1r517 => 323

def height : Endpoint → ℝ
  | .q0r478 | .q1r464 => 5300546391395933 / 5000000000000000
  | .q0r531 | .q1r517 => 5297961656084411 / 5000000000000000

abbrev target : ℝ := 6799610938322487 / 5000000000000000

/-- Take the innermost rows on each side. Restore chronological order on the negative half. -/
def window (e : Endpoint) (k : ℕ) : List (Block false) :=
  ((((archive e).take (middle e)).reverse.take k).reverse ++ ((archive e).drop (middle e)).take k)

def mass (e : Endpoint) (k : ℕ) : ℝ := total (window e k) / (3072 * 1099511627776 : ℝ)

theorem mass_monotone (e : Endpoint) : Monotone (mass e) := by
  intro i j h
  have lower : List.Sublist (window e i) (window e j) :=
    (List.take_sublist_take_left h).reverse.append (List.take_sublist_take_left h)
  have sum_le {xs ys : List ℕ} (sub : xs.Sublist ys) : xs.sum ≤ ys.sum := by
    induction sub with
    | slnil => rfl
    | cons _ _ ih => simp only [List.sum_cons]; omega
    | cons_cons _ _ ih => simpa using ih
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact_mod_cast sum_le (lower.map Block.mass)

theorem window_length (e : Endpoint) : (window e (cutoff e)).length = cutoff e + cutoff e := by
  cases e <;> kernel_fact

set_option maxRecDepth 8192 in
/-- The winning physical input is the corresponding contiguous slice of the original
chronological archive. A cover assembled in the original coordinates can be used directly. -/
theorem at_cutoff (e : Endpoint) : window e (cutoff e) =
    ((archive e).drop (middle e - cutoff e)).take (cutoff e + cutoff e) := by
  cases e <;> with_unfolding_all rfl

private theorem checks (e : Endpoint) :
    total (window e (cutoff e - 1)) * 5000000000000000 <
      6799610938322487 * (3072 * 1099511627776) ∧
    6799610938322487 * (3072 * 1099511627776) <
      total (window e (cutoff e)) * 5000000000000000 := by
  cases e <;> constructor <;> kernel_fact

/-- The last omitted row pair is necessary for this particular lower quadrature sum. -/
theorem first_crossing (e : Endpoint) :
    (∀ k < cutoff e, mass e k < target) ∧ target < mass e (cutoff e) := by
  have lo : mass e (cutoff e - 1) < target := by
    apply (div_lt_div_iff₀ (by norm_num) (by norm_num)).2
    exact_mod_cast (checks e).1
  refine ⟨fun k hk => (mass_monotone e (show k ≤ cutoff e - 1 by omega)).trans_lt lo, ?_⟩
  apply (div_lt_div_iff₀ (by norm_num) (by norm_num)).2
  exact_mod_cast (checks e).2

/-- A physical cover of the winning core suffices for any enclosing interval with nonnegative
arclength weight, including a first well once its two endpoints have been located. -/
theorem action_on_enclosing_interval (e : Endpoint) {f w : ℝ → ℝ} {l r : ℝ}
    (left : l ≤ -(cutoff e : ℝ) / 64) (right : (cutoff e : ℝ) / 64 ≤ r)
    (cells : Covers false w f (height e) (-(cutoff e : ℝ) / 64) (window e (cutoff e)))
    (nonneg : ∀ t ∈ Icc l r, 0 ≤ w t) (cf : ContinuousOn f (Icc l r))
    (cw : ContinuousOn w (Icc l r)) :
    target < mass e (cutoff e) ∧
      mass e (cutoff e) ≤ Kinetic.MirrorHeightAction.action f w l r (height e) := by
  have sub := Icc_subset_Icc left right
  have core := Certificates.NativeActionInterval.exact_lower_mass (window_length e) cells
    (fun t ht => nonneg t (sub ht)) (cf.mono sub) (cw.mono sub)
  exact ⟨(first_crossing e).2, core.trans (Kinetic.MirrorActionEnvelope.action_mono_interval
    left (by linarith only [Nat.cast_nonneg (α := ℝ) (cutoff e)]) right cf cw nonneg)⟩

end PlasmaLean.Design.DommaschkLowerActionWindows
