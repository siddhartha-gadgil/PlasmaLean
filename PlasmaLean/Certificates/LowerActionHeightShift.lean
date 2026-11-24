/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction

/-! # Transport of lower action quadrature under a decrease of mirror height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.LowerActionHeightShift
open MirrorActionQuadrature Set

/-- Lowering a height by at most half a squared-speed allowance preserves a clipped floor. -/
theorem clipped_lower {g f H h d : ℝ} (hd : 0 ≤ d) (shift : 2 * (H - h) ≤ d)
    (bound : g ≤ max (2 * (H - f)) 0) :
    max (g - d) 0 ≤ max (2 * (h - f)) 0 := by
  apply max_le _ (le_max_right _ _)
  rcases le_total 0 (2 * (H - f)) with pos | neg
  · rw [max_eq_left pos] at bound
    exact (show g - d ≤ 2 * (h - f) by linarith).trans (le_max_left _ _)
  · rw [max_eq_right neg] at bound
    exact (show g - d ≤ 0 by linarith).trans (le_max_right _ _)

/-- Compare the original and proposed panel digits. Natural subtraction clips the shifted
squared-speed witness at zero, and `floor` is a lower bound on every new squared-speed digit. -/
def panelTest (ticks floor : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n + 1, p, q =>
    (density q).ble (density p) && (speedSq q).ble (speedSq p - ticks) &&
    floor.ble (speedSq q) && panelTest ticks floor n (p >>> 72) (q >>> 72)

/-- Adjacent rows must agree in order and count. -/
def blockTest (ticks floor : ℕ) : List (Block false) → List (Block false) → Bool
  | [], [] => true
  | p :: ps, q :: qs => panelTest ticks floor 48 p.packed q.packed && blockTest ticks floor ps qs
  | _, _ => false

/-- Independently checked consecutive lists form a single checked height transfer. -/
theorem blockTest_append {ticks floor : ℕ} {p q p' q' : List (Block false)}
    (left : blockTest ticks floor p q = true) (right : blockTest ticks floor p' q' = true) :
    blockTest ticks floor (p ++ p') (q ++ q') = true := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [blockTest]
  | cons b ps ih =>
    cases q with
    | nil => simp [blockTest] at left
    | cons c qs =>
      simp only [blockTest, Bool.and_eq_true] at left
      simp only [List.cons_append,blockTest,Bool.and_eq_true]
      exact ⟨left.1, ih left.2⟩

private theorem digit_lower {P Q d : ℕ} {f h H : ℝ} (comp : Q ≤ P - d)
    (shift : 2 * (H - h) ≤ d / 67108864) (bound : (P : ℝ) / 67108864 ≤ max (2 * (H - f)) 0) :
    (Q : ℝ) / 67108864 ≤ max (2 * (h - f)) 0 := by
  by_cases room : d ≤ P
  · have lim : (Q : ℝ) + d ≤ P := by exact_mod_cast (show Q + d ≤ P by omega)
    apply le_trans _ (clipped_lower (by positivity) shift bound)
    have scaled : (Q : ℝ) / 67108864 ≤ P / 67108864 - d / 67108864 := by linarith
    exact scaled.trans (le_max_left _ _)
  · have : Q = 0 := by omega
    simp [this]

private theorem panels_sound {ticks floor : ℕ} {w f : ℝ → ℝ} {H h : ℝ}
    (shift : 2 * (H - h) ≤ ticks / 67108864) (a : ℝ) (n p q : ℕ)
    (check : panelTest ticks floor n p q = true) (old : Cells false w f H a n p) :
    Cells false w f h a n q ∧ (0 < n → ∀ t ∈ Icc a (a + n / 3072),
      (floor : ℝ) / 67108864 ≤ max (2 * (h - f t)) 0) := by
  induction n generalizing a p q with
  | zero => exact ⟨trivial, by omega⟩
  | succ n ih =>
    simp only [panelTest, Bool.and_eq_true, Nat.ble_eq] at check
    obtain ⟨⟨⟨den,gap⟩,fl⟩,tail⟩ := check
    have hd : (density q : ℝ) / 1048576 ≤ density p / 1048576 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr den) (by norm_num)
    have hf : (floor : ℝ) / 67108864 ≤ speedSq q / 67108864 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr fl) (by norm_num)
    have cell : Cell false w f h a q := fun t ht =>
      ⟨hd.trans (old.1 t ht).1, digit_lower gap shift (old.1 t ht).2⟩
    obtain ⟨next,hnext⟩ := ih _ _ _ tail old.2
    refine ⟨⟨cell,next⟩,fun _ t ht => ?_⟩
    by_cases left : t ≤ a + 1 / 3072
    · exact hf.trans (cell t ⟨ht.1,left⟩).2
    · have nt : 0 < n := by
        by_contra! z
        have eq : n = 0 := by omega
        subst n
        norm_num at ht
        linarith [ht.2]
      apply hnext nt t
      exact ⟨le_of_not_ge left,by push_cast at ht; linarith [ht.2]⟩

/-- A successful digit comparison transports the whole physical cover. The same proof yields
a uniform lower bound on clipped squared speed at every point, including all panel boundaries. -/
theorem covers {ticks floor : ℕ} {w f : ℝ → ℝ} {H h : ℝ}
    (shift : 2 * (H - h) ≤ ticks / 67108864) (a : ℝ) {ps qs : List (Block false)}
    (check : blockTest ticks floor ps qs = true) (old : Covers false w f H a ps) :
    Covers false w f h a qs ∧ (qs ≠ [] → ∀ t ∈ Icc a (a + qs.length / 64),
      (floor : ℝ) / 67108864 ≤ max (2 * (h - f t)) 0) := by
  induction ps generalizing a qs with
  | nil => cases qs <;> simp_all [blockTest,Covers]
  | cons p ps ih =>
    cases qs with
    | nil => simp [blockTest] at check
    | cons q qs =>
      simp only [blockTest,Bool.and_eq_true] at check
      obtain ⟨one,hOne⟩ := panels_sound shift a 48 p.packed q.packed check.1 old.1
      obtain ⟨next,hNext⟩ := ih _ check.2 old.2
      refine ⟨⟨one,next⟩,fun _ t ht => ?_⟩
      by_cases left : t ≤ a + 1 / 64
      · apply hOne (by norm_num) t
        exact ⟨ht.1,by norm_num; linarith⟩
      · have nonempty : qs ≠ [] := by
          rintro rfl
          norm_num at ht
          linarith [ht.2]
        apply hNext nonempty t
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at ht
        exact ⟨le_of_not_ge left,by linarith [ht.2]⟩

/-- The zero panel remains valid across the turning threshold. -/
theorem turning_panel : panelTest 256 0 1 0 0 = true := rfl

/-- A positive floor at a clipped zero is rejected. -/
theorem reject_positive_at_turn : panelTest 256 1 1 0 0 = false := rfl

end PlasmaLean.Certificates.LowerActionHeightShift
