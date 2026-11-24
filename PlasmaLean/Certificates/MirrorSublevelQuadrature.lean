/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature
public import PlasmaLean.Theory.Kinetic.MirrorSublevelPartition

/-! # Sublevel arclength of a packed mirror quadrature

A selected time cell contributes its arclength bound once, including when
the stored speed is exactly the requested threshold. The angular cell width
is 1/3072 and its density carries a factor of 2⁻²⁰.
-/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorSublevelQuadrature
open MeasureTheory Set MirrorActionQuadrature Kinetic.MirrorSublevelAction

def selectedDensity (v p : ℕ) : ℕ := if v ≤ speed p then density p else 0

/-- Sum the directed density over the selected cells in one packed word. -/
def slabTail (v : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => selectedDensity v p + slabTail v n (p >>> 72)

/-- Density sum over the entire prescribed angular bracket. -/
def packetTail {u : Bool} (v : ℕ) (bs : List (Block u)) : ℕ :=
  (bs.map fun b => slabTail v 48 b.packed).sum

private theorem speed_bound {u : Bool} {p : ℕ} {z : ℝ} (hr : rootTest u p = true)
    (hg : Directed u (max z 0) (speedSq p / 67108864)) :
    Directed u (Real.sqrt z) (speed p / 1048576) := by
  have pos : 0 ≤ (speed p : ℝ) / 1048576 := by positivity
  cases u
  · change (speed p ^ 2).ble (speedSq p * 16384) = true at hr
    have hs : (speed p : ℝ) ^ 2 ≤ speedSq p * 16384 := by exact_mod_cast Nat.le_of_ble_eq_true hr
    change (speedSq p : ℝ) / 67108864 ≤ max z 0 at hg
    apply (sq_le_sq₀ pos (Real.sqrt_nonneg z)).mp
    nlinarith only [hs, hg, Real.sq_sqrt' (x := z)]
  · change (speedSq p * 16384).ble (speed p ^ 2) = true at hr
    have hs : (speedSq p : ℝ) * 16384 ≤ (speed p : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_of_ble_eq_true hr
    change max z 0 ≤ (speedSq p : ℝ) / 67108864 at hg
    apply (sq_le_sq₀ (Real.sqrt_nonneg z) pos).mp
    nlinarith only [hs, hg, Real.sq_sqrt' (x := z)]

noncomputable def masked (f w : ℝ → ℝ) (h : ℝ) (v : ℕ) : ℝ → ℝ :=
  {t | f t ≤ h - ((v : ℝ) / 1048576) ^ 2 / 2}.indicator w

/-- One physical time cell bounds the threshold indicator times its arclength density. -/
theorem cell_bound {u : Bool} {p v : ℕ} (hzero : u = true ∨ 0 < v)
    {h a t : ℝ} {f w : ℝ → ℝ} (c : Cell u w f h a p) (root : rootTest u p = true)
    (ht : t ∈ Icc a (a + 1 / 3072)) (hw : 0 ≤ w t) :
    Directed u (masked f w h v t) (selectedDensity v p / 1048576) := by
  obtain ⟨hd, hg⟩ := c t ht
  have hs := speed_bound root hg
  let E : Set ℝ := {t | f t ≤ h - ((v : ℝ) / 1048576) ^ 2 / 2}
  have scale : (v : ℝ) / 1048576 ≤ (speed p : ℝ) / 1048576 ↔ v ≤ speed p := by
    rw [div_le_div_iff_of_pos_right (by norm_num)]
    exact Nat.cast_le
  cases u
  · have vpos : (0 : ℝ) < v / 1048576 := by
      have hn : 0 < v := by simpa using hzero
      positivity
    change E.indicator w t ≥ (selectedDensity v p : ℝ) / 1048576
    by_cases sel : v ≤ speed p
    · have mem : t ∈ E := (Kinetic.MirrorSublevelPartition.sublevel_iff_speed vpos).mpr
        ((scale.mpr sel).trans hs)
      simpa [selectedDensity, sel, mem, MirrorActionQuadrature.Directed] using hd
    · rw [show selectedDensity v p = 0 by simp [selectedDensity, sel]]
      simp only [Nat.cast_zero, zero_div]
      by_cases mem : t ∈ E <;> simp [mem, hw]
  · change E.indicator w t ≤ (selectedDensity v p : ℝ) / 1048576
    by_cases mem : t ∈ E
    · have hz : f t ≤ h - ((v : ℝ) / 1048576) ^ 2 / 2 := mem
      have sel := scale.mp ((Real.le_sqrt_of_sq_le (by linarith only [hz])).trans hs)
      simpa [selectedDensity, sel, mem, MirrorActionQuadrature.Directed] using hd
    · rw [Set.indicator_of_notMem mem]
      positivity

private theorem append_bound {u : Bool} {a b c x y : ℝ} (h₁ : Directed u (b - a) x)
    (h₂ : Directed u (c - b) y) : Directed u (c - a) (x + y) := by
  cases u <;> simp [MirrorActionQuadrature.Directed] at * <;> linarith

/-- Sum a scalar primitive over the cells of a slab. -/
private theorem slab_bound {u : Bool} {f w F : ℝ → ℝ} {h L R : ℝ} {v : ℕ}
    (step : ∀ a p, L ≤ a → a + 1 / 3072 ≤ R → Cell u w f h a p → rootTest u p = true →
      Directed u (F (a + 1 / 3072) - F a) (selectedDensity v p / (3072 * 1048576 : ℝ)))
    (n p : ℕ) (a : ℝ) (ha : L ≤ a) (hb : a + n / 3072 ≤ R)
    (c : Cells u w f h a n p) (hr : (read u n p).1 = true) :
    Directed u (F (a + n / 3072) - F a) (slabTail v n p / (3072 * 1048576 : ℝ)) := by
  induction n generalizing p a with
  | zero => cases u <;> simp [MirrorActionQuadrature.Directed, slabTail]
  | succ n ih =>
    obtain ⟨head, tail⟩ := c
    change rootTest u p && (read u n (p >>> 72)).1 = true at hr
    obtain ⟨root, rest⟩ := Bool.and_eq_true_iff.mp hr
    have endpt : a + 1 / 3072 + n / 3072 = a + (n + 1 : ℕ) / 3072 := by push_cast; ring
    have next := step a p ha (by push_cast at hb; linarith [Nat.cast_nonneg (α := ℝ) n]) head root
    have more := ih (p >>> 72) (a + 1 / 3072) (by linarith) (endpt ▸ hb) tail rest
    rw [endpt] at more
    simpa [slabTail, add_div] using append_bound next more

/-- Sum the same primitive across the boundaries of all packed slabs. -/
private theorem packet_bound {u : Bool} {f w F : ℝ → ℝ} {h L R : ℝ} {v : ℕ}
    (step : ∀ a p, L ≤ a → a + 1 / 3072 ≤ R → Cell u w f h a p → rootTest u p = true →
      Directed u (F (a + 1 / 3072) - F a) (selectedDensity v p / (3072 * 1048576 : ℝ)))
    (bs : List (Block u)) (a : ℝ) (ha : L ≤ a) (hb : a + bs.length / 64 ≤ R)
    (C : Covers u w f h a bs) :
    Directed u (F (a + bs.length / 64) - F a) (packetTail v bs / (3072 * 1048576 : ℝ)) := by
  induction bs generalizing a with
  | nil => cases u <;> simp [MirrorActionQuadrature.Directed, packetTail]
  | cons b bs ih =>
    obtain ⟨head, tail⟩ := C
    have ep : a + 1 / 64 + bs.length / 64 = a + ((b :: bs).length : ℕ) / 64 := by simp; ring
    have stop : a + 1 / 64 ≤ R := by
      rw [← ep] at hb
      linarith [Nat.cast_nonneg (α := ℝ) bs.length]
    have one := slab_bound step 48 b.packed a ha (by norm_num; exact stop) head
      (congrArg Prod.fst b.checked)
    have eq : a + (48 : ℕ) / 3072 = a + 1 / 64 := by norm_num
    rw [eq] at one
    have more := ih (a + 1 / 64) (by linarith) (ep ▸ hb) tail
    rw [ep] at more
    rw [show packetTail v (b :: bs) = slabTail v 48 b.packed + packetTail v bs by simp [packetTail],
      Nat.cast_add, add_div]
    exact append_bound one more

/-- On a time bracket, the weighted measure of the field-strength sublevel equals
the usual threshold-indicator integral with respect to geometric angle. -/
theorem sublevel_trace {f w : ℝ → ℝ} {L R h : ℝ} (v : ℕ) (hab : L ≤ R)
    (hf : Measurable f) (hw : Measurable w) (hn : ∀ t ∈ Ioc L R, 0 ≤ w t) :
    sublevelLength ((volume.restrict (Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t)))
      f (h - ((v : ℝ) / 1048576) ^ 2 / 2) = ∫ t in L..R, masked f w h v t := by
  let E : Set ℝ := {t | f t ≤ h - ((v : ℝ) / 1048576) ^ 2 / 2}
  have he : MeasurableSet E := measurableSet_le hf measurable_const
  change ((volume.restrict (Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t))).real E =
    ∫ t in L..R, E.indicator w t
  rw [← integral_indicator_one he, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  by_cases mem : t ∈ E <;> simp [mem, ENNReal.toReal_ofReal (hn t ht)]

/-- The archived primitive panel enclosures imply an actual directed threshold
arclength bound on their entire angular bracket, with the archived density scale. -/
theorem covers_sublevel {u : Bool} {bs : List (Block u)} {v : ℕ} (hzero : u = true ∨ 0 < v)
    {f w : ℝ → ℝ} {L R h : ℝ} (endpt : L + bs.length / 64 = R) (c : Covers u w f h L bs)
    (hf : Measurable f) (hw : Measurable w) (hn : ∀ t ∈ Icc L R, 0 ≤ w t)
    (hi : IntegrableOn w (Ioc L R)) :
    Directed u (sublevelLength
      ((volume.restrict (Ioc L R)).withDensity (fun t => ENNReal.ofReal (w t)))
      f (h - ((v : ℝ) / 1048576) ^ 2 / 2)) (packetTail v bs / (3072 * 1048576 : ℝ)) := by
  have hab : L ≤ R := by rw [← endpt]; linarith [Nat.cast_nonneg (α := ℝ) bs.length]
  rw [sublevel_trace v hab hf hw (fun t ht => hn t (Ioc_subset_Icc_self ht))]
  let g := masked f w h v
  let F := fun x : ℝ => ∫ t in L..x, g t
  have gated : IntegrableOn g (Ioc L R) := hi.indicator (measurableSet_le hf measurable_const)
  have intg {x y : ℝ} (hx : L ≤ x) (hxy : x ≤ y) (hy : y ≤ R) :
      IntervalIntegrable g volume x y := (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr
        (gated.mono_set (Ioc_subset_Ioc hx hy))
  have step (a : ℝ) (p : ℕ) (ha : L ≤ a) (hb : a + 1 / 3072 ≤ R)
      (C : Cell u w f h a p) (root : rootTest u p = true) :
      Directed u (F (a + 1 / 3072) - F a) (selectedDensity v p / (3072 * 1048576 : ℝ)) := by
    have ab : a ≤ a + 1 / 3072 := by linarith
    have integr := intg ha ab hb
    have sum := intervalIntegral.integral_add_adjacent_intervals
      (intg le_rfl ha (ab.trans hb)) integr
    have localEq : F (a + 1 / 3072) - F a = ∫ t in a..a + 1 / 3072, g t := by
      dsimp [F]
      linarith only [sum]
    rw [localEq]
    let k : ℝ := selectedDensity v p / 1048576
    have weight : (∫ _ in a..a + 1 / 3072, k) = selectedDensity v p / (3072 * 1048576 : ℝ) := by
      simp [k, smul_eq_mul]; ring
    rw [← weight]
    have point (t : ℝ) (ht : t ∈ Icc a (a + 1 / 3072)) : Directed u (g t) k :=
      cell_bound hzero C root ht (hn t ⟨ha.trans ht.1, ht.2.trans hb⟩)
    cases u
    · exact intervalIntegral.integral_mono_on ab intervalIntegrable_const integr point
    · exact intervalIntegral.integral_mono_on ab integr intervalIntegrable_const point
  have result := packet_bound step bs L le_rfl endpt.le c
  rw [endpt] at result
  simpa [F, g] using result

end PlasmaLean.Certificates.MirrorSublevelQuadrature
