/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicConfined
public import PlasmaLean.Theory.Fields.BiotSavartComplex
public import PlasmaLean.Certificates.KernelFact

/-!
# Certified distance from the confinement region to the coils

For the complexified coil field (`Design/CoilFieldComplex`) we need a quantitative lower bound
on the distance from a real neighbourhood of the confinement region to every straight segment of
the coil set `filsC` (192 segments).

* `Far A c`: the point `c` is outside the square-section solid torus of half-width `A` around the
  unit circle: `|c₂| ≥ A`, or `c₀² + c₁² ≥ (1 + A)²`, or `c₀² + c₁² ≤ (1 - A)²`.
* `pieceOK A p q s e` (exact rational checker): on the parameter piece `[s, e]` of the segment
  `p → q` (integer vertices at scale `2⁻³²`), either the height `z(t)` (affine) stays `≥ A` or
  `≤ -A`, or `r²(t)` (a convex quadratic) stays `≤ (1 - A)²` (endpoints suffice) or `≥ (1 + A)²`
  (exact minimum of the quadratic on the piece). `segCheck` adds bisection with fuel.
* `pieceOK_sound`, `segCheck_sound`: the checkers imply `Far A` along the piece.
* `farAll_true` (kernel certificate, `kernel_fact`): every segment of `allSegs filsC` passes
  with `A = 7/20` and fuel `3`; hence `filsC_far`.
* `realTube w`: `|√(x₀² + x₁²) - 1| ≤ w`, `|x₂| ≤ w`; `dist_of_far`: points of `realTube w` are at
  distance `≥ d` from every `Far A` point when `w + d ≤ A`.
* Data bounds (`kernel_fact`): `filsC_kappa` (`|K| ≤ 90485364`), `filsC_norm_le`
  (`‖p‖ ≤ 3` for every segment start), `filsC_len_le` (`‖q - p‖ ≤ 23/10`).

**Sanity.** `far_vertex_fixture` (a coil vertex is `Far`), the rejected fixture
`not_far_circle` (the point `(1, 0, 0)` of the magnetic axis is not `Far`), and `Ka_sub_realTube`
(the closed confinement tube `Ka aF` lies in `realTube (3/20)`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilFieldComplex

open PlasmaLean.Fields PlasmaLean.Design.PolygonCoil PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.RationalStellarator.Confined
  PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Fields.BiotSavartComplex Set

/-! ## The exact checker -/

/-- The scale `2³²` as a rational. -/
def NQ : ℚ := 4294967296

/-- The scaled height `N z(t) = p₂ + t (q₂ - p₂)`. -/
def zQ (p q : ℤ × ℤ × ℤ) (t : ℚ) : ℚ := (p.2.2 : ℚ) + t * ((q.2.2 : ℚ) - p.2.2)

/-- Coefficient `a = v₀² + v₁²` of the scaled `N² r²(t) = a t² + b t + c`. -/
def qa (p q : ℤ × ℤ × ℤ) : ℚ := ((q.1 : ℚ) - p.1) ^ 2 + ((q.2.1 : ℚ) - p.2.1) ^ 2

/-- Coefficient `b = 2 (p₀ v₀ + p₁ v₁)`. -/
def qb (p q : ℤ × ℤ × ℤ) : ℚ :=
  2 * ((p.1 : ℚ) * ((q.1 : ℚ) - p.1) + (p.2.1 : ℚ) * ((q.2.1 : ℚ) - p.2.1))

/-- Coefficient `c = p₀² + p₁²`. -/
def qc (p : ℤ × ℤ × ℤ) : ℚ := (p.1 : ℚ) ^ 2 + (p.2.1 : ℚ) ^ 2

/-- The scaled squared cylindrical radius `N² r²(t)`. -/
def qQ (p q : ℤ × ℤ × ℤ) (t : ℚ) : ℚ := qa p q * t ^ 2 + qb p q * t + qc p

/-- The exact minimum of the convex quadratic `qQ` on `[s, e]`. -/
def qmin (p q : ℤ × ℤ × ℤ) (s e : ℚ) : ℚ :=
  if 0 ≤ 2 * qa p q * s + qb p q then qQ p q s
  else if 2 * qa p q * e + qb p q ≤ 0 then qQ p q e
  else qc p - qb p q ^ 2 / (4 * qa p q)

/-- **Piece check**: on `[s, e]` the segment is `Far A` by one of four exact criteria. -/
def pieceOK (A : ℚ) (p q : ℤ × ℤ × ℤ) (s e : ℚ) : Bool :=
  (decide (A * NQ ≤ zQ p q s) && decide (A * NQ ≤ zQ p q e)) ||
  (decide (zQ p q s ≤ -(A * NQ)) && decide (zQ p q e ≤ -(A * NQ))) ||
  (decide (qQ p q s ≤ (1 - A) ^ 2 * NQ ^ 2) && decide (qQ p q e ≤ (1 - A) ^ 2 * NQ ^ 2)) ||
  decide ((1 + A) ^ 2 * NQ ^ 2 ≤ qmin p q s e)

/-- Piece check with bisection (fuel `n`). -/
def segCheck (A : ℚ) (p q : ℤ × ℤ × ℤ) : ℕ → ℚ → ℚ → Bool
  | 0, s, e => pieceOK A p q s e
  | n + 1, s, e => pieceOK A p q s e ||
      (segCheck A p q n s ((s + e) / 2) && segCheck A p q n ((s + e) / 2) e)

/-- The check over all segments of a coil set. -/
def farAll (A : ℚ) (n : ℕ) (l : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) : Bool :=
  l.all fun z => segCheck A z.2.1 z.2.2 n 0 1

/-! ## Soundness -/

/-- `c` lies outside the square-section solid torus of half-width `A` around the unit circle. -/
def Far (A : ℝ) (c : Space) : Prop :=
  A ≤ |c 2| ∨ (1 + A) ^ 2 ≤ c 0 ^ 2 + c 1 ^ 2 ∨ c 0 ^ 2 + c 1 ^ 2 ≤ (1 - A) ^ 2

/-- An affine function bounded below at both ends of an interval is bounded below on it. -/
theorem affine_ge {z0 v K s e t : ℝ} (hs : K ≤ z0 + s * v) (he : K ≤ z0 + e * v) (hst : s ≤ t)
    (hte : t ≤ e) : K ≤ z0 + t * v := by
  rcases eq_or_lt_of_le (hst.trans hte) with h | h
  · have : t = s := le_antisymm (h ▸ hte) hst
    rw [this]; exact hs
  · have key : (e - s) * (z0 + t * v - K) =
        (e - t) * (z0 + s * v - K) + (t - s) * (z0 + e * v - K) := by
      ring
    have h1 : 0 ≤ (e - s) * (z0 + t * v - K) := by
      rw [key]; exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith)
        (by linarith))
    have := (mul_nonneg_iff_of_pos_left (by linarith : 0 < e - s)).1 h1
    linarith

/-- A convex quadratic bounded above at both ends of an interval is bounded above on it. -/
theorem quad_le {a b c B s e t : ℝ} (ha : 0 ≤ a) (hs : a * s ^ 2 + b * s + c ≤ B)
    (he : a * e ^ 2 + b * e + c ≤ B) (hst : s ≤ t) (hte : t ≤ e) : a * t ^ 2 + b * t + c ≤ B := by
  rcases eq_or_lt_of_le (hst.trans hte) with h | h
  · have : t = s := le_antisymm (h ▸ hte) hst
    rw [this]; exact hs
  · have key : (e - t) * (a * s ^ 2 + b * s + c) + (t - s) * (a * e ^ 2 + b * e + c) -
        (e - s) * (a * t ^ 2 + b * t + c) = a * (e - s) * (t - s) * (e - t) := by ring
    have h1 : 0 ≤ a * (e - s) * (t - s) * (e - t) :=
      mul_nonneg (mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)) (by linarith)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - t)
        (by linarith : 0 ≤ B - (a * s ^ 2 + b * s + c)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - s) (by linarith : 0 ≤ B - (a * e ^ 2 + b * e + c))]

/-- The exact minimum of a convex quadratic on an interval (three cases). -/
theorem quad_ge {a b c s e t : ℝ} (ha : 0 ≤ a) (hst : s ≤ t) (hte : t ≤ e) :
    (if 0 ≤ 2 * a * s + b then a * s ^ 2 + b * s + c
      else if 2 * a * e + b ≤ 0 then a * e ^ 2 + b * e + c
      else c - b ^ 2 / (4 * a)) ≤ a * t ^ 2 + b * t + c := by
  split_ifs with h1 h2
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - s) (by nlinarith : 0 ≤ a * (t + s) + b)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - t) (by nlinarith : 0 ≤ -(a * (t + e) + b))]
  · have ha' : 0 < a := by
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp at h1 h2; linarith
      · exact h
    have e1 : a * t ^ 2 + b * t + c - (c - b ^ 2 / (4 * a)) = (2 * a * t + b) ^ 2 / (4 * a) := by
      field_simp; ring
    have : 0 ≤ (2 * a * t + b) ^ 2 / (4 * a) := by positivity
    linarith

/-- Coordinates of a segment point between integer vertices. -/
theorem seg_ptR_apply (p q : ℤ × ℤ × ℤ) (t : ℝ) :
    seg (ptR p) (ptR q) t 0 = ((p.1 : ℝ) + t * ((q.1 : ℝ) - p.1)) / S32 ∧
    seg (ptR p) (ptR q) t 1 = ((p.2.1 : ℝ) + t * ((q.2.1 : ℝ) - p.2.1)) / S32 ∧
    seg (ptR p) (ptR q) t 2 = ((p.2.2 : ℝ) + t * ((q.2.2 : ℝ) - p.2.2)) / S32 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [seg_apply, ptR] <;> ring

/-- `S32` is the rational scale `NQ`. -/
theorem S32_eq : S32 = ((NQ : ℚ) : ℝ) := by norm_num [S32, NQ]

/-- **Soundness of the piece check.** -/
theorem pieceOK_sound {A : ℚ} {p q : ℤ × ℤ × ℤ} {s e : ℚ} (h : pieceOK A p q s e = true)
    {t : ℝ} (hst : (s : ℝ) ≤ t) (hte : t ≤ (e : ℝ)) : Far A (seg (ptR p) (ptR q) t) := by
  obtain ⟨h0, h1, h2⟩ := seg_ptR_apply p q t
  have hN : (0 : ℝ) < S32 := S32_pos
  have hNQ : ((NQ : ℚ) : ℝ) = S32 := S32_eq.symm
  -- real forms of the scaled quantities
  have hz : ∀ u : ℚ, ((zQ p q u : ℚ) : ℝ) = (p.2.2 : ℝ) + (u : ℝ) * ((q.2.2 : ℝ) - p.2.2) := by
    intro u; simp [zQ]
  have hQ : ∀ u : ℚ, ((qQ p q u : ℚ) : ℝ) = (qa p q : ℝ) * (u : ℝ) ^ 2 + (qb p q : ℝ) * u +
      (qc p : ℝ) := by intro u; simp [qQ]
  have ha : (0 : ℝ) ≤ (qa p q : ℝ) := by
    have : (0 : ℚ) ≤ qa p q := by unfold qa; positivity
    exact_mod_cast this
  -- the squared radius at `t`
  have hr : seg (ptR p) (ptR q) t 0 ^ 2 + seg (ptR p) (ptR q) t 1 ^ 2 =
      ((qa p q : ℝ) * t ^ 2 + (qb p q : ℝ) * t + (qc p : ℝ)) / S32 ^ 2 := by
    rw [h0, h1]; simp only [qa, qb, qc]; push_cast; field_simp; ring
  simp only [pieceOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Far
  rcases h with ((⟨hs, he⟩ | ⟨hs, he⟩) | ⟨hs, he⟩) | hm
  · left
    have hs' : ((A * NQ : ℚ) : ℝ) ≤ ((zQ p q s : ℚ) : ℝ) := by exact_mod_cast hs
    have he' : ((A * NQ : ℚ) : ℝ) ≤ ((zQ p q e : ℚ) : ℝ) := by exact_mod_cast he
    rw [hz] at hs' he'
    push_cast at hs' he'
    rw [hNQ] at hs' he'
    have := affine_ge hs' he' hst hte
    rw [h2, le_abs, le_div_iff₀ hN]
    left; linarith
  · left
    have hs' : ((zQ p q s : ℚ) : ℝ) ≤ ((-(A * NQ) : ℚ) : ℝ) := by exact_mod_cast hs
    have he' : ((zQ p q e : ℚ) : ℝ) ≤ ((-(A * NQ) : ℚ) : ℝ) := by exact_mod_cast he
    rw [hz] at hs' he'
    push_cast at hs' he'
    rw [hNQ] at hs' he'
    have := affine_ge (z0 := -(p.2.2 : ℝ)) (v := -((q.2.2 : ℝ) - p.2.2)) (K := (A : ℝ) * S32)
      (by linarith) (by linarith) hst hte
    rw [h2, le_abs]
    right
    rw [← neg_div, le_div_iff₀ hN]; linarith
  · right; right
    have hs' : ((qQ p q s : ℚ) : ℝ) ≤ (((1 - A) ^ 2 * NQ ^ 2 : ℚ) : ℝ) := by exact_mod_cast hs
    have he' : ((qQ p q e : ℚ) : ℝ) ≤ (((1 - A) ^ 2 * NQ ^ 2 : ℚ) : ℝ) := by exact_mod_cast he
    rw [hQ] at hs' he'
    push_cast at hs' he'
    rw [hNQ] at hs' he'
    have := quad_le ha hs' he' hst hte
    rw [hr, div_le_iff₀ (by positivity)]; exact this
  · right; left
    have hm' : (((1 + A) ^ 2 * NQ ^ 2 : ℚ) : ℝ) ≤ ((qmin p q s e : ℚ) : ℝ) := by exact_mod_cast hm
    have hq := quad_ge (a := (qa p q : ℝ)) (b := (qb p q : ℝ)) (c := (qc p : ℝ)) ha hst hte
    have hcast : ((qmin p q s e : ℚ) : ℝ) = (if 0 ≤ 2 * (qa p q : ℝ) * s + qb p q then
        (qa p q : ℝ) * (s : ℝ) ^ 2 + qb p q * s + qc p
        else if 2 * (qa p q : ℝ) * e + qb p q ≤ 0 then
          (qa p q : ℝ) * (e : ℝ) ^ 2 + qb p q * e + qc p
        else (qc p : ℝ) - (qb p q : ℝ) ^ 2 / (4 * qa p q)) := by
      unfold qmin
      by_cases c1 : (0 : ℚ) ≤ 2 * qa p q * s + qb p q
      · have c1' : (0 : ℝ) ≤ 2 * (qa p q : ℝ) * s + qb p q := by exact_mod_cast c1
        simp only [c1, c1', ↓reduceIte]; simp [qQ]
      · have c1' : ¬ (0 : ℝ) ≤ 2 * (qa p q : ℝ) * s + qb p q := by exact_mod_cast c1
        simp only [c1, c1', ↓reduceIte]
        by_cases c2 : 2 * qa p q * e + qb p q ≤ 0
        · have c2' : 2 * (qa p q : ℝ) * e + qb p q ≤ 0 := by exact_mod_cast c2
          simp only [c2, c2', ↓reduceIte]; simp [qQ]
        · have c2' : ¬ 2 * (qa p q : ℝ) * e + qb p q ≤ 0 := by exact_mod_cast c2
          simp only [c2, c2', ↓reduceIte]; push_cast; ring
    push_cast at hm'
    rw [hNQ] at hm'
    rw [hcast] at hm'
    rw [hr, le_div_iff₀ (by positivity)]; linarith

/-- **Soundness of the bisection check.** -/
theorem segCheck_sound {A : ℚ} {p q : ℤ × ℤ × ℤ} :
    ∀ (n : ℕ) {s e : ℚ}, segCheck A p q n s e = true →
      ∀ {t : ℝ}, (s : ℝ) ≤ t → t ≤ (e : ℝ) → Far A (seg (ptR p) (ptR q) t)
  | 0, s, e, h, t, hst, hte => pieceOK_sound h hst hte
  | n + 1, s, e, h, t, hst, hte => by
    simp only [segCheck, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact pieceOK_sound h hst hte
    · by_cases hm : t ≤ (((s + e) / 2 : ℚ) : ℝ)
      · exact segCheck_sound n h1 hst hm
      · exact segCheck_sound n h2 (le_of_not_ge hm) hte

/-- **Kernel certificate**: every segment of the coil set passes the check at `A = 7/20`. -/
theorem farAll_true : farAll (7 / 20) 3 (allSegs filsC) = true := by kernel_fact

/-- Every point of every coil segment is `Far (7/20)`. -/
theorem filsC_far {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} (hz : z ∈ allSegs filsC) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : Far (7 / 20) (seg (ptR z.2.1) (ptR z.2.2) t) := by
  have h := List.all_eq_true.mp farAll_true z hz
  have := segCheck_sound (A := 7 / 20) 3 h (t := t) (by simpa using ht.1) (by simpa using ht.2)
  simpa using this

/-! ## From `Far` to a distance -/

/-- The closed real neighbourhood `|√(x₀² + x₁²) - 1| ≤ w`, `|x₂| ≤ w` of the unit circle. -/
def realTube (w : ℝ) : Set Space :=
  {x | |Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - 1| ≤ w ∧ |x 2| ≤ w}

/-- The cylindrical radius is `1`-Lipschitz: `|r(x) - r(c)| ≤ ‖x - c‖`. -/
theorem abs_sqrt_sub_le (x c : Space) :
    |Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - Real.sqrt (c 0 ^ 2 + c 1 ^ 2)| ≤ ‖x - c‖ := by
  set R := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)
  set ρ := Real.sqrt (c 0 ^ 2 + c 1 ^ 2)
  have hR : R ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hρ : ρ ^ 2 = c 0 ^ 2 + c 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hcs : x 0 * c 0 + x 1 * c 1 ≤ R * ρ := by
    have h1 : (x 0 * c 0 + x 1 * c 1) ^ 2 ≤ (R * ρ) ^ 2 := by
      rw [mul_pow, hR, hρ]; nlinarith [sq_nonneg (x 0 * c 1 - x 1 * c 0)]
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have hn := norm_sq_space (x - c)
  simp only [PiLp.sub_apply] at hn
  have h2 : (R - ρ) ^ 2 ≤ ‖x - c‖ ^ 2 := by nlinarith [sq_nonneg (x 2 - c 2)]
  exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |> fun h => abs_le.2 ⟨h.1, h.2⟩

/-- **Distance from the tube to a `Far` point**: if `x ∈ realTube w`, `Far A c` and
`w + d ≤ A`, then `‖x - c‖ ≥ d`. -/
theorem dist_of_far {w d A : ℝ} (hwdA : w + d ≤ A) (hA : A < 1) {x c : Space}
    (hx : x ∈ realTube w) (hc : Far A c) : d ≤ ‖x - c‖ := by
  obtain ⟨hr, hz⟩ := hx
  have hL := abs_sqrt_sub_le x c
  have hw : 0 ≤ w := (abs_nonneg _).trans hz
  rcases hc with hc | hc | hc
  · have h := abs_coord_le (x - c) 2
    simp only [PiLp.sub_apply] at h
    have : |c 2| - |x 2| ≤ |x 2 - c 2| := by
      have := abs_sub_abs_le_abs_sub (c 2) (x 2); rwa [abs_sub_comm (c 2)] at this
    linarith
  · have hρ : 1 + A ≤ Real.sqrt (c 0 ^ 2 + c 1 ^ 2) :=
      Real.le_sqrt_of_sq_le hc
    have := (abs_le.1 hr).2
    have := (abs_le.1 hL).1
    linarith
  · have hρ : Real.sqrt (c 0 ^ 2 + c 1 ^ 2) ≤ 1 - A := by
      rw [Real.sqrt_le_left (by linarith)]; exact hc
    have := (abs_le.1 hr).1
    have := (abs_le.1 hL).2
    linarith

/-! ## Data bounds -/

/-- Integer bound check: `|K| ≤ 90485364`, `‖p‖² ≤ 9 N²`, `100 ‖q - p‖² ≤ 529 N²`. -/
def dataOK (z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) : Bool :=
  decide (z.1.natAbs ≤ 90485364) &&
  decide (z.2.1.1 ^ 2 + z.2.1.2.1 ^ 2 + z.2.1.2.2 ^ 2 ≤ 9 * 4294967296 ^ 2) &&
  decide (100 * ((z.2.2.1 - z.2.1.1) ^ 2 + (z.2.2.2.1 - z.2.1.2.1) ^ 2 +
    (z.2.2.2.2 - z.2.1.2.2) ^ 2) ≤ 529 * 4294967296 ^ 2)

/-- Kernel check of the data bounds. -/
theorem dataOK_all : (allSegs filsC).all dataOK = true := by kernel_fact

/-- The current numerators are bounded: `|K| ≤ 90485364`. -/
theorem filsC_kappa {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} (hz : z ∈ allSegs filsC) :
    |(z.1 : ℝ) / S32| ≤ 90485364 / S32 := by
  have h := List.all_eq_true.mp dataOK_all z hz
  simp only [dataOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : |(z.1 : ℝ)| ≤ 90485364 := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast h.1.1
  rw [abs_div, abs_of_pos S32_pos]
  exact div_le_div_of_nonneg_right h1 S32_pos.le

/-- Squared norm of an integer point. -/
theorem norm_ptR_sq (p : ℤ × ℤ × ℤ) :
    ‖ptR p‖ ^ 2 = ((p.1 : ℝ) ^ 2 + (p.2.1 : ℝ) ^ 2 + (p.2.2 : ℝ) ^ 2) / S32 ^ 2 := by
  rw [norm_sq_space]; simp [ptR]; field_simp

/-- Every segment starts within distance `3` of the origin. -/
theorem filsC_norm_le {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} (hz : z ∈ allSegs filsC) :
    ‖ptR z.2.1‖ ≤ 3 := by
  have h := List.all_eq_true.mp dataOK_all z hz
  simp only [dataOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 : ((z.2.1.1 : ℝ) ^ 2 + (z.2.1.2.1 : ℝ) ^ 2 + (z.2.1.2.2 : ℝ) ^ 2) ≤
      9 * 4294967296 ^ 2 := by exact_mod_cast h.1.2
  have : ‖ptR z.2.1‖ ^ 2 ≤ 3 ^ 2 := by
    rw [norm_ptR_sq, div_le_iff₀ (by have := S32_pos; positivity)]
    simp only [S32]; linarith
  exact abs_le_of_sq_le_sq' this (by norm_num) |>.2 |> fun h => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (abs_le_of_sq_le_sq' this (by norm_num)).2

/-- Every segment has length at most `23/10`. -/
theorem filsC_len_le {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} (hz : z ∈ allSegs filsC) :
    ‖ptR z.2.2 - ptR z.2.1‖ ≤ 23 / 10 := by
  have h := List.all_eq_true.mp dataOK_all z hz
  simp only [dataOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 : 100 * (((z.2.2.1 : ℝ) - z.2.1.1) ^ 2 + ((z.2.2.2.1 : ℝ) - z.2.1.2.1) ^ 2 +
      ((z.2.2.2.2 : ℝ) - z.2.1.2.2) ^ 2) ≤ 529 * 4294967296 ^ 2 := by exact_mod_cast h.2
  have : ‖ptR z.2.2 - ptR z.2.1‖ ^ 2 ≤ (23 / 10) ^ 2 := by
    have e : ‖ptR z.2.2 - ptR z.2.1‖ ^ 2 = (((z.2.2.1 : ℝ) - z.2.1.1) ^ 2 +
        ((z.2.2.2.1 : ℝ) - z.2.1.2.1) ^ 2 + ((z.2.2.2.2 : ℝ) - z.2.1.2.2) ^ 2) / S32 ^ 2 := by
      rw [norm_sq_space]; simp [ptR]; field_simp
    rw [e, div_le_iff₀ (by have := S32_pos; positivity)]
    simp only [S32]; linarith
  exact (abs_le_of_sq_le_sq' this (by norm_num)).2

/-! ## Sanity -/

/-- A coil vertex is `Far` (accepted fixture: the first vertex of the first filament). -/
theorem far_vertex_fixture :
    Far (7 / 20) (ptR (7925370926, 828655364, 1977389707)) := by
  unfold Far; right; left
  simp [ptR, S32]; norm_num

/-- Rejected fixture: the point `(1, 0, 0)` on the unit circle is not `Far`. -/
theorem not_far_circle : ¬ Far (7 / 20) (WithLp.toLp 2 ![1, 0, 0]) := by
  unfold Far; simp; norm_num

/-- The closed confinement tube `Ka aF` lies in `realTube (3/20)`. -/
theorem Ka_sub_realTube : Ka aF ⊆ realTube (3 / 20) := by
  intro x ⟨hs, hz⟩
  have ha : aF = 3420 / 32761 := rfl
  refine ⟨?_, hz.trans (by rw [ha]; norm_num)⟩
  simp only [sc, r2] at hs
  rw [abs_le] at hs ⊢
  have h0 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (x 0 ^ 2 + x 1 ^ 2)
  rw [ha] at hs
  constructor <;> nlinarith

end PlasmaLean.Design.CoilFieldComplex
