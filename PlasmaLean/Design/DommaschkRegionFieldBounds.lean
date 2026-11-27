/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRegionRowsAll
public import PlasmaLean.Design.DommaschkRegionRegularity

/-!
# Field bounds for QA2R on the whole spatial envelope, at every angle

For every planar point `p` of the closed envelope `Region` (`7/8 ≤ R ≤ 1`, `|z| ≤ 5/64`) and every
toroidal angle `t`, with `B = DommaschkQA2R.field DommaschkQA2R.candidate`:

* `toroidal_bounds`: `47/50 ≤ B_φ ≤ 13/10`;
* `planar_speed_le`: the field-line equation with the angle as time has speed
  `‖euclideanFlow 0 1 t p‖ ≤ 9/25`;
* `strength_ge`, `strength_le`: `47/50 ≤ ‖B‖ ≤ 141/100` at `cylPoint (p 0) t (p 1)`;
* `flowLabel_speed_le`: the same speed bound in the form of the field `speed` of
  `FlowLabel.Tube`.

They follow from the three polynomial inequalities `b₀ R⁷ ≤ D ≤ c₁ R⁷`,
`n_R² + n_z² ≤ M² D²` (`polynomial_bounds`), certified on an adaptive grid of boxes by centred
interval enclosures (`DommaschkRegionGrid.rows`, `DommaschkRegionEnclosure.good_sound`).

The passage from the polynomial inequalities to the field (`PolyBounds.toroidal`, `.poloidal`,
`.speed`, `.strength_ge`, `.strength_sq_le`) is stated at one point with arbitrary constants, and
`of_good` produces them from the check on any box: a box around one slab of a thin tube gives the
sharper constants of that slab.

These are bounds on the whole envelope, which is much larger than the thin tubes of note N-216:
untrusted sampling gives the suprema `0.3025` (speed) and `[0.9559, 1.3315]` (strength) on the
envelope.

**Sanity.** `speed_bound_fixture`: the numerical values of the thresholds.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRegionFieldBounds
open Fields Contract Set
open Certificates.PositionFrameSlabs (Plane)
open DommaschkSignedTraceDomain DommaschkBounceField DommaschkKam DommaschkJacobian
open DommaschkCartesianAngleFlow DkPoly DommaschkRegionGrid

/-! ## From the polynomial inequalities to the field, with arbitrary constants

These statements hold at a single point and for any constants, so that they also apply to the
check `DommaschkRegionEnclosure.good` on a box around a thin tube (`of_good`). -/

/-- The three polynomial inequalities at a cylindrical point, with constants `b`, `c`, `m`. -/
def PolyBounds (b c m R t z : ℝ) : Prop :=
  b * R ^ 7 ≤ atPoint dD R t z ∧ atPoint dD R t z ≤ c * R ^ 7 ∧
    atPoint dnR R t z ^ 2 + atPoint dnZ R t z ^ 2 ≤ m ^ 2 * atPoint dD R t z ^ 2

/-- The check on a box gives the polynomial inequalities at every point of the box. -/
theorem of_good {b c m : ℚ} (hb : 0 ≤ b) (hc : 0 ≤ c) {box : Box}
    (h : DommaschkRegionEnclosure.good b c m box = true) {R t z : ℝ}
    (mem : box.Mem (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t))) :
    PolyBounds b c m R t z := by
  simpa [PolyBounds, atPoint] using DommaschkRegionEnclosure.good_sound hb hc h mem

/-- The toroidal component lies between `b` and `c`. -/
theorem PolyBounds.toroidal {b c m R t z : ℝ} (h : PolyBounds b c m R t z) (hR : 0 < R) :
    b ≤ cylBphi R t z ∧ cylBphi R t z ≤ c := by
  obtain ⟨lo, hi, -⟩ := h
  rw [(field_id hR t z).1] at lo hi
  have h7 : 0 < R ^ 7 := by positivity
  exact ⟨le_of_mul_le_mul_left (by linarith) h7, le_of_mul_le_mul_left (by linarith) h7⟩

/-- The poloidal components are at most `m B_φ / R` in norm. -/
theorem PolyBounds.poloidal {b c m R t z : ℝ} (h : PolyBounds b c m R t z) (hR : 0 < R) :
    R ^ 2 * (cylBR R t z ^ 2 + cylBz R t z ^ 2) ≤ m ^ 2 * cylBphi R t z ^ 2 := by
  obtain ⟨-, -, sp⟩ := h
  obtain ⟨d, nr, nz⟩ := field_id hR t z
  rw [d, nr, nz] at sp
  have h14 : 0 < R ^ 14 := by positivity
  refine le_of_mul_le_mul_left ?_ h14
  linear_combination sp

/-- The planar speed of the field-line equation is at most `m`. -/
theorem PolyBounds.speed {b c m t : ℝ} {p : Plane} (h : PolyBounds b c m (p 0) t (p 1))
    (hR : 0 < p 0) (hb : 0 < b) (hm : 0 ≤ m) : ‖euclideanFlow 0 1 t p‖ ≤ m := by
  have hφ : 0 < cylBphi (p 0) t (p 1) := hb.trans_le (h.toroidal hR).1
  have pol := h.poloidal hR
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hm, ?_⟩
  have e0 : (euclideanFlow 0 1 t p) 0 = p 0 * cylBR (p 0) t (p 1) / cylBphi (p 0) t (p 1) := by
    simp [euclideanFlow, physicalFlow, coordinates]
  have e1 : (euclideanFlow 0 1 t p) 1 = p 0 * cylBz (p 0) t (p 1) / cylBphi (p 0) t (p 1) := by
    simp [euclideanFlow, physicalFlow, coordinates]
  rw [e0, e1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, div_pow, div_pow, ← add_div,
    div_le_iff₀ (by positivity)]
  linear_combination pol

/-- The field strength is at least `b`. -/
theorem PolyBounds.strength_ge {b c m R t z : ℝ} (h : PolyBounds b c m R t z) (hR : 0 < R)
    (hb : 0 ≤ b) : b ≤ ‖B (cylPoint R t z)‖ := by
  obtain ⟨bl, -⟩ := h.toroidal hR
  have sq := DommaschkKamC.norm_field_sq R t z
  apply (sq_le_sq₀ hb (norm_nonneg _)).mp
  change _ ≤ ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R t z)‖ ^ 2
  rw [sq]
  nlinarith [sq_nonneg (cylBR R t z), sq_nonneg (cylBz R t z), pow_le_pow_left₀ hb bl 2]

/-- The squared field strength is at most `c² (1 + m²/R²)`. -/
theorem PolyBounds.strength_sq_le {b c m R t z : ℝ} (h : PolyBounds b c m R t z) (hR : 0 < R)
    (hb : 0 ≤ b) : ‖B (cylPoint R t z)‖ ^ 2 ≤ c ^ 2 * (1 + m ^ 2 / R ^ 2) := by
  obtain ⟨bl, bu⟩ := h.toroidal hR
  have pol := h.poloidal hR
  have sq := DommaschkKamC.norm_field_sq R t z
  change ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R t z)‖ ^ 2 ≤ _
  rw [sq]
  have φ2 : cylBphi R t z ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (hb.trans bl) bu 2
  have r2 : 0 < R ^ 2 := by positivity
  have pol' : cylBR R t z ^ 2 + cylBz R t z ^ 2 ≤ m ^ 2 / R ^ 2 * cylBphi R t z ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ r2]
    linarith
  have m2 : 0 ≤ m ^ 2 / R ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left φ2 m2]

/-! ## The whole envelope -/

/-- **The three polynomial inequalities** on the envelope, at every angle. -/
theorem polynomial_bounds {R z : ℝ} (t : ℝ) (lo : 7 / 8 ≤ R) (hi : R ≤ 1) (hz : |z| ≤ 5 / 64) :
    PolyBounds (47 / 50) (13 / 10) (9 / 25) R t z := by
  have h := bounds_of_rows rows (u := R - dkR0) (z := z) (c := Real.cos (2 * t))
    (s := Real.sin (2 * t)) (by unfold dkR0; linarith) (by unfold dkR0; linarith) hz
    (Real.cos_sq_add_sin_sq (2 * t))
  simpa [PolyBounds, Bounds, b₀, c₁, M, atPoint] using h

/-- The toroidal component on the envelope lies between `47/50` and `13/10`. -/
theorem toroidal_bounds {p : Plane} (reg : Region p) (t : ℝ) :
    47 / 50 ≤ cylBphi (p 0) t (p 1) ∧ cylBphi (p 0) t (p 1) ≤ 13 / 10 :=
  (polynomial_bounds t reg.1.1 reg.1.2 reg.2).toroidal (by linarith [reg.1.1])

/-- **Planar speed.** The field-line equation in the angle has speed at most `9/25` on the
envelope. -/
theorem planar_speed_le {p : Plane} (reg : Region p) (t : ℝ) :
    ‖euclideanFlow 0 1 t p‖ ≤ 9 / 25 :=
  (polynomial_bounds t reg.1.1 reg.1.2 reg.2).speed (by linarith [reg.1.1]) (by norm_num)
    (by norm_num)

/-- The same bound as the speed field of `FlowLabel.Tube`, on any time interval and any tube
inside the envelope. -/
theorem flowLabel_speed_le {W : ℝ → Set Plane} (hW : ∀ t, ∀ x ∈ W t, Region x) (a b : ℝ) :
    ∀ t ∈ Ioo a b, ∀ x ∈ W t, ‖euclideanFlow 0 1 t x‖ ≤ 9 / 25 :=
  fun t _ x hx => planar_speed_le (hW t x hx) t

set_option maxRecDepth 8000 in
/-- **Field strength from below** on the envelope. -/
theorem strength_ge {p : Plane} (reg : Region p) (t : ℝ) :
    47 / 50 ≤ ‖B (cylPoint (p 0) t (p 1))‖ :=
  (polynomial_bounds t reg.1.1 reg.1.2 reg.2).strength_ge (by linarith [reg.1.1]) (by norm_num)

set_option maxRecDepth 8000 in
/-- **Field strength from above** on the envelope. -/
theorem strength_le {p : Plane} (reg : Region p) (t : ℝ) :
    ‖B (cylPoint (p 0) t (p 1))‖ ≤ 141 / 100 := by
  have hR : 0 < p 0 := by linarith [reg.1.1]
  have sq := (polynomial_bounds t reg.1.1 reg.1.2 reg.2).strength_sq_le hR (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  refine sq.trans ?_
  have r2 : (7 / 8 : ℝ) ^ 2 ≤ p 0 ^ 2 := pow_le_pow_left₀ (by norm_num) reg.1.1 2
  have inv : (9 / 25 : ℝ) ^ 2 / p 0 ^ 2 ≤ (9 / 25) ^ 2 / (7 / 8) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) r2
  nlinarith

/-- **Sanity**: the upper strength bound is the toroidal bound times `√(1 + (M / R_min)²)`,
rounded up. -/
theorem speed_bound_fixture :
    ((13 / 10 : ℚ) ^ 2 * (1 + (9 / 25) ^ 2 / (7 / 8) ^ 2) ≤ (141 / 100) ^ 2) ∧
      ((14 / 10 : ℚ) ^ 2 < (13 / 10) ^ 2 * (1 + (9 / 25) ^ 2 / (7 / 8) ^ 2)) := by
  norm_num

end PlasmaLean.Design.DommaschkRegionFieldBounds
