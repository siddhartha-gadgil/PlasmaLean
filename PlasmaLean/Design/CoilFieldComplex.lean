/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilFieldComplexDist
public import PlasmaLean.Theory.KAM.TorusFieldAna

/-!
# The full coil field at complex points

Stage 1 of the coil-field KAM (`notes/theory/coil-kam-status.md`, gap 3). This file complexifies
the field `tfField + polyCoilFieldC` of the concrete coil set (closed TF rectangle plus the 192
straight segments of `filsC`) as a finite sum of complex segment fields `segFieldC`
(`Theory/Fields/BiotSavartComplex`).

* `coilFieldCC = tfFieldCC + polyFieldCC`, and `coilFieldCC_ofReal`: at real points of the tube
  `realTube w` (`w < 7/20`) it is the real field `tfField + polyCoilFieldC`.
* `coilNbhdP w η`: the open complex neighbourhood `|r(Re y) - 1| < w`, `|(Re y)₂| < w`,
  `|Im y| < η` (`isOpen_coilNbhdP`), with the concrete instance
  `coilNbhd = coilNbhdP (3/20) (3/20)`;
  it contains the complexified confinement tube `Ka aF` (`ofRealV_mem_coilNbhd`).
* **Distance** (from the kernel certificate `filsC_far` of `CoilFieldComplexDist`): for
  `w + d ≤ 7/20`, the real part of every `y ∈ coilNbhdP w η` is at distance `≥ d` from every coil
  segment (`polySeg_dist`), at distance `≥ 1 - w` from the TF axis segment (`axis_dist`) and at
  distance `≥ Λ - 2` from the three far TF segments (`far_dist`).
* **Holomorphy**: `coilFieldCC_differentiableOn` on `coilNbhdP w η` for `η < d`, `w + d ≤ 7/20`.
* **Sup bound**: `norm_coilFieldCC_le`: `‖coilFieldCC y‖ ≤ Mcoil w d η` on `coilNbhdP w η`, with
  the closed form
  `Mcoil w d η = 192 κ₀ (23/10) √((4 + 2w)² + η²)/(d² - η²)^{3/2}
     + (1 - η²/(1 - w)²)^{-3/2} (1/(1 - w) + η/(1 - w)²) + 3/1000`, `κ₀ = 90485364/2³²`
  (coil segments by `segFieldC_bound_sup`, `norm_polyTerm_le`; TF axis by the new long-segment bound
  `segFieldC_bound_line`; far TF segments `≤ 10⁻³` each). Concrete: `Mcoil_concrete_le`:
  `Mcoil (3/20) (1/5) (3/20) ≤ 17400`; `norm_coilFieldCC_apply_le` gives the component bounds.
* `segFieldC_bound_line` (general): if the line of the segment stays at distance `≥ ρ` from
  `Re y` (Gram form) and the segment at distance `≥ d > η ≥ |Im y|`, then
  `‖segFieldC κ p q y‖ ≤ 2|κ| (1 - η²/d²)^{-3/2} (1/ρ + η/ρ²)`, uniformly in the length.

* **Analytic field along a torus** (`coilAnaFieldP`, concrete `coilAnaField`): for torus
  coefficients `u₁, u₂ ∈ ℓ¹_{ρ'}` whose complexified torus neighbourhood
  (`torusMapC`, `|Im θ|, |Im ψ| < ρ'`, `|zᵢ| < d'`) lies in the coil neighbourhood, each Cartesian
  component of `coilFieldCC ∘ torusMapC` is an `AnaFieldAt r (M ((1+q)/(1-q))²) d`
  (`Theory/KAM/TorusFieldAna.anaFieldAt_torus`), with `M = Mcoil w δ η` resp. `17400`.

**Sanity.** `one_mem_coilNbhd` (the axis point `(1,0,0)` is in the neighbourhood, accepted fixture),
`vertex_not_mem_coilNbhd` (a coil vertex is not, rejected fixture), `realTube_zero` (degenerate
tube = the unit circle) and `segFieldC_bound_line_zero` (no current, zero bound).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilFieldComplex

open PlasmaLean.Fields PlasmaLean.Design.PolygonCoil PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.RationalStellarator.Confined
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Fields.BiotSavartComplex Set Complex
open scoped RealInnerProductSpace

/-! ## A long-segment bound -/

/-- `Re y - seg p q t = -((p - Re y) + t (q - p))`, in norm. -/
theorem norm_reV_sub_seg (p q : Space) (y : CVec) (t : ℝ) :
    ‖reV y - seg p q t‖ = ‖(p - reV y) + t • (q - p)‖ := by
  rw [← norm_neg]; congr 1; simp only [seg]; abel

/-- Splitting `p - y` into real and imaginary parts. -/
theorem ofRealV_sub_eq (p : Space) (y : CVec) :
    ofRealV p - y = ofRealV (p - reV y) + (-I) • ofRealV (imV y) := by
  ext i; apply Complex.ext <;> simp

/-- The complex cross product is additive in the first slot. -/
theorem crossC_add_left (u₁ u₂ w : CVec) : crossC (u₁ + u₂) w = crossC u₁ w + crossC u₂ w := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

/-- `‖a × v‖ = √(gram a v)`. -/
theorem norm_cross_eq_sqrt_gram (a v : Space) : ‖cross a v‖ = Real.sqrt (gram a v) := by
  rw [gram, ← norm_cross_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The cross-product factor of the complex segment field: `‖a × b‖ ≤ √G + η |q - p|`. -/
theorem norm_crossC_seg_le {p q : Space} {y : CVec} {η : ℝ} (hη : ‖imV y‖ ≤ η) :
    ‖crossC (ofRealV p - y) (ofRealV q - y)‖ ≤
      Real.sqrt (gram (p - reV y) (q - p)) + η * ‖q - p‖ := by
  rw [crossC_seg, ofRealV_sub_eq, crossC_add_left]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← ofRealV_cross, ← norm_cross_eq_sqrt_gram, ← hnorm_ofRealV]
    exact norm_le_hnorm _
  · refine (norm_le_hnorm _).trans ((hnorm_crossC_le _ _).trans ?_)
    rw [hnorm_smul, hnorm_ofRealV]
    simp only [norm_neg, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_right hη (norm_nonneg _)

/-- `|segG a v t| ≤ |v|/G` (Cauchy–Schwarz). -/
theorem abs_segG_le {a v : Space} (hG : 0 < gram a v) (t : ℝ) (hn : a + t • v ≠ 0) :
    |segG a v t| ≤ ‖v‖ / gram a v := by
  have hn0 : 0 < ‖a + t • v‖ := norm_pos_iff.mpr hn
  have hin : t * ‖v‖ ^ 2 + ⟪a, v⟫ = ⟪a + t • v, v⟫ := by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]; simp; ring
  unfold segG
  rw [hin, abs_div, abs_of_pos (mul_pos hG hn0), div_le_div_iff₀ (mul_pos hG hn0) hG]
  have := abs_real_inner_le_norm (a + t • v) v
  nlinarith

/-- `(k n²)^{-3/2} = k^{-3/2} (n³)⁻¹`. -/
theorem rpow_mul_sq_neg_three_halves {k n : ℝ} (hk : 0 ≤ k) (hn : 0 ≤ n) :
    (k * n ^ 2) ^ (-(3 / 2) : ℝ) = k ^ (-(3 / 2) : ℝ) * (n ^ 3)⁻¹ := by
  rw [Real.mul_rpow hk (by positivity)]
  congr 1
  rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn,
    show ((2 : ℕ) : ℝ) * (-(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn,
    Real.rpow_natCast]

/-- **Long-segment bound.** If `|Im y| ≤ η < d ≤ dist(Re y, segment)` and the *line* of the
segment stays at distance `≥ ρ > 0` from `Re y` (in Gram form `ρ²|v|² ≤ G`), then
`‖segFieldC κ p q y‖ ≤ 2|κ| (1 - η²/d²)^{-3/2} (1/ρ + η/ρ²)`, independently of the length. -/
theorem segFieldC_bound_line {κ d η ρ : ℝ} {p q : Space} {y : CVec} (hη : ‖imV y‖ ≤ η)
    (hηd : η < d) (hd : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg p q t‖) (hρ : 0 < ρ)
    (hG : ρ ^ 2 * ‖q - p‖ ^ 2 ≤ gram (p - reV y) (q - p)) (hv : q ≠ p) :
    ‖segFieldC κ p q y‖ ≤ 2 * |κ| * (1 - η ^ 2 / d ^ 2) ^ (-(3 / 2) : ℝ) * (1 / ρ + η / ρ ^ 2) := by
  set a := p - reV y
  set v := q - p
  set G := gram a v
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have hd0 : 0 < d := hη0.trans_lt hηd
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hG
  set k := 1 - η ^ 2 / d ^ 2
  have hk : 0 < k := by
    have : η ^ 2 / d ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; exact pow_lt_pow_left₀ hηd hη0 two_ne_zero
    simp only [k]; linarith
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖a + t • v‖ := fun t ht => by
    rw [← norm_reV_sub_seg]; exact hd t ht
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, a + t • v ≠ 0 := fun t ht =>
    norm_pos_iff.mp (hd0.trans_le (hn t ht))
  -- pointwise bound on the integrand
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ‖(segQ p q y t) ^ (-(3 / 2 : ℂ))‖ ≤
      k ^ (-(3 / 2) : ℝ) * (‖a + t • v‖ ^ 3)⁻¹ := by
    intro t ht
    set n := ‖a + t • v‖
    have hnd := hn t ht
    have hre : k * n ^ 2 ≤ (segQ p q y t).re := by
      rw [re_segQ, norm_reV_sub_seg]
      have h1 : ‖imV y‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hη 2
      have h2 : η ^ 2 ≤ η ^ 2 * n ^ 2 / d ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd0.le hnd 2) (sq_nonneg η)
      have e : k * n ^ 2 = n ^ 2 - η ^ 2 * n ^ 2 / d ^ 2 := by simp only [k]; ring
      rw [e]; linarith
    have hkn : 0 < k * n ^ 2 := mul_pos hk (pow_pos (hd0.trans_le hnd) 2)
    rw [norm_cpow_neg_three_halves, ← rpow_mul_sq_neg_three_halves hk.le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos hkn (hre.trans (re_le_norm_segQ p q y t)) (by norm_num)
  -- the integral
  have hcont : ContinuousOn (fun t : ℝ => k ^ (-(3 / 2) : ℝ) * (‖a + t • v‖ ^ 3)⁻¹)
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun t ht =>
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hne t ht)))
  have hI : ‖segIntC p q y‖ ≤ k ^ (-(3 / 2) : ℝ) * (segG a v 1 - segG a v 0) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1)
      (μ := MeasureTheory.volume)
      (f := fun t => (segQ p q y t) ^ (-(3 / 2 : ℂ))) zero_le_one
      (Filter.Eventually.of_forall fun t ht => hpt t (Ioc_subset_Icc_self ht))
      (hcont.intervalIntegrable)
    have hcont' : ContinuousOn (fun t : ℝ => (‖a + t • v‖ ^ 3)⁻¹) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact ContinuousOn.inv₀ (by fun_prop) fun t ht =>
        pow_ne_zero _ (norm_ne_zero_iff.mpr (hne t ht))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_segG hG0 t (hne t (by rwa [uIcc_of_le zero_le_one] at ht)))
      hcont'.intervalIntegrable] at h
    simpa [segIntC] using h
  have hS : segG a v 1 - segG a v 0 ≤ 2 * ‖v‖ / G := by
    have h1 := abs_segG_le hG0 1 (hne 1 ⟨zero_le_one, le_rfl⟩)
    have h0 := abs_segG_le hG0 0 (hne 0 ⟨le_rfl, zero_le_one⟩)
    have := (abs_le.1 h1).2; have := (abs_le.1 h0).1
    rw [mul_div_assoc]; linarith
  have hC := norm_crossC_seg_le (p := p) (q := q) hη
  -- assemble
  have hkp : 0 ≤ k ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hk.le _
  rw [segFieldC, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  set s := Real.sqrt G
  have hs2 : s ^ 2 = G := Real.sq_sqrt hG0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hG0
  have hsρ : ρ * ‖v‖ ≤ s := by
    have : (ρ * ‖v‖) ^ 2 ≤ s ^ 2 := by rw [hs2, mul_pow]; exact hG
    exact abs_le_of_sq_le_sq' this hs0.le |>.2 |> fun h => le_trans (le_abs_self _) (by
      simpa [abs_of_pos (mul_pos hρ hv0)] using (abs_le_of_sq_le_sq' this hs0.le).2)
  have hfin : 2 * ‖v‖ / G * (s + η * ‖v‖) ≤ 2 * (1 / ρ + η / ρ ^ 2) := by
    rw [← hs2]
    have e : 2 * ‖v‖ / s ^ 2 * (s + η * ‖v‖) = 2 * (‖v‖ / s) + 2 * η * (‖v‖ / s) ^ 2 := by
      field_simp
    have hq : ‖v‖ / s ≤ 1 / ρ := by
      rw [div_le_div_iff₀ hs0 hρ]; linarith
    have hq0 : 0 ≤ ‖v‖ / s := by positivity
    rw [e]
    have : (‖v‖ / s) ^ 2 ≤ (1 / ρ) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    have e2 : (1 / ρ) ^ 2 = 1 / ρ ^ 2 := by ring
    rw [e2] at this
    have : η * (‖v‖ / s) ^ 2 ≤ η * (1 / ρ ^ 2) := mul_le_mul_of_nonneg_left this hη0
    have e3 : η / ρ ^ 2 = η * (1 / ρ ^ 2) := by ring
    nlinarith
  calc |κ| * ‖segIntC p q y‖ * ‖crossC (ofRealV p - y) (ofRealV q - y)‖
      ≤ |κ| * (k ^ (-(3 / 2) : ℝ) * (2 * ‖v‖ / G)) * (s + η * ‖v‖) := by
        gcongr
        exact hI.trans (mul_le_mul_of_nonneg_left hS hkp)
    _ = |κ| * k ^ (-(3 / 2) : ℝ) * (2 * ‖v‖ / G * (s + η * ‖v‖)) := by ring
    _ ≤ |κ| * k ^ (-(3 / 2) : ℝ) * (2 * (1 / ρ + η / ρ ^ 2)) := by gcongr
    _ = _ := by ring

/-- Sanity: with no current the long-segment bound is `0`. -/
theorem segFieldC_bound_line_zero (d η ρ : ℝ) :
    2 * |(0 : ℝ)| * (1 - η ^ 2 / d ^ 2) ^ (-(3 / 2) : ℝ) * (1 / ρ + η / ρ ^ 2) = 0 := by simp

/-! ## The complexified coil field -/

/-- The complexified TF rectangle (`κ = μ₀I/4π = 1/2` on each side). -/
def tfFieldCC (y : CVec) : CVec :=
  segFieldC (1 / 2) P0 P1 y + segFieldC (1 / 2) P1 P2 y + segFieldC (1 / 2) P2 P3 y +
    segFieldC (1 / 2) P3 P0 y

/-- The complexified field of one coil segment record `(K, p, q)`. -/
def polyTerm (z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) : CVec → CVec :=
  segFieldC ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)

/-- The complexified field of the 192 coil segments of `filsC`. -/
def polyFieldCC (y : CVec) : CVec := ((allSegs filsC).map fun z => polyTerm z y).sum

/-- **The complexified full coil field** `tfFieldCC + polyFieldCC`. -/
def coilFieldCC (y : CVec) : CVec := tfFieldCC y + polyFieldCC y

/-- The open complex neighbourhood: `|r(Re y) - 1| < w`, `|(Re y)₂| < w`, `|Im y| < η`. -/
def coilNbhdP (w η : ℝ) : Set CVec :=
  {y | |Real.sqrt ((y 0).re ^ 2 + (y 1).re ^ 2) - 1| < w ∧ |(y 2).re| < w ∧ ‖imV y‖ < η}

/-- The concrete half-width `w = 3/20` of the real tube. -/
def coilW : ℝ := 3 / 20
/-- The concrete coil distance `d = 1/5` (`w + d = 7/20`). -/
def coilD : ℝ := 1 / 5
/-- The concrete imaginary width `η = 3/20 < d`. -/
def coilEta : ℝ := 3 / 20

/-- The concrete neighbourhood `coilNbhdP (3/20) (3/20)`. -/
def coilNbhd : Set CVec := coilNbhdP coilW coilEta

/-- `imV` is continuous. -/
theorem continuous_imV : Continuous imV :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun i => Complex.continuous_im.comp
    (continuous_apply i))

/-- The neighbourhood is open. -/
theorem isOpen_coilNbhdP (w η : ℝ) : IsOpen (coilNbhdP w η) := by
  have h0 : Continuous fun y : CVec => (y 0).re := Complex.continuous_re.comp (continuous_apply 0)
  have h1 : Continuous fun y : CVec => (y 1).re := Complex.continuous_re.comp (continuous_apply 1)
  have h2 : Continuous fun y : CVec => (y 2).re := Complex.continuous_re.comp (continuous_apply 2)
  have o1 : IsOpen {y : CVec | |Real.sqrt ((y 0).re ^ 2 + (y 1).re ^ 2) - 1| < w} :=
    isOpen_lt (continuous_abs.comp (((h0.pow 2).add (h1.pow 2)).sqrt.sub continuous_const))
      continuous_const
  have o2 : IsOpen {y : CVec | |(y 2).re| < w} := isOpen_lt (continuous_abs.comp h2)
    continuous_const
  have o3 : IsOpen {y : CVec | ‖imV y‖ < η} := isOpen_lt continuous_imV.norm continuous_const
  exact o1.inter (o2.inter o3)

/-- The concrete neighbourhood is open. -/
theorem isOpen_coilNbhd : IsOpen coilNbhd := isOpen_coilNbhdP _ _

/-- The imaginary part of a point of the neighbourhood is smaller than `η`. -/
theorem norm_imV_lt {w η : ℝ} {y : CVec} (hy : y ∈ coilNbhdP w η) : ‖imV y‖ < η := hy.2.2

/-- The real part of a point of the neighbourhood lies in the closed tube. -/
theorem reV_mem_realTube {w η : ℝ} {y : CVec} (hy : y ∈ coilNbhdP w η) : reV y ∈ realTube w :=
  ⟨by simpa using hy.1.le, by simp only [reV_apply]; exact hy.2.1.le⟩

/-- The complexified tube: real points of `realTube w'` with `w' < w` are in the neighbourhood
(`η > 0`). -/
theorem ofRealV_mem_coilNbhdP {w w' η : ℝ} (hw : w' < w) (hη : 0 < η) {x : Space}
    (hx : x ∈ realTube w') : ofRealV x ∈ coilNbhdP w η := by
  have him : imV (ofRealV x) = 0 := by ext i; simp
  refine ⟨?_, ?_, ?_⟩
  · simpa using hx.1.trans_lt hw
  · simpa using hx.2.trans_lt hw
  · rw [him, norm_zero]; exact hη

/-- **The complexified confinement tube `Ka aF` lies in `coilNbhd`.** -/
theorem ofRealV_mem_coilNbhd {x : Space} (hx : x ∈ Ka aF) : ofRealV x ∈ coilNbhd := by
  -- `Ka aF` is in fact inside the tube of half-width `0.111 < 3/20`
  obtain ⟨hs, hz⟩ := hx
  have ha : aF = 3420 / 32761 := rfl
  have hx' : x ∈ realTube (1 / 9) := by
    refine ⟨?_, hz.trans (by rw [ha]; norm_num)⟩
    simp only [sc, r2] at hs
    rw [abs_le] at hs ⊢
    have h0 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    have hsq := Real.sq_sqrt h0
    have hs0 := Real.sqrt_nonneg (x 0 ^ 2 + x 1 ^ 2)
    rw [ha] at hs
    constructor <;> nlinarith
  exact ofRealV_mem_coilNbhdP (by norm_num [coilW]) (by norm_num [coilEta]) hx'

/-! ## Distances -/

/-- A point of the tube has norm at most `1 + 2w`. -/
theorem norm_le_of_realTube {w : ℝ} {x : Space} (hx : x ∈ realTube w) : ‖x‖ ≤ 1 + 2 * w := by
  obtain ⟨hr, hz⟩ := hx
  have hw : 0 ≤ w := (abs_nonneg _).trans hz
  have hR := (abs_le.1 hr).2
  have h0 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
  have hsq := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (x 0 ^ 2 + x 1 ^ 2)
  have hz2 : x 2 ^ 2 ≤ w ^ 2 := by
    have := sq_abs (x 2); nlinarith [abs_nonneg (x 2)]
  have : ‖x‖ ^ 2 ≤ (1 + 2 * w) ^ 2 := by
    rw [norm_sq_space]; nlinarith
  exact (abs_le_of_sq_le_sq' this (by linarith)).2

/-- **Distance to the coil segments**: for `w + d ≤ 7/20`, `Re y` is at distance `≥ d` from
every point of every segment of `filsC`. -/
theorem polySeg_dist {w d η : ℝ} (hwd : w + d ≤ 7 / 20) {y : CVec} (hy : y ∈ coilNbhdP w η)
    {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)} (hz : z ∈ allSegs filsC) :
    ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg (ptR z.2.1) (ptR z.2.2) t‖ := fun t ht =>
  dist_of_far (A := 7 / 20) (by linarith) (by norm_num) (reV_mem_realTube hy)
    (by simpa using filsC_far hz ht)

/-- **Distance to the TF axis segment**: at least `1 - w`. -/
theorem axis_dist {w η : ℝ} {y : CVec} (hy : y ∈ coilNbhdP w η) :
    ∀ t ∈ Icc (0 : ℝ) 1, 1 - w ≤ ‖reV y - seg P0 P1 t‖ := fun t _ => by
  have h := abs_sqrt_sub_le (reV y) (seg P0 P1 t)
  have e0 : seg P0 P1 t 0 = 0 := by simp [seg_apply, P0, P1]
  have e1 : seg P0 P1 t 1 = 0 := by simp [seg_apply, P0, P1]
  rw [e0, e1] at h
  have := (abs_le.1 (reV_mem_realTube hy).1).1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_zero, sub_zero] at h
  have := le_abs_self (Real.sqrt (reV y 0 ^ 2 + reV y 1 ^ 2))
  linarith

/-- `‖v‖ ≤ |v₀| + |v₁| + |v₂|`. -/
theorem norm_le_sum_abs (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [norm_sq_space]
    nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2), abs_nonneg (v 0), abs_nonneg (v 1),
      abs_nonneg (v 2), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]
  exact (abs_le_of_sq_le_sq' this (by positivity)).2

/-- `Λ = 10⁶ > 0`. -/
theorem Λ_pos : (0 : ℝ) < Λ := by norm_num [Λ]

/-- **Distance to the far TF segments**: at least `Λ - 2` (for `w ≤ 1/2`). The three segments
are `P1 → P2` (height `Λ`), `P2 → P3` (`x₀ = Λ`) and `P3 → P0` (height `-Λ`). -/
theorem far_dist {w η : ℝ} (hw : w ≤ 1 / 2) {y : CVec} (hy : y ∈ coilNbhdP w η) :
    (∀ t ∈ Icc (0 : ℝ) 1, Λ - 2 ≤ ‖reV y - seg P1 P2 t‖) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, Λ - 2 ≤ ‖reV y - seg P2 P3 t‖) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, Λ - 2 ≤ ‖reV y - seg P3 P0 t‖) := by
  have hx := reV_mem_realTube hy
  have hn := norm_le_of_realTube hx
  have hΛ := Λ_pos
  have hc : ∀ (c : Space) (i : Fin 3), Λ ≤ |c i| → Λ - 2 ≤ ‖reV y - c‖ := fun c i hci => by
    have h1 := abs_coord_le (reV y - c) i
    have h2 := abs_coord_le (reV y) i
    simp only [PiLp.sub_apply] at h1
    have : |c i| - |reV y i| ≤ |reV y i - c i| := by
      have := abs_sub_abs_le_abs_sub (c i) (reV y i); rwa [abs_sub_comm (c i)] at this
    linarith
  refine ⟨fun t _ => hc _ 2 ?_, fun t _ => hc _ 0 ?_, fun t _ => hc _ 2 ?_⟩
  · simp [seg_apply, P1, P2, abs_of_pos hΛ]
  · simp [seg_apply, P2, P3, abs_of_pos hΛ]
  · simp [seg_apply, P3, P0, abs_of_pos hΛ]

/-! ## Holomorphy -/

/-- Finite sums of holomorphic maps are holomorphic. -/
theorem differentiableOn_list_sum {ι : Type*} (f : ι → CVec → CVec) (s : Set CVec) :
    ∀ l : List ι, (∀ i ∈ l, DifferentiableOn ℂ (f i) s) →
      DifferentiableOn ℂ (fun y => (l.map fun i => f i y).sum) s
  | [], _ => by simp
  | i :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (differentiableOn_list_sum f s l fun j hj => h j (by simp [hj]))

/-- A segment field is holomorphic wherever `|Im y| <` the distance to the segment. -/
theorem segFieldC_differentiableOn_of_dist {κ d : ℝ} {p q : Space} {s : Set CVec}
    (h : ∀ y ∈ s, ‖imV y‖ < d ∧ ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖reV y - seg p q t‖) :
    DifferentiableOn ℂ (segFieldC κ p q) s :=
  (segFieldC_differentiableOn_boundRegion κ p q).mono fun y hy t ht =>
    (h y hy).1.trans_le ((h y hy).2 t ht)

/-- **Holomorphy of the complexified coil field** on `coilNbhdP w η` for `0 ≤ w`, `0 ≤ η < d`,
`w + d ≤ 7/20`. -/
theorem coilFieldCC_differentiableOn {w d η : ℝ} (hw : 0 ≤ w) (hη : 0 ≤ η) (hηd : η < d)
    (hwd : w + d ≤ 7 / 20) : DifferentiableOn ℂ coilFieldCC (coilNbhdP w η) := by
  have hw1 : w ≤ 1 / 2 := by linarith
  have hΛ : (3 : ℝ) ≤ Λ := by norm_num [Λ]
  have hax : DifferentiableOn ℂ (segFieldC (1 / 2) P0 P1) (coilNbhdP w η) :=
    segFieldC_differentiableOn_of_dist fun y hy => ⟨by linarith [norm_imV_lt hy], axis_dist hy⟩
  have h12 : DifferentiableOn ℂ (segFieldC (1 / 2) P1 P2) (coilNbhdP w η) :=
    segFieldC_differentiableOn_of_dist fun y hy =>
      ⟨by linarith [norm_imV_lt hy], (far_dist hw1 hy).1⟩
  have h23 : DifferentiableOn ℂ (segFieldC (1 / 2) P2 P3) (coilNbhdP w η) :=
    segFieldC_differentiableOn_of_dist fun y hy =>
      ⟨by linarith [norm_imV_lt hy], (far_dist hw1 hy).2.1⟩
  have h30 : DifferentiableOn ℂ (segFieldC (1 / 2) P3 P0) (coilNbhdP w η) :=
    segFieldC_differentiableOn_of_dist fun y hy =>
      ⟨by linarith [norm_imV_lt hy], (far_dist hw1 hy).2.2⟩
  have hP : DifferentiableOn ℂ polyFieldCC (coilNbhdP w η) :=
    differentiableOn_list_sum polyTerm _ (allSegs filsC) fun z hz =>
      segFieldC_differentiableOn_of_dist fun y hy =>
        ⟨(norm_imV_lt hy).trans hηd, polySeg_dist hwd hy hz⟩
  have hT : DifferentiableOn ℂ tfFieldCC (coilNbhdP w η) := ((hax.add h12).add h23).add h30
  have e : coilFieldCC = tfFieldCC + polyFieldCC := rfl
  rw [e]
  exact hT.add hP

/-- The concrete neighbourhood: holomorphy on `coilNbhd`. -/
theorem coilFieldCC_differentiableOn_coilNbhd : DifferentiableOn ℂ coilFieldCC coilNbhd :=
  coilFieldCC_differentiableOn (d := coilD) (by norm_num [coilW]) (by norm_num [coilEta])
    (by norm_num [coilEta, coilD]) (by norm_num [coilW, coilD])

/-! ## Agreement with the real field -/

/-- `ofRealV` is additive. -/
theorem ofRealV_add (x z : Space) : ofRealV (x + z) = ofRealV x + ofRealV z := by
  ext i; simp

/-- `ofRealV` commutes with finite sums. -/
theorem ofRealV_list_sum {ι : Type*} (f : ι → Space) :
    ∀ l : List ι, ofRealV ((l.map f).sum) = (l.map fun i => ofRealV (f i)).sum
  | [] => by ext i; simp
  | i :: l => by simp only [List.map_cons, List.sum_cons, ofRealV_add, ofRealV_list_sum f l]

/-- Points of the tube `realTube w` (`w < 7/20`) are not on the coil. -/
theorem not_coilPt_of_realTube {w : ℝ} (hw : w < 7 / 20) {y : Space} (hy : y ∈ realTube w) :
    ¬ coilPt filsC y := by
  rintro ⟨z, hz, t, ht, hyz⟩
  have h := dist_of_far (d := 7 / 20 - w) (A := 7 / 20) (by linarith) (by norm_num) hy
    (filsC_far hz ht)
  rw [← hyz, sub_self, norm_zero] at h
  linarith

/-- The TF side `segField` is the closed form with `κ = 1/2`. -/
theorem segField_eq_half (p q x : Space) : segField p q x = segClosed (1 / 2) p q x := by
  unfold segField
  rw [segField_eq_closed]
  congr 1
  field_simp
  ring

/-- **Agreement at real points**: on the tube `realTube w` (`w < 7/20`) the complexified field
is the real coil field `tfField + polyCoilFieldC`. -/
theorem coilFieldCC_ofReal {w : ℝ} (hw : w < 7 / 20) {y : Space} (hy : y ∈ realTube w) :
    coilFieldCC (ofRealV y) = ofRealV (tfField y + polyCoilFieldC y) := by
  rw [polyCoilFieldC_eq (not_coilPt_of_realTube hw hy), ofRealV_add]
  unfold coilFieldCC
  congr 1
  · unfold tfFieldCC tfField
    simp only [segFieldC_ofReal, segField_eq_half, ofRealV_add]
  · unfold polyFieldCC Bseg
    rw [ofRealV_list_sum]
    refine congrArg List.sum (List.map_congr_left fun z _ => ?_)
    exact segFieldC_ofReal _ _ _ _

/-! ## The sup bound -/

/-- `m^{3/2} = m √m`. -/
theorem rpow_three_halves {m : ℝ} (hm : 0 ≤ m) : m ^ (3 / 2 : ℝ) = m * Real.sqrt m := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h; simp
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
      Real.sqrt_eq_rpow]

/-- Norm of a finite sum, termwise bounded. -/
theorem norm_list_sum_le {ι : Type*} (f : ι → CVec) {T : ℝ} :
    ∀ l : List ι, (∀ i ∈ l, ‖f i‖ ≤ T) → ‖(l.map f).sum‖ ≤ l.length * T
  | [], _ => by simp
  | i :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h i (by simp)
    have h2 := norm_list_sum_le f l fun j hj => h j (by simp [hj])
    calc ‖f i + (l.map f).sum‖ ≤ ‖f i‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ T + l.length * T := add_le_add h1 h2
      _ = ((l.length + 1 : ℕ) : ℝ) * T := by push_cast; ring

/-- The coil set has `192` segments. -/
theorem length_allSegs_filsC : (allSegs filsC).length = 192 := by decide +kernel

/-- The current scale `κ₀ = 90485364/2³²` of the coil segments. -/
def κ0 : ℝ := 90485364 / S32

/-- The per-segment bound for the coil segments. -/
def Tpoly (w d η : ℝ) : ℝ :=
  κ0 * (23 / 10) * Real.sqrt ((4 + 2 * w) ^ 2 + η ^ 2) / (d ^ 2 - η ^ 2) ^ (3 / 2 : ℝ)

/-- The bound for the TF axis segment. -/
def Taxis (w η : ℝ) : ℝ :=
  (1 - η ^ 2 / (1 - w) ^ 2) ^ (-(3 / 2) : ℝ) * (1 / (1 - w) + η / (1 - w) ^ 2)

/-- **The explicit sup bound** `192 Tpoly + Taxis + 3/1000`. -/
def Mcoil (w d η : ℝ) : ℝ := 192 * Tpoly w d η + Taxis w η + 3 / 1000

/-- Bound for one coil segment on the neighbourhood. -/
theorem norm_polyTerm_le {w d η : ℝ} (hw : 0 ≤ w) (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    {y : CVec} (hy : y ∈ coilNbhdP w η) {z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)}
    (hz : z ∈ allSegs filsC) : ‖polyTerm z y‖ ≤ Tpoly w d η := by
  have hηy := norm_imV_lt hy
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hηy.le
  have hD : ‖reV y - ptR z.2.1‖ ≤ 4 + 2 * w := by
    have h1 := norm_le_of_realTube (reV_mem_realTube hy)
    have h2 := filsC_norm_le hz
    exact (norm_sub_le _ _).trans (by linarith)
  have h := segFieldC_bound_sup (κ := (z.1 : ℝ) / S32) (hηy.trans hηd)
    (polySeg_dist hwd hy hz) hD
  refine h.trans ?_
  set e := ‖imV y‖
  have he0 : 0 ≤ e := norm_nonneg _
  have hm : 0 < d ^ 2 - η ^ 2 := by nlinarith
  have hden : (d ^ 2 - η ^ 2) ^ (3 / 2 : ℝ) ≤ (d ^ 2 - e ^ 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hm.le (by nlinarith) (by norm_num)
  have hnum : |(z.1 : ℝ) / S32| * ‖ptR z.2.2 - ptR z.2.1‖ * Real.sqrt ((4 + 2 * w) ^ 2 + e ^ 2) ≤
      κ0 * (23 / 10) * Real.sqrt ((4 + 2 * w) ^ 2 + η ^ 2) := by
    have hs : Real.sqrt ((4 + 2 * w) ^ 2 + e ^ 2) ≤ Real.sqrt ((4 + 2 * w) ^ 2 + η ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hk := filsC_kappa hz
    have hl := filsC_len_le hz
    have hk0 : 0 ≤ κ0 := by unfold κ0; have := S32_pos; positivity
    calc _ ≤ κ0 * (23 / 10) * Real.sqrt ((4 + 2 * w) ^ 2 + e ^ 2) := by
          gcongr
          · exact hk
      _ ≤ _ := by gcongr
  unfold Tpoly
  exact div_le_div₀ (by unfold κ0; have := S32_pos; positivity) hnum
    (Real.rpow_pos_of_pos hm _) hden

/-- Real inner product in coordinates. -/
theorem inner_space (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- Bound for the TF axis segment on the neighbourhood. -/
theorem norm_axis_le {w d η : ℝ} (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    {y : CVec} (hy : y ∈ coilNbhdP w η) : ‖segFieldC (1 / 2) P0 P1 y‖ ≤ Taxis w η := by
  have hρ : 0 < 1 - w := by linarith [(norm_nonneg (imV y)).trans (norm_imV_lt hy).le]
  have hx := reV_mem_realTube hy
  set x := reV y
  have hr : 1 - w ≤ Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by linarith [(abs_le.1 hx.1).1]
  have hr2 : (1 - w) ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by
    have := pow_le_pow_left₀ hρ.le hr 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hG : (1 - w) ^ 2 * ‖P1 - P0‖ ^ 2 ≤ gram (P0 - x) (P1 - P0) := by
    unfold gram
    rw [norm_sq_space, norm_sq_space, inner_space]
    simp only [PiLp.sub_apply, P0, P1]
    simp
    nlinarith [sq_nonneg (Λ : ℝ)]
  have hv : P1 ≠ P0 := by
    intro h
    have := congrArg (fun v : Space => v 2) h
    simp [P0, P1, Λ] at this
    norm_num at this
  have h := segFieldC_bound_line (κ := 1 / 2) (norm_imV_lt hy).le (by linarith) (axis_dist hy) hρ
    hG hv
  refine h.trans (le_of_eq ?_)
  unfold Taxis
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

/-- The arithmetic of a far TF side: `|1/2| L √(D² + e²)/((Λ - 2)² - e²)^{3/2} ≤ 10⁻³` for
`L ≤ 2Λ`, `D ≤ 3Λ`, `e ≤ 1`. -/
theorem far_arith {L D e : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 2 * Λ) (hD0 : 0 ≤ D) (hD : D ≤ 3 * Λ)
    (he0 : 0 ≤ e) (he : e ≤ 1) :
    |(1 / 2 : ℝ)| * L * Real.sqrt (D ^ 2 + e ^ 2) / ((Λ - 2) ^ 2 - e ^ 2) ^ (3 / 2 : ℝ) ≤
      1 / 1000 := by
  have hΛ : Λ = 10 ^ 6 := rfl
  set m := (Λ - 2) ^ 2 - e ^ 2
  have hm : 9 * 10 ^ 11 ≤ m := by simp only [m, hΛ]; nlinarith
  have hsm : 9 * 10 ^ 5 ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsD : Real.sqrt (D ^ 2 + e ^ 2) ≤ 4 * 10 ^ 6 := by
    rw [Real.sqrt_le_left (by norm_num)]
    rw [hΛ] at hD; nlinarith
  rw [rpow_three_halves (by linarith), div_le_iff₀ (by positivity)]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hΛ] at hL
  have h1 : 1 / 2 * L * Real.sqrt (D ^ 2 + e ^ 2) ≤ 1 / 2 * (2 * 10 ^ 6) * (4 * 10 ^ 6) := by
    gcongr
  have h2 : (9 * 10 ^ 11) * (9 * 10 ^ 5) ≤ m * Real.sqrt m := by gcongr
  nlinarith

/-- Bound for the three far TF sides on the neighbourhood (`w ≤ 1/2`, `η ≤ 1`). -/
theorem norm_far_le {w η : ℝ} (hw : w ≤ 1 / 2) (hη : η ≤ 1) {y : CVec}
    (hy : y ∈ coilNbhdP w η) :
    ‖segFieldC (1 / 2) P1 P2 y‖ ≤ 1 / 1000 ∧ ‖segFieldC (1 / 2) P2 P3 y‖ ≤ 1 / 1000 ∧
      ‖segFieldC (1 / 2) P3 P0 y‖ ≤ 1 / 1000 := by
  have hΛ : (10 : ℝ) ≤ Λ := by norm_num [Λ]
  have hx := norm_le_of_realTube (reV_mem_realTube hy)
  have hw0 : 0 ≤ w := (abs_nonneg _).trans (reV_mem_realTube hy).2
  have he := norm_imV_lt hy
  have he0 := norm_nonneg (imV y)
  have hed : ‖imV y‖ < Λ - 2 := by linarith
  obtain ⟨d12, d23, d30⟩ := far_dist hw hy
  have key : ∀ p q : Space, ‖p‖ ≤ 2 * Λ → ‖q - p‖ ≤ 2 * Λ →
      (∀ t ∈ Icc (0 : ℝ) 1, Λ - 2 ≤ ‖reV y - seg p q t‖) →
      ‖segFieldC (1 / 2) p q y‖ ≤ 1 / 1000 := fun p q hp hqp hd => by
    have hD : ‖reV y - p‖ ≤ 3 * Λ := (norm_sub_le _ _).trans (by linarith)
    exact (segFieldC_bound_sup hed hd hD).trans
      (far_arith (norm_nonneg _) hqp (by linarith) le_rfl he0 (by linarith))
  have hΛ0 : 0 ≤ Λ := by linarith
  have n1 : ‖P1‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by simp [P1, abs_of_nonneg hΛ0]; linarith)
  have n2 : ‖P2‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by simp [P2, abs_of_nonneg hΛ0]; linarith)
  have n3 : ‖P3‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by simp [P3, abs_of_nonneg hΛ0]; linarith)
  have l12 : ‖P2 - P1‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by
    simp [P1, P2, abs_of_nonneg hΛ0]; linarith)
  have l23 : ‖P3 - P2‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by
    simp [P2, P3, abs_le]; constructor <;> linarith)
  have l30 : ‖P0 - P3‖ ≤ 2 * Λ := (norm_le_sum_abs _).trans (by
    simp [P3, P0, abs_of_nonneg hΛ0]; linarith)
  exact ⟨key _ _ n1 l12 d12, key _ _ n2 l23 d23, key _ _ n3 l30 d30⟩

/-- **The sup bound**: for `0 ≤ w`, `0 ≤ η < d`, `w + d ≤ 7/20`,
`‖coilFieldCC y‖ ≤ Mcoil w d η` on `coilNbhdP w η`. -/
theorem norm_coilFieldCC_le {w d η : ℝ} (hw : 0 ≤ w) (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    {y : CVec} (hy : y ∈ coilNbhdP w η) : ‖coilFieldCC y‖ ≤ Mcoil w d η := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (norm_imV_lt hy).le
  have hη1 : η ≤ 1 := by linarith
  obtain ⟨f12, f23, f30⟩ := norm_far_le (by linarith) hη1 hy
  have hax := norm_axis_le hηd hwd hy
  have hP : ‖polyFieldCC y‖ ≤ 192 * Tpoly w d η := by
    have h := norm_list_sum_le (fun z => polyTerm z y) (allSegs filsC)
      fun z hz => norm_polyTerm_le hw hηd hwd hy hz
    rwa [length_allSegs_filsC, Nat.cast_ofNat] at h
  unfold coilFieldCC tfFieldCC Mcoil
  calc ‖segFieldC (1 / 2) P0 P1 y + segFieldC (1 / 2) P1 P2 y + segFieldC (1 / 2) P2 P3 y +
        segFieldC (1 / 2) P3 P0 y + polyFieldCC y‖
      ≤ ‖segFieldC (1 / 2) P0 P1 y‖ + ‖segFieldC (1 / 2) P1 P2 y‖ +
          ‖segFieldC (1 / 2) P2 P3 y‖ + ‖segFieldC (1 / 2) P3 P0 y‖ + ‖polyFieldCC y‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_add_le _ _
    _ ≤ 192 * Tpoly w d η + Taxis w η + 3 / 1000 := by linarith

/-- Componentwise bound: `|(coilFieldCC y)ᵢ| ≤ Mcoil w d η`. -/
theorem norm_coilFieldCC_apply_le {w d η : ℝ} (hw : 0 ≤ w) (hηd : η < d)
    (hwd : w + d ≤ 7 / 20) {y : CVec} (hy : y ∈ coilNbhdP w η) (i : Fin 3) :
    ‖coilFieldCC y i‖ ≤ Mcoil w d η :=
  (norm_le_pi_norm (coilFieldCC y) i).trans (norm_coilFieldCC_le hw hηd hwd hy)

/-- **Concrete constant**: `Mcoil (3/20) (1/5) (3/20) ≤ 17400`. -/
theorem Mcoil_concrete_le : Mcoil coilW coilD coilEta ≤ 17400 := by
  unfold Mcoil Tpoly Taxis κ0 coilW coilD coilEta
  have hS : S32 = 4294967296 := rfl
  -- the coil part
  have hs1 : Real.sqrt ((4 + 2 * (3 / 20 : ℝ)) ^ 2 + (3 / 20) ^ 2) ≤ 431 / 100 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hm : ((1 / 5 : ℝ) ^ 2 - (3 / 20) ^ 2) = 7 / 400 := by norm_num
  have hs2 : (1322 / 10000 : ℝ) ≤ Real.sqrt (7 / 400) := Real.le_sqrt_of_sq_le (by norm_num)
  have hden : (7 / 400 : ℝ) * (1322 / 10000) ≤ ((1 / 5 : ℝ) ^ 2 - (3 / 20) ^ 2) ^ (3 / 2 : ℝ) := by
    rw [hm, rpow_three_halves (by norm_num)]; gcongr
  have hP : 90485364 / S32 * (23 / 10) * Real.sqrt ((4 + 2 * (3 / 20 : ℝ)) ^ 2 + (3 / 20) ^ 2) /
      ((1 / 5 : ℝ) ^ 2 - (3 / 20) ^ 2) ^ (3 / 2 : ℝ) ≤
      90485364 / 4294967296 * (23 / 10) * (431 / 100) / ((7 / 400) * (1322 / 10000)) := by
    rw [hS]; gcongr
  -- the axis part
  have hk : (1 - (3 / 20 : ℝ) ^ 2 / (1 - 3 / 20) ^ 2) = 301 / 289 * (289 / 301) *
      (1 - (3 / 20 : ℝ) ^ 2 / (1 - 3 / 20) ^ 2) := by norm_num
  have hk0 : (1 - (3 / 20 : ℝ) ^ 2 / (1 - 3 / 20) ^ 2) = 280 / 289 := by norm_num
  have hsk : (98 / 100 : ℝ) ≤ Real.sqrt (280 / 289) := Real.le_sqrt_of_sq_le (by norm_num)
  have hA : (1 - (3 / 20 : ℝ) ^ 2 / (1 - 3 / 20) ^ 2) ^ (-(3 / 2) : ℝ) ≤
      ((280 / 289) * (98 / 100))⁻¹ := by
    rw [hk0, Real.rpow_neg (by norm_num), rpow_three_halves (by norm_num)]
    gcongr
  have hA0 : 0 ≤ (1 / (1 - 3 / 20) + (3 / 20 : ℝ) / (1 - 3 / 20) ^ 2) := by norm_num
  have hAx := mul_le_mul_of_nonneg_right hA hA0
  norm_num at hP hAx ⊢
  linarith

/-- The concrete sup bound on `coilNbhd`: `‖coilFieldCC y‖ ≤ 17400`. -/
theorem norm_coilFieldCC_le_concrete {y : CVec} (hy : y ∈ coilNbhd) : ‖coilFieldCC y‖ ≤ 17400 :=
  (norm_coilFieldCC_le (d := coilD) (by norm_num [coilW]) (by norm_num [coilEta, coilD])
    (by norm_num [coilW, coilD]) hy).trans Mcoil_concrete_le

/-! ## Sanity -/

/-- The degenerate tube of half-width `0` is the unit circle in the plane `x₂ = 0`. -/
theorem realTube_zero : realTube 0 = {x : Space | Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = 1 ∧ x 2 = 0} := by
  ext x; simp [realTube, sub_eq_zero]

/-- Accepted fixture: the axis point `(1, 0, 0)` is in the concrete neighbourhood. -/
theorem one_mem_coilNbhd : ((![1, 0, 0] : Fin 3 → ℂ)) ∈ coilNbhd := by
  have him : imV ![1, 0, 0] = 0 := by ext i; fin_cases i <;> simp [imV]
  refine ⟨?_, ?_, ?_⟩
  · simp [coilW]
  · simp [coilW]
  · rw [him, norm_zero]; norm_num [coilEta]

/-- Rejected fixture: a coil vertex is not in the neighbourhood. -/
theorem vertex_not_mem_coilNbhd :
    ofRealV (ptR (7925370926, 828655364, 1977389707)) ∉ coilNbhd := by
  intro h
  have hx := reV_mem_realTube h
  have hre : reV (ofRealV (ptR (7925370926, 828655364, 1977389707))) =
      ptR (7925370926, 828655364, 1977389707) := by ext i; simp
  rw [hre] at hx
  have := dist_of_far (d := 1 / 5) (A := 7 / 20) (by norm_num [coilW]) (by norm_num) hx
    far_vertex_fixture
  rw [sub_self, norm_zero] at this
  norm_num at this

/-! ## Analytic fields along a torus inside the coil neighbourhood -/

open PlasmaLean.Theory.KAM PlasmaLean.Theory.KAM.PaleyWiener
  PlasmaLean.Theory.KAM.AnalyticComposition PlasmaLean.Theory.KAM.FourierSumHolo
  PlasmaLean.Theory.KAM.TorusFieldAna

/-- A Cartesian component of the complex coil field is holomorphic on `coilNbhdP w η`. -/
theorem coilFieldCC_apply_differentiableOn {w δ η : ℝ} (hw : 0 ≤ w) (hη : 0 ≤ η) (hηδ : η < δ)
    (hwδ : w + δ ≤ 7 / 20) (i : Fin 3) :
    DifferentiableOn ℂ (fun y => coilFieldCC y i) (coilNbhdP w η) :=
  fun y hy => (differentiableWithinAt_pi.1 (coilFieldCC_differentiableOn hw hη hηδ hwδ y hy)) i

/-- **The coil field along a complexified torus is an analytic field** (general parameters).
Let `w + δ ≤ 7/20`, `0 ≤ η < δ`, and let the complexified torus neighbourhood
`|Im θ|, |Im ψ| < ρ'`, `|zᵢ| < d'` of `torusMapC u₁ u₂` (`u₁, u₂ ∈ ℓ¹_{ρ'}`, the `R`- and
`Z`-coefficients of the torus) lie in `coilNbhdP w η`. Then for `0 ≤ r < ρ < ρ'`, `0 < d < d'`,
the `i`-th Cartesian component of `coilFieldCC(cylC (K₁ + z₁, ψ, K₂ + z₂))` is an
`AnaFieldAt r (Mcoil w δ η · ((1+q)/(1-q))²) d`, `q = e^{-(ρ-r)}`. -/
def coilAnaFieldP {w δ η : ℝ} (hw : 0 ≤ w) (hη : 0 ≤ η) (hηδ : η < δ) (hwδ : w + δ ≤ 7 / 20)
    (i : Fin 3) {u₁ u₂ : ℤ × ℤ → ℂ} {ρ' ρ r d d' : ℝ}
    (hu₁ : InWeighted ρ' u₁) (hu₂ : InWeighted ρ' u₂)
    (hmap : ∀ θ ψ z₁ z₂ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → ‖z₁‖ < d' → ‖z₂‖ < d' →
      torusMapC u₁ u₂ θ ψ z₁ z₂ ∈ coilNbhdP w η)
    (hr0 : 0 ≤ r) (hr : r < ρ) (hρ : ρ < ρ') (hd : 0 < d) (hdd : d < d') :
    AnaFieldAt r (Mcoil w δ η * geoZ (Real.exp (-(ρ - r))) ^ 2) d
      (fun θ ψ z₁ z₂ => coilFieldCC (torusMapC u₁ u₂ θ ψ z₁ z₂) i) :=
  anaFieldAt_torus (F := fun y => coilFieldCC y i)
    (coilFieldCC_apply_differentiableOn hw hη hηδ hwδ i)
    (fun _ hy => norm_coilFieldCC_apply_le hw hηδ hwδ hy i) hu₁ hu₂ hmap hr0 hr hρ hd hdd

/-- **The coil field along a complexified torus is an analytic field** (concrete
neighbourhood `coilNbhd`, `w = η = 3/20`, sup bound `17400`). -/
def coilAnaField (i : Fin 3) {u₁ u₂ : ℤ × ℤ → ℂ} {ρ' ρ r d d' : ℝ}
    (hu₁ : InWeighted ρ' u₁) (hu₂ : InWeighted ρ' u₂)
    (hmap : ∀ θ ψ z₁ z₂ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → ‖z₁‖ < d' → ‖z₂‖ < d' →
      torusMapC u₁ u₂ θ ψ z₁ z₂ ∈ coilNbhd)
    (hr0 : 0 ≤ r) (hr : r < ρ) (hρ : ρ < ρ') (hd : 0 < d) (hdd : d < d') :
    AnaFieldAt r (17400 * geoZ (Real.exp (-(ρ - r))) ^ 2) d
      (fun θ ψ z₁ z₂ => coilFieldCC (torusMapC u₁ u₂ θ ψ z₁ z₂) i) :=
  anaFieldAt_torus (F := fun y => coilFieldCC y i)
    (coilFieldCC_apply_differentiableOn (δ := coilD) (by norm_num [coilW])
      (by norm_num [coilEta]) (by norm_num [coilEta, coilD]) (by norm_num [coilW, coilD]) i)
    (fun _ hy => (norm_le_pi_norm _ i).trans (norm_coilFieldCC_le_concrete hy)) hu₁ hu₂ hmap
    hr0 hr hρ hd hdd

end PlasmaLean.Design.CoilFieldComplex
