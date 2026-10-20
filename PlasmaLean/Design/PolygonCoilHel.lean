/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorCoilsTransfer
public import PlasmaLean.Design.PolygonCoilInterp

/-!
# The helical target field in polar form and its derivative bounds on the frontier faces

`hel = field (1/4) - ∇φ = (1/16)∇H` (`Design/RationalStellaratorCoilsTransfer`) at the point
`(ρ cos φ, ρ sin φ, ζ)` is a trigonometric polynomial in `φ` (`hel_polar`):

`hel = (A cos φ + B sin φ + G cos 3φ + D sin 3φ, -A sin φ + B cos φ + G sin 3φ - D cos 3φ,
        E sin 2φ + F cos 2φ)`

with `A = (ρ² - 1)/(8ρ)`, `B = ζ(3 - ρ²)/(8ρ)`, `G = (ρ² - 1 + 4ζ²)/(8ρ³)`,
`D = ζ(5 - 3ρ² - 4ζ²)/(8ρ³)`, `E = (6ρ² - ρ⁴ - 5 + 12ζ²)/(16ρ²)`, `F = -ζ/(2ρ²)` (verified
symbolically: the difference is `(cos²φ + sin²φ - 1)` times a rational function).

From it, for every unit vector `n`:
* `hel_phi_interp`: along `φ` (fixed `ρ`, `ζ`) the second derivative of `⟨n, hel⟩` is at most
  `|A| + |B| + 9|G| + 9|D| + 4|E| + 4|F|`;
* `hel_zeta_interp`: along `ζ` (fixed `ρ`, `φ`) at most `1/ρ³ + 3|ζ|/ρ³ + 3/(2ρ²)`;
* `hel_rho_interp`: along `ρ` (fixed `ζ`, `φ`) at most the sum of the absolute second
  derivatives of the six coefficients;

and, through `lin_interp_bound`, the corresponding linear-interpolation bounds. The per-face
constants used by the checker (`helH`) are proved in `helFace_phi`, `helFace_w`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  Set Real
open scoped RealInnerProductSpace

/-! ## The polar formula -/

/-- Coefficient `A = (ρ² - 1)/(8ρ)`. -/
@[expose] def cA (ρ : ℝ) : ℝ := (ρ ^ 2 - 1) / (8 * ρ)
/-- Coefficient `B = ζ(3 - ρ²)/(8ρ)`. -/
@[expose] def cB (ρ ζ : ℝ) : ℝ := ζ * (3 - ρ ^ 2) / (8 * ρ)
/-- Coefficient `G = (ρ² - 1 + 4ζ²)/(8ρ³)`. -/
@[expose] def cG (ρ ζ : ℝ) : ℝ := (ρ ^ 2 - 1 + 4 * ζ ^ 2) / (8 * ρ ^ 3)
/-- Coefficient `D = ζ(5 - 3ρ² - 4ζ²)/(8ρ³)`. -/
@[expose] def cD (ρ ζ : ℝ) : ℝ := ζ * (5 - 3 * ρ ^ 2 - 4 * ζ ^ 2) / (8 * ρ ^ 3)
/-- Coefficient `E = (6ρ² - ρ⁴ - 5 + 12ζ²)/(16ρ²)`. -/
@[expose] def cE (ρ ζ : ℝ) : ℝ := (6 * ρ ^ 2 - ρ ^ 4 - 5 + 12 * ζ ^ 2) / (16 * ρ ^ 2)
/-- Coefficient `F = -ζ/(2ρ²)`. -/
@[expose] def cF (ρ ζ : ℝ) : ℝ := -ζ / (2 * ρ ^ 2)

/-- The point `(ρ cos φ, ρ sin φ, ζ)`. -/
@[expose] def polarPt (ρ ζ φ : ℝ) : Space := WithLp.toLp 2 ![ρ * cos φ, ρ * sin φ, ζ]

/-- The polar formula of `hel`. -/
@[expose] def helP (ρ ζ φ : ℝ) : Space :=
  WithLp.toLp 2 ![cA ρ * cos φ + cB ρ ζ * sin φ + cG ρ ζ * cos (3 * φ) + cD ρ ζ * sin (3 * φ),
    -cA ρ * sin φ + cB ρ ζ * cos φ + cG ρ ζ * sin (3 * φ) - cD ρ ζ * cos (3 * φ),
    cE ρ ζ * sin (2 * φ) + cF ρ ζ * cos (2 * φ)]

/-- `r₂ = ρ²` at a polar point. -/
theorem r2_polarPt (ρ ζ φ : ℝ) : r2 (polarPt ρ ζ φ) = ρ ^ 2 := by
  simp only [r2, polarPt]
  simp
  nlinarith [sin_sq_add_cos_sq φ]

/-- `hel = (1/16) ∇H`. -/
theorem hel_eq (y : Space) : hel y = (1 / 16 : ℝ) • gradH y := by
  simp only [hel, field, add_sub_cancel_left]
  norm_num

/-- **The polar formula of the helical field.** -/
theorem hel_polar {ρ : ℝ} (hρ : 0 < ρ) (ζ φ : ℝ) : hel (polarPt ρ ζ φ) = helP ρ ζ φ := by
  have hr := r2_polarPt ρ ζ φ
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq φ
  have c3 : cos (3 * φ) = cos φ ^ 3 - 3 * cos φ * sin φ ^ 2 := by
    rw [cos_three_mul]; linear_combination 3 * cos φ * hcs
  have s3 : sin (3 * φ) = 3 * cos φ ^ 2 * sin φ - sin φ ^ 3 := by
    rw [sin_three_mul]; linear_combination (-3) * sin φ * hcs
  have c2 : cos (2 * φ) = cos φ ^ 2 - sin φ ^ 2 := by rw [cos_two_mul]; linear_combination hcs
  have s2 : sin (2 * φ) = 2 * sin φ * cos φ := sin_two_mul φ
  have hρ0 : ρ ≠ 0 := hρ.ne'
  rw [hel_eq]
  ext i
  fin_cases i
  · simp only [gradH, G, Hd, H0, Hnum, Aq, Bq, Xd, Yp, cv, winv]
    rw [hr]
    simp [polarPt, helP, cA, cB, cG, cD, c3, s3]
    linear_combination (norm := skip) ((cos φ * ρ ^ 2 + 4 * cos φ * ζ ^ 2 - cos φ -
      3 * ρ ^ 2 * sin φ * ζ - 4 * sin φ * ζ ^ 3 + 5 * sin φ * ζ) / (8 * ρ ^ 3)) * hcs
    field_simp
    ring
  · simp only [gradH, G, Hd, H1, Hnum, Aq, Bq, Xd, Yp, cv, winv]
    rw [hr]
    simp [polarPt, helP, cA, cB, cG, cD, c3, s3]
    linear_combination (norm := skip) ((-3 * cos φ * ρ ^ 2 * ζ - 4 * cos φ * ζ ^ 3 +
      5 * cos φ * ζ - ρ ^ 2 * sin φ - 4 * sin φ * ζ ^ 2 + sin φ) / (8 * ρ ^ 3)) * hcs
    field_simp
    ring
  · simp only [gradH, G, Hd, H2, cv, winv, Xd, Yp, Bq]
    rw [hr]
    simp [polarPt, helP, cE, cF, c2, s2]
    field_simp
    ring


/-! ## Inner products with the polar formula -/

/-- `⟨n, v⟩` in coordinates. -/
theorem inner_coords (n v : Space) : ⟪n, v⟫ = n 0 * v 0 + n 1 * v 1 + n 2 * v 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  ring

/-- Coordinates of a unit-ball vector: `n₀² + n₁² + n₂² ≤ 1`. -/
theorem coords_sq_le {n : Space} (hn : ‖n‖ ≤ 1) : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 ≤ 1 := by
  have h : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [sq_abs]
  nlinarith [norm_nonneg n]

/-- Pairing bound: `|a c + b s| ≤ 1` if `a² + b² ≤ 1` and `c² + s² = 1`. -/
theorem pair_le {a b c s : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    |a * c + b * s| ≤ 1 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a * s - b * c), sq_nonneg (a * c + b * s - 1),
    sq_nonneg (a * c + b * s + 1)]

/-- The generic quadratic-form bound: for `‖n‖ ≤ 1`,
`|n₀(α c₁ + β s₁ + γ c₃ + δ s₃) + n₁(-α s₁ + β c₁ + γ s₃ - δ c₃) + n₂(ε s₂ + ϑ c₂)|
 ≤ |α| + |β| + |γ| + |δ| + |ε| + |ϑ|` for unit pairs `(c_k, s_k)`. -/
theorem polar_comb_le {n : Space} (hn : ‖n‖ ≤ 1) {c1 s1 c3 s3 c2 s2 : ℝ}
    (h1 : c1 ^ 2 + s1 ^ 2 = 1) (h3 : c3 ^ 2 + s3 ^ 2 = 1) (h2 : c2 ^ 2 + s2 ^ 2 = 1)
    (α β γ δ ε ϑ : ℝ) :
    |n 0 * (α * c1 + β * s1 + γ * c3 + δ * s3) + n 1 * (-α * s1 + β * c1 + γ * s3 - δ * c3) +
      n 2 * (ε * s2 + ϑ * c2)| ≤ |α| + |β| + |γ| + |δ| + |ε| + |ϑ| := by
  have hn3 := coords_sq_le hn
  have hab : n 0 ^ 2 + n 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (n 2)]
  have hn2 : |n 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  have p1 := pair_le hab h1
  have p2 := pair_le (a := n 0) (b := -n 1) (by nlinarith) (show s1 ^ 2 + c1 ^ 2 = 1 by linarith)
  have p3 := pair_le hab h3
  have p4 := pair_le (a := n 0) (b := -n 1) (by nlinarith) (show s3 ^ 2 + c3 ^ 2 = 1 by linarith)
  have p5 : |ε * s2 + ϑ * c2| ≤ |ε| + |ϑ| := by
    have hs2 : |s2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
    have hc2 : |c2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
    calc |ε * s2 + ϑ * c2| ≤ |ε * s2| + |ϑ * c2| := abs_add_le _ _
      _ = |ε| * |s2| + |ϑ| * |c2| := by rw [abs_mul, abs_mul]
      _ ≤ |ε| * 1 + |ϑ| * 1 := by gcongr
      _ = |ε| + |ϑ| := by ring
  have e : n 0 * (α * c1 + β * s1 + γ * c3 + δ * s3) + n 1 * (-α * s1 + β * c1 + γ * s3 - δ * c3) +
      n 2 * (ε * s2 + ϑ * c2) = α * (n 0 * c1 + -n 1 * s1) + β * (n 0 * s1 + n 1 * c1) +
      γ * (n 0 * c3 + n 1 * s3) + δ * (n 0 * s3 + -n 1 * c3) + n 2 * (ε * s2 + ϑ * c2) := by ring
  have p2' : |n 0 * s1 + n 1 * c1| ≤ 1 := by
    have := pair_le (a := n 0) (b := n 1) hab (show s1 ^ 2 + c1 ^ 2 = 1 by linarith); exact this
  have p4' : |n 0 * s3 + -n 1 * c3| ≤ 1 := by
    have := pair_le (a := n 0) (b := -n 1) (by nlinarith) (show s3 ^ 2 + c3 ^ 2 = 1 by linarith)
    exact this
  have p1' : |n 0 * c1 + -n 1 * s1| ≤ 1 := by
    have := pair_le (a := n 0) (b := -n 1) (by nlinarith) h1; exact this
  rw [e]
  calc _ ≤ |α * (n 0 * c1 + -n 1 * s1)| + |β * (n 0 * s1 + n 1 * c1)| +
        |γ * (n 0 * c3 + n 1 * s3)| + |δ * (n 0 * s3 + -n 1 * c3)| + |n 2 * (ε * s2 + ϑ * c2)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ |α| * 1 + |β| * 1 + |γ| * 1 + |δ| * 1 + 1 * (|ε| + |ϑ|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

/-- `⟨n, helP⟩` in the form of `polar_comb_le`. -/
theorem inner_helP (n : Space) (ρ ζ φ : ℝ) :
    ⟪n, helP ρ ζ φ⟫ = n 0 * (cA ρ * cos φ + cB ρ ζ * sin φ + cG ρ ζ * cos (3 * φ) +
        cD ρ ζ * sin (3 * φ)) + n 1 * (-cA ρ * sin φ + cB ρ ζ * cos φ + cG ρ ζ * sin (3 * φ) -
        cD ρ ζ * cos (3 * φ)) + n 2 * (cE ρ ζ * sin (2 * φ) + cF ρ ζ * cos (2 * φ)) := by
  rw [inner_coords]; simp [helP]

/-! ## Interpolation along `φ` -/

/-- The trigonometric pair `α cos kφ + β sin kφ`. -/
@[expose] def tp (α β k φ : ℝ) : ℝ := α * cos (k * φ) + β * sin (k * φ)

/-- Derivative of the trigonometric pair. -/
theorem hasDerivAt_tp (α β k φ : ℝ) : HasDerivAt (tp α β k) (tp (k * β) (-(k * α)) k φ) φ := by
  have hk : HasDerivAt (fun x : ℝ => k * x) (k * 1) φ := (hasDerivAt_id' φ).const_mul k
  have := (hk.cos.const_mul α).add (hk.sin.const_mul β)
  unfold tp
  convert this using 1; ring

/-- `⟨n, helP ρ ζ ·⟩` as a combination of trigonometric pairs. -/
theorem inner_helP_tp (n : Space) (ρ ζ φ : ℝ) :
    ⟪n, helP ρ ζ φ⟫ = n 0 * (tp (cA ρ) (cB ρ ζ) 1 φ + tp (cG ρ ζ) (cD ρ ζ) 3 φ) +
      n 1 * (tp (cB ρ ζ) (-cA ρ) 1 φ + tp (-cD ρ ζ) (cG ρ ζ) 3 φ) +
      n 2 * tp (cF ρ ζ) (cE ρ ζ) 2 φ := by
  rw [inner_helP]; simp only [tp, one_mul]; ring

/-- **Interpolation of `⟨n, hel⟩` along `φ`** (fixed `ρ > 0`, `ζ`), for `‖n‖ ≤ 1`. -/
theorem hel_phi_interp {n : Space} (hn : ‖n‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (ζ : ℝ) {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) :
    |(b - a) * ⟪n, hel (polarPt ρ ζ x)⟫ - ((b - x) * ⟪n, hel (polarPt ρ ζ a)⟫ +
        (x - a) * ⟪n, hel (polarPt ρ ζ b)⟫)| ≤
      (|cA ρ| + |cB ρ ζ| + 9 * |cG ρ ζ| + 9 * |cD ρ ζ| + 4 * |cE ρ ζ| + 4 * |cF ρ ζ|) *
        (x - a) * (b - x) * (b - a) / 2 := by
  simp only [hel_polar hρ, inner_helP_tp]
  set A := cA ρ; set B := cB ρ ζ; set G := cG ρ ζ; set D := cD ρ ζ; set E := cE ρ ζ
  set F := cF ρ ζ
  let g : ℝ → ℝ := fun φ => n 0 * (tp A B 1 φ + tp G D 3 φ) + n 1 * (tp B (-A) 1 φ + tp (-D) G 3 φ)
    + n 2 * tp F E 2 φ
  let g1 : ℝ → ℝ := fun φ => n 0 * (tp (1 * B) (-(1 * A)) 1 φ + tp (3 * D) (-(3 * G)) 3 φ) +
    n 1 * (tp (1 * -A) (-(1 * B)) 1 φ + tp (3 * G) (-(3 * -D)) 3 φ) + n 2 * tp (2 * E) (-(2 * F)) 2
        φ
  let g2 : ℝ → ℝ := fun φ =>
    n 0 * (tp (1 * -(1 * A)) (-(1 * (1 * B))) 1 φ + tp (3 * -(3 * G)) (-(3 * (3 * D))) 3 φ) +
    n 1 * (tp (1 * -(1 * B)) (-(1 * (1 * -A))) 1 φ + tp (3 * -(3 * -D)) (-(3 * (3 * G))) 3 φ) +
    n 2 * tp (2 * -(2 * F)) (-(2 * (2 * E))) 2 φ
  have hd1 : ∀ y ∈ Icc a b, HasDerivAt g (g1 y) y := fun y _ =>
    (((hasDerivAt_tp A B 1 y).add (hasDerivAt_tp G D 3 y)).const_mul (n 0)).add
      (((hasDerivAt_tp B (-A) 1 y).add (hasDerivAt_tp (-D) G 3 y)).const_mul (n 1)) |>.add
      ((hasDerivAt_tp F E 2 y).const_mul (n 2))
  have hd2 : ∀ y ∈ Icc a b, HasDerivAt g1 (g2 y) y := fun y _ =>
    (((hasDerivAt_tp _ _ 1 y).add (hasDerivAt_tp _ _ 3 y)).const_mul (n 0)).add
      (((hasDerivAt_tp _ _ 1 y).add (hasDerivAt_tp _ _ 3 y)).const_mul (n 1)) |>.add
      ((hasDerivAt_tp _ _ 2 y).const_mul (n 2))
  have hM : ∀ y ∈ Icc a b, |g2 y| ≤ |A| + |B| + 9 * |G| + 9 * |D| + 4 * |E| + 4 * |F| := by
    intro y _
    have h := polar_comb_le hn (c1 := cos y) (s1 := sin y) (c3 := cos (3 * y)) (s3 := sin (3 * y))
      (c2 := cos (2 * y)) (s2 := sin (2 * y)) (by rw [add_comm]; exact sin_sq_add_cos_sq y)
      (by rw [add_comm]; exact sin_sq_add_cos_sq _) (by rw [add_comm]; exact sin_sq_add_cos_sq _)
      (-A) (-B) (-9 * G) (-9 * D) (-4 * E) (-4 * F)
    have e : g2 y = n 0 * (-A * cos y + -B * sin y + -9 * G * cos (3 * y) + -9 * D * sin (3 * y)) +
        n 1 * (-(-A) * sin y + -B * cos y + -9 * G * sin (3 * y) - -9 * D * cos (3 * y)) +
        n 2 * (-4 * E * sin (2 * y) + -4 * F * cos (2 * y)) := by
      simp only [g2, tp, one_mul]; ring
    rw [e]
    refine h.trans (le_of_eq ?_)
    simp only [abs_neg, abs_mul]; norm_num
  exact lin_interp_bound hab hx hd1 hd2 hM

/-! ## Interpolation along `ζ` (cylinder faces) -/

/-- Linear interpolation of a cubic polynomial. -/
theorem cubic_interp {k0 k1 k2 k3 a b x M : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b)
    (hM : ∀ y ∈ Icc a b, |2 * k2 + 6 * k3 * y| ≤ M) :
    |(b - a) * (k0 + k1 * x + k2 * x ^ 2 + k3 * x ^ 3) -
        ((b - x) * (k0 + k1 * a + k2 * a ^ 2 + k3 * a ^ 3) +
          (x - a) * (k0 + k1 * b + k2 * b ^ 2 + k3 * b ^ 3))| ≤
      M * (x - a) * (b - x) * (b - a) / 2 := by
  refine lin_interp_bound (g := fun y => k0 + k1 * y + k2 * y ^ 2 + k3 * y ^ 3)
    (g' := fun y => k1 + 2 * k2 * y + 3 * k3 * y ^ 2) (g'' := fun y => 2 * k2 + 6 * k3 * y)
    hab hx (fun y _ => ?_) (fun y _ => ?_) hM
  · have := ((((hasDerivAt_id' y).const_mul k1).const_add k0).add
      (((hasDerivAt_id' y).pow 2).const_mul k2)).add (((hasDerivAt_id' y).pow 3).const_mul k3)
    convert this using 1; simp; ring
  · have := (((hasDerivAt_id' y).const_mul (2 * k2)).const_add k1).add
      (((hasDerivAt_id' y).pow 2).const_mul (3 * k3))
    convert this using 1; simp; ring

/-- **Interpolation of `⟨n, hel⟩` along `ζ`** (fixed `ρ > 0`, `φ`), for `‖n‖ ≤ 1`. -/
theorem hel_zeta_interp {n : Space} (hn : ‖n‖ ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) {a b x Z : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (hZ : ∀ y ∈ Icc a b, |y| ≤ Z) :
    |(b - a) * ⟪n, hel (polarPt ρ x φ)⟫ - ((b - x) * ⟪n, hel (polarPt ρ a φ)⟫ +
        (x - a) * ⟪n, hel (polarPt ρ b φ)⟫)| ≤
      (1 / ρ ^ 3 + 3 * Z / ρ ^ 3 + 3 / (2 * ρ ^ 2)) * (x - a) * (b - x) * (b - a) / 2 := by
  simp only [hel_polar hρ]
  set c1 := cos φ; set s1 := sin φ; set c3 := cos (3 * φ); set s3 := sin (3 * φ)
  set c2 := cos (2 * φ); set s2 := sin (2 * φ)
  set k0 := n 0 * ((ρ ^ 2 - 1) / (8 * ρ) * c1 + (ρ ^ 2 - 1) / (8 * ρ ^ 3) * c3) +
    n 1 * (-((ρ ^ 2 - 1) / (8 * ρ)) * s1 + (ρ ^ 2 - 1) / (8 * ρ ^ 3) * s3) +
    n 2 * ((6 * ρ ^ 2 - ρ ^ 4 - 5) / (16 * ρ ^ 2) * s2)
  set k1 := n 0 * ((3 - ρ ^ 2) / (8 * ρ) * s1 + (5 - 3 * ρ ^ 2) / (8 * ρ ^ 3) * s3) +
    n 1 * ((3 - ρ ^ 2) / (8 * ρ) * c1 - (5 - 3 * ρ ^ 2) / (8 * ρ ^ 3) * c3) +
    n 2 * (-1 / (2 * ρ ^ 2) * c2)
  set k2 := n 0 * (1 / (2 * ρ ^ 3) * c3) + n 1 * (1 / (2 * ρ ^ 3) * s3) + n 2 * (3 / (4 * ρ ^ 2) *
      s2)
  set k3 := n 0 * (-1 / (2 * ρ ^ 3) * s3) - n 1 * (-1 / (2 * ρ ^ 3) * c3)
  have hpoly : ∀ ζ, ⟪n, helP ρ ζ φ⟫ = k0 + k1 * ζ + k2 * ζ ^ 2 + k3 * ζ ^ 3 := by
    intro ζ
    rw [inner_helP]
    simp only [cA, cB, cG, cD, cE, cF, k0, k1, k2, k3, c1, s1, c2, s2, c3, s3]
    field_simp
    ring
  simp only [hpoly]
  refine cubic_interp hab hx fun y hy => ?_
  have h := polar_comb_le hn (c1 := c1) (s1 := s1) (c3 := c3) (s3 := s3) (c2 := c2) (s2 := s2)
    (by rw [add_comm]; exact sin_sq_add_cos_sq φ) (by rw [add_comm]; exact sin_sq_add_cos_sq _)
    (by rw [add_comm]; exact sin_sq_add_cos_sq _)
    0 0 (1 / ρ ^ 3) (-3 * y / ρ ^ 3) (3 / (2 * ρ ^ 2)) 0
  have e : 2 * k2 + 6 * k3 * y = n 0 * (0 * c1 + 0 * s1 + 1 / ρ ^ 3 * c3 + -3 * y / ρ ^ 3 * s3) +
      n 1 * (-0 * s1 + 0 * c1 + 1 / ρ ^ 3 * s3 - -3 * y / ρ ^ 3 * c3) +
      n 2 * (3 / (2 * ρ ^ 2) * s2 + 0 * c2) := by
    simp only [k2, k3]; field_simp; ring
  rw [e]
  refine h.trans ?_
  have hy' := hZ y hy
  have : |-3 * y / ρ ^ 3| ≤ 3 * Z / ρ ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ρ ^ 3)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num; linarith
  rw [abs_of_pos (by positivity : (0:ℝ) < 1 / ρ ^ 3),
    abs_of_pos (by positivity : (0:ℝ) < 3 / (2 * ρ ^ 2))]
  simp only [abs_zero]
  linarith

/-! ## Interpolation along `ρ` (plane faces) -/

/-- Derivative of `ρ ↦ (ρ^(j+1))⁻¹`. -/
theorem hasDerivAt_inv_pow' {ρ : ℝ} (hρ : ρ ≠ 0) (j : ℕ) :
    HasDerivAt (fun r : ℝ => (r ^ (j + 1))⁻¹) (-((j : ℝ) + 1) * (ρ ^ (j + 2))⁻¹) ρ := by
  have h := ((hasDerivAt_id' ρ).pow (j + 1)).inv (pow_ne_zero _ hρ)
  convert h using 1
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- A Laurent polynomial `l₂ρ² + l₁ρ + l₀ + l₋₁/ρ + l₋₂/ρ² + l₋₃/ρ³`. -/
@[expose] def laur (l2 l1 l0 lm1 lm2 lm3 ρ : ℝ) : ℝ :=
  l2 * ρ ^ 2 + l1 * ρ + l0 + lm1 * (ρ ^ 1)⁻¹ + lm2 * (ρ ^ 2)⁻¹ + lm3 * (ρ ^ 3)⁻¹

/-- Linear interpolation of a Laurent polynomial on `[a, b] ⊂ (0, ∞)`. -/
theorem laur_interp {l2 l1 l0 lm1 lm2 lm3 a b x M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Icc a b)
    (hM : ∀ y ∈ Icc a b, |2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ +
      12 * lm3 * (y ^ 5)⁻¹| ≤ M) :
    |(b - a) * laur l2 l1 l0 lm1 lm2 lm3 x - ((b - x) * laur l2 l1 l0 lm1 lm2 lm3 a +
        (x - a) * laur l2 l1 l0 lm1 lm2 lm3 b)| ≤ M * (x - a) * (b - x) * (b - a) / 2 := by
  refine lin_interp_bound (g := laur l2 l1 l0 lm1 lm2 lm3)
    (g' := fun y => 2 * l2 * y + l1 - lm1 * (y ^ 2)⁻¹ - 2 * lm2 * (y ^ 3)⁻¹ - 3 * lm3 * (y ^ 4)⁻¹)
    (g'' := fun y => 2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ + 12 * lm3 * (y ^ 5)⁻¹)
    hab hx (fun y hy => ?_) (fun y hy => ?_) hM
  · have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have := (((((hasDerivAt_id' y).pow 2).const_mul l2).add ((hasDerivAt_id' y).const_mul
        l1)).add_const
      l0 |>.add ((hasDerivAt_inv_pow' hy0 0).const_mul lm1)).add
      ((hasDerivAt_inv_pow' hy0 1).const_mul lm2) |>.add ((hasDerivAt_inv_pow' hy0 2).const_mul lm3)
    unfold laur
    convert this using 1; push_cast; ring
  · have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have := ((((hasDerivAt_id' y).const_mul (2 * l2)).add_const l1).sub
      ((hasDerivAt_inv_pow' hy0 1).const_mul lm1)).sub
      ((hasDerivAt_inv_pow' hy0 2).const_mul (2 * lm2)) |>.sub
      ((hasDerivAt_inv_pow' hy0 3).const_mul (3 * lm3))
    convert this using 1; push_cast; ring

/-- **Interpolation of `⟨n, hel⟩` along `ρ`** (fixed `ζ`, `φ`), for `‖n‖ ≤ 1` and
`[a, b] ⊂ (0, ∞)`; the bound `M` must dominate the sum of the absolute second derivatives of the
six coefficients. -/
theorem hel_rho_interp {n : Space} (hn : ‖n‖ ≤ 1) (ζ φ : ℝ) {a b x M : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hx : x ∈ Icc a b)
    (hM : ∀ y ∈ Icc a b, |1 / (4 * y ^ 3)| + |3 * ζ / (4 * y ^ 3)| +
      |1 / (4 * y ^ 3) + 3 * (4 * ζ ^ 2 - 1) / (2 * y ^ 5)| +
      |3 * ζ * (5 - 4 * ζ ^ 2) / (2 * y ^ 5) - 3 * ζ / (4 * y ^ 3)| +
      |-1 / 8 + 3 * (12 * ζ ^ 2 - 5) / (8 * y ^ 4)| + |3 * ζ / y ^ 4| ≤ M) :
    |(b - a) * ⟪n, hel (polarPt x ζ φ)⟫ - ((b - x) * ⟪n, hel (polarPt a ζ φ)⟫ +
        (x - a) * ⟪n, hel (polarPt b ζ φ)⟫)| ≤ M * (x - a) * (b - x) * (b - a) / 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  rw [hel_polar hxpos, hel_polar ha, hel_polar hbpos]
  set c1 := cos φ; set s1 := sin φ; set c3 := cos (3 * φ); set s3 := sin (3 * φ)
  set c2 := cos (2 * φ); set s2 := sin (2 * φ)
  set l2 := n 2 * (-1 / 16 * s2)
  set l1 := n 0 * (c1 / 8 - ζ * s1 / 8) + n 1 * (-(s1 / 8) - ζ * c1 / 8)
  set l0 := n 2 * (3 / 8 * s2)
  set lm1 := n 0 * (-(c1 / 8) + 3 * ζ * s1 / 8 + c3 / 8 - 3 * ζ * s3 / 8) +
    n 1 * (s1 / 8 + 3 * ζ * c1 / 8 + s3 / 8 + 3 * ζ * c3 / 8)
  set lm2 := n 2 * ((12 * ζ ^ 2 - 5) / 16 * s2 - ζ / 2 * c2)
  set lm3 := n 0 * ((4 * ζ ^ 2 - 1) / 8 * c3 + ζ * (5 - 4 * ζ ^ 2) / 8 * s3) +
    n 1 * ((4 * ζ ^ 2 - 1) / 8 * s3 - ζ * (5 - 4 * ζ ^ 2) / 8 * c3)
  have hl : ∀ r, 0 < r → ⟪n, helP r ζ φ⟫ = laur l2 l1 l0 lm1 lm2 lm3 r := by
    intro r hr
    rw [inner_helP]
    simp only [cA, cB, cG, cD, cE, cF, laur, l2, l1, l0, lm1, lm2, lm3, c1, s1, c2, s2, c3, s3]
    field_simp
    ring
  rw [hl x hxpos, hl a ha, hl b hbpos]
  refine laur_interp ha hab hx fun y hy => ?_
  have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
  have h := polar_comb_le hn (c1 := c1) (s1 := s1) (c3 := c3) (s3 := s3) (c2 := c2) (s2 := s2)
    (by rw [add_comm]; exact sin_sq_add_cos_sq φ) (by rw [add_comm]; exact sin_sq_add_cos_sq _)
    (by rw [add_comm]; exact sin_sq_add_cos_sq _)
    (-1 / (4 * y ^ 3)) (3 * ζ / (4 * y ^ 3)) (1 / (4 * y ^ 3) + 3 * (4 * ζ ^ 2 - 1) / (2 * y ^ 5))
    (3 * ζ * (5 - 4 * ζ ^ 2) / (2 * y ^ 5) - 3 * ζ / (4 * y ^ 3))
    (-1 / 8 + 3 * (12 * ζ ^ 2 - 5) / (8 * y ^ 4)) (-3 * ζ / y ^ 4)
  have e : 2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ + 12 * lm3 * (y ^ 5)⁻¹ =
      n 0 * (-1 / (4 * y ^ 3) * c1 + 3 * ζ / (4 * y ^ 3) * s1 +
        (1 / (4 * y ^ 3) + 3 * (4 * ζ ^ 2 - 1) / (2 * y ^ 5)) * c3 +
        (3 * ζ * (5 - 4 * ζ ^ 2) / (2 * y ^ 5) - 3 * ζ / (4 * y ^ 3)) * s3) +
      n 1 * (-(-1 / (4 * y ^ 3)) * s1 + 3 * ζ / (4 * y ^ 3) * c1 +
        (1 / (4 * y ^ 3) + 3 * (4 * ζ ^ 2 - 1) / (2 * y ^ 5)) * s3 -
        (3 * ζ * (5 - 4 * ζ ^ 2) / (2 * y ^ 5) - 3 * ζ / (4 * y ^ 3)) * c3) +
      n 2 * ((-1 / 8 + 3 * (12 * ζ ^ 2 - 5) / (8 * y ^ 4)) * s2 + -3 * ζ / y ^ 4 * c2) := by
    simp only [l2, lm1, lm2, lm3]; field_simp; ring
  rw [e]
  refine h.trans ?_
  have := hM y hy
  rw [show |-1 / (4 * y ^ 3)| = |1 / (4 * y ^ 3)| by rw [neg_div, abs_neg],
    show |-3 * ζ / y ^ 4| = |3 * ζ / y ^ 4| by rw [neg_mul, neg_div, abs_neg]]
  exact this

/-! ## Per-face constants -/

/-- The half-width `a = 3420/32761` of the frontier tube (`1 ± 2a = (199/181)², (161/181)²`). -/
@[expose] def aF : ℝ := 3420 / 32761

/-- Crude bound along `φ` on a cylinder face (`ρ > 0` fixed, `|ζ| ≤ Z`). -/
theorem hel_phi_cyl {ρ ζ Z : ℝ} (hρ : 0 < ρ) (hζ : |ζ| ≤ Z) :
    |cA ρ| + |cB ρ ζ| + 9 * |cG ρ ζ| + 9 * |cD ρ ζ| + 4 * |cE ρ ζ| + 4 * |cF ρ ζ| ≤
      |ρ ^ 2 - 1| / (8 * ρ) + Z * |3 - ρ ^ 2| / (8 * ρ) + 9 * ((|ρ ^ 2 - 1| + 4 * Z ^ 2) / (8 * ρ ^
          3)) +
      9 * (Z * (|5 - 3 * ρ ^ 2| + 4 * Z ^ 2) / (8 * ρ ^ 3)) +
      4 * ((|6 * ρ ^ 2 - ρ ^ 4 - 5| + 12 * Z ^ 2) / (16 * ρ ^ 2)) + 4 * (Z / (2 * ρ ^ 2)) := by
  have hz0 := abs_nonneg ζ
  have hZ0 : 0 ≤ Z := hz0.trans hζ
  have hz2 : ζ ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; gcongr
  have h4 : |4 * ζ ^ 2| ≤ 4 * Z ^ 2 := by rw [abs_of_nonneg (by positivity)]; linarith
  have h12 : |12 * ζ ^ 2| ≤ 12 * Z ^ 2 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hA : |cA ρ| = |ρ ^ 2 - 1| / (8 * ρ) := by
    unfold cA; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ)]
  have hB : |cB ρ ζ| ≤ Z * |3 - ρ ^ 2| / (8 * ρ) := by
    unfold cB; rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ)]; gcongr
  have hG : |cG ρ ζ| ≤ (|ρ ^ 2 - 1| + 4 * Z ^ 2) / (8 * ρ ^ 3) := by
    unfold cG; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ ^ 3)]; gcongr
    exact (abs_add_le _ _).trans (by linarith)
  have hD : |cD ρ ζ| ≤ Z * (|5 - 3 * ρ ^ 2| + 4 * Z ^ 2) / (8 * ρ ^ 3) := by
    unfold cD; rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ ^ 3)]; gcongr
    exact (abs_sub _ _).trans (by linarith)
  have hE : |cE ρ ζ| ≤ (|6 * ρ ^ 2 - ρ ^ 4 - 5| + 12 * Z ^ 2) / (16 * ρ ^ 2) := by
    unfold cE; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 16 * ρ ^ 2)]; gcongr
    exact (abs_add_le _ _).trans (by linarith)
  have hF : |cF ρ ζ| ≤ Z / (2 * ρ ^ 2) := by
    unfold cF; rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * ρ ^ 2)]; gcongr
  rw [hA]; linarith

/-- Face `0` (`ρ = 199/181`): `H_φ = 19/25`. -/
theorem hel_phi_face0 {ζ : ℝ} (hζ : |ζ| ≤ aF) :
    |cA (199 / 181)| + |cB (199 / 181) ζ| + 9 * |cG (199 / 181) ζ| + 9 * |cD (199 / 181) ζ| +
      4 * |cE (199 / 181) ζ| + 4 * |cF (199 / 181) ζ| ≤ 19 / 25 := by
  refine (hel_phi_cyl (by norm_num) hζ).trans ?_
  unfold aF
  rw [abs_of_pos (by norm_num : (0:ℝ) < (199 / 181) ^ 2 - 1),
    abs_of_pos (by norm_num : (0:ℝ) < 3 - (199 / 181) ^ 2),
    abs_of_pos (by norm_num : (0:ℝ) < 5 - 3 * (199 / 181) ^ 2),
    abs_of_pos (by norm_num : (0:ℝ) < 6 * (199 / 181) ^ 2 - (199 / 181) ^ 4 - 5)]
  norm_num

/-- Face `1` (`ρ = 161/181`): `H_φ = 3/2`. -/
theorem hel_phi_face1 {ζ : ℝ} (hζ : |ζ| ≤ aF) :
    |cA (161 / 181)| + |cB (161 / 181) ζ| + 9 * |cG (161 / 181) ζ| + 9 * |cD (161 / 181) ζ| +
      4 * |cE (161 / 181) ζ| + 4 * |cF (161 / 181) ζ| ≤ 3 / 2 := by
  refine (hel_phi_cyl (by norm_num) hζ).trans ?_
  unfold aF
  rw [abs_of_neg (by norm_num : (161 / 181 : ℝ) ^ 2 - 1 < 0),
    abs_of_pos (by norm_num : (0:ℝ) < 3 - (161 / 181) ^ 2),
    abs_of_pos (by norm_num : (0:ℝ) < 5 - 3 * (161 / 181) ^ 2),
    abs_of_neg (by norm_num : 6 * (161 / 181 : ℝ) ^ 2 - (161 / 181) ^ 4 - 5 < 0)]
  norm_num

/-- Face `0` along `ζ`: `H_w = 223/100`. -/
theorem hel_w_face0 : 1 / (199 / 181 : ℝ) ^ 3 + 3 * aF / (199 / 181) ^ 3 +
    3 / (2 * (199 / 181) ^ 2) ≤ 223 / 100 := by unfold aF; norm_num

/-- Face `1` along `ζ`: `H_w = 19/5`. -/
theorem hel_w_face1 : 1 / (161 / 181 : ℝ) ^ 3 + 3 * aF / (161 / 181) ^ 3 +
    3 / (2 * (161 / 181) ^ 2) ≤ 19 / 5 := by unfold aF; norm_num

/-- Plane faces (`ρ ∈ [161/181, 199/181]`, `|ζ| ≤ a`) along `φ`: `H_φ = 147/100`. -/
theorem hel_phi_plane {ρ ζ : ℝ} (h1 : 161 / 181 ≤ ρ) (h2 : ρ ≤ 199 / 181) (hζ : |ζ| ≤ aF) :
    |cA ρ| + |cB ρ ζ| + 9 * |cG ρ ζ| + 9 * |cD ρ ζ| + 4 * |cE ρ ζ| + 4 * |cF ρ ζ| ≤ 147 / 100 := by
  have hρ : 0 < ρ := by linarith
  unfold aF at hζ
  have hz0 := abs_nonneg ζ
  have hz2 : ζ ^ 2 ≤ (3420 / 32761) ^ 2 := by rw [← sq_abs]; gcongr
  have hr2l : (161 / 181 : ℝ) ^ 2 ≤ ρ ^ 2 := by gcongr
  have hr2u : ρ ^ 2 ≤ (199 / 181 : ℝ) ^ 2 := by gcongr
  have hr3 : (161 / 181 : ℝ) ^ 3 ≤ ρ ^ 3 := by gcongr
  have hA : |cA ρ| ≤ 2 * (3420 / 32761) / (8 * (161 / 181)) := by
    unfold cA; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ)]
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by linarith)
    rw [abs_le]; constructor <;> norm_num at hr2l hr2u ⊢ <;> linarith
  have hB : |cB ρ ζ| ≤ 3420 / 32761 * (3 - (161 / 181) ^ 2) / (8 * (161 / 181)) := by
    unfold cB; rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ),
      abs_of_pos (by nlinarith : (0:ℝ) < 3 - ρ ^ 2)]
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by linarith)
    exact mul_le_mul hζ (by linarith) (by nlinarith) (by norm_num)
  have hG : |cG ρ ζ| ≤ (2 * (3420 / 32761) + 4 * (3420 / 32761) ^ 2) / (8 * (161 / 181) ^ 3) := by
    unfold cG; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ ^ 3)]
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by linarith)
    rw [abs_le]; constructor <;> norm_num at hr2l hr2u hz2 ⊢ <;> nlinarith [sq_nonneg ζ]
  have hD : |cD ρ ζ| ≤ 3420 / 32761 * (5 - 3 * (161 / 181) ^ 2) / (8 * (161 / 181) ^ 3) := by
    unfold cD; rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 8 * ρ ^ 3)]
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by linarith)
    refine mul_le_mul hζ ?_ (abs_nonneg _) (by norm_num)
    rw [abs_le]; constructor <;> norm_num at hr2l hr2u hz2 ⊢ <;> nlinarith [sq_nonneg ζ]
  have hE : |cE ρ ζ| ≤ (8 * (3420 / 32761) + 8 * (3420 / 32761) ^ 2) / (16 * (161 / 181) ^ 2) := by
    unfold cE; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 16 * ρ ^ 2)]
    apply div_le_div₀ (by norm_num) _ (by norm_num) (by nlinarith)
    rw [abs_le]; constructor <;> norm_num at hr2l hr2u hz2 ⊢ <;>
      nlinarith [sq_nonneg ζ, mul_nonneg (sub_nonneg.2 hr2l) (sub_nonneg.2 hr2u)]
  have hF : |cF ρ ζ| ≤ 3420 / 32761 / (2 * (161 / 181) ^ 2) := by
    unfold cF; rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * ρ ^ 2)]
    exact div_le_div₀ (by norm_num) hζ (by norm_num) (by nlinarith)
  have : 2 * (3420 / 32761 : ℝ) / (8 * (161 / 181)) +
      3420 / 32761 * (3 - (161 / 181) ^ 2) / (8 * (161 / 181)) +
      9 * ((2 * (3420 / 32761) + 4 * (3420 / 32761) ^ 2) / (8 * (161 / 181) ^ 3)) +
      9 * (3420 / 32761 * (5 - 3 * (161 / 181) ^ 2) / (8 * (161 / 181) ^ 3)) +
      4 * ((8 * (3420 / 32761) + 8 * (3420 / 32761) ^ 2) / (16 * (161 / 181) ^ 2)) +
      4 * (3420 / 32761 / (2 * (161 / 181) ^ 2)) ≤ 147 / 100 := by norm_num
  linarith

/-- Plane faces along `ρ`: `H_w = 17/2` dominates the six absolute second derivatives. -/
theorem hel_w_plane {ρ ζ : ℝ} (h1 : 161 / 181 ≤ ρ) (hζ : |ζ| = aF) :
    |1 / (4 * ρ ^ 3)| + |3 * ζ / (4 * ρ ^ 3)| +
      |1 / (4 * ρ ^ 3) + 3 * (4 * ζ ^ 2 - 1) / (2 * ρ ^ 5)| +
      |3 * ζ * (5 - 4 * ζ ^ 2) / (2 * ρ ^ 5) - 3 * ζ / (4 * ρ ^ 3)| +
      |-1 / 8 + 3 * (12 * ζ ^ 2 - 5) / (8 * ρ ^ 4)| + |3 * ζ / ρ ^ 4| ≤ 17 / 2 := by
  have hρ : 0 < ρ := by linarith
  unfold aF at hζ
  set t := ρ⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hρ
  have ht1 : t ≤ 181 / 161 := by
    rw [ht]; rw [inv_le_comm₀ hρ (by norm_num)]; norm_num; linarith
  have k3 : 1 / (4 * ρ ^ 3) = 1 / 4 * t ^ 3 := by rw [ht]; field_simp
  have k3' : 3 * ζ / (4 * ρ ^ 3) = 3 / 4 * ζ * t ^ 3 := by rw [ht]; field_simp
  have k5 : 3 * (4 * ζ ^ 2 - 1) / (2 * ρ ^ 5) = 3 / 2 * (4 * ζ ^ 2 - 1) * t ^ 5 := by
    rw [ht]; field_simp
  have k5' : 3 * ζ * (5 - 4 * ζ ^ 2) / (2 * ρ ^ 5) = 3 / 2 * ζ * (5 - 4 * ζ ^ 2) * t ^ 5 := by
    rw [ht]; field_simp
  have k4 : 3 * (12 * ζ ^ 2 - 5) / (8 * ρ ^ 4) = 3 / 8 * (12 * ζ ^ 2 - 5) * t ^ 4 := by
    rw [ht]; field_simp
  have k4' : 3 * ζ / ρ ^ 4 = 3 * ζ * t ^ 4 := by rw [ht]; field_simp
  rw [k3, k3', k5, k5', k4, k4']
  have hz0 := abs_nonneg ζ
  have hz2 : ζ ^ 2 = (3420 / 32761) ^ 2 := by rw [← sq_abs, hζ]
  have hζ' : |ζ| ≤ 3420 / 32761 := hζ.le
  have t3 : t ^ 3 ≤ (181 / 161) ^ 3 := by gcongr
  have t4 : t ^ 4 ≤ (181 / 161) ^ 4 := by gcongr
  have t5 : t ^ 5 ≤ (181 / 161) ^ 5 := by gcongr
  have p3 : 0 < t ^ 3 := by positivity
  have p4 : 0 < t ^ 4 := by positivity
  have p5 : 0 < t ^ 5 := by positivity
  have a1 : |4 * ζ ^ 2 - 1| ≤ 1 - 4 * (3420 / 32761) ^ 2 := by
    rw [hz2, abs_of_neg (by norm_num)]; norm_num
  have a2 : |5 - 4 * ζ ^ 2| ≤ 5 - 4 * (3420 / 32761) ^ 2 := by
    rw [hz2, abs_of_pos (by norm_num)]
  have a3 : |12 * ζ ^ 2 - 5| ≤ 5 - 12 * (3420 / 32761) ^ 2 := by
    rw [hz2, abs_of_neg (by norm_num)]; norm_num
  have T : ∀ c u v : ℝ, 0 ≤ c → 0 ≤ v → |c * u * v| = c * |u| * v := fun c u v hc hv => by
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hv]
  have D2 : ∀ c v : ℝ, 0 ≤ c → 0 ≤ v → |c * v| = c * v := fun c v hc hv => by
    rw [abs_mul, abs_of_nonneg hc, abs_of_nonneg hv]
  have m1 : |1 / 4 * t ^ 3| ≤ 1 / 4 * (181 / 161) ^ 3 := by
    rw [D2 _ _ (by norm_num) p3.le]; linarith
  have m2 : |3 / 4 * ζ * t ^ 3| ≤ 3 / 4 * (3420 / 32761) * (181 / 161) ^ 3 := by
    rw [T _ _ _ (by norm_num) p3.le]; gcongr
  have m3 : |1 / 4 * t ^ 3 + 3 / 2 * (4 * ζ ^ 2 - 1) * t ^ 5| ≤
      1 / 4 * (181 / 161) ^ 3 + 3 / 2 * (1 - 4 * (3420 / 32761) ^ 2) * (181 / 161) ^ 5 := by
    refine (abs_add_le _ _).trans ?_
    rw [D2 _ _ (by norm_num) p3.le, T _ _ _ (by norm_num) p5.le]
    gcongr
  have m4 : |3 / 2 * ζ * (5 - 4 * ζ ^ 2) * t ^ 5 - 3 / 4 * ζ * t ^ 3| ≤
      3 / 2 * (3420 / 32761 * (5 - 4 * (3420 / 32761) ^ 2)) * (181 / 161) ^ 5 +
        3 / 4 * (3420 / 32761) * (181 / 161) ^ 3 := by
    refine (abs_sub _ _).trans ?_
    rw [show 3 / 2 * ζ * (5 - 4 * ζ ^ 2) * t ^ 5 = 3 / 2 * (ζ * (5 - 4 * ζ ^ 2)) * t ^ 5 by ring,
      T _ _ _ (by norm_num) p5.le, T _ _ _ (by norm_num) p3.le, abs_mul]
    have : |ζ| * |5 - 4 * ζ ^ 2| ≤ 3420 / 32761 * (5 - 4 * (3420 / 32761) ^ 2) := by gcongr
    have h5 : 3 / 2 * (|ζ| * |5 - 4 * ζ ^ 2|) * t ^ 5 ≤
        3 / 2 * (3420 / 32761 * (5 - 4 * (3420 / 32761) ^ 2)) * (181 / 161) ^ 5 := by gcongr
    have h3 : 3 / 4 * |ζ| * t ^ 3 ≤ 3 / 4 * (3420 / 32761) * (181 / 161) ^ 3 := by gcongr
    linarith
  have m5 : |-1 / 8 + 3 / 8 * (12 * ζ ^ 2 - 5) * t ^ 4| ≤
      1 / 8 + 3 / 8 * (5 - 12 * (3420 / 32761) ^ 2) * (181 / 161) ^ 4 := by
    refine (abs_add_le _ _).trans ?_
    rw [T _ _ _ (by norm_num) p4.le, show |(-1 / 8 : ℝ)| = 1 / 8 by norm_num]
    gcongr
  have m6 : |3 * ζ * t ^ 4| ≤ 3 * (3420 / 32761) * (181 / 161) ^ 4 := by
    rw [T _ _ _ (by norm_num) p4.le]; gcongr
  have hnum : 1 / 4 * (181 / 161 : ℝ) ^ 3 + 3 / 4 * (3420 / 32761) * (181 / 161) ^ 3 +
      (1 / 4 * (181 / 161) ^ 3 + 3 / 2 * (1 - 4 * (3420 / 32761) ^ 2) * (181 / 161) ^ 5) +
      (3 / 2 * (3420 / 32761 * (5 - 4 * (3420 / 32761) ^ 2)) * (181 / 161) ^ 5 +
        3 / 4 * (3420 / 32761) * (181 / 161) ^ 3) +
      (1 / 8 + 3 / 8 * (5 - 12 * (3420 / 32761) ^ 2) * (181 / 161) ^ 4) +
      3 * (3420 / 32761) * (181 / 161) ^ 4 ≤ 17 / 2 := by
    norm_num
  linarith

end PlasmaLean.Design.PolygonCoil
