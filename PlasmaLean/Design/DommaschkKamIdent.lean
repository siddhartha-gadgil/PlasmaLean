/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamIdentCheckD
public import PlasmaLean.Design.DommaschkKamIdentCheckR
public import PlasmaLean.Design.DommaschkKamField
public import PlasmaLean.Design.DommaschkQA2R

/-!
# The flow-form polynomials of the Dommaschk target are the components of `field candidate`

For `B = DommaschkQA2R.field candidate` at the point `cylPoint R φ z = (R cos φ, R sin φ, z)` with
`R > 0`, and its cylindrical components `B_R = cos φ B_x + sin φ B_y`,
`B_φ = −sin φ B_x + cos φ B_y`, `B_z` (`cylBR`, `cylBphi`, `cylBz`), the polynomials of
`Design/DommaschkKamField`, evaluated at `ptC R φ z = (R − R₀, z, cos 2φ, sin 2φ, 0, 0)`, are

* **`Dp_ident`**: `D = R⁷ B_φ`;
* **`nRp_ident`**: `n_R = R⁸ B_R`;
* **`nZp_ident`**: `n_z = R⁸ B_z`;

so the flow-form vector field `X = n/D` is `(R B_R/B_φ, R B_z/B_φ)`, the field-line equations
`dR/dφ`, `dz/dφ` of `B` with the toroidal angle as time, wherever `B_φ ≠ 0` (`flow_ident`).

Proof: the substitution `R = R₀ + u` (`subst_D`, …: kernel checks) turns the `u`-form data into
`R`-form data with even powers of `R`; each term `q R^{2k} z^b c^i s^j` is the cylindrical potential
`q r₂^{k−i−j} z^b (x² − y²)^i (2xy)^j` at `cylPoint` (`eval_convAll`, using
`x² − y² = R² cos 2φ`, `2xy = R² sin 2φ`); and the resulting Cartesian identities against the
gradient of the potentials `P k` are checked in normal form (`ident_D`, `ident_nR`, `ident_nZ`;
`eval_eq_zero_of_degCheck`), which holds wherever `r₂ ≠ 0`.

These are the pointwise statements item 10 (N-33) needs to transfer an invariant torus of the flow
form (`D 𝓛K = n` with `D ≠ 0`) to a `FieldTorus` of `field candidate`. (In the strip algebra,
`KamFlowField.eval_polyExpr` evaluates `PolyExpr.eval (xB u z) e` at `(θ, ψ)` as `e` at
`(u(θ, ψ), z(θ, ψ), −sin ψ, cos ψ, 0, 0)`, and `−sin ψ = cos 2φ`, `cos ψ = sin 2φ` for
`ψ = 2φ − π/2`.)

**Sanity.** `cmulMono_eval`, `eval_trigC` (the Cartesian forms of `cos 2φ`, `sin 2φ`), and the
rejected fixture `ident_nZ_bad` of `DommaschkKamIdentCheck`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKam

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton DkPoly PlasmaLean.Fields
  PlasmaLean.Fields.CylAlgebra PlasmaLean.Contract Real

/-! ## Real points and the substitution `R = R₀ + u` -/

/-- The variables `(R − R₀, z, cos 2φ, sin 2φ, 0, 0)` of the flow-form polynomials at the point
with cylindrical coordinates `(R, φ, z)`. -/
def ptC (R φ z : ℝ) : Fin 6 → ℂ :=
  ![((R - dkR0 : ℝ) : ℂ), (z : ℂ), (cos (2 * φ) : ℂ), (sin (2 * φ) : ℂ), 0, 0]

/-- Real evaluation of a sparse polynomial. -/
def evR (x0 x1 x2 x3 : ℝ) (p : SP) : ℝ :=
  (p.map fun t => (t.q : ℝ) * (x0 ^ t.a * x1 ^ t.b * x2 ^ t.c * x3 ^ t.d)).sum

/-- Evaluation at real values is real. -/
theorem ev_ofReal (x0 x1 x2 x3 : ℝ) (p : SP) :
    ev ![(x0 : ℂ), (x1 : ℂ), (x2 : ℂ), (x3 : ℂ), 0, 0] p = (evR x0 x1 x2 x3 p : ℂ) := by
  induction p with
  | nil => simp [evR]
  | cons t p ih =>
    rw [ev_cons, ih]
    simp [evR, Tm.ev]

/-- `Rl` is `R₀ + u`. -/
theorem ev_Rl (x : Fin 6 → ℂ) : ev x Rl = ((R0q : ℚ) : ℂ) + x 0 := by
  simp [Rl, Tm.ev]

/-- `RpowL n` is `(R₀ + u)ⁿ`. -/
theorem ev_RpowL (x : Fin 6 → ℂ) : ∀ n, ev x (RpowL n) = (((R0q : ℚ) : ℂ) + x 0) ^ n
  | 0 => by simp [RpowL, Tm.ev]
  | n + 1 => by rw [RpowL, ev_mul, ev_RpowL x n, ev_Rl, pow_succ, mul_comm]

/-- **The substitution**: `substR p` at `u` is `p` at `R = R₀ + u`. -/
theorem ev_substR (x : Fin 6 → ℂ) (p : SP) :
    ev x (substR p) = ev ![((R0q : ℚ) : ℂ) + x 0, x 1, x 2, x 3, 0, 0] p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [substR, List.foldr_cons] at ih ⊢
    rw [ev_merge, ih, ev_mulMono, ev_RpowL, ev_cons]
    simp [Tm.ev]
    ring

/-- At `ptC R φ z`, an `R`-form polynomial `p` with `substR p = pu` gives `pu = p(R, …)`. -/
theorem ev_ptC_of_subst {p pu : SP} (h : substR p = pu) (R φ z : ℝ) :
    ev (ptC R φ z) pu = (evR R z (cos (2 * φ)) (sin (2 * φ)) p : ℂ) := by
  rw [← h, ev_substR, ← ev_ofReal]
  congr 1
  funext i
  fin_cases i <;> simp [ptC, R0q_cast, dkR0]

/-! ## Cylindrical potentials at `cylPoint` -/

/-- The `x`-coordinate of `cylPoint`. -/
theorem cyl0 (R φ z : ℝ) : (cylPoint R φ z) 0 = R * cos φ := by simp [cylPoint]
/-- The `y`-coordinate of `cylPoint`. -/
theorem cyl1 (R φ z : ℝ) : (cylPoint R φ z) 1 = R * sin φ := by simp [cylPoint]
/-- The `z`-coordinate of `cylPoint`. -/
theorem cyl2 (R φ z : ℝ) : (cylPoint R φ z) 2 = z := by simp [cylPoint]

/-- `r₂ = R²` at `cylPoint`. -/
theorem r2_cyl (R φ z : ℝ) : r2 (cylPoint R φ z) = R ^ 2 := by
  rw [r2, cyl0, cyl1]
  linear_combination R ^ 2 * sin_sq_add_cos_sq φ

/-- Evaluation of a product with a monomial (off the axis). -/
theorem cmulMono_eval (m : Mono) (f : CylPoly) {y : Space} (hy : r2 y ≠ 0) :
    eval (cmulMono m f) y = m.eval y * eval f y := by
  induction f with
  | nil => simp [cmulMono]
  | cons n f ih =>
    simp only [cmulMono, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    simp only [Mono.eval, Int.cast_mul, pow_add, zpow_add₀ hy]
    ring

/-- Evaluation of a product (off the axis). -/
theorem cmul_eval (f g : CylPoly) {y : Space} (hy : r2 y ≠ 0) :
    eval (cmul f g) y = eval f y * eval g y := by
  induction f with
  | nil => simp [cmul]
  | cons m f ih =>
    simp only [cmul, List.flatMap_cons, eval_append, eval_cons] at ih ⊢
    rw [ih, cmulMono_eval m g hy]
    ring

/-- Evaluation of a power (off the axis). -/
theorem cpow_eval (f : CylPoly) {y : Space} (hy : r2 y ≠ 0) :
    ∀ n, eval (cpow f n) y = eval f y ^ n
  | 0 => by simp [cpow, Mono.eval]
  | n + 1 => by rw [cpow, cmul_eval _ _ hy, cpow_eval f hy n, pow_succ, mul_comm]

/-- Evaluation of an integer multiple. -/
theorem cscale_eval (k : ℤ) (f : CylPoly) (y : Space) :
    eval (cscale k f) y = k * eval f y := by
  induction f with
  | nil => simp [cscale]
  | cons m f ih =>
    simp only [cscale, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    simp only [Mono.eval, Int.cast_mul]
    ring

/-- `(x² − y²)^i (2xy)^j` at `cylPoint` is `R^{2(i+j)} cos^i 2φ sin^j 2φ`. -/
theorem eval_trigC (i j : ℕ) {R : ℝ} (hR : R ≠ 0) (φ z : ℝ) :
    eval (trigC i j) (cylPoint R φ z) =
      (R ^ 2 * cos (2 * φ)) ^ i * (R ^ 2 * sin (2 * φ)) ^ j := by
  have hy : r2 (cylPoint R φ z) ≠ 0 := by rw [r2_cyl]; positivity
  rw [trigC, cmul_eval _ _ hy, cpow_eval _ hy, cpow_eval _ hy]
  congr 2
  · simp [X2, Mono.eval, cyl0, cyl1, cos_two_mul]
    linear_combination (-R ^ 2) * sin_sq_add_cos_sq φ
  · simp [XY, Mono.eval, cyl0, cyl1, sin_two_mul]; ring

/-- One converted term at `cylPoint`. -/
theorem eval_convT (N : ℕ) (t : Tm) (hden : (N * t.q).den = 1) (heven : t.a % 2 = 0)
    {R : ℝ} (hR : R ≠ 0) (φ z : ℝ) :
    eval (convT N t) (cylPoint R φ z) =
      (N : ℝ) * ((t.q : ℝ) * (R ^ t.a * z ^ t.b * cos (2 * φ) ^ t.c * sin (2 * φ) ^ t.d)) := by
  have hy : r2 (cylPoint R φ z) ≠ 0 := by rw [r2_cyl]; positivity
  have hR2 : R ^ 2 ≠ 0 := by positivity
  rw [convT, cscale_eval, cmulMono_eval _ _ hy, eval_trigC _ _ hR]
  have hnum : (((N * t.q).num : ℤ) : ℝ) = (N : ℝ) * (t.q : ℝ) := by
    have := Rat.coe_int_num_of_den_eq_one hden
    exact_mod_cast this
  rw [hnum]
  obtain ⟨k, hk⟩ : ∃ k, t.a = 2 * k := ⟨t.a / 2, by omega⟩
  have hk2 : t.a / 2 = k := by omega
  simp only [Mono.eval, r2_cyl, cyl2, hk2, Int.cast_one, pow_zero, mul_one, one_mul]
  have hz : (R ^ 2) ^ (((k : ℕ) : ℤ) - (t.c : ℤ) - (t.d : ℤ)) * (R ^ 2) ^ t.c * (R ^ 2) ^ t.d =
      R ^ t.a := by
    rw [← zpow_natCast (R ^ 2) t.c, ← zpow_natCast (R ^ 2) t.d, ← zpow_add₀ hR2,
      ← zpow_add₀ hR2, show ((k : ℕ) : ℤ) - t.c - t.d + t.c + t.d = (k : ℤ) by ring,
      zpow_natCast, ← pow_mul, hk]
  rw [← hz]
  ring

/-- The exactness check, termwise. -/
theorem convOK_iff {N : ℕ} {p : SP} :
    convOK N p = true ↔ ∀ t ∈ p, (N * t.q).den = 1 ∧ t.a % 2 = 0 := by
  simp [convOK]

/-- **The conversion at `cylPoint`**: `convAll N p` is `N p(R, z, cos 2φ, sin 2φ)`. -/
theorem eval_convAll {N : ℕ} {p : SP} (h : convOK N p = true) {R : ℝ} (hR : R ≠ 0) (φ z : ℝ) :
    eval (convAll N p) (cylPoint R φ z) = N * evR R z (cos (2 * φ)) (sin (2 * φ)) p := by
  rw [convOK_iff] at h
  induction p with
  | nil => simp [convAll, evR]
  | cons t p ih =>
    have ht := h t List.mem_cons_self
    simp only [convAll, List.flatMap_cons, eval_append] at ih ⊢
    rw [ih fun s hs => h s (List.mem_cons_of_mem _ hs), eval_convT N t ht.1 ht.2 hR]
    simp only [evR, List.map_cons, List.sum_cons]
    ring

/-! ## The field side -/

/-- The components of `field candidate` in Cartesian coordinates. -/
theorem field_apply (y : Space) (i : Fin 3) : (DommaschkQA2R.field DommaschkQA2R.candidate y) i =
    RationalStellarator.toroidal y i + ∑ k, ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k :
      ℚ) : ℝ) * eval (d i (DommaschkQA2R.P k)) y := by
  simp [DommaschkQA2R.field, gradField_apply]

/-- Each `L w_k` is an integer. -/
theorem LW_den (k : Fin 42) : (LWq k).den = 1 := by
  have h := LW_int
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h k (List.mem_finRange k)

/-- `L w_k` as a real number. -/
theorem LW_cast (k : Fin 42) : (((LWq k).num : ℤ) : ℝ) =
    (Lw : ℝ) * ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k : ℚ) : ℝ) := by
  have := Rat.coe_int_num_of_den_eq_one (LW_den k)
  have h2 : ((LWq k : ℚ) : ℝ) = (Lw : ℝ) * ((DommaschkQA2R.candidate k *
      DommaschkQA2R.scale k : ℚ) : ℝ) := by simp [LWq]
  rw [← h2, ← this]; push_cast; rfl

/-- Evaluation of a `flatMap` over any list. -/
theorem eval_flatMap' {α : Type*} (l : List α) (g : α → CylPoly) (y : Space) :
    eval (l.flatMap g) y = (l.map fun k => eval (g k) y).sum := by
  induction l with
  | nil => rfl
  | cons k l ih => simp [List.flatMap_cons, ih]

/-- `Σ_k L w_k f_k` at a point. -/
theorem eval_Gpart (f : Fin 42 → CylPoly) (y : Space) :
    eval (Gpart f) y = (Lw : ℝ) * ∑ k, ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k :
      ℚ) : ℝ) * eval (f k) y := by
  rw [Gpart, eval_flatMap', Finset.mul_sum, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  split_ifs with h
  · have h0 : LWq k = 0 := by simpa using h
    have : (Lw : ℝ) * ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k : ℚ) : ℝ) = 0 := by
      rw [← LW_cast, h0]; simp
    rw [eval_nil, ← mul_assoc, this, zero_mul]
  · rw [cscale_eval, LW_cast]; ring

/-- `r₂ · r₂⁻¹ = 1` off the axis. -/
theorem winv_mul (y : Space) (hy : r2 y ≠ 0) :
    RationalStellarator.r2 y * RationalStellarator.winv y = 1 := by
  rw [RationalStellarator.winv]
  exact mul_inv_cancel₀ hy

/-- The components of `∇φ`. -/
theorem toroidal_apply (y : Space) :
    RationalStellarator.toroidal y 0 = -y 1 * RationalStellarator.winv y ∧
      RationalStellarator.toroidal y 1 = y 0 * RationalStellarator.winv y ∧
      RationalStellarator.toroidal y 2 = 0 := by
  simp [RationalStellarator.toroidal]

/-- The monomial `r₂ⁿ`. -/
theorem eval_r2mono (n : ℕ) (y : Space) : Mono.eval ⟨1, 0, 0, 0, (n : ℤ), 0⟩ y = r2 y ^ n := by
  simp [Mono.eval]

/-- `Gphi = L r₂³ (−y B_x + x B_y)`. -/
theorem eval_Gphi (y : Space) (hy : r2 y ≠ 0) :
    eval Gphi y = (Lw : ℝ) * r2 y ^ 3 *
      (-(y 1) * (DommaschkQA2R.field DommaschkQA2R.candidate y) 0 +
        y 0 * (DommaschkQA2R.field DommaschkQA2R.candidate y) 1) := by
  set w : Fin 42 → ℝ := fun k => ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k : ℚ) : ℝ)
  have hin : ∀ k, eval (cmulMono ⟨1, 1, 0, 0, 0, 0⟩ (nz (d1 (DommaschkQA2R.P k))) ++
      cmulMono ⟨-1, 0, 1, 0, 0, 0⟩ (nz (d0 (DommaschkQA2R.P k)))) y =
      y 0 * eval (d1 (DommaschkQA2R.P k)) y - y 1 * eval (d0 (DommaschkQA2R.P k)) y := by
    intro k
    rw [eval_append, cmulMono_eval _ _ hy, cmulMono_eval _ _ hy]
    simp only [nz, eval_filter_ne_zero]
    simp [Mono.eval]; ring
  have hS : ∑ k, w k * (y 0 * eval (d1 (DommaschkQA2R.P k)) y -
      y 1 * eval (d0 (DommaschkQA2R.P k)) y) =
      y 0 * ∑ k, w k * eval (d 1 (DommaschkQA2R.P k)) y -
        y 1 * ∑ k, w k * eval (d 0 (DommaschkQA2R.P k)) y := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [d]; simp; ring
  have hw := winv_mul y hy
  obtain ⟨h0, h1, -⟩ := toroidal_apply y
  rw [Gphi, show (⟨1, 0, 0, 0, 3, 0⟩ : Mono) = ⟨1, 0, 0, 0, ((3 : ℕ) : ℤ), 0⟩ from rfl,
    cmulMono_eval _ _ hy, eval_r2mono, eval_cons, eval_Gpart, field_apply, field_apply, h0, h1]
  simp only [hin]
  rw [hS]
  have hL : Mono.eval ⟨(Lw : ℤ), 0, 0, 0, 0, 0⟩ y = Lw := by simp [Mono.eval]
  rw [hL]
  have hr : RationalStellarator.r2 y = r2 y := rfl
  rw [hr] at hw
  have hr2 : r2 y = y 0 ^ 2 + y 1 ^ 2 := rfl
  linear_combination (-(Lw : ℝ)) * r2 y ^ 3 * hw + (Lw : ℝ) * r2 y ^ 3 *
    RationalStellarator.winv y * hr2

/-- `GRh = L r₂³ (x B_x + y B_y)`. -/
theorem eval_GRh (y : Space) (hy : r2 y ≠ 0) :
    eval GRh y = (Lw : ℝ) * r2 y ^ 3 *
      (y 0 * (DommaschkQA2R.field DommaschkQA2R.candidate y) 0 +
        y 1 * (DommaschkQA2R.field DommaschkQA2R.candidate y) 1) := by
  set w : Fin 42 → ℝ := fun k => ((DommaschkQA2R.candidate k * DommaschkQA2R.scale k : ℚ) : ℝ)
  have hin : ∀ k, eval (cmulMono ⟨1, 1, 0, 0, 0, 0⟩ (nz (d0 (DommaschkQA2R.P k))) ++
      cmulMono ⟨1, 0, 1, 0, 0, 0⟩ (nz (d1 (DommaschkQA2R.P k)))) y =
      y 0 * eval (d0 (DommaschkQA2R.P k)) y + y 1 * eval (d1 (DommaschkQA2R.P k)) y := by
    intro k
    rw [eval_append, cmulMono_eval _ _ hy, cmulMono_eval _ _ hy]
    simp only [nz, eval_filter_ne_zero]
    simp [Mono.eval]
  have hS : ∑ k, w k * (y 0 * eval (d0 (DommaschkQA2R.P k)) y +
      y 1 * eval (d1 (DommaschkQA2R.P k)) y) =
      y 0 * ∑ k, w k * eval (d 0 (DommaschkQA2R.P k)) y +
        y 1 * ∑ k, w k * eval (d 1 (DommaschkQA2R.P k)) y := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [d]; simp; ring
  obtain ⟨h0, h1, -⟩ := toroidal_apply y
  rw [GRh, show (⟨1, 0, 0, 0, 3, 0⟩ : Mono) = ⟨1, 0, 0, 0, ((3 : ℕ) : ℤ), 0⟩ from rfl,
    cmulMono_eval _ _ hy, eval_r2mono, eval_Gpart, field_apply, field_apply, h0, h1]
  simp only [hin]
  rw [hS]
  ring

/-- `GZ = L r₂⁴ B_z`. -/
theorem eval_GZ (y : Space) (hy : r2 y ≠ 0) :
    eval GZ y = (Lw : ℝ) * r2 y ^ 4 * (DommaschkQA2R.field DommaschkQA2R.candidate y) 2 := by
  obtain ⟨-, -, h2⟩ := toroidal_apply y
  rw [GZ, show (⟨1, 0, 0, 0, 4, 0⟩ : Mono) = ⟨1, 0, 0, 0, ((4 : ℕ) : ℤ), 0⟩ from rfl,
    cmulMono_eval _ _ hy, eval_r2mono, eval_Gpart, field_apply, h2, zero_add]
  simp only [d, nz, eval_filter_ne_zero]
  simp
  ring

/-! ## The degree-sliced check -/

/-- **Soundness of the degree-sliced check** off the axis. -/
theorem eval_eq_zero_of_degCheck {js : List ℕ} {ks : List ℤ} {L : CylPoly}
    (h : degCheck js ks L = true) {y : Space} (hy : r2 y ≠ 0) : eval L y = 0 := by
  induction ks generalizing L with
  | nil => exact eval_eq_zero_of_sliceCheck h hy
  | cons k ks ih =>
    simp only [degCheck, Bool.and_eq_true] at h
    rw [← eval_filter_add L (fun m => rdeg m == k) y, eval_eq_zero_of_sliceCheck h.1 hy,
      zero_add]
    exact ih h.2

/-! ## The identification -/

/-- The cylindrical component `B_R = cos φ B_x + sin φ B_y` of `field candidate`. -/
def cylBR (R φ z : ℝ) : ℝ :=
  cos φ * (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)) 0 +
    sin φ * (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)) 1

/-- The cylindrical component `B_φ = −sin φ B_x + cos φ B_y` of `field candidate`. -/
def cylBphi (R φ z : ℝ) : ℝ :=
  -(sin φ * (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)) 0) +
    cos φ * (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)) 1

/-- The vertical component `B_z` of `field candidate`. -/
def cylBz (R φ z : ℝ) : ℝ := (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)) 2

/-- From a sliced normal-form check `L·convAll N p − N·G = 0` and `G = L v` at `cylPoint`,
`p = v` there. -/
theorem evR_ident {N : ℕ} {p : SP} {G : CylPoly} (hN : (N : ℝ) ≠ 0)
    (hc : convOK N p = true)
    (hchk : degCheck zs rs (cscale Lw (convAll N p) ++ cscale (-N) G) = true)
    {R : ℝ} (hR : R ≠ 0) (φ z : ℝ) {v : ℝ} (hG : eval G (cylPoint R φ z) = (Lw : ℝ) * v) :
    evR R z (cos (2 * φ)) (sin (2 * φ)) p = v := by
  have hy : r2 (cylPoint R φ z) ≠ 0 := by rw [r2_cyl]; positivity
  have h := eval_eq_zero_of_degCheck hchk hy
  rw [eval_append, cscale_eval, cscale_eval, eval_convAll hc hR, hG] at h
  have hL : (Lw : ℝ) ≠ 0 := by norm_num [Lw]
  have : (Lw : ℝ) * N * (evR R z (cos (2 * φ)) (sin (2 * φ)) p - v) = 0 := by
    push_cast at h; linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (mul_ne_zero hL hN)
  · linarith

/-- **`D = R⁷ B_φ`** at every point with `R > 0`. -/
theorem Dp_ident {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    PolyExpr.eval (ptC R φ z) Dp = ((R ^ 7 * cylBphi R φ z : ℝ) : ℂ) := by
  rw [Dp, eval_toPE, ev_ptC_of_subst subst_D]
  congr 1
  refine evR_ident (by norm_num [NDn]) convOK_D ident_D hR.ne' φ z ?_
  rw [eval_Gphi _ (by rw [r2_cyl]; positivity), r2_cyl, cyl0, cyl1, cylBphi]
  ring

/-- Multiplying by `R` (slot `0`). -/
theorem evR_mulR (x0 x1 x2 x3 : ℝ) (p : SP) :
    evR x0 x1 x2 x3 (mulMono ⟨1, 1, 0, 0, 0⟩ p) = x0 * evR x0 x1 x2 x3 p := by
  induction p with
  | nil => simp [mulMono, evR]
  | cons t p ih =>
    simp only [mulMono, evR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [one_mul, Nat.zero_add]
    ring

/-- **`n_R = R⁸ B_R`** at every point with `R > 0`. -/
theorem nRp_ident {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    PolyExpr.eval (ptC R φ z) nRp = ((R ^ 8 * cylBR R φ z : ℝ) : ℂ) := by
  rw [nRp, eval_toPE, ev_ptC_of_subst subst_nR]
  congr 1
  rw [evR_mulR, evR_ident (v := R ^ 7 * cylBR R φ z) (by norm_num [NRn]) convOK_nR ident_nR
    hR.ne' φ z ?_]
  · ring
  · rw [eval_GRh _ (by rw [r2_cyl]; positivity), r2_cyl, cyl0, cyl1, cylBR]
    ring

/-- **`n_z = R⁸ B_z`** at every point with `R > 0`. -/
theorem nZp_ident {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    PolyExpr.eval (ptC R φ z) nZp = ((R ^ 8 * cylBz R φ z : ℝ) : ℂ) := by
  rw [nZp, eval_toPE, ev_ptC_of_subst subst_nZ]
  congr 1
  refine evR_ident (by norm_num [NZn]) convOK_nZ ident_nZ hR.ne' φ z ?_
  rw [eval_GZ _ (by rw [r2_cyl]; positivity), r2_cyl, cylBz]
  ring

/-- **The flow-form vector field is the field-line vector field of `field candidate`**: where
`R > 0` and `B_φ ≠ 0`, `D ≠ 0` and `X = (n_R/D, n_z/D) = (R B_R/B_φ, R B_z/B_φ)`. -/
theorem flow_ident {R : ℝ} (hR : 0 < R) (φ z : ℝ) (hB : cylBphi R φ z ≠ 0) :
    PolyExpr.eval (ptC R φ z) Dp ≠ 0 ∧
      PolyExpr.eval (ptC R φ z) nRp / PolyExpr.eval (ptC R φ z) Dp =
        ((R * cylBR R φ z / cylBphi R φ z : ℝ) : ℂ) ∧
      PolyExpr.eval (ptC R φ z) nZp / PolyExpr.eval (ptC R φ z) Dp =
        ((R * cylBz R φ z / cylBphi R φ z : ℝ) : ℂ) := by
  rw [Dp_ident hR, nRp_ident hR, nZp_ident hR]
  have h7 : R ^ 7 ≠ 0 := by positivity
  refine ⟨by exact_mod_cast mul_ne_zero h7 hB, ?_, ?_⟩
  · rw [← Complex.ofReal_div]; congr 1; field_simp
  · rw [← Complex.ofReal_div]; congr 1; field_simp

end PlasmaLean.Design.DommaschkKam
