/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorConfinedMain
public import PlasmaLean.Design.RationalStellaratorConfinedFaces
public import PlasmaLean.Design.RationalStellarator
public import PlasmaLean.Theory.Fields.DefectConfinementLocal
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Field-line confinement in the rational stellarator over 95 toroidal transits

Module 4 of `notes/theory/first-stellarator-rung.md` (§2.1, §4): a certified approximate first
integral for the exact vacuum field `field (1/4)` of `Design/RationalStellarator`
(`B = ∇φ + ε ∇h`, `ε = 1/4`, two field periods, stellarator symmetric).

**Main result** (`rationalStellarator_confined_local`; `rationalStellarator_confined` for
global forward field lines). Every curve that is a field line on `[0, 750]` starting in the tube
`((x² + y² - 1)/2)² + z² ≤ (1/44)²` around the magnetic axis `R = 1, z = 0` stays in
`T = {|x² + y² - 1|/2 ≤ 1/10, |z| ≤ 1/10}` for all parameters `s ∈ [0, 750]`, and its
toroidal angle advances by `∫₀^750 (x ẏ - y ẋ)/(x² + y²) ds ≥ 600 ≥ 2π · 95`: at least
**95 toroidal transits** (`B · ∇φ ≥ 4/5` on `T`).

**Method** (Theorem A, `Fields.fieldLine_confined_of_defect`).
* `I = P(s, z, cos 2φ, sin 2φ)` (`Ifun`, scaled by `2⁴⁰`), `s = (x² + y² - 1)/2`, with `P` a
  least-squares fit of order `(10, 5)` in the stellarator-symmetric basis
  `s^j z^k {cos, sin}(nθ)`, `θ = 2φ` (data in `RationalStellaratorConfinedData`; untrusted).
* The rates of change of `s, z, C, S` along `B` are polynomials in `(s, z, C, S)` divided by
  `4 r₂²` (`rate0`–`rate3`, rational identities), so `4 r₂² DI·B = V(s, z, C, S)` with
  `V = ∑ᵢ ∂ᵢP · G4ᵢ` (`defect_formula`, via `LiePoly.hasDerivAt_eval`).
* On the half circle `C ≥ 0` the rational chart `C = (1 - t²)/(1 + t²)`, `S = 2t/(1 + t²)`,
  `|t| ≤ 1`, turns `V` into the polynomial `(1 + t²)⁶ V` in `(s, z, t)` (`ev3_Qroot`), computed
  exactly by the kernel. The half `C ≤ 0` follows from the stellarator symmetry (`V` is odd and
  `I` even under `(z, C) ↦ (-z, -C)`, `parity_all`).
* Three kernel-checked Taylor-shift covers (`Cover.check`, exact integer arithmetic):
  `|V| ≤ δ' r₂²` with `δ' = 17592186` on `|s|, |z| ≤ 1/10` (`mainGood`, 65 cells);
  `I > I_b = 4398046511` on the four faces of `T` (`face_*`); `I ≤ I_a = 1099511628` on
  `J ≤ 1/1250` (`start_cover`), with `J = s² + z² + (z² - s²) S/2 + s z C` used only as an
  S-procedure multiplier (`J ≥ (s² + z²)/2` is proved, `J_bounds`); that `J` is the quadratic
  invariant of the linearised flow (rotating ellipse, note §1.3) is motivation, not verified
  here.
* Hence `|DI·B| ≤ δ = δ'/4` on `T`, and `δ · 750 = 3298534875 < I_b - I_a = 3298534883`.
* Kernel organisation: each cover is a Boolean checker evaluated by `decide +kernel`, so the
  Taylor re-expansions are shared between a cell and its sub-cells (a per-leaf proof term would
  have to recompute or materialise every cell polynomial); the main cover is split into five
  kernel checks through external nodes (`Cover.Plan.ext`, `mainCP_good`). Clean build of the
  five certificate modules ≈ 1 min wall time, peak memory ≈ 5 GB (kernel caches; the
  largest single check is ≈ 110k elementary steps).

In physical terms (`I/2⁴⁰`): `I_b ≈ 0.004`, `I_a ≈ 0.001`, `δ ≈ 4 × 10⁻⁶`.

**Scope.** Field-line confinement over a finite length only (a worst-case linear drift bound
for an approximate first integral; no KAM tori), for the exact vacuum model field (`β = 0`),
which is singular on the `z`-axis (the line current of `∇φ`; outside `T`, where `r₂ ≥ 4/5`),
with no coils and no particle (guiding-centre) dynamics. Field lines are supplied curves (no
existence theorem is used).
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellarator.Confined
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.RationalStellarator.Cover
  PlasmaLean.Kinetic.LiePoly PlasmaLean.Fields

/-! ## Coordinates and the approximate first integral -/

/-- `s = (x² + y² - 1)/2` (`≈ R - 1` near the axis). -/
@[expose] def sc (y : Space) : ℝ := (r2 y - 1) / 2
/-- `C = cos 2φ = (x² - y²)/r₂`. -/
@[expose] def cc (y : Space) : ℝ := (y 0 ^ 2 - y 1 ^ 2) * winv y
/-- `S = sin 2φ = 2xy/r₂`. -/
@[expose] def ss (y : Space) : ℝ := 2 * y 0 * y 1 * winv y
/-- The variables `(s, z, C, S)` (zero beyond index `3`). -/
@[expose] def W (y : Space) : ℕ → ℝ := fun i => [sc y, y 2, cc y, ss y].getD i 0

/-- The first integral as a rational polynomial. -/
@[expose] def PQ : Poly := toQ Pz
/-- The rate polynomials as rational polynomials. -/
@[expose] def G4Q : List Poly := G4.map toQ

/-- **The approximate first integral** `I = P(s, z, cos 2φ, sin 2φ)` (scaled by `2⁴⁰`). -/
@[expose] def Ifun (y : Space) : ℝ := eval PQ (W y)

/-- The defect polynomial `V = ∑ᵢ ∂ᵢP · G4ᵢ` as a function of the variables. -/
@[expose] def Vfun (w : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, eval (pderiv PQ j) w * eval (G4Q.getD j []) w

/-- The variables vanish beyond index `3`. -/
theorem W_ge4 (y : Space) {i : ℕ} (hi : 4 ≤ i) : W y i = 0 := by
  unfold W
  rw [List.getD_eq_default _ _ (by simpa using hi)]

/-- `C² + S² = 1` off the `z`-axis. -/
theorem cc_sq_add_ss_sq (y : Space) (hy : r2 y ≠ 0) : cc y ^ 2 + ss y ^ 2 = 1 := by
  have hw : winv y = (y 0 ^ 2 + y 1 ^ 2)⁻¹ := rfl
  have hr : r2 y = y 0 ^ 2 + y 1 ^ 2 := rfl
  rw [hr] at hy
  simp only [cc, ss, hw]
  field_simp
  ring

/-! ## Derivatives of the coordinates -/

/-- Derivative of `f` along the straight line `r ↦ x + (r K) v` at `r = 0`. -/
theorem curve_hasDerivAt {f : Space → ℝ} {L : Space →L[ℝ] ℝ} {x : Space}
    (hf : HasFDerivAt f L x) (K : ℝ) (v : Space) :
    HasDerivAt (fun r : ℝ => f (x + (r * K) • v)) (K * L v) 0 := by
  have hc : HasDerivAt (fun r : ℝ => x + (r * K) • v) (K • v) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const K).smul_const v).const_add x
    simpa using this
  have hf' : HasFDerivAt f L (x + ((0 : ℝ) * K) • v) := by simpa using hf
  have := hf'.comp_hasDerivAt (0 : ℝ) hc
  rw [map_smul, smul_eq_mul] at this
  exact this

/-- Derivative of `s`. -/
theorem hasFDerivAt_sc (x : Space) : HasFDerivAt sc (lin (x 0) (x 1) 0) x :=
  hfd (((hasFDerivAt_r2 x).sub_const 1).mul_const (1 / 2)) (fun y => by simp [sc]; ring)
    (fun v => by simp [lin_apply]; ring)

/-- Derivative of `C` off the axis. -/
theorem hasFDerivAt_cc (x : Space) (hx : r2 x ≠ 0) :
    HasFDerivAt cc (lin (2 * x 0 * winv x - (x 0 ^ 2 - x 1 ^ 2) * winv x ^ 2 * (2 * x 0))
      (-2 * x 1 * winv x - (x 0 ^ 2 - x 1 ^ 2) * winv x ^ 2 * (2 * x 1)) 0) x :=
  hfd ((((hasFDerivAt_coord x 0).pow 2).sub ((hasFDerivAt_coord x 1).pow 2)).mul
      (hasFDerivAt_winv x hx)) (fun y => rfl)
    (fun v => by simp [lin_apply, wd, cv]; ring)

/-- Derivative of `S` off the axis. -/
theorem hasFDerivAt_ss (x : Space) (hx : r2 x ≠ 0) :
    HasFDerivAt ss (lin (2 * x 1 * winv x - 2 * x 0 * x 1 * winv x ^ 2 * (2 * x 0))
      (2 * x 0 * winv x - 2 * x 0 * x 1 * winv x ^ 2 * (2 * x 1)) 0) x :=
  hfd (((((hasFDerivAt_coord x 0).const_mul 2).mul (hasFDerivAt_coord x 1))).mul
      (hasFDerivAt_winv x hx)) (fun y => rfl)
    (fun v => by simp [lin_apply, wd, cv]; ring)

/-! ## The rates of change along the field are polynomials -/

section Rates
variable (x : Space) (hx : r2 x ≠ 0)
include hx

/-- Rate of `s`: `4 r₂² (x B_x + y B_y) = G4₀(s, z, C, S)` (rational identity). -/
theorem rate0 : 4 * r2 x ^ 2 * (x 0 * field (1 / 4) x 0 + x 1 * field (1 / 4) x 1) =
    eval (toQ G4_0) (W x) := by
  obtain ⟨e0, e1, e2⟩ := field_apply (1 / 4) x
  rw [e0, e1]
  simp only [G4_0, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, W,
    List.getD_cons_zero, List.getD_cons_succ, sc, cc, ss]
  simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hw : winv x = (x 0 ^ 2 + x 1 ^ 2)⁻¹ := rfl
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have hx' : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hx
  rw [hw, hr]
  field_simp
  push_cast
  ring

/-- Rate of `z`: `4 r₂² B_z = G4₁(s, z, C, S)`. -/
theorem rate1 : 4 * r2 x ^ 2 * field (1 / 4) x 2 = eval (toQ G4_1) (W x) := by
  obtain ⟨e0, e1, e2⟩ := field_apply (1 / 4) x
  rw [e2]
  simp only [G4_1, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, W,
    List.getD_cons_zero, List.getD_cons_succ, sc, cc, ss]
  simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have hw : winv x = (x 0 ^ 2 + x 1 ^ 2)⁻¹ := rfl
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have hx' : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hx
  rw [hw, hr]
  field_simp
  push_cast
  ring

/-- Rate of `C`: `4 r₂² DC·B = G4₂(s, z, C, S)`. -/
theorem rate2 : 4 * r2 x ^ 2 * ((2 * x 0 * winv x - (x 0 ^ 2 - x 1 ^ 2) * winv x ^ 2 * (2 * x 0)) *
      field (1 / 4) x 0 + (-2 * x 1 * winv x - (x 0 ^ 2 - x 1 ^ 2) * winv x ^ 2 * (2 * x 1)) *
      field (1 / 4) x 1) = eval (toQ G4_2) (W x) := by
  obtain ⟨e0, e1, e2⟩ := field_apply (1 / 4) x
  rw [e0, e1]
  simp only [G4_2, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, W,
    List.getD_cons_zero, List.getD_cons_succ, sc, cc, ss]
  simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hw : winv x = (x 0 ^ 2 + x 1 ^ 2)⁻¹ := rfl
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have hx' : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hx
  rw [hw, hr]
  field_simp
  push_cast
  ring

/-- Rate of `S`: `4 r₂² DS·B = G4₃(s, z, C, S)`. -/
theorem rate3 : 4 * r2 x ^ 2 * ((2 * x 1 * winv x - 2 * x 0 * x 1 * winv x ^ 2 * (2 * x 0)) *
      field (1 / 4) x 0 + (2 * x 0 * winv x - 2 * x 0 * x 1 * winv x ^ 2 * (2 * x 1)) *
      field (1 / 4) x 1) = eval (toQ G4_3) (W x) := by
  obtain ⟨e0, e1, e2⟩ := field_apply (1 / 4) x
  rw [e0, e1]
  simp only [G4_3, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, W,
    List.getD_cons_zero, List.getD_cons_succ, sc, cc, ss]
  simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hw : winv x = (x 0 ^ 2 + x 1 ^ 2)⁻¹ := rfl
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have hx' : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hx
  rw [hw, hr]
  field_simp
  push_cast
  ring

end Rates

/-- Derivatives of the variables along the rescaled line `r ↦ x + (4 r₂² r) B(x)`. -/
theorem hasDerivAt_W (x : Space) (hx : r2 x ≠ 0) (i : ℕ) :
    HasDerivAt (fun r : ℝ => W (x + (r * (4 * r2 x ^ 2)) • field (1 / 4) x) i)
      (eval (G4Q.getD i []) (W x)) 0 := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · have := curve_hasDerivAt (hasFDerivAt_sc x) (4 * r2 x ^ 2) (field (1 / 4) x)
      simp only [lin_apply, zero_mul, add_zero] at this
      rw [rate0 x hx] at this
      simpa [W, G4Q, G4] using this
    · have := curve_hasDerivAt (hasFDerivAt_coord x 2) (4 * r2 x ^ 2) (field (1 / 4) x)
      rw [show (pr 2) (field (1 / 4) x) = field (1 / 4) x 2 from rfl, rate1 x hx] at this
      simpa [W, G4Q, G4] using this
    · have := curve_hasDerivAt (hasFDerivAt_cc x hx) (4 * r2 x ^ 2) (field (1 / 4) x)
      simp only [lin_apply, zero_mul, add_zero] at this
      rw [rate2 x hx] at this
      simpa [W, G4Q, G4] using this
    · have := curve_hasDerivAt (hasFDerivAt_ss x hx) (4 * r2 x ^ 2) (field (1 / 4) x)
      simp only [lin_apply, zero_mul, add_zero] at this
      rw [rate3 x hx] at this
      simpa [W, G4Q, G4] using this
  · have h1 : (fun r : ℝ => W (x + (r * (4 * r2 x ^ 2)) • field (1 / 4) x) i) = fun _ => 0 :=
      funext fun r => W_ge4 _ hi
    have h2 : G4Q.getD i [] = [] := List.getD_eq_default _ _ (by simp [G4Q, G4]; omega)
    rw [h1, h2]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-! ## Differentiability and the defect formula -/

/-- Monomials in differentiable variables are differentiable. -/
theorem differentiableAt_evalMono (e : List ℕ) {X : Space → ℕ → ℝ} {x : Space}
    (hX : ∀ i, DifferentiableAt ℝ (fun y => X y i) x) :
    DifferentiableAt ℝ (fun y => evalMono e (X y)) x := by
  induction e generalizing X with
  | nil => simp [evalMono]
  | cons k e ih =>
    simp only [evalMono]
    exact ((hX 0).pow k).mul (ih (X := fun y i => X y (i + 1)) (fun i => hX (i + 1)))

/-- Polynomials in differentiable variables are differentiable. -/
theorem differentiableAt_eval (p : Poly) {X : Space → ℕ → ℝ} {x : Space}
    (hX : ∀ i, DifferentiableAt ℝ (fun y => X y i) x) :
    DifferentiableAt ℝ (fun y => eval p (X y)) x := by
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [eval_cons]
    exact ((differentiableAt_evalMono t.2 hX).const_mul _).add ih

/-- The variables are differentiable off the axis. -/
theorem differentiableAt_W (x : Space) (hx : r2 x ≠ 0) (i : ℕ) :
    DifferentiableAt ℝ (fun y => W y i) x := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · exact (hasFDerivAt_sc x).differentiableAt
    · exact (hasFDerivAt_coord x 2).differentiableAt
    · exact (hasFDerivAt_cc x hx).differentiableAt
    · exact (hasFDerivAt_ss x hx).differentiableAt
  · have : (fun y => W y i) = fun _ => 0 := funext fun y => W_ge4 y hi
    rw [this]; exact differentiableAt_const _

/-- The first integral is differentiable off the axis. -/
theorem differentiableAt_Ifun (x : Space) (hx : r2 x ≠ 0) : DifferentiableAt ℝ Ifun x :=
  differentiableAt_eval PQ (differentiableAt_W x hx)

/-- **The defect formula**: `4 r₂² DI·B = V(s, z, C, S)`. -/
theorem defect_formula (x : Space) (hx : r2 x ≠ 0) :
    4 * r2 x ^ 2 * fderiv ℝ Ifun x (field (1 / 4) x) = Vfun (W x) := by
  set K := 4 * r2 x ^ 2
  have h1 := hasDerivAt_eval PQ G4Q (X := fun r => W (x + (r * K) • field (1 / 4) x)) (t := 0)
    (fun i => by simpa using hasDerivAt_W x hx i)
  have h2 := curve_hasDerivAt (differentiableAt_Ifun x hx).hasFDerivAt K (field (1 / 4) x)
  have h3 := h2.unique h1
  simp only [zero_mul, zero_smul, add_zero] at h3
  rw [h3, lie, eval_lieAux]
  simp [Vfun, G4Q, G4]


/-! ## The chart `C ≥ 0` and the main cover -/

/-- Variables `[s, z, C, S]`. -/
@[expose] def vars4 (s z C S : ℝ) : ℕ → ℝ := fun i => [s, z, C, S].getD i 0

/-- `W` in terms of `vars4`. -/
theorem W_eq_vars4 (y : Space) : W y = vars4 (sc y) (y 2) (cc y) (ss y) := rfl

/-- Every point of the half circle `C ≥ 0` is `(C(t), S(t))` for some `|t| ≤ 1`. -/
theorem chart_point {C S : ℝ} (h : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C) :
    ∃ t : ℝ, |t| ≤ 1 ∧ (1 : ℤ) * (1 - t ^ 2) / (1 + t ^ 2) = C ∧
      (1 : ℤ) * (2 * t) / (1 + t ^ 2) = S := by
  have h1 : 0 < 1 + C := by linarith
  refine ⟨S / (1 + C), ?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos h1, div_le_one h1, abs_le]
    constructor <;> nlinarith [sq_nonneg (S + 1 + C), sq_nonneg (S - 1 - C)]
  · have : (1 + (S / (1 + C)) ^ 2) = 2 / (1 + C) := by
      field_simp; nlinarith
    rw [this]; simp only [Int.cast_one, one_mul]; field_simp; nlinarith
  · have : (1 + (S / (1 + C)) ^ 2) = 2 / (1 + C) := by
      field_simp; nlinarith
    rw [this]; simp only [Int.cast_one, one_mul]; field_simp

/-- The chart variables at the chart parameter of `(C, S)`. -/
theorem chartVars_eq {s z t C S : ℝ} (hC : (1 : ℤ) * (1 - t ^ 2) / (1 + t ^ 2) = C)
    (hS : (1 : ℤ) * (2 * t) / (1 + t ^ 2) = S) : chartVars 1 s z t = vars4 s z C S := by
  funext i
  simp only [chartVars, vars4]
  rw [hC, hS]

/-- Admissibility of the sparse polynomials for the charts (kernel check). -/
theorem chartOK_all : (chartOK 5 (pderivZ Pz 0) && chartOK 1 G4_0 && chartOK 5 (pderivZ Pz 1) &&
    chartOK 1 G4_1 && chartOK 4 (pderivZ Pz 2) && chartOK 2 G4_2 && chartOK 4 (pderivZ Pz 3) &&
    chartOK 2 G4_3) = true := by
  decide +kernel

/-- The chart of the defect is `(1 + t²)⁶ V`. -/
theorem ev3_Qroot (s z t : ℝ) : ev3 Qroot s z t = (1 + t ^ 2) ^ 6 * Vfun (chartVars 1 s z t) := by
  have h := chartOK_all
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, g0⟩, h1⟩, g1⟩, h2⟩, g2⟩, h3⟩, g3⟩ := h
  have hs : (1 : ℤ) ^ 2 = 1 := by norm_num
  unfold Qroot
  simp only [ev3_add3, ev3_mul3, ev3_chartD _ _ hs _ h0, ev3_chartD _ _ hs _ g0,
    ev3_chartD _ _ hs _ h1, ev3_chartD _ _ hs _ g1, ev3_chartD _ _ hs _ h2,
    ev3_chartD _ _ hs _ g2, ev3_chartD _ _ hs _ h3, ev3_chartD _ _ hs _ g3, toQ_pderivZ]
  simp only [Vfun, Finset.sum_range_succ, Finset.sum_range_zero, G4Q, G4, PQ, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- Value of the rescaled defect chart. -/
theorem ev3_Alit (σ ζ τ : ℝ) :
    ev3 Alit σ ζ τ =
      (10 : ℝ) ^ 25 * ((1 + τ ^ 2) ^ 6 * Vfun (chartVars 1 (σ / 10) (ζ / 10) τ)) := by
  have h := Alit_eq
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  simp only [lenOK, decide_eq_true_eq, List.all_eq_true] at h0 h1
  rw [← ev3_beq3 _ _ h2, ev3_scale0 10 12 (by norm_num) _ (by simpa [scale1] using h0),
    ev3_scale1 10 13 (by norm_num) _ h1, ev3_Qroot]
  push_cast
  ring

/-- Value of the bound polynomial. -/
theorem ev3_Dlit (σ ζ τ : ℝ) :
    ev3 Dlit σ ζ τ = 17592186 * (10 : ℝ) ^ 25 * (1 + 2 * (σ / 10)) ^ 2 * (1 + τ ^ 2) ^ 6 := by
  simp only [Dlit, ev3, ev2, evL_cons, evL_nil, ev1_smul1, ev1_onePlusSq]
  push_cast
  ring

/-- **Defect bound in the chart `C ≥ 0`.** -/
theorem V_bound_pos {s z C S : ℝ} (hs : |s| ≤ 1 / 10) (hz : |z| ≤ 1 / 10)
    (hCS : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C) :
    |Vfun (vars4 s z C S)| ≤ 17592186 * (1 + 2 * s) ^ 2 := by
  obtain ⟨t, ht, hCt, hSt⟩ := chart_point hCS hC
  have hσ : |10 * s| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have hζ : |10 * z| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have h := mainGood (10 * s) (10 * z) t hσ hζ ht
  simp only [ite_true, Nat.cast_zero, add_zero] at h
  rw [ev3_Alit, ev3_Dlit] at h
  have e1 : 10 * s / 10 = s := by ring
  have e2 : 10 * z / 10 = z := by ring
  rw [e1, e2, chartVars_eq hCt hSt] at h
  have hpos : (0 : ℝ) < (10 : ℝ) ^ 25 * (1 + t ^ 2) ^ 6 := by positivity
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 10 ^ 25),
    abs_of_pos (by positivity : (0 : ℝ) < (1 + t ^ 2) ^ 6)] at h
  have : (10 : ℝ) ^ 25 * (1 + t ^ 2) ^ 6 * |Vfun (vars4 s z C S)| ≤
      (10 : ℝ) ^ 25 * (1 + t ^ 2) ^ 6 * (17592186 * (1 + 2 * s) ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left this hpos

/-! ## Stellarator symmetry: parity of the polynomials -/

/-- All monomials `s^j z^k C^a S^b` have `k + a ≡ π (mod 2)` (and at most four exponents). -/
@[expose] def parityOK (π : ℕ) (p : FPoly) : Bool :=
  p.all fun t => decide (t.2.length ≤ 4) && decide ((t.2.getD 1 0 + t.2.getD 2 0) % 2 = π)

/-- Parity under stellarator symmetry `(z, C) ↦ (-z, -C)`. -/
theorem eval_reflect (π : ℕ) (p : FPoly) (h : parityOK π p = true) (s z C S : ℝ) :
    eval (toQ p) (vars4 s (-z) (-C) S) = (-1) ^ π * eval (toQ p) (vars4 s z C S) := by
  unfold parityOK at h
  rw [List.all_eq_true] at h
  induction p with
  | nil => simp [toQ]
  | cons u p ih =>
    have hu := h u (by simp)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    simp only [toQ, List.map_cons, eval_cons] at ih ⊢
    rw [ih (fun x hx => h x (by simp [hx])), evalMono_four _ hu.1, evalMono_four _ hu.1]
    simp only [vars4, List.getD_cons_zero, List.getD_cons_succ]
    have key : (-z) ^ u.2.getD 1 0 * (-C) ^ u.2.getD 2 0 =
        (-1) ^ π * (z ^ u.2.getD 1 0 * C ^ u.2.getD 2 0) := by
      rw [neg_pow, neg_pow, ← hu.2]
      rw [show (-1 : ℝ) ^ ((u.2.getD 1 0 + u.2.getD 2 0) % 2) =
        (-1) ^ (u.2.getD 1 0 + u.2.getD 2 0) from
          (neg_one_pow_eq_pow_mod_two (R := ℝ) _).symm, pow_add]
      ring
    rw [show s ^ u.2.getD 0 0 * (-z) ^ u.2.getD 1 0 * (-C) ^ u.2.getD 2 0 * S ^ u.2.getD 3 0 =
      s ^ u.2.getD 0 0 * ((-z) ^ u.2.getD 1 0 * (-C) ^ u.2.getD 2 0) * S ^ u.2.getD 3 0 by ring,
      key]
    ring

/-- Parities of `P`, its partial derivatives, the rates and `J` (kernel check). -/
theorem parity_all : (parityOK 0 Pz && parityOK 0 (pderivZ Pz 0) && parityOK 1 (pderivZ Pz 1) &&
    parityOK 1 (pderivZ Pz 2) && parityOK 0 (pderivZ Pz 3) && parityOK 1 G4_0 &&
    parityOK 0 G4_1 && parityOK 0 G4_2 && parityOK 1 G4_3 && parityOK 0 J2) = true := by
  decide +kernel

/-- The defect polynomial is odd under the stellarator symmetry. -/
theorem Vfun_reflect (s z C S : ℝ) : Vfun (vars4 s (-z) (-C) S) = -Vfun (vars4 s z C S) := by
  have h := parity_all
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h0⟩, h1⟩, h2⟩, h3⟩, g0⟩, g1⟩, g2⟩, g3⟩, _⟩ := h
  simp only [Vfun, Finset.sum_range_succ, Finset.sum_range_zero, G4Q, G4, PQ, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, ← toQ_pderivZ]
  rw [eval_reflect _ _ h0, eval_reflect _ _ h1, eval_reflect _ _ h2, eval_reflect _ _ h3,
    eval_reflect _ _ g0, eval_reflect _ _ g1, eval_reflect _ _ g2, eval_reflect _ _ g3]
  ring

/-- The first integral is even under the stellarator symmetry. -/
theorem Ifun_reflect (s z C S : ℝ) :
    eval PQ (vars4 s (-z) (-C) S) = eval PQ (vars4 s z C S) := by
  have h := parity_all
  simp only [Bool.and_eq_true] at h
  rw [PQ, eval_reflect 0 Pz h.1.1.1.1.1.1.1.1.1]
  ring

/-- **Defect bound on the whole tube** (both halves of the circle). -/
theorem V_bound {s z C S : ℝ} (hs : |s| ≤ 1 / 10) (hz : |z| ≤ 1 / 10) (hCS : C ^ 2 + S ^ 2 = 1) :
    |Vfun (vars4 s z C S)| ≤ 17592186 * (1 + 2 * s) ^ 2 := by
  rcases le_total 0 C with hC | hC
  · exact V_bound_pos hs hz hCS hC
  · have := V_bound_pos (s := s) (z := -z) (C := -C) (S := S) hs (by rwa [abs_neg])
      (by rw [neg_sq]; exact hCS) (by linarith)
    rwa [Vfun_reflect, abs_neg] at this


/-! ## The boundary of the tube -/

set_option maxRecDepth 100000 in
/-- Admissibility and degree bounds for the chart of `P` (kernel check). -/
theorem chartOK_Pz : (chartOK 5 Pz && lenOK 0 10 (chartD 5 1 Pz) &&
    lenOK 1 10 (chartD 5 1 Pz)) = true := by
  decide +kernel

/-- Value of the rescaled chart of the first integral. -/
theorem ev3_Ichart (σ ζ τ : ℝ) :
    ev3 Ichart σ ζ τ = (10 : ℝ) ^ 20 * ((1 + τ ^ 2) ^ 5 *
      eval PQ (chartVars 1 (σ / 10) (ζ / 10) τ)) := by
  have h := chartOK_Pz
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  simp only [lenOK, decide_eq_true_eq, List.all_eq_true] at h1 h2
  rw [Ichart, ev3_scale0 10 10 (by norm_num) _ (by simpa [scale1] using h1),
    ev3_scale1 10 10 (by norm_num) _ h2, ev3_chartD 5 1 (by norm_num) _ h0, PQ]
  push_cast
  ring

/-- Value of the constant polynomial `I_b 10²⁰ (1 + τ²)⁵`. -/
theorem ev3_IbPoly (σ ζ τ : ℝ) :
    ev3 IbPoly σ ζ τ = 4398046511 * (10 : ℝ) ^ 20 * (1 + τ ^ 2) ^ 5 := by
  simp only [IbPoly, ev3, ev2, evL_cons, evL_nil, ev1_smul1, ev1_onePlusSq]
  push_cast
  ring

/-- From a face certificate: `I_b < I` at the corresponding points. -/
theorem face_consequence {F : D3} {dd : ℕ × ℕ × ℕ} {p : Plan}
    (h : check false dd [] p (add3 IbPoly (neg3 F)) [[[-1]]] 0 = true)
    (σ ζ τ : ℝ) (hσ : |σ| ≤ 1) (hζ : |ζ| ≤ 1) (hτ : |τ| ≤ 1) :
    4398046511 * (10 : ℝ) ^ 20 * (1 + τ ^ 2) ^ 5 + 1 ≤ ev3 F σ ζ τ := by
  have hg := check_sound (by simp) p _ _ _ h σ ζ τ hσ hζ hτ
  simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, add_zero, ev3_add3, ev3_neg3,
    ev3_IbPoly] at hg
  have : ev3 [[[(-1 : ℤ)]]] σ ζ τ = -1 := by simp [ev3, ev2, ev1]
  rw [this] at hg
  linarith

/-- Faces of the tube, chart `C ≥ 0`. -/
theorem I_face_pos {s z C S : ℝ} (hs : |s| ≤ 1 / 10) (hz : |z| ≤ 1 / 10)
    (hCS : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C)
    (hf : s = 1 / 10 ∨ s = -1 / 10 ∨ z = 1 / 10 ∨ z = -1 / 10) :
    4398046511 < eval PQ (vars4 s z C S) := by
  obtain ⟨t, ht, hCt, hSt⟩ := chart_point hCS hC
  have hσ : |10 * s| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have hζ : |10 * z| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have hpos : (0 : ℝ) < (10 : ℝ) ^ 20 * (1 + t ^ 2) ^ 5 := by positivity
  have key : ∀ σ ζ : ℝ, σ / 10 = s → ζ / 10 = z →
      4398046511 * (10 : ℝ) ^ 20 * (1 + t ^ 2) ^ 5 + 1 ≤ ev3 Ichart σ ζ t →
      4398046511 < eval PQ (vars4 s z C S) := by
    intro σ ζ h1 h2 h
    rw [ev3_Ichart, h1, h2, chartVars_eq hCt hSt] at h
    by_contra hn
    push Not at hn
    have : (10 : ℝ) ^ 20 * ((1 + t ^ 2) ^ 5 * eval PQ (vars4 s z C S)) ≤
        (10 : ℝ) ^ 20 * ((1 + t ^ 2) ^ 5 * 4398046511) := by
      gcongr
    linarith
  rcases hf with h | h | h | h
  · refine key 1 (10 * z) (by rw [h]) (by ring) ?_
    have := face_consequence face_sPos 0 (10 * z) t (by norm_num) hζ ht
    rwa [ev3_restrict0] at this
  · refine key (-1) (10 * z) (by rw [h]) (by ring) ?_
    have := face_consequence face_sNeg 0 (10 * z) t (by norm_num) hζ ht
    rwa [ev3_restrict0] at this
  · refine key (10 * s) 1 (by ring) (by rw [h]) ?_
    have := face_consequence face_zPos (10 * s) 0 t hσ (by norm_num) ht
    rwa [ev3_restrict1] at this
  · refine key (10 * s) (-1) (by ring) (by rw [h]) ?_
    have := face_consequence face_zNeg (10 * s) 0 t hσ (by norm_num) ht
    rwa [ev3_restrict1] at this

/-- **On the faces of the tube**, `I > I_b`. -/
theorem I_face {s z C S : ℝ} (hs : |s| ≤ 1 / 10) (hz : |z| ≤ 1 / 10) (hCS : C ^ 2 + S ^ 2 = 1)
    (hf : s = 1 / 10 ∨ s = -1 / 10 ∨ z = 1 / 10 ∨ z = -1 / 10) :
    4398046511 < eval PQ (vars4 s z C S) := by
  rcases le_total 0 C with hC | hC
  · exact I_face_pos hs hz hCS hC hf
  · rw [← Ifun_reflect]
    refine I_face_pos (z := -z) (C := -C) hs (by rwa [abs_neg]) (by rw [neg_sq]; exact hCS)
      (by linarith) ?_
    rcases hf with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; norm_num)))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; norm_num)))

/-! ## The start set -/

/-- `J = s² + z² + (z² - s²) S/2 + s z C`, the S-procedure multiplier for the start set
(motivated, unverified here, as the quadratic invariant of the linearised flow). -/
@[expose] def Jfun (s z C S : ℝ) : ℝ := s ^ 2 + z ^ 2 + (z ^ 2 - s ^ 2) * S / 2 + s * z * C

/-- `(s² + z²)/2 ≤ J ≤ 3(s² + z²)/2` (the eigenvalues of the rotating ellipse). -/
theorem J_bounds {s z C S : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) :
    (s ^ 2 + z ^ 2) / 2 ≤ Jfun s z C S ∧ Jfun s z C S ≤ 3 / 2 * (s ^ 2 + z ^ 2) := by
  have key : ((z ^ 2 - s ^ 2) / 2 * S + s * z * C) ^ 2 ≤ ((s ^ 2 + z ^ 2) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((z ^ 2 - s ^ 2) / 2 * C - s * z * S)]
  have hR : 0 ≤ (s ^ 2 + z ^ 2) / 2 := by positivity
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' key hR
  unfold Jfun
  constructor <;> nlinarith

/-- Evaluation of a concatenation. -/
theorem eval_toQ_append (p q : FPoly) (w : ℕ → ℝ) :
    eval (toQ (p ++ q)) w = eval (toQ p) w + eval (toQ q) w := by
  simp [toQ, eval, List.map_append, List.sum_append]

/-- Evaluation of a scaled polynomial. -/
theorem eval_toQ_scale (k : ℤ) (p : FPoly) (w : ℕ → ℝ) :
    eval (toQ (p.map fun t => (k * t.1, t.2))) w = k * eval (toQ p) w := by
  induction p with
  | nil => simp [toQ]
  | cons u p ih =>
    simp only [toQ, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Value of the start-set polynomial. -/
theorem eval_Pstart (s z C S : ℝ) :
    eval (toQ Pstart) (vars4 s z C S) = 20000 * eval PQ (vars4 s z C S) -
      10625 * 2 ^ 40 * (2 * Jfun s z C S) + (17 * 2 ^ 40 - 20000 * 1099511628) := by
  unfold Pstart
  rw [eval_toQ_append, eval_toQ_append]
  have hJ : eval (toQ (J2.map fun t => (-(10625 * 2 ^ 40) * t.1, t.2))) (vars4 s z C S) =
      -(10625 * 2 ^ 40) * (2 * Jfun s z C S) := by
    rw [eval_toQ_scale]
    simp only [J2, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, vars4,
      List.getD_cons_zero, List.getD_cons_succ, Jfun]
    push_cast; ring
  have hP : eval (toQ (Pz.map fun t => (20000 * t.1, t.2))) (vars4 s z C S) =
      20000 * eval PQ (vars4 s z C S) := by
    rw [eval_toQ_scale, PQ]; push_cast; ring
  rw [hJ, hP]
  simp [toQ, evalMono, vars4]
  ring

set_option maxRecDepth 100000 in
/-- Admissibility and degree bounds for the chart of the start polynomial. -/
theorem chartOK_Pstart : (chartOK 5 Pstart && lenOK 0 10 (chartD 5 1 Pstart) &&
    lenOK 1 10 (chartD 5 1 Pstart)) = true := by
  decide +kernel

/-- Start set, chart `C ≥ 0` (S-procedure with multiplier `17/16`). -/
theorem I_start_pos {s z C S : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) (hC : 0 ≤ C)
    (hJ : Jfun s z C S ≤ 1 / 1250) : eval PQ (vars4 s z C S) ≤ 1099511628 := by
  obtain ⟨hJl, -⟩ := J_bounds (s := s) (z := z) hCS
  have hs : |25 * s| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, sq_nonneg (25 * s - 1), sq_nonneg (25 * s + 1)]
  have hz : |25 * z| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg (25 * z - 1), sq_nonneg (25 * z + 1)]
  obtain ⟨t, ht, hCt, hSt⟩ := chart_point hCS hC
  have h := check_sound (by simp) _ _ _ _ start_cover (25 * s) (25 * z) t hs hz ht
  simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, add_zero] at h
  have h0 : ev3 [[[(0 : ℤ)]]] (25 * s) (25 * z) t = 0 := by simp [ev3, ev2, ev1]
  have hc := chartOK_Pstart
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨c0, c1⟩, c2⟩ := hc
  simp only [lenOK, decide_eq_true_eq, List.all_eq_true] at c1 c2
  rw [h0, Schart, ev3_scale0 25 10 (by norm_num) _ (by simpa [scale1] using c1),
    ev3_scale1 25 10 (by norm_num) _ c2, ev3_chartD 5 1 (by norm_num) _ c0] at h
  have e1 : 25 * s / 25 = s := by ring
  have e2 : 25 * z / 25 = z := by ring
  push_cast at h
  rw [e1, e2, chartVars_eq hCt hSt, eval_Pstart] at h
  have hpos : (0 : ℝ) < (25 : ℝ) ^ 10 * ((25 : ℝ) ^ 10 * (1 + t ^ 2) ^ 5) := by positivity
  have h' : 20000 * eval PQ (vars4 s z C S) - 10625 * 2 ^ 40 * (2 * Jfun s z C S) +
      (17 * 2 ^ 40 - 20000 * 1099511628) ≤ 0 := by
    by_contra hn
    push Not at hn
    have := mul_pos hpos hn
    linarith
  have hJ' : 10625 * (2 : ℝ) ^ 40 * (2 * Jfun s z C S) ≤ 10625 * 2 ^ 40 * (2 * (1 / 1250)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e : (10625 : ℝ) * 2 ^ 40 * (2 * (1 / 1250)) = 17 * 2 ^ 40 := by norm_num
  rw [e] at hJ'
  linarith

/-- **On the start set** `J ≤ 1/1250`, `I ≤ I_a`. -/
theorem I_start {s z C S : ℝ} (hCS : C ^ 2 + S ^ 2 = 1) (hJ : Jfun s z C S ≤ 1 / 1250) :
    eval PQ (vars4 s z C S) ≤ 1099511628 := by
  rcases le_total 0 C with hC | hC
  · exact I_start_pos hCS hC hJ
  · rw [← Ifun_reflect]
    exact I_start_pos (z := -z) (C := -C) (by rw [neg_sq]; exact hCS) (by linarith)
      (by unfold Jfun at hJ ⊢; nlinarith)


/-! ## The tube, its boundary and the start set in space -/

/-- **The confinement region** `T = {|s| ≤ 1/10, |z| ≤ 1/10}`, `s = (x² + y² - 1)/2`:
a solid torus of square cross-section around the magnetic axis `R = 1, z = 0`. -/
@[expose] def tubeT : Set Space := {y | |sc y| ≤ 1 / 10 ∧ |y 2| ≤ 1 / 10}

/-- **The start tube** `s² + z² ≤ (1/44)²` around the magnetic axis. -/
@[expose] def startTube : Set Space := {y | sc y ^ 2 + y 2 ^ 2 ≤ (1 / 44) ^ 2}

/-- `r₂ = 1 + 2s`. -/
theorem r2_eq (y : Space) : r2 y = 1 + 2 * sc y := by unfold sc; ring

/-- The tube lies in the current-free domain `r₂ > 0`. -/
theorem r2_pos_of_tube {y : Space} (hy : y ∈ tubeT) : 0 < r2 y := by
  have := (abs_le.mp hy.1).1
  rw [r2_eq]; linarith

/-- `s` is continuous. -/
theorem continuous_sc : Continuous sc := by unfold sc r2; fun_prop

/-- The tube is closed. -/
theorem isClosed_tubeT : IsClosed tubeT :=
  (isClosed_le (continuous_abs.comp continuous_sc) continuous_const).inter
    (isClosed_le (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ => ℝ) 2)) continuous_const)

/-- The frontier of the tube lies on its four faces. -/
theorem frontier_tubeT {y : Space} (hy : y ∈ frontier tubeT) :
    y ∈ tubeT ∧ (|sc y| = 1 / 10 ∨ |y 2| = 1 / 10) := by
  have hT : y ∈ tubeT := isClosed_tubeT.frontier_subset hy
  refine ⟨hT, ?_⟩
  by_contra hn
  push Not at hn
  have hU : IsOpen {y : Space | |sc y| < 1 / 10 ∧ |y 2| < 1 / 10} :=
    (isOpen_lt (continuous_abs.comp continuous_sc) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ => ℝ) 2)) continuous_const)
  have hsub : {y : Space | |sc y| < 1 / 10 ∧ |y 2| < 1 / 10} ⊆ tubeT :=
    fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hint : y ∈ interior tubeT :=
    interior_maximal hsub hU ⟨lt_of_le_of_ne hT.1 hn.1, lt_of_le_of_ne hT.2 hn.2⟩
  exact hy.2 hint

/-- **Defect bound**: `|DI · B| ≤ δ' / 4` on the tube (`δ' = 17592186`, i.e.
`δ ≈ 4 × 10⁻⁶` for `I/2⁴⁰`). -/
theorem defect_bound {y : Space} (hy : y ∈ tubeT) :
    |fderiv ℝ Ifun y (field (1 / 4) y)| ≤ 17592186 / 4 := by
  have hr := r2_pos_of_tube hy
  have hf := defect_formula y hr.ne'
  have hV := V_bound hy.1 hy.2 (cc_sq_add_ss_sq y hr.ne')
  rw [← W_eq_vars4, ← hf, ← r2_eq, abs_mul, abs_of_pos (by positivity : 0 < 4 * r2 y ^ 2)] at hV
  have hpos : 0 < 4 * r2 y ^ 2 := by positivity
  have : 4 * r2 y ^ 2 * |fderiv ℝ Ifun y (field (1 / 4) y)| ≤ 4 * r2 y ^ 2 * (17592186 / 4) := by
    linarith
  exact le_of_mul_le_mul_left this hpos

/-- **The first integral exceeds `I_b` on the boundary of the tube.** -/
theorem front_bound {y : Space} (hy : y ∈ frontier tubeT) : 4398046511 < Ifun y := by
  obtain ⟨hT, hf⟩ := frontier_tubeT hy
  have hr := r2_pos_of_tube hT
  unfold Ifun
  rw [W_eq_vars4]
  refine I_face hT.1 hT.2 (cc_sq_add_ss_sq y hr.ne') ?_
  rcases hf with h | h
  · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 10) |>.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (by rw [h']; norm_num))
  · rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 10) |>.mp h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (by rw [h']; norm_num)))

/-- The start tube lies in the confinement tube. -/
theorem startTube_sub {y : Space} (hy : y ∈ startTube) : y ∈ tubeT := by
  have h : sc y ^ 2 + y 2 ^ 2 ≤ (1 / 44) ^ 2 := hy
  refine ⟨abs_le.mpr ⟨by nlinarith [sq_nonneg (y 2)], by nlinarith [sq_nonneg (y 2)]⟩,
    abs_le.mpr ⟨by nlinarith [sq_nonneg (sc y)], by nlinarith [sq_nonneg (sc y)]⟩⟩

/-- **The first integral is at most `I_a` on the start tube.** -/
theorem start_bound {y : Space} (hy : y ∈ startTube) : Ifun y ≤ 1099511628 := by
  have hT := startTube_sub hy
  have hr := r2_pos_of_tube hT
  have hCS := cc_sq_add_ss_sq y hr.ne'
  unfold Ifun
  rw [W_eq_vars4]
  refine I_start hCS ?_
  have := (J_bounds (s := sc y) (z := y 2) hCS).2
  have h : sc y ^ 2 + y 2 ^ 2 ≤ (1 / 44) ^ 2 := hy
  nlinarith

/-! ## Toroidal advance -/

/-- The toroidal rate `dφ/ds = B · ∇φ = (x B_y - y B_x)/r₂` along field lines. -/
@[expose] def phiRate (y : Space) : ℝ := (y 0 * field (1 / 4) y 1 - y 1 * field (1 / 4) y 0) / r2 y

/-- `4 r₂² B · ∇φ = 4 + 8s + 2 N_θ` with `N_θ = b C - a S`. -/
@[expose] def Gphi : FPoly :=
  [(4, [0, 0, 0, 0]), (8, [1, 0, 0, 0]), (-2, [2, 1, 1, 0]), (4, [1, 1, 1, 0]),
    (2, [0, 3, 1, 0]), (-2, [2, 0, 0, 1]), (2, [0, 2, 0, 1])]

/-- `4 r₂ (x B_y - y B_x) = Gphi(s, z, C, S)` (rational identity). -/
theorem ratePhi (x : Space) (hx : r2 x ≠ 0) :
    4 * r2 x * (x 0 * field (1 / 4) x 1 - x 1 * field (1 / 4) x 0) = eval (toQ Gphi) (W x) := by
  obtain ⟨e0, e1, e2⟩ := field_apply (1 / 4) x
  rw [e0, e1]
  simp only [Gphi, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, W,
    List.getD_cons_zero, List.getD_cons_succ, sc, cc, ss]
  simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hw : winv x = (x 0 ^ 2 + x 1 ^ 2)⁻¹ := rfl
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  have hx' : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := hx
  rw [hw, hr]
  field_simp
  push_cast
  ring

/-- `Gphi ≥ (16/5) r₂²` on the tube. -/
theorem Gphi_lower {s z C S : ℝ} (hs : |s| ≤ 1 / 10) (hz : |z| ≤ 1 / 10)
    (hCS : C ^ 2 + S ^ 2 = 1) : 16 / 5 * (1 + 2 * s) ^ 2 ≤ eval (toQ Gphi) (vars4 s z C S) := by
  simp only [Gphi, toQ, List.map_cons, List.map_nil, eval_cons, eval_nil, evalMono, vars4,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  have hC : |C| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg S, sq_nonneg (C + 1), sq_nonneg (C - 1)]
  have hS : |S| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg C, sq_nonneg (S + 1), sq_nonneg (S - 1)]
  have hs' := abs_le.mp hs
  have hz' := abs_le.mp hz
  have b1 : |s ^ 2 * z * C| ≤ 1 / 1000 := by
    rw [abs_mul, abs_mul, abs_pow]
    calc |s| ^ 2 * |z| * |C| ≤ (1 / 10) ^ 2 * (1 / 10) * 1 := by gcongr
      _ = 1 / 1000 := by norm_num
  have b2 : |s * z * C| ≤ 1 / 100 := by
    rw [abs_mul, abs_mul]
    calc |s| * |z| * |C| ≤ (1 / 10) * (1 / 10) * 1 := by gcongr
      _ = 1 / 100 := by norm_num
  have b3 : |z ^ 3 * C| ≤ 1 / 1000 := by
    rw [abs_mul, abs_pow]
    calc |z| ^ 3 * |C| ≤ (1 / 10) ^ 3 * 1 := by gcongr
      _ = 1 / 1000 := by norm_num
  have b4 : |s ^ 2 * S| ≤ 1 / 100 := by
    rw [abs_mul, abs_pow]
    calc |s| ^ 2 * |S| ≤ (1 / 10) ^ 2 * 1 := by gcongr
      _ = 1 / 100 := by norm_num
  have b5 : |z ^ 2 * S| ≤ 1 / 100 := by
    rw [abs_mul, abs_pow]
    calc |z| ^ 2 * |S| ≤ (1 / 10) ^ 2 * 1 := by gcongr
      _ = 1 / 100 := by norm_num
  have c1 := (abs_le.mp b1).1
  have c2 := (abs_le.mp b2).1
  have c3 := (abs_le.mp b3).1
  have c4 := (abs_le.mp b4).2
  have c5 := (abs_le.mp b5).1
  nlinarith

/-- **`B · ∇φ ≥ 4/5` on the tube.** -/
theorem phiRate_lower {y : Space} (hy : y ∈ tubeT) : 4 / 5 ≤ phiRate y := by
  have hr := r2_pos_of_tube hy
  have h1 := ratePhi y hr.ne'
  have h2 := Gphi_lower hy.1 hy.2 (cc_sq_add_ss_sq y hr.ne')
  rw [← W_eq_vars4, ← h1, ← r2_eq] at h2
  unfold phiRate
  rw [le_div_iff₀ hr]
  nlinarith

/-- `phiRate` is continuous off the axis. -/
theorem continuousAt_phiRate {y : Space} (hy : 0 < r2 y) : ContinuousAt phiRate y := by
  have hB : ContinuousAt (field (1 / 4)) y :=
    (field_contDiffOn (1 / 4)).continuousOn.continuousAt (isOpen_domain.mem_nhds hy)
  have h0 : ContinuousAt (fun z : Space => field (1 / 4) z 0) y :=
    ((PiLp.continuous_apply 2 _ 0).continuousAt).comp hB
  have h1 : ContinuousAt (fun z : Space => field (1 / 4) z 1) y :=
    ((PiLp.continuous_apply 2 _ 1).continuousAt).comp hB
  have hr : ContinuousAt r2 y := by unfold r2; fun_prop
  unfold phiRate
  exact ((((PiLp.continuous_apply 2 _ 0).continuousAt).mul h1).sub
    (((PiLp.continuous_apply 2 _ 1).continuousAt).mul h0)).div hr hy.ne'


/-! ## Main theorem -/

/-- Confinement in `T` for the parameter range `[0, 750]` (first-exit argument,
`Fields.fieldLine_confined_of_defect_local` with
`I_b - I_a = 3298534883 > 750 δ = 3298534875`), for a curve that is a field line on `[0, 750]`. -/
theorem confined_tube_local {γ : ℝ → Space}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 750, HasDerivAt γ (field (1 / 4) (γ t)) t)
    (h0 : γ 0 ∈ startTube) : ∀ s ∈ Set.Icc (0 : ℝ) 750, γ s ∈ tubeT := by
  have h := fieldLine_confined_of_defect_local (B := field (1 / 4)) (I := Ifun) (T := tubeT)
    (Ia := 1099511628) (Ib := 4398046511) (δ := 17592186 / 4) (by norm_num) isClosed_tubeT
    (fun x hx => differentiableAt_Ifun x (r2_pos_of_tube hx).ne') (fun x hx => front_bound hx)
    (fun x hx _ => defect_bound hx) hγ (startTube_sub h0) (start_bound h0)
  intro s hs
  exact (h s hs (by nlinarith [hs.2])).1

/-- Along a field line, `phiRate (γ u)` is the derivative of the toroidal angle:
`(x ẏ - y ẋ)/(x² + y²)`. -/
theorem phiRate_eq_deriv {γ : ℝ → Space} {u : ℝ}
    (hγ : HasDerivAt γ (field (1 / 4) (γ u)) u) :
    phiRate (γ u) = (γ u 0 * deriv (fun v => γ v 1) u - γ u 1 * deriv (fun v => γ v 0) u) /
      r2 (γ u) := by
  have hd : ∀ i : Fin 3, deriv (fun v => γ v i) u = field (1 / 4) (γ u) i := fun i =>
    (((PiLp.proj 2 (fun _ => ℝ) i : Space →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt u hγ).deriv
  rw [hd 0, hd 1]
  rfl

/-- **Rational stellarator field lines are confined over 95 toroidal transits** (local form).

For the exact vacuum field `B = ∇φ + ε ∇h`, `ε = 1/4` (`field (1/4)`, two field periods,
stellarator symmetric, `RationalStellarator.field_vacuum`), every curve `γ` with `γ' = B(γ)` on
`[0, 750]` (no global existence is assumed) starting in the tube
`((x² + y² - 1)/2)² + z² ≤ (1/44)²` around the magnetic axis `R = 1, z = 0`

* stays in the tube `T = {|x² + y² - 1|/2 ≤ 1/10, |z| ≤ 1/10}` for all `s ∈ [0, 750]`, and
* winds around the `z`-axis: its toroidal angle advances by
  `∫₀^750 (x ẏ - y ẋ)/(x² + y²) ds ≥ 600 ≥ 2π · 95`, i.e. at least **95 toroidal transits**
  (`B · ∇φ ≥ 4/5` on `T`, `phiRate_eq_deriv`).

Scope: field-line confinement over a finite length (worst-case drift bound
`|dI/ds| ≤ δ` for a certified approximate first integral `I`); vacuum field, no coils, no
KAM tori, no particle drifts. -/
theorem rationalStellarator_confined_local {γ : ℝ → Space}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 750, HasDerivAt γ (field (1 / 4) (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 750, γ s ∈ tubeT) ∧
      2 * Real.pi * 95 ≤ ∫ u in (0 : ℝ)..750, phiRate (γ u) := by
  have hT := confined_tube_local hγ h0
  refine ⟨hT, ?_⟩
  have hcont : ContinuousOn (fun u => phiRate (γ u)) (Set.Icc 0 750) := fun u hu =>
    ((continuousAt_phiRate (r2_pos_of_tube (hT u hu))).comp
      (hγ u hu).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable (fun u => phiRate (γ u)) MeasureTheory.volume 0 750 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 750)
    (intervalIntegrable_const (c := (4 / 5 : ℝ))) hint (fun u hu => phiRate_lower (hT u hu))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  have hpi := Real.pi_lt_d2
  nlinarith

/-- **Rational stellarator field lines are confined over 95 toroidal transits**: the corollary
of `rationalStellarator_confined_local` for forward field lines (`IsForwardFieldLine`). -/
theorem rationalStellarator_confined {γ : ℝ → Space} (hγ : IsForwardFieldLine (field (1 / 4)) γ)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 750, γ s ∈ tubeT) ∧
      2 * Real.pi * 95 ≤ ∫ u in (0 : ℝ)..750, phiRate (γ u) :=
  rationalStellarator_confined_local (fun t ht => hγ t ht.1) h0

/-! ## Sanity checks -/

/-- The magnetic axis lies in the start tube. -/
theorem axis_mem_startTube (t : ℝ) : axis t ∈ startTube := by
  have hr : r2 (axis t) = 1 := by simp [r2, axis, Real.cos_sq_add_sin_sq]
  have hs : sc (axis t) = 0 := by rw [sc, hr]; norm_num
  have hz : axis t 2 = 0 := by simp [axis]
  have : sc (axis t) ^ 2 + axis t 2 ^ 2 ≤ (1 / 44) ^ 2 := by rw [hs, hz]; norm_num
  exact this

/-- Non-vacuous instance: the magnetic axis (an exact field line, `axis_fieldLine`) satisfies
the hypotheses, hence the conclusion of `rationalStellarator_confined`. -/
theorem axis_confined : (∀ s ∈ Set.Icc (0 : ℝ) 750, axis s ∈ tubeT) ∧
    2 * Real.pi * 95 ≤ ∫ u in (0 : ℝ)..750, phiRate (axis u) :=
  rationalStellarator_confined (axis_fieldLine (1 / 4)) (axis_mem_startTube 0)

/-- Rejected fixture: `I ≤ I_a` fails on the outer face `s = 1/10` (at `z = 0`, `φ = 0`), so
the start set cannot be enlarged to the whole tube. -/
theorem start_bound_fails_on_face : ¬ ∀ y ∈ tubeT, Ifun y ≤ 1099511628 := by
  intro h
  set y : Space := WithLp.toLp 2 ![Real.sqrt (6 / 5), 0, 0] with hy
  have h0 : y 0 = Real.sqrt (6 / 5) := by simp [hy]
  have h1 : y 1 = 0 := by simp [hy]
  have h2 : y 2 = 0 := by simp [hy]
  have hr : r2 y = 6 / 5 := by
    rw [r2, h0, h1, Real.sq_sqrt (by norm_num)]; norm_num
  have hs : sc y = 1 / 10 := by rw [sc, hr]; norm_num
  have hc : cc y = 1 := by
    rw [cc, winv, hr, h0, h1, Real.sq_sqrt (by norm_num)]; norm_num
  have hss : ss y = 0 := by rw [ss, h1]; ring
  have hT : y ∈ tubeT := ⟨by rw [hs]; norm_num, by rw [h2]; norm_num⟩
  have hI := I_face (s := 1 / 10) (z := 0) (C := 1) (S := 0) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl rfl)
  have h3 := h y hT
  unfold Ifun at h3
  rw [W_eq_vars4, hs, h2, hc, hss] at h3
  linarith

end PlasmaLean.Design.RationalStellarator.Confined
