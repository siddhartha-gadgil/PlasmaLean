/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.ClebschDivergence
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A formal algebra of cylindrical potentials (`x^a y^b z^j r₂^s (log r₂)^q`)

Dommaschk potentials (and many other vacuum potentials in toroidal geometry) are, in Cartesian
coordinates, finite sums of monomials
`c · x^a · y^b · z^j · r₂^s · (log r₂)^q`, `r₂ = x² + y²`, with `c ∈ ℤ`, `a, b, j, q ∈ ℕ`,
`s ∈ ℤ`. This file makes such sums a computable data type `CylPoly` with:

* `eval f : Space → ℝ` (meaningful on `domain = {r₂ > 0}`; Lean's `r₂^s` and `log` are total);
* formal partial derivatives `d 0, d 1, d 2` and the theorem `hasFDerivAt_eval`: off the
  `z`-axis the actual Fréchet derivative of `eval f` has partials `eval (d i f)`; smoothness
  `contDiffAt_eval` (every order);
* the formal Laplacian `lap f` and a computable, evaluation-sound normal form `nf`
  (`y² ↦ r₂ − x²`, merge like monomials, drop zeros): `eval_nf`, `eval_eq_zero_of_nf`;
* the gradient field `gradField f` (`hasFDerivAt_eval_inner`: it is `∇ eval f`), symmetry of
  the formal Hessian on the domain (`eval_d_comm`, from Schwarz's theorem), and the criterion
  **`gradField_vacuum`**: if `nf (lap f) = []` then `∇ eval f` is a vacuum field
  (`VacuumField domain`), i.e. `eval f` is harmonic off the axis;
* closure of `VacuumField` under `+`, scalar multiples and finite sums
  (`PlasmaLean.Vacuum.VacuumField.add`, `.smul`, `.sum`, `.zero`; stated in the kernel's
  namespace so that dot notation works, candidates for `Kernel/Vacuum`);
* stellarator symmetry `stellRefl (x, y, z) = (x, −y, −z)`: a computable parity check
  `parityCheck 1 f` (every monomial has `b + j` odd) gives `gradField_stellRefl`:
  `∇ eval f (σ y) = −σ ∇ eval f (y)`.

The normal form is a check, not a decision procedure: only the sound direction
(`nf f = [] → eval f = 0` on the domain) is proved and used. (The reduced monomials
`x^a y^b z^j r₂^s (log r₂)^q`, `b ≤ 1`, should be linearly independent, which would make the check
complete; this is neither proved nor needed.) Sanity: `nf_lap_x2` (`x²` is rejected),
`nf_lap_logr2` (`log r₂` is accepted), `nf_lap_nil`, `parityCheck_fixtures`.
-/

open scoped RealInnerProductSpace

public section
namespace PlasmaLean.Fields.CylAlgebra
open PlasmaLean.Fields PlasmaLean.Vacuum WithLp

/-! ## Data -/

/-- A monomial `c · x^a · y^b · z^j · r₂^s · (log r₂)^q`. -/
structure Mono where
  /-- Integer coefficient. -/
  c : ℤ
  /-- Exponent of `x`. -/
  a : ℕ
  /-- Exponent of `y`. -/
  b : ℕ
  /-- Exponent of `z`. -/
  j : ℕ
  /-- Exponent of `r₂ = x² + y²`. -/
  s : ℤ
  /-- Exponent of `log r₂`. -/
  q : ℕ
deriving DecidableEq, Repr

/-- A cylindrical potential: a finite sum of monomials. -/
abbrev CylPoly := List Mono

/-! ## Formal operations (computable) -/

/-- Formal `∂ₓ` of a monomial:
`∂ₓ (x^a … r₂^s L^q) = a x^(a−1) … + 2s x^(a+1) … r₂^(s−1) + 2q x^(a+1) … r₂^(s−1) L^(q−1)`. -/
@[expose] def Mono.dx (m : Mono) : CylPoly :=
  [⟨m.c * m.a, m.a - 1, m.b, m.j, m.s, m.q⟩,
   ⟨m.c * 2 * m.s, m.a + 1, m.b, m.j, m.s - 1, m.q⟩,
   ⟨m.c * 2 * m.q, m.a + 1, m.b, m.j, m.s - 1, m.q - 1⟩]

/-- Formal `∂_y` of a monomial. -/
@[expose] def Mono.dy (m : Mono) : CylPoly :=
  [⟨m.c * m.b, m.a, m.b - 1, m.j, m.s, m.q⟩,
   ⟨m.c * 2 * m.s, m.a, m.b + 1, m.j, m.s - 1, m.q⟩,
   ⟨m.c * 2 * m.q, m.a, m.b + 1, m.j, m.s - 1, m.q - 1⟩]

/-- Formal `∂_z` of a monomial. -/
@[expose] def Mono.dz (m : Mono) : CylPoly := [⟨m.c * m.j, m.a, m.b, m.j - 1, m.s, m.q⟩]

/-- Formal `∂ₓ`. -/
@[expose] def d0 (f : CylPoly) : CylPoly := f.flatMap Mono.dx
/-- Formal `∂_y`. -/
@[expose] def d1 (f : CylPoly) : CylPoly := f.flatMap Mono.dy
/-- Formal `∂_z`. -/
@[expose] def d2 (f : CylPoly) : CylPoly := f.flatMap Mono.dz

/-- Formal partial derivative `∂ᵢ`. -/
@[expose] def d (i : Fin 3) : CylPoly → CylPoly := ![d0, d1, d2] i

/-- The formal Laplacian `∂ₓ² + ∂_y² + ∂_z²`. -/
@[expose] def lap (f : CylPoly) : CylPoly := d0 (d0 f) ++ d1 (d1 f) ++ d2 (d2 f)

/-- Eliminate `y²` from a monomial (`y² = r₂ − x²`), with fuel. -/
@[expose] def redY : ℕ → Mono → CylPoly
  | 0, m => [m]
  | n + 1, m =>
    if 2 ≤ m.b then
      redY n ⟨m.c, m.a, m.b - 2, m.j, m.s + 1, m.q⟩ ++
        redY n ⟨-m.c, m.a + 2, m.b - 2, m.j, m.s, m.q⟩
    else [m]

/-- Same exponents. -/
@[expose] def sameKey (m n : Mono) : Bool :=
  m.a == n.a && m.b == n.b && m.j == n.j && m.s == n.s && m.q == n.q

/-- Add a monomial into a sum, merging it with a monomial of the same exponents if present. -/
@[expose] def insertM (m : Mono) : CylPoly → CylPoly
  | [] => [m]
  | n :: l => if sameKey m n then ⟨n.c + m.c, n.a, n.b, n.j, n.s, n.q⟩ :: l else n :: insertM m l

/-- **Normal form**: eliminate `y²`, merge like monomials, drop zero coefficients. -/
@[expose] def nf (f : CylPoly) : CylPoly :=
  ((f.flatMap fun m => redY m.b m).foldr insertM []).filter fun m => m.c != 0

/-! ## Evaluation -/

/-- Squared distance from the `z`-axis, `r₂ = x² + y²` (same formula as
`Design.RationalStellarator.r2`). -/
@[expose] noncomputable def r2 (y : Space) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- The region off the `z`-axis, `{r₂ > 0}`. -/
@[expose] noncomputable def domain : Set Space := {y | 0 < r2 y}

/-- Value of a monomial. -/
@[expose] noncomputable def Mono.eval (m : Mono) (y : Space) : ℝ :=
  m.c * y 0 ^ m.a * y 1 ^ m.b * y 2 ^ m.j * r2 y ^ m.s * Real.log (r2 y) ^ m.q

/-- Value of a cylindrical potential. -/
@[expose] noncomputable def eval (f : CylPoly) (y : Space) : ℝ := (f.map fun m => m.eval y).sum

/-- The gradient field `(eval (d 0 f), eval (d 1 f), eval (d 2 f))`. -/
@[expose] noncomputable def gradField (f : CylPoly) (y : Space) : Space :=
  toLp 2 ![eval (d0 f) y, eval (d1 f) y, eval (d2 f) y]

@[simp] theorem eval_nil (y : Space) : eval [] y = 0 := rfl

@[simp] theorem eval_cons (m : Mono) (f : CylPoly) (y : Space) :
    eval (m :: f) y = m.eval y + eval f y := by simp [eval]

@[simp] theorem eval_append (f g : CylPoly) (y : Space) :
    eval (f ++ g) y = eval f y + eval g y := by simp [eval]

theorem eval_flatMap (f : CylPoly) (g : Mono → CylPoly) (y : Space) :
    eval (f.flatMap g) y = (f.map fun m => eval (g m) y).sum := by
  induction f with
  | nil => rfl
  | cons m f ih => simp [List.flatMap_cons, ih]

/-- Coordinates of the gradient field. -/
theorem gradField_apply (f : CylPoly) (y : Space) (k : Fin 3) :
    gradField f y k = eval (d k f) y := by
  fin_cases k <;> rfl

/-! ## Derivatives -/

/-- Coordinate functional. -/
noncomputable abbrev pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- The linear functional with partial derivatives `(a, b, c)`. -/
@[expose] noncomputable def lin (a b c : ℝ) : Space →L[ℝ] ℝ := a • pr 0 + b • pr 1 + c • pr 2

theorem lin_apply (a b c : ℝ) (v : Space) : lin a b c v = a * v 0 + b * v 1 + c * v 2 := by
  simp [lin]

theorem lin_add (a b c a' b' c' : ℝ) :
    lin a b c + lin a' b' c' = lin (a + a') (b + b') (c + c') := by
  ext v; simp [lin_apply]; ring

/-- Transfer a derivative along a pointwise identity, identifying the partials. -/
theorem hfd {f g : Space → ℝ} {L : Space →L[ℝ] ℝ} {a b c : ℝ} {x : Space}
    (h : HasFDerivAt g L x) (hf : ∀ y, f y = g y)
    (hL : ∀ v, L v = a * v 0 + b * v 1 + c * v 2) : HasFDerivAt f (lin a b c) x := by
  rw [show f = g from funext hf]
  refine h.congr_fderiv ?_
  ext v
  rw [hL, lin_apply]

theorem hasFDerivAt_coord (x : Space) (i : Fin 3) : HasFDerivAt (fun y : Space => y i) (pr i) x :=
  (pr i).hasFDerivAt

theorem hasFDerivAt_r2 (x : Space) : HasFDerivAt r2 (lin (2 * x 0) (2 * x 1) 0) x :=
  hfd (((hasFDerivAt_coord x 0).pow 2).add ((hasFDerivAt_coord x 1).pow 2))
    (fun y => rfl) (fun v => by simp)

theorem continuous_r2 : Continuous r2 := by
  unfold r2; fun_prop

theorem isOpen_domain : IsOpen domain := isOpen_lt continuous_const continuous_r2

theorem isOpen_r2_ne : IsOpen {y : Space | r2 y ≠ 0} := isOpen_ne_fun continuous_r2 continuous_const

/-- Derivative of a monomial off the axis. -/
theorem hasFDerivAt_monoEval (m : Mono) {x : Space} (hx : r2 x ≠ 0) :
    HasFDerivAt m.eval (lin (eval m.dx x) (eval m.dy x) (eval m.dz x)) x := by
  obtain ⟨c, a, b, j, s, q⟩ := m
  have hr := hasFDerivAt_r2 x
  have h0 := (hasDerivAt_pow a (x 0)).hasFDerivAt.comp x (hasFDerivAt_coord x 0)
  have h1 := (hasDerivAt_pow b (x 1)).hasFDerivAt.comp x (hasFDerivAt_coord x 1)
  have h2 := (hasDerivAt_pow j (x 2)).hasFDerivAt.comp x (hasFDerivAt_coord x 2)
  have hs := (hasDerivAt_zpow s (r2 x) (Or.inl hx)).hasFDerivAt.comp x hr
  have hl := (hasDerivAt_pow q (Real.log (r2 x))).hasFDerivAt.comp x
    ((Real.hasDerivAt_log hx).hasFDerivAt.comp x hr)
  have := (((((hasFDerivAt_const (c : ℝ) x).mul h0).mul h1).mul h2).mul hs).mul hl
  refine hfd this (fun y => rfl) (fun v => ?_)
  simp [Mono.dx, Mono.dy, Mono.dz, Mono.eval, lin_apply, zpow_sub_one₀ hx]
  ring

/-- **The formal partials are the actual partials**: off the `z`-axis the Fréchet derivative of
`eval f` has partial derivatives `eval (d i f)`. -/
theorem hasFDerivAt_eval (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) :
    HasFDerivAt (eval f) (lin (eval (d0 f) x) (eval (d1 f) x) (eval (d2 f) x)) x := by
  induction f with
  | nil =>
    refine hfd (hasFDerivAt_const (0 : ℝ) x) (fun y => rfl) (fun v => ?_)
    simp [d0, d1, d2]
  | cons m f ih =>
    have := (hasFDerivAt_monoEval m hx).add ih
    rw [lin_add] at this
    refine (this.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall
      fun y => by simp)
    simp [d0, d1, d2, List.flatMap_cons]

/-- Same, in terms of `d i`. -/
theorem hasFDerivAt_eval' (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) :
    HasFDerivAt (eval f) (lin (eval (d 0 f) x) (eval (d 1 f) x) (eval (d 2 f) x)) x :=
  hasFDerivAt_eval f hx

/-- **`gradField f` is the gradient of `eval f`**: `D (eval f) x = ⟪gradField f x, ·⟫`. -/
theorem hasFDerivAt_eval_inner (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) :
    HasFDerivAt (eval f) (innerSL ℝ (gradField f x)) x := by
  refine (hasFDerivAt_eval f hx).congr_fderiv ?_
  ext v
  simp [lin_apply, gradField, PiLp.inner_apply, Fin.sum_univ_three]
  ring

/-- `r₂^s` is smooth off the axis. -/
theorem contDiffAt_r2_zpow {n : WithTop ℕ∞} (s : ℤ) {x : Space} (hx : r2 x ≠ 0) :
    ContDiffAt ℝ n (fun y => r2 y ^ s) x := by
  have hr : ContDiff ℝ n r2 := by
    have h0 : ContDiff ℝ n (fun y : Space => y 0) := (pr 0).contDiff
    have h1 : ContDiff ℝ n (fun y : Space => y 1) := (pr 1).contDiff
    unfold r2; fun_prop
  rcases s with s | s
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact (hr.pow s).contDiffAt
  · simp only [zpow_negSucc]
    exact (hr.pow (s + 1)).contDiffAt.inv (pow_ne_zero _ hx)

/-- **Smoothness**: `eval f` is `C^n` (every `n`) off the axis. -/
theorem contDiffAt_eval {n : WithTop ℕ∞} (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) :
    ContDiffAt ℝ n (eval f) x := by
  induction f with
  | nil => exact contDiffAt_const
  | cons m f ih =>
    have hm : ContDiffAt ℝ n m.eval x := by
      have h0 : ContDiffAt ℝ n (fun y : Space => y 0) x := (pr 0).contDiff.contDiffAt
      have h1 : ContDiffAt ℝ n (fun y : Space => y 1) x := (pr 1).contDiff.contDiffAt
      have h2 : ContDiffAt ℝ n (fun y : Space => y 2) x := (pr 2).contDiff.contDiffAt
      have hr : ContDiffAt ℝ n r2 x := by unfold r2; fun_prop
      have hs := contDiffAt_r2_zpow (n := n) m.s hx
      have hl : ContDiffAt ℝ n (fun y => Real.log (r2 y)) x := hr.log hx
      unfold Mono.eval; fun_prop
    have e : eval (m :: f) = fun y => m.eval y + eval f y := funext fun y => eval_cons m f y
    rw [e]
    exact hm.add ih

/-! ## Symmetry of the formal Hessian -/

/-- **Schwarz**: on the domain the formal mixed partials agree after evaluation. -/
theorem eval_d_comm (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) (k l : Fin 3) :
    eval (d k (d l f)) x = eval (d l (d k f)) x := by
  set f' : Space → Space →L[ℝ] ℝ := fun y => lin (eval (d 0 f) y) (eval (d 1 f) y) (eval (d 2 f) y)
  have hev : ∀ᶠ y in nhds x, HasFDerivAt (eval f) (f' y) y :=
    Filter.mem_of_superset (isOpen_r2_ne.mem_nhds hx) fun y hy => hasFDerivAt_eval' f hy
  set L : Fin 3 → Space →L[ℝ] ℝ := fun i =>
    lin (eval (d 0 (d i f)) x) (eval (d 1 (d i f)) x) (eval (d 2 (d i f)) x)
  have hf' : HasFDerivAt f'
      ((L 0).smulRight (pr 0) + (L 1).smulRight (pr 1) + (L 2).smulRight (pr 2)) x := by
    have e : f' = fun y => eval (d 0 f) y • pr 0 + eval (d 1 f) y • pr 1 +
        eval (d 2 f) y • pr 2 := rfl
    rw [e]
    exact (((hasFDerivAt_eval' (d 0 f) hx).smul_const (pr 0)).add
      ((hasFDerivAt_eval' (d 1 f) hx).smul_const (pr 1))).add
      ((hasFDerivAt_eval' (d 2 f) hx).smul_const (pr 2))
  have h := second_derivative_symmetric_of_eventually hev hf' (coordVec k) (coordVec l)
  simp only [L] at h
  fin_cases k <;> fin_cases l <;> simp [lin_apply] at h ⊢ <;> linarith

/-! ## The gradient field is a vacuum field when the Laplacian normalises to zero -/

/-- Derivative of a coordinate of the gradient field. -/
theorem hasFDerivAt_gradField_coord (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) (k : Fin 3) :
    HasFDerivAt (fun y => gradField f y k)
      (lin (eval (d 0 (d k f)) x) (eval (d 1 (d k f)) x) (eval (d 2 (d k f)) x)) x := by
  simp only [gradField_apply]
  exact hasFDerivAt_eval' (d k f) hx

/-- The derivative of the gradient field (the Hessian operator). -/
@[expose] noncomputable def hess (f : CylPoly) (x : Space) : Space →L[ℝ] Space :=
  ∑ k, (lin (eval (d 0 (d k f)) x) (eval (d 1 (d k f)) x) (eval (d 2 (d k f)) x)).smulRight
    (basis k)

theorem hasFDerivAt_gradField (f : CylPoly) {x : Space} (hx : r2 x ≠ 0) :
    HasFDerivAt (gradField f) (hess f x) x :=
  hasFDerivAt_of_coords fun k => hasFDerivAt_gradField_coord f hx k

theorem hess_entry (f : CylPoly) (x : Space) (i j : Fin 3) :
    hess f x (coordVec j) i = eval (d j (d i f)) x := by
  rw [hess, coords_apply, lin_apply]
  fin_cases j <;> simp

/-- `eval (lap f)` is the trace of the formal Hessian. -/
theorem eval_lap (f : CylPoly) (y : Space) :
    eval (lap f) y = eval (d 0 (d 0 f)) y + eval (d 1 (d 1 f)) y + eval (d 2 (d 2 f)) y := by
  simp [lap, d]; ring

/-! ## Soundness of the normal form -/

theorem eval_redY (n : ℕ) (m : Mono) {y : Space} (hy : r2 y ≠ 0) :
    eval (redY n m) y = m.eval y := by
  induction n generalizing m with
  | zero => simp [redY]
  | succ n ih =>
    rw [redY]
    split_ifs with h
    · rw [eval_append, ih, ih]
      obtain ⟨c, a, b, j, s, q⟩ := m
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by simp at h; omega⟩
      simp only [Mono.eval, Nat.add_sub_cancel, zpow_add_one₀ hy, Int.cast_neg]
      have : r2 y = y 0 ^ 2 + y 1 ^ 2 := rfl
      rw [this]; ring
    · simp

theorem eval_insertM (m : Mono) (l : CylPoly) (y : Space) :
    eval (insertM m l) y = m.eval y + eval l y := by
  induction l with
  | nil => simp [insertM]
  | cons n l ih =>
    rw [insertM]
    split_ifs with h
    · obtain ⟨c, a, b, j, s, q⟩ := m
      obtain ⟨c', a', b', j', s', q'⟩ := n
      simp only [sameKey, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
      simp only [eval_cons, Mono.eval, Int.cast_add]; ring
    · simp only [eval_cons, ih]; ring

theorem eval_filter_ne_zero (f : CylPoly) (y : Space) :
    eval (f.filter fun m => m.c != 0) y = eval f y := by
  induction f with
  | nil => rfl
  | cons m f ih =>
    by_cases h : m.c = 0
    · simp [h, ih, Mono.eval]
    · simp [h, ih]

/-- **Soundness of the normal form** off the axis. -/
theorem eval_nf (f : CylPoly) {y : Space} (hy : r2 y ≠ 0) : eval (nf f) y = eval f y := by
  rw [nf, eval_filter_ne_zero]
  have hfold : ∀ g : CylPoly, eval (g.foldr insertM []) y = eval g y := by
    intro g
    induction g with
    | nil => rfl
    | cons m g ih => rw [List.foldr_cons, eval_insertM, ih, eval_cons]
  rw [hfold, eval_flatMap]
  simp only [eval_redY _ _ hy]
  rfl

/-- A potential whose normal form is empty vanishes off the axis. -/
theorem eval_eq_zero_of_nf {f : CylPoly} (h : nf f = []) {y : Space} (hy : r2 y ≠ 0) :
    eval f y = 0 := by
  rw [← eval_nf f hy, h, eval_nil]

/-! ## The vacuum criterion -/

/-- **Vacuum criterion**: if the formal Laplacian of `f` normalises to zero, then `∇ eval f` is
a vacuum field off the `z`-axis (open, `C²`, divergence free, curl free). -/
theorem gradField_vacuum {f : CylPoly} (h : nf (lap f) = []) :
    VacuumField domain (gradField f) := by
  refine ⟨isOpen_domain, ?_, fun x hx => ?_, fun x hx => ?_⟩
  · intro x hx
    refine ContDiffAt.contDiffWithinAt ((contDiffAt_piLp 2).mpr fun k => ?_)
    simp only [gradField_apply]
    exact contDiffAt_eval _ (ne_of_gt hx)
  · have hx' : r2 x ≠ 0 := ne_of_gt hx
    rw [fieldDiv, (hasFDerivAt_gradField f hx').fderiv, divOp_apply, hess_entry, hess_entry,
      hess_entry, ← eval_lap]
    exact eval_eq_zero_of_nf h hx'
  · have hx' : r2 x ≠ 0 := ne_of_gt hx
    rw [fieldCurl, (hasFDerivAt_gradField f hx').fderiv, curlOp_eq_zero_iff]
    intro i j
    rw [hess_entry, hess_entry]
    exact eval_d_comm f hx' j i

/-- Harmonicity in coordinates: `∂ₓ² + ∂_y² + ∂_z²` of `eval f` vanishes on the domain. -/
theorem eval_lap_eq_zero {f : CylPoly} (h : nf (lap f) = []) {x : Space} (hx : x ∈ domain) :
    eval (lap f) x = 0 :=
  eval_eq_zero_of_nf h (ne_of_gt hx)

/-! ## Closure of vacuum fields -/

section Closure
variable {Ω : Set Euclid3} {B B' : Euclid3 → Euclid3}

theorem divOp_add (L L' : Euclid3 →L[ℝ] Euclid3) : divOp (L + L') = divOp L + divOp L' := by
  simp [divOp, Finset.sum_add_distrib]

theorem divOp_smul (c : ℝ) (L : Euclid3 →L[ℝ] Euclid3) : divOp (c • L) = c * divOp L := by
  simp [divOp, Finset.mul_sum]

theorem curlOp_add (L L' : Euclid3 →L[ℝ] Euclid3) : curlOp (L + L') = curlOp L + curlOp L' := by
  ext k; fin_cases k <;> simp [curlOp] <;> ring

theorem curlOp_smul (c : ℝ) (L : Euclid3 →L[ℝ] Euclid3) : curlOp (c • L) = c • curlOp L := by
  ext k; fin_cases k <;> simp [curlOp] <;> ring

theorem _root_.PlasmaLean.Vacuum.VacuumField.differentiableAt (hB : VacuumField Ω B) {x : Euclid3}
    (hx : x ∈ Ω) :
    DifferentiableAt ℝ B x :=
  ((hB.contDiffOn x hx).contDiffAt (hB.isOpen.mem_nhds hx)).differentiableAt (by norm_num)

/-- The zero field is a vacuum field on any open region. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.zero (hΩ : IsOpen Ω) : VacuumField Ω (fun _ => 0) :=
  ⟨hΩ, contDiffOn_const, fun x _ => by simp [fieldDiv, divOp],
    fun x _ => by ext k; fin_cases k <;> simp [fieldCurl, curlOp]⟩

/-- Vacuum fields on the same region are closed under addition. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.add (hB : VacuumField Ω B) (hB' : VacuumField Ω B') :
    VacuumField Ω (B + B') := by
  refine ⟨hB.isOpen, hB.contDiffOn.add hB'.contDiffOn, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, fderiv_add (hB.differentiableAt hx) (hB'.differentiableAt hx), divOp_add]
    have h1 := hB.div_eq_zero x hx
    have h2 := hB'.div_eq_zero x hx
    rw [fieldDiv] at h1 h2
    rw [h1, h2, add_zero]
  · rw [fieldCurl, fderiv_add (hB.differentiableAt hx) (hB'.differentiableAt hx), curlOp_add]
    have h1 := hB.curl_eq_zero x hx
    have h2 := hB'.curl_eq_zero x hx
    rw [fieldCurl] at h1 h2
    rw [h1, h2, add_zero]

/-- Vacuum fields are closed under scalar multiples. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.smul (c : ℝ) (hB : VacuumField Ω B) :
    VacuumField Ω (c • B) := by
  refine ⟨hB.isOpen, hB.contDiffOn.const_smul c, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, fderiv_const_smul (hB.differentiableAt hx), divOp_smul]
    have h1 := hB.div_eq_zero x hx
    rw [fieldDiv] at h1
    rw [h1, mul_zero]
  · rw [fieldCurl, fderiv_const_smul (hB.differentiableAt hx), curlOp_smul]
    have h1 := hB.curl_eq_zero x hx
    rw [fieldCurl] at h1
    rw [h1, smul_zero]

/-- Vacuum fields are closed under finite sums. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.sum {ι : Type*} (s : Finset ι)
    {F : ι → Euclid3 → Euclid3} (hΩ : IsOpen Ω) (hF : ∀ i ∈ s, VacuumField Ω (F i)) :
    VacuumField Ω (fun y => ∑ i ∈ s, F i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using VacuumField.zero hΩ
  | insert i s hi ih =>
    have h := (hF i (Finset.mem_insert_self i s)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))
    convert h using 1
    funext y
    simp [Finset.sum_insert hi]

end Closure

/-! ## Stellarator symmetry `(x, y, z) ↦ (x, −y, −z)` -/

/-- The stellarator-symmetry reflection `(R, φ, z) ↦ (R, −φ, −z)`, i.e. `(x, y, z) ↦ (x, −y, −z)`
(rotation by `π` about the `x`-axis). -/
@[expose] noncomputable def stellRefl (y : Space) : Space := toLp 2 ![y 0, -y 1, -y 2]

/-- Computable parity check: every monomial has `b + j ≡ p (mod 2)` (or zero coefficient). -/
@[expose] def parityCheck (p : ℕ) (f : CylPoly) : Bool :=
  f.all fun m => m.c == 0 || (m.b + m.j) % 2 == p

theorem stellRefl_coords (y : Space) :
    stellRefl y 0 = y 0 ∧ stellRefl y 1 = -y 1 ∧ stellRefl y 2 = -y 2 := by
  simp [stellRefl]

theorem stellRefl_add (u v : Space) : stellRefl (u + v) = stellRefl u + stellRefl v := by
  ext k; fin_cases k <;> simp [stellRefl] <;> ring

theorem stellRefl_smul (c : ℝ) (u : Space) : stellRefl (c • u) = c • stellRefl u := by
  ext k; fin_cases k <;> simp [stellRefl]

theorem stellRefl_neg (u : Space) : stellRefl (-u) = -stellRefl u := by
  ext k; fin_cases k <;> simp [stellRefl]

theorem stellRefl_zero : stellRefl 0 = 0 := by
  ext k; fin_cases k <;> simp [stellRefl]

theorem stellRefl_sum {ι : Type*} (s : Finset ι) (u : ι → Space) :
    stellRefl (∑ i ∈ s, u i) = ∑ i ∈ s, stellRefl (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [stellRefl_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, stellRefl_add, ih]

theorem r2_stellRefl (y : Space) : r2 (stellRefl y) = r2 y := by simp [r2, stellRefl]

theorem parityCheck_cons (p : ℕ) (m : Mono) (f : CylPoly) :
    parityCheck p (m :: f) = true ↔ (m.c = 0 ∨ (m.b + m.j) % 2 = p) ∧ parityCheck p f = true := by
  simp [parityCheck]

theorem Mono.eval_stellRefl (m : Mono) (y : Space) :
    m.eval (stellRefl y) = (-1) ^ (m.b + m.j) * m.eval y := by
  obtain ⟨e0, e1, e2⟩ := stellRefl_coords y
  simp only [Mono.eval, r2_stellRefl, e0, e1, e2, neg_pow (y 1), neg_pow (y 2), pow_add]
  ring

/-- Under the reflection, `eval f` is multiplied by `(-1)^p` when every monomial has parity `p`. -/
theorem eval_stellRefl {p : ℕ} {f : CylPoly} (h : parityCheck p f = true) (y : Space) :
    eval f (stellRefl y) = (-1) ^ p * eval f y := by
  induction f with
  | nil => simp
  | cons m f ih =>
    rw [parityCheck_cons] at h
    rw [eval_cons, eval_cons, ih h.2, Mono.eval_stellRefl, mul_add]
    congr 1
    rcases h.1 with h0 | h0
    · simp [Mono.eval, h0]
    · rw [← Nat.mod_add_div (m.b + m.j) 2, h0, pow_add, pow_mul]; simp

theorem parityCheck_append {p : ℕ} {f g : CylPoly} :
    parityCheck p (f ++ g) = true ↔ parityCheck p f = true ∧ parityCheck p g = true := by
  simp [parityCheck, List.all_append]

theorem parityCheck_flatMap {p : ℕ} {f : CylPoly} {g : Mono → CylPoly}
    (h : ∀ m ∈ f, parityCheck p (g m) = true) : parityCheck p (f.flatMap g) = true := by
  induction f with
  | nil => rfl
  | cons m f ih =>
    rw [List.flatMap_cons, parityCheck_append]
    exact ⟨h m (by simp), ih fun n hn => h n (by simp [hn])⟩

/-- `∂ₓ` preserves the parity of `b + j`. -/
theorem parityCheck_d0 {p : ℕ} {f : CylPoly} (h : parityCheck p f = true) :
    parityCheck p (d0 f) = true := by
  refine parityCheck_flatMap fun m hm => ?_
  have hm' : m.c = 0 ∨ (m.b + m.j) % 2 = p := by
    simp only [parityCheck, List.all_eq_true] at h
    simpa using h m hm
  rcases hm' with h0 | h0 <;> simp [Mono.dx, parityCheck, h0]

/-- `∂_y` flips the parity of `b + j`. -/
theorem parityCheck_d1 {p : ℕ} {f : CylPoly} (h : parityCheck p f = true) :
    parityCheck ((p + 1) % 2) (d1 f) = true := by
  refine parityCheck_flatMap fun m hm => ?_
  have hm' : m.c = 0 ∨ (m.b + m.j) % 2 = p := by
    simp only [parityCheck, List.all_eq_true] at h
    simpa using h m hm
  rcases hm' with h0 | h0
  · simp [Mono.dy, parityCheck, h0]
  · simp only [Mono.dy, parityCheck, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    rcases Nat.eq_zero_or_pos m.b with hb | hb
    · simp [hb]; omega
    · omega

/-- `∂_z` flips the parity of `b + j`. -/
theorem parityCheck_d2 {p : ℕ} {f : CylPoly} (h : parityCheck p f = true) :
    parityCheck ((p + 1) % 2) (d2 f) = true := by
  refine parityCheck_flatMap fun m hm => ?_
  have hm' : m.c = 0 ∨ (m.b + m.j) % 2 = p := by
    simp only [parityCheck, List.all_eq_true] at h
    simpa using h m hm
  rcases hm' with h0 | h0
  · simp [Mono.dz, parityCheck, h0]
  · simp only [Mono.dz, parityCheck, List.all_cons, List.all_nil, Bool.and_true,
      Bool.or_eq_true, beq_iff_eq]
    rcases Nat.eq_zero_or_pos m.j with hj | hj
    · simp [hj]
    · omega

/-- **Stellarator symmetry of the gradient field**: if `eval f` is odd under the reflection
(`parityCheck 1 f`), then `∇ eval f (σ y) = −σ ∇ eval f (y)`. -/
theorem gradField_stellRefl {f : CylPoly} (h : parityCheck 1 f = true) (y : Space) :
    gradField f (stellRefl y) = -stellRefl (gradField f y) := by
  have h0 := eval_stellRefl (parityCheck_d0 h) y
  have h1 := eval_stellRefl (parityCheck_d1 h) y
  have h2 := eval_stellRefl (parityCheck_d2 h) y
  norm_num at h0 h1 h2
  obtain ⟨e0, e1, e2⟩ := stellRefl_coords (gradField f y)
  ext k
  rw [gradField_apply, PiLp.neg_apply]
  fin_cases k
  · rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, e0, gradField_apply]; exact h0
  · rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, e1, gradField_apply, neg_neg]; exact h1
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, e2, gradField_apply, neg_neg]; exact h2

/-! ## Sanity checks -/

/-- Degenerate case: the empty potential is harmonic. -/
theorem nf_lap_nil : nf (lap []) = [] := rfl

/-- **Rejected fixture**: `x²` is not harmonic; its Laplacian normalises to `2`. -/
theorem nf_lap_x2 : nf (lap [⟨1, 2, 0, 0, 0, 0⟩]) = [⟨2, 0, 0, 0, 0, 0⟩] := by
  decide_cbv

/-- The checker is not vacuous: `x²` fails it. -/
theorem nf_lap_x2_ne : nf (lap [⟨1, 2, 0, 0, 0, 0⟩]) ≠ [] := by
  rw [nf_lap_x2]; exact List.cons_ne_nil _ _

/-- **Accepted fixture**: `log r₂` (the 2D fundamental solution) is harmonic off the axis. -/
theorem nf_lap_logr2 : nf (lap [⟨1, 0, 0, 0, 0, 1⟩]) = [] := by
  decide_cbv

/-- Concrete instance: `∇ log r₂` is a vacuum field off the axis. -/
theorem gradField_logr2_vacuum : VacuumField domain (gradField [⟨1, 0, 0, 0, 0, 1⟩]) :=
  gradField_vacuum nf_lap_logr2

/-- Parity fixtures: `y` is odd under the stellarator symmetry, `x` is not. -/
theorem parityCheck_fixtures :
    parityCheck 1 [⟨1, 0, 1, 0, 0, 0⟩] = true ∧ parityCheck 1 [⟨1, 1, 0, 0, 0, 0⟩] = false :=
  ⟨rfl, rfl⟩

end PlasmaLean.Fields.CylAlgebra
