/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Stability.Newcomb
public import LeanTheory.Certificates.EvalCert
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Exact polynomial positivity certificates on intervals

Univariate polynomials are coefficient lists `List ℚ` (constant term first), evaluated by
Horner's rule. Addition, scaling, multiplication, differentiation and the Taylor shift
`p(c + t)` are computed exactly in `ℚ` and proved correct for the real evaluation.

The checker `checkPieces p m pts` covers an interval by consecutive points supplied by an
untrusted search. On each piece `[c, d]` it shifts `p` to `c` and evaluates the Horner
lower bound `d₀ + min 0 (h · L)`, recursively, with `h = d - c`; this bounds `p` below on the
whole piece (`lowerBound_le`). Soundness (`checkPieces_sound`, `checkOn_sound`) holds for
every REAL point of the covered interval, not just at samples. Fixtures are evaluated by
the Lean kernel (`eval_cert`); there is no `decide`, no `native_decide` and no floating point.

Application: `jacobi_poly_certificate` and `riccati_poly_certificate` discharge the
hypotheses of the Newcomb/Jacobi/Riccati stability certificates for polynomial profiles.
`example_beyond_constant` proves `Q(ξ) ≥ ∫ ξ²` for `f = 1 + x²`, `g = -21/2` on `[0,1]`,
a drive the constant-coefficient bound `f ≥ 1` (Dirichlet constant `π² < 23/2`) cannot
handle. The certificate polynomial `u` was found numerically outside Lean.
-/
public section

namespace LeanTheory.Certificates.QPoly

/-- Exact rational evaluation by Horner's rule. -/
@[expose] def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

/-- Real evaluation of a rational coefficient list by Horner's rule. -/
@[expose] noncomputable def eval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => a + x * eval p x

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℚ) (p : List ℚ) (x : ℝ) :
    eval (a :: p) x = a + x * eval p x := rfl

/-- Rational and real evaluation agree at rational points. -/
theorem eval_cast (p : List ℚ) (x : ℚ) : eval p x = (evalQ p x : ℝ) := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [evalQ, ih]

/-- Sanity: the coefficient list `[a, b, c]` is the quadratic `a + b x + c x²`. -/
theorem eval_quadratic (a b c : ℚ) (x : ℝ) :
    eval [a, b, c] x = a + b * x + c * x ^ 2 := by
  simp; ring

/-- Coefficientwise sum. -/
@[expose] def add : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

@[simp] theorem eval_add (p q : List ℚ) (x : ℝ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

/-- Scaling by a rational constant. -/
@[expose] def scale (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

@[simp] theorem eval_scale (c : ℚ) (p : List ℚ) (x : ℝ) :
    eval (scale c p) x = c * eval p x := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    simp only [scale, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Product, by `(a + x P) Q = a Q + x (P Q)`. -/
@[expose] def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

@[simp] theorem eval_mul (p q : List ℚ) (x : ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

/-- Formal derivative, by `(a + x P)' = P + x P'`. -/
@[expose] def deriv : List ℚ → List ℚ
  | [] => []
  | _ :: p => add p (0 :: deriv p)

/-- The formal derivative is the actual derivative of the real evaluation. -/
theorem hasDerivAt_eval (p : List ℚ) (x : ℝ) : HasDerivAt (eval p) (eval (deriv p) x) x := by
  induction p with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) x
    exact hasDerivAt_const x 0
  | cons a p ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
    convert h using 1
    · funext y; simp
    · simp [deriv]

/-- Polynomial evaluation is continuous. -/
theorem continuous_eval (p : List ℚ) : Continuous (eval p) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_eval p x).continuousAt

/-- Sanity: the derivative of `x²` is `2x`. -/
theorem eval_deriv_sq (x : ℝ) : eval (deriv [0, 0, 1]) x = 2 * x := by
  simp [deriv, add]; ring

/-- Taylor shift: `shift c p` has evaluation `t ↦ p(c + t)`. -/
@[expose] def shift (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => add [a] (mul [c, 1] (shift c p))

@[simp] theorem eval_shift (c : ℚ) (p : List ℚ) (t : ℝ) :
    eval (shift c p) t = eval p (c + t) := by
  induction p with
  | nil => simp [shift]
  | cons a p ih => simp [shift, ih]

/-- Horner lower bound on `[0, h]`: `d₀ + min 0 (h · L)` with `L` the bound for the tail. -/
@[expose] def lowerBound (h : ℚ) : List ℚ → ℚ
  | [] => 0
  | a :: p => a + min 0 (h * lowerBound h p)

/-- Soundness of the Horner lower bound on the whole real segment `[0, h]`. -/
theorem lowerBound_le {h : ℚ} (p : List ℚ) {t : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h) :
    (lowerBound h p : ℝ) ≤ eval p t := by
  induction p with
  | nil => simp [lowerBound]
  | cons a p ih =>
    simp only [lowerBound, eval_cons, Rat.cast_add, Rat.cast_min, Rat.cast_zero,
      Rat.cast_mul]
    have key : min 0 ((h : ℝ) * lowerBound h p) ≤ t * eval p t := by
      rcases le_or_gt 0 (lowerBound h p : ℝ) with hL | hL
      · exact (min_le_left _ _).trans (mul_nonneg ht0 (hL.trans ih))
      · refine (min_le_right _ _).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left ih ht0]
    linarith

/-- Sanity: nonnegative coefficients give their constant term as the lower bound. -/
theorem lowerBound_monomial (h : ℚ) (hh : 0 ≤ h) : lowerBound h [1, 0, 1] = 1 := by
  simp [lowerBound, min_eq_left hh]

/-- Last point of a nonempty list of subdivision points. -/
@[expose] def lastPt : ℚ → List ℚ → ℚ
  | c, [] => c
  | _, d :: rest => lastPt d rest

/-- Piecewise checker: every piece `[c, d]` has `c ≤ d` and shifted lower bound `≥ m`;
a single point is checked by exact evaluation. -/
@[expose] def checkPieces (p : List ℚ) (m : ℚ) : List ℚ → Bool
  | [] => true
  | [c] => decide (m ≤ evalQ p c)
  | c :: d :: rest => decide (c ≤ d) && decide (m ≤ lowerBound (d - c) (shift c p)) &&
      checkPieces p m (d :: rest)

/-- Soundness of the piecewise checker at every real point between the first and last
subdivision points. -/
theorem checkPieces_sound (p : List ℚ) (m : ℚ) (c : ℚ) (rest : List ℚ)
    (hc : checkPieces p m (c :: rest) = true) (x : ℝ) (h1 : (c : ℝ) ≤ x)
    (h2 : x ≤ lastPt c rest) : (m : ℝ) ≤ eval p x := by
  induction rest generalizing c with
  | nil =>
    simp only [lastPt] at h2
    have hx : x = c := le_antisymm h2 h1
    simp only [checkPieces, decide_eq_true_eq] at hc
    rw [hx, eval_cast]; exact_mod_cast hc
  | cons d rest ih =>
    simp only [checkPieces, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hcd, hlb⟩, hrest⟩ := hc
    rcases le_or_gt x d with hxd | hxd
    · have hb := lowerBound_le (h := d - c) (shift c p) (t := x - c) (by linarith)
        (by push_cast; linarith)
      rw [eval_shift] at hb
      have e : ((c : ℚ) : ℝ) + (x - c) = x := by ring
      rw [e] at hb
      exact (by exact_mod_cast hlb : (m : ℝ) ≤ (lowerBound (d - c) (shift c p) : ℝ)).trans hb
    · exact ih d hrest hxd.le h2

/-- Interval checker: points `pts` after the left endpoint `a` must reach `b`. -/
@[expose] def checkOn (p : List ℚ) (m a b : ℚ) (pts : List ℚ) : Bool :=
  checkPieces p m (a :: pts) && decide (b ≤ lastPt a pts)

/-- **Soundness.** An accepted certificate proves `m ≤ p(x)` for every real `x ∈ [a, b]`. -/
theorem checkOn_sound {p : List ℚ} {m a b : ℚ} {pts : List ℚ}
    (h : checkOn p m a b pts = true) (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) :
    (m : ℝ) ≤ eval p x := by
  simp only [checkOn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkPieces_sound p m a pts h.1 x hx.1
    (hx.2.trans (by exact_mod_cast h.2))

/-! ## Fixtures evaluated by the kernel -/

/-- `(2x - 1)⁴ + 1/1000`, whose minimum `1/1000` on `[0,1]` is attained at `1/2`. -/
@[expose] def tightQuartic : List ℚ := [1 + 1 / 1000, -8, 24, -32, 16]

/-- Sanity: the coefficient list is the stated quartic. -/
theorem tightQuartic_eval (x : ℝ) : eval tightQuartic x = (2 * x - 1) ^ 4 + 1 / 1000 := by
  simp [tightQuartic]; ring

/-- Thirty-two uniform pieces of `[0, 1]`, generated by an untrusted search. -/
@[expose] def grid32 : List ℚ := (List.range 32).map (fun i => ((i : ℚ) + 1) / 32)

/-- Accepted certificate: the tight quartic is at least `1/2000` on `[0,1]`. -/
theorem tightQuartic_check : checkOn tightQuartic (1 / 2000) 0 1 grid32 = true := by
  eval_cert

/-- Consequence for every real point. -/
theorem tightQuartic_pos (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < (2 * x - 1) ^ 4 + 1 / 1000 := by
  have := checkOn_sound tightQuartic_check x (by simpa using hx)
  rw [tightQuartic_eval] at this
  have h : (0 : ℝ) < ((1 / 2000 : ℚ) : ℝ) := by norm_num
  linarith

/-- `(1 - 2x)² - 1/100`, negative at `x = 1/2`. -/
@[expose] def dipQuadratic : List ℚ := [1 - 1 / 100, -4, 4]

/-- Rejected certificate: the checker refuses nonnegativity of `dipQuadratic`. -/
theorem dipQuadratic_reject : checkOn dipQuadratic 0 0 1 grid32 = false := by
  eval_cert

/-- The rejection is justified: the polynomial is negative at the exact point `1/2`. -/
theorem dipQuadratic_neg : eval dipQuadratic (1 / 2) < 0 := by
  norm_num [dipQuadratic]

/-! ## Polynomial stability certificates -/

open LeanTheory.Stability

/-- Riccati residual `g - c - (f w)' - f w²` for polynomial profiles. -/
@[expose] def riccatiResidual (f g w : List ℚ) (c : ℚ) : List ℚ :=
  add g (add [-c] (scale (-1) (add (deriv (mul f w)) (mul f (mul w w)))))

/-- Jacobi residual `(g - c) u - (f u')'` for polynomial profiles. -/
@[expose] def jacobiResidual (f g u : List ℚ) (c : ℚ) : List ℚ :=
  add (mul (add g [-c]) u) (scale (-1) (deriv (mul f (deriv u))))

/-- **Riccati certificate from exact checks.** Accepted checks of `f ≥ 0` and of the
Riccati residual on `[a, b]` prove `c ∫ ξ² ≤ Q(ξ)` for every admissible `ξ`. -/
theorem riccati_poly_certificate {f g w : List ℚ} {c a b : ℚ} {pts : List ℚ}
    (hab : a ≤ b) (hf : checkOn f 0 a b pts = true)
    (hR : checkOn (riccatiResidual f g w c) 0 a b pts = true)
    {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' a b) (h₀ : ξ a = 0) (h₁ : ξ b = 0) :
    (c : ℝ) * ∫ x in (a : ℝ)..b, ξ x ^ 2 ≤ newcombForm (eval f) (eval g) a b ξ ξ' := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hI : Set.uIcc (a : ℝ) b = Set.Icc (a : ℝ) b := Set.uIcc_of_le habR
  refine riccati_certificate (w := eval w) (h := eval (deriv (mul f w))) habR hξ h₀ h₁
    (continuous_eval f).continuousOn (continuous_eval g).continuousOn (fun x _ => ?_)
    (continuous_eval _).continuousOn (fun x hx => ?_) (fun x hx => ?_)
  · have := hasDerivAt_eval (mul f w) x
    convert this using 1
    funext y; simp
  · rw [hI] at hx
    simpa using checkOn_sound hf x hx
  · rw [hI] at hx
    have := checkOn_sound hR x hx
    simp [riccatiResidual] at this
    nlinarith [this]

/-- **Jacobi certificate from exact checks.** Accepted checks of `f ≥ 0`, `u ≥ m > 0` and
`(g - c) u - (f u')' ≥ 0` on `[a, b]` prove `c ∫ ξ² ≤ Q(ξ)`. -/
theorem jacobi_poly_certificate {f g u : List ℚ} {c m a b : ℚ} {pts : List ℚ}
    (hab : a ≤ b) (hm : 0 < m) (hf : checkOn f 0 a b pts = true)
    (hu : checkOn u m a b pts = true)
    (hS : checkOn (jacobiResidual f g u c) 0 a b pts = true)
    {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' a b) (h₀ : ξ a = 0) (h₁ : ξ b = 0) :
    (c : ℝ) * ∫ x in (a : ℝ)..b, ξ x ^ 2 ≤ newcombForm (eval f) (eval g) a b ξ ξ' := by
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hI : Set.uIcc (a : ℝ) b = Set.Icc (a : ℝ) b := Set.uIcc_of_le habR
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine jacobi_certificate (u := eval u) (u' := eval (deriv u))
    (k := eval (deriv (mul f (deriv u)))) habR hξ h₀ h₁
    (continuous_eval f).continuousOn (continuous_eval g).continuousOn
    (fun x hx => ?_) (fun x _ => hasDerivAt_eval u x) (continuous_eval _).continuousOn
    (fun x hx => ?_) (fun x _ => ?_) (continuous_eval _).continuousOn (fun x hx => ?_)
  · rw [hI] at hx
    simpa using checkOn_sound hf x hx
  · rw [hI] at hx
    exact hmR.trans_le (checkOn_sound hu x hx)
  · have := hasDerivAt_eval (mul f (deriv u)) x
    convert this using 1
    funext y; simp
  · rw [hI] at hx
    have := checkOn_sound hS x hx
    simp [jacobiResidual] at this
    nlinarith [this]

/-! ## Worked example beyond the constant-coefficient bound -/

/-- Shear weight `f = 1 + x²`. -/
@[expose] def shearWeight : List ℚ := [1, 0, 1]

/-- Destabilizing drive `g = -21/2`. -/
@[expose] def strongDrive : List ℚ := [-21 / 2]

/-- Degree-12 Jacobi certificate `u`, a rational least-squares fit (found outside Lean) to a
positive solution of `((1 + x²) u')' = -12 u` on `[0,1]`. Only its exact checks are
trusted. -/
@[expose] def jacobiU : List ℚ :=
  [814 / 11611, 1573617 / 444043, -218755 / 520889, -5084283 / 613871, 528973 / 687817,
    8709567 / 958610, 106481 / 43427, -11324059 / 664171, 7437129 / 792629,
    4822589 / 602695, -6213327 / 497693, 4193726 / 686815, -771767 / 698682]

/-- Quarter subdivision of `[0, 1]`. -/
@[expose] def quarters : List ℚ := [1 / 4, 1 / 2, 3 / 4, 1]

theorem shearWeight_check : checkOn shearWeight 0 0 1 quarters = true := by eval_cert

theorem jacobiU_check : checkOn jacobiU (1 / 100) 0 1 quarters = true := by eval_cert

theorem strongDrive_residual_check :
    checkOn (jacobiResidual shearWeight strongDrive jacobiU 1) 0 0 1 quarters = true := by
  eval_cert

/-- **Exact stability margin.** For `f = 1 + x²` and drive `g = -21/2` on `[0,1]`, every
C¹ displacement vanishing at both ends has `Q(ξ) ≥ ∫ ξ²`. The cruder bound from `f ≥ 1`
and the Dirichlet constant `π²` fails here since `π² < 23/2`; the variable shear weight is
essential. (Numerically the sharp constant is about `13.16 - 21/2`.) -/
theorem example_beyond_constant {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' 0 1) (h₀ : ξ 0 = 0)
    (h₁ : ξ 1 = 0) :
    ∫ x in (0 : ℝ)..1, ξ x ^ 2 ≤
      newcombForm (fun x => 1 + x ^ 2) (fun _ => -(21 / 2)) 0 1 ξ ξ' := by
  have h := jacobi_poly_certificate (pts := quarters) (c := 1) (m := 1 / 100)
    (by norm_num : (0 : ℚ) ≤ 1) (by norm_num) shearWeight_check jacobiU_check
    strongDrive_residual_check (ξ := ξ) (ξ' := ξ') (by simpa using hξ) (by simpa using h₀)
    (by simpa using h₁)
  have ef : eval shearWeight = fun x => 1 + x ^ 2 := by
    funext x; simp [shearWeight]; ring
  have eg : eval strongDrive = fun _ => -(21 / 2) := by
    funext x; simp [strongDrive]; norm_num
  rw [ef, eg] at h
  simpa using h

end LeanTheory.Certificates.QPoly
