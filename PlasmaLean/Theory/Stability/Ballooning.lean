/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PolyInterval
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The one-dimensional ballooning operator and Barta certificates

Along a magnetic field line, parametrized by `l ∈ [-L, L]`, high-mode-number ideal-MHD
ballooning perturbations reduce (Connor–Hastie–Taylor 1978; Dewar–Glasser 1983) to the
Sturm–Liouville problem

  `-(P X')' + Q X = λ W X`,   `X(±L) = 0`,

with bending stiffness `P > 0`, pressure/curvature drive `Q` (of either sign) and inertial
weight `W > 0`. The associated energy is `E(ξ) = ∫ (P ξ'² + Q ξ²)` and the weighted mass
is `M(ξ) = ∫ W ξ²` (`BallooningOperator.energy`, `BallooningOperator.mass`). The
coefficients of an actual equilibrium are SUPPLIED here; the reduction of `δW` to this
form is not formalized.

**Barta certificate (sufficiency).** If a positive `w` with `P w'` differentiable
satisfies `-(P w')' + Q w ≥ c W w` on `[-L, L]` (`BartaCertificate c`), then
`E(ξ) ≥ c M(ξ)` for every C¹ `ξ` vanishing at `±L` (`BartaCertificate.lower_bound`).
The proof is NOT re-done: it applies `PlasmaLean.Stability.jacobi_certificate` (Picone's
identity, Newcomb module) to the shifted potential `Q - c W`. Corollaries:

* `BartaCertificate.energy_pos`: `c > 0` gives `E(ξ) > 0` for every admissible `ξ ≠ 0`;
* `lower_bound_of_Q_ge`, `energy_nonneg_of_Q_nonneg`: the trivial witness `w = 1`;
* `BartaCertificate.ofContDiff`: the witness may be given as a `C²` function, with
  `deriv` in place of supplied derivatives (the form of the roadmap);
* `barta_poly_certificate` and `example_poly`: exact polynomial checks
  (`PlasmaLean.Certificates.QPoly.checkOn`) certify a nontrivial example with
  `P = 1 + l²`, `Q = -7/2 + 4 l²`, `W = 1` on `[-1, 1]`, where the frozen-coefficient
  bound (`P ≥ 1`, `Q ≥ -7/2`, Dirichlet constant `π²/4 < 7/2`) fails.

**Necessity.** `no_certificate_of_energy_lt` is the usable contrapositive: one admissible
`ξ` with `E(ξ) < c M(ξ)` rules out every Barta certificate at level `c`. For constant
coefficients `P = p > 0`, `Q = q < 0`, `const_stable_iff` is a genuine iff (Sturm/Jacobi):
`E ≥ 0` on all admissible `ξ` exactly when `L ≤ (π/2)·√(p/(-q))`. The `≤` direction uses
the cosine witness on a slightly longer line and a limit; the converse exhibits the
explicit mode `ξ(l) = cos(π l/(2L))` with `E(ξ) = (p π²/(4L²) + q) L < 0`
(`const_energy_cosMode`).

Scope: finite line `[-L, L]` with Dirichlet ends, continuous coefficients, C¹
displacements. The infinite-line ballooning problem (asymptotic tails), general
Sturm oscillation/necessity for variable coefficients, and the derivation of `P, Q, W`
from a three-dimensional equilibrium are not covered.
-/
public section

noncomputable section
namespace PlasmaLean.Stability.Ballooning
open intervalIntegral Set PlasmaLean.Stability

/-- Coefficients of the ballooning operator `-(P X')' + Q X = λ W X` on `[-L, L]`. -/
structure BallooningOperator where
  /-- Half-length of the field-line segment. -/
  L : ℝ
  /-- Field-line bending stiffness. -/
  P : ℝ → ℝ
  /-- Pressure/curvature drive. -/
  Q : ℝ → ℝ
  /-- Inertial weight. -/
  W : ℝ → ℝ
  hL : 0 < L
  P_pos : ∀ l ∈ Icc (-L) L, 0 < P l
  W_pos : ∀ l ∈ Icc (-L) L, 0 < W l
  P_cont : ContinuousOn P (Icc (-L) L)
  Q_cont : ContinuousOn Q (Icc (-L) L)
  W_cont : ContinuousOn W (Icc (-L) L)

namespace BallooningOperator
variable (op : BallooningOperator)

/-- Ballooning energy `E(ξ) = ∫_{-L}^{L} (P ξ'² + Q ξ²)` (a Newcomb form). -/
@[expose] def energy (ξ ξ' : ℝ → ℝ) : ℝ := newcombForm op.P op.Q (-op.L) op.L ξ ξ'

/-- Weighted mass `M(ξ) = ∫_{-L}^{L} W ξ²`. -/
@[expose] def mass (ξ : ℝ → ℝ) : ℝ := ∫ l in (-op.L)..op.L, op.W l * ξ l ^ 2

/-- Admissible displacements: C¹ on `[-L, L]` (derivative `ξ'`), vanishing at `±L`. -/
structure Admissible (ξ ξ' : ℝ → ℝ) : Prop where
  c1 : C1On ξ ξ' (-op.L) op.L
  left : ξ (-op.L) = 0
  right : ξ op.L = 0

/-- **Barta supersolution certificate at level `c`**: a positive C¹ function `w` (with
derivative `w'`) such that `P w'` has a continuous derivative `k = (P w')'` and
`-(P w')' + Q w ≥ c W w` on `[-L, L]`. -/
structure BartaCertificate (c : ℝ) where
  /-- The positive witness. -/
  w : ℝ → ℝ
  /-- Its derivative. -/
  w' : ℝ → ℝ
  /-- The derivative of the flux `P w'`. -/
  k : ℝ → ℝ
  hw : ∀ l ∈ Icc (-op.L) op.L, HasDerivAt w (w' l) l
  hw'c : ContinuousOn w' (Icc (-op.L) op.L)
  hk : ∀ l ∈ Icc (-op.L) op.L, HasDerivAt (fun s => op.P s * w' s) (k l) l
  hkc : ContinuousOn k (Icc (-op.L) op.L)
  pos : ∀ l ∈ Icc (-op.L) op.L, 0 < w l
  super : ∀ l ∈ Icc (-op.L) op.L, c * op.W l * w l ≤ -k l + op.Q l * w l

theorem L_neg_le : -op.L ≤ op.L := by linarith [op.hL]

theorem uIcc_eq : uIcc (-op.L) op.L = Icc (-op.L) op.L := uIcc_of_le op.L_neg_le

/-- The energy splits off the weighted mass: `E_{P,Q}(ξ) = E_{P,Q-cW}(ξ) + c M(ξ)`. -/
theorem energy_eq_shift (c : ℝ) {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' (-op.L) op.L) :
    op.energy ξ ξ' =
      newcombForm op.P (fun l => op.Q l - c * op.W l) (-op.L) op.L ξ ξ' + c * op.mass ξ := by
  have hI := op.uIcc_eq
  have hP : ContinuousOn op.P (uIcc (-op.L) op.L) := hI ▸ op.P_cont
  have hQ : ContinuousOn op.Q (uIcc (-op.L) op.L) := hI ▸ op.Q_cont
  have hW : ContinuousOn op.W (uIcc (-op.L) op.L) := hI ▸ op.W_cont
  have h1 := newcomb_integrable (g := fun l => op.Q l - c * op.W l) hξ hP
    (hQ.sub (continuousOn_const.mul hW))
  have h2 : IntervalIntegrable (fun l => c * (op.W l * ξ l ^ 2)) MeasureTheory.volume
      (-op.L) op.L := ((hW.mul (hξ.continuousOn.pow 2)).intervalIntegrable).const_mul c
  unfold energy mass newcombForm
  rw [← integral_const_mul, ← integral_add h1 h2]
  congr 1; funext l; ring

/-- **Barta certificate theorem.** A positive supersolution at level `c` gives
`c M(ξ) ≤ E(ξ)` for every admissible `ξ`. Proof: Picone/Jacobi
(`jacobi_certificate`) applied to the potential `Q - c W`. -/
theorem BartaCertificate.lower_bound {c : ℝ} (cert : op.BartaCertificate c)
    {ξ ξ' : ℝ → ℝ} (hξ : op.Admissible ξ ξ') : c * op.mass ξ ≤ op.energy ξ ξ' := by
  have hI := op.uIcc_eq
  have h0 := jacobi_certificate (f := op.P) (g := fun l => op.Q l - c * op.W l) (c := 0)
    (u := cert.w) (u' := cert.w') (k := cert.k) op.L_neg_le hξ.c1 hξ.left hξ.right
    (hI ▸ op.P_cont)
    (hI ▸ ((op.Q_cont.sub (continuousOn_const.mul op.W_cont)) :
      ContinuousOn (fun l => op.Q l - c * op.W l) _))
    (fun x hx => (op.P_pos x (hI ▸ hx)).le) (fun x hx => cert.hw x (hI ▸ hx))
    (hI ▸ cert.hw'c) (fun x hx => cert.pos x (hI ▸ hx)) (fun x hx => cert.hk x (hI ▸ hx))
    (hI ▸ cert.hkc) (fun x hx => by
      have := cert.super x (hI ▸ hx)
      linarith)
  rw [op.energy_eq_shift c hξ.c1]
  linarith

/-- The weighted mass of an admissible displacement is nonnegative. -/
theorem mass_nonneg {ξ : ℝ → ℝ} : 0 ≤ op.mass ξ :=
  integral_nonneg op.L_neg_le fun l hl => mul_nonneg (op.W_pos l hl).le (sq_nonneg _)

/-- The weighted mass is positive as soon as `ξ` is continuous and nonzero somewhere. -/
theorem mass_pos {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' (-op.L) op.L) {l₀ : ℝ}
    (hl₀ : l₀ ∈ Icc (-op.L) op.L) (hne : ξ l₀ ≠ 0) : 0 < op.mass ξ := by
  have hlt : -op.L < op.L := by linarith [op.hL]
  refine integral_pos hlt (op.W_cont.mul ((op.uIcc_eq ▸ hξ.continuousOn).pow 2))
    (fun l hl => mul_nonneg (op.W_pos l (Ioc_subset_Icc_self hl)).le (sq_nonneg _))
    ⟨l₀, hl₀, mul_pos (op.W_pos l₀ hl₀) (by positivity)⟩

/-- **Strict positivity.** A certificate at a positive level `c` makes the energy of
every nonzero admissible displacement strictly positive (strict ballooning stability on
the segment). -/
theorem BartaCertificate.energy_pos {c : ℝ} (hc : 0 < c) (cert : op.BartaCertificate c)
    {ξ ξ' : ℝ → ℝ} (hξ : op.Admissible ξ ξ') {l₀ : ℝ} (hl₀ : l₀ ∈ Icc (-op.L) op.L)
    (hne : ξ l₀ ≠ 0) : 0 < op.energy ξ ξ' :=
  lt_of_lt_of_le (mul_pos hc (op.mass_pos hξ.c1 hl₀ hne)) (cert.lower_bound op hξ)

/-- A certificate at level `0` gives `E ≥ 0`. -/
theorem BartaCertificate.energy_nonneg (cert : op.BartaCertificate 0) {ξ ξ' : ℝ → ℝ}
    (hξ : op.Admissible ξ ξ') : 0 ≤ op.energy ξ ξ' := by
  simpa using cert.lower_bound op hξ

/-- The trivial witness `w = 1` is a certificate at level `c` whenever `Q ≥ c W`. -/
def constCertificate {c : ℝ} (hQ : ∀ l ∈ Icc (-op.L) op.L, c * op.W l ≤ op.Q l) :
    op.BartaCertificate c where
  w := fun _ => 1
  w' := fun _ => 0
  k := fun _ => 0
  hw l _ := hasDerivAt_const l 1
  hw'c := continuousOn_const
  hk l _ := by simpa using hasDerivAt_const l (0 : ℝ)
  hkc := continuousOn_const
  pos _ _ := one_pos
  super l hl := by simpa using hQ l hl

/-- Sanity (trivial witness): `Q ≥ c W` gives `E ≥ c M`. -/
theorem lower_bound_of_Q_ge {c : ℝ} (hQ : ∀ l ∈ Icc (-op.L) op.L, c * op.W l ≤ op.Q l)
    {ξ ξ' : ℝ → ℝ} (hξ : op.Admissible ξ ξ') : c * op.mass ξ ≤ op.energy ξ ξ' :=
  (op.constCertificate hQ).lower_bound op hξ

/-- Sanity: purely favourable curvature `Q ≥ 0` gives `E ≥ 0`. -/
theorem energy_nonneg_of_Q_nonneg (hQ : ∀ l ∈ Icc (-op.L) op.L, 0 ≤ op.Q l)
    {ξ ξ' : ℝ → ℝ} (hξ : op.Admissible ξ ξ') : 0 ≤ op.energy ξ ξ' := by
  simpa using op.lower_bound_of_Q_ge (c := 0) (fun l hl => by simpa using hQ l hl) hξ

/-- Sanity: strictly favourable curvature `Q > 0` gives strict stability, via `w = 1`
at a positive level. -/
theorem energy_pos_of_Q_pos {c : ℝ} (hc : 0 < c)
    (hQ : ∀ l ∈ Icc (-op.L) op.L, c * op.W l ≤ op.Q l) {ξ ξ' : ℝ → ℝ}
    (hξ : op.Admissible ξ ξ') {l₀ : ℝ} (hl₀ : l₀ ∈ Icc (-op.L) op.L) (hne : ξ l₀ ≠ 0) :
    0 < op.energy ξ ξ' :=
  (op.constCertificate hQ).energy_pos op hc hξ hl₀ hne

/-- **Necessity, usable form.** If one admissible displacement has `E(ξ) < c M(ξ)`, then
there is no Barta certificate at level `c` (in particular no positive supersolution). -/
theorem no_certificate_of_energy_lt {c : ℝ} {ξ ξ' : ℝ → ℝ} (hξ : op.Admissible ξ ξ')
    (hlt : op.energy ξ ξ' < c * op.mass ξ) : IsEmpty (op.BartaCertificate c) :=
  ⟨fun cert => absurd (cert.lower_bound op hξ) (not_le.mpr hlt)⟩

/-- Special case: a single admissible displacement with negative energy rules out every
nonnegative-level certificate. -/
theorem no_certificate_of_energy_neg {c : ℝ} (hc : 0 ≤ c) {ξ ξ' : ℝ → ℝ}
    (hξ : op.Admissible ξ ξ') (hneg : op.energy ξ ξ' < 0) : IsEmpty (op.BartaCertificate c) :=
  op.no_certificate_of_energy_lt hξ (lt_of_lt_of_le hneg (mul_nonneg hc op.mass_nonneg))

/-- **`C²` witness (roadmap form).** If `w` is `C²`, `P` is `C¹` (globally), `w > 0` and
`-(P w')' + Q w ≥ c W w` on `[-L, L]` with `deriv`, then this is a Barta certificate. -/
def BartaCertificate.ofContDiff {c : ℝ} (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w)
    (hP : ContDiff ℝ 1 op.P) (hpos : ∀ l ∈ Icc (-op.L) op.L, 0 < w l)
    (hsuper : ∀ l ∈ Icc (-op.L) op.L,
      c * op.W l * w l ≤ -deriv (fun s => op.P s * deriv w s) l + op.Q l * w l) :
    op.BartaCertificate c where
  w := w
  w' := deriv w
  k := deriv (fun s => op.P s * deriv w s)
  hw l _ := ((hw.differentiable (by norm_num)) l).hasDerivAt
  hw'c := (hw.continuous_deriv (by norm_num)).continuousOn
  hk l _ := by
    have h1 : ContDiff ℝ 1 (deriv w) := by
      have := (contDiff_succ_iff_deriv (n := 1)).mp hw
      exact this.2.2
    exact ((hP.mul h1).differentiable (by norm_num) l).hasDerivAt
  hkc := by
    have h1 : ContDiff ℝ 1 (deriv w) := ((contDiff_succ_iff_deriv (n := 1)).mp hw).2.2
    exact ((hP.mul h1).continuous_deriv (by norm_num)).continuousOn
  pos := hpos
  super := hsuper

end BallooningOperator

/-! ## Constant coefficients: a genuine necessary and sufficient condition -/

/-- Energy with constant coefficients `p`, `q` on `[-L, L]`. -/
@[expose] def constEnergy (p q L : ℝ) (ξ ξ' : ℝ → ℝ) : ℝ :=
  newcombForm (fun _ => p) (fun _ => q) (-L) L ξ ξ'

/-- The constant-coefficient operator (`W = 1`) as a `BallooningOperator`. -/
@[expose] def constOp (p q L : ℝ) (hp : 0 < p) (hL : 0 < L) : BallooningOperator where
  L := L
  P := fun _ => p
  Q := fun _ => q
  W := fun _ => 1
  hL := hL
  P_pos _ _ := hp
  W_pos _ _ := one_pos
  P_cont := continuousOn_const
  Q_cont := continuousOn_const
  W_cont := continuousOn_const

/-- The cosine mode `cos(a l)`. -/
@[expose] def cosMode (a l : ℝ) : ℝ := Real.cos (a * l)

/-- Derivative of the cosine mode, `-a sin(a l)`. -/
@[expose] def cosMode' (a l : ℝ) : ℝ := -a * Real.sin (a * l)

theorem cosMode_hasDerivAt (a l : ℝ) : HasDerivAt (cosMode a) (cosMode' a l) l := by
  have := ((hasDerivAt_id l).const_mul a).cos
  change HasDerivAt (fun x => Real.cos (a * x)) _ l
  simpa [cosMode', mul_comm] using this

theorem cosMode_C1On (a x₀ x₁ : ℝ) : C1On (cosMode a) (cosMode' a) x₀ x₁ where
  deriv x _ := cosMode_hasDerivAt a x
  cont := by unfold cosMode'; fun_prop

/-- Cosine witness: for `0 < a` and `a L < π/2`, `cos(a l)` is a Barta certificate at
level `p a² + q` for the constant operator. -/
def cosCertificate {p q L a : ℝ} (hp : 0 < p) (hL : 0 < L) (ha : 0 < a)
    (haL : a * L < Real.pi / 2) : (constOp p q L hp hL).BartaCertificate (p * a ^ 2 + q) where
  w := cosMode a
  w' := cosMode' a
  k := fun l => -(p * a ^ 2) * Real.cos (a * l)
  hw l _ := cosMode_hasDerivAt a l
  hw'c := (by unfold cosMode'; fun_prop : Continuous (cosMode' a)).continuousOn
  hk l _ := by
    have := (((hasDerivAt_id l).const_mul a).sin.const_mul (-a)).const_mul p
    convert this using 1
    · funext s; simp [constOp, cosMode']
    · simp; ring
  hkc := by fun_prop
  pos l hl := by
    simp only [constOp] at hl
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [hl.1]
    · nlinarith [hl.2]
  super l _ := by simp [constOp, cosMode]; ring_nf; rfl

/-- `∫_{-L}^{L} cos²(π l/(2L)) = L`. -/
theorem integral_cos_sq_mode {L : ℝ} (hL : 0 < L) :
    ∫ l in (-L)..L, Real.cos (Real.pi / (2 * L) * l) ^ 2 = L := by
  have ha : Real.pi / (2 * L) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) ha, integral_cos_sq]
  have e1 : Real.pi / (2 * L) * L = Real.pi / 2 := by field_simp
  have e2 : Real.pi / (2 * L) * -L = -(Real.pi / 2) := by field_simp
  rw [e1, e2]
  simp
  field_simp

/-- `∫_{-L}^{L} sin²(π l/(2L)) = L`. -/
theorem integral_sin_sq_mode {L : ℝ} (hL : 0 < L) :
    ∫ l in (-L)..L, Real.sin (Real.pi / (2 * L) * l) ^ 2 = L := by
  have ha : Real.pi / (2 * L) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) ha, integral_sin_sq]
  have e1 : Real.pi / (2 * L) * L = Real.pi / 2 := by field_simp
  have e2 : Real.pi / (2 * L) * -L = -(Real.pi / 2) := by field_simp
  rw [e1, e2]
  simp
  field_simp

/-- **Explicit mode.** With `a = π/(2L)`, the energy of `cos(a l)` (which vanishes at
`±L`) is `(p a² + q) L`. -/
theorem const_energy_cosMode (p q : ℝ) {L : ℝ} (hL : 0 < L) :
    constEnergy p q L (cosMode (Real.pi / (2 * L))) (cosMode' (Real.pi / (2 * L))) =
      (p * (Real.pi / (2 * L)) ^ 2 + q) * L := by
  set a := Real.pi / (2 * L)
  have hc : IntervalIntegrable (fun l => Real.cos (a * l) ^ 2) MeasureTheory.volume (-L) L :=
    (by fun_prop : Continuous fun l => Real.cos (a * l) ^ 2).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun l => Real.sin (a * l) ^ 2) MeasureTheory.volume (-L) L :=
    (by fun_prop : Continuous fun l => Real.sin (a * l) ^ 2).intervalIntegrable _ _
  have e : (fun l => p * cosMode' a l ^ 2 + q * cosMode a l ^ 2) =
      fun l => (p * a ^ 2) * Real.sin (a * l) ^ 2 + q * Real.cos (a * l) ^ 2 := by
    funext l; simp [cosMode, cosMode']; ring
  unfold constEnergy newcombForm
  rw [e, integral_add (hs.const_mul _) (hc.const_mul _), integral_const_mul,
    integral_const_mul, integral_sin_sq_mode hL, integral_cos_sq_mode hL]
  ring

/-- The cosine mode vanishes at both ends. -/
theorem cosMode_ends {L : ℝ} (hL : 0 < L) :
    cosMode (Real.pi / (2 * L)) (-L) = 0 ∧ cosMode (Real.pi / (2 * L)) L = 0 := by
  have e1 : Real.pi / (2 * L) * L = Real.pi / 2 := by field_simp
  have e2 : Real.pi / (2 * L) * -L = -(Real.pi / 2) := by field_simp
  simp [cosMode, e1, e2]

/-- `L ≤ (π/2)√(p/(-q))` is equivalent to `p (π/(2L))² + q ≥ 0`. -/
theorem length_cond_iff {p q L : ℝ} (hp : 0 < p) (hq : q < 0) (hL : 0 < L) :
    L ≤ Real.pi / 2 * Real.sqrt (p / -q) ↔ 0 ≤ p * (Real.pi / (2 * L)) ^ 2 + q := by
  have hpq : 0 < p / -q := div_pos hp (by linarith)
  have e : Real.pi / 2 * Real.sqrt (p / -q) = Real.sqrt ((Real.pi / 2) ^ 2 * (p / -q)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e, Real.le_sqrt hL.le (by positivity)]
  have hq' : 0 < -q := by linarith
  have A : L ^ 2 ≤ (Real.pi / 2) ^ 2 * (p / -q) ↔ L ^ 2 * -q ≤ (Real.pi / 2) ^ 2 * p := by
    rw [mul_div_assoc', le_div_iff₀ hq']
  have h2 : p * (Real.pi / (2 * L)) ^ 2 = (Real.pi / 2) ^ 2 * p / L ^ 2 := by
    field_simp
  rw [A, h2, show (0 : ℝ) ≤ (Real.pi / 2) ^ 2 * p / L ^ 2 + q ↔
      -q ≤ (Real.pi / 2) ^ 2 * p / L ^ 2 from by constructor <;> intro h <;> linarith,
    le_div_iff₀ (by positivity), mul_comm]

/-- **Sturm/Jacobi criterion for constant coefficients.** For `p > 0`, `q < 0`, the
energy `∫ (p ξ'² + q ξ²)` is nonnegative for every C¹ `ξ` vanishing at `±L` if and only
if `L ≤ (π/2)·√(p/(-q))`. -/
theorem const_stable_iff {p q L : ℝ} (hp : 0 < p) (hq : q < 0) (hL : 0 < L) :
    (∀ ξ ξ' : ℝ → ℝ, C1On ξ ξ' (-L) L → ξ (-L) = 0 → ξ L = 0 → 0 ≤ constEnergy p q L ξ ξ')
      ↔ L ≤ Real.pi / 2 * Real.sqrt (p / -q) := by
  rw [length_cond_iff hp hq hL]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have := h _ _ (cosMode_C1On _ _ _) (cosMode_ends hL).1 (cosMode_ends hL).2
    rw [const_energy_cosMode p q hL] at this
    nlinarith
  · intro h ξ ξ' hξ h₀ h₁
    set op := constOp p q L hp hL
    have hadm : op.Admissible ξ ξ' := ⟨hξ, h₀, h₁⟩
    have hbound : ∀ δ : ℝ, 0 < δ →
        (p * (Real.pi / (2 * (L + δ))) ^ 2 + q) * op.mass ξ ≤ constEnergy p q L ξ ξ' := by
      intro δ hδ
      have ha : 0 < Real.pi / (2 * (L + δ)) := by positivity
      have haL : Real.pi / (2 * (L + δ)) * L < Real.pi / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Real.pi_pos]
      exact (cosCertificate (q := q) hp hL ha haL).lower_bound op hadm
    have hcont : ContinuousAt
        (fun δ : ℝ => (p * (Real.pi / (2 * (L + δ))) ^ 2 + q) * op.mass ξ) 0 := by
      have : (2 * (L + 0)) ≠ 0 := by positivity
      fun_prop (disch := assumption)
    have hlim := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Ioi 0) fun δ hδ => hbound δ hδ)
    simp only [add_zero] at hlim
    exact le_trans (mul_nonneg h op.mass_nonneg) hlim

/-! ## Exact polynomial Barta certificates -/

section poly
open PlasmaLean.Certificates.QPoly

/-- Barta residual `-(P w')' + Q w - c W w` for polynomial data (the Jacobi residual of
the shifted potential `Q - c W`). -/
@[expose] def bartaResidual (P Q W w : List ℚ) (c : ℚ) : List ℚ :=
  jacobiResidual P (add Q (scale (-c) W)) w 0

/-- The residual evaluates to `-(P w')' + Q w - c W w`. -/
theorem eval_bartaResidual (P Q W w : List ℚ) (c : ℚ) (x : ℝ) :
    eval (bartaResidual P Q W w c) x =
      -eval (deriv (mul P (deriv w))) x + eval Q x * eval w x - c * eval W x * eval w x := by
  simp [bartaResidual, jacobiResidual]; ring

/-- **Barta certificate from exact checks.** Accepted checks of `P ≥ 0`, `w ≥ m > 0` and
of the Barta residual `≥ 0` on `[a, b]` prove `c ∫ W ξ² ≤ ∫ (P ξ'² + Q ξ²)` for every C¹
`ξ` vanishing at `a` and `b`. -/
theorem barta_poly_certificate {P Q W w : List ℚ} {c m a b : ℚ} {pts : List ℚ}
    (hab : a ≤ b) (hm : 0 < m) (hP : checkOn P 0 a b pts = true)
    (hw : checkOn w m a b pts = true) (hR : checkOn (bartaResidual P Q W w c) 0 a b pts = true)
    {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' a b) (h₀ : ξ a = 0) (h₁ : ξ b = 0) :
    (c : ℝ) * ∫ x in (a : ℝ)..b, eval W x * ξ x ^ 2 ≤
      newcombForm (eval P) (eval Q) a b ξ ξ' := by
  have h := jacobi_poly_certificate (c := 0) hab hm hP hw hR hξ h₀ h₁
  simp only [Rat.cast_zero, zero_mul] at h
  have h1 := newcomb_integrable (f := eval P) (g := eval (add Q (scale (-c) W))) hξ
    (continuous_eval _).continuousOn (continuous_eval _).continuousOn
  have h2 : IntervalIntegrable (fun x => (c : ℝ) * (eval W x * ξ x ^ 2))
      MeasureTheory.volume a b :=
    (((continuous_eval W).continuousOn.mul (hξ.continuousOn.pow 2)).intervalIntegrable).const_mul _
  have e : newcombForm (eval P) (eval Q) a b ξ ξ' =
      newcombForm (eval P) (eval (add Q (scale (-c) W))) a b ξ ξ' +
        (c : ℝ) * ∫ x in (a : ℝ)..b, eval W x * ξ x ^ 2 := by
    unfold newcombForm
    rw [← integral_const_mul, ← integral_add h1 h2]
    congr 1; funext x; simp; ring
  linarith

/-- Witness for the example, found by a linear program outside Lean (untrusted). -/
@[expose] def exampleW : List ℚ :=
  [1, 0, -3943 / 2048, 0, 6899 / 4096, 0, -2049 / 2048, 0, 535 / 2048]

/-- Sixty-four uniform pieces of `[-1, 1]`. -/
@[expose] def grid64 : List ℚ := (List.range 64).map (fun i => -1 + ((i : ℚ) + 1) / 32)

/-- Accepted check: `P = 1 + l² ≥ 0` on `[-1, 1]`. -/
theorem example_P_check : checkOn [1, 0, 1] 0 (-1) 1 grid64 = true := by decide +kernel

/-- Accepted check: the witness is at least `1/64` on `[-1, 1]`. -/
theorem example_w_check : checkOn exampleW (1 / 64) (-1) 1 grid64 = true := by decide +kernel

/-- Accepted check: `-(P w')' + Q w - (1/4) w ≥ 0` on `[-1, 1]`. -/
theorem example_residual_check :
    checkOn (bartaResidual [1, 0, 1] [-7 / 2, 0, 4] [1] exampleW (1 / 4)) 0 (-1) 1 grid64 =
      true := by decide +kernel

/-- **Certified example.** On `[-1, 1]`, with `P = 1 + l²`, `Q = -7/2 + 4 l²` (bad
curvature near `l = 0`) and `W = 1`, every admissible `ξ` satisfies
`∫ (P ξ'² + Q ξ²) ≥ (1/4) ∫ ξ²`. (Numerically `λ₀ ≈ 0.585`.) The frozen-coefficient
bound `P ≥ 1`, `Q ≥ -7/2` cannot prove even `E ≥ 0`, since `π²/4 < 7/2`. -/
theorem example_poly {ξ ξ' : ℝ → ℝ} (hξ : C1On ξ ξ' (-1) 1) (h₀ : ξ (-1) = 0)
    (h₁ : ξ 1 = 0) :
    (1 / 4) * ∫ x in (-1 : ℝ)..1, ξ x ^ 2 ≤
      newcombForm (fun l => 1 + l ^ 2) (fun l => -7 / 2 + 4 * l ^ 2) (-1) 1 ξ ξ' := by
  have h := barta_poly_certificate (P := [1, 0, 1]) (Q := [-7 / 2, 0, 4]) (W := [1])
    (w := exampleW) (c := 1 / 4) (m := 1 / 64) (a := -1) (b := 1) (by norm_num) (by norm_num)
    example_P_check example_w_check example_residual_check (ξ := ξ) (ξ' := ξ')
    (by simpa using hξ) (by simpa using h₀) (by simpa using h₁)
  have eP : eval [1, 0, 1] = fun l => 1 + l ^ 2 := by funext l; simp; ring
  have eQ : eval [-7 / 2, 0, 4] = fun l => -7 / 2 + 4 * l ^ 2 := by funext l; simp; ring
  rw [eP, eQ] at h
  simpa using h

/-- The example as a `BallooningOperator` (`L = 1`, `W = 1`). -/
@[expose] def exampleOp : BallooningOperator where
  L := 1
  P := fun l => 1 + l ^ 2
  Q := fun l => -7 / 2 + 4 * l ^ 2
  W := fun _ => 1
  hL := one_pos
  P_pos _ _ := by positivity
  W_pos _ _ := one_pos
  P_cont := by fun_prop
  Q_cont := by fun_prop
  W_cont := continuousOn_const

/-- Corollary: strict ballooning stability of the example segment — every nonzero
admissible displacement has positive energy. -/
theorem example_energy_pos {ξ ξ' : ℝ → ℝ} (hξ : exampleOp.Admissible ξ ξ') {l₀ : ℝ}
    (hl₀ : l₀ ∈ Icc (-1 : ℝ) 1) (hne : ξ l₀ ≠ 0) : 0 < exampleOp.energy ξ ξ' := by
  have hm := exampleOp.mass_pos hξ.c1 hl₀ hne
  have h := example_poly hξ.c1 hξ.left hξ.right
  have : exampleOp.mass ξ = ∫ x in (-1 : ℝ)..1, ξ x ^ 2 := by
    simp [exampleOp, BallooningOperator.mass]
  change _ ≤ exampleOp.energy ξ ξ' at h
  linarith

/-- Rejected fixture: the constant witness `w = 1` does not certify the example at level
`0` (the residual `Q = -7/2 + 4 l²` is negative at `l = 0`). -/
theorem example_const_reject :
    checkOn (bartaResidual [1, 0, 1] [-7 / 2, 0, 4] [1] [1] 0) 0 (-1) 1 grid64 = false := by
  decide +kernel

end poly

end PlasmaLean.Stability.Ballooning
