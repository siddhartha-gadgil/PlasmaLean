/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Scalar checks for a position error in a moving two-dimensional frame

Coordinates and radii use units of 2⁻⁸⁰, frame entries use units of 2⁻⁴⁰,
and outward time has step 1/64. The full signed polynomial determines both
endpoints of every reference. Adjacent slabs inherit the frame matrix, physical
reference endpoint, and transformed-coordinate error radius.
-/

@[expose] public section
namespace PlasmaLean.Certificates.PositionFrameSlabs

/-- Coordinates in integer units of 2⁻⁸⁰. -/
@[ext] structure Point where
  x : ℤ
  y : ℤ
deriving BEq

/-- Matrix in row-major order and units of 2⁻⁴⁰. -/
structure Frame where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving BEq

/-- The data inherited by the next angular slab. -/
structure State where
  point : Point
  frame : Frame
  radius : ℕ

/-- All fractions are the exact signed quantities from the trajectory witness. -/
structure Step where
  px : List ℤ
  py : List ℤ
  frame : Frame
  jump : Point
  jumpBound : ℕ
  incoming : ℕ
  outgoing : ℕ
  trial : ℕ
  physicalIn : ℕ
  physicalOut : ℕ
  physicalTrial : ℕ
  detLower : ℚ
  op : ℚ
  mu : ℚ
  defect : ℚ

/-- Evaluate the stored ascending integer coefficients at either signed endpoint. -/
def atSign (p : List ℤ) (s : ℤ) : ℤ := p.foldr (fun c y => c + s*y) 0

/-- Exact difference between the new polynomial start and the old reference end. -/
def displacement (s : State) (r : Step) : Point :=
  ⟨atSign r.px (-1) - s.point.x, atSign r.py (-1) - s.point.y⟩

/-- The endpoint conditions for the next slab. -/
def next (r : Step) : State := ⟨⟨atSign r.px 1, atSign r.py 1⟩, r.frame, r.outgoing⟩

/-- Determinant numerator of a packed matrix. -/
def det (m : Frame) : ℤ := m.a*m.d - m.b*m.c

/-- Coefficient of s in det(center + s*rate). -/
def mixed (l r : Frame) : ℤ := l.a*r.d + r.a*l.d - l.b*r.c - r.b*l.c

/-- Twice the midpoint matrix in packed units. -/
def center (l r : Frame) : Frame := ⟨l.a+r.a, l.b+r.b, l.c+r.c, l.d+r.d⟩

/-- Twice the matrix coefficient of s in packed units. -/
def rate (l r : Frame) : Frame := ⟨r.a-l.a, r.b-l.b, r.c-l.c, r.d-l.d⟩

/-- Lower bound for the affine frame determinant throughout the normalized time cell. -/
def detFloor (l r : Frame) : ℚ :=
  let p := center l r
  let d := rate l r
  ((det p - |mixed p d| - |det d| : ℤ) : ℚ) / (4*2^80)

/-- Product of maximal absolute column and row sums of the linearly interpolated frame. -/
def normProduct (l r : Frame) : ℤ :=
  let a := max |l.a| |r.a|
  let b := max |l.b| |r.b|
  let c := max |l.c| |r.c|
  let d := max |l.d| |r.d|
  max (a+c) (b+d) * max (a+b) (c+d)

/-- Squared norm of the jump multiplied by the squared packed determinant. -/
def jumpNumerator (m : Frame) (p : Point) : ℤ :=
  2^80 * ((m.d*p.x - m.b*p.y)^2 + (m.a*p.y - m.c*p.x)^2)

/-- Compare signed integers through the positive part of their difference. -/
def leZ (x y : ℤ) : Bool := (x-y).toNat == 0

@[simp] theorem leZ_true {x y : ℤ} : leZ x y = true ↔ x ≤ y := by
  simp [leZ]

/-- Rational comparison by exact cross multiplication. -/
def leQ (x y : ℚ) : Bool := leZ (x.num * y.den) (y.num * x.den)

/-- Strict rational comparison by exact cross multiplication. -/
def ltQ (x y : ℚ) : Bool := !(leQ y x)

@[simp] theorem leQ_true {x y : ℚ} : leQ x y = true ↔ x ≤ y := by
  simp only [leQ, leZ_true]
  exact (Rat.le_iff ..).symm

@[simp] theorem ltQ_true {x y : ℚ} : ltQ x y = true ↔ x < y := by
  simp [ltQ, ← Bool.not_eq_true]

/-- Uniform limits to certify along one trajectory. -/
structure Limits where
  operator : ℚ
  physical : ℚ

/-- Sharp limits used for the section-zero u=0.470 pilot. -/
def pilotLimits : Limits := ⟨12/5, 1/300000⟩

/-- Common limits covering both symmetry sections and all eight endpoints. -/
def allLimits : Limits := ⟨31/10, 69/20000000⟩

/-- Check the polynomial reference jump and both affine matrix bounds. -/
def geometry (lim : Limits) (s : State) (r : Step) : Bool :=
  let diff := displacement s r
  (r.px.length == 8) && (r.py.length == 8) &&
    (r.jump.x == diff.x) && (r.jump.y == diff.y) && leZ 1 (det s.frame) &&
    leZ (jumpNumerator s.frame r.jump) ((r.jumpBound : ℤ)^2 * (det s.frame)^2) &&
    ltQ (97/100) r.detLower && leQ r.detLower (detFloor s.frame r.frame) &&
    leQ 0 r.op && ltQ r.op lim.operator &&
    leQ (normProduct s.frame r.frame : ℤ) (2^80*r.op^2)

/-- Check the reduced differential inequality in rational arithmetic and convert each
transformed radius to physical units using the operator bound. -/
def growth (lim : Limits) (s : State) (r : Step) : Bool :=
  let g := max 0 r.mu
  (r.incoming == s.radius+r.jumpBound) && leQ 0 r.defect && ltQ g 64 &&
    leQ (64*r.incoming + 2^80*r.defect) (r.outgoing*(64-g)) &&
    r.outgoing.blt r.trial && leQ (r.op*r.incoming) r.physicalIn &&
    leQ (r.op*r.outgoing) r.physicalOut && leQ (r.op*r.trial) r.physicalTrial &&
    ltQ (r.physicalOut / 2^80) lim.physical && (100000*r.physicalTrial).blt (2^80)

/-- Both checks are required on every adjacent slab. -/
def test (lim : Limits) (s : State) (r : Step) : Bool := geometry lim s r && growth lim s r

/-- Value of an affine matrix entry at coordinate s in [-1,1]. -/
noncomputable def entry (a b : ℤ) (s : ℝ) : ℝ :=
  ((a+b : ℤ) + s*(b-a : ℤ)) / (2*2^40)

/-- Actual normalized determinant of the interpolated frame. -/
noncomputable def affineDet (l r : Frame) (s : ℝ) : ℝ :=
  entry l.a r.a s * entry l.d r.d s - entry l.b r.b s * entry l.c r.c s

/-- The determinant coefficient estimate applies at every intermediate time. -/
theorem detFloor_le (l r : Frame) {s : ℝ} (hs : |s| ≤ 1) :
    (detFloor l r : ℝ) ≤ affineDet l r s := by
  let p := center l r
  let d := rate l r
  have expand : affineDet l r s =
      ((det p : ℝ) + (mixed p d : ℝ)*s + (det d : ℝ)*s^2) / (4*2^80) := by
    simp only [affineDet, entry, det, p, d, mixed, center, rate]
    push_cast
    ring
  have bound (k y : ℝ) (hy : |y| ≤ 1) : -|k| ≤ k*y :=
    (neg_le_neg (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg k) hy)).trans
      (neg_abs_le (k*y))
  rw [expand]
  have e : (detFloor l r : ℝ) =
      ((det p : ℝ) - |(mixed p d : ℝ)| - |(det d : ℝ)|) / (4*2^80) := by
    simp [detFloor, p, d]
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h2 : |s^2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  linarith only [bound (mixed p d) s hs, bound (det d) (s^2) h2]

/-- The jump, the inverse-frame quadratic bound, and the stated determinant
and matrix-norm certificates all concern the two consecutive stored frames. -/
theorem geometry_sound {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true) :
    r.jump = displacement s r ∧ 0 < det s.frame ∧
    jumpNumerator s.frame r.jump ≤ (r.jumpBound : ℤ)^2 * (det s.frame)^2 ∧
    (97/100 : ℝ) < (r.detLower : ℝ) ∧
    (∀ t : ℝ, |t| ≤ 1 → (r.detLower : ℝ) ≤ affineDet s.frame r.frame t) ∧
    0 ≤ (r.op : ℝ) ∧ (r.op : ℝ) < lim.operator ∧
    (normProduct s.frame r.frame : ℝ) ≤ 2^80*(r.op : ℝ)^2 := by
  simp only [geometry, Bool.and_eq_true, beq_iff_eq, leZ_true, leQ_true, ltQ_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hx⟩, hy⟩, hd⟩, hj⟩, hl⟩, hf⟩, h0⟩, ho⟩, hp⟩ := h
  have eq : r.jump = displacement s r := Point.ext hx hy
  refine ⟨eq, by omega, hj, ?_, ?_, by exact_mod_cast h0, ?_, by exact_mod_cast hp⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hl
  · intro t ht
    exact (Rat.cast_le.mpr hf).trans (detFloor_le _ _ ht)
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr ho

/-- Norm of the new reference start minus the old reference end, in the inverse
start frame. Both sides use units of 2⁻⁸⁰. -/
theorem inverse_jump {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true) :
    let m := s.frame
    let p := displacement s r
    Real.sqrt (((2^40 : ℝ)*(m.d*p.x-m.b*p.y : ℤ) / (det m : ℝ))^2 +
      ((2^40 : ℝ)*(m.a*p.y-m.c*p.x : ℤ) / (det m : ℝ))^2) ≤ r.jumpBound := by
  obtain ⟨hp, hd, hj, _⟩ := geometry_sound h
  dsimp only
  rw [← hp]
  have dd : (det s.frame : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  simp only [div_pow]
  rw [← add_div, div_le_iff₀ (sq_pos_of_ne_zero dd)]
  have num := (Int.cast_le (R := ℝ)).mpr hj
  unfold jumpNumerator at num
  push_cast at num ⊢
  nlinarith only [num]

private noncomputable def weight (a b : ℤ) : ℝ := ((max |a| |b| : ℤ) : ℝ) / 2^40

private theorem entry_weight (a b : ℤ) {t : ℝ} (ht : |t| ≤ 1) :
    |entry a b t| ≤ weight a b := by
  have T := abs_le.mp ht
  have w : (max |a| |b| : ℤ) ≥ |a| := le_max_left ..
  have v : (max |a| |b| : ℤ) ≥ |b| := le_max_right ..
  have wa : |(a : ℝ)| ≤ ((max |a| |b| : ℤ) : ℝ) := by exact_mod_cast w
  have wb : |(b : ℝ)| ≤ ((max |a| |b| : ℤ) : ℝ) := by exact_mod_cast v
  rw [entry, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2*2^40)]
  apply (div_le_iff₀ (by norm_num)).mpr
  rw [show ((a+b : ℤ) : ℝ) + t*((b-a : ℤ) : ℝ) = (1-t)*a+(1+t)*b by push_cast; ring]
  apply (abs_add_le ..).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-t),
    abs_of_nonneg (by linarith : 0 ≤ 1+t)]
  unfold weight
  linarith only [mul_le_mul_of_nonneg_left wa (show 0 ≤ 1-t by linarith),
    mul_le_mul_of_nonneg_left wb (show 0 ≤ 1+t by linarith)]

private theorem row_norm {a b A B x y : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    (a*x+b*y)^2 ≤ (A+B)*(A*x^2+B*y^2) := by
  have hA := (abs_nonneg _).trans ha
  have hB := (abs_nonneg _).trans hb
  have bound : |a*x+b*y| ≤ A*|x|+B*|y| := by
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    gcongr
  calc
    (a*x+b*y)^2 = |a*x+b*y|^2 := (sq_abs _).symm
    _ ≤ (A*|x|+B*|y|)^2 := pow_le_pow_left₀ (abs_nonneg _) bound _
    _ ≤ (A+B)*(A*x^2+B*y^2) := by
      rw [← sq_abs x, ← sq_abs y]
      nlinarith only [mul_nonneg (mul_nonneg hA hB) (sq_nonneg (|x|-|y|))]

/-- The certified column/row estimate bounds the Euclidean action of the interpolated
matrix on every vector, at every intermediate time. -/
theorem frame_norm_sq {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    {t : ℝ} (ht : |t| ≤ 1) (x y : ℝ) :
    let l := s.frame
    let e := r.frame
    (entry l.a e.a t*x + entry l.b e.b t*y)^2 + (entry l.c e.c t*x + entry l.d e.d t*y)^2
      ≤ (r.op : ℝ)^2*(x^2+y^2) := by
  dsimp only
  obtain ⟨_,_,_,_,_,_,_,hop⟩ := geometry_sound h
  let l := s.frame
  let e := r.frame
  let A := weight l.a e.a
  let B := weight l.b e.b
  let C := weight l.c e.c
  let D := weight l.d e.d
  let R := max (A+B) (C+D)
  let K := max (A+C) (B+D)
  have A0 : 0 ≤ A := (abs_nonneg _).trans (entry_weight _ _ ht)
  have B0 : 0 ≤ B := (abs_nonneg _).trans (entry_weight _ _ ht)
  have C0 : 0 ≤ C := (abs_nonneg _).trans (entry_weight _ _ ht)
  have D0 : 0 ≤ D := (abs_nonneg _).trans (entry_weight _ _ ht)
  have R0 : 0 ≤ R := (add_nonneg A0 B0).trans (le_max_left ..)
  have prod : R*K ≤ (r.op : ℝ)^2 := by
    have scale : (normProduct l e : ℝ) = 2^80 * (R*K) := by
      unfold normProduct R K A B C D weight
      push_cast
      simp only [← add_div, max_div_div_right (by positivity : (0 : ℝ) ≤ 2^40)]
      ring
    rw [scale] at hop
    linarith only [hop]
  have row1 := row_norm (x := x) (y := y) (entry_weight l.a e.a ht) (entry_weight l.b e.b ht)
  have row2 := row_norm (x := x) (y := y) (entry_weight l.c e.c ht) (entry_weight l.d e.d ht)
  apply (add_le_add row1 row2).trans
  calc
    (A+B)*(A*x^2+B*y^2)+(C+D)*(C*x^2+D*y^2) ≤
        R*(A*x^2+B*y^2)+R*(C*x^2+D*y^2) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
        (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
    _ = R*((A+C)*x^2+(B+D)*y^2) := by ring
    _ ≤ R*(K*x^2+K*y^2) := by
      apply mul_le_mul_of_nonneg_left _ R0
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left ..) (sq_nonneg x))
        (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg y))
    _ = (R*K)*(x^2+y^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right prod (by positivity)

/-- Exact rational scalar hypotheses, in physical units, of the moving-frame
Gronwall step. The strict trial bound is valid up to the next step, including the
new reference jump. -/
theorem growth_sound {lim : Limits} {s : State} {r : Step} (h : growth lim s r = true) :
    r.incoming = s.radius + r.jumpBound ∧ 0 ≤ (r.defect : ℝ) ∧
    max 0 (r.mu : ℝ) / 64 < 1 ∧
    ((r.incoming : ℝ) / 2^80 + r.defect/64) / (1-max 0 (r.mu : ℝ)/64)
      ≤ (r.outgoing : ℝ) / 2^80 ∧
    (r.outgoing : ℝ) / 2^80 < (r.trial : ℝ) / 2^80 ∧
    (r.op : ℝ) * r.incoming ≤ r.physicalIn ∧
    (r.op : ℝ) * r.outgoing ≤ r.physicalOut ∧
    (r.op : ℝ) * r.trial ≤ r.physicalTrial ∧
    (r.physicalOut : ℝ) / 2^80 < lim.physical ∧
    (r.physicalTrial : ℝ) / 2^80 < 1/100000 := by
  simp only [growth, Bool.and_eq_true, beq_iff_eq, leQ_true, ltQ_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨eq, he⟩, hg⟩, hh⟩, hT⟩, hi⟩, ho⟩, ht⟩, hm⟩, hm'⟩ := h
  have hg' : max 0 (r.mu : ℝ) < 64 := by exact_mod_cast hg
  have hh' : 64*(r.incoming : ℝ) + 2^80*(r.defect : ℝ) ≤
      r.outgoing*(64-max 0 (r.mu : ℝ)) := by exact_mod_cast hh
  refine ⟨eq, by exact_mod_cast he, by linarith, ?_, ?_, by exact_mod_cast hi,
    by exact_mod_cast ho, by exact_mod_cast ht, ?_, ?_⟩
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith only [hh']
  · gcongr
  · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_lt (K := ℝ)).mpr hm
  · have hm'' : 100000*(r.physicalTrial : ℝ) < 2^80 := by exact_mod_cast hm'
    linarith

/-- One block checks a bounded list and exposes the exact exit state. -/
def run (lim : Limits) : State → List Step → Bool × State
  | s, [] => (true,s)
  | s, r::rs =>
    let rest := run lim (next r) rs
    (test lim s r && rest.1,rest.2)

/-- Pointwise validity with exactly the previous step's exit data. -/
def Each (lim : Limits) : State → List Step → Prop
  | _, [] => True
  | s, r::rs => test lim s r = true ∧ Each lim (next r) rs

/-- Execution provides the checked hypotheses for every member of one chunk. -/
theorem run_each {lim : Limits} {s e : State} {rs : List Step}
    (h : run lim s rs = (true, e)) : Each lim s rs := by
  induction rs generalizing s with
  | nil => trivial
  | cons r rs ih =>
    have hb := congrArg Prod.fst h
    change (_ && _) = true at hb
    have he := congrArg Prod.snd h
    obtain ⟨ok,rest⟩ := Bool.and_eq_true_iff.mp hb
    exact ⟨ok,ih (Prod.ext rest he)⟩

/-- Blocks compose only when all four endpoint matrix entries, both endpoint
coordinates, and the inherited error radius coincide exactly. -/
inductive Chain (lim : Limits) : State → List (List Step) → ℕ → State → Prop
  | nil s : Chain lim s [] 0 s
  | cons {s m e n rs blocks} (ok : run lim s rs = (true,m)) (tail : Chain lim m blocks n e) :
      Chain lim s (rs::blocks) (rs.length+n) e

/-- The exit data obtained from one checked block feed the next block. -/
def All (lim : Limits) : State → List (List Step) → Prop
  | _, [] => True
  | s, rs::blocks => Each lim s rs ∧ All lim (run lim s rs).2 blocks

/-- Every recorded slab inherits the initial state and its local tests hold. -/
theorem Chain.sound {lim : Limits} {s e : State} {bs : List (List Step)} {n : ℕ}
    (h : Chain lim s bs n e) : All lim s bs := by
  induction h with
  | nil => trivial
  | cons ok _ ih => exact ⟨run_each ok, by simpa only [ok] using ih⟩

/-- Degenerate trace of zero length carries its exact state. -/
theorem empty (lim : Limits) (s e : State) : Chain lim s [] 0 e ↔ e = s := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil _

/-- The zero reference in a unit stationary frame, with one unit of trial slack. -/
def stationary : Step :=
  ⟨List.replicate 8 0, List.replicate 8 0, ⟨2^40, 0, 0, 2^40⟩, ⟨0, 0⟩,
   0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩

/-- A zero-defect stationary reference passes without increasing the endpoint radius. -/
theorem stationary_checked : test pilotLimits (next stationary) stationary = true := by
  with_unfolding_all rfl

/-- Equality with the trial boundary fails the strict first-exit condition. -/
theorem reject_equal_trial :
    test pilotLimits (next stationary) {stationary with trial := 0} = false := by
  with_unfolding_all rfl

end PlasmaLean.Certificates.PositionFrameSlabs
