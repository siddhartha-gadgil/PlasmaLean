/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGradientCheck
public import PlasmaLean.Design.DommaschkTubeCheck
public import PlasmaLean.Design.DommaschkTubeSymmetry
public import PlasmaLean.Certificates.TrajectoryHarmonicPacket
public import PlasmaLean.Theory.Fields.FlowLabelSymmetric

/-!
# Field bounds on the tube of a chain of position-frame slabs

The box check `fine` of `DommaschkGradientCheck` is applied to one box per slab of a chain of
position-frame records: the rectangle in `(R, z)` that contains the trial ellipsoid of the slab,
and the arc of `(cos 2φ, sin 2φ)` over the angles of the slab. Both are computed from the record
and from the checked centre values of the harmonic packets, with outward rounding to the
fixed-point grid.

* `floorFx`, `ceilFx`, `QI.toFIv`: outward rounding of a rational interval.
* `rect r j shift`, `mem_rect`: the coordinate interval of the trial tube of the record `r`.
* `arcBox nc ns`, `mem_arcBox`: the arc within `1/64` of an angle whose cosine and sine are
  `nc / 2⁹⁶` and `ns / 2⁹⁶` up to `2⁻⁹⁵`.
* `slabBox`, `SlabQ`, `slabQ_of_cert`: a subdivision certificate on the box of slab `k` gives the
  polynomial inequalities `Fine` on the trial tube of the slab.
* `SlabsOn`, with `SlabsOn.append` and `SlabsOn.at`: the statement along a list of records.
* `fine_of_outer`, `fine_of_double`: the inequalities on the outer tube of the chain and on its
  two-sided extension by the reflection `flipIso` (using `Fine.reflect`).
* `field_of_double`: on the two-sided tube, `‖∇|B|‖ ≤ g`, `s ≤ |B|`, planar speed at most `m`,
  and `PolyBounds b c m`.

**Sanity.** `floorFx_fixture`, `ceilFx_fixture` (rounding of `1/3` and of an exact grid point),
`arcBox_fixture` (the arc around the angle zero), `slabsOn_nil`.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeField
open DommaschkKam DommaschkBounceField Certificates.ValidatedQuadrature
open Certificates Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
open Certificates.PositionFrameTube Certificates.TrajectoryHarmonicPacket
open Certificates.TrajectoryTrig
open DommaschkGradientCheck DommaschkRegionFieldBounds DommaschkTubeSymmetry
open DommaschkCartesianAngleFlow DommaschkJacobian Contract Fields Set

/-! ## Outward rounding to the fixed-point grid -/

/-- The largest fixed-point integer `n` with `n / 2³² ≤ q`. -/
def floorFx (q : ℚ) : ℤ := (q.num * 4294967296) / (q.den : ℤ)

/-- The smallest fixed-point integer `n` with `q ≤ n / 2³²`. -/
def ceilFx (q : ℚ) : ℤ := -floorFx (-q)

theorem floorFx_le (q : ℚ) : fxVal (floorFx q) ≤ (q : ℝ) := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.pos
  have h : floorFx q * (q.den : ℤ) ≤ q.num * 4294967296 := Int.ediv_mul_le _ hd.ne'
  have h' : (floorFx q : ℝ) * q.den ≤ q.num * 4294967296 := by exact_mod_cast h
  have hd' : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  rw [fxVal, fxScale, Rat.cast_def, div_le_div_iff₀ (by norm_num) hd']
  push_cast
  linarith

theorem le_ceilFx (q : ℚ) : (q : ℝ) ≤ fxVal (ceilFx q) := by
  have h := floorFx_le (-q)
  simp only [ceilFx, fxVal, Int.cast_neg, neg_div, Rat.cast_neg] at h ⊢
  linarith

/-- The fixed-point interval that contains a rational interval. -/
def _root_.PlasmaLean.Design.DommaschkGradientCheck.QI.toFIv (I : QI) : FIv :=
  ⟨floorFx I.lo, ceilFx I.hi, true⟩

theorem mem_toFIv {I : QI} {x : ℝ} (h : I.Mem x) : I.toFIv.Mem x :=
  fun _ => ⟨(floorFx_le _).trans h.1, h.2.trans (le_ceilFx _)⟩

/-- **Sanity**: `⌊2³² / 3⌋ = 1431655765`. -/
theorem floorFx_fixture : floorFx (1 / 3) = 1431655765 ∧ ceilFx (1 / 3) = 1431655766 := by
  constructor <;> with_unfolding_all rfl

/-- **Sanity**: a grid point is not moved. -/
theorem ceilFx_fixture : floorFx (-3 / 2) = -6442450944 ∧ ceilFx (-3 / 2) = -6442450944 := by
  constructor <;> with_unfolding_all rfl

/-! ## The coordinate rectangle of a slab -/

/-- The interval of the coordinate `j` (minus `shift`) on the trial tube of the record: the
constant coefficient of the reference polynomial, enlarged by the other coefficients and by
`op · trial / 2⁸⁰`. -/
def rect (r : Step) (j : Fin 2) (shift : ℚ) : FIv :=
  QI.toFIv
    ⟨(polynomial r j).headD 0 - (r.op * r.trial / 2 ^ 80 + magnitude (polynomial r j).tail) - shift,
      (polynomial r j).headD 0 + (r.op * r.trial / 2 ^ 80 + magnitude (polynomial r j).tail) -
        shift⟩

theorem abs_eval_sub_head {τ : ℝ} (hτ : |τ| ≤ 1) (p : List ℚ) :
    |QPoly.eval p τ - ((p.headD 0 : ℚ) : ℝ)| ≤ ((magnitude p.tail : ℚ) : ℝ) := by
  cases p with
  | nil => simp [magnitude]
  | cons a p =>
    have h := abs_eval_le hτ p
    simp only [QPoly.eval_cons, List.headD_cons, List.tail_cons, add_sub_cancel_left, abs_mul]
    calc |τ| * |QPoly.eval p τ| ≤ 1 * (magnitude p : ℝ) :=
          mul_le_mul hτ h (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _

theorem mem_rect {r : Step} {j : Fin 2} (shift : ℚ) {τ x : ℝ} (hτ : |τ| ≤ 1)
    (hx : |x - QPoly.eval (polynomial r j) τ| ≤ (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80)) :
    (rect r j shift).Mem (x - shift) := by
  apply mem_toFIv
  obtain ⟨a, b⟩ := abs_le.mp hx
  obtain ⟨c, d⟩ := abs_le.mp (abs_eval_sub_head hτ (polynomial r j))
  simp only [QI.Mem]
  push_cast
  constructor <;> linarith

/-! ## The arc of a slab -/

/-- Enclosures of `cos θ` and `sin θ` for `θ` within `1/64` of an angle whose cosine and sine
are `nc / 2⁹⁶` and `ns / 2⁹⁶` up to `2⁻⁹⁵`. -/
def arcBox (nc ns : ℤ) : FIv × FIv :=
  let ca : QI := ⟨nc / 2 ^ 96 - 1 / 2 ^ 95, nc / 2 ^ 96 + 1 / 2 ^ 95⟩
  let sa : QI := ⟨ns / 2 ^ 96 - 1 / 2 ^ 95, ns / 2 ^ 96 + 1 / 2 ^ 95⟩
  let cd : QI := ⟨8191 / 8192, 1⟩
  let sd : QI := ⟨-1 / 64, 1 / 64⟩
  (((ca.mul cd).add (sa.mul sd)).toFIv, ((sa.mul cd).add (ca.mul sd)).toFIv)

theorem mem_arcBox {a : ℚ} (c : Centre false a) (z : Centre true a) {θ : ℝ}
    (h : |θ - (a : ℝ)| ≤ 1 / 64) :
    (arcBox c.numerator z.numerator).1.Mem (Real.cos θ) ∧
      (arcBox c.numerator z.numerator).2.Mem (Real.sin θ) := by
  obtain ⟨c0, c1⟩ := abs_le.mp c.error
  obtain ⟨s0, s1⟩ := abs_le.mp z.error
  simp only [wave] at c0 c1 s0 s1
  push_cast at c0 c1 s0 s1
  have mca : (⟨c.numerator / 2 ^ 96 - 1 / 2 ^ 95, c.numerator / 2 ^ 96 + 1 / 2 ^ 95⟩ : QI).Mem
      (Real.cos a) := by
    simp only [QI.Mem]
    push_cast
    constructor <;> linarith
  have msa : (⟨z.numerator / 2 ^ 96 - 1 / 2 ^ 95, z.numerator / 2 ^ 96 + 1 / 2 ^ 95⟩ : QI).Mem
      (Real.sin a) := by
    simp only [QI.Mem]
    push_cast
    constructor <;> linarith
  have sq : (θ - a) ^ 2 ≤ (1 / 64) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have mcd : (⟨8191 / 8192, 1⟩ : QI).Mem (Real.cos (θ - a)) := by
    simp only [QI.Mem]
    push_cast
    exact ⟨by linarith [Real.one_sub_sq_div_two_le_cos (x := θ - a)], Real.cos_le_one _⟩
  obtain ⟨d0, d1⟩ := abs_le.mp ((Real.abs_sin_le_abs (x := θ - a)).trans h)
  have msd : (⟨-1 / 64, 1 / 64⟩ : QI).Mem (Real.sin (θ - a)) := by
    simp only [QI.Mem]
    push_cast
    constructor <;> linarith
  have msd' : (⟨-1 / 64, 1 / 64⟩ : QI).Mem (-Real.sin (θ - a)) := by
    simp only [QI.Mem]
    push_cast
    constructor <;> linarith
  have ec : Real.cos θ = Real.cos a * Real.cos (θ - a) + Real.sin a * -Real.sin (θ - a) := by
    have := Real.cos_add a (θ - a)
    rw [add_sub_cancel] at this
    rw [this]
    ring
  have es : Real.sin θ = Real.sin a * Real.cos (θ - a) + Real.cos a * Real.sin (θ - a) := by
    have := Real.sin_add a (θ - a)
    rw [add_sub_cancel] at this
    exact this
  constructor
  · rw [ec]
    exact mem_toFIv (QI.mem_add (QI.mem_mul mca mcd) (QI.mem_mul msa msd'))
  · rw [es]
    exact mem_toFIv (QI.mem_add (QI.mem_mul msa mcd) (QI.mem_mul mca msd))

/-- **Sanity**: around the angle zero the cosine is enclosed in `[1 − 2⁻¹³, 1]` and the sine in
`[−1/64, 1/64]`, up to the rounding. -/
theorem arcBox_fixture :
    arcBox (2 ^ 96) 0 = (⟨4294443007, 4294967297, true⟩, ⟨-67108865, 67108865, true⟩) := by
  with_unfolding_all rfl

/-! ## One slab -/

/-- The box of a slab: the rectangle of the record and the arc of the centre values. -/
def slabBox (r : Step) (nc ns : ℤ) : Box :=
  ⟨rect r 0 (29 / 32), rect r 1 0, (arcBox nc ns).1, (arcBox nc ns).2⟩

/-- The polynomial inequalities on the trial tube of the slab `k` with record `r`: at every
angle of the slab, at every point whose coordinates are within `op · trial / 2⁸⁰` of the
reference polynomials. -/
def SlabQ (g s b c m : ℚ) (k : ℕ) (r : Step) : Prop :=
  ∀ t ∈ Icc ((k : ℝ) / 64) ((k : ℝ) / 64 + 1 / 64), ∀ x : Plane,
    (∀ j : Fin 2, |x j - QPoly.eval (polynomial r j) (coord ((k : ℝ) / 64) t)| ≤
      (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80)) →
    Fine g s b c m (x 0 - dkR0) (x 1) (Real.cos (2 * t)) (Real.sin (2 * t))

/-- **One slab.** A subdivision certificate on the box of the slab, with the centre values of
the harmonic packet of the slab, gives the polynomial inequalities on its trial tube. -/
theorem slabQ_of_cert {i k : ℕ} (pk : Packet i) (hk : i = k) {g s b c m : ℚ} (hb : 0 ≤ b)
    (hc : 0 ≤ c) {r : Step}
    (cert : Cert g s b c m
      (slabBox r (pk false 0).cosCentre.numerator (pk false 0).sinCentre.numerator)) :
    SlabQ g s b c m k r := by
  subst hk
  intro t ht x hx
  apply cert.sound hb hc
  have hτ := abs_coord_le ht
  have ang : |2 * t - (((2 * i + 1 : ℚ) * frequency false 0 / 64 : ℚ) : ℝ)| ≤ 1 / 64 := by
    simp only [frequency, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, Nat.cast_zero, zero_add,
      mul_one, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
      Rat.cast_one]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨mc, ms⟩ := mem_arcBox (pk false 0).cosCentre (pk false 0).sinCentre ang
  refine ⟨?_, ?_, mc, ms⟩
  · have h := mem_rect (29 / 32) hτ (hx 0)
    rwa [show ((29 / 32 : ℚ) : ℝ) = dkR0 by norm_num [dkR0]] at h
  · have h := mem_rect 0 hτ (hx 1)
    rwa [Rat.cast_zero, sub_zero] at h

/-! ## A chain of slabs -/

/-- A statement about the slab `k` and its record, along a list of records starting at the
slab `k`. -/
def SlabsOn (Q : ℕ → Step → Prop) : ℕ → List Step → Prop
  | _, [] => True
  | k, r :: rs => Q k r ∧ SlabsOn Q (k + 1) rs

/-- **Sanity**: the empty chain. -/
theorem slabsOn_nil (Q : ℕ → Step → Prop) (k : ℕ) : SlabsOn Q k [] := trivial

theorem SlabsOn.append {Q : ℕ → Step → Prop} {k : ℕ} {l r : List Step} (h₁ : SlabsOn Q k l)
    (h₂ : SlabsOn Q (k + l.length) r) : SlabsOn Q k (l ++ r) := by
  induction l generalizing k with
  | nil => simpa using h₂
  | cons x xs ih =>
    refine ⟨h₁.1, ih h₁.2 ?_⟩
    rwa [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm] at h₂

theorem SlabsOn.at {Q : ℕ → Step → Prop} {k : ℕ} {rows : List Step} (h : SlabsOn Q k rows)
    {j : ℕ} (hj : j < rows.length) : Q (k + j) (rowAt rows j) := by
  induction rows generalizing k j with
  | nil => exact absurd hj (Nat.not_lt_zero j)
  | cons r rs ih =>
    cases j with
    | zero => exact h.1
    | succ j =>
      have h' := ih h.2 (Nat.lt_of_succ_lt_succ hj)
      rwa [rowAt_cons_succ, show k + (j + 1) = k + 1 + j by omega]

theorem time_zero_eq (k : ℕ) : time 0 k = (k : ℝ) / 64 := by
  simp only [time, PiecewiseTube.node]
  ring

/-- The coordinates of a point of the trial tube of a slab are within `op · trial / 2⁸⁰` of the
reference polynomials. -/
theorem coords_of_trial {lim : Limits} {s : PositionFrameSlabs.State} {r : Step} {a t : ℝ}
    {x : Plane}
    (geo : geometry lim s r = true) (ht : t ∈ Icc a (a + 1 / 64))
    (hx : ‖(moving s r a t).symm (x - reference a r t)‖ ≤ r.trial / (2 : ℝ) ^ 80) (j : Fin 2) :
    |x j - QPoly.eval (polynomial r j) (coord a t)| ≤ (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80) := by
  obtain ⟨_, _, _, _, _, op0, _⟩ := geometry_sound geo
  have physical : ‖x - reference a r t‖ ≤ (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80) := by
    have h := ((moving s r a t).toContinuousLinearMap.le_opNorm
      ((moving s r a t).symm (x - reference a r t))).trans
      (mul_le_mul (frame_op_norm geo (abs_coord_le ht)) hx (norm_nonneg _) op0)
    simpa using h
  exact (PiLp.norm_apply_le (x - reference a r t) j).trans physical

variable {g s b c m : ℚ} {s₀ : PositionFrameSlabs.State} {rows : List Step}

/-- **The outer tube.** If every slab of the chain has the polynomial inequalities on its trial
tube, they hold at every point of the outer tube. -/
theorem fine_of_outer (geo : Geo s₀ rows) (h : SlabsOn (SlabQ g s b c m) 0 rows) {t : ℝ}
    {x : Plane} (hx : x ∈ outer s₀ 0 rows t) :
    Fine g s b c m (x 0 - dkR0) (x 1) (Real.cos (2 * t)) (Real.sin (2 * t)) := by
  obtain ⟨k, hk, ht, hg⟩ := hx
  rw [time_succ] at ht
  have Q := h.at hk
  rw [Nat.zero_add] at Q
  have e := coords_of_trial (geo.at hk) ht hg
  rw [time_zero_eq] at e ht
  exact Q t ht x e

/-- A point of the two-sided tube lies in the outer tube, or is the mirror image of a point of
the outer tube at the opposite angle. -/
theorem double_cases {W : ℝ → Set Plane} {t : ℝ} {x : Plane}
    (hx : x ∈ FlowLabel.doubleW flipIso 0 W t) : x ∈ W t ∨ ∃ y ∈ W (-t), flipIso y = x := by
  rcases lt_trichotomy 0 t with h | h | h
  · left
    rwa [FlowLabel.doubleW_of_lt h] at hx
  · subst h
    rw [FlowLabel.doubleW_self] at hx
    rcases hx with hx | ⟨y, hy, e⟩
    · exact Or.inl hx
    · exact Or.inr ⟨y, by simpa using hy, e⟩
  · right
    rw [FlowLabel.doubleW_of_gt h] at hx
    obtain ⟨y, hy, e⟩ := hx
    exact ⟨y, by simpa using hy, e⟩

/-- **The two-sided tube.** The polynomial inequalities hold on the outer tube and on its
mirror image at negative angles. -/
theorem fine_of_double (geo : Geo s₀ rows) (h : SlabsOn (SlabQ g s b c m) 0 rows) {t : ℝ}
    {x : Plane} (hx : x ∈ FlowLabel.doubleW flipIso 0 (outer s₀ 0 rows) t) :
    Fine g s b c m (x 0 - dkR0) (x 1) (Real.cos (2 * t)) (Real.sin (2 * t)) := by
  rcases double_cases hx with h1 | ⟨y, hy, rfl⟩
  · exact fine_of_outer geo h h1
  · have f := (fine_of_outer geo h hy).reflect
    simpa only [mul_neg, Real.cos_neg, Real.sin_neg, neg_neg, flipIso_apply,
      DommaschkJacobianReflection.flip_zero, DommaschkJacobianReflection.flip_one] using f

/-- **Field bounds on the two-sided tube**: the gradient of the field strength is at most `g`,
the field strength at least `s`, the planar speed of the field-line equation at most `m`, and
`PolyBounds b c m` holds, at every angle and every point of the two-sided tube, if the radius is
positive on the outer tube. -/
theorem field_of_double (geo : Geo s₀ rows) (h : SlabsOn (SlabQ g s b c m) 0 rows) (hb : 0 < b)
    (hs : 0 ≤ s) (hg : 0 ≤ g) (hm : 0 ≤ m)
    (pos : ∀ (t : ℝ) (x : Plane), x ∈ outer s₀ 0 rows t → 0 < x 0) {t : ℝ} {x : Plane}
    (hx : x ∈ FlowLabel.doubleW flipIso 0 (outer s₀ 0 rows) t) :
    ‖Kinetic.GCLittlejohn.gradAbsB B (cylPoint (x 0) t (x 1))‖ ≤ (g : ℝ) ∧
      (s : ℝ) ≤ ‖B (cylPoint (x 0) t (x 1))‖ ∧ ‖euclideanFlow 0 1 t x‖ ≤ (m : ℝ) ∧
      PolyBounds b c m (x 0) t (x 1) := by
  have hR : 0 < x 0 := by
    rcases double_cases hx with h1 | ⟨y, hy, rfl⟩
    · exact pos t x h1
    · simpa using pos (-t) y hy
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  obtain ⟨gr, st, pb⟩ := (fine_of_double geo h hx).field hR hb' (by exact_mod_cast hs)
    (by exact_mod_cast hg)
  exact ⟨gr, st, pb.speed hR hb' (by exact_mod_cast hm), pb⟩

end PlasmaLean.Design.DommaschkTubeField
