/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFirstContactHeightBudget
public import PlasmaLean.Design.DommaschkToroidalFieldBounds
public import PlasmaLean.Design.DommaschkEndpointTraceFamily
public import PlasmaLean.Design.DommaschkSignedBirthApproach
public import PlasmaLean.Certificates.PositionFrameObservationPrefix
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! # Regular first-mirror heights on a physical QA2R field line at any section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
open Set MeasureTheory Fields Contract DommaschkMirrorLaunch DommaschkMirrorTubeCrossing
open Certificates.PositionFrameSlabs Kinetic.FirstMirror DommaschkFirstMirrorLaunchSign
open DommaschkSignedTraceDomain
set_option maxRecDepth 12000

/-- Elapsed azimuth on either outward clock of a common signed field line. -/
def clock (back : Bool) (t : ℝ) : ℝ := if back then -t else t

/-- Actual Cartesian QA2R field evaluated at the physical azimuth of a cylindrical solution. -/
def vector (phase : ℝ) (y : ℝ → Plane) (back : Bool) (t : ℝ) : Space :=
  DommaschkQA2R.field DommaschkQA2R.candidate
    (cylPoint (y (clock back t) 0) (phase + clock back t) (y (clock back t) 1))

def profile (phase : ℝ) (y : ℝ → Plane) (back : Bool) (t : ℝ) : ℝ :=
  strength (phase + clock back t) (y (clock back t))

theorem vector_differentiableOn {phase T a b : ℝ} {y : ℝ → Plane} (back : Bool)
    (ode : ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow phase 1 t (y t))
      (Icc (-T) T) t) (ha : 0 ≤ a) (ab : a ≤ b) (time : b ≤ T)
    (radial : ∀ t ∈ Icc a b, 0 < y (clock back t) 0) :
    DifferentiableOn ℝ (vector phase y back) (Icc a b) := by
  have clockDiff : Differentiable ℝ (clock back) := by
    cases back
    · exact differentiable_id
    · exact differentiable_id.neg
  have maps : MapsTo (clock back) (Icc a b) (Icc (-T) T) := by
    intro t ht
    cases back <;> simp only [clock,Bool.false_eq_true,↓reduceIte,mem_Icc] <;>
      constructor <;> linarith [ht.1,ht.2]
  have dy : DifferentiableOn ℝ y (Icc (-T) T) := fun t ht => (ode t ht).differentiableWithinAt
  have yc : DifferentiableOn ℝ (fun t => y (clock back t)) (Icc a b) :=
    dy.comp clockDiff.differentiableOn maps
  intro t ht
  have coord (i : Fin 2) := (differentiableWithinAt_piLp 2).mp (yc t ht) i
  have angle := (differentiable_const (c := phase)).add clockDiff
  have point : DifferentiableWithinAt ℝ
      (fun u => cylPoint (y (clock back u) 0) (phase + clock back u) (y (clock back u) 1))
      (Icc a b) t := by
    apply (differentiableWithinAt_piLp 2).2
    intro i
    fin_cases i
    · exact (coord 0).mul (angle t).cos.differentiableWithinAt
    · exact (coord 0).mul (angle t).sin.differentiableWithinAt
    · exact coord 1
  have onDomain := DommaschkQA2R.poloidalLoop_mem_domain
    (R := fun _ _ => y (clock back t) 0) (z := fun _ _ => y (clock back t) 1)
    (θ := 0) (φ₀ := phase + clock back t) (radial t ht)
  have vac := DommaschkQA2R.field_vacuum DommaschkQA2R.candidate
  have field := vac.contDiffOn.contDiffAt (vac.isOpen.mem_nhds onDomain)
  exact (field.differentiableAt (by norm_num)).comp_differentiableWithinAt t point

/-- A common signed path has first-contact maps on both outward clocks. Almost every height
has two simple first mirrors, and a specified measure of heights has two slopes above 1 / 1250. -/
def Good (phase : ℝ) (y : ℝ → Plane) (a b c d : ℝ) : Prop :=
  ∃ p : Family (profile phase y false) a b (height false) (height true),
    ∃ q : Family (profile phase y true) c d (height false) (height true),
      (∀ᵐ H : ℝ, ∀ h : Icc (height false : ℝ) (height true), (h : ℝ) = H →
        0 < deriv (profile phase y false) (p.time h) ∧
        0 < deriv (profile phase y true) (q.time h)) ∧
      ENNReal.ofReal (667367655761 / 2500000000000000) ≤
        volume {H : ℝ | ∃ h : Icc (height false : ℝ) (height true), (h : ℝ) = H ∧
          1 / 1250 < deriv (profile phase y false) (p.time h) ∧
          1 / 1250 < deriv (profile phase y true) (q.time h)}

theorem on_signed {phase T a b c d : ℝ} {y : ℝ → Plane}
    (ode : ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow phase 1 t (y t))
      (Icc (-T) T) t)
    (ha : 0 ≤ a) (hab : a < b) (ht : b ≤ T) (hc : 0 ≤ c) (hcd : c < d) (ht' : d ≤ T)
    (short : b - a ≤ 10 / 64) (short' : d - c ≤ 10 / 64)
    (forwardBox : ∀ t ∈ Icc a b, Region (y t))
    (backBox : ∀ t ∈ Icc c d, Region (y (-t)))
    (early : ∀ t ∈ Icc 0 a, profile phase y false t < height false)
    (early' : ∀ t ∈ Icc 0 c, profile phase y true t < height false)
    (cap : (height true : ℝ) < profile phase y false b)
    (cap' : (height true : ℝ) < profile phase y true d) : Good phase y a b c d := by
  have data (back : Bool) {l r : ℝ} (hl : 0 ≤ l) (lr : l ≤ r) (room : r ≤ T)
      (box : ∀ t ∈ Icc l r, Region (y (clock back t))) :
      ContinuousOn (profile phase y back) (Icc l r) ∧
      ∀ t ∈ Ioo l r, DifferentiableAt ℝ (profile phase y back) t := by
    have v := vector_differentiableOn back ode hl lr room
      (fun t ht => (by norm_num : (0 : ℝ) < 7 / 8).trans_le (box t ht).1.1)
    refine ⟨v.continuousOn.norm,?_⟩
    intro t ht
    have pos := DommaschkToroidalFieldBounds.strength_lower (phase + clock back t)
      (box t (Ioo_subset_Icc_self ht))
    have nz : vector phase y back t ≠ 0 :=
      norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 7 / 8).trans pos)
    exact ((v t (Ioo_subset_Icc_self ht)).differentiableAt (Icc_mem_nhds ht.1 ht.2)).norm ℝ nz
  obtain ⟨cf,df⟩ := data false ha hab.le ht forwardBox
  obtain ⟨cg,dg⟩ := data true hc hcd.le ht' backBox
  obtain ⟨p⟩ := exists_family ha hab early cf cap
  obtain ⟨q⟩ := exists_family hc hcd early' cg cap'
  exact ⟨p,q,ae_two_sided p q ha hc (fun t h _ => df t h) (fun t h _ => dg t h),
    DommaschkFirstContactHeightBudget.good_height_measure p q ha hc short short' df dg⟩

open DommaschkEndpointTraceFamily DommaschkEndpointSignedTrace

/-- Closed physical inputs on one clock. The bracket starts at k / 64 and ends at the
right endpoint of the row with index j. The initial clearance and high cap may have
different numerical certificates, with no derivative or slope hypothesis. -/
structure Side (phase : ℝ) (entry : State) (back : Bool) (k j : ℕ) (rows : List Step) : Prop where
  positive : 0 < k
  before : k ≤ j
  reaches : j < rows.length
  width : j + 1 ≤ k + 10
  packed_prefix : (rows.take (j + 1)).all packed = true
  early : OnTubes (fun t x => strength (phase + clock back t) x < height false)
    entry 0 (rows.take k)
  high : ∀ (prev : State) (x : Plane),
    x ∈ (physicalSlab prev rows[j] (j / 64)).tube (((j : ℝ) + 1) / 64) →
      (height true : ℝ) < strength (phase + clock back (((j : ℝ) + 1) / 64)) x

theorem Side.inputs {phase : ℝ} {entry : State} {back : Bool} {k j : ℕ} {rs : List Step}
    {y : ℝ → Plane} (h : Side phase entry back k j rs)
    (inside : ∀ v ∈ physicalSlabs entry 0 rs, ∀ t ∈ Icc v.start v.stop,
      y (clock back t) ∈ v.tube t) :
    (∀ t ∈ Icc 0 (((j : ℝ) + 1) / 64), Region (y (clock back t))) ∧
    (∀ t ∈ Icc 0 ((k : ℝ) / 64), profile phase y back t < height false) ∧
    (height true : ℝ) < profile phase y back (((j : ℝ) + 1) / 64) := by
  have boxes := tubes (List.all_eq_true.mp h.packed_prefix) entry 0
  have box := boxes.on_initial (y := fun t => y (clock back t)) (Nat.succ_pos j) h.reaches inside
  have first := h.early.on_initial (y := fun t => y (clock back t)) h.positive
    (h.before.trans h.reaches.le) inside
  simp only [zero_add,Nat.cast_succ] at box first
  obtain ⟨prev,mem⟩ := DommaschkSignedObservable.slab_at entry 0 h.reaches
  rw [zero_add] at mem
  refine ⟨box, first, h.high prev _ (inside _ mem _ ?_)⟩
  change (j : ℝ) / 64 ≤ (j+1:ℝ) / 64 ∧ (j+1:ℝ) / 64 ≤ j/64+1 / 64
  constructor <;> linarith

/-- Reversing the approach clock identifies the original torus interpolation on the very
same signed field line. The absolute azimuth is phase plus elapsed signed time. -/
theorem original_position {phase T φ σ : ℝ} {a : ℝ → DommaschkBounceField.State} {y : ℝ → Plane}
    (wide : 1 / 64 ≤ T) (small : |φ - phase| ≤ 1 / 64) (unit : |σ| = 1)
    (arrives : φ + σ * |φ - phase| = phase) (start : y 0 = coordinates.symm (a |φ - phase|))
    (approach : ∀ t ∈ Icc 0 |φ - phase|, HasDerivWithinAt a
      (DommaschkBounceField.physicalFlow φ σ t (a t)) (Icc 0 |φ - phase|) t)
    (ode : ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow phase 1 t (y t))
      (Icc (-T) T) t)
    (box : ∀ t ∈ Icc (-(1 / 64)) (1 / 64), Region (y t)) :
    y (φ - phase) = coordinates.symm (a 0) := by
  let κ := fun t : ℝ => φ - phase + σ * t
  have inWindow : MapsTo κ (Icc 0 |φ - phase|) (Icc (-(1 / 64)) (1 / 64)) := by
    intro t ht
    apply abs_le.mp
    have eq : κ t = σ * (t - |φ - phase|) := by
      dsimp [κ]
      linarith only [arrives,mul_sub σ t |φ - phase|]
    rw [eq,abs_mul,unit,one_mul,abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  have inside : MapsTo κ (Icc 0 |φ - phase|) (Icc (-T) T) :=
    fun t ht => Icc_subset_Icc (neg_le_neg wide) wide (inWindow ht)
  have clockEq (t : ℝ) : phase + κ t = φ + σ * t := by dsimp [κ]; ring
  have agree : EqOn a (fun t => coordinates (y (κ t))) (Icc 0 |φ - phase|) := by
    apply Fields.ode_eqOn_of_terminal approach
    · intro t ht
      have dy := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
        (κ t) (ode (κ t) (inside ht))
      have der : HasDerivWithinAt (fun u => coordinates (y u))
          (DommaschkBounceField.physicalFlow phase 1 (κ t) (coordinates (y (κ t)))) (Icc (-T) T)
          (κ t) := dy.congr_deriv (coordinates.apply_symm_apply _)
      have dκ : HasDerivAt κ σ t := by
        simpa only [κ,id_eq,mul_one] using ((hasDerivAt_id t).const_mul σ).const_add (φ - phase)
      apply (der.scomp t dκ.hasDerivWithinAt inside).congr_deriv
      ext i
      fin_cases i <;> simp [DommaschkBounceField.physicalFlow,clockEq]
    · intro t ht
      have reg := box _ (inWindow ht)
      have d := DommaschkSignedTraceDenominator.regular (phase + κ t) reg.1 reg.2
      rw [clockEq] at d
      have rr : 0 < y (κ t) 0 := (by norm_num : (0 : ℝ) < 7 / 8).trans_le reg.1.1
      have den := ((by norm_num : (0 : ℝ) < 1 / 64).trans d).ne'
      exact DommaschkSignedBirthApproach.physical_smooth φ σ _ rr den
    · have atEnd : κ |φ - phase| = 0 := by dsimp [κ]; linarith
      simp only [atEnd,start,coordinates.apply_symm_apply]
  apply coordinates.injective
  simpa only [κ,mul_zero,add_zero,coordinates.apply_symm_apply] using
    (agree (show 0 ∈ Icc 0 |φ - phase| from ⟨le_rfl,abs_nonneg _⟩)).symm

/-- The approach from the actual launch and the full signed path, exits, tube enclosures,
first-contact families and area bound are all supplied by one trajectory. -/
def FromLaunch (e : MirrorEndpoint) (c : Checkpoint) (k j l i : ℕ)
    (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) : Prop :=
  let phase := azimuth e.opposite
  let δ := |φ - phase|
  let T : ℝ := c.length / 64
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * δ = phase ∧ a 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 δ, HasDerivWithinAt a (DommaschkBounceField.physicalFlow φ s t (a t))
      (Icc 0 δ) t) ∧ y 0 = coordinates.symm (a δ) ∧
    y (φ - phase) = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
    y (-T) ∈ stateSet c.backwardExit ∧
    y T ∈ stateSet c.forwardExit ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow phase 1 t (y t))
      (Icc (-T) T) t) ∧
    (∀ v ∈ physicalSlabs e.start 0 c.forwardRows, ∀ t ∈ Icc v.start v.stop, y t ∈ v.tube t) ∧
    (∀ v ∈ physicalSlabs e.start 0 c.backwardRows, ∀ t ∈ Icc v.start v.stop, y (-t) ∈ v.tube t) ∧
    Good phase y (k / 64) (((j : ℝ) + 1) / 64) (l / 64) (((i : ℝ) + 1) / 64)

theorem from_passage {e : MirrorEndpoint} {c : Checkpoint} {k j l i : ℕ}
    {uC zC uA zA : Theory.KAM.FA} {φ : ℝ} (path : c.Passage e uC zC uA zA φ)
    (fr : Side (azimuth e.opposite) e.start false k j c.forwardRows)
    (br : Side (azimuth e.opposite) e.start true l i c.backwardRows)
    (lf : c.forwardRows.length = c.length) (lb : c.backwardRows.length = c.length)
    (admitted : |φ - azimuth e.opposite| ≤ 1 / 64) :
    FromLaunch e c k j l i uC zC uA zA φ := by
  obtain ⟨s,a,unit,atPhase,born,approach,y,at0,left,right,ode,f,b⟩ := path
  obtain ⟨fbox,fearly,fcap⟩ := fr.inputs (y := y) f
  obtain ⟨bbox,bearly,bcap⟩ := br.inputs (y := y) b
  have jf : (j : ℝ) + 1 ≤ c.length := by exact_mod_cast (lf ▸ fr.reaches : j < c.length)
  have ib : (i : ℝ) + 1 ≤ c.length := by exact_mod_cast (lb ▸ br.reaches : i < c.length)
  have kf : (k : ℝ) ≤ j := by exact_mod_cast fr.before
  have lg : (l : ℝ) ≤ i := by exact_mod_cast br.before
  have wf : (j : ℝ) + 1 ≤ k + 10 := by exact_mod_cast fr.width
  have wb : (i : ℝ) + 1 ≤ l + 10 := by exact_mod_cast br.width
  have near (t : ℝ) (ht : t ∈ Icc (-(1 / 64)) (1 / 64)) : Region (y t) := by
    rcases le_total 0 t with pos | neg
    · exact fbox t ⟨pos,by linarith [ht.2,Nat.cast_nonneg (α := ℝ) j]⟩
    · simpa only [clock,↓reduceIte,neg_neg] using bbox (-t) ⟨neg_nonneg.mpr neg,
        by linarith [ht.1,Nat.cast_nonneg (α := ℝ) i]⟩
  have actual := original_position (by linarith [Nat.cast_nonneg (α := ℝ) j])
    admitted unit atPhase at0 approach ode near
  rw [born] at actual
  exact ⟨s,a,y,unit,atPhase,born,approach,at0,actual,left,right,ode,f,b,
    on_signed ode (by positivity) (by linarith) (by linarith) (by positivity)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (fun t ht => fbox t ⟨(by positivity : (0 : ℝ) ≤ k / 64).trans ht.1,ht.2⟩)
      (fun t ht => bbox t ⟨(by positivity : (0 : ℝ) ≤ l / 64).trans ht.1,ht.2⟩)
      fearly bearly fcap bcap⟩

end PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
