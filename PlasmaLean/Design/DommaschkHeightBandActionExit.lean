/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOuterFaceFlight
public import PlasmaLean.Design.DommaschkActionFlightFloor

/-! # First radial exits measured at varying birth heights on the two completed faces -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkHeightBandActionExit
open Set Theory.KAM Certificates.PositionFrameSlabs DommaschkRadialFamilyContinuity
open DommaschkNativeWellAction DommaschkMirrorLaunch DommaschkFirstMirrorLaunchSign
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkOuterFaceFlight (limit Side)

abbrev heights := Icc (level - 1 / 500000) level
abbrev margin : ℝ := 249 / 250000
abbrev inner : ℝ := 47 / 100
abbrev outer : ℝ := 239 / 500

/-- The observer uses a true physical field through this specific birth and the first
well about its phase. The reference solutions will place both contacts in the shared window. -/
def Observation (uC zC uA zA : FA) (u φ h J : ℝ) : Prop :=
  ∃ (y : ℝ → Plane) (l r : ℝ), y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
    Enclosed y (-limit) limit ∧ LaunchWell (field y) φ h l r ∧
    action (field y) (density y) l r h = J

structure Bounds (uC zC uA zA : FA) (φ h : ℝ) : Prop where
  inner_exists : ∃ J, Observation uC zC uA zA inner φ h J
  outer_exists : ∃ J, Observation uC zC uA zA outer φ h J
  inner_upper : ∀ J, Observation uC zC uA zA inner φ h J → J ≤ DommaschkActionArchiveMass.mass
  outer_lower : ∀ J, Observation uC zC uA zA outer φ h J →
    target + 19 / 10000 - 452 * (level-h) < J

private theorem identified {uC zC uA zA : FA} {u φ h a b J : ℝ} {x : ℝ → Plane}
    (time : φ ∈ Icc (-limit) limit) (source : x φ = coordinates.symm (birth uC zC uA zA u φ))
    (path : Enclosed x (-limit) limit) (well : LaunchWell (field x) 0 h a b)
    (inside : φ ∈ Ioo a b) (sub : Icc a b ⊆ Icc (-limit) limit)
    (obs : Observation uC zC uA zA u φ h J) : J = action (field x) (density x) a b h := by
  obtain ⟨z,l,r,born,ez,w,value⟩ := obs
  obtain ⟨other,mass⟩ := transfer_well path ez time (source.trans born.symm) well sub
  have about : LaunchWell (field z) φ h a b :=
    ⟨inside.1,inside.2,other.left_hit,other.right_hit,other.accessible⟩
  obtain ⟨hl,hr⟩ := w.unique about
  rw [← value,hl,hr,← mass]

/-- The certified pilot and outer time bounds suffice for every height in the top band.
The reference paths may be distinct from those used by an observer at either face. -/
theorem of_endpoints {uC zC uA zA : FA} {φ : ℝ} (small : |φ| ≤ 1 / 2 ^ 19)
    {x y : ℝ → Plane} (bornI : x φ = coordinates.symm (birth uC zC uA zA inner φ))
    (bornO : y φ = coordinates.symm (birth uC zC uA zA outer φ))
    (ex : Enclosed x (-limit) limit) (ey : Enclosed y (-limit) limit)
    (pilot : DommaschkActionFlightFloor.TimeBounds φ x)
    (p : Side (field y)) (m : Side (fun t => field y (-t)))
    (response : DommaschkOuterFaceFlight.Result uC zC uA zA φ) {h : ℝ} (hh : h ∈ heights) :
    Bounds uC zC uA zA φ h := by
  have time : φ ∈ Icc (-limit) limit := by
    obtain ⟨l,r⟩ := abs_le.mp small
    constructor <;> unfold DommaschkOuterFaceFlight.limit <;> linarith
  have band : h ∈ DommaschkOuterFaceFlight.H := by
    obtain ⟨lo,hi⟩ := hh
    constructor <;> norm_num [level,height] at lo hi ⊢ <;> linarith
  obtain ⟨a,ha,b,hb,birthI,wI,cap,_⟩ := pilot h band
  have scopeI : Icc a b ⊆ Icc (-limit) limit := Icc_subset_Icc
    (by unfold DommaschkOuterFaceFlight.limit; linarith [ha.1])
    (by unfold DommaschkOuterFaceFlight.limit; linarith [hb.2])
  have cart : action (field x) (density x) a b h ≤ DommaschkActionArchiveMass.mass := by
    refine le_trans (le_of_eq ?_) cap
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (wI.left_lt.trans wI.lt_right).le] at ht
    have ht' := scopeI ht
    have box := ex.region t ht'
    have eq := DommaschkPhysicalActionPanel.arcDensity_of_ode (ex.ode t ht')
      ((by norm_num : (0:ℝ)<7/8).trans_le box.1.1)
      ((by norm_num : (0:ℝ)<1/64).trans (DommaschkSignedTraceDenominator.regular t box.1 box.2))
    exact congrArg (fun w => w * Real.sqrt (2*(h-field x t))) eq
  let j : DommaschkOuterFaceFlight.H := ⟨h,band⟩
  have wO := DommaschkOuterFaceFlight.well p m j (φ := 0) (by norm_num)
  have about := DommaschkOuterFaceFlight.well p m j small
  have birthO : φ ∈ Ioo (-m.time j) (p.time j) := ⟨about.left_lt,about.lt_right⟩
  have scopeO : Icc (-m.time j) (p.time j) ⊆ Icc (-limit) limit :=
    Icc_subset_Icc (neg_le_neg (m.interior_time j).2.le) (p.interior_time j).2.le
  obtain ⟨z,bz,ez,all⟩ := response
  obtain ⟨l,r,wr,eq,_,slope⟩ := all j
  have orig : Observation uC zC uA zA outer φ h (DommaschkOuterFaceFlight.mass z h) :=
    ⟨z,l,r,bz,ez,wr,eq.symm⟩
  have trueMass := identified time bornO ey wO birthO scopeO orig
  have near : level - 1/100000 ≤ (j:ℝ) := by
    change level - 1/100000 ≤ h
    linarith [hh.1]
  have lower := (slope near).2
  change target+19/10000-452*(level-h) < DommaschkOuterFaceFlight.mass z h at lower
  rw [trueMass] at lower
  refine ⟨⟨_,x,a,b,bornI,ex,⟨birthI.1,birthI.2,wI.left_hit,wI.right_hit,wI.accessible⟩,rfl⟩,
    ⟨_,orig⟩,?_,?_⟩
  · intro J measure
    rw [identified time bornI ex wI birthI scopeI measure]
    exact cart
  · intro J measure
    rw [identified time bornO ey wO birthO scopeO measure]
    exact lower

def Observes (uC zC uA zA : FA) (u φ h J : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, u s ∈ Icc inner outer) → (u t = inner ∨ u t = outer) →
    |φ t| ≤ 1 / 2 ^ 19 ∧ h t ∈ heights ∧ Observation uC zC uA zA (u t) (φ t) (h t) (J t)

theorem stays_inside {uC zC uA zA : FA} {u φ h J : ℝ → ℝ} {T d : ℝ}
    (faces : ∀ θ, |θ| ≤ 1 / 2 ^ 19 → ∀ k ∈ heights, Bounds uC zC uA zA θ k)
    (observe : Observes uC zC uA zA u φ h J T) (cu : ContinuousOn u (Icc 0 T))
    (birth : u 0 ∈ Ioo inner outer) (budget : |J 0 - target| + d ≤ margin)
    (drift : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, u s ∈ Icc inner outer) → |J t - J 0| ≤ d) :
    ∀ t ∈ Icc 0 T, u t ∈ Ioo inner outer := by
  intro t ht
  by_contra outside
  obtain ⟨s,hs,hit,prior⟩ := ActionFaceBarrier.first_hit_of_departure cu birth ht outside
  obtain ⟨angle,hh,obs⟩ := observe s hs prior hit
  have bounds := faces _ angle _ hh
  have close : |J s-target| ≤ margin := calc
    _ ≤ |J s-J 0|+|J 0-target| := abs_sub_le _ _ _
    _ ≤ d+|J 0-target| := add_le_add_left (drift s hs prior) _
    _ ≤ _ := (add_comm d _).le.trans budget
  obtain ⟨low,high⟩ := abs_le.mp close
  rcases hit with left | right
  · rw [left] at obs
    have value := bounds.inner_upper _ obs
    have floor : DommaschkActionArchiveMass.mass < target-margin := by
      norm_num [DommaschkActionArchiveMass.mass,target,margin]
    linarith only [low,value,floor]
  · rw [right] at obs
    have value := bounds.outer_lower _ obs
    have range := hh.1
    unfold margin at high
    linarith only [high,value,range]

theorem stays_inside_of_correction {uC zC uA zA : FA} {u φ h J g k : ℝ → ℝ} {T ε G K : ℝ}
    (faces : ∀ θ, |θ| ≤ 1 / 2 ^ 19 → ∀ v ∈ heights, Bounds uC zC uA zA θ v)
    (observe : Observes uC zC uA zA u φ h J T) (cu : ContinuousOn u (Icc 0 T))
    (birth : u 0 ∈ Ioo inner outer) (hK : 0 ≤ K)
    (budget : |J 0 - target| + (2 * |ε| * G + T * ε ^ 2 * K) ≤ margin)
    (correction : ∀ t ∈ Icc 0 T, u t ∈ Icc inner outer → |g t| ≤ G)
    (residual : ∀ t ∈ Icc 0 T, u t ∈ Icc inner outer → |k t| ≤ K)
    (derivative : ∀ t ∈ Icc 0 T, u t ∈ Icc inner outer →
      HasDerivAt (fun s => J s + ε * g s) (ε ^ 2 * k t) t) :
    ∀ t ∈ Icc 0 T, u t ∈ Ioo inner outer := by
  apply stays_inside faces observe cu birth budget
  intro t ht prior
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have bound := AveragedConfinement.displacement_le ht.1
    (fun s hs => (derivative s (sub hs) (prior s hs)).hasDerivWithinAt)
    (fun s hs => residual s (sub hs) (prior s hs))
    (correction 0 ⟨le_rfl,ht.1.trans ht.2⟩ (Ioo_subset_Icc_self birth))
    (correction t ht (prior t (right_mem_Icc.mpr ht.1)))
  exact bound.trans (by gcongr; exact ht.2)

/-- A sector's two independently grounded endpoint observations suffice for every path
which is measured at each possible first radial exit. -/
def Guard (uC zC uA zA : FA) : Prop := ∀ (u φ h J : ℝ → ℝ) (T d : ℝ),
  Observes uC zC uA zA u φ h J T → ContinuousOn u (Icc 0 T) → u 0 ∈ Ioo inner outer →
  |J 0 - target| + d ≤ margin →
  (∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, u s ∈ Icc inner outer) → |J t - J 0| ≤ d) →
  ∀ t ∈ Icc 0 T, u t ∈ Ioo inner outer

theorem guard {uC zC uA zA : FA}
    (faces : ∀ θ, |θ| ≤ 1 / 2 ^ 19 → ∀ v ∈ heights, Bounds uC zC uA zA θ v) : Guard uC zC uA zA :=
  fun _ _ _ _ _ _ => stays_inside faces

end PlasmaLean.Design.DommaschkHeightBandActionExit
