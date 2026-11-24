/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionComparison
public import PlasmaLean.Theory.Geometry.LocalLevelGraphs

/-!
# Radial tile summary certificates for mirror actions

One outward trace provides bounds for the squared strength and arclength density
and their radial derivatives. Square comparisons verify the dyadic root
witnesses and give an action slope on the accessible unit core. Adding the two
directions and gluing consecutive tiles preserves a uniform lower secant.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.RadialTile

open Set
open PlasmaLean.Kinetic.MirrorHeightAction

/-- Directed interval data for a single outward trace. The last four entries are
the lower and upper square-root witnesses, integrand bound and exported secant. -/
structure Half where
  bLow : ℝ
  bHigh : ℝ
  aLow : ℝ
  aHigh : ℝ
  dbLow : ℝ
  dbHigh : ℝ
  daLow : ℝ
  daHigh : ℝ
  coreUpper : ℝ
  capLower : ℝ
  outward : ℝ
  bMin : ℝ
  bMax : ℝ
  amplitude : ℝ
  slope : ℝ
  steps : ℕ

/-- Exact checks on the outward-rounded extrema and the subsidiary witnesses.
The final comparison in each rounding pair records rounding to one grid unit. -/
structure Half.Valid (D : Half) (low high unit step limit : ℝ) : Prop where
  strength : 0 < D.bLow ∧ D.bLow ≤ D.bHigh
  density : 0 < D.aLow ∧ D.aLow ≤ D.aHigh
  dStrength : D.dbLow ≤ D.dbHigh ∧ D.dbHigh < 0
  dDensity : 0 < D.daLow ∧ D.daLow ≤ D.daHigh
  core : D.coreUpper < low ^ 2
  cap : high ^ 2 < D.capLower
  orientation : 0 < D.outward
  rootLow : 0 ≤ D.bMin ∧ D.bMin^2 ≤ D.bLow ∧ D.bLow < (D.bMin + unit)^2
  rootHigh : 0 < D.bMax ∧ D.bHigh ≤ D.bMax^2 ∧ (D.bMax - unit)^2 < D.bHigh
  rootAmp : 0 < D.amplitude ∧ 2 * D.aHigh * (high - D.bMin) ≤ D.amplitude ^ 2 ∧
    (D.amplitude - unit)^2 < 2 * D.aHigh * (high - D.bMin)
  gridSlope : 0 < D.slope ∧
    (2 * D.amplitude * D.bMax) * D.slope ≤ D.aLow * (-D.dbHigh) ∧
    D.aLow * (-D.dbHigh) < (2 * D.amplitude * D.bMax) * (D.slope + unit)
  extent : ((D.steps : ℝ) - 1) * step < limit ∧ limit ≤ (D.steps : ℝ) * step

/-- Paired signed traces on one radial subinterval. -/
structure Piece where
  left : ℝ
  right : ℝ
  backward : Half
  forward : Half

/-- Each constructor checks one tile and requires its right endpoint to be
the left endpoint of the remaining cover. -/
inductive Cover (low high unit step limit m : ℝ) : ℝ → ℝ → List Piece → Prop
  | nil (r) : Cover low high unit step limit m r r []
  | cons (p : Piece) {b : ℝ} {ps : List Piece}
      (ordered : p.left < p.right) (back : p.backward.Valid low high unit step limit)
      (forward : p.forward.Valid low high unit step limit)
      (slope : m ≤ p.backward.slope + p.forward.slope)
      (tail : Cover low high unit step limit m p.right b ps) :
      Cover low high unit step limit m p.left b (p :: ps)

/-- Each of these inequalities concerns the actual continuously parametrized
field line or its derivative. Establishing them is the trajectory checker's job. -/
structure Half.Encloses (D : Half) (B A : ℝ → ℝ → ℝ) (a b low high limit : ℝ) : Prop where
  bTime : ∀ r ∈ Icc a b, ContinuousOn (B r) (Icc 0 limit)
  bDiff : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 limit, DifferentiableAt ℝ (B r) t
  aTime : ∀ r ∈ Icc a b, ContinuousOn (A r) (Icc 0 limit)
  nonneg : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 limit, 0 ≤ B r t ∧ 0 ≤ A r t
  bRange : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 limit, (B r t)^2 ∈ Icc D.bLow D.bHigh
  aRange : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 limit, (A r t)^2 ∈ Icc D.aLow D.aHigh
  radialB : ∀ t ∈ Icc 0 limit, ∀ r ∈ Icc a b, ∃ z ∈ Icc D.dbLow D.dbHigh,
    HasDerivAt (fun s => (B s t)^2) z r
  radialA : ∀ t ∈ Icc 0 limit, ∀ r ∈ Icc a b, ∃ z ∈ Icc D.daLow D.daHigh,
    HasDerivAt (fun s => (A s t)^2) z r
  core : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 1, (B r t)^2 ≤ D.coreUpper
  cap : ∀ r ∈ Icc a b, D.capLower ≤ (B r limit)^2
  outward : ∀ r ∈ Icc a b, ∀ t ∈ Icc 0 limit, B r t ∈ Icc low high →
    D.outward ≤ deriv (fun s => (B r s)^2) t

/-- A verified lower derivative bound on a closed interval gives a finite secant. -/
private theorem square_secants {f : ℝ → ℝ} {a b l h u v : ℝ}
    (der : ∀ x ∈ Icc a b, ∃ z ∈ Icc l h, HasDerivAt f z x)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    l*(v-u) ≤ f v-f u ∧ f v-f u ≤ h*(v-u) := by
  have diff (s : ℝ) (hs : s ∈ Icc a b) : DifferentiableAt ℝ f s :=
    (der s hs).choose_spec.2.differentiableAt
  have cf : ContinuousOn f (Icc a b) := fun s hs => (diff s hs).continuousAt.continuousWithinAt
  have df : DifferentiableOn ℝ f (interior (Icc a b)) :=
    fun s hs => (diff s (interior_subset hs)).differentiableWithinAt
  have bd (s : ℝ) (hs : s ∈ interior (Icc a b)) : deriv f s ∈ Icc l h := by
    obtain ⟨z, hz, dz⟩ := der s (interior_subset hs)
    exact dz.deriv.symm ▸ hz
  exact ⟨(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv cf df (fun s hs => (bd s hs).1)
    u hu v hv huv, (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le cf df
      (fun s hs => (bd s hs).2) u hu v hv huv⟩

/-- The exported slope bounds the growth of the clipped action on one half
trace. It is derived from the field and density derivatives throughout the tile. -/
theorem Half.Valid.action_secant {D : Half} {B A : ℝ → ℝ → ℝ}
    {a b low high unit step limit h u v : ℝ} (C : D.Valid low high unit step limit)
    (E : D.Encloses B A a b low high limit) (hlow : 0 < low) (hh : h ∈ Icc low high)
    (ht : 1 ≤ limit) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
    D.slope*(v-u) ≤ action (B v) (A v) 0 limit h - action (B u) (A u) 0 limit h := by
  have du : 0 ≤ v-u := sub_nonneg.mpr huv
  have bv (r : ℝ) (hr : r ∈ Icc a b) (t : ℝ) (hit : t ∈ Icc 0 limit) :
      D.bMin ≤ B r t ∧ B r t ≤ D.bMax := by
    have range := E.bRange r hr t hit
    exact ⟨le_of_sq_le_sq (C.rootLow.2.1.trans range.1) (E.nonneg r hr t hit).1,
      le_of_sq_le_sq (range.2.trans C.rootHigh.2.1) C.rootHigh.1.le⟩
  have sec (t : ℝ) (hit : t ∈ Icc 0 limit) :
      (A u t)^2 ≤ (A v t)^2 ∧
      2*D.bMax*(B u t-B v t) ≥ (-D.dbHigh)*(v-u) ∧ B v t ≤ B u t := by
    have ha := (square_secants (E.radialA t hit) hu hv huv).1
    have hb := (square_secants (E.radialB t hit) hu hv huv).2
    have hd : D.dbHigh * (v - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg C.dStrength.2.le du
    have hB : B v t ≤ B u t := le_of_sq_le_sq (by linarith) (E.nonneg u hu t hit).1
    have prod := mul_le_mul_of_nonneg_right
      (show B u t + B v t ≤ 2*D.bMax by linarith [(bv u hu t hit).2, (bv v hv t hit).2])
      (sub_nonneg.mpr hB)
    exact ⟨by linarith [mul_nonneg C.dDensity.1.le du], by nlinarith only [hb, prod], hB⟩
  let k := 2*D.amplitude*D.slope*(v-u)
  have hk : 0 ≤ k := by dsimp [k]; positivity [C.rootAmp.1, C.gridSlope.1]
  have bound := action_gap_ge_of_core (h := h) (a := 0) (b := limit) (c := 0) (d := 1)
    le_rfl zero_le_one ht C.rootAmp.1 hk (E.bTime u hu) (E.bTime v hv) (E.aTime u hu)
    (E.aTime v hv) (fun t hit => (E.nonneg u hu t hit).2)
    (fun t hit => (E.nonneg v hv t hit).2) (fun t hit hB =>
      mul_le_mul (sec t hit).1 (sub_le_sub_left (sec t hit).2.2 h)
        (sub_nonneg.mpr hB.le) (sq_nonneg _)) (by
      intro t core
      have hit : t ∈ Icc 0 limit := ⟨core.1, core.2.trans ht⟩
      have allowed : B u t ≤ h := (le_of_sq_le_sq ((E.core u hu t core).trans C.core.le)
        hlow.le).trans hh.1
      have drop := (sec t hit).2.2
      have clipped := mul_le_mul_of_nonneg_right (sec t hit).1 (sub_nonneg.mpr allowed)
      have multiply := mul_le_mul_of_nonneg_right (E.aRange v hv t hit).1 (sub_nonneg.mpr drop)
      have key : 2*D.amplitude*D.slope*(v-u) ≤ 2*D.aLow*(B u t-B v t) := by
        apply le_of_mul_le_mul_right (a := D.bMax) _ C.rootHigh.1
        have h₁ := mul_le_mul_of_nonneg_right C.gridSlope.2.1 du
        have h₂ := mul_le_mul_of_nonneg_left (sec t hit).2.1 C.density.1.le
        nlinarith only [h₁, h₂]
      have highGap : h - B v t ≤ high - D.bMin :=
        sub_le_sub hh.2 (bv v hv t hit).1
      have upper := mul_le_mul (E.aRange v hv t hit).2 highGap
        (sub_nonneg.mpr (drop.trans allowed)) (C.density.1.le.trans C.density.2)
      exact ⟨by positivity [sub_nonneg.mpr allowed],
        by dsimp [k]; nlinarith only [key, clipped, multiply],
        by nlinarith only [upper, C.rootAmp.2.1]⟩)
  convert bound using 1
  dsimp [k]
  field_simp [C.rootAmp.1.ne']
  ring

/-- The same extrema establish a unique oriented outward crossing for each
height in the window. This prevents a second accessible pocket on the clipped trace. -/
theorem Half.Valid.crossing {D : Half} {B A : ℝ → ℝ → ℝ}
    {a b low high unit step limit h r : ℝ} (C : D.Valid low high unit step limit)
    (E : D.Encloses B A a b low high limit) (hlow : 0 < low) (hh : h ∈ Icc low high)
    (ht : 1 ≤ limit) (hr : r ∈ Icc a b) :
    ∃ s ∈ Ioo 0 limit, B r s = h ∧ 0 < deriv (B r) s ∧
      (∀ t ∈ Ico 0 s, B r t < h) ∧ (∀ t ∈ Ioc s limit, h < B r t) := by
  have pos := hlow.trans_le hh.1
  apply Kinetic.MirrorWell.upward_crossing (zero_lt_one.trans_le ht) (E.bTime r hr)
  · have bound := (E.core r hr 0 ⟨le_rfl, zero_le_one⟩).trans_lt C.core
    exact (lt_of_not_ge fun e => bound.not_ge (pow_le_pow_left₀ hlow.le e 2)).trans_le hh.1
  · have bound := C.cap.trans_le (E.cap r hr)
    have nn := (E.nonneg r hr limit ⟨zero_le_one.trans ht, le_rfl⟩).1
    exact hh.2.trans_lt (lt_of_not_ge fun e => bound.not_ge (pow_le_pow_left₀ nn e 2))
  · intro t hit eqn
    have slope := C.orientation.trans_le (E.outward r hr t hit (eqn ▸ hh))
    have chain := ((E.bDiff r hr t hit).hasDerivAt.pow 2).deriv
    simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at chain
    change 0 < deriv (B r ^ 2) t at slope
    rw [chain, eqn] at slope
    exact pos_of_mul_pos_right slope (by positivity)

/-- Uniform lower radial secant over a single closed launch interval. -/
def LowerSecant (J : ℝ → ℝ) (m a b : ℝ) : Prop :=
  ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → m * (v-u) ≤ J v-J u

/-- Secants add when neighbouring closed tiles share an endpoint. -/
theorem LowerSecant.join {J : ℝ → ℝ} {m a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (L : LowerSecant J m a b) (R : LowerSecant J m b c) : LowerSecant J m a c := by
  intro u hu v hv huv
  by_cases left : v ≤ b
  · exact L u ⟨hu.1, huv.trans left⟩ v ⟨hv.1, left⟩ huv
  by_cases right : b ≤ u
  · exact R u ⟨right, hu.2⟩ v ⟨right.trans huv, hv.2⟩ huv
  have ub := (lt_of_not_ge right).le
  have bv := (lt_of_not_ge left).le
  have l := L u ⟨hu.1, ub⟩ b ⟨hab, le_rfl⟩ ub
  have r := R b ⟨le_rfl, hbc⟩ v ⟨bv, hv.2⟩ bv
  linarith only [l,r]

/-- The two half actions use increasing outward coordinates on their respective arcs. -/
def twoSidedAction (Bn An Bp Ap : ℝ → ℝ → ℝ) (limit h u : ℝ) : ℝ :=
  action (Bn u) (An u) 0 limit h + action (Bp u) (Ap u) 0 limit h

/-- A zero crossing slope is rejected by the numerical certificate even when
the field and action values themselves may be well-defined. -/
theorem Half.not_valid_of_zero_outward (D : Half) (low high unit step limit : ℝ)
    (hz : D.outward = 0) : ¬ D.Valid low high unit step limit :=
  fun h => (ne_of_gt h.orientation) hz

/-- The unit integral on the backward half uses positive arclength. Reflection
recovers the signed trace coordinate, and the two half actions add to the
ordinary single-passage integral. -/
theorem twoSidedAction_eq {B A : ℝ → ℝ} {limit h : ℝ} (ht : 0 ≤ limit)
    (hB : ContinuousOn B (Icc (-limit) limit)) (hA : ContinuousOn A (Icc (-limit) limit)) :
    action (fun t => B (-t)) (fun t => A (-t)) 0 limit h + action B A 0 limit h =
      action B A (-limit) limit h := by
  let f := fun t => A t * Real.sqrt (2*(h-B t))
  have cf : ContinuousOn f (Icc (-limit) limit) :=
    hA.mul ((continuousOn_const.mul (continuousOn_const.sub hB)).sqrt)
  have zero : -limit ≤ 0 := neg_nonpos.mpr ht
  have full := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((cf.mono (Icc_subset_Icc_right ht)).intervalIntegrable_of_Icc zero)
    ((cf.mono (Icc_subset_Icc_left zero)).intervalIntegrable_of_Icc ht)
  unfold action
  have reflected := intervalIntegral.integral_comp_neg (a := 0) (b := limit) f
  simp only [neg_zero] at reflected
  exact (congrArg (· + _) reflected).trans full

/-- The physical half traces identify the first pair of mirrors and the fixed-window
action with the integral between them. The left root is reported in the signed
coordinate and its transversality is stated in the backward outward coordinate. -/
theorem mirrorPair_action {Dn Dp : Half} {B A : ℝ → ℝ → ℝ}
    {a b low high unit step limit h u : ℝ} (Cn : Dn.Valid low high unit step limit)
    (Cp : Dp.Valid low high unit step limit)
    (En : Dn.Encloses (fun r t => B r (-t)) (fun r t => A r (-t)) a b low high limit)
    (Ep : Dp.Encloses B A a b low high limit) (hlow : 0 < low) (hh : h ∈ Icc low high)
    (ht : 1 ≤ limit) (hu : u ∈ Icc a b) (hB : ContinuousOn (B u) (Icc (-limit) limit))
    (hA : ContinuousOn (A u) (Icc (-limit) limit)) :
    ∃ l ∈ Ioo (-limit) 0, ∃ r ∈ Ioo 0 limit, B u l = h ∧ B u r = h ∧
      0 < deriv (fun t => B u (-t)) (-l) ∧ 0 < deriv (B u) r ∧
      (∀ t ∈ Ioo l r, B u t < h) ∧
      twoSidedAction (fun p t => B p (-t)) (fun p t => A p (-t)) B A limit h u =
        action (B u) (A u) l r h := by
  obtain ⟨s, hs, es, ds, before, after⟩ := Cn.crossing En hlow hh ht hu
  obtain ⟨r, hr, er, dr, left, right⟩ := Cp.crossing Ep hlow hh ht hu
  refine ⟨-s, ⟨neg_lt_neg hs.2, neg_lt_zero.mpr hs.1⟩, r, hr, es, er, ?_, dr, ?_, ?_⟩
  · simpa only [neg_neg] using ds
  · intro t hit
    by_cases zero : 0 ≤ t
    · exact left t ⟨zero, hit.2⟩
    · simpa only [neg_neg] using before (-t) ⟨by linarith, by linarith [hit.1]⟩
  · unfold twoSidedAction
    rw [twoSidedAction_eq (zero_le_one.trans ht) hB hA]
    apply action_eq_between (neg_le_neg hs.2.le) (by linarith [hs.1, hr.1]) hr.2.le hB hA
    · intro t hit
      rcases hit.2.lt_or_eq with ht' | rfl
      · simpa only [neg_neg] using (after (-t) ⟨by linarith, by linarith [hit.1]⟩).le
      · exact es.ge
    · intro t hit
      rcases hit.1.lt_or_eq with ht' | rfl
      · exact (right t ⟨ht', hit.2⟩).le
      · exact er.ge

/-- Once a shorter endpoint lies above the energy, the rest of that half is
forbidden. This equates a quadrature on shorter, asymmetric arcs with the
same full-window action used by the radial secant. -/
theorem action_eq_short_of_caps {Dn Dp : Half} {B A : ℝ → ℝ → ℝ}
    {a b low high unit step limit h u L R : ℝ} (Cn : Dn.Valid low high unit step limit)
    (Cp : Dp.Valid low high unit step limit)
    (En : Dn.Encloses (fun r t => B r (-t)) (fun r t => A r (-t)) a b low high limit)
    (Ep : Dp.Encloses B A a b low high limit) (hlow : 0 < low) (hh : h ∈ Icc low high)
    (ht : 1 ≤ limit) (hu : u ∈ Icc a b) (hB : ContinuousOn (B u) (Icc (-limit) limit))
    (hA : ContinuousOn (A u) (Icc (-limit) limit)) (hL : L ∈ Icc 0 limit)
    (hR : R ∈ Icc 0 limit) (left : h ≤ B u (-L)) (right : h ≤ B u R) :
    twoSidedAction (fun p t => B p (-t)) (fun p t => A p (-t)) B A limit h u =
      action (B u) (A u) (-L) R h := by
  have tail {f : ℝ → ℝ} {s e : ℝ} (he : e ∈ Icc 0 limit)
      (hbefore : ∀ t ∈ Ico 0 s, f t < h) (hafter : ∀ t ∈ Ioc s limit, h < f t)
      (cap : h ≤ f e) : ∀ t ∈ Icc e limit, h ≤ f t := by
    have se : s ≤ e := le_of_not_gt fun below => (hbefore e ⟨he.1, below⟩).not_ge cap
    intro t hit
    rcases hit.1.lt_or_eq with strict | rfl
    · exact (hafter t ⟨se.trans_lt strict, hit.2⟩).le
    · exact cap
  obtain ⟨_, _, _, _, bn, an⟩ := Cn.crossing En hlow hh ht hu
  obtain ⟨_, _, _, _, bp, ap⟩ := Cp.crossing Ep hlow hh ht hu
  unfold twoSidedAction
  rw [twoSidedAction_eq (zero_le_one.trans ht) hB hA]
  apply action_eq_between (neg_le_neg hL.2) ((neg_nonpos.mpr hL.1).trans hR.1) hR.2 hB hA
  · intro t hit
    simpa only [neg_neg] using tail hL bn an left (-t) ⟨by linarith [hit.2], by linarith [hit.1]⟩
  · exact tail hR bp ap right

/-- Covers have ordered ends, including the empty zero-width cover. -/
theorem Cover.ordered {low high unit step limit m a b : ℝ} {ps : List Piece}
    (C : Cover low high unit step limit m a b ps) : a ≤ b := by
  induction C with
  | nil => exact le_rfl
  | cons _ h _ _ _ _ ih => exact h.le.trans ih

/-- The connected numerical cover turns spatial, derivative and core enclosures
on its actual traces into one secant bound on the complete radius bracket. -/
theorem Cover.action_secant {Bn An Bp Ap : ℝ → ℝ → ℝ} {low high unit step limit m a b h : ℝ}
    {ps : List Piece} (C : Cover low high unit step limit m a b ps) (hlow : 0 < low)
    (hh : h ∈ Icc low high) (ht : 1 ≤ limit)
    (trace : ∀ p ∈ ps, p.backward.Encloses Bn An p.left p.right low high limit ∧
      p.forward.Encloses Bp Ap p.left p.right low high limit) :
    LowerSecant (twoSidedAction Bn An Bp Ap limit h) m a b := by
  induction C with
  | nil =>
    intro u hu v hv _
    simp only [Icc_self, mem_singleton_iff] at hu hv
    simp [hu, hv]
  | cons p ord back forward slope tail ih =>
    apply LowerSecant.join ord.le tail.ordered _
      (ih fun x hx => trace x (List.mem_cons_of_mem _ hx))
    intro u hu v hv huv
    obtain ⟨eb, ef⟩ := trace p (List.mem_cons_self ..)
    have L := back.action_secant eb hlow hh ht hu hv huv
    have R := forward.action_secant ef hlow hh ht hu hv huv
    have hmul := mul_le_mul_of_nonneg_right slope (sub_nonneg.mpr huv)
    dsimp [twoSidedAction]
    linarith only [L,R,hmul]

/-- With independently enclosed endpoint actions and joint continuity, a tile
cover supplies the secant field of the local level-graph theorem. -/
theorem Cover.secantBracket {X : Type*} [TopologicalSpace X]
    {low high unit step limit m a b h j : ℝ}
    {ps : List Piece} (C : Cover low high unit step limit m a b ps) (hlow : 0 < low)
    (hh : h ∈ Icc low high) (ht : 1 ≤ limit) (hm : 0 < m)
    (Bn An Bp Ap : X → ℝ → ℝ → ℝ)
    (trace : ∀ x p, p ∈ ps → p.backward.Encloses (Bn x) (An x) p.left p.right low high limit ∧
      p.forward.Encloses (Bp x) (Ap x) p.left p.right low high limit)
    (J : X → ℝ → ℝ) (ident : ∀ x r, r ∈ Icc a b →
      J x r = twoSidedAction (Bn x) (An x) (Bp x) (Ap x) limit h r)
    (hc : ContinuousOn (fun p : X × ℝ => J p.1 p.2) (univ ×ˢ Icc a b))
    (left : ∀ x, J x a < j) (right : ∀ x, j < J x b) :
    LocalLevelGraphs.SecantBracket J a b j m := by
  refine ⟨C.ordered, hm, hc, left, right, ?_⟩
  intro x u hu v hv huv
  rw [ident x u hu, ident x v hv]
  exact (C.action_secant hlow hh ht (trace x)) u hu v hv huv

end PlasmaLean.Certificates.RadialTile
