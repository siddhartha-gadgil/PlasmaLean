/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import PlasmaLean.Design.DommaschkSignedTraceDomain
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
public import PlasmaLean.Theory.Kinetic.MirrorHeightBand

/-! # First mirror branches over the whole pilot height interval -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedMirrorBand

open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedMirrorSlope
open DommaschkSignedTraceDomain DommaschkMirrorTubeCrossing DommaschkJacobian
open Kinetic.MirrorHeightBand DommaschkFirstMirrorLaunchSign Set

def Rate (f : ℝ → ℝ) (k t : ℝ) : Prop :=
  ∃ v > k, HasDerivAt (fun u => (f u) ^ 2) v t

/-- At a point of a closed physical tube the derivative may be supplied by the longer
joined trajectory, including when that point is a numerical slab endpoint. -/
def SlabSlope (r : Step) (sign a b k : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ y : ℝ → Plane, ∀ prev : State, y t ∈ (physicalSlab prev r a).tube t →
    HasDerivAt y (euclideanFlow 0 sign t (y t)) t → Rate (fun u => strength (sign * u) (y u)) k t

def Rates (y : ℝ → Plane) (a b k : ℝ) : Prop :=
  ∀ t ∈ Icc a b,
    HasDerivAt y (euclideanFlow 0 1 t (y t)) t →
    HasDerivAt (fun u => y (-u)) (euclideanFlow 0 (-1) t (y (-t))) t →
    Rate (fun u => strength u (y u)) k t ∧ Rate (fun u => strength (-u) (y (-u))) k t

theorem attach {n i : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {k : ℝ} (path : Path n fs bs fr br x y) (reached : i < n)
    (hf : i < fr.length) (hb : i < br.length)
    (f : SlabSlope fr[i] 1 (i / 64) (((i : ℝ) + 1) / 64) k)
    (b : SlabSlope br[i] (-1) (i / 64) (((i : ℝ) + 1) / 64) k) :
    Rates y (i / 64) (((i : ℝ) + 1) / 64) k := by
  obtain ⟨_, pf, forward⟩ := path.at_row reached false hf
  obtain ⟨_, pb, backward⟩ := path.at_row reached true hb
  intro t ht df db
  exact ⟨by simpa only [one_mul] using f t ht y pf (forward t ht) df,
    by simpa only [neg_one_mul] using b t ht (fun u => y (-u)) pb (backward t ht) db⟩

theorem Rates.append {y : ℝ → Plane} {a b c k : ℝ} (left : Rates y a b k)
    (right : Rates y b c k) : Rates y a c k := by
  intro t ht
  rcases le_total t b with early | late
  · exact left t ⟨ht.1, early⟩
  · exact right t ⟨late, ht.2⟩

def Branches (y : ℝ → Plane) : Prop :=
  Nonempty (Branch (fun t => strength t (y t)) (316 / 64) (325 / 64)
    (height false) (height true) (1 / 400)) ∧
  Nonempty (Branch (fun t => strength (-t) (y (-t))) (316 / 64) (325 / 64)
    (height false) (height true) (1 / 400))

/-- Both inverse branches refer to the same physical field line at all heights. -/
theorem branches {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (lower : FirstBoth (316 / 64) (317 / 64) (height false) y)
    (upper : HitsBoth (324 / 64) (325 / 64) (height true) y)
    (rates : Rates y (316 / 64) (325 / 64) (1 / 400)) : Branches y := by
  let a : ℝ := 316 / 64
  let b : ℝ := 325 / 64
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have clocks := clock_odes path (a := a) (b := b) (by norm_num [a]) (by dsimp [b]; linarith)
  have contained (t : ℝ) (ht : t ∈ Icc a b) :
      t ∈ Icc (-(n : ℝ) / 64) (n / 64) ∧ -t ∈ Icc (-(n : ℝ) / 64) (n / 64) := by
    obtain ⟨lo, hi⟩ := ht
    dsimp [a,b] at lo hi
    constructor <;> constructor <;> linarith
  have fc : ContinuousOn (fun t => strength t (y t)) (Icc a b) := by
    have cy : ContinuousOn y (Icc a b) := fun t ht => (clocks.1 t ht).continuousWithinAt
    simpa only [one_mul] using continuousOn_strength cy 1
      (fun t ht => by linarith [(region t (contained t ht).1).1.1])
  have bc : ContinuousOn (fun t => strength (-t) (y (-t))) (Icc a b) := by
    have cy : ContinuousOn (fun t => y (-t)) (Icc a b) :=
      fun t ht => (clocks.2 t ht).continuousWithinAt
    simpa only [neg_one_mul] using continuousOn_strength cy (-1)
      (fun t ht => by linarith [(region (-t) (contained t ht).2).1.1])
  have growth (t : ℝ) (ht : t ∈ Ioo a b) :=
    rates t (Ioo_subset_Icc_self ht)
      ((clocks.1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      ((clocks.2 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  have each {f : ℝ → ℝ} (cont : ContinuousOn f (Icc a b)) (nonneg : ∀ t, 0 ≤ f t)
      (low : ∃ c ∈ Ioo a (317 / 64), f c = height false ∧ ∀ t ∈ Ico 0 c, f t < height false)
      (high : ∃ c ∈ Ioo (324 / 64) b, f c = height true)
      (slope : ∀ t ∈ Ioo a b, Rate f (1 / 400) t) :
      Nonempty (Branch f a b (height false) (height true) (1 / 400)) := by
    obtain ⟨u, hu, _, history⟩ := low
    obtain ⟨v, hv, atV⟩ := high
    apply exists_branch (by norm_num [a]) (by norm_num [a,b]) (by norm_num [height])
      (by norm_num) nonneg cont (fun t ht => history t ⟨ht.1, ht.2.trans_lt hu.1⟩) _ slope
    exact ⟨v, ⟨lt_trans (by norm_num [a] : a < 324 / 64) hv.1, hv.2⟩, atV⟩
  exact ⟨each fc (fun _ => norm_nonneg _) lower.1 upper.1 (fun t ht => (growth t ht).1),
    each bc (fun _ => norm_nonneg _) lower.2 upper.2 (fun t ht => (growth t ht).2)⟩

theorem Branches.first_transverse {y : ℝ → Plane} (hbranches : Branches y)
    {h : ℝ} (hh : h ∈ Icc (height false : ℝ) (height true)) :
    FirstTransverseBoth (316 / 64) (325 / 64) h (1 / 400) y := by
  obtain ⟨⟨f⟩, ⟨b⟩⟩ := hbranches
  let j : Icc (height false : ℝ) (height true) := ⟨h, hh⟩
  exact ⟨⟨f.time j, f.interior_time j, f.hit j, f.before j, f.unique_time j, f.transverse j⟩,
    ⟨b.time j, b.interior_time j, b.hit j, b.before j, b.unique_time j, b.transverse j⟩⟩

end PlasmaLean.Design.DommaschkSignedMirrorBand
