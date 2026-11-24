/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkEndpointMirrorBranch
public import PlasmaLean.Design.DommaschkSecondaryActionCore
public import PlasmaLean.Design.DommaschkNativeWellAction
public import PlasmaLean.Certificates.MirrorActionBlockBounds

/-! # Transporting chronological rectangles to a single signed physical trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkLowerActionPath
open Certificates.PositionFrameSlabs DommaschkEndpointMirrorBranch DommaschkEndpointSignedTrace
open DommaschkPhysicalActionPanel DommaschkMirrorTubeCrossing DommaschkJacobian Set

def density (y : ℝ → Plane) (t : ℝ) := arcDensity (y t 0) t (y t 1)
def field (y : ℝ → Plane) (t : ℝ) := strength t (y t)

/-- Membership in the true position tube of one recorded row on the indicated clock. -/
def InRow (back : Bool) (y : ℝ → Plane) (i : ℕ) (r : Step) : Prop :=
  ∃ prev, ∀ t ∈ Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64),
    y (if back then -t else t) ∈ (physicalSlab prev r (i / 64)).tube t

/-- One path supplies the indexed pointwise input to a whole family of chronological cells. -/
def Tracks (fr br : List Step) (k : ℕ) (y : ℝ → Plane) : Prop :=
  (∀ i, i < k → (hi : i < fr.length) → InRow false y i fr[i]) ∧
  (∀ i, i < k → (hi : i < br.length) → InRow true y i br[i])

theorem Tracks.mono {fr br : List Step} {k n : ℕ} {y : ℝ → Plane}
    (h : Tracks fr br n y) (hk : k ≤ n) : Tracks fr br k y :=
  ⟨fun i hi => h.1 i (hi.trans_le hk),fun i hi => h.2 i (hi.trans_le hk)⟩

theorem tracks_of_take {entry : State} {fr br : List Step} {k : ℕ} {T : ℝ} {y : ℝ → Plane}
    (f : Outward entry (fr.take k) 1 T y)
    (b : Outward entry (br.take k) (-1) T (fun t => y (-t))) : Tracks fr br k y := by
  constructor
  · intro i hik hi
    obtain ⟨prev,mem⟩ := f.at_row (i := i) (by simpa using lt_min hik hi)
    exact ⟨prev, by simpa only [Bool.false_eq_true, ↓reduceIte,List.getElem_take] using mem⟩
  · intro i hik hi
    obtain ⟨prev,mem⟩ := b.at_row (i := i) (by simpa using lt_min hik hi)
    exact ⟨prev, by simpa only [↓reduceIte,List.getElem_take] using mem⟩

/-- Keep the signed ODE, in particular the derivative at the common section, on the
same function that realizes both forward and backward row enclosures. -/
structure Signed (entry : State) (fr br : List Step) (T : ℝ) (y : ℝ → Plane) : Prop where
  ode : ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-T) T) t
  forward : Outward entry fr 1 T y
  backward : Outward entry br (-1) T (fun t => y (-t))

theorem from_joined {entry : State} {fr br : List Step} {x : Plane} {fe be : Set Plane} {T : ℝ}
    (h : Joined 0 T x fe be (physicalSlabs entry 0 fr) (physicalSlabs entry 0 br)) :
    ∃ y, y 0 = x ∧ Signed entry fr br T y := by
  obtain ⟨y,hy,_,_,ode,f,b⟩ := h
  refine ⟨y,hy,ode,⟨?_,f⟩,⟨?_,b⟩⟩
  · intro t ht
    have m : t ∈ Ioo (-T) T := ⟨by linarith [ht.1,ht.2], ht.2⟩
    exact (ode t (Ioo_subset_Icc_self m)).hasDerivAt (Icc_mem_nhds m.1 m.2)
  · intro t ht
    have m : -t ∈ Ioo (-T) T := ⟨by linarith [ht.2],by linarith [ht.1,ht.2]⟩
    have d := (ode (-t) (Ioo_subset_Icc_self m)).hasDerivAt (Icc_mem_nhds m.1 m.2)
    have eq : -euclideanFlow 0 1 (-t) (y (-t)) = euclideanFlow 0 (-1) t (y (-t)) := by
      ext i
      fin_cases i <;> simp [euclideanFlow,DommaschkBounceField.physicalFlow]
    simpa only [Function.comp_def,neg_one_smul,eq] using d.scomp t (hasDerivAt_neg t)

/-- Positivity of the toroidal field on the common spatial box identifies the
quadrature weight with the norm of the Cartesian derivative, including at the launch. -/
theorem Signed.inputs {entry : State} {fr br : List Step} {T a b : ℝ} {y : ℝ → Plane}
    (path : Signed entry fr br T y) (inside : Icc a b ⊆ Ioo (-T) T)
    (valid : ∀ t ∈ Icc a b, DommaschkSignedTraceDomain.Region (y t)) :
    ContinuousOn (field y) (Icc a b) ∧ ContinuousOn (density y) (Icc a b) ∧
      ∀ t ∈ Icc a b, DommaschkNativeWellAction.density y t = density y t := by
  have d (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt y (euclideanFlow 0 1 t (y t)) t :=
    (path.ode t (Ioo_subset_Icc_self (inside ht))).hasDerivAt
      (Icc_mem_nhds (inside ht).1 (inside ht).2)
  have cont : ContinuousOn y (Icc a b) := fun t ht => (d t ht).continuousAt.continuousWithinAt
  refine ⟨?_,DommaschkSignedTraceDensity.continuousOn_density_region cont valid,?_⟩
  · change ContinuousOn (fun t => strength t (y t)) (Icc a b)
    simpa only [one_mul] using
      continuousOn_strength cont 1
        (fun t ht => by linarith [(valid t ht).1.1])
  · intro t ht
    have h := valid t ht
    have pos := DommaschkSignedTraceDenominator.regular t h.1 h.2
    exact arcDensity_of_ode (d t ht) (by linarith [h.1.1]) (by linarith)

/-- A signed angular window inherits the checked spatial box of its two outward lists. -/
theorem regions {entry : State} {fr br : List Step} {n : ℕ} {T : ℝ} {y : ℝ → Plane}
    (f : Outward entry fr 1 T y) (b : Outward entry br (-1) T (fun t => y (-t)))
    (positive : 0 < n) (lf : fr.length = n) (lb : br.length = n)
    (rf : fr.all DommaschkSignedTraceDomain.packed = true)
    (rb : br.all DommaschkSignedTraceDomain.packed = true) :
    ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), DommaschkSignedTraceDomain.Region (y t) := by
  have side {rs : List Step} {z : ℝ → Plane} {sign : ℝ} (p : Outward entry rs sign T z)
      (len : rs.length = n) (ok : rs.all DommaschkSignedTraceDomain.packed = true) :
      ∀ t ∈ Icc 0 (n / 64 : ℝ), DommaschkSignedTraceDomain.Region (z t) := by
    have full := DommaschkSignedTraceDomain.tubes (List.all_eq_true.mp ok) entry 0
    have ne : rs ≠ [] := by rintro rfl; simp at len; omega
    have res := full.on_nonempty_prefix (post := []) (y := z) ne
      (by simpa only [List.append_nil] using p.contained)
    simpa only [len,zero_add] using res
  intro t ht
  rcases le_total 0 t with h | h
  · exact side f lf rf t ⟨h,ht.2⟩
  · simpa only [neg_neg] using side b lb rb (-t) ⟨by linarith,by linarith [ht.1]⟩

open DommaschkMirrorLaunch DommaschkBounceField DommaschkKamC KamNewton
open Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- The original physical approach and its section point belong to the same observed solution. -/
def AtBirth (e : MirrorEndpoint) (uC zC uA zA : FA) (φ : ℝ) (P : (ℝ → Plane) → Prop) : Prop :=
  let duration := |φ - azimuth e.opposite|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = azimuth e.opposite ∧ a 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = Certificates.PositionFrameSlabs.coordinates.symm (a duration) ∧ P y

theorem observe {e : MirrorEndpoint} (phase : azimuth e.opposite = 0)
    {uC zC uA zA : FA} {φ T : ℝ} {fe be : Set Plane} {fr br : List Step} {P : (ℝ → Plane) → Prop}
    (passage : FromBirth e uC zC uA zA φ T fe be
      (physicalSlabs e.start 0 fr) (physicalSlabs e.start 0 br))
    (property : ∀ y, Signed e.start fr br T y → P y) : AtBirth e uC zC uA zA φ P := by
  obtain ⟨s,a,hs,hφ,src,d,j⟩ := passage
  rw [phase] at j
  obtain ⟨y,hy,path⟩ := from_joined j
  refine ⟨s,a,y,hs,hφ,src,d,?_,property y path⟩
  simpa only [phase] using hy

end PlasmaLean.Design.DommaschkLowerActionPath
