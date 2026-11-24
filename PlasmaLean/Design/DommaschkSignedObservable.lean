/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBackwardPairedPrefix
public import PlasmaLean.Design.DommaschkMirrorTubeCrossing
public import PlasmaLean.Certificates.PositionFrameObservables

/-! # Observables on the same signed field line as a Q-16 birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedObservable

open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkKamC KamNewton Set
open DommaschkBackwardPairedPrefix DommaschkMirrorTubeCrossing
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Theory.KAM WEll1Z2

/-- The same signed trajectory encounters a level on both sides of a specified
elapsed-angle bracket. -/
def HitsBoth (a b h : ℝ) (y : ℝ → Plane) : Prop :=
  (∃ t ∈ Ioo a b, strength t (y t) = h) ∧
  (∃ t ∈ Ioo a b, strength (-t) (y (-t)) = h)

/-- Earliest encounter with one height on each side of the same section. -/
def FirstBoth (a b h : ℝ) (y : ℝ → Plane) : Prop :=
  (∃ c ∈ Ioo a b, strength c (y c) = h ∧ ∀ t ∈ Ico 0 c, strength t (y t) < h) ∧
  (∃ c ∈ Ioo a b, strength (-c) (y (-c)) = h ∧ ∀ t ∈ Ico 0 c, strength (-t) (y (-t)) < h)

/-- The fixed-index enclosure at its physical clock, including the predecessor
state inherited at its entrance. -/
theorem slab_at {i : ℕ} {rows : List Step} (s : State) (a : ℝ) (hi : i < rows.length) :
    ∃ prev, physicalSlab prev rows[i] (a + i / 64) ∈ physicalSlabs s a rows := by
  induction rows generalizing i s a with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => exact ⟨s, by simp [physicalSlabs]⟩
    | succ j =>
      obtain ⟨prev, mem⟩ := ih (next r) (a + 1 / 64) (Nat.lt_of_succ_lt_succ hi)
      refine ⟨prev, List.mem_cons_of_mem _ ?_⟩
      rw [Nat.cast_succ, show a + ((j : ℝ) + 1) / 64 = (a + 1 / 64) + j / 64 by ring]
      exact mem

/-- The path solves the signed ODE and stays in both sets of authenticated tubes. -/
structure Path (n : ℕ) (fexit bexit : State) (frows brows : List Step) (x : Plane)
    (y : ℝ → Plane) : Prop where
  starts : y 0 = x
  backward_exit : y (-(n : ℝ) / 64) ∈ stateSet bexit
  forward_exit : y (n / 64) ∈ stateSet fexit
  ode : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), HasDerivWithinAt y
    (DommaschkJacobian.euclideanFlow 0 1 t (y t)) (Icc (-(n : ℝ) / 64) (n / 64)) t
  forward : ∀ u ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 frows,
    ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t
  backward : ∀ u ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 brows,
    ∀ t ∈ Icc u.start u.stop, y (-t) ∈ u.tube t

/-- Tube and continuity evidence for a row at elapsed angle i/64 in either direction. -/
theorem Path.at_row {n i : ℕ} {fexit bexit : State} {frows brows : List Step} {x : Plane}
    {y : ℝ → Plane} (path : Path n fexit bexit frows brows x y) (within : i < n)
    (back : Bool) (hi : i < (if back then brows else frows).length) :
    let z := fun t => y (if back then -t else t)
    let a := (i : ℝ) / 64
    let b := ((i : ℝ) + 1) / 64
    ContinuousOn z (Icc a b) ∧ ∃ prev, ∀ t ∈ Icc a b,
      z t ∈ (physicalSlab prev (if back then brows else frows)[i] a).tube t := by
  have size : (i : ℝ) + 1 ≤ n := by exact_mod_cast within
  have zero_i : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have within_signed {t : ℝ} (ht : t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64)) :
      t ∈ Icc (-(n : ℝ) / 64) (n / 64) ∧ -t ∈ Icc (-(n : ℝ) / 64) (n / 64) := by
    obtain ⟨hl, hr⟩ := ht
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have cont : ContinuousOn y (Icc (-(n : ℝ) / 64) (n / 64)) :=
    fun t ht => (path.ode t ht).continuousWithinAt
  have hstop : (i : ℝ) / 64 + 1 / 64 = ((i : ℝ) + 1) / 64 := by ring
  cases back
  · obtain ⟨prev, mem⟩ := slab_at (MirrorEndpoint.start .q0r470) 0 hi
    simp only [Bool.false_eq_true, ite_false, zero_add] at mem ⊢
    refine ⟨cont.mono (fun _ ht => (within_signed ht).1),
      prev, fun t ht => path.forward _ mem t ?_⟩
    change t ∈ Icc ((i : ℝ) / 64) (i / 64 + 1 / 64)
    rwa [hstop]
  · obtain ⟨prev, mem⟩ := slab_at (MirrorEndpoint.start .q0r470) 0 hi
    simp only [ite_true, zero_add] at mem ⊢
    refine ⟨cont.comp continuous_neg.continuousOn (fun _ ht => (within_signed ht).2),
      prev, fun t ht => path.backward _ mem t ?_⟩
    change t ∈ Icc ((i : ℝ) / 64) (i / 64 + 1 / 64)
    rwa [hstop]

/-- Signs on a nonempty initial part of each outward archive give a strict
bound throughout the signed interval on the same physical path. -/
theorem Path.below_on {n k : ℕ} {fexit bexit : State} {fr br : List Step} {x : Plane}
    {y : ℝ → Plane} {h : ℝ} (path : Path n fexit bexit fr br x y) (hk : 0 < k)
    (hf : (fr.take k).length = k) (hb : (br.take k).length = k)
    (f : OnTubes (fun t p => strength t p < h) (MirrorEndpoint.start .q0r470) 0 (fr.take k))
    (b : OnTubes (fun t p => strength (-t) p < h) (MirrorEndpoint.start .q0r470) 0 (br.take k)) :
    ∀ t ∈ Icc (-(k : ℝ) / 64) (k / 64), strength t (y t) < h := by
  have nonempty {rs : List Step} (len : rs.length = k) : rs ≠ [] := by
    rintro rfl
    simp only [List.length_nil] at len
    omega
  have forward := f.on_nonempty_prefix (post := fr.drop k) (y := y) (nonempty hf)
    (by simpa only [List.take_append_drop] using path.forward)
  have backward := b.on_nonempty_prefix (post := br.drop k) (y := fun t => y (-t)) (nonempty hb)
    (by simpa only [List.take_append_drop] using path.backward)
  simp only [hf, hb, zero_add] at forward backward
  intro t ht
  rcases le_total 0 t with ht' | ht'
  · exact forward t ⟨ht', ht.2⟩
  · simpa only [neg_neg] using backward (-t) ⟨neg_nonneg.mpr ht', by linarith [ht.1]⟩

/-- Q-16 launch geometry, the approach to the section and a property of the
same physical trajectory through that section. -/
def BirthWith (P : Plane → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 →
      ∃ (sign : ℝ) (approach : ℝ → DommaschkBounceField.State),
        |sign| = 1 ∧ φ + sign * |φ| = 0 ∧ approach 0 = birth uC zC uA zA (47 / 100) φ ∧
        (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach
          (DommaschkBounceField.physicalFlow φ sign t (approach t)) (Icc 0 |φ|) t) ∧
        P (coordinates.symm (approach |φ|))

/-- Attach an observable assertion to the actual path supplied by the signed
birth theorem without choosing different field lines for different assertions. -/
theorem birth_with {n : ℕ} {fexit bexit : State} {frows brows : List Step}
    (births : BirthPassage n fexit bexit frows brows) {P : (ℝ → Plane) → Prop}
    (prove : ∀ x y, Path n fexit bexit frows brows x y → P y) :
    BirthWith (fun x => ∃ y, Path n fexit bexit frows brows x y ∧ P y) := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,each⟩ := births
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hφ => ?_⟩
  obtain ⟨sign,approach,hs,ha,hb,ode,y,ys,yb,yf,yd,ft,bt⟩ := each φ hφ
  have path : Path n fexit bexit frows brows (coordinates.symm (approach |φ|)) y :=
    ⟨ys,by simpa only [neg_div] using yb,yf,by simpa only [neg_div] using yd,ft,bt⟩
  exact ⟨sign,approach,hs,ha,hb,ode,y,path,prove _ _ path⟩

end PlasmaLean.Design.DommaschkSignedObservable
