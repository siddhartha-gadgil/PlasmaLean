/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorLaunch
public import PlasmaLean.Design.DommaschkBounceLaunchStep
public import PlasmaLean.Design.DommaschkKamEmbedded

/-!
# A physical field-line collar on both mirror-launch sectors

The radii and heights in the initial condition come from the same embedded C/A
pair as Q-16. The launch phase ranges over an interval and the interpolation
coordinate ranges over the entire deep strip.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open DommaschkKamC KamNewton DommaschkBounceField Set
open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Fields.RectangularODEStep
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer

/-- The actual interpolated radius and height at birth. -/
def birth (uC zC uA zA : FA) (u φ : ℝ) : State :=
  ![blend u (RofC uC 0 φ) (RofC uA 0 φ), blend u (Zof zC 0 φ) (Zof zA 0 φ)]

/-- Both angular directions have a true field line up to 1/64 radian from the birth. -/
def Collar (uC zC uA zA : FA) : Prop :=
  ∀ (q : Bool) (u φ sign : ℝ), u ∈ Icc (11/25) (27/50) → |φ - azimuth q| ≤ 1/4096 →
    |sign| ≤ 1 → ∃ x : ℝ → State, x 0 = birth uC zC uA zA u φ ∧ ∀ t ∈ Icc 0 (1/64 : ℝ),
      HasDerivWithinAt x (physicalFlow φ sign t (x t)) (Icc 0 (1/64)) t ∧
      x t ∈ Icc (tubeLo q) (tubeHi q) ∧ ∃ v ∈ Icc (fun _ : Fin 2 => -(1/4:ℝ)) (fun _ => 1/4),
        x t = birth uC zC uA zA u φ + t • v

/-- Sharp Q-16 strip closeness suffices for the full-sector ODE collar. -/
theorem collar_of_close {uC zC uA zA : FA}
    (hc : Close (9/1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1/10^12))
    (ha : Close (9/1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A
      (1/10^12)) : Collar uC zC uA zA := by
  intro q u φ sign hu hφ hs
  obtain ⟨hr,hz⟩ := sector_box hc ha q hu hφ
  apply exists_launch_step q φ sign (1/64) hs (by norm_num) (by change |φ - azimuth q| + _ ≤ _; linarith)
  · cases q <;> change _ ∈ Icc _ _ at hr <;> change _ ≤ blend _ _ _ <;>
      norm_num only [Bool.false_eq_true, ite_false, ite_true] <;> linarith [hr.1]
  · cases q <;> change _ ∈ Icc _ _ at hr <;> change blend _ _ _ ≤ _ <;>
      norm_num only [Bool.false_eq_true, ite_false, ite_true] <;> linarith [hr.2]
  · change |blend _ _ _| ≤ _
    linarith

/-- An unconditional collar on a single pair of the nested field-line tori of Q-16. -/
theorem exists_nested_collar :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      Collar uC zC uA zA := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,_,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  exact ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,collar_of_close (by simpa using cC) (by simpa using cA)⟩

end PlasmaLean.Design.DommaschkMirrorLaunch
