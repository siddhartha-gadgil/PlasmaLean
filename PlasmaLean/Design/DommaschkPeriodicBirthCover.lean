/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPeriodicBirthFourier
public import PlasmaLean.Certificates.TrajectoryHarmonicPacket
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.ToIntervalMod

/-! # Periodic covering argument for field strength at the original birth point -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPeriodicBirthCover

open Set Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open DommaschkMirrorLaunch DommaschkFirstMirrorLaunchSign DommaschkPeriodicBirthFourier
open Certificates.TrajectoryTaylorModel

def linearModel (q0 q1 q2 q3 e : ℚ) (m1 m2 m3 : Model) : Model :=
  addModel (addModel (addModel (addModel (exactPoly [q0]) (mulModel (exactPoly [q1]) m1))
    (mulModel (exactPoly [q2]) m2)) (mulModel (exactPoly [q3]) m3)) ⟨[0], e⟩

theorem linear_mem {q0 q1 q2 q3 e : ℚ} {m1 m2 m3 dst : Model} {s x y1 y2 y3 : ℝ}
    (hs : |s| ≤ 1) (h1 : m1.Mem s y1) (h2 : m2.Mem s y2) (h3 : m3.Mem s y3)
    (hx : |x - ((q0 : ℝ) + q1*y1 + q2*y2 + q3*y3)| ≤ (e : ℝ))
    (fit : (linearModel q0 q1 q2 q3 e m1 m2 m3).radius +
      magnitude (difference (linearModel q0 q1 q2 q3 e m1 m2 m3).poly dst.poly) ≤ dst.radius) :
    dst.Mem s x := by
  have const (q : ℚ) : (exactPoly [q]).Mem s (q : ℝ) := by
    simp [exactPoly, Model.Mem, Certificates.QPoly.eval]
  let y := (q0 : ℝ) + q1*y1 + q2*y2 + q3*y3
  have he : (⟨[0],e⟩ : Model).Mem s (x-y) := by
    simpa [Model.Mem, Certificates.QPoly.eval, y] using hx
  have h := mem_add (mem_add (mem_add (mem_add (const q0) (mem_mul hs (const q1) h1))
    (mem_mul hs (const q2) h2)) (mem_mul hs (const q3) h3)) he
  change (linearModel q0 q1 q2 q3 e m1 m2 m3).Mem s (y + (x-y)) at h
  rw [show y + (x-y) = x by ring] at h
  exact enclose hs h fit

/-- The argument passed to the field can be any real representative of the same phase. -/
def Sector (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ R z φ : ℝ, |R-low false t| ≤ error false → |z-low true t| ≤ error true →
    Real.cos (2*φ) = Real.cos (2*t) → Real.sin (2*φ) = Real.sin (2*t) →
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖ < height false

theorem sector_join {a b c : ℝ} (left : Sector a b) (right : Sector b c) : Sector a c := by
  intro t ht
  by_cases h : t ≤ b
  · exact left t ⟨ht.1,h⟩
  · exact right t ⟨(not_le.mp h).le,ht.2⟩

private theorem representatives (φ : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) (202/64), (∀ (z : Bool) (j : ℤ),
      wave z (2*j*φ) = wave z (2*j*t)) := by
  let t := toIcoMod Real.pi_pos 0 φ
  let n := toIcoDiv Real.pi_pos 0 φ
  have ht := toIcoMod_mem_Ico' Real.pi_pos φ
  have hφ : t + (n : ℝ)*Real.pi = φ := by
    simpa only [zsmul_eq_mul] using toIcoMod_add_toIcoDiv_zsmul Real.pi_pos 0 φ
  refine ⟨t,⟨ht.1,by linarith [ht.2, Real.pi_lt_d2]⟩,?_⟩
  intro z j
  rw [show 2*(j : ℝ)*φ = 2*j*t + ((j*n : ℤ) : ℝ)*(2*Real.pi) by
    rw [← hφ, Int.cast_mul]; ring]
  cases z <;> first | exact Real.cos_add_int_mul_two_pi _ _ | exact Real.sin_add_int_mul_two_pi _ _

/-- A finite cover of one field period suffices also when the true KAM witness is
given only through strip norm closeness at each original azimuth. -/
theorem at_original (verified : Sector 0 (202/64)) {uC zC uA zA : FA}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA
      DommaschkKamA.u₀A DommaschkKamA.z₀A (1 / 10 ^ 12))
    {u : ℝ} (hu : u ∈ Icc (11 / 25 : ℝ) (27 / 50)) (φ : ℝ) :
    let b := birth uC zC uA zA u φ
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint (b 0) φ (b 1))‖ < height false := by
  obtain ⟨t,ht,hw⟩ := representatives φ
  have eq (z : Bool) (j : ℤ) : wave z (2*j*φ) = wave z (2*j*t) := hw z j
  have c1 (z : Bool) : wave z (2*φ) = wave z (2*t) := by simpa using eq z 1
  have c2 (z : Bool) : wave z (4*φ) = wave z (4*t) := by convert eq z 2 using 2 <;> norm_num
  have c3 (z : Bool) : wave z (6*φ) = wave z (6*t) := by convert eq z 3 using 2 <;> norm_num
  have same (z : Bool) : low z φ = low z t := by rw [low_eq,low_eq,c1,c2,c3]
  obtain ⟨hr,hz⟩ := birth_error hc ha hu φ
  rw [same] at hr hz
  exact verified t ht _ _ φ hr hz (c1 false) (c1 true)

def CommonBirths : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC)
      DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA)
      DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (u φ : ℝ), u ∈ Icc (11 / 25 : ℝ) (27 / 50) →
      let b := birth uC zC uA zA u φ
      ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint (b 0) φ (b 1))‖ < height false

set_option maxRecDepth 8192 in
theorem from_period (verified : Sector 0 (202/64)) : CommonBirths := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),?_⟩
  intro u φ hu
  exact at_original verified (uC := uC) (zC := zC) (uA := uA) (zA := zA)
    (by simpa using cC) (by simpa using cA) hu φ

end PlasmaLean.Design.DommaschkPeriodicBirthCover
