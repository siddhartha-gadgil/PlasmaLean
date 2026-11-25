/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPeriodicBirthCover
public import PlasmaLean.Design.DommaschkMirrorTwoSided

/-! # Uniform two-sided ODE collar for the original QA2R birth annulus -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPeriodicBirthCollar
open Set Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open DommaschkMirrorLaunch DommaschkFirstMirrorLaunchSign DommaschkPeriodicBirthFourier
open DommaschkBounceField DommaschkKam

def duration : ℝ := 1/256
def speed : ℝ := 1/6
def clearance : ℝ := 1/1000
def cap : ℝ := (height false : ℝ) - clearance

open Certificates.TrajectoryTaylorModel

/-- Altering a physical input at fixed normalized birth phase only expands its error radius. -/
theorem perturbed {a b : Model} {x y s : ℝ} {e : ℚ} (hx : a.Mem s x)
    (hy : |y-x| ≤ (e : ℝ)) (hp : a.poly = b.poly) (he : a.radius+e ≤ b.radius) :
    b.Mem s y := by
  unfold Model.Mem at hx ⊢
  rw [hp] at hx
  have h : (a.radius : ℝ) + (e : ℝ) ≤ b.radius := by exact_mod_cast he
  linarith only [abs_sub_le y x (Certificates.QPoly.eval b.poly s),hy,hx,h]

def Bounds (R z ψ : ℝ) : Prop :=
  1/2 < R ∧ 0 < atPoint dD R ψ z ∧
  |atPoint dnR R ψ z / atPoint dD R ψ z| ≤ speed ∧
  |atPoint dnZ R ψ z / atPoint dD R ψ z| ≤ speed ∧
  ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R ψ z)‖ < cap

/-- A birth angle in this sector and every observation in the swept space-time tube. -/
def Sector (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ R z ψ : ℝ,
    |R-low false t| ≤ error false + duration*speed →
    |z-low true t| ≤ error true + duration*speed →
    |Real.cos (2*ψ)-Real.cos (2*t)| ≤ 2*duration →
    |Real.sin (2*ψ)-Real.sin (2*t)| ≤ 2*duration → Bounds R z ψ

theorem sector_join {a b c : ℝ} (l : Sector a b) (r : Sector b c) : Sector a c := by
  intro t ht
  by_cases h : t ≤ b
  · exact l t ⟨ht.1,h⟩
  · exact r t ⟨(not_le.mp h).le,ht.2⟩

private theorem representative (φ : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) (202/64), (∀ z, low z φ = low z t) ∧
      Real.cos (2*φ) = Real.cos (2*t) ∧ Real.sin (2*φ) = Real.sin (2*t) := by
  let t := toIcoMod Real.pi_pos 0 φ
  let n := toIcoDiv Real.pi_pos 0 φ
  have ht := toIcoMod_mem_Ico' Real.pi_pos φ
  have he : t + (n : ℝ)*Real.pi = φ := by
    simpa only [zsmul_eq_mul] using toIcoMod_add_toIcoDiv_zsmul Real.pi_pos 0 φ
  have hw (z : Bool) (j : ℤ) : wave z (2*j*φ) = wave z (2*j*t) := by
    rw [show 2*(j : ℝ)*φ = 2*j*t + ((j*n : ℤ) : ℝ)*(2*Real.pi) by
      rw [← he, Int.cast_mul]; ring]
    cases z <;> first | exact Real.cos_add_int_mul_two_pi .. | exact Real.sin_add_int_mul_two_pi ..
  have c1 (z : Bool) : wave z (2*φ) = wave z (2*t) := by simpa using hw z 1
  have c2 (z : Bool) : wave z (4*φ) = wave z (4*t) := by convert hw z 2 using 2 <;> norm_num
  have c3 (z : Bool) : wave z (6*φ) = wave z (6*t) := by convert hw z 3 using 2 <;> norm_num
  exact ⟨t,⟨ht.1,by linarith [ht.2,Real.pi_lt_d2]⟩,
    fun z => by rw [low_eq,low_eq,c1,c2,c3],c1 false,c1 true⟩

def Swept (x₀ x : State) : Prop := ∀ i, |x i-x₀ i| ≤ duration*speed

theorem bounds_at {x₀ x : State} {φ τ sign : ℝ} (sectors : Sector 0 (202/64))
    (hr : |x₀ 0-low false φ| ≤ error false) (hz : |x₀ 1-low true φ| ≤ error true)
    (hs : |sign| ≤ 1) (ht : τ ∈ Icc 0 duration) (swept : Swept x₀ x) :
    Bounds (x 0) (x 1) (φ+sign*τ) := by
  obtain ⟨t,ht',hl,hc,hsin⟩ := representative φ
  have angle : |2*(φ+sign*τ)-2*φ| ≤ 2*duration := by
    rw [show 2*(φ+sign*τ)-2*φ = 2*(sign*τ) by ring,abs_mul,abs_mul,abs_of_nonneg ht.1]
    have h := mul_le_mul_of_nonneg_right hs ht.1
    norm_num at h ⊢
    linarith [ht.2]
  apply sectors t ht'
  · rw [← hl]
    linarith only [abs_sub_le (x 0) (x₀ 0) (low false φ),swept 0,hr]
  · rw [← hl]
    linarith only [abs_sub_le (x 1) (x₀ 1) (low true φ),swept 1,hz]
  · rw [← hc]
    exact (Real.abs_cos_sub_cos_le _ _).trans angle
  · rw [← hsin]
    exact (Real.abs_sin_sub_sin_le _ _).trans angle

/-- A true QA2R solution on an outward clock from the original unevolved section point.
It stays below the lowered height and moves by at most the speed allowance times elapsed time. -/
theorem outward {x₀ : State} {φ sign : ℝ} (sectors : Sector 0 (202/64))
    (hr : |x₀ 0-low false φ| ≤ error false) (hz : |x₀ 1-low true φ| ≤ error true)
    (hs : |sign| ≤ 1) :
    ∃ x : ℝ → State, x 0 = x₀ ∧ ∀ t ∈ Icc 0 duration,
      HasDerivWithinAt x (physicalFlow φ sign t (x t)) (Icc 0 duration) t ∧
      Bounds (x t 0) (x t 1) (φ+sign*t) ∧ ∀ i, |x t i-x₀ i| ≤ t*speed := by
  let lo : State := fun i => x₀ i-duration*speed
  let hi : State := fun i => x₀ i+duration*speed
  let vlo : State := fun _ => -speed
  let vhi : State := fun _ => speed
  have hT : 0 ≤ duration := by norm_num [duration]
  have hV : 0 ≤ speed := by norm_num [speed]
  have hB (x : State) (hx : x ∈ Icc lo hi) : Swept x₀ x := by
    intro i
    have h₁ : x₀ i-duration*speed ≤ x i := hx.1 i
    have h₂ : x i ≤ x₀ i+duration*speed := hx.2 i
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hb {t : ℝ} (ht : t ∈ Icc 0 duration) {x} (hx : x ∈ Icc lo hi) :=
    bounds_at sectors hr hz hs ht (hB x hx)
  have hbox : lo ≤ hi := fun i => by dsimp [lo,hi]; linarith [mul_nonneg hT hV]
  have hlo : lo ∈ Icc lo hi := ⟨le_rfl,hbox⟩
  have hR := (hb (t := 0) ⟨le_rfl,hT⟩ hlo).1
  have absV (v : ℝ) (hv : |v| ≤ speed) : |sign*v| ≤ speed := by
    rw [abs_mul]
    simpa using mul_le_mul hs hv (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  obtain ⟨x, hx, hstep⟩ := exists_physical_step (phase := φ) (sign := sign)
    (vlo := vlo) (vhi := vhi) (x₀ := x₀) hT hbox (by linarith only [hR])
    (fun _ ht _ hx => (hb ht hx).2.1) (by
      intro t ht x hx
      obtain ⟨_,_,nr,nz,_⟩ := hb ht hx
      constructor <;> intro i <;> fin_cases i
      · exact (abs_le.mp (absV _ nr)).1
      · exact (abs_le.mp (absV _ nz)).1
      · exact (abs_le.mp (absV _ nr)).2
      · exact (abs_le.mp (absV _ nz)).2) (by
      intro t ht v hv
      apply Fields.RectangularODEStep.tube_of_endpoints _ _ _ ht hv
      · constructor <;> intro i <;> dsimp [lo,hi] <;> linarith [mul_nonneg hT hV]
      · intro i
        change x₀ i-duration*speed ≤ x₀ i+duration*(-speed)
        linarith
      · exact le_rfl)
  refine ⟨x,hx,fun t ht => ?_⟩
  obtain ⟨der,mem,v,hv,eqv⟩ := hstep t ht
  refine ⟨der,hb ht mem,fun i => ?_⟩
  rw [eqv]
  change |x₀ i+t*v i-x₀ i| ≤ t*speed
  rw [add_sub_cancel_left,abs_mul,abs_of_nonneg ht.1]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hv.1 i,hv.2 i⟩) ht.1

open DommaschkJacobian (PhysicalPlane coordinates euclideanFlow)

/-- One signed trajectory with a derivative at the launch join and uniform clearance. -/
def Passage (x₀ : State) (φ : ℝ) : Prop :=
  ∃ y : ℝ → PhysicalPlane, coordinates (y 0) = x₀ ∧ ∀ t ∈ Icc (-duration) duration,
    HasDerivWithinAt y (euclideanFlow φ 1 t (y t)) (Icc (-duration) duration) t ∧
    Bounds (y t 0) (y t 1) (φ+t) ∧ ∀ i, |y t i-x₀ i| ≤ |t| * speed

theorem at_original {uC zC uA zA : FA} (sectors : Sector 0 (202/64))
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA
      DommaschkKamA.u₀A DommaschkKamA.z₀A (1 / 10 ^ 12))
    {u : ℝ} (hu : u ∈ Icc (11 / 25 : ℝ) (27 / 50)) (φ : ℝ) :
    Passage (birth uC zC uA zA u φ) φ := by
  obtain ⟨hr,hz⟩ := birth_error hc ha hu φ
  obtain ⟨f, hf, fd⟩ := outward sectors hr hz (sign := 1) (by norm_num)
  obtain ⟨b, hb, bd⟩ := outward sectors hr hz (sign := -1) (by norm_num)
  have conv {sign t : ℝ} {x : ℝ → State}
      (d : HasDerivWithinAt x (physicalFlow φ sign t (x t)) (Icc 0 duration) t) :
      HasDerivWithinAt (fun s => coordinates.symm (x s))
        (euclideanFlow φ sign t (coordinates.symm (x t))) (Icc 0 duration) t := by
    have der := coordinates.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t d
    rw [euclideanFlow,coordinates.apply_symm_apply]
    exact der
  have hT : (0:ℝ) ≤ duration := by norm_num [duration]
  obtain ⟨y,left,right,ode⟩ := join_physical_clocks (phase := φ) hT
    (congrArg coordinates.symm (hb.trans hf.symm)) (fun t ht => conv (fd t ht).1)
      (fun t ht => conv (bd t ht).1)
  refine ⟨y,?_,fun t ht => ⟨ode t ht,?_⟩⟩
  · rw [right (show (0:ℝ) ∈ Icc 0 duration from ⟨le_rfl,hT⟩)]
    exact (coordinates.apply_symm_apply _).trans hf
  · rcases le_total 0 t with hp | hn
    · rw [right ⟨hp,ht.2⟩,abs_of_nonneg hp]
      rw [show (coordinates.symm (f t)).ofLp = f t from coordinates.apply_symm_apply _]
      simpa only [one_mul] using (fd t ⟨hp,ht.2⟩).2
    · have hb' : -t ∈ Icc 0 duration := ⟨by linarith,by linarith [ht.1]⟩
      rw [left ⟨ht.1,hn⟩,abs_of_nonpos hn]
      rw [show (coordinates.symm (b (-t))).ofLp = b (-t) from coordinates.apply_symm_apply _]
      simpa only [neg_one_mul,neg_neg] using (bd (-t) hb').2

def CommonCollar : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC)
      DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA)
      DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ (u φ : ℝ), u ∈ Icc (11 / 25 : ℝ) (27 / 50) → Passage (birth uC zC uA zA u φ) φ

set_option maxRecDepth 8192 in
theorem from_period (verified : Sector 0 (202/64)) : CommonCollar := by
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

end PlasmaLean.Design.DommaschkPeriodicBirthCollar
