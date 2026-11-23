/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.EmbeddedSurfaces
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Instances.ZMultiples

/-!
# Irrational returns on a winding section

Equality of positions, or vanishing of a tangent, need only propagate one return.
The irrational return has dense forward orbits. Winding once removes smaller periods
of the position and excludes a section with identically vanishing tangent.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Contract

open Real Set Function Forms Fields Vacuum
open scoped Topology

/-- A closed condition on a continuous periodic observable extends from a single
initial point to the whole circle if it propagates under an irrational return. -/
theorem periodic_mem_closed_of_irrational_return {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {U : Set E} {ι x₀ : ℝ} (hc : Continuous f) (hp : Periodic f (2 * π))
    (hU : IsClosed U) (hι : Irrational ι) (h₀ : f x₀ ∈ U)
    (step : ∀ x, f x ∈ U → f (x + 2 * π * ι) ∈ U) (x : ℝ) : f x ∈ U := by
  let _ : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  let d := 2 * π * ι
  let hp' := hp.const_add x₀
  have hl : Continuous hp'.lift :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
      (hc.comp (continuous_const.add continuous_id))
  have hd : DenseRange (fun n : ℕ => n • (d : AddCircle (2 * π))) := by
    apply denseRange_zsmul_iff_nsmul.mp
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa [d, two_pi_pos.ne'] using hι
  have hn (n : ℕ) : f (x₀ + n • d) ∈ U := by
    induction n with
    | zero => simpa using h₀
    | succ n ih => simpa only [succ_nsmul, ← add_assoc, d] using step (x₀ + n • d) ih
  have hall (q : AddCircle (2 * π)) : hp'.lift q ∈ U := by
    apply hd.induction_on (p := fun y => hp'.lift y ∈ U) q (hU.preimage hl)
    intro n
    rw [← AddCircle.coe_nsmul, Periodic.lift_coe]
    exact hn n
  have h := hall ((x - x₀ : ℝ) : AddCircle (2 * π))
  rw [Periodic.lift_coe] at h
  simpa only [add_sub_cancel] using h

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {R₀ z₀ : ℝ → ℝ} {Θ : ℝ → ℝ → ℝ} {ι : ℝ}

private theorem PoloidalAngle.angle_sub_mem (hΘ : PoloidalAngle R z R₀ z₀ Θ)
    {θ θ' φ : ℝ} (hR : R θ φ = R θ' φ) (hz : z θ φ = z θ' φ) :
    Θ θ' φ - Θ θ φ ∈ AddSubgroup.zmultiples (2 * π) := by
  obtain ⟨r, hr, u, v⟩ := hΘ.polar θ φ
  obtain ⟨s, hs, u', v'⟩ := hΘ.polar θ' φ
  have hu : r * cos (Θ θ φ) = s * cos (Θ θ' φ) := by rw [← u, ← u', hR]
  have hv : r * sin (Θ θ φ) = s * sin (Θ θ' φ) := by rw [← v, ← v', hz]
  have radial (q a : ℝ) : (q * cos a) ^ 2 + (q * sin a) ^ 2 = q ^ 2 := by
    linear_combination q ^ 2 * Real.cos_sq_add_sin_sq a
  have hrs : r = s := by
    have hsq := radial r (Θ θ φ)
    rw [hu, hv, radial] at hsq
    nlinarith
  subst s
  obtain ⟨m, hm⟩ := exists_int_of_cos_sin_eq (mul_left_cancel₀ hr.ne' hu)
    (mul_left_cancel₀ hr.ne' hv)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, by rw [hm, zsmul_eq_mul]; ring⟩

/-- Every common period of the two section coordinates is a whole number of turns
when its polar angle has degree one. -/
theorem PoloidalAngle.section_period (hΘ : PoloidalAngle R z R₀ z₀ Θ) {φ d : ℝ}
    (hp : ∀ y, R (y + d) φ = R y φ ∧ z (y + d) φ = z y φ) :
    ∃ m : ℤ, d = 2 * π * m := by
  let inc : ℝ → AddSubgroup.zmultiples (2 * π) := fun y =>
    ⟨Θ (y + d) φ - Θ y φ, hΘ.angle_sub_mem (hp y).1.symm (hp y).2.symm⟩
  have hθ : Continuous fun y => Θ y φ := hΘ.continuous.comp (continuous_id.prodMk continuous_const)
  have hi : Continuous inc := (hθ.comp (continuous_id.add continuous_const) |>.sub hθ).subtype_mk _
  have hi' (y : ℝ) : Θ (y + d) φ - Θ y φ = Θ (0 + d) φ - Θ 0 φ :=
    congrArg Subtype.val (hi.isConst_of_preconnectedSpace y 0)
  let drift := fun y => Θ y φ - y
  have hper : Periodic drift (2 * π) := fun y => by simp [drift, hΘ.wind_θ]
  have hcompact := hper.compact_of_continuous two_pi_pos.ne' (hθ.sub continuous_id)
  obtain ⟨_, ⟨y, rfl⟩, hmax⟩ := hcompact.exists_isMaxOn (range_nonempty _) continuousOn_id
  have upper (u : ℝ) : drift u ≤ drift y := hmax (mem_range_self u)
  have hL := upper (y + d)
  have hR := upper (y - d)
  have hiL := hi' y
  have hiR := hi' (y - d)
  rw [sub_add_cancel] at hiR
  dsimp [drift] at hL hR
  have he : d = Θ (0 + d) φ - Θ 0 φ := by linarith
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (inc 0).property
  exact ⟨m, he.trans (by simpa only [zsmul_eq_mul, mul_comm] using hm.symm)⟩

/-- A single - valued return over an irrational rotation makes every winding - one
section injective modulo its angular period. -/
theorem PoloidalAngle.sections_injective_of_irrational_return (hΘ : PoloidalAngle R z R₀ z₀ Θ)
    (hι : Irrational ι) (hT : FieldTorus B R z ι)
    (step : ∀ θ θ' φ, R θ φ = R θ' φ → z θ φ = z θ' φ →
      R (θ + 2 * π * ι) φ = R (θ' + 2 * π * ι) φ ∧
      z (θ + 2 * π * ι) φ = z (θ' + 2 * π * ι) φ)
    (θ θ' φ : ℝ) (hr : R θ φ = R θ' φ) (hz : z θ φ = z θ' φ) :
    ∃ m : ℤ, θ' = θ + 2 * π * m := by
  let d := θ' - θ
  let k := fun x : ℝ => (R x φ, z x φ)
  have hc : Continuous k := (hT.continuous_R.prodMk hT.continuous_z).comp
    (continuous_id.prodMk continuous_const)
  have hper : Periodic k (2 * π) := fun x => Prod.ext (hT.per_θ_R x φ) (hT.per_θ_z x φ)
  let f := fun x => k (x + d) - k x
  have hf : Continuous f := (hc.comp (continuous_id.add continuous_const)).sub hc
  have hp : Periodic f (2 * π) := (hper.add_const d).sub hper
  have h₀ : f θ ∈ ({0} : Set (ℝ × ℝ)) := by
    rw [mem_singleton_iff, show f θ = k (θ+d) - k θ from rfl, sub_eq_zero]
    simpa only [d, add_sub_cancel] using (Prod.ext hr.symm hz.symm : k θ' = k θ)
  have hstep (x : ℝ) (hx : f x ∈ ({0} : Set (ℝ × ℝ))) : f (x + 2 * π * ι) ∈ ({0} : Set _) := by
    have h : k (x + d) = k x := sub_eq_zero.mp hx
    obtain ⟨a, b⟩ := step (x + d) x φ (congrArg Prod.fst h) (congrArg Prod.snd h)
    apply sub_eq_zero.mpr
    rw [add_right_comm x (2 * π * ι) d]
    exact Prod.ext a b
  obtain ⟨m, hm⟩ := hΘ.section_period (φ := φ) (d := d) fun x => by
    have h : k (x + d) = k x := sub_eq_zero.mp
      (periodic_mem_closed_of_irrational_return hf hp isClosed_singleton hι h₀ hstep x)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  exact ⟨m, by dsimp [d] at hm; linarith⟩

/-- A vanishing section tangent would propagate densely and make the section constant,
contrary to its winding about the reference point. -/
theorem PoloidalAngle.sections_immersed_of_irrational_return (hΘ : PoloidalAngle R z R₀ z₀ Θ)
    (hι : Irrational ι) (hT : FieldTorus B R z ι)
    (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2))
    (step : ∀ θ φ, deriv (fun x => R x φ) θ = 0 ∧ deriv (fun x => z x φ) θ = 0 →
      deriv (fun x => R x φ) (θ + 2 * π * ι) = 0 ∧ deriv (fun x => z x φ) (θ + 2 * π * ι) = 0)
    (θ φ : ℝ) : ¬ (deriv (fun x => R x φ) θ = 0 ∧ deriv (fun x => z x φ) θ = 0) := by
  intro h0
  have rreg : ContDiff ℝ 2 (fun x => R x φ) := hR.comp (contDiff_id.prodMk contDiff_const)
  have zreg : ContDiff ℝ 2 (fun x => z x φ) := hz.comp (contDiff_id.prodMk contDiff_const)
  let f := fun x => (deriv (fun u => R u φ) x, deriv (fun u => z u φ) x)
  have hc : Continuous f := (rreg.continuous_deriv (by norm_num)).prodMk
    (zreg.continuous_deriv (by norm_num))
  have dper {g : ℝ → ℝ} (hp : Periodic g (2 * π)) : Periodic (deriv g) (2 * π) := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun F : ℝ → ℝ => deriv F x) (funext hp)
  have hp : Periodic f (2 * π) := fun x =>
    Prod.ext (dper (fun u => hT.per_θ_R u φ) x) (dper (fun u => hT.per_θ_z u φ) x)
  have hs (x : ℝ) (hx : f x ∈ ({0} : Set (ℝ × ℝ))) : f (x + 2 * π * ι) ∈ ({0} : Set _) := by
    apply Prod.ext
    · exact (step x φ ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩).1
    · exact (step x φ ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩).2
  have he (x : ℝ) : f x = 0 := periodic_mem_closed_of_irrational_return
    hc hp isClosed_singleton hι (Prod.ext h0.1 h0.2 : f θ = 0) hs x
  obtain ⟨x, hx⟩ := hΘ.exists_R_gt φ
  obtain ⟨y, hy⟩ := hΘ.exists_R_lt φ
  have heq := is_const_of_deriv_eq_zero (rreg.differentiable (by norm_num))
    (fun u => congrArg Prod.fst (he u)) x y
  exact (ne_of_gt (hy.trans hx)) heq

end PlasmaLean.Contract
