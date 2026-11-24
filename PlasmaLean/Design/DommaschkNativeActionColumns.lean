/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeActionColumns
public import PlasmaLean.Design.DommaschkPhysicalActionPanel

/-! # Directed native action digits bound arclength and clipped parallel speed -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkNativeActionColumns
open Certificates Certificates.NativeActionInterval Certificates.MirrorActionQuadrature
open DommaschkBounceField DommaschkKam DommaschkPhysicalActionPanel Contract

abbrev magnitude (R φ z : ℝ) : ℝ :=
  ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)‖

/-- The signed gap numerator is positive on the accessible side of a turning point. -/
def quantities (R φ z h : ℝ) : Five ℝ :=
  let d := atPoint dD R φ z
  let nr := atPoint dnR R φ z
  let nz := atPoint dnZ R φ z
  ⟨d, R^8, R^16, (R*d)^2 + nr^2 + nz^2, R^16 * (h^2 - (magnitude R φ z)^2)⟩

theorem root_eq {R : ℝ} (hr : 0 < R) (φ z h : ℝ) :
    Real.sqrt (quantities R φ z h).u = R^8 * magnitude R φ z := by
  have eq : (quantities R φ z h).u = (R^8 * magnitude R φ z)^2 := by
    rw [mul_pow, show (magnitude R φ z)^2 = _ from norm_sq_eq_strengthSq hr φ z]
    dsimp [quantities, RadialSlabs.strengthSq]
    field_simp [hr.ne']
    ring
  rw [eq, Real.sqrt_sq (mul_nonneg (pow_nonneg hr.le _) (norm_nonneg _))]

theorem clipped_eq {R B h : ℝ} (r : 0 < R) (b : 0 ≤ B) (hh : 0 < h) :
    2 * (max (R^16 * (h^2-B^2)) 0 / (R^16 * (h+B))) = max (2*(h-B)) 0 := by
  have pos : 0 < R^16*(h+B) := mul_pos (pow_pos r _) (add_pos_of_pos_of_nonneg hh b)
  have eq : R^16*(h^2-B^2) = (h-B)*(R^16*(h+B)) := by ring
  have clipped : max (R^16*(h^2-B^2)) 0 = (max (h-B) 0)*(R^16*(h+B)) := by
    rw [eq, mul_comm (max (h-B) 0), mul_max_of_nonneg _ _ pos.le, mul_zero, mul_comm (h-B)]
  rw [clipped, mul_div_cancel_right₀ _ pos.ne', mul_max_of_nonneg _ _ (by norm_num), mul_zero]

theorem physical {R φ z : ℝ} {h : ℚ} {upper : Bool}
    {v : Five NativeActionInterval.Box} {root : NativeActionInterval.Box} {p : ℕ}
    (r : 0 < R) (hh : 0 < h) (ch : Checked upper v root h p)
    (mem : Five.Rel NativeActionInterval.Box.Mem v (quantities R φ z h)) :
    Directed upper (arcDensity R φ z) (density p / 1048576) ∧
    Directed upper (max (2*((h:ℝ)-magnitude R φ z)) 0) (speedSq p / 67108864) := by
  have dpos : 0 < atPoint dD R φ z := pos_of_mem ch.den_pos mem.1
  have hn : 0 ≤ (quantities R φ z h).u :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  obtain ⟨density_bound,speed_bound⟩ := ch.sound mem hn
  rw [root_eq r] at density_bound speed_bound
  change Directed upper (R^8*magnitude R φ z / atPoint dD R φ z) _ at density_bound
  have ds : R^8*magnitude R φ z / atPoint dD R φ z = arcDensity R φ z := by
    rw [(field_id r φ z).1, arcDensity]
    field_simp [r.ne', (toroidal_pos_of_den r dpos).ne']
  rw [ds] at density_bound
  change Directed upper (2 * (max (R^16*((h:ℝ)^2 - (magnitude R φ z)^2)) 0 /
    (R^16*((h:ℝ)+R^8*magnitude R φ z / R^8)))) _ at speed_bound
  rw [mul_div_cancel_left₀ _ (pow_ne_zero 8 r.ne'),
    clipped_eq r (norm_nonneg _) (by exact_mod_cast hh)] at speed_bound
  exact ⟨density_bound,speed_bound⟩

end PlasmaLean.Design.DommaschkNativeActionColumns
