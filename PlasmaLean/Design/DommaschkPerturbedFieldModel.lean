/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkUniformFieldError

/-! # Promote a checked central polynomial model to a physical tube -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkPerturbedFieldModel
open DommaschkBounceTaylor DommaschkKam DommaschkKam.DkPoly DommaschkKamC
open Certificates.TrajectoryTaylorModel DommaschkPhysicalPolynomialError

/-- Bounds checked on the reference coordinates and the physical uncertainty in its two inputs. -/
structure Geometry (center tube : Inputs) : Prop where
  uCenter : tube.u.poly = center.u.poly
  zCenter : tube.z.poly = center.z.poly
  cos : tube.cos = center.cos
  sin : tube.sin = center.sin
  uNonneg : 0 ≤ center.u.radius
  zNonneg : 0 ≤ center.z.radius
  uBound : magnitude center.u.poly ≤ 3 / 32
  zBound : magnitude center.z.poly ≤ 5 / 64
  uError : tube.u.radius ≤ 1 / 2 ^ 18
  zError : tube.z.radius ≤ 1 / 2 ^ 18

/-- Real trigonometric inputs satisfy the unit bounds in the sparse perturbation majorant. -/
structure FieldModel (tube : Inputs) (p : SP) (value : Model) : Prop where
  mem : ∀ {t u z c s : ℝ}, |t| ≤ 1 → tube.Mem t u z c s → |c| ≤ 1 → |s| ≤ 1 →
    value.Mem t (evR u z c s p)

/-- One reusable candidate-wide perturbation budget suffices on every matching trajectory slab. -/
theorem transfer {center tube : Inputs} {p : SP} {m n : Model} {F : Format} {δ : ℚ}
    (geometry : Geometry center tube) (nominal : Blocks F center p m)
    (bounded : lipQ (3 / 32) (5 / 64) (1 / 2 ^ 18) (1 / 2 ^ 18) 1 p ≤ δ)
    (poly : m.poly = n.poly) (error : m.radius + δ ≤ n.radius) : FieldModel tube p n := by
  constructor
  intro t u z c s ht h hc hs
  let u₀ := Certificates.QPoly.eval center.u.poly t
  let z₀ := Certificates.QPoly.eval center.z.poly t
  have nom : center.Mem t u₀ z₀ c s := by
    refine ⟨?_, ?_, geometry.cos ▸ h.2.2.1, geometry.sin ▸ h.2.2.2⟩
    · simpa [u₀, Model.Mem] using (Rat.cast_nonneg.mpr geometry.uNonneg :
        0 ≤ (center.u.radius : ℝ))
    · simpa [z₀, Model.Mem] using (Rat.cast_nonneg.mpr geometry.zNonneg :
        0 ≤ (center.z.radius : ℝ))
  have lift {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h
  have ub : |u₀| ≤ (3 / 32 : ℝ) :=
    (abs_eval_le ht _).trans (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using lift geometry.uBound)
  have zb : |z₀| ≤ (5 / 64 : ℝ) :=
    (abs_eval_le ht _).trans (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using lift geometry.zBound)
  have eu := h.1
  have ez := h.2.1
  rw [Model.Mem, geometry.uCenter] at eu
  rw [Model.Mem, geometry.zCenter] at ez
  have du : |u - u₀| ≤ (1 / 2 ^ 18 : ℝ) := eu.trans (by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow] using
      lift geometry.uError)
  have dz : |z - z₀| ≤ (1 / 2 ^ 18 : ℝ) := ez.trans (by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow] using
      lift geometry.zError)
  have major := (lipR_cast (3 / 32) (5 / 64) (1 / 2 ^ 18) (1 / 2 ^ 18) 1 p).le.trans
    (Rat.cast_le.mpr bounded)
  push_cast at major
  apply widen (nominal.mem ht nom) _ poly error
  exact (field_error p ub zb du dz hc hs).trans major

end PlasmaLean.Design.DommaschkPerturbedFieldModel
