/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGroupedMirrorModels
public import PlasmaLean.Design.DommaschkNativeActionGeometry

/-! # Compensated mirror-gap estimates from the first angular harmonic -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkGroupedHarmonicGap
open Certificates.TrajectoryTaylorModel DommaschkBounceTaylor DommaschkHarmonicHorner
open DommaschkCompensatedAction DommaschkMirrorEndpointSign DommaschkKam

abbrev product := (⟨7, 80⟩ : Format).mul
abbrev twice (a : Model) := addModel a a
abbrev three (a : Model) := addModel (twice a) a
abbrev four (a : Model) := twice (twice a)

/-- Enclose every angular harmonic of the physical field on the same group clock. -/
def harmonic (c s : Model) : Wave → Model
  | .one => constant 1
  | .sin1 => s
  | .cos1 => c
  | .sin2 => twice (product s c)
  | .cos2 => addModel (twice (product c c)) (constant (-1))
  | .sin3 => addModel (three s) (TaylorResidual.neg (four (product (product s s) s)))
  | .cos3 => addModel (four (product (product c c) c)) (TaylorResidual.neg (three c))

theorem harmonic_mem {w θ : ℝ} {c s : Model} (hw : |w| ≤ 1)
    (hc : c.Mem w (Real.cos θ)) (hs : s.Mem w (Real.sin θ)) (k : Wave) :
    (harmonic c s k).Mem w (k.value θ) := by
  have prod {a b : Model} {x y : ℝ} (ha : a.Mem w x) (hb : b.Mem w y) :
      (product a b).Mem w (x*y) := Format.mul_mem _ hw ha hb
  have dbl {a : Model} {x : ℝ} (ha : a.Mem w x) : (twice a).Mem w (x+x) := mem_add ha ha
  cases k with
  | one => simpa only [harmonic, Wave.value, Rat.cast_one] using constant_mem 1 w
  | sin1 => exact hs
  | cos1 => exact hc
  | sin2 =>
    rw [harmonic, Wave.value, Real.sin_two_mul]
    convert dbl (prod hs hc) using 1
    ring
  | cos2 =>
    rw [harmonic, Wave.value, Real.cos_two_mul]
    have neg_one : (constant (-1)).Mem w (-1) := by simpa using constant_mem (-1) w
    convert mem_add (dbl (prod hc hc)) neg_one using 1
    ring
  | sin3 =>
    rw [harmonic, Wave.value, Real.sin_three_mul]
    convert mem_add (mem_add (dbl hs) hs) (TaylorResidual.neg_mem
      (dbl (dbl (prod (prod hs hs) hs)))) using 1
    ring
  | cos3 =>
    rw [harmonic, Wave.value, Real.cos_three_mul]
    convert mem_add (dbl (dbl (prod (prod hc hc) hc))) (TaylorResidual.neg_mem
      (mem_add (dbl hc) hc)) using 1
    ring

/-- Evaluate the factored difference after subtracting the exact dominant term from D. -/
def estimate (r d nr nz shift : Model) : Model :=
  addModel (addModel (product (product (product r r) shift)
    (addModel (twice d) (TaylorResidual.neg shift))) (product nr nr)) (product nz nz)

theorem estimate_mem {k : ℚ} {r d nr nz shift : Model} {w R z c s : ℝ} (hw : |w| ≤ 1)
    (hr : r.Mem w R) (hd : d.Mem w (evR (R - dkR0) z c s dD))
    (hnr : nr.Mem w (evR (R - dkR0) z c s dnR))
    (hnz : nz.Mem w (evR (R - dkR0) z c s dnZ))
    (hsh : shift.Mem w (evR (R - dkR0) z c s (shiftedD k))) :
    (estimate r d nr nz shift).Mem w (gap R k (evR (R - dkR0) z c s dD)
      (evR (R - dkR0) z c s dnR) (evR (R - dkR0) z c s dnZ)) := by
  have prod {a b : Model} {x y : ℝ} (ha : a.Mem w x) (hb : b.Mem w y) :
      (product a b).Mem w (x*y) := Format.mul_mem _ hw ha hb
  rw [estimate, gap_from_shift k (rfl : R - dkR0 = R - dkR0)]
  convert mem_add (mem_add (prod (prod (prod hr hr) hsh)
    (mem_add (mem_add hd hd) (TaylorResidual.neg_mem hsh))) (prod hnr hnr)) (prod hnz hnz)
    using 1
  ring

end PlasmaLean.Design.DommaschkGroupedHarmonicGap
