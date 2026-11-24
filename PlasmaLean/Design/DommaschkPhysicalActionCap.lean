/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalActionPanel

/-! # A quadrature panel beyond a transverse mirror -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalActionPanel
open Certificates DommaschkBounceField DommaschkKam DommaschkMirrorEndpointSign

/-- The arclength bound needs only four scalar enclosures, independently of the mirror height. -/
theorem arcDensity_le_of_ranges {R φ z a r d b c : ℝ}
    (hr : 0 < R) (ha : 0 ≤ a) (hr' : R ≤ r) (hd : 0 < d) (hd' : d ≤ atPoint dD R φ z)
    (hb : |atPoint dnR R φ z| ≤ b) (hc : |atPoint dnZ R φ z| ≤ c) (hs : r ^ 2 ≤ a ^ 2)
    (checked : b ^ 2 + c ^ 2 ≤ (a ^ 2 - r ^ 2) * d ^ 2) : arcDensity R φ z ≤ a := by
  have margin := density_margin_of_ranges hr.le hr' hd.le hd' hb hc hs checked
  apply (upper_columns (h := 0) (g := 0) hr ha le_rfl (by norm_num) (hd.trans_le hd')
    margin ?_).1
  rw [gap_eq hr]
  norm_num
  positivity

/-- An outward-monotone squared field gives exactly zero clipped speed on the entire
part of the panel following a single above-height sample. -/
theorem zero_speed_of_monotone {f : ℝ → ℝ} {I : Set ℝ} {a t h : ℝ}
    (mono : MonotoneOn (fun x => (f x) ^ 2) I) (ha : a ∈ I) (ht : t ∈ I) (order : a ≤ t)
    (fa : 0 ≤ f a) (ft : 0 ≤ f t) (above : h ≤ f a) : max (2 * (h - f t)) 0 = 0 := by
  have ge := (sq_le_sq₀ fa ft).mp (mono ha ht order)
  exact max_eq_right (by linarith)

end PlasmaLean.Design.DommaschkPhysicalActionPanel
