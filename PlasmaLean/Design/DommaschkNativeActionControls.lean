/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkActionQ0R470
public import PlasmaLean.Certificates.NativeActionColumns

/-! # Ordering and one-tick negative controls on actual archived row 16 -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkNativeActionControls
open Certificates.MirrorActionQuadrature Certificates.NativeActionInterval

/-- The forward launch-outward panel at `t = 16/64`. -/
noncomputable def forwardWord : ℕ := DommaschkActionQ0R470.slabGroup21[5].packed % 2^72
/-- Index zero in backward chronological order is the other end of the slab. -/
noncomputable def backwardPacked : ℕ := DommaschkActionQ0R470.slabGroup19[4].packed

theorem reversed_record_matches :
    (forwardWord == ((backwardPacked >>> (47*72)) % 2^72)) = true := by kernel_fact

theorem unreversed_record_differs :
    (forwardWord == (backwardPacked % 2^72)) = false := by kernel_fact

theorem small_root_rejected : rootTest true (forwardWord - 2^48) = false := by kernel_fact

theorem large_root_fails_minimality :
    rootTest true (forwardWord + 2^48) = true ∧
    rootNeighbor true (forwardWord + 2^48) = false := by kernel_fact

end PlasmaLean.Design.DommaschkNativeActionControls
