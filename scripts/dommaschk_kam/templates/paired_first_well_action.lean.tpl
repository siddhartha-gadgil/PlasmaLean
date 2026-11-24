module
public import PlasmaLean.Design.DommaschkPairedFirstWellAction
public import SecondaryFirstWellLowerCache.DommaschkQ0R478LowerFirstWell

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedFirstWell325
open Certificates.PositionFrameSlabs DommaschkPairedFirstWellAction
open DommaschkEndpointTraceFamily DommaschkComparedTracePrefixes DommaschkLowerActionPath
open DommaschkQ0R478MirrorBranch327 DommaschkQ0R478LowerFirstWell
open DommaschkMirrorLaunch DommaschkEndpointMirrorBranch
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The same physical outer trajectory supplies the signed tube comparisons, the regular
arclength density and both first mirrors for all shifted heights at once. -/
theorem from_family {c : MirrorEndpoint → Checkpoint} {P : ℝ → (ℝ → Plane) → Prop}
    {extraF extraB : List Step}
    (cal : DommaschkCommonPilotObservables.Common c P)
    (pilot : ∀ {φ y}, P φ y → DommaschkActionFlightFloor.TimeBounds φ y ∧
      DommaschkFiniteRadialAction.PairTest y)
    (hf : 325 ≤ (c .q0r470).forwardRows.length) (hb : 325 ≤ (c .q0r470).backwardRows.length)
    (room : 327 / 64 < ((c .q0r478).length : ℝ) / 64)
    (flink : (c .q0r478).forwardRows = fwdRows ++ extraF)
    (blink : (c .q0r478).backwardRows = backRows ++ extraB)
    (cert : ComparedRows 325 (c .q0r470) (c .q0r478)) : OnCommonTori c P := by
  apply common cal hf hb cert
  intro φ y z obs path cmp
  have f := path.forward
  have b := path.backward
  rw [flink] at f
  rw [blink] at b
  have fw := f.prefix
  have bw := b.prefix
  obtain ⟨fb⟩ := fwd_branch fw room
  obtain ⟨bb⟩ := back_branch bw room
  have reg := regions fw bw (n := 327) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) forward_regular backward_regular
  exact gains_of_branches (pilot obs).1 (pilot obs).2 cmp path room
    (by simpa only [Nat.cast_ofNat] using reg) fb bb

end PlasmaLean.Design.DommaschkPairedFirstWell325
