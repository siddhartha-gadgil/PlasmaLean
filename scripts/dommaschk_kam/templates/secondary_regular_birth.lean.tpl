module
public import PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
public import SecondaryFirstWellLowerCache.DommaschkQ0R478LowerFirstWell

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkQ0R478RegularBirths
open Set Certificates.PositionFrameSlabs DommaschkPhaseZeroRegularBirth DommaschkEndpointTraceFamily
open DommaschkQ0R478MirrorBranch327 DommaschkMirrorLaunch DommaschkLowerActionPath
open DommaschkFirstMirrorWell DommaschkEndpointMirrorBranch DommaschkSignedTraceDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem from_passage {c : Checkpoint} {uC zC uA zA : Theory.KAM.FA} {φ : ℝ}
    {extraF extraB : List Step} (small : |φ| ≤ 1 / 2 ^ 19)
    (passage : c.Passage .q0r478 uC zC uA zA φ) (time : 327 / 64 < (c.length : ℝ) / 64)
    (lf : c.forwardRows.length = c.length) (lb : c.backwardRows.length = c.length)
    (rf : c.forwardRows.all packed = true) (rb : c.backwardRows.all packed = true)
    (flink : c.forwardRows = fwdRows ++ extraF) (blink : c.backwardRows = backRows ++ extraB) :
    ∃ y, y φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ) ∧
      Signed (MirrorEndpoint.start .q0r478) c.forwardRows c.backwardRows (c.length / 64) y ∧
      Population (317 / 64) y := by
  have pos : 0 < c.length := by
    by_contra! zero
    rw [Nat.eq_zero_of_le_zero zero] at time
    norm_num at time
  have result := at_original_birth (e := .q0r478) rfl (c := c)
    (P := fun y => Signed (MirrorEndpoint.start .q0r478) c.forwardRows c.backwardRows
      (c.length / 64) y ∧ Population (317 / 64) y) passage (small.trans (by linarith)) (by
      intro y path
      have reg := regions path.forward path.backward pos lf lb rf rb
      refine ⟨reg,path,?_⟩
      have f := path.forward
      have b := path.backward
      rw [flink] at f
      rw [blink] at b
      obtain ⟨fw⟩ := fwd_branch f.prefix time
      obtain ⟨bw⟩ := back_branch b.prefix time
      have region (t : ℝ) (ht : t ∈ Icc (-(327 / 64) : ℝ) (327 / 64)) : Region (y t) :=
        reg t ⟨by linarith [ht.1],by linarith [ht.2]⟩
      exact population path time region fw bw)
  convert result using 4
  norm_num [MirrorEndpoint.radius]

end PlasmaLean.Design.DommaschkQ0R478RegularBirths
