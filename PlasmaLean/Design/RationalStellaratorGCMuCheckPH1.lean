/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuTreesH
public import PlasmaLean.Design.RationalStellaratorGCMuKvSH
public import PlasmaLean.Certificates.KronProof
meta import PlasmaLean.Design.RationalStellaratorGCMuTreesH
meta import PlasmaLean.Design.RationalStellaratorGCMuKvSH

/-!
# Kronecker ball checks as proof terms (`Design/RationalStellaratorGCMuCheckH1`, prototype)

The checks of `Design/RationalStellaratorGCMuCheckH1`, with the same statements, proved by explicit
certificates (`Certificates/KronProof`) instead of `decide +kernel`: `kron_proof` builds the
signed-image, reading and comparison certificate of each `k*S_*` check (`chebKV_le_of_cert`), and
`kron_lt` proves each `ℓ¹` check by one kernel fact `Nat.ble (a + 1) c = true`. The theorems are in
the sub-namespace `ProofTerm` (prototype, Phase 16). Light module.
-/

@[expose] public section

-- check the theorems one at a time (bounded memory per process)
set_option Elab.async false

namespace PlasmaLean.Design.RationalStellaratorGC.ProofTerm

open PlasmaLean.Certificates.KronBallCheb PlasmaLean.Certificates.KronLowMem
  PlasmaLean.Certificates.KronProof

/-- Proof-term check of the node `qR`: truncation norm. -/
theorem kHMS_qR : node3KS SHM NHM MHM DHM WtHM KvSHM trHMN_qR (1 : Int) 1 0 47 245 145 109 49 13 8 19 72 54 ≤
    2871217126197696523159428903662867917151339450908395928209607000404560624138523408080768956151568120430986760240394568550160802823362238726023698741462336224223031381809307720149996260259468426267263894305956856760815875965857605239341612511128733192730767145640643304607427494661450196554181297915437980981397821088973870089174969015746182880373643238150633946278429606157037782519538016997577183336503106557740671099551476158319697629853876437288932012960098566100990234504743525660352134418764498509369427946484321708487289850316717140657999303822247681436528260353393479758734764307367354194977485034572183313235609554128105815303866286080000000 := by
  kron_proof

/-- Proof-term check of the node `qR`: a priori `ℓ¹` bound. -/
theorem lHM_qR : nodeL1N SHM LHM trHMN_qR (1 : Int) 1 0 47 < 2 ^ (245 - 1) := by
  kron_lt

end PlasmaLean.Design.RationalStellaratorGC.ProofTerm
