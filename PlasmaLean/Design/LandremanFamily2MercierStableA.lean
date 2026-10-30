/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2ArcCert

/-!
# Rejected fixture of the family-2 Mercier checker: the near-axis cell (`λ = 200`)

Non-vacuity of `PlasmaLean.Design.LandremanFamily2Quad.cellCheck`: the checker rejects
the near-axis cell `k ∈ [1/10, 11/100]` at `λ = 200`
(hill-dominated; numerically those surfaces are Mercier unstable). The check is split into
pieces, each a separate declaration so that kernel memory stays bounded (one declaration for
the whole run peaked at ≈ 6.9 GB): the one-dimensional quadratures (`oned_cert`), the four
outer-arc surface-integral contributions (evaluation certificates `eval_cert`, see
`f2_arc_cert` in `PlasmaLean.Design.LandremanFamily2ArcCert`) and the final combination
(`fiv_cert`), against literal enclosures produced by `#eval` of the same functions (untrusted;
the kernel re-checks them). Re-exported by `PlasmaLean.Design.LandremanFamily2MercierStable`.
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad
open PlasmaLean.Design.SolovevMercierQuadrature (Ecell)

set_option maxRecDepth 100000

/-- **Assembly from pieces** (equation form, for accepted and rejected cells alike): with the
one-dimensional data and the four outer-arc contributions known, the checker equals its final
combination. -/
theorem cellCheck_eq_of_pieces {lam N1 ntip nside N2 : ℕ} {ka kb : ℚ}
    {D : FIv × FIv × FIv × FIv × FIv × FIv} {O0 O1 O2 O3 : FIv × FIv × FIv}
    (hD : oneD N1 (Ecell ka kb) = D)
    (h0 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 0 = O0)
    (h1 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 1 = O1)
    (h2 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 2 = O2)
    (h3 : outerArc (lamC lam) (Ecell ka kb) (Ecell ka kb).sq (dIof lam D.1 D.2.2.2.2.1) ntip
      nside N2 3 = O3) :
    cellCheck lam N1 ntip nside N2 ka kb =
      cellCheckOf lam N1 ntip nside N2 ka kb D (add3 (add3 O0 O1) (add3 O2 O3)) := by
  unfold cellCheck outerSum
  simp only [hD]
  rw [h0, h1, h2, h3]

/-- One-dimensional enclosures `F₁, F₁', Z, Z', E, E'` of the near-axis cell. -/
@[expose] def Dax : FIv × FIv × FIv × FIv × FIv × FIv :=
  (⟨3367853489, 3396470108, true⟩, ⟨183345728, 220181743, true⟩, ⟨26947477013, 27111975586,
  true⟩, ⟨2700538947, 2995382986, true⟩, ⟨26985940680, 27136247997, true⟩, ⟨1348821768,
  1522253951, true⟩)

/-- One-dimensional piece of the near-axis cell. -/
theorem ax_oneD : oneD 128 (Ecell (1/10) (11/100)) = Dax := eq6_sound (by oned_cert)

/-- Outer-arc enclosures `0` of the near-axis cell. -/
@[expose] def Oax_0 : FIv × FIv × FIv :=
  (⟨881443015855049, 1696609407209801, true⟩, ⟨-3952658507968, 3591414613862, true⟩,
  ⟨-717663632294, 746536732007, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `0` of the near-axis cell. -/
theorem ax_arc0 : outerArc (lamC 200) (Ecell (1/10) (11/100)) (Ecell (1/10) (11/100)).sq
    (dIof 200 Dax.1 Dax.2.2.2.2.1) 8 8 4 0 = Oax_0 := by
  f2_arc_cert

/-- Outer-arc enclosures `1` of the near-axis cell. -/
@[expose] def Oax_1 : FIv × FIv × FIv :=
  (⟨857117737254079, 1650607210423044, true⟩, ⟨-3827399971108, 3489377993526, true⟩,
  ⟨-699551654030, 726098823078, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `1` of the near-axis cell. -/
theorem ax_arc1 : outerArc (lamC 200) (Ecell (1/10) (11/100)) (Ecell (1/10) (11/100)).sq
    (dIof 200 Dax.1 Dax.2.2.2.2.1) 8 8 4 1 = Oax_1 := by
  f2_arc_cert

/-- Outer-arc enclosures `2` of the near-axis cell. -/
@[expose] def Oax_2 : FIv × FIv × FIv :=
  (⟨851646249852587, 1706827833220634, true⟩, ⟨-4962147603337, 4604524051187, true⟩,
  ⟨-958986229154, 992243908074, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `2` of the near-axis cell. -/
theorem ax_arc2 : outerArc (lamC 200) (Ecell (1/10) (11/100)) (Ecell (1/10) (11/100)).sq
    (dIof 200 Dax.1 Dax.2.2.2.2.1) 8 8 4 2 = Oax_2 := by
  f2_arc_cert

/-- Outer-arc enclosures `3` of the near-axis cell. -/
@[expose] def Oax_3 : FIv × FIv × FIv :=
  (⟨851646249852587, 1706827833220634, true⟩, ⟨-4962147603337, 4604524051187, true⟩,
  ⟨-958986229154, 992243908074, true⟩)

set_option maxHeartbeats 4000000 in
-- the `eval_cert` builder evaluates ≈ 2.8·10⁴ interval operations in `meta` code
/-- Outer-arc piece `3` of the near-axis cell. -/
theorem ax_arc3 : outerArc (lamC 200) (Ecell (1/10) (11/100)) (Ecell (1/10) (11/100)).sq
    (dIof 200 Dax.1 Dax.2.2.2.2.1) 8 8 4 3 = Oax_3 := by
  f2_arc_cert

/-- Final combination of the near-axis cell: the checker rejects. -/
theorem ax_final : cellCheckOf 200 128 8 8 4 (1/10) (11/100) Dax
    (add3 (add3 Oax_0 Oax_1) (add3 Oax_2 Oax_3)) = false := by fiv_cert

/-- Rejected fixture (non-vacuity of the checker): a near-axis cell `k ∈ [1/10, 11/100]`,
where the surfaces are Mercier unstable (hill-dominated), is not accepted. -/
theorem cellCheck_rejects_axis : cellCheck 200 128 8 8 4 (1/10) (11/100) = false :=
  (cellCheck_eq_of_pieces ax_oneD ax_arc0 ax_arc1 ax_arc2 ax_arc3).trans ax_final

end PlasmaLean.Design.LandremanFamily2Cert
