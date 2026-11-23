/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormConvexRegion
public import PlasmaLean.Sanity.FormLoopCurrentInterval
public import PlasmaLean.Sanity.AuditRefreshContract
public import PlasmaLean.Design.RationalStellaratorEmbedded

/-!
# Fixtures for the loop-current corollaries of the stellarator contract

`Theory/Fields/FormLoopCurrentInterval` ends with three corollaries about the structures of the
contract: `FieldTorus.loopCurrent_eq_periodHom_div`,
`FieldTorus.loopCurrent_eq_zero_of_simplyConnected` and
`CurrentFreeTransform.current_eq_zero_of_simplyConnected`. This file shows that their hypotheses
can be satisfied together, by instances of the default build, including a genuine
`CurrentFreeTransform` (rotational transform bounded away from zero).

**Status of these fixtures (audit AV-M1, AV-M2).** The corollaries are Stokes' theorem on the
planar poloidal cross-section: no current through the cross-section, so no circulation around
it. The fixtures are satisfiability and consistency checks. They are NOT evidence that the
topological corollary improves a current allowance in practice: the only instance of
`CurrentFreeTransform` in the default build, `rationalStellarator_currentFreeTransform`, is
already proved with `I_max = 0` (from the potential of the field), and no instance exists
whose current bound was proved by an estimate. These fixtures use the rational stellarator
field. A closed-filament example satisfying the half-space hypothesis is in
`Sanity/MeridianCoil`.

**The mathematical point.** The simply connected region `U` of the corollaries has to contain
the poloidal loop; it does not have to be the whole region on which the field is a vacuum
field. A poloidal loop of a `FieldTorus` at toroidal angle `φ₀` lies in the open half-space
`meridianHalfSpace φ₀` (`Theory/Fields/FormConvexRegion`), which is convex, hence simply
connected, and does not meet the `z`-axis. The rational stellarator field `field (1/4)` is a
vacuum field off the `z`-axis (a region that is not simply connected), so it is a vacuum field
on every meridian half-space (`rationalStellarator_vacuum_meridian`). Zero poloidal circulation
and a non-zero rotational transform are compatible: the field is `∇φ + ∇(H/16)`, the transform
`ι_A = (75 + √5)/562 > 0` comes from the non-axisymmetric gradient part, and the poloidal loop
bounds a disc in the half-space on which the field is curl-free.

* Convex regions: `hyperbolic_lineIntegral_eq_zero` (all of space, every closed curve that is
  `C¹` on `[a, b]`), `hyperbolic_loopCurrent_ball` (the circular torus section inside the open
  ball of radius `2` about `(3, 0, 0)`).
* `FieldTorus`, `ι = 0` (axisymmetric): the circular tori of `∇φ`, every toroidal angle
  (`toroidal_circ_loopCurrent`).
* `FieldTorus`, `ι = ι_A > 0`: every `ExactTorus` of the rational stellarator field has zero
  loop current at every toroidal angle (`exactTorus_loopCurrent`, by
  `FieldTorus.loopCurrent_eq_zero_of_simplyConnected`), and the de Rham period of `B♭` on the
  class of its poloidal loop in the meridian half-space is zero (`exactTorus_period`, by
  `FieldTorus.loopCurrent_eq_periodHom_div`). Such a torus exists
  (`exists_fieldTorus_loopCurrent_eq_zero`, from the certified KAM torus `torusA_exact`).
* `CurrentFreeTransform`: for every family `S` and all `I_max`, `ι_min` with
  `CurrentFreeTransform μ₀ (field (1/4)) S I_max ι_min`, every surface has zero current
  (`rationalStellarator_current_eq_zero`, by
  `CurrentFreeTransform.current_eq_zero_of_simplyConnected`). The statement is not vacuous:
  `rationalStellarator_fixture` exhibits a family satisfying the clause with `ι_min = ι_A`.
  That fixture is staged: its source instance has `I_max = 0`, the fixture weakens the
  allowance to `1` with `CurrentFreeTransform.mono` and the corollary recovers `0`. It checks
  that the hypotheses of the corollary hold together with `ι ≠ 0`, and that two independent
  proofs of zero current (potential, topology) agree; nothing more.
* Regression (audit AV-M1), a bounded convex region: the poloidal loop of an `ExactTorus` at
  `φ₀ = 0` lies in the open ball of radius `1/2` about `(1, 0, 0)`
  (`exactSurface_loop_mem_ball`), on which the rational stellarator field is a vacuum field
  (`rationalStellarator_vacuum_ball`). The contract-level statement
  `CurrentFreeTransform.imax_zero_of_convex` then applies with that ball
  (`rationalStellarator_imax_zero_ball`, `rationalStellarator_ball_fixture`); the half-space
  is not needed. For the hyperbolic field only the loop-level statement
  `hyperbolic_loopCurrent_ball` is available: it has no invariant tori in the build, so no
  `CurrentFreeTransform` instance.
* Hypothesis check (rejected): the wire field of `Sanity/FormLoopCurrentInterval` has
  circulation `2π` around the circular torus section. Its vacuum region does not contain the
  meridian half-space of `φ₀ = 0` (`not_meridianHalfSpace_subset_ringRegion`: the wire crosses
  it), and no convex open subset of its vacuum region contains the section
  (`ring_no_convex_region`).

**Relation to `Sanity.AuditRefresh.CurrentFreeTransform.circulation_eq_zero`.** That theorem
unpacks the clause: from `CurrentFreeTransform μ₀ B S 0 ιmin` (allowance `I_max = 0`), for an
arbitrary field, it reads off `poloidalCirculation = 0` using `μ₀ > 0`. It has no vacuum or
topological hypothesis and no content beyond the clause. The topological corollary has the same
conclusion from different hypotheses: any allowance `I_max`, but `B` a vacuum field on a simply
connected region containing the loop. Neither statement implies the other. They compose: the
topological corollary shows that for such a field the clause holds with `I_max = 0`
(`CurrentFreeTransform.imax_zero_of_meridianHalfSpace`), which is the hypothesis of the audit
theorem; `circulation_eq_zero_via_audit` is that composition (its statement is that of
`CurrentFreeTransform.poloidalCirculation_eq_zero_of_meridianHalfSpace`, proved there without
the audit theorem), and `circulation_eq_zero_agrees` records that on a C1 family zero
circulation and zero net current are equivalent.

What is not proved: only the one certified torus of the rational stellarator is exhibited as a
family (`rationalStellarator_currentFreeTransform`); the Dommaschk instances of
`CurrentFreeTransform` are in modules outside the default build and are not used here, although
`current_eq_zero_of_meridianHalfSpace` applies to them as well (their field is a vacuum field
off the `z`-axis).
-/

@[expose] public section

namespace PlasmaLean.Sanity.ContractLoopCurrentFixture

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Contract PlasmaLean.Design
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-! ## Convex regions -/

/-- The hyperbolic field is a vacuum field on all of space, as an open region. -/
theorem hyperbolic_vacuum_top :
    VacuumField ((⊤ : Opens Space) : Set Space) (fun y => hyperbolicField y) := by
  simpa using hyperbolic_gradient_vacuum

/-- **Accepted case, all of space**: the hyperbolic vacuum field has zero circulation around
every closed curve that is `C¹` on `[a, b]`. -/
theorem hyperbolic_lineIntegral_eq_zero {γ : ℝ → Space} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) (hclosed : γ a = γ b) :
    lineIntegral (fun y => hyperbolicField y) γ a b = 0 :=
  hyperbolic_vacuum_top.lineIntegral_eq_zero_of_convex (by simpa using convex_univ) hab
    (fun _ _ => Opens.mem_top _) hγ hclosed

/-- The centre `(3, 0, 0)` of the circular torus section at `φ₀ = 0`. -/
noncomputable def sectionCentre : Space := WithLp.toLp 2 ![3, 0, 0]

/-- The circular torus section lies in the open ball of radius `2` about its centre. -/
theorem torus_mem_ball (θ : ℝ) :
    poloidalLoop FormLoopCurrent.torusR FormLoopCurrent.torusZ 0 θ ∈ ballOpens sectionCentre 2 := by
  rw [mem_ballOpens, FormLoopCurrent.torus_poloidalLoop, sectionCentre, EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_three]

/-- The hyperbolic field is a vacuum field on the ball. -/
theorem hyperbolic_vacuum_ball :
    VacuumField (ballOpens sectionCentre 2 : Set Space) (fun y => hyperbolicField y) :=
  ⟨(ballOpens sectionCentre 2).isOpen,
    hyperbolic_gradient_vacuum.contDiffOn.mono (Set.subset_univ _),
    fun x _ => hyperbolic_gradient_vacuum.div_eq_zero x (Set.mem_univ x),
    fun x _ => hyperbolic_gradient_vacuum.curl_eq_zero x (Set.mem_univ x)⟩

/-- **Accepted case, a ball**: the hyperbolic vacuum field has zero loop current through the
circular torus section, which lies in a ball. -/
theorem hyperbolic_loopCurrent_ball (μ₀ : ℝ) :
    loopCurrent μ₀ (fun y => hyperbolicField y) FormLoopCurrent.torusR FormLoopCurrent.torusZ 0
      = 0 :=
  hyperbolic_vacuum_ball.loopCurrent_eq_zero_of_convex μ₀ (convex_ball _ _)
    (fun θ _ => torus_mem_ball θ) FormLoopCurrent.torus_contDiff.contDiffOn
    FormLoopCurrent.torus_closed.symm

/-! ## The off-axis region and the meridian half-spaces -/

/-- Every meridian half-space lies in the vacuum region of the rational stellarator fields,
the complement of the `z`-axis. -/
theorem meridianHalfSpace_subset_domain (φ₀ : ℝ) :
    (meridianHalfSpace φ₀ : Set Space) ⊆ RationalStellarator.domain :=
  fun _ hx => r2_pos_of_mem_meridianHalfSpace hx

/-- The rational stellarator field is a vacuum field on every meridian half-space, a convex
region. -/
theorem rationalStellarator_vacuum_meridian (φ₀ : ℝ) :
    VacuumField (meridianHalfSpace φ₀ : Set Space) (RationalStellarator.field (1 / 4)) :=
  (RationalStellarator.field_vacuum (1 / 4)).restrict_meridianHalfSpace
    (meridianHalfSpace_subset_domain φ₀)

/-! ## `FieldTorus` with `ι = 0`: the circular tori of `∇φ` -/

/-- **Accepted case, `ι = 0` (axisymmetric)**: the circular tori of the vacuum field `∇φ`
(`RationalStellaratorContract.circTorus_iotaOnTorus`, rotation number `0`) carry zero loop
current at every toroidal angle, by `FieldTorus.loopCurrent_eq_zero_of_simplyConnected` in the
meridian half-space. -/
theorem toroidal_circ_loopCurrent {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ RationalStellarator.toroidal (RationalStellaratorContract.circR a)
      (RationalStellaratorContract.circZ a) φ₀ = 0 :=
  have hT := (RationalStellaratorContract.circTorus_iotaOnTorus ha ha1).1
  hT.loopCurrent_eq_zero_of_simplyConnected (U := meridianHalfSpace φ₀) μ₀
    (RationalStellarator.toroidal_vacuum.restrict_meridianHalfSpace
      (meridianHalfSpace_subset_domain φ₀))
    (fun θ _ => poloidalLoop_mem_meridianHalfSpace (hT.R_pos θ φ₀))
    (contDiff_poloidalLoop
      (by unfold RationalStellaratorContract.circR; fun_prop)
      (by unfold RationalStellaratorContract.circZ; fun_prop)).contDiffOn

/-! ## `FieldTorus` with `ι = ι_A > 0`: the exact torus of the rational stellarator -/

section Exact

variable {Rk zk : ℝ → ℝ → ℝ}

/-- The poloidal loop of an `ExactTorus` at `φ₀` lies in the meridian half-space of `φ₀`. -/
theorem exactTorus_mem (hK : KamTorusA.ExactTorus Rk zk) (φ₀ : ℝ) :
    ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop Rk zk φ₀ θ ∈ meridianHalfSpace φ₀ :=
  fun θ _ => poloidalLoop_mem_meridianHalfSpace
    ((RationalStellaratorContract.ExactTorus.fieldTorus hK).R_pos θ φ₀)

/-- The poloidal loops of an `ExactTorus` are `C¹`. -/
theorem exactTorus_contDiff (hK : KamTorusA.ExactTorus Rk zk) (φ₀ : ℝ) :
    ContDiff ℝ 1 (poloidalLoop Rk zk φ₀) :=
  contDiff_poloidalLoop (hK.contDiff_R.comp (contDiff_id.prodMk contDiff_const))
    (hK.contDiff_Z.comp (contDiff_id.prodMk contDiff_const))

/-- **Accepted case, `ι = ι_A ≠ 0`**: an `ExactTorus` of the rational stellarator field is a
`FieldTorus` with rotation number `ι_A = (75 + √5)/562`, and its loop current is zero at every
toroidal angle, by `FieldTorus.loopCurrent_eq_zero_of_simplyConnected` with every hypothesis
discharged (the region is the meridian half-space). -/
theorem exactTorus_loopCurrent (hK : KamTorusA.ExactTorus Rk zk) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ (RationalStellarator.field (1 / 4)) Rk zk φ₀ = 0 :=
  (RationalStellaratorContract.ExactTorus.fieldTorus hK).loopCurrent_eq_zero_of_simplyConnected
    μ₀ (rationalStellarator_vacuum_meridian φ₀) (exactTorus_mem hK φ₀)
    (exactTorus_contDiff hK φ₀).contDiffOn

/-- **Period check**: the de Rham period of `B♭` on the class of the poloidal loop of an
`ExactTorus` in the meridian half-space is `0`, by `FieldTorus.loopCurrent_eq_periodHom_div`
(with `μ₀ = 1`). -/
theorem exactTorus_period (hK : KamTorusA.ExactTorus Rk zk) (φ₀ : ℝ) :
    periodHom (onOpens (meridianHalfSpace φ₀) fun y => flat (RationalStellarator.field (1 / 4) y))
      (intervalCurve (poloidalLoop Rk zk φ₀) neg_pi_lt_pi.le (exactTorus_mem hK φ₀) 0)
      (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le (exactTorus_mem hK φ₀)
        (exactTorus_contDiff hK φ₀).contDiffOn.continuousOn
        ((RationalStellaratorContract.ExactTorus.fieldTorus hK).poloidalLoop_closed φ₀)))))
      = 0 := by
  have h := (RationalStellaratorContract.ExactTorus.fieldTorus hK).loopCurrent_eq_periodHom_div
    (U := meridianHalfSpace φ₀) 1
    ((rationalStellarator_vacuum_meridian φ₀).contDiffOn.of_le (by norm_num))
    (rationalStellarator_vacuum_meridian φ₀).curl_eq_zero (exactTorus_mem hK φ₀)
    (exactTorus_contDiff hK φ₀).contDiffOn
  rw [exactTorus_loopCurrent hK 1 φ₀, div_one] at h
  exact h.symm

end Exact

/-- `ι_A ≠ 0`. -/
theorem iota_ne_zero : KamTorusA.iota ≠ 0 := RationalStellaratorContract.iota_pos.ne'

/-- **The `FieldTorus` fixture exists**: there is an invariant torus of the rational
stellarator vacuum field with rotation number `ι_A ≠ 0` and transform `ι_A` in the sense of the
contract, whose loop current vanishes for every `μ₀` and every toroidal angle. -/
theorem exists_fieldTorus_loopCurrent_eq_zero :
    ∃ R z : ℝ → ℝ → ℝ, FieldTorus (RationalStellarator.field (1 / 4)) R z KamTorusA.iota ∧
      IotaOnTorus (RationalStellarator.field (1 / 4)) R z KamTorusA.iota ∧
      ∀ μ₀ φ₀, loopCurrent μ₀ (RationalStellarator.field (1 / 4)) R z φ₀ = 0 := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := KamNewton.torusA_exact
  have hK := KamNewton.exactTorus hu hz hur hzr hR hZ hC
  exact ⟨_, _, RationalStellaratorContract.ExactTorus.fieldTorus hK,
    RationalStellaratorContract.ExactTorus.iotaOnTorus hK, exactTorus_loopCurrent hK⟩

/-! ## `CurrentFreeTransform` -/

section C1

variable {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData}

/-- **Clause C1 for the rational stellarator field: zero current on every surface.** For every
family `S` and all `I_max`, `ι_min` such that the clause holds, each surface has zero net
current. This is `CurrentFreeTransform.current_eq_zero_of_simplyConnected` with the region the
meridian half-space of the surface. -/
theorem rationalStellarator_current_eq_zero
    (hC : CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S Imax ιmin)
    {s : SurfaceData} (hs : s ∈ S) : s.current μ₀ (RationalStellarator.field (1 / 4)) = 0 :=
  hC.current_eq_zero_of_simplyConnected (rationalStellarator_vacuum_meridian s.φ₀) hs
    fun θ _ => poloidalLoop_mem_meridianHalfSpace ((hC.torus s hs).1.R_pos θ s.φ₀)

/-- The original loop-current fixture with embeddedness on the same family. -/
theorem rationalStellarator_embedded_fixture (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      EmbeddedCurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 1 KamTorusA.iota ∧
      0 < KamTorusA.iota ∧
      ∀ s ∈ S, KamTorusA.iota ≤ |s.iota| ∧
        s.current μ₀ (RationalStellarator.field (1 / 4)) = 0 := by
  obtain ⟨S, hS⟩ := RationalStellaratorContract.rationalStellarator_embeddedCurrentFreeTransform hμ
  have hS1 := hS.mono zero_le_one le_rfl RationalStellaratorContract.iota_pos
  exact ⟨S, hS1, RationalStellaratorContract.iota_pos, fun s hs =>
    ⟨hS1.iota_ge s hs, rationalStellarator_current_eq_zero hS1.toCurrentFreeTransform hs⟩⟩

/-- **The `CurrentFreeTransform` fixture: a satisfiability and consistency check.** For every
`μ₀ > 0` there is a family of surfaces on which the rational stellarator field satisfies clause
C1 with the allowance `I_max = 1` and `ι_min = ι_A > 0`; on every surface of the family the
transform is at least `ι_A` in absolute value and the net current is `0` by the topological
corollary. So the hypotheses of `CurrentFreeTransform.current_eq_zero_of_simplyConnected` hold
together for a field with non-zero rotational transform.

The fixture is staged (audit AV-M2): the source instance
`rationalStellarator_currentFreeTransform` is already proved with `I_max = 0`, from the
potential of the field; the proof here forgets that with `CurrentFreeTransform.mono` and the
corollary recovers it. What is checked is that the hypotheses are jointly satisfiable with
`ι ≠ 0` and that two independent proofs of zero current agree. It is not evidence that the
corollary improves an allowance: no instance exists whose current bound was proved by an
estimate. -/
theorem rationalStellarator_fixture (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 1 KamTorusA.iota ∧
      0 < KamTorusA.iota ∧
      ∀ s ∈ S, KamTorusA.iota ≤ |s.iota| ∧
        s.current μ₀ (RationalStellarator.field (1 / 4)) = 0 := by
  obtain ⟨S, hS, hι, hcurrent⟩ := rationalStellarator_embedded_fixture hμ
  exact ⟨S, hS.toCurrentFreeTransform, hι, hcurrent⟩

/-! ## Comparison with the audit theorem -/

variable {Ω : Set Space} {B : Space → Space}

/-- **Composition with the audit theorem (a consistency check).** For a vacuum field on a
region containing the meridian half-spaces of the surfaces, the clause with any allowance
`I_max` gives the clause with `I_max = 0` (Stokes on the poloidal cross-section), and
`AuditRefresh.CurrentFreeTransform.circulation_eq_zero` then gives zero poloidal circulation.
The statement is that of `CurrentFreeTransform.poloidalCirculation_eq_zero_of_meridianHalfSpace`
and adds nothing to it; the clause `hC` is assumed, and no instance in the build has an
allowance that this improves (audit AV-M2). -/
theorem circulation_eq_zero_via_audit (hC : CurrentFreeTransform μ₀ B S Imax ιmin)
    (h : VacuumField Ω B) (hΩ : ∀ s ∈ S, (meridianHalfSpace s.φ₀ : Set Space) ⊆ Ω)
    {s : SurfaceData} (hs : s ∈ S) : poloidalCirculation B s.R s.z s.φ₀ = 0 :=
  AuditRefresh.CurrentFreeTransform.circulation_eq_zero (hC.imax_zero_of_meridianHalfSpace h hΩ)
    hs

/-- **The two routes agree.** Zero circulation on a surface of a C1 family is equivalent to
zero net current (the audit theorem's unpacking, valid for any field since `μ₀ > 0`); so the
conclusion of the topological corollary and that of the audit theorem are the same statement. -/
theorem circulation_eq_zero_agrees (hC : CurrentFreeTransform μ₀ B S Imax ιmin)
    (s : SurfaceData) : poloidalCirculation B s.R s.z s.φ₀ = 0 ↔ s.current μ₀ B = 0 := by
  rw [SurfaceData.current, loopCurrent, div_eq_zero_iff]
  exact ⟨Or.inl, fun h => h.resolve_right hC.mu0_pos.ne'⟩

/-- For the rational stellarator field, through the audit theorem: zero poloidal circulation on
every surface of every C1 family, whatever the allowance. A consistency check (audit AV-M2):
the only such family in the build, `rationalStellarator_currentFreeTransform`, already has
`I_max = 0`, proved from the potential of the field, so this is a second proof of a known
value and not an improved allowance. -/
theorem rationalStellarator_circulation_eq_zero
    (hC : CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S Imax ιmin)
    {s : SurfaceData} (hs : s ∈ S) :
    poloidalCirculation (RationalStellarator.field (1 / 4)) s.R s.z s.φ₀ = 0 :=
  circulation_eq_zero_via_audit hC (RationalStellarator.field_vacuum (1 / 4))
    (fun s _ => meridianHalfSpace_subset_domain s.φ₀) hs

/-! ## A bounded convex region (audit AV-M1) -/

/-- The point `(1, 0, 0)`, near the centre of the cross-section of torus A at `φ₀ = 0`. -/
noncomputable def stellCentre : Space := WithLp.toLp 2 ![1, 0, 0]

/-- The open ball of radius `1/2` about `(1, 0, 0)` does not meet the `z`-axis. -/
theorem stellBall_subset_domain :
    (ballOpens stellCentre (1 / 2) : Set Space) ⊆ RationalStellarator.domain := by
  intro x hx
  have hd : dist x stellCentre < 1 / 2 := hx
  have h0 : |x 0 - 1| < 1 / 2 := by
    have h := (PiLp.norm_apply_le (x - stellCentre) 0).trans_lt (by rwa [← dist_eq_norm])
    simpa [stellCentre] using h
  have hpos : 0 < x 0 := by linarith [(abs_lt.1 h0).1]
  change 0 < RationalStellarator.r2 x
  unfold RationalStellarator.r2
  positivity

/-- The rational stellarator field is a vacuum field on the ball, a bounded convex region. -/
theorem rationalStellarator_vacuum_ball :
    VacuumField (ballOpens stellCentre (1 / 2) : Set Space) (RationalStellarator.field (1 / 4)) :=
  have h := RationalStellarator.field_vacuum (1 / 4)
  ⟨(ballOpens stellCentre (1 / 2)).isOpen, h.contDiffOn.mono stellBall_subset_domain,
    fun x hx => h.div_eq_zero x (stellBall_subset_domain hx),
    fun x hx => h.curl_eq_zero x (stellBall_subset_domain hx)⟩

/-- The poloidal loop at `φ₀ = 0` of an `ExactTorus` lies in the ball: `(R - 1)² + z² < 1/4`. -/
theorem exactSurface_loop_mem_ball {Rk zk : ℝ → ℝ → ℝ} (hK : KamTorusA.ExactTorus Rk zk)
    (θ : ℝ) :
    (RationalStellaratorContract.exactSurface Rk zk).loop θ ∈ ballOpens stellCentre (1 / 2) := by
  have hb := (hK.rt2_bounds θ 0).2
  have hlt : Real.sqrt ((Rk θ 0 - 1) ^ 2 + zk θ 0 ^ 2) < 1 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  rw [mem_ballOpens, EuclideanSpace.dist_eq]
  convert hlt using 2
  simp [SurfaceData.loop, RationalStellaratorContract.exactSurface, poloidalLoop, cylPoint,
    stellCentre, Fin.sum_univ_three, Real.dist_eq]

/-- **Regression (audit AV-M1): the half-space is not needed.** For every family of surfaces on
which the rational stellarator field satisfies clause C1 with some allowance `I_max`, and whose
poloidal loops lie in the bounded ball of radius `1/2` about `(1, 0, 0)`, the clause holds
with `I_max = 0`, by `CurrentFreeTransform.imax_zero_of_convex` with that ball. The vacuum
hypothesis is used only on the ball, a convex neighbourhood of the poloidal cross-section;
nothing is assumed about the field elsewhere in the meridian half-space. The clause `hC` is
assumed: only the allowance improves. -/
theorem rationalStellarator_imax_zero_ball
    (hC : CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S Imax ιmin)
    (hS : ∀ s ∈ S, ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, s.loop θ ∈ ballOpens stellCentre (1 / 2)) :
    CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 0 ιmin :=
  hC.imax_zero_of_convex fun s hs =>
    ⟨ballOpens stellCentre (1 / 2), convex_ball _ _, rationalStellarator_vacuum_ball, hS s hs⟩

/-- Embedded C1 at both current allowances on the exact surface used by the bounded-ball
loop-current fixture. The proof of the sharper allowance uses the convex vacuum region. -/
theorem rationalStellarator_embedded_ball_fixture (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      EmbeddedCurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 1 KamTorusA.iota ∧
      (∀ s ∈ S, ∀ θ, s.loop θ ∈ ballOpens stellCentre (1 / 2)) ∧
      EmbeddedCurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 0 KamTorusA.iota ∧
      ∀ s ∈ S, s.current μ₀ (RationalStellarator.field (1 / 4)) = 0 := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := KamNewton.torusA_exact
  have hK := KamNewton.exactTorus hu hz hur hzr hR hZ hC
  have h0 := RationalStellaratorContract.ExactTorus.embeddedCurrentFreeTransform hK hμ
  have h1 := h0.mono zero_le_one le_rfl RationalStellaratorContract.iota_pos
  let surf := RationalStellaratorContract.exactSurface (KamNewton.Rof u) (KamNewton.Zof z)
  have hball : ∀ s ∈ ({surf} : Set SurfaceData), ∀ θ : ℝ,
      s.loop θ ∈ ballOpens stellCentre (1 / 2) := by
    rintro s rfl θ
    exact exactSurface_loop_mem_ball hK θ
  refine ⟨_, h1, hball, ⟨rationalStellarator_imax_zero_ball h1.toCurrentFreeTransform
    (fun s hs θ _ => hball s hs θ), h1.embedded⟩, ?_⟩
  intro s hs
  exact h1.toCurrentFreeTransform.current_eq_zero_of_convex (convex_ball _ _)
    rationalStellarator_vacuum_ball hs
    (fun θ _ => hball s hs θ)

/-- **Regression (audit AV-M1): the bounded-region statement is instantiated.** For every
`μ₀ > 0` there is a family of surfaces (the certified exact torus near torus A, with its
poloidal loop at `φ₀ = 0`) satisfying clause C1 for the rational stellarator field with
allowance `I_max = 1` and `ι_min = ι_A`, whose poloidal loops lie in the ball of radius `1/2`
about `(1, 0, 0)`; `rationalStellarator_imax_zero_ball` gives the clause with `I_max = 0` and
`CurrentFreeTransform.current_eq_zero_of_convex` gives zero current on each surface.

The family consists of the same embedded KAM witness as the stronger bounded-ball fixture.
Its clause is proved with `I_max = 0` from the potential of the field, and the
allowance `1` is obtained by `CurrentFreeTransform.mono`; so, as for
`rationalStellarator_fixture`, this is a satisfiability and consistency check of the hypotheses
of the convex-region corollary, not an improved estimate. The field is an idealised one
(singular only on the `z`-axis); no coil-generated field is instantiated. -/
theorem rationalStellarator_ball_fixture (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 1 KamTorusA.iota ∧
      (∀ s ∈ S, ∀ θ, s.loop θ ∈ ballOpens stellCentre (1 / 2)) ∧
      CurrentFreeTransform μ₀ (RationalStellarator.field (1 / 4)) S 0 KamTorusA.iota ∧
      ∀ s ∈ S, s.current μ₀ (RationalStellarator.field (1 / 4)) = 0 := by
  obtain ⟨S, h1, hball, h0, hcurrent⟩ := rationalStellarator_embedded_ball_fixture hμ
  exact ⟨S, h1.toCurrentFreeTransform, hball, h0.toCurrentFreeTransform, hcurrent⟩

end C1

/-! ## Rejected: the wire through the section -/

open FormLoopCurrentInterval in
/-- **Hypothesis check**: the vacuum region of the wire field does not contain the meridian
half-space of `φ₀ = 0`; the wire passes through `(3, 0, 0)`. -/
theorem not_meridianHalfSpace_subset_ringRegion :
    ¬ (meridianHalfSpace 0 : Set Space) ⊆ ringRegion := by
  intro h
  have hmem : sectionCentre ∈ (meridianHalfSpace 0 : Set Space) := by
    change sectionCentre ∈ meridianHalfSpace 0
    rw [mem_meridianHalfSpace]
    simp [sectionCentre]
  have h0 : 0 < ringR2 sectionCentre := h hmem
  simp [ringR2, sectionCentre] at h0

open FormLoopCurrentInterval in
/-- **Rejected case**: no convex open subset of the vacuum region of the wire field contains
the circular torus section; otherwise the circulation `2π` around it would vanish. -/
theorem ring_no_convex_region (U : Opens Space) (hc : Convex ℝ (U : Set Space))
    (hsub : (U : Set Space) ⊆ ringRegion) :
    ¬ ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      poloidalLoop FormLoopCurrent.torusR FormLoopCurrent.torusZ 0 θ ∈ U := fun hU =>
  have hV : VacuumField (U : Set Space) ringField :=
    ⟨U.isOpen, ringField_vacuum.contDiffOn.mono hsub,
      fun x hx => ringField_vacuum.div_eq_zero x (hsub hx),
      fun x hx => ringField_vacuum.curl_eq_zero x (hsub hx)⟩
  ring_poloidalCirculation_ne_zero
    (hV.poloidalCirculation_eq_zero_of_convex hc hU FormLoopCurrent.torus_contDiff.contDiffOn
      FormLoopCurrent.torus_closed.symm)

end PlasmaLean.Sanity.ContractLoopCurrentFixture
