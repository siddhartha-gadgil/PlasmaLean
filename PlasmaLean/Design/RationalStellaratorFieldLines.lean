/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorConfinedForever
public import PlasmaLean.Theory.Fields.FieldLineExistence

/-!
# Field lines of the rational stellarator exist, are unique, and are confined forever

`RationalStellarator.rationalStellarator_confined_forever` says that every two-sided field line of
`field (1/4)` starting inside the exact KAM torus stays inside forever, but it does not say that
such field lines exist. Here we prove that they do: **from every point on the exact magnetic axis
or inside the torus there is exactly one two-sided field line, defined for all time, and it stays
inside the torus forever** (`rationalStellarator_confined_forever_exists`).

Proof outline.
1. *Grönwall collar bound* (`KamTorusA.ExactTorus.exists_gronwall`): for the profile `ρ` of an
   exact torus near torus A, `|DG · B| ≤ L |G|` on the collar `|G| < 1/100`, `G = rt − ρ(θs, φs)`
   (the estimate of `rationalStellarator_confined_forever_of_exact`, stated separately).
2. *A priori confinement of local solutions* (`Fields.torus_trapping_Icc`): solutions on any
   closed interval `[a, b] ∋ 0` starting inside the torus stay inside.
3. The inside lies in the compact set `{rt ≤ 0.19}` (`isCompact_rtLe`), which lies in the
   domain `{r₂ > 0}` where the field is `C²` (`field_contDiffOn`).
4. The generic theorem `Fields.ODEGlobal.existsUnique_global` (uniform Picard–Lindelöf time on a
   compact set, continuation by gluing, Grönwall uniqueness) gives global existence and
   uniqueness.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Real Set Filter Topology PlasmaLean.Fields PlasmaLean.Design.RationalStellarator

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- **Grönwall bound on the collar** for the profile of an exact torus near torus A: with
`G = rt − ρ(θs, φs)`, `|DG · B| ≤ L |G|` wherever `0 < rt < 1/2` and `|G| < 1/100`. -/
theorem exists_gronwall : ∃ L : ℝ, ∀ y : Space, rt y < 1 / 2 → 0 < rt y →
    |rt y - hK.profile (θs y) (φs y)| < 1 / 100 →
    |fderiv ℝ (fun x => rt x - hK.profile (θs x) (φs x)) y (field (1 / 4) y)| ≤
      L * |rt y - hK.profile (θs y) (φs y)| := by
  obtain ⟨Cρ, hCρ⟩ := hK.exists_bound_fderiv_profile
  obtain ⟨L, hL⟩ := exists_lipschitz_W Cρ
  have hρ := hK.torusProfile
  refine ⟨L, fun y hy hpos hG => ?_⟩
  have hyeq : y = torPt (rt y) (θs y) (φs y) := eq_torPt hy
  obtain ⟨hr0l, hr0u⟩ := hK.profile_bounds (θs y) (φs y)
  have hrr := abs_lt.mp hG
  -- `DG · B` at `y` and on the torus, in toroidal coordinates
  have hF := fderiv_G_field_torPt hρ hpos hy (θs y) (φs y)
  rw [← hyeq] at hF
  rw [hF]
  have htan := hK.tangent (θs y) (φs y)
  set D := fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (θs y, φs y) with hDdef
  have hlin : ∀ x x' : ℝ, D (x, x') = x * D (1, 0) + x' * D (0, 1) := fun x x' => by
    rw [show ((x, x') : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + x' • ((0 : ℝ), (1 : ℝ)) by simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hb1 : |D (1, 0)| ≤ Cρ := by
    have := D.le_opNorm (1, 0)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  have hb2 : |D (0, 1)| ≤ Cρ := by
    have := D.le_opNorm (0, 1)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  set r₀ := hK.profile (θs y) (φs y)
  set q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ := (rt y, cos (θs y), sin (θs y), cos (2 * φs y),
    sin (2 * φs y), D (1, 0), D (0, 1))
  set q₀ : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ := (r₀, cos (θs y), sin (θs y), cos (2 * φs y),
    sin (2 * φs y), D (1, 0), D (0, 1))
  have hWq : vRad (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y)) -
      D (vPol (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y)),
        vTor (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y))) = Wfun q := by
    rw [hlin]; simp only [Wfun, q]; ring
  have hWq₀ : Wfun q₀ = 0 := by
    simp only [Wfun, q₀]; rw [htan, hlin]; ring
  have hmem : ∀ x : ℝ, 1 / 20 ≤ x → x ≤ 1 / 4 → (x, cos (θs y), sin (θs y), cos (2 * φs y),
      sin (2 * φs y), D (1, 0), D (0, 1)) ∈ Wbox Cρ := fun x h1 h2 =>
    ⟨⟨h1, h2⟩, ⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_sin _, sin_le_one _⟩,
      ⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_sin _, sin_le_one _⟩, abs_le.mp hb1,
      abs_le.mp hb2⟩
  have hq : q ∈ Wbox Cρ := hmem _ (by linarith) (by linarith)
  have hq₀ : q₀ ∈ Wbox Cρ := hmem _ (by linarith) (by linarith)
  rw [hWq, ← sub_zero (Wfun q), ← hWq₀]
  exact hL q q₀ hq hq₀ rfl

end ExactTorus

end PlasmaLean.Design.KamTorusA

namespace PlasmaLean.Design.RationalStellarator

open Real Set Filter Topology PlasmaLean.Fields PlasmaLean.Design.KamTorusA
  PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM

/-- The closed tube `{rt ≤ 19/100}` about the exact magnetic axis is compact. -/
theorem isCompact_rtLe : IsCompact {x : Space | rt x ≤ 19 / 100} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_rt continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := 2)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy' : rt y ≤ 19 / 100 := hy
  have hn : ‖y‖ ^ 2 = r2 y + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; rfl
  have hr2 : 0 ≤ r2 y := by unfold r2; positivity
  have hRc : Rc y ^ 2 = r2 y := Real.sq_sqrt hr2
  have hRc0 : 0 ≤ Rc y := Real.sqrt_nonneg _
  have hsq := rt_sq y
  have h0 := rt_nonneg y
  have hrt2 : rt y ^ 2 ≤ (19 / 100) ^ 2 := by nlinarith
  have hz : y 2 ^ 2 ≤ (19 / 100) ^ 2 := by nlinarith [sq_nonneg (Rc y - 1)]
  have hR1 : (Rc y - 1) ^ 2 ≤ (19 / 100) ^ 2 := by nlinarith [sq_nonneg (y 2)]
  have hR2 : Rc y ≤ 119 / 100 := by nlinarith
  have hN : ‖y‖ ^ 2 ≤ 2 ^ 2 := by rw [hn, ← hRc]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg y) (by norm_num) two_ne_zero).mp hN

/-- The closed tube `{rt ≤ 19/100}` lies in the current-free domain `{r₂ > 0}`. -/
theorem rtLe_subset_domain : {x : Space | rt x ≤ 19 / 100} ⊆ domain := fun x hx =>
  r2_pos_of_rt_lt (show rt x < 1 / 2 by have : rt x ≤ 19 / 100 := hx; linarith)

/-- **Existence, uniqueness and confinement of the field lines from an exact torus.** If
`(Rk, zk)` is an exact invariant torus near torus A, then from every point on the exact axis or
inside the torus `rt < ρ(θs, φs)` (`ρ` its profile) there is exactly one two-sided field line of
`field (1/4)` through it at parameter `0`, and every such field line stays inside the torus, within
distance `0.19` of the axis, for all time. -/
theorem fieldLines_existsUnique_of_exact {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
    (x₀ : Space) (hx₀ : rt x₀ = 0 ∨ rt x₀ < hK.profile (θs x₀) (φs x₀)) :
    (∃! γ : ℝ → Space, IsFieldLine (field (1 / 4)) γ ∧ γ 0 = x₀) ∧
      ∀ γ : ℝ → Space, IsFieldLine (field (1 / 4)) γ → γ 0 = x₀ → ∀ t,
        rt (γ t) ≤ 19 / 100 ∧
          (rt (γ t) = 0 ∨ rt (γ t) < hK.profile (θs (γ t)) (φs (γ t))) := by
  obtain ⟨L, hL⟩ := hK.exists_gronwall
  have hρ := hK.torusProfile
  have hlo : ∀ a b, 77 / 1000 ≤ hK.profile a b := fun a b => (hK.profile_bounds a b).1
  have hhi : ∀ a b, hK.profile a b ≤ 19 / 100 := fun a b => (hK.profile_bounds a b).2
  have hinv : ODEGlobal.LocallyInvariant (field (1 / 4)) (tube.inside hK.profile) :=
    fun a b α ha hb h0 hα => torus_trapping_Icc (c := tube) (B := field (1 / 4)) hρ
      (ρmin := 77 / 1000) (R₁ := 19 / 100) (g₀ := 1 / 100) (L := L) (by norm_num) hlo hhi
      (isClosed_subTube (by norm_num)) (by norm_num) (fun x hx hr hG => hL x hx hr hG)
      ha hb hα h0
  have hΩK : tube.inside hK.profile ⊆ {x : Space | rt x ≤ 19 / 100} := fun x hx =>
    (TubeCoords.inside_subset_closedTube (by norm_num) hhi hx).2
  have hin0 : x₀ ∈ tube.inside hK.profile := by
    rcases hx₀ with h | h
    · exact ⟨show rt x₀ < 1 / 2 by linarith, Or.inl h.le⟩
    · exact ⟨show rt x₀ < 1 / 2 by linarith [hhi (θs x₀) (φs x₀)], Or.inr h⟩
  obtain ⟨⟨γ, ⟨hγ0, hγ⟩, huniq⟩, hstay⟩ := ODEGlobal.existsUnique_global isOpen_domain
    ((field_contDiffOn (1 / 4)).of_le (by norm_num)) isCompact_rtLe rtLe_subset_domain hΩK hinv
    hin0
  refine ⟨⟨γ, ⟨hγ, hγ0⟩, fun γ' ⟨h', h0'⟩ => huniq γ' ⟨h0', h'⟩⟩, fun γ' h' h0' t => ?_⟩
  have ht := hstay γ' h0' h' t
  refine ⟨hΩK ht, ?_⟩
  rcases ht.2 with h | h
  · exact Or.inl (le_antisymm h (rt_nonneg _))
  · exact Or.inr h

/-- **All-time confinement in the rational stellarator, non-vacuously.** There is a torus profile
`ρ` with `0.077 ≤ ρ ≤ 0.19` (the exact KAM torus of rotational transform `(75 + √5)/562` near
torus A) such that

* from every point `x₀` on the exact magnetic axis or strictly inside the torus
  `rt < ρ(θs, φs)` there is **exactly one** two-sided field line `γ : ℝ → Space` of
  `field (1/4)` with `γ 0 = x₀` (it exists for all time); and
* every two-sided field line starting on the axis or inside the torus stays inside it — in
  particular within distance `0.19` of the axis — for all time, forward and backward.

So the confinement statement of `rationalStellarator_confined_forever` applies to an actual field
line through every starting point of the region. -/
theorem rationalStellarator_confined_forever_exists :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 77 / 1000 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 19 / 100) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (field (1 / 4)) γ ∧ γ 0 = x₀) ∧
      ∀ {γ : ℝ → Space}, IsFieldLine (field (1 / 4)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 19 / 100 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := torusA_exact
  have hK := exactTorus hu hz hur hzr hR hZ hC
  refine ⟨hK.profile, hK.torusProfile, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, fun x₀ hx₀ => (fieldLines_existsUnique_of_exact hK x₀
    hx₀).1, fun {γ} hγ h0 => (fieldLines_existsUnique_of_exact hK (γ 0) h0).2 γ hγ rfl⟩

/-- **Every starting point in the region has a confined field line.** For the profile `ρ` of
`rationalStellarator_confined_forever_exists`, every point `x₀` on the axis or inside the torus
lies on a two-sided field line `γ` of `field (1/4)` (`γ 0 = x₀`) which stays inside the torus, and
within distance `0.19` of the axis, for all time. -/
theorem rationalStellarator_confined_fieldLine_through :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 77 / 1000 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 19 / 100) ∧
      ∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃ γ : ℝ → Space, IsFieldLine (field (1 / 4)) γ ∧ γ 0 = x₀ ∧
          ∀ t, rt (γ t) ≤ 19 / 100 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  obtain ⟨ρ, hρ, hlo, hhi, hex, hconf⟩ := rationalStellarator_confined_forever_exists
  refine ⟨ρ, hρ, hlo, hhi, fun x₀ hx₀ => ?_⟩
  obtain ⟨γ, ⟨hγ, hγ0⟩, -⟩ := hex x₀ hx₀
  exact ⟨γ, hγ, hγ0, hconf hγ (hγ0 ▸ hx₀)⟩

/-- Sanity check: the exact magnetic axis is the unique field line through `axis 0`. -/
theorem axis_unique_fieldLine :
    ∀ γ : ℝ → Space, IsFieldLine (field (1 / 4)) γ → γ 0 = axis 0 → γ = axis := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := torusA_exact
  have hK := exactTorus hu hz hur hzr hR hZ hC
  obtain ⟨⟨γ₀, -, huniq⟩, -⟩ := fieldLines_existsUnique_of_exact hK (axis 0)
    (Or.inl (axis_inside 0))
  intro γ hγ h0
  rw [huniq γ ⟨hγ, h0⟩, huniq axis ⟨axis_isFieldLine _, rfl⟩]

end PlasmaLean.Design.RationalStellarator
