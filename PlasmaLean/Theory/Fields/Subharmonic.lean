/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Subharmonicity of `|B|²` and the weak maximum principle

Theory layer above `Kernel/Vacuum` (track T1, Milestone A).

Main results.
* `laplacian_eq_sum_fderiv_fderiv`, `laplacian_eq_sum_partials`: Mathlib's
  `InnerProductSpace.laplacian` on `Euclid3` is the coordinate Laplacian
  `∑ⱼ ∂ⱼ∂ⱼ u`.
* `deriv_deriv_nonpos_of_isLocalMax`, `laplacian_nonpos_of_isLocalMax`: the
  second-derivative test at an interior maximum.
* `weak_maximum_principle`, `exists_frontier_isMaxOn`: for `u ∈ C²(Ω)`,
  continuous on `closure Ω`, `Δu ≥ 0` on a bounded open `Ω ⊆ ℝ³`, the maximum
  over `closure Ω` is attained on (bounded by its values on) the frontier.
* `laplacian_normSqField` (**Bochner identity**): for a vacuum field,
  `Δ|B|² = 2 ∑ᵢⱼ (∂ⱼ Bᵢ)² ≥ 0`.
* Corollaries: `VacuumField.normSq_le_of_frontier`, `VacuumField.norm_le_of_frontier`
  (boundary-to-interior bound), `VacuumField.error_le_of_frontier` (the error
  between two vacuum fields in the volume is bounded by the error on the
  surface), `VacuumField.not_strict_local_max_norm` (no strict interior local
  maximum of `|B|`).
* Correct direction of the obstruction: subharmonicity forbids interior MAXIMA of
  `|B|`, not minima. `hyperbolicField_strict_min` exhibits a vacuum field
  `B = (x, y, -2z)` whose `|B|² = x² + y² + 4z²` has a strict interior minimum.

Setting. Everything is on `Euclid3 = EuclideanSpace ℝ (Fin 3)` with the
Euclidean norm; `|B|²` is the sum of squares of Cartesian components, which
equals `‖B‖²` there (`normSqField_eq_norm_sq`). Boundedness, openness and
closures do not depend on the choice of norm on ℝ³, so the hypotheses transfer
verbatim to the sup-norm model `Vec3`.

Not covered: the strong maximum principle (constancy when an interior maximum is
attained), unbounded regions, and regularity of the coil fields up to the
boundary (supplied as hypotheses).
-/

open scoped InnerProductSpace RealInnerProductSpace Topology Laplacian
open Filter Set InnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Vacuum

/-! ### Second-derivative test at an interior maximum -/

/-- One-dimensional second-derivative test, necessary form: if `f` has a local
maximum at `a` and is continuous there, then `f''(a) ≤ 0`. No differentiability
is assumed (`deriv` is `0` where the derivative does not exist). -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMax f a)
    (hc : ContinuousAt f a) : deriv (deriv f) a ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hmin := isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hc
  have hconst : f =ᶠ[𝓝 a] fun _ => f a :=
    (h.and hmin).mono fun x hx => le_antisymm hx.1 hx.2
  have hd : deriv f =ᶠ[𝓝 a] fun _ => 0 :=
    hconst.eventuallyEq_nhds.mono fun x hx => by rw [hx.deriv_eq]; simp
  rw [hd.deriv_eq] at hpos
  simp at hpos

/-- Second directional derivative as an iterated derivative of a directional
derivative: `D²f(x)(v, w) = D(y ↦ Df(y) w)(x) v`. -/
theorem fderiv_fderiv_apply_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euclid3 → F} {x : Euclid3} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : Euclid3) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-- At an interior local maximum of a `C²` function, every second directional
derivative `D²u(x)(v, v)` is nonpositive. -/
theorem fderiv_fderiv_self_nonpos_of_isLocalMax {u : Euclid3 → ℝ} {x : Euclid3}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) (v : Euclid3) :
    fderiv ℝ (fderiv ℝ u) x v v ≤ 0 := by
  set γ : ℝ → Euclid3 := fun t => x + t • v with hγ
  have hγc : Continuous γ := by fun_prop
  have hγ0 : γ 0 = x := by simp [hγ]
  have hγd : ∀ t, HasDerivAt γ v t := fun t => by
    have := ((hasDerivAt_id t).smul_const v).const_add x
    simpa only [id, one_smul] using this
  have hdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hdiff' : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ u (γ t) := by
    have := hγc.continuousAt (x := 0)
    rw [ContinuousAt, hγ0] at this
    exact this.eventually hdiff
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hderiv : deriv (u ∘ γ) =ᶠ[𝓝 0] fun t => fderiv ℝ u (γ t) v :=
    hdiff'.mono fun t ht => ((ht.hasFDerivAt.comp_hasDerivAt t (hγd t))).deriv
  have h2 : HasDerivAt (fun t => fderiv ℝ u (γ t) v) (fderiv ℝ (fderiv ℝ u) x v v) 0 := by
    have hc : HasDerivAt (fun t => fderiv ℝ u (γ t)) (fderiv ℝ (fderiv ℝ u) x v) 0 := by
      have hD' : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) (γ 0) := by
        rw [hγ0]; exact hD.hasFDerivAt
      exact hD'.comp_hasDerivAt 0 (hγd 0)
    simpa using hc.clm_apply (hasDerivAt_const 0 v)
  have hmax' : IsLocalMax (u ∘ γ) 0 := by
    apply IsLocalMax.comp_continuous (by rw [hγ0]; exact hmax) hγc.continuousAt
  have hcont : ContinuousAt (u ∘ γ) 0 :=
    ContinuousAt.comp (by rw [hγ0]; exact hu.continuousAt) hγc.continuousAt
  have := deriv_deriv_nonpos_of_isLocalMax hmax' hcont
  rwa [hderiv.deriv_eq, h2.deriv] at this


/-! ### The Laplacian in Cartesian coordinates -/

/-- Mathlib's Laplacian on `Euclid3` is the sum of the three Cartesian second
derivatives `D²u(x)(eⱼ, eⱼ)` (no regularity hypothesis is needed). -/
theorem laplacian_eq_sum_fderiv_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Euclid3 → F) (x : Euclid3) :
    Δ u x = ∑ j : Fin 3, fderiv ℝ (fderiv ℝ u) x (coordVec j) (coordVec j) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]

/-- Coordinate Laplacian: for `u` twice differentiable at `x`,
`Δu(x) = ∑ⱼ ∂ⱼ(∂ⱼ u)(x)`, the sum of iterated Cartesian partial derivatives. -/
theorem laplacian_eq_sum_partials {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : Euclid3 → F} {x : Euclid3} (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    Δ u x = ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ u y (coordVec j)) x (coordVec j) := by
  simp only [laplacian_eq_sum_fderiv_fderiv, fderiv_fderiv_apply_eq hu]

/-- At an interior local maximum of a `C²` function, `Δu ≤ 0`. -/
theorem laplacian_nonpos_of_isLocalMax {u : Euclid3 → ℝ} {x : Euclid3}
    (hu : ContDiffAt ℝ 2 u x) (hmax : IsLocalMax u x) : Δ u x ≤ 0 := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_nonpos fun j _ => fderiv_fderiv_self_nonpos_of_isLocalMax hu hmax _

/-- The second derivative of `|x|²` is `2⟪·,·⟫` everywhere. -/
theorem fderiv_fderiv_normSq (x : Euclid3) :
    fderiv ℝ (fderiv ℝ fun y : Euclid3 => ‖y‖ ^ 2) x = 2 • innerSL ℝ := by
  have h : (fderiv ℝ fun y : Euclid3 => ‖y‖ ^ 2) = fun y => 2 • innerSL ℝ y :=
    funext fun y => (hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv
  rw [h]
  exact ((innerSL ℝ : Euclid3 →L[ℝ] Euclid3 →L[ℝ] ℝ).hasFDerivAt.const_smul (2 : ℕ)).fderiv

/-- `Δ|x|² = 6` in ℝ³. -/
theorem laplacian_normSq (x : Euclid3) : Δ (fun y : Euclid3 => ‖y‖ ^ 2) x = 6 := by
  rw [laplacian_eq_sum_fderiv_fderiv, fderiv_fderiv_normSq]
  have h1 : ∀ j : Fin 3, innerSL ℝ (coordVec j) (coordVec j) = 1 := fun j => by
    rw [innerSL_apply_apply]
    simp
  simp [h1]
  norm_num


/-! ### The weak maximum principle -/

/-- **Weak maximum principle** for subharmonic functions in ℝ³. Let `Ω` be a
bounded open set, `u` of class `C²` on `Ω` and continuous on `closure Ω`, with
`Δu ≥ 0` on `Ω`. If `u ≤ M` on the frontier of `Ω`, then `u ≤ M` on all of
`closure Ω`.

Proof: for `ε > 0` the function `v = u + ε|x|²` has `Δv ≥ 6ε > 0` on `Ω`, so its
maximum over the compact set `closure Ω` cannot be attained in `Ω`
(`laplacian_nonpos_of_isLocalMax`); hence `u ≤ v ≤ M + ε R²` where `R` bounds
`|x|` on `closure Ω`. Let `ε → 0`. -/
theorem weak_maximum_principle {Ω : Set Euclid3} {u : Euclid3 → ℝ} {M : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hc : ContinuousOn u (closure Ω)) (hsub : ∀ x ∈ Ω, 0 ≤ Δ u x)
    (hM : ∀ y ∈ frontier Ω, u y ≤ M) : ∀ x ∈ closure Ω, u x ≤ M := by
  obtain ⟨R, hR⟩ := hb.closure.exists_norm_le
  have hK : IsCompact (closure Ω) := hb.isCompact_closure
  have key : ∀ ε > 0, ∀ x ∈ closure Ω, u x ≤ M + ε * R ^ 2 := by
    intro ε hε x hx
    set v : Euclid3 → ℝ := fun y => u y + ε * ‖y‖ ^ 2 with hv
    have hvc : ContinuousOn v (closure Ω) := hc.add (by fun_prop)
    obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hvc
    have hx₀Ω : x₀ ∉ Ω := by
      intro hx₀Ω
      have hloc : IsLocalMax v x₀ :=
        Filter.mem_of_superset (hΩ.mem_nhds hx₀Ω) fun y hy => hmax (subset_closure hy)
      have hua : ContDiffAt ℝ 2 u x₀ := hu.contDiffAt (hΩ.mem_nhds hx₀Ω)
      have hn : ContDiffAt ℝ 2 (fun y : Euclid3 => ‖y‖ ^ 2) x₀ :=
        (contDiff_norm_sq ℝ).contDiffAt
      have hwa : ContDiffAt ℝ 2 (fun y : Euclid3 => ε * ‖y‖ ^ 2) x₀ :=
        contDiffAt_const.mul hn
      have hlap : Δ v x₀ = Δ u x₀ + ε * 6 := by
        rw [show v = u + fun y => ε * ‖y‖ ^ 2 from rfl, hua.laplacian_add hwa]
        congr 1
        rw [show (fun y : Euclid3 => ε * ‖y‖ ^ 2) = ε • fun y => ‖y‖ ^ 2 from rfl,
          laplacian_smul ε hn, laplacian_normSq]
        simp
      have h1 := laplacian_nonpos_of_isLocalMax (hua.add hwa) hloc
      have h2 := hsub x₀ hx₀Ω
      rw [show (fun y => u y + ε * ‖y‖ ^ 2) = v from rfl, hlap] at h1
      linarith
    have hfr : x₀ ∈ frontier Ω := by
      rw [hΩ.frontier_eq]
      exact ⟨hx₀, hx₀Ω⟩
    have hR0 : ‖x₀‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR x₀ hx₀) 2
    calc u x ≤ v x := by simp only [hv]; nlinarith [sq_nonneg ‖x‖]
      _ ≤ v x₀ := hmax hx
      _ ≤ M + ε * R ^ 2 := by
        simp only [hv]
        nlinarith [hM x₀ hfr]
  intro x hx
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hR2 : 0 < R ^ 2 + 1 := by positivity
  have h := key (δ / (R ^ 2 + 1)) (by positivity) x hx
  have h' : δ / (R ^ 2 + 1) * R ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR2]
    nlinarith
  linarith


/-- **Maximum on the frontier.** Under the hypotheses of the weak maximum
principle and `Ω ≠ ∅`, the maximum of `u` over `closure Ω` is attained at a
frontier point: `sup_{closure Ω} u = max_{frontier Ω} u`. -/
theorem exists_frontier_isMaxOn {Ω : Set Euclid3} {u : Euclid3 → ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (hu : ContDiffOn ℝ 2 u Ω)
    (hc : ContinuousOn u (closure Ω)) (hsub : ∀ x ∈ Ω, 0 ≤ Δ u x) :
    ∃ y ∈ frontier Ω, IsMaxOn u (closure Ω) y := by
  have hfne : (frontier Ω).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨hne, fun h => NormedSpace.unbounded_univ ℝ Euclid3 (h ▸ hb)⟩
  have hfK : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure)
  obtain ⟨y, hy, hmax⟩ := hfK.exists_isMaxOn hfne (hc.mono frontier_subset_closure)
  exact ⟨y, hy, fun x hx => weak_maximum_principle hΩ hb hu hc hsub (fun z hz => hmax hz) x hx⟩

/-! ### Bochner identity: `|B|²` is subharmonic for vacuum fields -/

/-- Squared Euclidean field magnitude `|B|² = ∑ᵢ Bᵢ²` (the sum of squares of the
Cartesian components, i.e. `B ⬝ᵥ B`), as a scalar field. -/
@[expose] def normSqField (B : Euclid3 → Euclid3) : Euclid3 → ℝ := fun y => ∑ i : Fin 3, B y i ^ 2

/-- `|B|²` is the squared Euclidean norm `‖B‖²`. -/
theorem normSqField_eq_norm_sq (B : Euclid3 → Euclid3) (y : Euclid3) :
    normSqField B y = ‖B y‖ ^ 2 := by
  simp [normSqField, EuclideanSpace.real_norm_sq_eq]

/-- `|B|²` is the Euclidean inner product `⟪B, B⟫`. -/
theorem normSqField_eq_inner (B : Euclid3 → Euclid3) :
    normSqField B = fun y => ⟪B y, B y⟫ := by
  funext y
  rw [real_inner_self_eq_norm_sq, normSqField_eq_norm_sq]

/-- A coordinate of a derivative is the derivative of the coordinate. -/
theorem fderiv_coord_apply {g : Euclid3 → Euclid3} {x : Euclid3}
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) (v : Euclid3) :
    fderiv ℝ (fun y => g y i) x v = fderiv ℝ g x v i := by
  have h := ((EuclideanSpace.proj i : Euclid3 →L[ℝ] ℝ).hasFDerivAt.comp x hg.hasFDerivAt).fderiv
  exact congrArg (fun L : Euclid3 →L[ℝ] ℝ => L v) h

/-- `|B|²` is `C²` wherever `B` is. -/
theorem contDiffOn_normSqField {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : ContDiffOn ℝ 2 B Ω) : ContDiffOn ℝ 2 (normSqField B) Ω := by
  rw [normSqField_eq_inner]
  exact hB.inner ℝ hB

/-- **Bochner identity.** For a vacuum field, `Δ|B|² = 2 ∑ᵢⱼ (∂ⱼ Bᵢ)²` at every
point of the region.

Proof: `∂ⱼ∂ⱼ|B|² = 2(|∂ⱼB|² + ⟪B, ∂ⱼ∂ⱼB⟫)`, and the vector Laplacian of `B`
vanishes: by the curl-free condition and symmetry of second derivatives,
`∑ⱼ ∂ⱼ∂ⱼ Bᵢ = ∑ⱼ ∂ᵢ∂ⱼ Bⱼ = ∂ᵢ(∇ · B) = 0`. -/
theorem laplacian_normSqField {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) :
    Δ (normSqField B) x = 2 * ∑ i : Fin 3, ∑ j : Fin 3, (fderiv ℝ B x (coordVec j) i) ^ 2 := by
  have hnhds : Ω ∈ 𝓝 x := hB.isOpen.mem_nhds hx
  have hC : ∀ y ∈ Ω, ContDiffAt ℝ 2 B y := fun y hy =>
    hB.contDiffOn.contDiffAt (hB.isOpen.mem_nhds hy)
  have hD1 : ∀ y ∈ Ω, DifferentiableAt ℝ B y := fun y hy =>
    (hC y hy).differentiableAt (by norm_num)
  have hD2 : DifferentiableAt ℝ (fderiv ℝ B) x :=
    ((hC x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDe : ∀ v, DifferentiableAt ℝ (fun y => fderiv ℝ B y v) x := fun v =>
    hD2.clm_apply (differentiableAt_const v)
  have hP : ∀ v k, DifferentiableAt ℝ (fun y => fderiv ℝ B y v k) x := fun v k =>
    (EuclideanSpace.proj k : Euclid3 →L[ℝ] ℝ).differentiableAt.comp x (hDe v)
  set H : Euclid3 →L[ℝ] Euclid3 →L[ℝ] Euclid3 := fderiv ℝ (fderiv ℝ B) x with hHdef
  have hsymm : ∀ v w, H v w = H w v := (hC x hx).isSymmSndFDerivAt (by simp)
  have hH : ∀ v w, fderiv ℝ (fun y => fderiv ℝ B y w) x v = H v w :=
    fderiv_fderiv_apply_eq hD2
  -- The vector Laplacian of a vacuum field vanishes.
  have hvecLap : ∀ i, ∑ j : Fin 3, H (coordVec j) (coordVec j) i = 0 := by
    intro i
    have step : ∀ j, H (coordVec j) (coordVec j) i =
        fderiv ℝ (fun y => fderiv ℝ B y (coordVec j) j) x (coordVec i) := by
      intro j
      have hev : (fun y => fderiv ℝ B y (coordVec j) i) =ᶠ[𝓝 x]
          (fun y => fderiv ℝ B y (coordVec i) j) :=
        Filter.mem_of_superset hnhds fun y hy =>
          (curlOp_eq_zero_iff _).1 (hB.curl_eq_zero y hy) i j
      rw [← hH, ← fderiv_coord_apply (hDe _), hev.fderiv_eq, fderiv_coord_apply (hDe _), hH,
        hsymm, ← hH, fderiv_coord_apply (hDe _)]
    simp_rw [step]
    rw [← sum_apply, ← fderiv_fun_sum (u := Finset.univ)
      (A := fun j y => fderiv ℝ B y (coordVec j) j) fun j _ => hP _ _]
    have hev : (fun y => ∑ j : Fin 3, fderiv ℝ B y (coordVec j) j) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.mem_of_superset hnhds fun y hy => hB.div_eq_zero y hy
    rw [hev.fderiv_eq]
    simp
  -- Second directional derivatives of `|B|²`.
  have hu1 : ∀ v, (fun y => fderiv ℝ (normSqField B) y v) =ᶠ[𝓝 x]
      fun y => 2 * ⟪B y, fderiv ℝ B y v⟫ := by
    intro v
    refine Filter.mem_of_superset hnhds fun y hy => ?_
    change fderiv ℝ (normSqField B) y v = 2 * ⟪B y, fderiv ℝ B y v⟫
    rw [normSqField_eq_inner, fderiv_inner_apply ℝ (hD1 y hy) (hD1 y hy), real_inner_comm]
    ring
  have huC : ContDiffAt ℝ 2 (normSqField B) x :=
    (contDiffOn_normSqField hB.contDiffOn).contDiffAt hnhds
  have huD : DifferentiableAt ℝ (fderiv ℝ (normSqField B)) x :=
    (huC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond : ∀ v, fderiv ℝ (fderiv ℝ (normSqField B)) x v v =
      2 * (⟪B x, H v v⟫ + ⟪fderiv ℝ B x v, fderiv ℝ B x v⟫) := by
    intro v
    rw [← fderiv_fderiv_apply_eq huD, (hu1 v).fderiv_eq,
      fderiv_const_mul ((hD1 x hx).inner ℝ (hDe v)), smul_apply,
      fderiv_inner_apply ℝ (hD1 x hx) (hDe v), hH, smul_eq_mul]
  rw [laplacian_eq_sum_fderiv_fderiv]
  simp only [hsecond]
  have h0 := hvecLap 0
  have h1 := hvecLap 1
  have h2 := hvecLap 2
  simp only [Fin.sum_univ_three, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h0 h1 h2 ⊢
  linear_combination (2 * B x 0) * h0 + (2 * B x 1) * h1 + (2 * B x 2) * h2

/-- **`|B|²` is subharmonic** in any vacuum region: `Δ|B|² ≥ 0`. -/
theorem laplacian_normSqField_nonneg {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) : 0 ≤ Δ (normSqField B) x := by
  rw [laplacian_normSqField hB hx]
  positivity


/-! ### Linear structure of vacuum fields -/

/-- The divergence operator is additive-subtractive: `div (L₁ - L₂) = div L₁ - div L₂`. -/
theorem divOp_sub (L₁ L₂ : Euclid3 →L[ℝ] Euclid3) : divOp (L₁ - L₂) = divOp L₁ - divOp L₂ := by
  simp [divOp, Finset.sum_sub_distrib]

/-- The curl operator commutes with subtraction. -/
theorem curlOp_sub (L₁ L₂ : Euclid3 →L[ℝ] Euclid3) :
    curlOp (L₁ - L₂) = curlOp L₁ - curlOp L₂ := by
  ext k
  fin_cases k <;> simp [curlOp] <;> ring

/-- The difference of two vacuum fields on the same region is a vacuum field
(the vacuum equations are linear). This is the field-error field `B₁ - B₂`. -/
theorem VacuumField.sub {Ω : Set Euclid3} {B₁ B₂ : Euclid3 → Euclid3}
    (h₁ : VacuumField Ω B₁) (h₂ : VacuumField Ω B₂) : VacuumField Ω (B₁ - B₂) := by
  have hd : ∀ x ∈ Ω, fderiv ℝ (B₁ - B₂) x = fderiv ℝ B₁ x - fderiv ℝ B₂ x := fun x hx =>
    fderiv_sub ((h₁.contDiffOn.contDiffAt (h₁.isOpen.mem_nhds hx)).differentiableAt
      (by norm_num)) ((h₂.contDiffOn.contDiffAt (h₁.isOpen.mem_nhds hx)).differentiableAt
      (by norm_num))
  refine ⟨h₁.isOpen, h₁.contDiffOn.sub h₂.contDiffOn, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, hd x hx, divOp_sub, ← fieldDiv, ← fieldDiv, h₁.div_eq_zero x hx,
      h₂.div_eq_zero x hx, sub_zero]
  · rw [fieldCurl, hd x hx, curlOp_sub, ← fieldCurl, ← fieldCurl, h₁.curl_eq_zero x hx,
      h₂.curl_eq_zero x hx, sub_zero]

/-- Restricting a vacuum field to an open subregion gives a vacuum field. -/
theorem VacuumField.mono {Ω Ω' : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) : VacuumField Ω' B :=
  ⟨hΩ', hB.contDiffOn.mono hsub, fun x hx => hB.div_eq_zero x (hsub hx),
    fun x hx => hB.curl_eq_zero x (hsub hx)⟩

/-! ### Boundary-to-interior bounds -/

/-- **Boundary-to-interior bound for `|B|²`.** If `B` is a vacuum field on a
bounded open region `Ω`, continuous up to the boundary, and `|B|² ≤ M` on the
frontier, then `|B|² ≤ M` throughout `closure Ω`. -/
theorem VacuumField.normSq_le_of_frontier {Ω : Set Euclid3} {B : Euclid3 → Euclid3} {M : ℝ}
    (hB : VacuumField Ω B) (hb : Bornology.IsBounded Ω) (hc : ContinuousOn B (closure Ω))
    (hM : ∀ y ∈ frontier Ω, normSqField B y ≤ M) : ∀ x ∈ closure Ω, normSqField B x ≤ M := by
  refine weak_maximum_principle hB.isOpen hb (contDiffOn_normSqField hB.contDiffOn) ?_
    (fun x hx => laplacian_normSqField_nonneg hB hx) hM
  rw [normSqField_eq_inner]
  exact hc.inner hc

/-- Boundary-to-interior bound in norm form: `‖B‖ ≤ b` on the frontier implies
`‖B‖ ≤ b` on `closure Ω`. -/
theorem VacuumField.norm_le_of_frontier {Ω : Set Euclid3} {B : Euclid3 → Euclid3} {b : ℝ}
    (hB : VacuumField Ω B) (hb : Bornology.IsBounded Ω) (hc : ContinuousOn B (closure Ω))
    (hb0 : 0 ≤ b) (hM : ∀ y ∈ frontier Ω, ‖B y‖ ≤ b) : ∀ x ∈ closure Ω, ‖B x‖ ≤ b := by
  intro x hx
  have h := hB.normSq_le_of_frontier hb hc (M := b ^ 2) (fun y hy => by
    rw [normSqField_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM y hy) 2) x hx
  rw [normSqField_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 (by norm_num)).1 h

/-- **Field-error transfer.** If two vacuum fields on a bounded open region (e.g. a
model coil field and the as-built field, both current free in `Ω`) differ by at
most `δ` on the frontier, they differ by at most `δ` everywhere in `closure Ω`:
the volume error is bounded by the surface error. -/
theorem VacuumField.error_le_of_frontier {Ω : Set Euclid3} {B₁ B₂ : Euclid3 → Euclid3}
    {δ : ℝ} (h₁ : VacuumField Ω B₁) (h₂ : VacuumField Ω B₂) (hb : Bornology.IsBounded Ω)
    (hc₁ : ContinuousOn B₁ (closure Ω)) (hc₂ : ContinuousOn B₂ (closure Ω)) (hδ : 0 ≤ δ)
    (hM : ∀ y ∈ frontier Ω, ‖B₁ y - B₂ y‖ ≤ δ) : ∀ x ∈ closure Ω, ‖B₁ x - B₂ x‖ ≤ δ :=
  (h₁.sub h₂).norm_le_of_frontier hb (hc₁.sub hc₂) hδ hM

/-- **No strict interior local maximum of `|B|²`** in a vacuum region. (A strict
local *minimum* is possible: see `hyperbolicField_strict_min`.) -/
theorem VacuumField.not_strict_local_max_normSq {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) :
    ¬ ∀ᶠ y in 𝓝[≠] x, normSqField B y < normSqField B x := by
  intro h
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 h
  obtain ⟨δ, hδ, hδs⟩ := Metric.isOpen_iff.1 hB.isOpen x hx
  set r := min ε δ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by have := min_le_left ε δ; linarith
  have hrδ : r < δ := by have := min_le_right ε δ; linarith
  have hcl : closure (Metric.ball x r) = Metric.closedBall x r := closure_ball x hr0.ne'
  have hsubΩ : Metric.closedBall x r ⊆ Ω :=
    (Metric.closedBall_subset_ball hrδ).trans hδs
  have hu : ContDiffOn ℝ 2 (normSqField B) Ω := contDiffOn_normSqField hB.contDiffOn
  have hB' : VacuumField (Metric.ball x r) B :=
    hB.mono Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hsubΩ)
  obtain ⟨y, hy, hmax⟩ := exists_frontier_isMaxOn Metric.isOpen_ball Metric.isBounded_ball
    ⟨x, Metric.mem_ball_self hr0⟩ (contDiffOn_normSqField hB'.contDiffOn)
    (by rw [hcl]; exact hu.continuousOn.mono hsubΩ)
    (fun z hz => laplacian_normSqField_nonneg hB' hz)
  rw [frontier_ball x hr0.ne'] at hy
  have hxy : normSqField B x ≤ normSqField B y :=
    hmax (subset_closure (Metric.mem_ball_self hr0))
  have hyx : normSqField B y < normSqField B x := by
    refine hεs ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Metric.mem_sphere.1 hy]
      exact hrε
    · intro hyx
      rw [Set.mem_singleton_iff] at hyx
      rw [hyx, Metric.mem_sphere, dist_self] at hy
      exact hr0.ne' hy.symm
  linarith

/-- **No strict interior local maximum of `|B|`** in a vacuum region. -/
theorem VacuumField.not_strict_local_max_norm {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hB : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) :
    ¬ ∀ᶠ y in 𝓝[≠] x, ‖B y‖ < ‖B x‖ := by
  intro h
  apply hB.not_strict_local_max_normSq hx
  filter_upwards [h] with y hy
  rw [normSqField_eq_norm_sq, normSqField_eq_norm_sq]
  exact pow_lt_pow_left₀ hy (norm_nonneg _) (by norm_num)

/-! ### Affine vacuum fields and the minimum-`|B|` counterexample -/

/-- An affine field `y ↦ B₀ + L y` with trace-free, curl-free (symmetric) `L` is a
vacuum field on every open region. -/
theorem vacuumField_affine {Ω : Set Euclid3} (hΩ : IsOpen Ω) (B₀ : Euclid3)
    (L : Euclid3 →L[ℝ] Euclid3) (hdiv : divOp L = 0) (hcurl : curlOp L = 0) :
    VacuumField Ω (fun y => B₀ + L y) := by
  have hd : ∀ x, fderiv ℝ (fun y => B₀ + L y) x = L := fun x =>
    (L.hasFDerivAt.const_add B₀).fderiv
  refine ⟨hΩ, (contDiff_const.add L.contDiff).contDiffOn, fun x _ => ?_, fun x _ => ?_⟩
  · rw [fieldDiv, hd, hdiv]
  · rw [fieldCurl, hd, hcurl]

/-- The hyperbolic (X-point) linear field `B(x, y, z) = (x, y, -2z)`, the gradient
of the harmonic polynomial `(x² + y²)/2 - z²`. -/
@[expose] def hyperbolicField : Euclid3 →L[ℝ] Euclid3 :=
  (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 0) +
    (EuclideanSpace.proj 1 : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 1) +
    (-2 : ℝ) • (EuclideanSpace.proj 2 : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 2)

/-- Coordinates of the hyperbolic field: `(x, y, -2z)`. -/
theorem hyperbolicField_coords (y : Euclid3) :
    hyperbolicField y 0 = y 0 ∧ hyperbolicField y 1 = y 1 ∧ hyperbolicField y 2 = -2 * y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hyperbolicField]

/-- The hyperbolic field is trace free. -/
theorem divOp_hyperbolicField : divOp hyperbolicField = 0 := by
  rw [divOp_apply]
  simp only [(hyperbolicField_coords _).1, (hyperbolicField_coords _).2.1,
    (hyperbolicField_coords _).2.2]
  simp
  norm_num

/-- The hyperbolic field is curl free. -/
theorem curlOp_hyperbolicField : curlOp hyperbolicField = 0 := by
  rw [curlOp_eq_zero_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicField]

/-- The hyperbolic field is a vacuum field on all of space. -/
theorem hyperbolicField_vacuum : VacuumField Set.univ (fun y => hyperbolicField y) := by
  simpa using vacuumField_affine isOpen_univ 0 hyperbolicField divOp_hyperbolicField
    curlOp_hyperbolicField

/-- `|B|² = x² + y² + 4z²` for the hyperbolic field. -/
theorem normSqField_hyperbolicField (y : Euclid3) :
    normSqField (fun y => hyperbolicField y) y = y 0 ^ 2 + y 1 ^ 2 + 4 * y 2 ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := hyperbolicField_coords y
  simp only [normSqField, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- **Counterexample (corrected min/max statement).** A vacuum field CAN have a
strict interior minimum of `|B|`: for the hyperbolic field, `|B|²` has a strict
global minimum (value `0`) at the origin. So subharmonicity of `|B|²` only rules
out interior maxima, not minima. -/
theorem hyperbolicField_strict_min (y : Euclid3) (hy : y ≠ 0) :
    normSqField (fun y => hyperbolicField y) 0 < normSqField (fun y => hyperbolicField y) y := by
  rw [normSqField_hyperbolicField, normSqField_hyperbolicField]
  have hne : y 0 ≠ 0 ∨ y 1 ≠ 0 ∨ y 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy
    ext i
    fin_cases i <;> simp [hcon.1, hcon.2.1, hcon.2.2]
  simp only [PiLp.zero_apply]
  rcases hne with h | h | h
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 2)]
  · have := pow_pos (abs_pos.2 h) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

/-- Packaged counterexample: there is a vacuum field on the unit ball whose
magnitude `|B|` has a strict interior minimum (at the centre). -/
theorem exists_vacuum_strict_interior_min :
    ∃ B : Euclid3 → Euclid3, VacuumField (Metric.ball 0 1) B ∧
      ∀ y, y ≠ 0 → ‖B 0‖ < ‖B y‖ := by
  refine ⟨fun y => hyperbolicField y,
    hyperbolicField_vacuum.mono Metric.isOpen_ball (Set.subset_univ _), fun y hy => ?_⟩
  have h := hyperbolicField_strict_min y hy
  rw [normSqField_eq_norm_sq, normSqField_eq_norm_sq] at h
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 h

end PlasmaLean.Vacuum
