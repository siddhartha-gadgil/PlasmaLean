/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.LorentzGlobalExistence

/-!
# Lorentz orbits for fields given on an open set, without potentials (audit finding AV-M4)

The Newton–Lorentz equations `x' = v`, `m v' = q (E(x) + v × B(x))` are the first-order system
`y' = lorentzEMField m q E B y` on `Space × Space` (`Theory/Kinetic/CrossedFieldOrbit`). The
earlier existence and uniqueness theorems assume `E`, `B` of class `C¹` on ALL of space, and
some of them a vector potential on all of space. Fields of coils, of a wire, or a Dommaschk
potential are regular only on an open set `U`, and often have no vector or scalar potential
there. In this file the fields are `C¹` on an open set `U` (`ContDiffOn ℝ 1 _ U`); their values
outside `U` are arbitrary and are never used. NO vector potential appears anywhere, and a
scalar potential for `E` (on `U` only) appears only in the energy law.

Hypotheses common to the existence and uniqueness results: `m ≠ 0`, `U` open, `E` and `B` of
class `C¹` on `U`. `B` need not be divergence free and `E` need not be a gradient.

* Tools. `lorentzEMField_contDiffOn`: the vector field is `C¹` on `U ×ˢ univ`.
  `integralCurve_eqOn_of_contDiffOn`: two integral curves of a vector field that is `C¹` on an
  open set `W`, on an order-connected set of times, staying in `W` and equal at one time, are
  equal. `LorentzOrbitOn.congr_fields`: an orbit staying in `U` only sees the fields on `U`.
* Local existence. **`lorentzOrbitOn_exists_local_of_contDiffOn`**: for `x₀ ∈ U`, every `v₀` and
  every initial time `t₀` there are `ε > 0` and an orbit on `(t₀ − ε, t₀ + ε)` through
  `(x₀, v₀)` at `t₀` that stays in `U`.
* Uniqueness. **`lorentzOrbitOn_unique_of_contDiffOn`**: two orbits on an order-connected set of
  times `s` (any interval) that stay in `U` and have the same position and velocity at one
  time of `s` agree on `s`.
* Conservation laws on `U`. `LorentzOrbitOn.energy_eq_of_potentialOn`: if `E = −∇Φ` at the
  points of `U`, the energy `(m/2)‖v‖² + q Φ(x)` is constant along an orbit that stays in `U`.
  `LorentzOrbitOn.speed_eq_of_electric_zero`: if `E = 0` on `U`, the speed is constant.
* Existence for all times. **`lorentzOrbit_existsUnique_of_apriori_on`**: a priori bounds
  (`APrioriBounded`) by compact subsets of `U ×ˢ univ` give an orbit for all times that stays
  in `U`, and every orbit for all times with the same initial data equals it.
  `lorentzEM_apriori_of_confined`: such bounds hold if the POSITIONS of the integral curves from
  `(x₀, v₀)` stay in one compact `K ⊆ U`; the speed is then bounded on every finite horizon
  by Grönwall's inequality, because the magnetic force does no work and `E` is bounded on `K`.
  **`lorentzOrbit_existsUnique_of_confined`** combines the two: confinement of the positions to
  a compact subset of `U` gives a unique orbit for all times.
* Extensions. `lorentzOrbitOn_existsUnique_of_extension`: if `E`, `B` agree on `U` with fields
  `E'`, `B'` that are `C¹` on all of space, `E'` of linear growth, then on every interval of
  times about `0` on which the global orbit of `(E', B')` stays in `U` it is an orbit of
  `(E, B)`, and the only one that stays in `U`.
* The case `U = Space`. `lorentzOrbit_existsUnique_of_linear_growth'` re-derives
  `lorentzOrbit_existsUnique_of_linear_growth` (and with it `lorentzOrbit_exists`, the case
  `E = 0`) from the open-set theorem.

Relation to the earlier results (none of them is changed). `lorentzOrbitOn_exists_local` and
`lorentzOrbitOn_unique` / `lorentzOrbit_unique` (`CrossedFieldOrbit`) assume `A` of class `C²`
on all of space with `B = ∇ × A` and `E = −∇Φ` of class `C¹` on all of space; since then `B`
is `C¹` (`contDiff_fieldCurl`), they are the case `U = Space` of the local existence and
uniqueness theorems here. `lorentzOrbitOn_unique_of_contDiff` is the case `U = Space`,
`s = Ioo a b`. The global theorems of `LorentzGlobalExistence` already use no vector potential.

Not proved: an escape lemma for maximal orbits (a maximal orbit that is not defined for all
times leaves every compact subset of `U × Space`); only its consequence for existence, in the
form of a priori bounds, is proved. No criterion is given here that confines the positions to
a compact subset of `U` for a concrete field (that is the role of conserved quantities, see
`orbit_trapped_Icc`). The Hamiltonian formulation on `U` (which needs a vector potential on
`U`) is not treated. Time-dependent fields and relativistic motion are not covered.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Fields.ODEGlobal PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti InnerProductSpace Set WithLp
open scoped RealInnerProductSpace

/-! ## The vector field on an open set; integral curves -/

/-- The Newton–Lorentz vector field is `C¹` on `U ×ˢ univ` when `E` and `B` are `C¹` on `U`.
No hypothesis on `m`. -/
theorem lorentzEMField_contDiffOn (m q : ℝ) {E B : Space → Space} {U : Set Space}
    (hE : ContDiffOn ℝ 1 E U) (hB : ContDiffOn ℝ 1 B U) :
    ContDiffOn ℝ 1 (lorentzEMField m q E B) (U ×ˢ univ) := by
  have hE' : ContDiffOn ℝ 1 (fun y : Space × Space => E y.1) (U ×ˢ univ) :=
    hE.comp contDiffOn_fst (fun y hy => hy.1)
  have hB' : ContDiffOn ℝ 1 (fun y : Space × Space => B y.1) (U ×ˢ univ) :=
    hB.comp contDiffOn_fst (fun y hy => hy.1)
  have hcr : ContDiffOn ℝ 1 (fun y : Space × Space => cross y.2 (B y.1)) (U ×ˢ univ) :=
    contDiff_cross.comp_contDiffOn (contDiffOn_snd.prodMk hB')
  exact contDiffOn_snd.prodMk ((hE'.add hcr).const_smul (q / m))

/-- **Uniqueness of integral curves in an open set.** Let `f` be `C¹` on the open set `W`. Two
integral curves of `f` at the times of an order-connected set `s` (an interval of any kind)
that stay in `W` and agree at one time of `s` agree on `s`. -/
theorem integralCurve_eqOn_of_contDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → F} {W : Set F} (hW : IsOpen W) (hf : ContDiffOn ℝ 1 f W) {s : Set ℝ}
    (hs : s.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ s) {γ₁ γ₂ : ℝ → F}
    (h₁ : ∀ t ∈ s, HasDerivAt γ₁ (f (γ₁ t)) t) (h₂ : ∀ t ∈ s, HasDerivAt γ₂ (f (γ₂ t)) t)
    (hW₁ : ∀ t ∈ s, γ₁ t ∈ W) (hW₂ : ∀ t ∈ s, γ₂ t ∈ W) (h0 : γ₁ t₀ = γ₂ t₀) :
    EqOn γ₁ γ₂ s := by
  have hlip : ∀ a b : ℝ, Icc a b ⊆ s →
      ∃ L, LipschitzOnWith L f (γ₁ '' Icc a b ∪ γ₂ '' Icc a b) := by
    intro a b hab
    have hK : IsCompact (γ₁ '' Icc a b ∪ γ₂ '' Icc a b) :=
      (isCompact_Icc.image_of_continuousOn fun r hr =>
        (h₁ r (hab hr)).continuousAt.continuousWithinAt).union
      (isCompact_Icc.image_of_continuousOn fun r hr =>
        (h₂ r (hab hr)).continuousAt.continuousWithinAt)
    have hKW : γ₁ '' Icc a b ∪ γ₂ '' Icc a b ⊆ W := by
      rintro y (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
      · exact hW₁ r (hab hr)
      · exact hW₂ r (hab hr)
    exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun y hy => by
      obtain ⟨Ky, u, hu, hl⟩ := (hf.contDiffAt (hW.mem_nhds (hKW hy))).exists_lipschitzOnWith
      exact ⟨Ky, u, mem_nhdsWithin_of_mem_nhds hu, hl⟩
  intro t ht
  rcases le_total t₀ t with h | h
  · have hab : Icc t₀ t ⊆ s := hs.out ht₀ ht
    obtain ⟨L, hL⟩ := hlip t₀ t hab
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f)
      (s := fun _ => γ₁ '' Icc t₀ t ∪ γ₂ '' Icc t₀ t) (fun _ _ => hL)
      (fun r hr => (h₁ r (hab hr)).continuousAt.continuousWithinAt)
      (fun r hr => (h₁ r (hab (Ico_subset_Icc_self hr))).hasDerivWithinAt)
      (fun r hr => Or.inl ⟨r, Ico_subset_Icc_self hr, rfl⟩)
      (fun r hr => (h₂ r (hab hr)).continuousAt.continuousWithinAt)
      (fun r hr => (h₂ r (hab (Ico_subset_Icc_self hr))).hasDerivWithinAt)
      (fun r hr => Or.inr ⟨r, Ico_subset_Icc_self hr, rfl⟩) h0 ⟨h, le_rfl⟩
  · have hab : Icc t t₀ ⊆ s := hs.out ht ht₀
    obtain ⟨L, hL⟩ := hlip t t₀ hab
    exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => f)
      (s := fun _ => γ₁ '' Icc t t₀ ∪ γ₂ '' Icc t t₀) (fun _ _ => hL)
      (fun r hr => (h₁ r (hab hr)).continuousAt.continuousWithinAt)
      (fun r hr => (h₁ r (hab (Ioc_subset_Icc_self hr))).hasDerivWithinAt)
      (fun r hr => Or.inl ⟨r, Ioc_subset_Icc_self hr, rfl⟩)
      (fun r hr => (h₂ r (hab hr)).continuousAt.continuousWithinAt)
      (fun r hr => (h₂ r (hab (Ioc_subset_Icc_self hr))).hasDerivWithinAt)
      (fun r hr => Or.inr ⟨r, Ioc_subset_Icc_self hr, rfl⟩) h0 ⟨le_rfl, h⟩

/-- **An orbit that stays in `U` only sees the fields on `U`.** If `E = E'` and `B = B'` at the
points of `U`, a Lorentz orbit of `(E', B')` on a set of times `s` whose position stays in `U`
is a Lorentz orbit of `(E, B)` on `s`. No hypothesis on `m`, on `U` or on the fields. -/
theorem LorentzOrbitOn.congr_fields {m q : ℝ} {E E' B B' : Space → Space} {U : Set Space}
    {x v : ℝ → Space} {s : Set ℝ} (h : LorentzOrbitOn m q E' B' x v s) (hE : EqOn E E' U)
    (hB : EqOn B B' U) (hxU : ∀ t ∈ s, x t ∈ U) : LorentzOrbitOn m q E B x v s where
  position := h.position
  newton t ht := by
    obtain ⟨a, ha, hlaw⟩ := h.newton t ht
    exact ⟨a, ha, by rw [hlaw, hE (hxU t ht), hB (hxU t ht)]⟩

/-! ## Local existence and uniqueness -/

/-- **Local existence of Lorentz orbits for fields on an open set, without potentials.** Let
`m ≠ 0`, `U` open, `E` and `B` of class `C¹` on `U`. For every `x₀ ∈ U`, every velocity `v₀`
and every initial time `t₀` there are `ε > 0` and a Lorentz orbit on `(t₀ − ε, t₀ + ε)` with
`x t₀ = x₀`, `v t₀ = v₀` whose position stays in `U`. -/
theorem lorentzOrbitOn_exists_local_of_contDiffOn {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} {U : Set Space} (hU : IsOpen U) (hE : ContDiffOn ℝ 1 E U)
    (hB : ContDiffOn ℝ 1 B U) {x₀ : Space} (hx₀ : x₀ ∈ U) (v₀ : Space) (t₀ : ℝ) :
    ∃ ε > 0, ∃ x v : ℝ → Space, LorentzOrbitOn m q E B x v (Ioo (t₀ - ε) (t₀ + ε)) ∧
      x t₀ = x₀ ∧ v t₀ = v₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), x t ∈ U := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence (hU.prod isOpen_univ)
    (lorentzEMField_contDiffOn m q hE hB) (isCompact_singleton (x := (x₀, v₀)))
    (singleton_subset_iff.mpr (mk_mem_prod hx₀ (mem_univ v₀)))
  obtain ⟨β, hβ0, hβ⟩ := hloc (x₀, v₀) rfl t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hcont : ContinuousAt (fun t => (β t).1) t₀ :=
    (hasDerivAt_prod_fst (hβ t₀ ht₀)).continuousAt
  have hnhds : (fun t => (β t).1) ⁻¹' U ∈ nhds t₀ :=
    hcont.preimage_mem_nhds (hU.mem_nhds (by simpa [hβ0] using hx₀))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hsub : Ioo (t₀ - min ε δ) (t₀ + min ε δ) ⊆ Ioo (t₀ - ε) (t₀ + ε) := fun t ht =>
    ⟨by linarith [ht.1, min_le_left ε δ], by linarith [ht.2, min_le_left ε δ]⟩
  refine ⟨min ε δ, lt_min hε hδ, _, _, lorentzOrbitOn_of_flow hm fun t ht => hβ t (hsub ht),
    by rw [hβ0], by rw [hβ0], fun t ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [ht.1, min_le_right ε δ], by linarith [ht.2, min_le_right ε δ]⟩

/-- **Uniqueness of Lorentz orbits for fields on an open set, without potentials.** Let
`m ≠ 0`, `U` open, `E` and `B` of class `C¹` on `U`. Two Lorentz orbits on an order-connected
set of times `s` (an interval of any kind) whose positions stay in `U` and which have the same
position and velocity at one time of `s` have the same position and velocity on `s`. -/
theorem lorentzOrbitOn_unique_of_contDiffOn {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    {U : Set Space} (hU : IsOpen U) (hE : ContDiffOn ℝ 1 E U) (hB : ContDiffOn ℝ 1 B U)
    {s : Set ℝ} (hs : s.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ s) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbitOn m q E B x₁ v₁ s) (h₂ : LorentzOrbitOn m q E B x₂ v₂ s)
    (hU₁ : ∀ t ∈ s, x₁ t ∈ U) (hU₂ : ∀ t ∈ s, x₂ t ∈ U) (hx : x₁ t₀ = x₂ t₀)
    (hv : v₁ t₀ = v₂ t₀) : EqOn x₁ x₂ s ∧ EqOn v₁ v₂ s := by
  have key := integralCurve_eqOn_of_contDiffOn (hU.prod isOpen_univ)
    (lorentzEMField_contDiffOn m q hE hB) hs ht₀
    (γ₁ := fun r => (x₁ r, v₁ r)) (γ₂ := fun r => (x₂ r, v₂ r))
    (fun r hr => h₁.hasDerivAt_lorentzEMField hm hr)
    (fun r hr => h₂.hasDerivAt_lorentzEMField hm hr)
    (fun r hr => mk_mem_prod (hU₁ r hr) (mem_univ _))
    (fun r hr => mk_mem_prod (hU₂ r hr) (mem_univ _)) (Prod.ext hx hv)
  exact ⟨fun t ht => congrArg Prod.fst (key ht), fun t ht => congrArg Prod.snd (key ht)⟩

/-! ## Conservation laws on an open set -/

/-- **Energy conservation for a potential on `U`.** Let `E = −∇Φ` at the points of `U` (no
hypothesis outside `U`). Along a Lorentz orbit on an order-connected set of times `s` whose
position stays in `U`, the energy `(m/2)‖v‖² + q Φ(x)` takes the same value at all times of
`s`. No hypothesis on `m`, on `B`, or on `U`. -/
theorem LorentzOrbitOn.energy_eq_of_potentialOn {m q : ℝ} {E B : Space → Space}
    {Φ : Space → ℝ} {U : Set Space} {x v : ℝ → Space} {s : Set ℝ} (hs : s.OrdConnected)
    (h : LorentzOrbitOn m q E B x v s)
    (hΦ : ∀ y ∈ U, HasFDerivAt Φ (-(innerSL ℝ (E y))) y) (hxU : ∀ t ∈ s, x t ∈ U) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) : orbitEnergy m q Φ x v a = orbitEnergy m q Φ x v b := by
  have hsub : Icc (min a b) (max a b) ⊆ s :=
    hs.out (by rcases min_choice a b with e | e <;> rw [e] <;> assumption)
      (by rcases max_choice a b with e | e <;> rw [e] <;> assumption)
  have hd : ∀ r ∈ Icc (min a b) (max a b), HasDerivAt (orbitEnergy m q Φ x v) 0 r := by
    intro r hr'
    have hr := hsub hr'
    obtain ⟨acc, hacc, hlaw⟩ := h.newton r hr
    have hk : HasDerivAt (fun u => m / 2 * ‖v u‖ ^ 2) (q * ⟪v r, E (x r)⟫) r := by
      have hn := (hacc.norm_sq).const_mul (m / 2)
      convert hn using 1
      have : m / 2 * (2 * ⟪v r, acc⟫) = ⟪v r, m • acc⟫ := by
        rw [inner_smul_right]; ring
      rw [this, hlaw, lorentz_power]
    have hp : HasDerivAt (fun u => Φ (x u)) (-⟪E (x r), v r⟫) r := by
      have := (hΦ (x r) (hxU r hr)).comp_hasDerivAt r (h.position r hr)
      convert this using 1
      · rfl
      · simp
    change HasDerivAt (fun u => m / 2 * ‖v u‖ ^ 2 + q * Φ (x u)) 0 r
    convert hk.add (hp.const_mul q) using 1
    rw [real_inner_comm]; ring
  exact eq_of_hasDerivAt_zero_Icc hd ⟨min_le_left a b, le_max_left a b⟩
    ⟨min_le_right a b, le_max_right a b⟩

/-- **Conservation of speed for a magnetic field on `U`.** Let `m ≠ 0` and `E = 0` at the points
of `U`. Along a Lorentz orbit on an order-connected set of times `s` whose position stays in
`U`, the speed `‖v‖` takes the same value at all times of `s`. No hypothesis on `B`. -/
theorem LorentzOrbitOn.speed_eq_of_electric_zero {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} {U : Set Space} {x v : ℝ → Space} {s : Set ℝ} (hs : s.OrdConnected)
    (h : LorentzOrbitOn m q E B x v s) (hE : ∀ y ∈ U, E y = 0) (hxU : ∀ t ∈ s, x t ∈ U)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : ‖v a‖ = ‖v b‖ := by
  have hen := h.energy_eq_of_potentialOn (Φ := fun _ => 0) (U := U) hs
    (fun y hy => by rw [hE y hy]; simpa using hasFDerivAt_const (0 : ℝ) y) hxU ha hb
  simp only [orbitEnergy, mul_zero, add_zero] at hen
  have hsq : ‖v a‖ ^ 2 = ‖v b‖ ^ 2 := by
    have h2 : m / 2 ≠ 0 := by positivity
    exact mul_left_cancel₀ h2 hen
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-! ## Existence for all times -/

/-- Under a priori bounds by compact subsets of `W`, an integral curve for all times from `x₀`
stays in `W`. -/
theorem aprioriBounded_mem_of_global {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] {f : F → F} {W : Set F} {x₀ : F} (hbd : APrioriBounded f W x₀)
    {γ : ℝ → F} (h0 : γ 0 = x₀) (hγ : ∀ t, HasDerivAt γ (f (γ t)) t) (t : ℝ) : γ t ∈ W := by
  obtain ⟨K, -, hKW, hK⟩ := hbd |t|
  exact hKW (hK |t| ⟨abs_nonneg t, le_rfl⟩ γ h0 (fun r _ => hγ r) t
    ⟨neg_abs_le t, le_abs_self t⟩)

/-- **From a priori bounds to a unique orbit for all times, for fields on an open set.** Let
`m ≠ 0`, `U` open, `E` and `B` of class `C¹` on `U`, `x₀ ∈ U`. If the integral curves of
`lorentzEMField m q E B` from `(x₀, v₀)` are a priori bounded on every finite horizon by
compact subsets of `U ×ˢ univ`, there is a Lorentz orbit for all times with `x 0 = x₀`,
`v 0 = v₀` whose position stays in `U`, and every Lorentz orbit for all times with these
initial data equals it. -/
theorem lorentzOrbit_existsUnique_of_apriori_on {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    {U : Set Space} (hU : IsOpen U) (hE : ContDiffOn ℝ 1 E U) (hB : ContDiffOn ℝ 1 B U)
    {x₀ v₀ : Space} (hx₀ : x₀ ∈ U)
    (hbd : APrioriBounded (lorentzEMField m q E B) (U ×ˢ univ) (x₀, v₀)) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ (∀ t, x t ∈ U) ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_of_apriori (hU.prod isOpen_univ)
    (lorentzEMField_contDiffOn m q hE hB) (mk_mem_prod hx₀ (mem_univ v₀)) hbd
  have horb : LorentzOrbit m q E B (fun t => (γ t).1) (fun t => (γ t).2) :=
    lorentzOrbitOn_univ.mp (lorentzOrbitOn_of_flow hm fun t _ => hγ t)
  have hx0 : (γ 0).1 = x₀ := by rw [hγ0]
  have hv0 : (γ 0).2 = v₀ := by rw [hγ0]
  have hγU : ∀ t, (γ t).1 ∈ U := fun t => (aprioriBounded_mem_of_global hbd hγ0 hγ t).1
  refine ⟨_, _, horb, hx0, hv0, hγU, fun x' v' h' hx' hv' => ?_⟩
  have hU' : ∀ t, x' t ∈ U := fun t =>
    (aprioriBounded_mem_of_global hbd (γ := fun r => (x' r, v' r)) (by rw [hx', hv'])
      (fun r => (h'.on univ).hasDerivAt_lorentzEMField hm (mem_univ r)) t).1
  have key := lorentzOrbitOn_unique_of_contDiffOn hm hU hE hB ordConnected_univ
    (mem_univ (0 : ℝ)) (h'.on univ) (horb.on univ) (fun t _ => hU' t) (fun t _ => hγU t)
    (hx'.trans hx0.symm) (hv'.trans hv0.symm)
  exact ⟨funext fun t => key.1 (mem_univ t), funext fun t => key.2 (mem_univ t)⟩

/-- **A priori bounds from confinement of the positions.** Let `K ⊆ U` be compact and `E`
continuous on `K`. If the position of every integral curve of `lorentzEMField m q E B` from
`(x₀, v₀)` on a symmetric interval of times stays in `K`, these integral curves are a priori
bounded by compact subsets of `U ×ˢ univ`: with `‖E‖ ≤ C` on `K`, `u = ‖v‖² + 1` satisfies
`|u'| ≤ |q/m| |C| u` (the magnetic force does no work), so the speed is bounded on every finite
horizon. No hypothesis on `B` or on `m`, and `E` need not be a gradient. -/
theorem lorentzEM_apriori_of_confined (m q : ℝ) {E : Space → Space} (B : Space → Space)
    {U K : Set Space} (hK : IsCompact K) (hKU : K ⊆ U) (hE : ContinuousOn E K)
    (x₀ v₀ : Space)
    (hconf : ∀ c : ℝ, 0 ≤ c → ∀ γ : ℝ → Space × Space, γ 0 = (x₀, v₀) →
      (∀ t ∈ Icc (-c) c, HasDerivAt γ (lorentzEMField m q E B (γ t)) t) →
      ∀ t ∈ Icc (-c) c, (γ t).1 ∈ K) :
    APrioriBounded (lorentzEMField m q E B) (U ×ˢ univ) (x₀, v₀) := by
  intro T
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hE
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = |q / m| * |C| := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  refine ⟨K ×ˢ Metric.closedBall 0 (gronwallBound |‖v₀‖ ^ 2 + 1| κ 0 T),
    hK.prod (isCompact_closedBall _ _), prod_mono hKU (subset_univ _),
    fun c hc γ h0 hγ t ht => ?_⟩
  have hpos := hconf c hc.1 γ h0 hγ
  have hud : ∀ s ∈ Icc (-c) c, HasDerivAt (fun r => ‖(γ r).2‖ ^ 2 + 1)
      (2 * ⟪(γ s).2, (q / m) • (E (γ s).1 + cross (γ s).2 (B (γ s).1))⟫) s := fun s hs =>
    (hasDerivAt_prod_snd (hγ s hs)).norm_sq.add_const 1
  have hub : ∀ s ∈ Icc (-c) c,
      |2 * ⟪(γ s).2, (q / m) • (E (γ s).1 + cross (γ s).2 (B (γ s).1))⟫| ≤
        κ * |‖(γ s).2‖ ^ 2 + 1| := by
    intro s hs
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(γ s).2‖ ^ 2 + 1), lorentz_power]
    have hV : 0 ≤ ‖(γ s).2‖ := norm_nonneg _
    have hEs : ‖E (γ s).1‖ ≤ |C| := (hC _ (hpos s hs)).trans (le_abs_self C)
    have h1 : |⟪(γ s).2, E (γ s).1⟫| ≤ ‖(γ s).2‖ * |C| :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hEs hV)
    have h2 : |2 * (q / m * ⟪(γ s).2, E (γ s).1⟫)| ≤ 2 * (|q / m| * (‖(γ s).2‖ * |C|)) := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) zero_le_two
    refine h2.trans ?_
    rw [hκ]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (q / m)) (abs_nonneg C))
      (sq_nonneg (‖(γ s).2‖ - 1))]
  have key := abs_le_gronwallBound_Icc hκ0 hc hud hub t ht
  simp only [h0] at key
  have hle := (le_abs_self _).trans key
  refine mk_mem_prod (hpos t ht) ?_
  rw [mem_closedBall_zero_iff]
  nlinarith [sq_nonneg (‖(γ t).2‖ - 1)]

/-- **Existence for all times and uniqueness under confinement.** Let `m ≠ 0`, `U` open, `E`
and `B` of class `C¹` on `U`, `x₀ ∈ U`, and let `K ⊆ U` be compact. If the position of every
integral curve of `lorentzEMField m q E B` from `(x₀, v₀)` on a symmetric interval of times
stays in `K`, there is a Lorentz orbit for all times with `x 0 = x₀`, `v 0 = v₀` whose
position stays in `K`, and every Lorentz orbit for all times with these initial data equals
it. No vector or scalar potential and no bound on the speed is assumed. -/
theorem lorentzOrbit_existsUnique_of_confined {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    {U K : Set Space} (hU : IsOpen U) (hE : ContDiffOn ℝ 1 E U) (hB : ContDiffOn ℝ 1 B U)
    (hK : IsCompact K) (hKU : K ⊆ U) {x₀ v₀ : Space} (hx₀ : x₀ ∈ U)
    (hconf : ∀ c : ℝ, 0 ≤ c → ∀ γ : ℝ → Space × Space, γ 0 = (x₀, v₀) →
      (∀ t ∈ Icc (-c) c, HasDerivAt γ (lorentzEMField m q E B (γ t)) t) →
      ∀ t ∈ Icc (-c) c, (γ t).1 ∈ K) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧ (∀ t, x t ∈ K) ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨x, v, horb, hx0, hv0, -, huniq⟩ := lorentzOrbit_existsUnique_of_apriori_on hm hU hE
    hB hx₀ (lorentzEM_apriori_of_confined m q B hK hKU (hE.continuousOn.mono hKU) x₀ v₀ hconf)
  refine ⟨x, v, horb, hx0, hv0, fun t => ?_, huniq⟩
  exact hconf |t| (abs_nonneg t) (fun r => (x r, v r)) (by rw [hx0, hv0])
    (fun r _ => (horb.on univ).hasDerivAt_lorentzEMField hm (mem_univ r)) t
    ⟨neg_abs_le t, le_abs_self t⟩

/-! ## Extensions to all of space, and the case `U = Space` -/

/-- **Orbits from a `C¹` extension.** Let `m ≠ 0`, `U` open, and let `E`, `B` agree on `U` with
fields `E'`, `B'` that are `C¹` on all of space, `‖E' y‖ ≤ a + b ‖y‖`. The orbit `(x, v)` of
`(E', B')` for all times from `(x₀, v₀)` has the following property: on every order-connected
set of times `s ∋ 0` on which `x` stays in `U`, it is a Lorentz orbit of `(E, B)`, and every
Lorentz orbit of `(E, B)` on `s` with the same initial data that stays in `U` agrees with it
on `s`. -/
theorem lorentzOrbitOn_existsUnique_of_extension {m q : ℝ} (hm : m ≠ 0)
    {E B E' B' : Space → Space} {U : Set Space} (hU : IsOpen U) (hE' : ContDiff ℝ 1 E')
    (hB' : ContDiff ℝ 1 B') (hE : EqOn E E' U) (hB : EqOn B B' U) {a b : ℝ}
    (hgrow : ∀ y, ‖E' y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E' B' x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ s : Set ℝ, s.OrdConnected → 0 ∈ s → (∀ t ∈ s, x t ∈ U) →
        LorentzOrbitOn m q E B x v s ∧
          ∀ x' v' : ℝ → Space, LorentzOrbitOn m q E B x' v' s → (∀ t ∈ s, x' t ∈ U) →
            x' 0 = x₀ → v' 0 = v₀ → EqOn x' x s ∧ EqOn v' v s := by
  obtain ⟨x, v, horb, hx0, hv0, -⟩ :=
    lorentzOrbit_existsUnique_of_linear_growth hm hE' hB' hgrow x₀ v₀
  refine ⟨x, v, horb, hx0, hv0, fun s hs h0 hxU => ?_⟩
  have hon : LorentzOrbitOn m q E B x v s := (horb.on s).congr_fields hE hB hxU
  exact ⟨hon, fun x' v' h' hxU' hx' hv' =>
    lorentzOrbitOn_unique_of_contDiffOn hm hU (hE'.contDiffOn.congr fun y hy => hE hy)
      (hB'.contDiffOn.congr fun y hy => hB hy) hs h0 h' hon hxU' hxU (hx'.trans hx0.symm)
      (hv'.trans hv0.symm)⟩

/-- Consistency: the case `U = Space` of `lorentzOrbit_existsUnique_of_apriori_on` gives the
statement of `lorentzOrbit_existsUnique_of_linear_growth` (`E`, `B` of class `C¹` on all of
space, `E` of linear growth, no potential); for `E = 0` this contains `lorentzOrbit_exists`
with uniqueness. -/
theorem lorentzOrbit_existsUnique_of_linear_growth' {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) {a b : ℝ}
    (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨x, v, horb, hx0, hv0, -, huniq⟩ := lorentzOrbit_existsUnique_of_apriori_on hm
    isOpen_univ hE.contDiffOn hB.contDiffOn (mem_univ x₀) (v₀ := v₀)
    (by rw [univ_prod_univ]; exact lorentzEM_apriori_of_linear_growth m q B hgrow x₀ v₀)
  exact ⟨x, v, horb, hx0, hv0, huniq⟩

end PlasmaLean.Kinetic
