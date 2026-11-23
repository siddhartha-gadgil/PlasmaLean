/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CrossedFieldOrbit

/-!
# Global existence of Lorentz orbits in non-uniform fields with an electric field

The Newton–Lorentz equations `x' = v`, `m v' = q (E(x) + v × B(x))` are the first-order system
`y' = lorentzEMField m q E B y` on `Space × Space` (`Theory/Kinetic/CrossedFieldOrbit`). This
file proves existence for ALL times, and uniqueness, of the orbit through every initial position
and velocity, from two a priori bounds. No vector potential is used in the first two parts.

Hypotheses common to all results: `m ≠ 0`, and `E`, `B` are `C¹` on ALL of space
(`ContDiff ℝ 1`). The magnetic field is otherwise arbitrary: no bound, no growth condition, and
it need not be divergence free.

* Tools. `lorentzOrbitOn_of_flow`: an integral curve of `lorentzEMField` on a set of times is a
  `LorentzOrbitOn` there (`m ≠ 0`). `LorentzOrbitOn.energy_eq_Icc`: the energy
  `(m/2)‖v‖² + q Φ(x)` is constant along a Lorentz orbit on a closed interval of times, for
  `E = −∇Φ` (the interval version of `energy_conserved`; no hypothesis on `m`).
  `abs_le_gronwallBound_Icc`: a two-sided Grönwall bound for a real function on `[-c, c]`.
  `lorentzOrbit_existsUnique_of_apriori`: a priori bounds (`APrioriBounded`) for
  `lorentzEMField` give a unique orbit for all times.
* Electric field of linear growth, `‖E y‖ ≤ a + b ‖y‖`; `E` need not be a gradient.
  `lorentzEM_apriori_of_linear_growth`: since the magnetic force does no work,
  `u = ‖x‖² + ‖v‖² + 1` satisfies `|u'| ≤ K u` with `K = |q/m| (|a| + |b|) + 1`, hence
  `u(t) ≤ u(0) exp (K |t|)`.
  **`lorentzOrbit_existsUnique_of_linear_growth`**: a unique orbit for all times from every
  initial position and velocity.
* Conservative electric field with potential energy bounded below. For `E = −∇Φ` and
  `c ≤ (q/m) Φ` everywhere, energy conservation bounds the speed on every interval of existence
  (`lorentzEM_apriori_of_energy_bound`), so there is a unique orbit for all times:
  **`lorentzOrbit_existsUnique_of_energy_bound`**. The hypothesis on `(q/m) Φ` covers both
  signs of the mass: for `0 < m` it says that `q Φ` is bounded below
  (**`lorentzOrbit_existsUnique_of_potential_bounded_below`**), for `m < 0` that `q Φ` is
  bounded above (`lorentzOrbit_existsUnique_of_potential_bounded_above`). No growth condition
  on `E` or `B`.
* Hamiltonian formulation. `contDiff_fieldCurl`: `∇ × A` is `C¹` for `A` of class `C²`. For
  `A` of class `C²` on all of space, `B = ∇ × A`, `E = −∇Φ` of class `C¹`:
  **`emHamilton_existsUnique_of_potential_bounded_below`** (and `…_of_energy_bound`,
  `…_of_linear_growth`): through every point of phase space there is exactly one integral
  curve, defined for all times, of the Hamiltonian vector field of `emHamiltonian m q A Φ`.
  There is NO growth condition on `A`.

Relation to the earlier results (none of them is changed).

* `lorentzOrbit_exists` (`Theory/Kinetic/LorentzExistence`) and
  `lorentzOrbit_existsUnique_of_contDiff`: `E = 0`, `B` of class `C¹`. This is the case
  `a = b = 0` of the linear-growth theorem, re-derived here as
  `lorentzOrbit_existsUnique_magnetic`.
* `lorentzOrbit_existsUnique_linearGauge`: `B = ∇ × L` for a continuous linear `L` (so `B` is
  uniform), `E = −∇Φ` of linear growth. Re-derived here from the linear-growth theorem as
  `lorentzOrbit_existsUnique_linearGauge'`, without the hypothesis that `E` is a gradient.
  `lorentzOrbit_existsUnique_uniform'` is the case of uniform `E` and `B`.
* `emHamilton_exists_global` allows `m = 0` (where Lean's division makes the kinetic term
  vanish); the Hamiltonian theorems here assume `m ≠ 0`, and are otherwise more general
  (`A` of class `C²` instead of linear).

Not covered: fields defined or regular only on a region of space (a toroidal domain, the
complement of a wire); time-dependent fields; relativistic motion. The two growth hypotheses
cannot simply be dropped: for the potential `Φ = −y₀⁴/4` (`E = y₀³ e_x`, `B = 0`,
`m = q = 1`) the equation is `x'' = x³`, whose solutions with large initial data leave every
bounded set in finite time. That blow-up is not proved in this project;
`Sanity/LorentzGlobalExistence` only proves that this field violates both hypotheses.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Fields.ODEGlobal PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti InnerProductSpace Set WithLp
open scoped RealInnerProductSpace

/-! ## Integral curves, orbits on an interval, energy -/

/-- For `m ≠ 0`, an integral curve of `lorentzEMField m q E B` at the times of a set `s` is a
Lorentz orbit on `s` (position and velocity are its two components). The converse is
`LorentzOrbitOn.hasDerivAt_lorentzEMField`. -/
theorem lorentzOrbitOn_of_flow {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    {γ : ℝ → Space × Space} {s : Set ℝ}
    (hγ : ∀ t ∈ s, HasDerivAt γ (lorentzEMField m q E B (γ t)) t) :
    LorentzOrbitOn m q E B (fun t => (γ t).1) (fun t => (γ t).2) s where
  position t ht := hasDerivAt_prod_fst (hγ t ht)
  newton t ht := ⟨_, hasDerivAt_prod_snd (hγ t ht), by
    simp only [lorentzEMField, smul_smul]
    rw [mul_div_cancel₀ q hm]⟩

/-- **Energy conservation on an interval of times.** Along a Lorentz orbit on `[a, b]` in the
fields `E = −∇Φ` and `B`, the energy `(m/2)‖v‖² + q Φ(x)` takes the same value at all times of
`[a, b]`. Interval version of `energy_conserved`; no hypothesis on `m` or on `B`. -/
theorem LorentzOrbitOn.energy_eq_Icc {m q : ℝ} {E B : Space → Space} {Φ : Space → ℝ}
    {x v : ℝ → Space} {a b : ℝ} (h : LorentzOrbitOn m q E B x v (Icc a b))
    (hΦ : IsPotential Φ E) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    orbitEnergy m q Φ x v s = orbitEnergy m q Φ x v t := by
  have hd : ∀ r ∈ Icc a b, HasDerivAt (orbitEnergy m q Φ x v) 0 r := by
    intro r hr
    obtain ⟨acc, ha, hlaw⟩ := h.newton r hr
    have hk : HasDerivAt (fun u => m / 2 * ‖v u‖ ^ 2) (q * ⟪v r, E (x r)⟫) r := by
      have hn := (ha.norm_sq).const_mul (m / 2)
      convert hn using 1
      have : m / 2 * (2 * ⟪v r, acc⟫) = ⟪v r, m • acc⟫ := by
        rw [inner_smul_right]; ring
      rw [this, hlaw, lorentz_power]
    have hp : HasDerivAt (fun u => Φ (x u)) (-⟪E (x r), v r⟫) r := by
      have := (hΦ (x r)).comp_hasDerivAt r (h.position r hr)
      convert this using 1
      · rfl
      · simp
    change HasDerivAt (fun u => m / 2 * ‖v u‖ ^ 2 + q * Φ (x u)) 0 r
    convert hk.add (hp.const_mul q) using 1
    rw [real_inner_comm]; ring
  exact eq_of_hasDerivAt_zero_Icc hd hs ht

/-- **Two-sided Grönwall bound.** A real function `u` on `[-c, c]` (`0 ≤ c ≤ T`) with
`|u'| ≤ K |u|`, `0 ≤ K`, satisfies `|u t| ≤ gronwallBound |u 0| K 0 T` (that is,
`|u 0| exp (K T)`) on `[-c, c]`. -/
theorem abs_le_gronwallBound_Icc {u u' : ℝ → ℝ} {K c T : ℝ} (hK : 0 ≤ K) (hc : c ∈ Icc 0 T)
    (hu : ∀ t ∈ Icc (-c) c, HasDerivAt u (u' t) t)
    (hb : ∀ t ∈ Icc (-c) c, |u' t| ≤ K * |u t|) :
    ∀ t ∈ Icc (-c) c, |u t| ≤ gronwallBound |u 0| K 0 T := by
  have hmono := gronwallBound_mono (abs_nonneg (u 0)) (le_refl (0 : ℝ)) hK
  have hfw : ∀ w w' : ℝ → ℝ, w 0 = u 0 → (∀ s ∈ Icc 0 c, HasDerivAt w (w' s) s) →
      (∀ s ∈ Icc 0 c, |w' s| ≤ K * |w s|) →
      ∀ s ∈ Icc 0 c, |w s| ≤ gronwallBound |u 0| K 0 T := by
    intro w w' h0 hw hbw s hs
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := w) (f' := w')
      (δ := |u 0|) (K := K) (ε := 0) (a := 0) (b := c)
      (fun r hr => (hw r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hw r (Ico_subset_Icc_self hr)).hasDerivWithinAt)
      (by rw [h0, Real.norm_eq_abs])
      (fun r hr => by
        rw [add_zero, Real.norm_eq_abs, Real.norm_eq_abs]
        exact hbw r (Ico_subset_Icc_self hr)) s hs
    rw [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (hmono (hs.2.trans hc.2))
  intro t ht
  rcases le_total 0 t with h | h
  · exact hfw u u' rfl (fun s hs => hu s ⟨by linarith [hs.1, hc.1], hs.2⟩)
      (fun s hs => hb s ⟨by linarith [hs.1, hc.1], hs.2⟩) t ⟨h, ht.2⟩
  · have hmem : ∀ s ∈ Icc 0 c, -s ∈ Icc (-c) c := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1, hc.1]⟩
    have hrev : ∀ s ∈ Icc 0 c, HasDerivAt (fun r => u (-r)) (-u' (-s)) s := by
      intro s hs
      have h1 := (hu (-s) (hmem s hs)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using h1
    have h2 := hfw (fun r => u (-r)) (fun s => -u' (-s)) (by simp) hrev
      (fun s hs => by rw [abs_neg]; exact hb _ (hmem s hs)) (-t)
      ⟨by linarith, by linarith [ht.1]⟩
    simpa using h2

/-- **From a priori bounds to a unique global orbit.** Let `m ≠ 0` and `E`, `B` be `C¹` on all
of space. If the integral curves of `lorentzEMField m q E B` from `(x₀, v₀)` are a priori
bounded on every finite horizon, there is a Lorentz orbit for all times with `x 0 = x₀`,
`v 0 = v₀`, and every Lorentz orbit with these initial data equals it. -/
theorem lorentzOrbit_existsUnique_of_apriori {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) {x₀ v₀ : Space}
    (hbd : APrioriBounded (lorentzEMField m q E B) univ (x₀, v₀)) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_of_apriori isOpen_univ
    (contDiff_lorentzEMField m q hE hB).contDiffOn (mem_univ (x₀, v₀)) hbd
  have horb : LorentzOrbit m q E B (fun t => (γ t).1) (fun t => (γ t).2) :=
    lorentzOrbitOn_univ.mp (lorentzOrbitOn_of_flow hm fun t _ => hγ t)
  have hx0 : (γ 0).1 = x₀ := by rw [hγ0]
  have hv0 : (γ 0).2 = v₀ := by rw [hγ0]
  exact ⟨_, _, horb, hx0, hv0, fun x' v' h' hx' hv' =>
    lorentzOrbit_unique_of_contDiff hm hE hB h' horb (t₀ := 0)
      (hx'.trans hx0.symm) (hv'.trans hv0.symm)⟩

/-! ## Electric field of linear growth -/

/-- **A priori bound for an electric field of linear growth.** If `‖E y‖ ≤ a + b ‖y‖`, then
along an integral curve of `lorentzEMField m q E B` the function `u = ‖x‖² + ‖v‖² + 1` satisfies
`|u'| ≤ K u`, `K = |q/m| (|a| + |b|) + 1` (the magnetic force does no work), so `u` is bounded
by `u(0) exp (K T)` up to time `T`. No hypothesis on `B`, on the regularity of `E`, or on `m`
(for `m = 0` Lean's division makes the acceleration `0`). -/
theorem lorentzEM_apriori_of_linear_growth (m q : ℝ) {E : Space → Space} (B : Space → Space)
    {a b : ℝ} (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    APrioriBounded (lorentzEMField m q E B) univ (x₀, v₀) := by
  intro T
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |q / m| * |a| + |q / m| * |b| + 1 := ⟨_, rfl⟩
  have hα : 0 ≤ |q / m| * |a| := by positivity
  have hβ : 0 ≤ |q / m| * |b| := by positivity
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨Metric.closedBall 0 (gronwallBound |‖x₀‖ ^ 2 + ‖v₀‖ ^ 2 + 1| K 0 T),
    isCompact_closedBall _ _, subset_univ _, fun c hc γ h0 hγ t ht => ?_⟩
  have hud : ∀ s ∈ Icc (-c) c,
      HasDerivAt (fun r => ‖(γ r).1‖ ^ 2 + ‖(γ r).2‖ ^ 2 + 1)
        (2 * ⟪(γ s).1, (γ s).2⟫ +
          2 * ⟪(γ s).2, (q / m) • (E (γ s).1 + cross (γ s).2 (B (γ s).1))⟫) s := by
    intro s hs
    have hx : HasDerivAt (fun r => (γ r).1) (γ s).2 s := hasDerivAt_prod_fst (hγ s hs)
    have hv : HasDerivAt (fun r => (γ r).2)
        ((q / m) • (E (γ s).1 + cross (γ s).2 (B (γ s).1))) s := hasDerivAt_prod_snd (hγ s hs)
    exact (hx.norm_sq.add hv.norm_sq).add_const 1
  have hub : ∀ s ∈ Icc (-c) c,
      |2 * ⟪(γ s).1, (γ s).2⟫ +
          2 * ⟪(γ s).2, (q / m) • (E (γ s).1 + cross (γ s).2 (B (γ s).1))⟫| ≤
        K * |‖(γ s).1‖ ^ 2 + ‖(γ s).2‖ ^ 2 + 1| := by
    intro s _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(γ s).1‖ ^ 2 + ‖(γ s).2‖ ^ 2 + 1),
      lorentz_power]
    have hX : 0 ≤ ‖(γ s).1‖ := norm_nonneg _
    have hV : 0 ≤ ‖(γ s).2‖ := norm_nonneg _
    have hE' : ‖E (γ s).1‖ ≤ |a| + |b| * ‖(γ s).1‖ := (hgrow _).trans
      (add_le_add (le_abs_self a) (mul_le_mul_of_nonneg_right (le_abs_self b) hX))
    have h1 : |⟪(γ s).1, (γ s).2⟫| ≤ ‖(γ s).1‖ * ‖(γ s).2‖ := abs_real_inner_le_norm _ _
    have h2 : |q / m * ⟪(γ s).2, E (γ s).1⟫| ≤
        |q / m| * (‖(γ s).2‖ * (|a| + |b| * ‖(γ s).1‖)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hE' hV)) (abs_nonneg _)
    have h3 : |2 * ⟪(γ s).1, (γ s).2⟫ + 2 * (q / m * ⟪(γ s).2, E (γ s).1⟫)| ≤
        2 * (‖(γ s).1‖ * ‖(γ s).2‖) +
          2 * (|q / m| * (‖(γ s).2‖ * (|a| + |b| * ‖(γ s).1‖))) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_two]
      linarith
    refine h3.trans ?_
    rw [hKdef]
    linarith [mul_nonneg hα (sq_nonneg (‖(γ s).2‖ - 1)),
      mul_nonneg hβ (sq_nonneg (‖(γ s).1‖ - ‖(γ s).2‖)), sq_nonneg (‖(γ s).1‖ - ‖(γ s).2‖),
      mul_nonneg hα (sq_nonneg ‖(γ s).1‖)]
  have key := abs_le_gronwallBound_Icc hK0 hc hud hub t ht
  simp only [h0] at key
  have hX : 0 ≤ ‖(γ t).1‖ := norm_nonneg _
  have hV : 0 ≤ ‖(γ t).2‖ := norm_nonneg _
  have hle := (le_abs_self _).trans key
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (by nlinarith [sq_nonneg (‖(γ t).1‖ - 1), sq_nonneg ‖(γ t).2‖])
    (by nlinarith [sq_nonneg (‖(γ t).2‖ - 1), sq_nonneg ‖(γ t).1‖])

/-- **Global existence and uniqueness for an electric field of linear growth.** Let `m ≠ 0`,
let `E` and `B` be `C¹` on all of space, and `‖E y‖ ≤ a + b ‖y‖` for all `y`. For every initial
position `x₀` and velocity `v₀` there is a Lorentz orbit for all times with `x 0 = x₀`,
`v 0 = v₀`, and every Lorentz orbit with these initial data equals it. The magnetic field is
arbitrary (not uniform, no growth condition), and `E` need not be a gradient. -/
theorem lorentzOrbit_existsUnique_of_linear_growth {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) {a b : ℝ}
    (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_apriori hm hE hB
    (lorentzEM_apriori_of_linear_growth m q B hgrow x₀ v₀)

/-- Consistency: the case `E = 0` of `lorentzOrbit_existsUnique_of_linear_growth` is the
statement of `lorentzOrbit_existsUnique_of_contDiff` (existence: `lorentzOrbit_exists`). -/
theorem lorentzOrbit_existsUnique_magnetic {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    (hB : ContDiff ℝ 1 B) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_linear_growth hm contDiff_const hB (a := 0) (b := 0)
    (fun _ => by simp) x₀ v₀

/-- Consistency: `lorentzOrbit_existsUnique_linearGauge` follows from
`lorentzOrbit_existsUnique_of_linear_growth`, and the hypothesis that `E` is a gradient is not
needed. Here `B = ∇ × L` for a continuous linear `L`, so `B` is uniform. -/
theorem lorentzOrbit_existsUnique_linearGauge' {m q : ℝ} (hm : m ≠ 0) (L : Space →L[ℝ] Space)
    {E B : Space → Space} (hcurl : ∀ y, B y = fieldCurl L y) (hE : ContDiff ℝ 1 E) {a b : ℝ}
    (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  have hB : B = fun _ => curlOp L := funext fun y => by rw [hcurl, fieldCurl, L.fderiv]
  exact lorentzOrbit_existsUnique_of_linear_growth hm hE (hB ▸ contDiff_const) hgrow x₀ v₀

/-- Consistency: the statement of `lorentzOrbit_existsUnique_uniform` (arbitrary uniform `E`
and `B`) from `lorentzOrbit_existsUnique_of_linear_growth`, with no gauge. -/
theorem lorentzOrbit_existsUnique_uniform' {m : ℝ} (hm : m ≠ 0) (q : ℝ)
    (Ev Bv x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => Ev) (fun _ => Bv) x v ∧ x 0 = x₀ ∧
      v 0 = v₀ ∧ ∀ x' v' : ℝ → Space, LorentzOrbit m q (fun _ => Ev) (fun _ => Bv) x' v' →
        x' 0 = x₀ → v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_linear_growth hm contDiff_const contDiff_const (a := ‖Ev‖)
    (b := 0) (fun _ => by simp) x₀ v₀

/-! ## Conservative electric field with potential energy bounded below -/

/-- **A priori bound from the energy.** Let `m ≠ 0`, `E = −∇Φ` and `c₀ ≤ (q/m) Φ` everywhere.
Along an integral curve of `lorentzEMField m q E B` from `(x₀, v₀)` the conserved energy gives
`‖v‖² ≤ ‖v₀‖² + 2 ((q/m) Φ(x₀) − c₀)`, so the speed is at most
`S = ‖v₀‖² + 2 ((q/m) Φ(x₀) − c₀) + 1` and up to time `T` the position stays within `S T` of
`x₀`. No hypothesis on `B` and no regularity of `E` beyond `E = −∇Φ`. -/
theorem lorentzEM_apriori_of_energy_bound {m q : ℝ} (hm : m ≠ 0) {E : Space → Space}
    (B : Space → Space) {Φ : Space → ℝ} (hΦ : IsPotential Φ E) {c₀ : ℝ}
    (hlow : ∀ y, c₀ ≤ q / m * Φ y) (x₀ v₀ : Space) :
    APrioriBounded (lorentzEMField m q E B) univ (x₀, v₀) := by
  intro T
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ‖v₀‖ ^ 2 + 2 * (q / m * Φ x₀ - c₀) + 1 := ⟨_, rfl⟩
  refine ⟨Metric.closedBall x₀ (S * T) ×ˢ Metric.closedBall 0 S,
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _), subset_univ _,
    fun c hc γ h0 hγ t ht => ?_⟩
  have h0m : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith [hc.1], hc.1⟩
  have horb := lorentzOrbitOn_of_flow hm hγ
  have h0x : (γ 0).1 = x₀ := by rw [h0]
  have h0v : (γ 0).2 = v₀ := by rw [h0]
  have hsp : ∀ s ∈ Icc (-c) c, ‖(γ s).2‖ ≤ S := by
    intro s hs
    have hen := horb.energy_eq_Icc hΦ hs h0m
    simp only [orbitEnergy, h0x, h0v] at hen
    have hsq : ‖(γ s).2‖ ^ 2 = ‖v₀‖ ^ 2 + 2 * (q / m * Φ x₀ - q / m * Φ (γ s).1) := by
      field_simp
      linarith
    have hl := hlow (γ s).1
    nlinarith [sq_nonneg (‖(γ s).2‖ - 1), norm_nonneg (γ s).2]
  refine ⟨?_, by simpa using hsp t ht⟩
  have hmv := (convex_Icc (-c) c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => (γ s).1) (f' := fun s => (γ s).2) (C := S)
    (fun s hs => (hasDerivAt_prod_fst (hγ s hs)).hasDerivWithinAt) hsp h0m ht
  rw [h0x, sub_zero, Real.norm_eq_abs] at hmv
  rw [Metric.mem_closedBall, dist_eq_norm]
  have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1, hc.2], by linarith [ht.2, hc.2]⟩
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hsp 0 h0m)
  exact hmv.trans (mul_le_mul_of_nonneg_left habs hS0)

/-- **Global existence and uniqueness from an energy bound.** Let `m ≠ 0`, let `E` and `B` be
`C¹` on all of space, `E = −∇Φ`, and `c₀ ≤ (q/m) Φ y` for all `y`. For every initial position
`x₀` and velocity `v₀` there is a Lorentz orbit for all times with `x 0 = x₀`, `v 0 = v₀`, and
every Lorentz orbit with these initial data equals it. No growth condition on `E` or `B`. -/
theorem lorentzOrbit_existsUnique_of_energy_bound {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} {Φ : Space → ℝ} (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B)
    (hΦ : IsPotential Φ E) {c₀ : ℝ} (hlow : ∀ y, c₀ ≤ q / m * Φ y) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_apriori hm hE hB
    (lorentzEM_apriori_of_energy_bound hm B hΦ hlow x₀ v₀)

/-- **Global existence and uniqueness for a potential energy bounded below.** Let `0 < m`, let
`E` and `B` be `C¹` on all of space, `E = −∇Φ`, and `c ≤ q Φ y` for all `y`. For every initial
position `x₀` and velocity `v₀` there is a Lorentz orbit for all times with `x 0 = x₀`,
`v 0 = v₀`, and every Lorentz orbit with these initial data equals it. -/
theorem lorentzOrbit_existsUnique_of_potential_bounded_below {m q : ℝ} (hm : 0 < m)
    {E B : Space → Space} {Φ : Space → ℝ} (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B)
    (hΦ : IsPotential Φ E) {c : ℝ} (hlow : ∀ y, c ≤ q * Φ y) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_energy_bound hm.ne' hE hB hΦ (c₀ := c / m)
    (fun y => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hlow y) hm.le) x₀ v₀

/-- The case of negative mass: for `m < 0` the sign of the bound flips, and the hypothesis is
that `q Φ` is bounded ABOVE (`q Φ y ≤ c`); the conclusion is as in
`lorentzOrbit_existsUnique_of_potential_bounded_below`. -/
theorem lorentzOrbit_existsUnique_of_potential_bounded_above {m q : ℝ} (hm : m < 0)
    {E B : Space → Space} {Φ : Space → ℝ} (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B)
    (hΦ : IsPotential Φ E) {c : ℝ} (hup : ∀ y, q * Φ y ≤ c) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_energy_bound hm.ne hE hB hΦ (c₀ := c / m)
    (fun y => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonpos_of_le hm.le (hup y)) x₀ v₀

/-! ## Hamiltonian formulation -/

/-- The curl of a `C²` vector field is `C¹`. -/
theorem contDiff_fieldCurl {A : Space → Space} (hA : ContDiff ℝ 2 A) :
    ContDiff ℝ 1 (fieldCurl A) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (m := 1) (by norm_num)
  have hc : ∀ i j : Fin 3, ContDiff ℝ 1 (fun y => fderiv ℝ A y (coordVec j) i) := fun i j =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp (hD.clm_apply contDiff_const)
  refine contDiff_piLp' 2 fun i => ?_
  fin_cases i
  · exact (hc 2 1).sub (hc 1 2)
  · exact (hc 0 2).sub (hc 2 0)
  · exact (hc 1 0).sub (hc 0 1)

/-- **From global Lorentz orbits to global integral curves.** Let `m ≠ 0`, `A` be `C²` on all
of space and `E = −∇Φ` be `C¹`. If every initial position and velocity starts a Lorentz orbit
for all times in the fields `E` and `∇ × A`, then through every point `z₀` of phase space there
is exactly one integral curve, defined for all times, of the Hamiltonian vector field of
`emHamiltonian m q A Φ` (the canonical lift of the orbit; uniqueness is `emHamilton_unique`). -/
theorem emHamilton_existsUnique_of_lorentzOrbit {m q : ℝ} (hm : m ≠ 0) {A E : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E)
    (hex : ∀ x₀ v₀ : Space, ∃ x v : ℝ → Space,
      LorentzOrbit m q E (fieldCurl A) x v ∧ x 0 = x₀ ∧ v 0 = v₀) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧
      (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (z t)) t) ∧
      ∀ z' : ℝ → PhaseSpace, z' 0 = z₀ →
        (∀ t, HasDerivAt z'
          ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
            (emHamiltonian m q A Φ) (z' t)) t) → z' = z := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  obtain ⟨x, v, horb, hx0, hv0⟩ := hex z₀.1 (kineticVelocity m q A z₀)
  have hz := lorentzOrbit_emHamilton hm horb hAd (fun _ => rfl) hΦ
  have hz0 : canonicalCurve m q A x v 0 = z₀ := by
    have h := congrFun (canonicalCurve_kineticVelocity hm q A (fun _ => z₀)) 0
    simp only [canonicalCurve, canonicalCovector] at h ⊢
    rw [hx0, hv0]
    exact h
  exact ⟨_, hz0, hz, fun z' hz'0 hz' =>
    emHamilton_unique m q hA hE hΦ hz' hz (t₀ := 0) (hz'0.trans hz0.symm)⟩

/-- **Global integral curves from an energy bound.** Let `m ≠ 0`, `A` be `C²` on all of space,
`E = −∇Φ` be `C¹` and `c₀ ≤ (q/m) Φ y` for all `y`. Through every point of phase space there
is exactly one integral curve, defined for all times, of the Hamiltonian vector field of
`emHamiltonian m q A Φ`. There is no growth condition on `A`. -/
theorem emHamilton_existsUnique_of_energy_bound {m q : ℝ} (hm : m ≠ 0) {A E : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E)
    {c₀ : ℝ} (hlow : ∀ y, c₀ ≤ q / m * Φ y) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧
      (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (z t)) t) ∧
      ∀ z' : ℝ → PhaseSpace, z' 0 = z₀ →
        (∀ t, HasDerivAt z'
          ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
            (emHamiltonian m q A Φ) (z' t)) t) → z' = z :=
  emHamilton_existsUnique_of_lorentzOrbit hm hA hE hΦ (fun x₀ v₀ => by
    obtain ⟨x, v, h, hx, hv, -⟩ := lorentzOrbit_existsUnique_of_energy_bound hm hE
      (contDiff_fieldCurl hA) hΦ hlow x₀ v₀
    exact ⟨x, v, h, hx, hv⟩) z₀

/-- **Global integral curves for a potential energy bounded below.** Let `0 < m`, `A` be `C²`
on all of space, `E = −∇Φ` be `C¹` and `c ≤ q Φ y` for all `y`. Through every point of phase
space there is exactly one integral curve, defined for all times, of the Hamiltonian vector
field of `emHamiltonian m q A Φ`. There is no growth condition on `A`. -/
theorem emHamilton_existsUnique_of_potential_bounded_below {m q : ℝ} (hm : 0 < m)
    {A E : Space → Space} {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E)
    (hΦ : IsPotential Φ E) {c : ℝ} (hlow : ∀ y, c ≤ q * Φ y) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧
      (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (z t)) t) ∧
      ∀ z' : ℝ → PhaseSpace, z' 0 = z₀ →
        (∀ t, HasDerivAt z'
          ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
            (emHamiltonian m q A Φ) (z' t)) t) → z' = z :=
  emHamilton_existsUnique_of_energy_bound hm.ne' hA hE hΦ (c₀ := c / m)
    (fun y => by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hlow y) hm.le) z₀

/-- **Global integral curves for an electric field of linear growth.** Let `m ≠ 0`, `A` be
`C²` on all of space, `E = −∇Φ` be `C¹` with `‖E y‖ ≤ a + b ‖y‖`. Through every point of phase
space there is exactly one integral curve, defined for all times, of the Hamiltonian vector
field of `emHamiltonian m q A Φ`. For `m ≠ 0` this contains `emHamilton_exists_global`, where
`A` is linear; here there is no growth condition on `A`. -/
theorem emHamilton_existsUnique_of_linear_growth {m q : ℝ} (hm : m ≠ 0) {A E : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E)
    {a b : ℝ} (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧
      (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (z t)) t) ∧
      ∀ z' : ℝ → PhaseSpace, z' 0 = z₀ →
        (∀ t, HasDerivAt z'
          ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
            (emHamiltonian m q A Φ) (z' t)) t) → z' = z :=
  emHamilton_existsUnique_of_lorentzOrbit hm hA hE hΦ (fun x₀ v₀ => by
    obtain ⟨x, v, h, hx, hv, -⟩ := lorentzOrbit_existsUnique_of_linear_growth hm hE
      (contDiff_fieldCurl hA) hgrow x₀ v₀
    exact ⟨x, v, h, hx, hv⟩) z₀

end PlasmaLean.Kinetic
