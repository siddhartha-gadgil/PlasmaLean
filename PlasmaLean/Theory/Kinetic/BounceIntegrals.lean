/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BounceOrbits
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Bounce integrals without singular endpoints, and periodicity of reference orbits (rung M4)

Companion to `notes/theory/near-qa-trapped-particles.md` (target T4, steps 2–3). Two generic
tools for trapped-orbit integrals along **supplied** trajectories.

**1. Cell comparison for time integrals (no inverse-square-root singularities).** A bounce
integral `∫ Ω dt` is usually written as `∮ Ω dθ / θ̇`, which is singular where `θ̇ = 0`. Here the
integral is never transformed: on a stretch where some monotone coordinate `x(t)` moves
(`ẋ ≥ 0`), a pointwise bound `Ω ≤ M_i ẋ` whenever `x(t)` lies in the `i`-th cell
`[i h, (i+1) h]` integrates to `∫ Ω dt ≤ h Σ M_i` (`integral_le_cell_sum`; the decreasing
version is `integral_le_cell_sum_rev`). Near a turning point of a banana orbit the parallel
gyroradius `ρ` (equivalently the flux `ψ`) is such a coordinate even though `θ̇` may vanish there,
so the cell bounds stay finite. Where instead `θ` is monotone, `Ω ≤ M (−θ̇)` gives
`∫ Ω ≤ M (θ(a) − θ(b))` (`integral_le_mul_drop`, with the lower bound
`mul_drop_le_integral`).

**2. Periodicity of autonomous reference orbits.** `periodic_of_return`: for an autonomous ODE
`ẏ = v(y)` whose right-hand side is Lipschitz on a set containing the solution, a return
`y(P) = y(0)` forces `y(t + kP) = y(t)` (Mathlib's Grönwall uniqueness
`ODE_solution_unique_of_mem_Icc_right`). `shift_of_periodic` then transports an additive
quantity with `ż = w(y)` (the toroidal angle): `z(t + kP) = z(t) + k (z(P) − z(0))`.

**3. Kick form with an explicit amplitude.** `periodic_kick_form_le` and
`bounce_drift_of_reference_le` are the versions of `periodic_kick_form` /
`bounce_drift_of_reference` with the amplitude bounded by `A ≤ 2 ∫ |g|` over one period.

Sanity: `cell_sum_fixture` (the comparison applied to `Ω = ẋ = 1`), `periodic_const_fixture`.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open Real Set Filter Topology

/-! ## Cell comparison -/

/-- A function with nonnegative derivative on `[a, b]` is monotone there. -/
theorem monotoneOn_of_hasDerivAt_nonneg {x x' : ℝ → ℝ} {a b : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a b, 0 ≤ x' t) :
    MonotoneOn x (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := x') (convex_Icc a b)
    (fun t ht => (hx t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · exact (hx t (interior_subset ht)).hasDerivWithinAt
  · exact hx'0 t (interior_subset ht)

/-- One cell: if `Ω ≤ M ẋ` on `[c, d]` then `∫_c^d Ω ≤ M (x d − x c)`. -/
theorem integral_le_mul_sub {Ω x x' : ℝ → ℝ} {c d M : ℝ} (hcd : c ≤ d)
    (hx : ∀ t ∈ Icc c d, HasDerivAt x (x' t) t)
    (hΩ : ContinuousOn Ω (Icc c d)) (hx'c : ContinuousOn x' (Icc c d))
    (hb : ∀ t ∈ Icc c d, Ω t ≤ M * x' t) :
    ∫ t in c..d, Ω t ≤ M * (x d - x c) := by
  have hu : uIcc c d = Icc c d := uIcc_of_le hcd
  have h1 : IntervalIntegrable Ω MeasureTheory.volume c d := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hΩ
  have h2 : IntervalIntegrable x' MeasureTheory.volume c d := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hx'c
  have hmono := intervalIntegral.integral_mono_on hcd h1 (h2.const_mul M) hb
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hx t (hu ▸ ht)) h2] at hmono
  exact hmono

/-- Helper for `integral_le_cell_sum`: induction on the number of cells, with the right
endpoint ranging over `[a, B]`. -/
theorem integral_le_cell_sum_aux {Ω x x' : ℝ → ℝ} {a B h : ℝ} {M : ℕ → ℝ} (hh : 0 < h)
    (hx : ∀ t ∈ Icc a B, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a B, 0 ≤ x' t)
    (hΩ : ContinuousOn Ω (Icc a B)) (hx'c : ContinuousOn x' (Icc a B)) (hxa : x a = 0)
    (hM : ∀ i, 0 ≤ M i)
    (hcell : ∀ t ∈ Icc a B, ∀ i : ℕ, x t ∈ Icc (i * h) ((i + 1) * h) → Ω t ≤ M i * x' t) :
    ∀ n : ℕ, ∀ b ∈ Icc a B, x b ≤ (n + 1) * h →
      ∫ t in a..b, Ω t ≤ h * ∑ i ∈ Finset.range (n + 1), M i := by
  have hmono := monotoneOn_of_hasDerivAt_nonneg hx hx'0
  have haB : ∀ b ∈ Icc a B, Icc a b ⊆ Icc a B := fun b hb => Icc_subset_Icc le_rfl hb.2
  -- one-cell estimate on a subinterval `[c, d] ⊆ [a, B]`
  have one : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ B → ∀ i : ℕ,
      (∀ t ∈ Icc c d, x t ∈ Icc (i * h) ((i + 1) * h)) →
      ∫ t in c..d, Ω t ≤ M i * (x d - x c) := by
    intro c d hac hcd hdB i hin
    have hs : Icc c d ⊆ Icc a B := Icc_subset_Icc hac hdB
    exact integral_le_mul_sub hcd (fun t ht => hx t (hs ht)) (hΩ.mono hs) (hx'c.mono hs)
      (fun t ht => hcell t (hs ht) i (hin t ht))
  intro n
  induction n with
  | zero =>
    intro b hb hxb
    have hin : ∀ t ∈ Icc a b, x t ∈ Icc (((0 : ℕ) : ℝ) * h) ((((0 : ℕ) : ℝ) + 1) * h) := by
      intro t ht
      have h1 : x a ≤ x t := hmono ⟨le_rfl, hb.1.trans hb.2⟩ (haB b hb ht) ht.1
      have h2 : x t ≤ x b := hmono (haB b hb ht) ⟨hb.1, hb.2⟩ ht.2
      push_cast at hxb ⊢
      constructor <;> linarith
    have := one a b le_rfl hb.1 hb.2 0 hin
    rw [hxa, sub_zero] at this
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero] at this hxb ⊢
    nlinarith [hM 0]
  | succ n ih =>
    intro b hb hxb
    have hsum : h * ∑ i ∈ Finset.range (n + 1 + 1), M i =
        h * ∑ i ∈ Finset.range (n + 1), M i + h * M (n + 1) := by
      rw [Finset.sum_range_succ]; ring
    rcases le_or_gt (x b) ((n + 1) * h) with hle | hgt
    · have := ih b hb hle
      rw [hsum]; nlinarith [hM (n + 1)]
    · -- the time `c` at which `x` reaches the cell boundary `(n+1) h`
      have hxc : ContinuousOn x (Icc a b) :=
        fun t ht => (hx t (haB b hb ht)).continuousAt.continuousWithinAt
      have hlev : ((n : ℝ) + 1) * h ∈ Icc (x a) (x b) := by
        rw [hxa]; exact ⟨by positivity, hgt.le⟩
      obtain ⟨c, hc, hxc'⟩ := intermediate_value_Icc hb.1 hxc hlev
      have hcB : c ∈ Icc a B := haB b hb hc
      have h1 := ih c hcB (by rw [hxc'])
      have hin : ∀ t ∈ Icc c b,
          x t ∈ Icc (((n + 1 : ℕ) : ℝ) * h) ((((n + 1 : ℕ) : ℝ) + 1) * h) := by
        intro t ht
        have htI : t ∈ Icc a B := ⟨hc.1.trans ht.1, ht.2.trans hb.2⟩
        have e1 : x c ≤ x t := hmono hcB htI ht.1
        have e2 : x t ≤ x b := hmono htI ⟨hb.1, hb.2⟩ ht.2
        push_cast at hxb ⊢
        constructor <;> linarith
      have h2 := one c b hc.1 hc.2 hb.2 (n + 1) hin
      have hsplit : ∫ t in a..b, Ω t = (∫ t in a..c, Ω t) + ∫ t in c..b, Ω t := by
        have hi : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ B →
            IntervalIntegrable Ω MeasureTheory.volume u v := by
          intro u v hau huv hvB
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le huv]; exact hΩ.mono (Icc_subset_Icc hau hvB)
        rw [intervalIntegral.integral_add_adjacent_intervals (hi a c le_rfl hc.1 hcB.2)
          (hi c b hc.1 hc.2 hb.2)]
      rw [hsplit, hsum]
      have : M (n + 1) * (x b - x c) ≤ h * M (n + 1) := by
        rw [hxc']; push_cast at hxb
        nlinarith [hM (n + 1)]
      linarith

/-- **Cell comparison, increasing coordinate.** Let `x` have derivative `x' ≥ 0` on `[a, b]`,
`x a = 0`, `x b ≤ (n+1) h`, and suppose that whenever `x t` lies in the cell
`[i h, (i+1) h]` the integrand satisfies `Ω t ≤ M i · x' t` (`M i ≥ 0`). Then
`∫_a^b Ω ≤ h Σ_{i ≤ n} M i`. No division by `x'` occurs, so `x'` may vanish. -/
theorem integral_le_cell_sum {Ω x x' : ℝ → ℝ} {a b h : ℝ} {M : ℕ → ℝ} {n : ℕ} (hab : a ≤ b)
    (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t) (hx'0 : ∀ t ∈ Icc a b, 0 ≤ x' t)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxa : x a = 0)
    (hxb : x b ≤ (n + 1) * h) (hM : ∀ i, 0 ≤ M i)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, x t ∈ Icc (i * h) ((i + 1) * h) → Ω t ≤ M i * x' t) :
    ∫ t in a..b, Ω t ≤ h * ∑ i ∈ Finset.range (n + 1), M i :=
  integral_le_cell_sum_aux hh hx hx'0 hΩ hx'c hxa hM hcell n b ⟨hab, le_rfl⟩ hxb

/-- **Cell comparison, decreasing coordinate.** If `x' ≤ 0` on `[a, b]`, `x b = 0`,
`x a ≤ (n+1) h`, and `Ω t ≤ M i · (−x' t)` whenever `x t ∈ [i h, (i+1) h]`, then
`∫_a^b Ω ≤ h Σ_{i ≤ n} M i` (time reversal of `integral_le_cell_sum`). -/
theorem integral_le_cell_sum_rev {Ω x x' : ℝ → ℝ} {a b h : ℝ} {M : ℕ → ℝ} {n : ℕ}
    (hab : a ≤ b) (hh : 0 < h) (hx : ∀ t ∈ Icc a b, HasDerivAt x (x' t) t)
    (hx'0 : ∀ t ∈ Icc a b, x' t ≤ 0)
    (hΩ : ContinuousOn Ω (Icc a b)) (hx'c : ContinuousOn x' (Icc a b)) (hxb : x b = 0)
    (hxa : x a ≤ (n + 1) * h) (hM : ∀ i, 0 ≤ M i)
    (hcell : ∀ t ∈ Icc a b, ∀ i : ℕ, x t ∈ Icc (i * h) ((i + 1) * h) → Ω t ≤ M i * -x' t) :
    ∫ t in a..b, Ω t ≤ h * ∑ i ∈ Finset.range (n + 1), M i := by
  have hneg : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b := fun s hs => ⟨by linarith [hs.2], by
    linarith [hs.1]⟩
  have key := integral_le_cell_sum (Ω := fun s => Ω (-s)) (x := fun s => x (-s))
    (x' := fun s => -x' (-s)) (a := -b) (b := -a) (h := h) (M := M) (n := n)
    (by linarith) hh
    (fun s hs => by
      have := (hx (-s) (hneg s hs)).comp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this)
    (fun s hs => by simpa using hx'0 (-s) (hneg s hs))
    (hΩ.comp continuousOn_neg (fun s hs => hneg s hs))
    ((hx'c.comp continuousOn_neg (fun s hs => hneg s hs)).neg)
    (by simpa using hxb) (by simpa using hxa) hM
    (fun s hs i hi => hcell (-s) (hneg s hs) i hi)
  rwa [intervalIntegral.integral_comp_neg (fun s => Ω s), neg_neg, neg_neg] at key

/-- **Monotone-angle bound.** If `Ω ≤ M · (−θ')` on `[a, b]` then
`∫_a^b Ω ≤ M (θ a − θ b)`. -/
theorem integral_le_mul_drop {Ω θ θ' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (θ' t) t)
    (hΩ : ContinuousOn Ω (Icc a b)) (hθc : ContinuousOn θ' (Icc a b))
    (hb : ∀ t ∈ Icc a b, Ω t ≤ M * -θ' t) :
    ∫ t in a..b, Ω t ≤ M * (θ a - θ b) := by
  have := integral_le_mul_sub (x := fun t => -θ t) (x' := fun t => -θ' t) hab
    (fun t ht => (hθ t ht).neg) hΩ hθc.neg hb
  linarith

/-- **Monotone-angle lower bound.** If `M · (−θ') ≤ Ω` on `[a, b]` then
`M (θ a − θ b) ≤ ∫_a^b Ω`. -/
theorem mul_drop_le_integral {Ω θ θ' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (θ' t) t)
    (hΩ : ContinuousOn Ω (Icc a b)) (hθc : ContinuousOn θ' (Icc a b))
    (hb : ∀ t ∈ Icc a b, M * -θ' t ≤ Ω t) :
    M * (θ a - θ b) ≤ ∫ t in a..b, Ω t := by
  have := integral_le_mul_drop (Ω := fun t => -Ω t) (M := -M) hab hθ hΩ.neg hθc
    (fun t ht => by have := hb t ht; linarith)
  rw [intervalIntegral.integral_neg] at this
  linarith

/-! ## Periodicity of autonomous reference orbits -/

section Periodic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Return implies periodicity** (autonomous ODE uniqueness). Let `y` solve `ẏ = v(y)` on
`[0, T]`, stay in a set `s` on which `v` is `K`-Lipschitz, and return, `y P = y 0` with
`0 < P`. Then `y (t + P) = y t` for `t ∈ [0, T − P]`. -/
theorem periodic_of_return {v : E → E} {s : Set E} {K : NNReal} {y : ℝ → E} {T P : ℝ}
    (hv : LipschitzOnWith K v s) (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (v (y t)) t)
    (hys : ∀ t ∈ Icc 0 T, y t ∈ s) (hP : 0 < P) (hret : y P = y 0) :
    ∀ t ∈ Icc 0 (T - P), y (t + P) = y t := by
  intro t ht
  have hTP : 0 ≤ T - P := ht.1.trans ht.2
  have hsub : ∀ u ∈ Icc 0 (T - P), u ∈ Icc 0 T := fun u hu =>
    ⟨hu.1, by linarith [hu.2]⟩
  have hsubP : ∀ u ∈ Icc 0 (T - P), u + P ∈ Icc 0 T := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => v) (s := fun _ => s) (K := K)
    (f := fun u => y (u + P)) (g := y) (a := 0) (b := T - P)
    (fun _ _ => hv)
    (fun u hu => (HasDerivAt.comp_add_const u P
      (hy (u + P) (hsubP u hu))).continuousAt.continuousWithinAt)
    (fun u hu => (HasDerivAt.comp_add_const u P
      (hy (u + P) (hsubP u (Ico_subset_Icc_self hu)))).hasDerivWithinAt)
    (fun u hu => hys _ (hsubP u (Ico_subset_Icc_self hu)))
    (fun u hu => (hy u (hsub u hu)).continuousAt.continuousWithinAt)
    (fun u hu => (hy u (hsub u (Ico_subset_Icc_self hu))).hasDerivWithinAt)
    (fun u hu => hys u (hsub u (Ico_subset_Icc_self hu)))
    (by simpa using hret)
  exact this ht

/-- Iterated return: under the hypotheses of `periodic_of_return`,
`y (t + k P) = y t` whenever `0 ≤ t` and `t + k P ≤ T`. -/
theorem periodic_of_return_iter {v : E → E} {s : Set E} {K : NNReal} {y : ℝ → E} {T P : ℝ}
    (hv : LipschitzOnWith K v s) (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (v (y t)) t)
    (hys : ∀ t ∈ Icc 0 T, y t ∈ s) (hP : 0 < P) (hret : y P = y 0) :
    ∀ k : ℕ, ∀ t, 0 ≤ t → t + k * P ≤ T → y (t + k * P) = y t := by
  intro k
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht htk
    have e : t + ((k + 1 : ℕ) : ℝ) * P = (t + k * P) + P := by push_cast; ring
    rw [e, periodic_of_return hv hy hys hP hret (t + k * P)
      ⟨by positivity, by push_cast at htk; linarith⟩]
    exact ih t ht (by push_cast at htk; nlinarith)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Additive drift along a periodic orbit.** If `ż = w(y)` on `[0, T]` and `y (t + P) = y t`
on `[0, T − P]`, then
`z (t + k P) = z t + k (z P − z 0)` whenever `0 ≤ t` and `t + k P ≤ T`. -/
theorem shift_of_periodic {w : E → ℝ} {y : ℝ → E} {z : ℝ → ℝ} {T P : ℝ} (hP : 0 < P)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (w (y t)) t)
    (hper : ∀ t ∈ Icc 0 (T - P), y (t + P) = y t) :
    ∀ k : ℕ, ∀ t, 0 ≤ t → t + k * P ≤ T → z (t + k * P) = z t + k * (z P - z 0) := by
  -- first: `z (t + P) − z t` is constant on `[0, T − P]`
  have hconst : ∀ t ∈ Icc 0 (T - P), z (t + P) - z t = z P - z 0 := by
    intro t ht
    have hTP : 0 ≤ T - P := ht.1.trans ht.2
    have hd : ∀ u ∈ Icc 0 (T - P), HasDerivAt (fun u => z (u + P) - z u) 0 u := by
      intro u hu
      have h1 := HasDerivAt.comp_add_const u P
        (hz (u + P) ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      have h2 := hz u ⟨hu.1, by linarith [hu.2]⟩
      have := h1.sub h2
      rwa [hper u hu, sub_self] at this
    have hcont : ContinuousOn (fun u => z (u + P) - z u) (Icc 0 (T - P)) :=
      fun u hu => (hd u hu).continuousAt.continuousWithinAt
    have := constant_of_has_deriv_right_zero hcont
      (fun u hu => (hd u (Ico_subset_Icc_self hu)).hasDerivWithinAt) t ht
    simpa using this
  intro k
  induction k with
  | zero => intro t _ _; simp
  | succ k ih =>
    intro t ht htk
    have e : t + ((k + 1 : ℕ) : ℝ) * P = (t + k * P) + P := by push_cast; ring
    have hk := ih t ht (by push_cast at htk; nlinarith)
    have h1 := hconst (t + k * P) ⟨by positivity, by push_cast at htk; linarith⟩
    rw [e]; push_cast
    linarith

end Periodic

/-! ## Kick form with an explicit amplitude bound -/

/-- `a cos x + b sin x = A sin(x + β)` with `0 ≤ A ≤ |a| + |b|`. -/
theorem exists_amp_phase_le (a b : ℝ) :
    ∃ A β : ℝ, 0 ≤ A ∧ A ≤ |a| + |b| ∧ ∀ x, a * cos x + b * sin x = A * sin (x + β) := by
  refine ⟨‖(⟨b, a⟩ : ℂ)‖, Complex.arg ⟨b, a⟩, norm_nonneg _, ?_, fun x => ?_⟩
  · have := Complex.norm_le_abs_re_add_abs_im (⟨b, a⟩ : ℂ)
    simp only at this; linarith
  · have h1 := Complex.norm_mul_cos_arg (⟨b, a⟩ : ℂ)
    have h2 := Complex.norm_mul_sin_arg (⟨b, a⟩ : ℂ)
    simp only at h1 h2
    rw [sin_add]
    linear_combination (-(sin x)) * h1 - cos x * h2

/-- **Kick form with explicit amplitude.** As `periodic_kick_form`, and moreover the amplitude
satisfies `A ≤ 2 ∫_{t₀}^{t₀+P} |g|`. -/
theorem periodic_kick_form_le {g φ : ℝ → ℝ} {t₀ P Δ : ℝ} (hP : 0 ≤ P)
    (hgc : ContinuousOn g (Icc t₀ (t₀ + P))) (hφc : ContinuousOn φ (Icc t₀ (t₀ + P)))
    (hg : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), g (t + k * P) = g t)
    (hφ : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), φ (t + k * P) = φ t + k * Δ) :
    ∃ A β : ℝ, 0 ≤ A ∧ A ≤ 2 * ∫ t in t₀..(t₀ + P), |g t| ∧ ∀ k : ℕ,
      ∫ t in (t₀ + k * P)..(t₀ + (k + 1) * P), g t * sin (2 * φ t) =
        A * sin (k * (2 * Δ) + β) := by
  set Sn := ∫ t in t₀..(t₀ + P), g t * sin (2 * φ t)
  set Cs := ∫ t in t₀..(t₀ + P), g t * cos (2 * φ t)
  obtain ⟨A, β, hA, hAle, hAβ⟩ := exists_amp_phase_le Sn Cs
  have hsub : uIcc t₀ (t₀ + P) = Icc t₀ (t₀ + P) := uIcc_of_le (by linarith)
  have hS : ContinuousOn (fun t => g t * sin (2 * φ t)) (uIcc t₀ (t₀ + P)) := by
    rw [hsub]; exact hgc.mul (continuous_sin.comp_continuousOn (continuousOn_const.mul hφc))
  have hC : ContinuousOn (fun t => g t * cos (2 * φ t)) (uIcc t₀ (t₀ + P)) := by
    rw [hsub]; exact hgc.mul (continuous_cos.comp_continuousOn (continuousOn_const.mul hφc))
  have hgabs : IntervalIntegrable (fun t => |g t|) MeasureTheory.volume t₀ (t₀ + P) := by
    apply ContinuousOn.intervalIntegrable; rw [hsub]; exact hgc.abs
  have hbound : ∀ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) →
      IntervalIntegrable (fun t => g t * f t) MeasureTheory.volume t₀ (t₀ + P) →
      |∫ t in t₀..(t₀ + P), g t * f t| ≤ ∫ t in t₀..(t₀ + P), |g t| := by
    intro f hf hi
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    refine intervalIntegral.integral_mono_on (by linarith) hi.abs hgabs (fun t _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf t)
  have h1 := hbound (fun t => sin (2 * φ t)) (fun t => abs_sin_le_one _) hS.intervalIntegrable
  have h2 := hbound (fun t => cos (2 * φ t)) (fun t => abs_cos_le_one _) hC.intervalIntegrable
  refine ⟨A, β, hA, by linarith, fun k => ?_⟩
  rw [← hAβ]
  have e1 := intervalIntegral.integral_comp_add_right
    (fun t => g t * sin (2 * φ t)) (a := t₀) (b := t₀ + P) (k * P)
  rw [show t₀ + ((k : ℝ) + 1) * P = t₀ + P + k * P by ring, ← e1]
  rw [intervalIntegral.integral_congr (g := fun t => cos (k * (2 * Δ)) * (g t * sin (2 * φ t)) +
    sin (k * (2 * Δ)) * (g t * cos (2 * φ t))) ?_]
  · rw [intervalIntegral.integral_add (hS.intervalIntegrable.const_mul _)
      (hC.intervalIntegrable.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [hsub] at ht
    simp only
    rw [hg k t ht, hφ k t ht, show 2 * (φ t + k * Δ) = 2 * φ t + k * (2 * Δ) by ring, sin_add]
    ring

/-- **Drift theorem with a periodic reference orbit and explicit amplitude.** As
`bounce_drift_of_reference`, with the amplitude bounded by `A ≤ 2 ∫_{t₀}^{t₀+P} |g|`. -/
theorem bounce_drift_of_reference_le {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T R t₀ P Δ : ℝ}
    {g φr : ℝ → ℝ} {τ : ℕ → ℝ} {N : ℕ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0) (hNT : τ N ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Icc 0 T))
    (hB : ∀ k ≤ N, 0 < along F.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity F m q ψ θ φ ρ (τ k) = 0)
    (hP : 0 ≤ P) (hgc : ContinuousOn g (Icc t₀ (t₀ + P)))
    (hφc : ContinuousOn φr (Icc t₀ (t₀ + P)))
    (hg : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), g (t + k * P) = g t)
    (hφ : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), φr (t + k * P) = φr t + k * Δ)
    (hΔ : sin Δ ≠ 0)
    (hclose : ∀ k < N, |(∫ t in τ k..τ (k + 1), qaKick F m q μ ψ θ φ ρ t) -
      ∫ t in (t₀ + k * P)..(t₀ + (k + 1) * P), g t * sin (2 * φr t)| ≤ R) :
    |q| * |F.ψp (ψ (τ N)) - F.ψp (ψ (τ 0))| ≤
      2 * (∫ t in t₀..(t₀ + P), |g t|) / |sin Δ| + N * R := by
  obtain ⟨A, β, hA, hAle, hkick⟩ := periodic_kick_form_le hP hgc hφc hg hφ
  have hα : sin (2 * Δ / 2) ≠ 0 := by rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have := bounce_drift_nonresonant (A := A) (α := 2 * Δ) (β := β) (R := R) hm hq hG h hτ h0 hNT
    hc hB hv hα (fun k hk => by rw [← hkick k]; exact hclose k hk)
  rw [mul_div_cancel_left₀ _ two_ne_zero, abs_of_nonneg hA] at this
  refine this.trans ?_
  gcongr

/-! ## Sanity checks -/

/-- Sanity (`integral_le_cell_sum`, accepted fixture): with `x t = t − a`, `Ω = ẋ = 1` and one
cell of width `h = b − a`, the comparison gives `∫_a^b 1 ≤ h · 1` (equality holds). -/
theorem cell_sum_fixture {a b : ℝ} (hab : a < b) : ∫ _t in a..b, (1 : ℝ) ≤ (b - a) * 1 := by
  have := integral_le_cell_sum (Ω := fun _ => (1 : ℝ)) (x := fun t => t - a)
    (x' := fun _ => 1) (h := b - a) (M := fun _ => 1) (n := 0) hab.le (by linarith)
    (fun t _ => (hasDerivAt_id t).sub_const a) (fun _ _ => zero_le_one) continuousOn_const
    continuousOn_const (by ring) (by push_cast; linarith) (fun _ => zero_le_one)
    (fun _ _ _ _ => by norm_num)
  simp only [zero_add, Finset.range_one, Finset.sum_singleton] at this
  exact this

/-- Sanity (`periodic_of_return`): a constant trajectory of the zero field returns and is
periodic with any period. -/
theorem periodic_const_fixture (c : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) (2 - 1), (fun _ : ℝ => c) (t + 1) = (fun _ : ℝ => c) t :=
  periodic_of_return (v := fun _ : ℝ => (0 : ℝ)) (s := univ) (K := 0) (T := 2)
    (LipschitzWith.const 0).lipschitzOnWith (fun t _ => hasDerivAt_const t c)
    (fun _ _ => mem_univ _) one_pos rfl

end PlasmaLean.Kinetic.Boozer
