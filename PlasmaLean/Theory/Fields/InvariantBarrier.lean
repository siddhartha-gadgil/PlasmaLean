/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FirstIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Invariant level sets as all-time Grönwall barriers (KAM route, stage K0)

Stage K0 of `notes/theory/kam-route.md` (§3, (B1)). Let `G` be differentiable on a set `U`
and suppose the zero set `{G = 0}` is invariant in the quantitative sense
`|DG(x) · B(x)| ≤ L |G(x)|` for `x ∈ U` (the *Grönwall condition*). Along a field line
`γ' = B(γ)` that stays in `U`, the function `g = G ∘ γ` satisfies `|g'| ≤ L |g|`, hence
(`abs_bounds_of_abs_deriv_le`, applied in `fieldLine_abs_bounds`)

`|G(γ 0)| e^{-L|t|} ≤ |G(γ t)| ≤ |G(γ 0)| e^{L|t|}`,

so `G ∘ γ` cannot change sign while the line stays in `U` (`fieldLine_sign_preserved`).

The all-time statement (`invariantBarrier_forward`, `invariantBarrier_forever`) needs the
Grönwall condition only on an open *collar* `C` of the frontier: if `Ω` is open, its frontier
lies in `C ∩ {G = 0}`, and `G ≠ 0` on `Ω ∩ C`, then every forward (resp. two-sided) field
line starting in `Ω` stays in `Ω` for all parameter values `s ≥ 0` (resp. all `s ∈ ℝ`). The
proof is a first-exit argument; it uses neither uniqueness of field lines nor area
preservation. `invariance_bound_of_tangent` derives the Grönwall condition from tangency on
the zero set plus a Lipschitz bound on `DG · B` (Hadamard-type estimate).

Sanity: `fieldLine_abs_exact` (exact first integral, `L = 0`), and the non-vacuous instance
`radial_barrier`: for the linear field `B(x) = x` and `G = x₀` the Grönwall condition holds
with `L = 1` (not with `L = 0`), the half-space `{x₀ < 0}` is a forward barrier, and the
explicit line `t ↦ eᵗ x` attains the upper bound with equality (`radial_bound_sharp`).

Scope: field-line statements only; no existence of field lines is postulated.
-/

public section
noncomputable section
namespace PlasmaLean.Fields
open Set Filter Topology Real

/-- A two-sided classical field line of `B`: `γ' = B(γ)` at every real parameter. -/
@[expose] def IsFieldLine (B : Space → Space) (γ : ℝ → Space) : Prop :=
  ∀ t, HasDerivAt γ (B (γ t)) t

/-- A two-sided field line is in particular a forward field line. -/
theorem IsFieldLine.forward {B : Space → Space} {γ : ℝ → Space} (h : IsFieldLine B γ) :
    IsForwardFieldLine B γ := fun t _ => h t

/-- Time reversal: if `γ` is a two-sided field line of `B`, then `s ↦ γ (-s)` is a
two-sided field line of `-B`. -/
theorem IsFieldLine.reverse {B : Space → Space} {γ : ℝ → Space} (h : IsFieldLine B γ) :
    IsFieldLine (fun x => -B x) (fun s => γ (-s)) := by
  intro t
  have := (h (-t)).scomp t (hasDerivAt_neg t)
  simp only [neg_one_smul] at this
  exact this

/-- The Grönwall condition: `G` is differentiable on `U` and `|DG · B| ≤ L |G|` there. -/
@[expose] def GronwallOn (B : Space → Space) (G : Space → ℝ) (L : ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ G x ∧ |fderiv ℝ G x (B x)| ≤ L * |G x|

/-- The Grönwall condition is insensitive to reversing the field. -/
theorem GronwallOn.neg {B : Space → Space} {G : Space → ℝ} {L : ℝ} {U : Set Space}
    (h : GronwallOn B G L U) : GronwallOn (fun x => -B x) G L U := fun x hx =>
  ⟨(h x hx).1, by rw [map_neg, abs_neg]; exact (h x hx).2⟩

/-- The Grönwall condition restricts to subsets. -/
theorem GronwallOn.mono {B : Space → Space} {G : Space → ℝ} {L : ℝ} {U V : Set Space}
    (h : GronwallOn B G L U) (hVU : V ⊆ U) : GronwallOn B G L V := fun x hx => h x (hVU hx)

/-- **Two-sided Grönwall bound for a scalar function.** If `|g'| ≤ L |g|` on `[a, b]`, then
`|g a| e^{-L(b-a)} ≤ |g b| ≤ |g a| e^{L(b-a)}`. (No sign condition on `L` is needed.) -/
theorem abs_bounds_of_abs_deriv_le {g g' : ℝ → ℝ} {L a b : ℝ} (hab : a ≤ b)
    (hg : ∀ u ∈ Icc a b, HasDerivAt g (g' u) u) (hb : ∀ u ∈ Icc a b, |g' u| ≤ L * |g u|) :
    |g a| * exp (-(L * (b - a))) ≤ |g b| ∧ |g b| ≤ |g a| * exp (L * (b - a)) := by
  have hcont : ContinuousOn g (Icc a b) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have key : ∀ u ∈ Icc a b, |g u * g' u| ≤ L * g u ^ 2 := by
    intro u hu
    rw [abs_mul]
    calc |g u| * |g' u| ≤ |g u| * (L * |g u|) := mul_le_mul_of_nonneg_left (hb u hu) (abs_nonneg _)
      _ = L * g u ^ 2 := by rw [← sq_abs (g u)]; ring
  have hint : interior (Icc a b) ⊆ Icc a b := interior_subset
  -- upper bound: `g² e^{-2Lu}` is antitone
  have hanti : AntitoneOn (fun u => g u ^ 2 * exp (-(2 * L) * u)) (Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (f' := fun u => (2 * g u * g' u) * exp (-(2 * L) * u) +
        g u ^ 2 * (exp (-(2 * L) * u) * (-(2 * L))))
      ((hcont.pow 2).mul (by fun_prop)) (fun u hu => ?_) (fun u hu => ?_)
    · have h1 := ((hg u (hint hu)).fun_pow 2).mul ((hasDerivAt_id u).const_mul (-(2 * L))).exp
      simp only [Nat.cast_ofNat, id, mul_one] at h1
      convert h1.hasDerivWithinAt using 1
      ring
    · have := (abs_le.mp (key u (hint hu))).2
      have he := exp_pos (-(2 * L) * u)
      nlinarith
  -- lower bound: `g² e^{2Lu}` is monotone
  have hmono : MonotoneOn (fun u => g u ^ 2 * exp ((2 * L) * u)) (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun u => (2 * g u * g' u) * exp ((2 * L) * u) +
        g u ^ 2 * (exp ((2 * L) * u) * (2 * L)))
      ((hcont.pow 2).mul (by fun_prop)) (fun u hu => ?_) (fun u hu => ?_)
    · have h1 := ((hg u (hint hu)).fun_pow 2).mul ((hasDerivAt_id u).const_mul (2 * L)).exp
      simp only [Nat.cast_ofNat, id, mul_one] at h1
      convert h1.hasDerivWithinAt using 1
      ring
    · have := (abs_le.mp (key u (hint hu))).1
      have he := exp_pos ((2 * L) * u)
      nlinarith
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb' : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hup := hanti ha hb' hab
  have hlo := hmono ha hb' hab
  simp only at hup hlo
  constructor
  · -- `(|g a| e^{-L(b-a)})² ≤ g b²`
    have hsq : (|g a| * exp (-(L * (b - a)))) ^ 2 ≤ |g b| ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs, ← exp_nat_mul]
      have e1 : exp ((2 * L) * a) = exp ((2 * L) * b) * exp ((2 : ℕ) * -(L * (b - a))) := by
        rw [← exp_add]; congr 1; push_cast; ring
      rw [e1] at hlo
      have hpos := exp_pos ((2 * L) * b)
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hsq
  · have hsq : |g b| ^ 2 ≤ (|g a| * exp (L * (b - a))) ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs, ← exp_nat_mul]
      have e1 : exp (-(2 * L) * a) = exp (-(2 * L) * b) * exp ((2 : ℕ) * (L * (b - a))) := by
        rw [← exp_add]; congr 1; push_cast; ring
      rw [e1] at hup
      have hpos := exp_pos (-(2 * L) * b)
      nlinarith
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Grönwall bound along a field line on `[a, b]` that stays in the region `U` where the
Grönwall condition holds. -/
theorem fieldLine_abs_bounds_Icc {B : Space → Space} {G : Space → ℝ} {L : ℝ} {U : Set Space}
    (hU : GronwallOn B G L U) {γ : ℝ → Space} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ u ∈ Icc a b, HasDerivAt γ (B (γ u)) u) (hstay : ∀ u ∈ Icc a b, γ u ∈ U) :
    |G (γ a)| * exp (-(L * (b - a))) ≤ |G (γ b)| ∧
      |G (γ b)| ≤ |G (γ a)| * exp (L * (b - a)) :=
  abs_bounds_of_abs_deriv_le (g := fun u => G (γ u)) hab
    (fun u hu => (hU _ (hstay u hu)).1.hasFDerivAt.comp_hasDerivAt u (hγ u hu))
    (fun u hu => (hU _ (hstay u hu)).2)

/-- **Grönwall barrier bound** (forward and backward). If `γ` is a field line on the
parameter interval between `0` and `t` and stays in `U` there, then
`|G(γ 0)| e^{-L|t|} ≤ |G(γ t)| ≤ |G(γ 0)| e^{L|t|}`. -/
theorem fieldLine_abs_bounds {B : Space → Space} {G : Space → ℝ} {L : ℝ} {U : Set Space}
    (hU : GronwallOn B G L U) {γ : ℝ → Space} {t : ℝ}
    (hγ : ∀ u ∈ uIcc 0 t, HasDerivAt γ (B (γ u)) u) (hstay : ∀ u ∈ uIcc 0 t, γ u ∈ U) :
    |G (γ 0)| * exp (-(L * |t|)) ≤ |G (γ t)| ∧ |G (γ t)| ≤ |G (γ 0)| * exp (L * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht] at hγ hstay
    simpa [abs_of_nonneg ht] using fieldLine_abs_bounds_Icc hU ht hγ hstay
  · rw [uIcc_of_ge ht] at hγ hstay
    obtain ⟨h1, h2⟩ := fieldLine_abs_bounds_Icc hU ht hγ hstay
    rw [abs_of_nonpos ht]
    simp only [zero_sub] at h1 h2
    have e : exp (-(L * -t)) * exp (L * -t) = 1 := by rw [← exp_add]; simp
    have hp := exp_pos (L * -t)
    have hp' := exp_pos (-(L * -t))
    constructor
    · nlinarith [abs_nonneg (G (γ 0)), abs_nonneg (G (γ t))]
    · nlinarith [abs_nonneg (G (γ 0)), abs_nonneg (G (γ t))]

/-- **No sign change** while in `U`: a forward field line with `G(γ 0) < 0` that stays in `U`
on `[0, t]` still has `G(γ t) < 0`. -/
theorem fieldLine_sign_preserved {B : Space → Space} {G : Space → ℝ} {L : ℝ} {U : Set Space}
    (hU : GronwallOn B G L U) {γ : ℝ → Space} {t : ℝ} (ht : 0 ≤ t)
    (hγ : ∀ u ∈ Icc 0 t, HasDerivAt γ (B (γ u)) u) (hstay : ∀ u ∈ Icc 0 t, γ u ∈ U)
    (h0 : G (γ 0) < 0) : G (γ t) < 0 := by
  have hne : ∀ u ∈ Icc 0 t, G (γ u) ≠ 0 := by
    intro u hu h
    have := (fieldLine_abs_bounds_Icc hU hu.1 (fun v hv => hγ v ⟨hv.1, hv.2.trans hu.2⟩)
      (fun v hv => hstay v ⟨hv.1, hv.2.trans hu.2⟩)).1
    rw [h, abs_zero] at this
    have := mul_pos (abs_pos.mpr h0.ne) (exp_pos (-(L * (u - 0))))
    linarith
  by_contra hc
  push Not at hc
  have hcont : ContinuousOn (fun u => G (γ u)) (Icc 0 t) := fun u hu =>
    ((hU _ (hstay u hu)).1.continuousAt.comp (hγ u hu).continuousAt).continuousWithinAt
  obtain ⟨c, hc', hc0⟩ := intermediate_value_Icc ht hcont ⟨h0.le, hc⟩
  exact hne c hc' hc0

/-- **All-time forward barrier** (first-exit argument). Let `Ω` be open, let `C` be an open
collar containing the frontier of `Ω`, with the frontier inside the zero set of `G`, and
`G ≠ 0` on `Ω ∩ C`. If the Grönwall condition holds on `C`, then every forward field line
starting in `Ω` stays in `Ω` for every parameter `s ≥ 0`. -/
theorem invariantBarrier_forward {B : Space → Space} {G : Space → ℝ} {L : ℝ}
    {Ω C : Set Space} (hΩ : IsOpen Ω) (hC : IsOpen C)
    (hfront : ∀ x ∈ frontier Ω, x ∈ C ∧ G x = 0) (hne : ∀ x ∈ Ω ∩ C, G x ≠ 0)
    (hgr : GronwallOn B G L C) {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ)
    (h0 : γ 0 ∈ Ω) : ∀ t, 0 ≤ t → γ t ∈ Ω := by
  by_contra hcon
  push Not at hcon
  have hγc : ContinuousOn γ (Ici 0) := fun u hu => (hγ u hu).continuousAt.continuousWithinAt
  set S := {t | 0 ≤ t ∧ γ t ∉ Ω} with hS
  have hSeq : S = Ici 0 ∩ γ ⁻¹' Ωᶜ := rfl
  have hSc : IsClosed S := by
    rw [hSeq]; exact hγc.preimage_isClosed_of_isClosed isClosed_Ici hΩ.isClosed_compl
  obtain ⟨t₀, ht₀, hbad⟩ := hcon
  have hSne : S.Nonempty := ⟨t₀, ht₀, hbad⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set t₁ := sInf S
  have ht₁S : t₁ ∈ S := hSc.csInf_mem hSne hSb
  have ht₁pos : 0 < t₁ := by
    rcases ht₁S.1.eq_or_lt with h | h
    · exact absurd (h ▸ h0) ht₁S.2
    · exact h
  have hbefore : ∀ u ∈ Ico 0 t₁, γ u ∈ Ω := by
    intro u hu
    by_contra h
    exact absurd (csInf_le hSb ⟨hu.1, h⟩) (not_le.mpr hu.2)
  -- `γ t₁` lies on the frontier
  have hlim : Tendsto γ (𝓝[<] t₁) (𝓝 (γ t₁)) :=
    (hγ t₁ ht₁S.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in 𝓝[<] t₁, γ u ∈ Ω := by
    filter_upwards [Ioo_mem_nhdsLT ht₁pos] with u hu
    exact hbefore u ⟨hu.1.le, hu.2⟩
  have hcl : γ t₁ ∈ closure Ω := mem_closure_of_tendsto hlim hev
  have hfr : γ t₁ ∈ frontier Ω := by
    rw [frontier, hΩ.interior_eq]; exact ⟨hcl, ht₁S.2⟩
  obtain ⟨hCt, hG0⟩ := hfront _ hfr
  -- a short interval before `t₁` stays in the collar
  have hnhds : γ ⁻¹' C ∈ 𝓝 t₁ := (hγ t₁ ht₁S.1).continuousAt.preimage_mem_nhds (hC.mem_nhds hCt)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  set a := max 0 (t₁ - η / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have hat : a < t₁ := max_lt ht₁pos (by linarith)
  have hinC : ∀ u ∈ Icc a t₁, γ u ∈ C := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : t₁ - η / 2 ≤ a := le_max_right _ _
    constructor <;> linarith [hu.1, hu.2]
  have hbd := (fieldLine_abs_bounds_Icc hgr hat.le
    (fun u hu => hγ u (ha0.trans hu.1)) hinC).1
  rw [hG0, abs_zero] at hbd
  have hGa : G (γ a) ≠ 0 := hne _ ⟨hbefore a ⟨ha0, hat⟩, hinC a ⟨le_rfl, hat.le⟩⟩
  have := mul_pos (abs_pos.mpr hGa) (exp_pos (-(L * (t₁ - a))))
  linarith

/-- **All-time two-sided barrier.** Under the hypotheses of `invariantBarrier_forward`, a
two-sided field line starting in `Ω` stays in `Ω` for every real parameter (forward by
`invariantBarrier_forward`, backward by applying it to the reversed line of `-B`). -/
theorem invariantBarrier_forever {B : Space → Space} {G : Space → ℝ} {L : ℝ}
    {Ω C : Set Space} (hΩ : IsOpen Ω) (hC : IsOpen C)
    (hfront : ∀ x ∈ frontier Ω, x ∈ C ∧ G x = 0) (hne : ∀ x ∈ Ω ∩ C, G x ≠ 0)
    (hgr : GronwallOn B G L C) {γ : ℝ → Space} (hγ : IsFieldLine B γ)
    (h0 : γ 0 ∈ Ω) : ∀ t, γ t ∈ Ω := by
  intro t
  rcases le_total 0 t with ht | ht
  · exact invariantBarrier_forward hΩ hC hfront hne hgr hγ.forward h0 t ht
  · have h := invariantBarrier_forward hΩ hC hfront hne hgr.neg hγ.reverse.forward
      (by simpa using h0) (-t) (by linarith)
    simpa using h

/-- **Hadamard-type bound: tangency plus Lipschitz gives the Grönwall condition.** If
`F = DG · B` vanishes on the invariant set `S`, is `M`-Lipschitz from `U` to `S`, and every
`x ∈ U` has a point of `S` within `K |G x|` (a nondegenerate defining function), then
`|F| ≤ (M K) |G|` on `U`. -/
theorem invariance_bound_of_tangent {F G : Space → ℝ} {S U : Set Space} {M K : ℝ}
    (hM : 0 ≤ M) (hvan : ∀ y ∈ S, F y = 0)
    (hlip : ∀ x ∈ U, ∀ y ∈ S, |F x - F y| ≤ M * ‖x - y‖)
    (hproj : ∀ x ∈ U, ∃ y ∈ S, ‖x - y‖ ≤ K * |G x|) :
    ∀ x ∈ U, |F x| ≤ (M * K) * |G x| := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hproj x hx
  have h := hlip x hx y hy
  rw [hvan y hy, sub_zero] at h
  calc |F x| ≤ M * ‖x - y‖ := h
    _ ≤ M * (K * |G x|) := mul_le_mul_of_nonneg_left hxy hM
    _ = (M * K) * |G x| := by ring

/-! ### Sanity checks -/

/-- Degenerate case `L = 0` (exact first integral on `U`): `|G ∘ γ|` is constant while the
field line stays in `U`. -/
theorem fieldLine_abs_exact {B : Space → Space} {G : Space → ℝ} {U : Set Space}
    (hU : ∀ x ∈ U, DifferentiableAt ℝ G x ∧ fderiv ℝ G x (B x) = 0) {γ : ℝ → Space} {t : ℝ}
    (hγ : ∀ u ∈ uIcc 0 t, HasDerivAt γ (B (γ u)) u) (hstay : ∀ u ∈ uIcc 0 t, γ u ∈ U) :
    |G (γ t)| = |G (γ 0)| := by
  have hgr : GronwallOn B G 0 U := fun x hx => ⟨(hU x hx).1, by simp [(hU x hx).2]⟩
  have h := fieldLine_abs_bounds hgr hγ hstay
  simp only [zero_mul, neg_zero, exp_zero, mul_one] at h
  exact le_antisymm h.2 h.1

/-- The linear (radial) field `B(x) = x`. -/
@[expose] def radialField (x : Space) : Space := x

/-- The first coordinate `G(x) = x₀`. -/
@[expose] def coord0 (x : Space) : ℝ := x 0

/-- `D coord0 · B = coord0` for the radial field: the Grönwall condition holds with `L = 1`
on all of space. -/
theorem radial_gronwall : GronwallOn radialField coord0 1 univ := by
  intro x _
  have h : HasFDerivAt coord0 (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt
  refine ⟨h.differentiableAt, ?_⟩
  rw [h.fderiv]
  simp [radialField, coord0]

/-- The Grönwall condition for the radial field genuinely needs `L > 0`: `coord0` is not a
first integral (the zero set is invariant, but nearby level sets are not). -/
theorem radial_not_firstIntegral : ¬ GronwallOn radialField coord0 0 univ := by
  intro h
  set x : Space := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have h1 := (radial_gronwall x trivial)
  have h0 := (h x trivial).2
  have hd : fderiv ℝ coord0 x (radialField x) = 1 := by
    have h' : HasFDerivAt coord0 (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt
    rw [h'.fderiv]; simp [radialField, x]
  rw [hd] at h0
  norm_num at h0

/-- The explicit radial field lines `t ↦ eᵗ x`. -/
theorem radial_fieldLine (x : Space) : IsFieldLine radialField (fun t => exp t • x) := by
  intro t
  simpa [radialField] using (hasDerivAt_exp t).smul_const x

/-- **Non-vacuous instance.** For the radial field, the open half-space `{x₀ < 0}` is an
all-time barrier (collar = all of space, `L = 1`), and the hypotheses are met by the explicit
line `t ↦ eᵗ x` from any `x` with `x₀ < 0`. -/
theorem radial_barrier {γ : ℝ → Space} (hγ : IsFieldLine radialField γ) (h0 : γ 0 0 < 0) :
    ∀ t, γ t 0 < 0 := by
  have hΩ : IsOpen {x : Space | coord0 x < 0} :=
    isOpen_lt (by unfold coord0; fun_prop) continuous_const
  have hfront : ∀ x ∈ frontier {x : Space | coord0 x < 0}, x ∈ univ ∧ coord0 x = 0 :=
    fun x hx => ⟨trivial, frontier_lt_subset_eq (by unfold coord0; fun_prop) continuous_const hx⟩
  exact invariantBarrier_forever (C := univ) hΩ isOpen_univ hfront
    (fun x hx => hx.1.ne) radial_gronwall hγ h0

/-- The upper Grönwall bound is sharp: along `t ↦ eᵗ x`, `|G(γ t)| = |G(γ 0)| e^{t}`. -/
theorem radial_bound_sharp (x : Space) (t : ℝ) :
    |coord0 (exp t • x)| = |coord0 (exp 0 • x)| * exp (1 * t) := by
  simp [coord0, abs_mul, abs_of_pos (exp_pos t), mul_comm]

end PlasmaLean.Fields
