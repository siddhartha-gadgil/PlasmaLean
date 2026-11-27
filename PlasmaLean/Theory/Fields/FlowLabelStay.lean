/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FlowLabel

/-!
# A perturbed path does not leave the region of a flow tube

A space-time path with velocity `λ(t) (1, F) + w(t)` moves the section label by at most `κ t`
as long as it stays in the region of the tube (`FlowLabel.displacement_le`). Here the
hypothesis that the path stays in the region is removed: it suffices that the points of the
region whose time lies in a window and whose label lies in a set `S` form part of a closed
subset `K` of the region, and that `S` contains the closed ball of radius `r + κ T` around a
point within `r` of the initial label.

* `stays_core`: the path stays in the closed core `K` and its label moves by at most `κ t`.
* `stays`: the same conclusion with membership in the region.
* `stays_zero`: the hypotheses hold together for the zero field and a constant path.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.FlowLabel
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : ℝ → E → E} {W V : ℝ → Set E} {c a b C M : ℝ}

/-- **No exit, with the closed core.** Let `K` be a closed subset of the region containing every
point of the region whose time lies in `[a', b']` and whose label lies in `S`. A path with
velocity `λ(t) (1, F) + w(t)` that starts in the region with label within `r` of `ℓ₀`, where
`S` contains the closed ball of radius `r + κ T` around `ℓ₀`, stays in `K` on `[0, T]`, and its
label moves by at most `κ t`. The bound on `w` and the time window are needed only at the times
up to which the path has stayed in the region. -/
theorem stays_core [CompleteSpace E] (tube : Tube F c a b W V C M)
    (hopen : IsOpen (region a b V)) (smooth : ∀ p ∈ region a b V, ContDiffAt ℝ 1 (field F) p)
    {K : Set (ℝ × E)} (Kclosed : IsClosed K) (Ksub : K ⊆ region a b V)
    {S : Set E} {a' b' : ℝ}
    (core : ∀ p ∈ region a b V, p.1 ∈ Icc a' b' → label F W c p ∈ S → p ∈ K)
    {X : ℝ → ℝ × E} {lam : ℝ → ℝ} {w : ℝ → ℝ × E} {κ T r : ℝ} {ℓ₀ : E}
    (hT : 0 ≤ T) (X0 : X 0 ∈ region a b V)
    (ode : ∀ t ∈ Icc 0 T, HasDerivAt X (lam t • field F (X t) + w t) t)
    (small : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, X s ∈ region a b V) → C * (1 + M) * ‖w t‖ ≤ κ)
    (window : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, X s ∈ region a b V) → (X t).1 ∈ Icc a' b')
    (start : ‖label F W c (X 0) - ℓ₀‖ ≤ r) (ball : Metric.closedBall ℓ₀ (r + κ * T) ⊆ S) :
    ∀ t ∈ Icc 0 T, X t ∈ K ∧ ‖label F W c (X t) - label F W c (X 0)‖ ≤ κ * t := by
  have zero : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  have only0 : ∀ s ∈ Icc (0 : ℝ) 0, X s ∈ region a b V := by
    intro s hs
    rw [Icc_self, mem_singleton_iff] at hs
    rwa [hs]
  have hκ : 0 ≤ κ := by
    have hC : 0 ≤ C := by linarith [tube.one_le]
    have hM := tube.speed_nonneg
    exact le_trans (by positivity) (small 0 zero only0)
  -- staying in the region up to `t` gives the label bound and membership in the core
  have step : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, X s ∈ region a b V) →
      ∀ s ∈ Icc 0 t, X s ∈ K ∧ ‖label F W c (X s) - label F W c (X 0)‖ ≤ κ * s := by
    intro t ht inU s hs
    have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have sub' : ∀ σ ∈ Icc 0 t, Icc 0 σ ⊆ Icc 0 t := fun σ hσ => Icc_subset_Icc_right hσ.2
    have d := displacement_le tube hopen smooth inU (fun σ hσ => ode σ (sub hσ))
      (fun σ hσ => small σ (sub hσ) fun ρ hρ => inU ρ (sub' σ hσ hρ)) s hs
    refine ⟨core _ (inU s hs) (window s (sub hs) fun ρ hρ => inU ρ (sub' s hs hρ)) (ball ?_), d⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have tri : ‖label F W c (X s) - ℓ₀‖ ≤
        ‖label F W c (X s) - label F W c (X 0)‖ + ‖label F W c (X 0) - ℓ₀‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have : κ * s ≤ κ * T := mul_le_mul_of_nonneg_left (hs.2.trans ht.2) hκ
    linarith
  let A : Set ℝ := {t | ∀ s ∈ Icc 0 t, X s ∈ K}
  have all : Icc 0 T ⊆ A := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · -- closedness
      refine isClosed_of_closure_subset fun t ht => ?_
      have htI : t ∈ Icc 0 T := by
        have := closure_mono (inter_subset_right (s := A) (t := Icc 0 T)) ht
        rwa [isClosed_Icc.closure_eq] at this
      refine ⟨fun s hs => ?_, htI⟩
      rcases hs.2.lt_or_eq with hlt | heq
      · obtain ⟨t', ht', ht'A⟩ := mem_closure_iff.mp ht (Ioi s) isOpen_Ioi hlt
        exact ht'A.1 s ⟨hs.1, (mem_Ioi.mp ht').le⟩
      · rw [heq]
        have cont := (ode t htI).continuousAt.continuousWithinAt (s := A ∩ Icc 0 T)
        have := cont.mem_closure ht (t := K) fun t' ht' => ht'.1 t' ⟨ht'.2.1, le_rfl⟩
        rwa [Kclosed.closure_eq] at this
    · exact fun s hs => (step 0 zero only0 s hs).1
    · rintro t ⟨htA, ht⟩
      have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
      have near : ∀ᶠ t' in 𝓝 t, X t' ∈ region a b V :=
        (ode t htI).continuousAt.eventually (hopen.mem_nhds (Ksub (htA t ⟨ht.1, le_rfl⟩)))
      obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp near
      have lt : t < min u T := lt_min hlu.2 ht.2
      refine mem_of_superset (Ioo_mem_nhdsGT lt) fun t' ht' => ?_
      have ht'I : t' ∈ Icc 0 T := ⟨ht.1.trans ht'.1.le, ht'.2.le.trans (min_le_right _ _)⟩
      have inU : ∀ s ∈ Icc 0 t', X s ∈ region a b V := by
        intro s hs
        rcases le_or_gt s t with h | h
        · exact Ksub (htA s ⟨hs.1, h⟩)
        · exact hsub ⟨hlu.1.trans h, hs.2.trans_lt (ht'.2.trans_le (min_le_left _ _))⟩
      exact fun s hs => (step t' ht'I inU s hs).1
  intro t ht
  exact step t ht (fun s hs => Ksub (all ht s hs)) t (right_mem_Icc.mpr ht.1)

/-- **No exit.** Under the hypotheses of `stays_core` the path stays in the region of the tube
on `[0, T]`, and its label moves by at most `κ t`. -/
theorem stays [CompleteSpace E] (tube : Tube F c a b W V C M)
    (hopen : IsOpen (region a b V)) (smooth : ∀ p ∈ region a b V, ContDiffAt ℝ 1 (field F) p)
    {K : Set (ℝ × E)} (Kclosed : IsClosed K) (Ksub : K ⊆ region a b V)
    {S : Set E} {a' b' : ℝ}
    (core : ∀ p ∈ region a b V, p.1 ∈ Icc a' b' → label F W c p ∈ S → p ∈ K)
    {X : ℝ → ℝ × E} {lam : ℝ → ℝ} {w : ℝ → ℝ × E} {κ T r : ℝ} {ℓ₀ : E}
    (hT : 0 ≤ T) (X0 : X 0 ∈ region a b V)
    (ode : ∀ t ∈ Icc 0 T, HasDerivAt X (lam t • field F (X t) + w t) t)
    (small : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, X s ∈ region a b V) → C * (1 + M) * ‖w t‖ ≤ κ)
    (window : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, X s ∈ region a b V) → (X t).1 ∈ Icc a' b')
    (start : ‖label F W c (X 0) - ℓ₀‖ ≤ r) (ball : Metric.closedBall ℓ₀ (r + κ * T) ⊆ S) :
    ∀ t ∈ Icc 0 T, X t ∈ region a b V ∧ ‖label F W c (X t) - label F W c (X 0)‖ ≤ κ * t :=
  fun t ht =>
    have h := stays_core tube hopen smooth Kclosed Ksub core hT X0 ode small window start ball t ht
    ⟨Ksub h.1, h.2⟩

/-- Sanity: for the zero field, the constant path at the section time satisfies all hypotheses
of `stays`, with the core the slice at the section time, `S` the whole space and `κ = 0`. -/
theorem stays_zero [CompleteSpace E] {a c b : ℝ} (h : c ∈ Ioo a b) (x : E) :
    ∀ t ∈ Icc (0 : ℝ) 1, ((c, x) : ℝ × E) ∈ region a b (fun _ => (univ : Set E)) ∧
      ‖label (fun _ _ => (0 : E)) (fun _ => univ) c (c, x) -
        label (fun _ _ => (0 : E)) (fun _ => univ) c (c, x)‖ ≤ 0 * t := by
  have hreg : region a b (fun _ => (univ : Set E)) = Ioo a b ×ˢ univ := by
    ext p
    simp [region]
  refine stays (K := {c} ×ˢ univ) (S := univ) (a' := c) (b' := c) (X := fun _ => (c, x))
    (lam := fun _ => 0) (w := fun _ => 0) (r := 0)
    (ℓ₀ := label (fun _ _ => (0 : E)) (fun _ => univ) c (c, x)) (tube_zero a c b h) ?_ ?_ ?_ ?_ ?_
    zero_le_one ⟨h, mem_univ _⟩ ?_ ?_ ?_ ?_ (subset_univ _)
  · rw [hreg]
    exact isOpen_Ioo.prod isOpen_univ
  · exact fun p _ => contDiffAt_const
  · exact isClosed_singleton.prod isClosed_univ
  · rintro p ⟨hp, -⟩
    exact ⟨mem_singleton_iff.mp hp ▸ h, mem_univ _⟩
  · rintro p - hp -
    exact ⟨mem_singleton_iff.mpr (le_antisymm hp.2 hp.1), mem_univ _⟩
  · intro t _
    simpa using hasDerivAt_const t ((c, x) : ℝ × E)
  · intro t _ _
    simp
  · intro t _ _
    exact ⟨le_rfl, le_rfl⟩
  · simp

end PlasmaLean.Fields.FlowLabel
