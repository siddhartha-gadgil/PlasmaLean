/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.LipschitzLabel
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The section label of a time-dependent flow

For a time-dependent equation `x' = F t x` on a real Banach space and a section time `c`, the
label of a space-time point `(t, x)` is the point where the solution through `(t, x)` meets the
time `c`. The hypotheses are collected in `Tube`: solutions starting in an inner tube `V` reach the
section inside an outer tube `W`, on which they are unique, contract at most by a factor `C`
towards the section, and have speed at most `M`.

* `label_eq`: the label is the section value of any solution in the outer tube through the point.
* `norm_label_sub_le`, `lipschitzOnWith`: the label is Lipschitz with constant `C (1 + M)` for the
  sup norm on `ℝ × E`.
* `label_invariant`, `invariantOn`: the label is constant on the integral curves of the
  autonomous field `(1, F)` on space-time.
* `displacement_le`: a path with velocity `λ(t) (1, F) + w(t)` moves the label by at most `κ t`
  when `C (1 + M) ‖w(t)‖ ≤ κ`.
* `tube_zero`, `label_zero`: the zero field satisfies the hypotheses, and its label is the space
  component.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.FlowLabel
open Set Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `v` solves `x' = F t x` on the closed interval between `s` and `t` and stays in the tube. -/
def SolOn (F : ℝ → E → E) (W : ℝ → Set E) (s t : ℝ) (v : ℝ → E) : Prop :=
  ∀ τ ∈ uIcc s t, HasDerivWithinAt v (F τ (v τ)) (uIcc s t) τ ∧ v τ ∈ W τ

/-- Hypotheses on the flow of `x' = F t x` between the times `a` and `b` around the section time
`c`: an inner tube `V` from which solutions reach the section inside the outer tube `W`, where
solutions are unique, contract at most by the factor `C` towards the section, and have speed at
most `M`. -/
structure Tube (F : ℝ → E → E) (c a b : ℝ) (W V : ℝ → Set E) (C M : ℝ) : Prop where
  /-- the section time lies in the time interval -/
  section_mem : c ∈ Ioo a b
  /-- the contraction factor is at least one -/
  one_le : 1 ≤ C
  /-- the speed bound is nonnegative -/
  speed_nonneg : 0 ≤ M
  /-- from every point of the inner tube a solution reaches the section inside the outer tube -/
  reach : ∀ t ∈ Ioo a b, ∀ x ∈ V t, ∃ v : ℝ → E, v t = x ∧ SolOn F W c t v
  /-- solutions in the outer tube are no further apart at the section than `C` times their
  distance at time `t` -/
  contract : ∀ t ∈ Ioo a b, ∀ u v : ℝ → E, SolOn F W c t u → SolOn F W c t v →
    ‖u c - v c‖ ≤ C * ‖u t - v t‖
  /-- uniqueness towards the section from any intermediate time -/
  unique : ∀ t ∈ Ioo a b, ∀ s ∈ uIcc c t, ∀ u v : ℝ → E, SolOn F W s t u → SolOn F W s t v →
    u t = v t → u s = v s
  /-- the field is bounded by `M` on the outer tube -/
  speed : ∀ t ∈ Ioo a b, ∀ x ∈ W t, ‖F t x‖ ≤ M

/-- The part of space-time over the inner tube. -/
def region (a b : ℝ) (V : ℝ → Set E) : Set (ℝ × E) := {p | p.1 ∈ Ioo a b ∧ p.2 ∈ V p.1}

/-- The section point of the solution through `p` (zero if there is none). -/
def label (F : ℝ → E → E) (W : ℝ → Set E) (c : ℝ) (p : ℝ × E) : E :=
  open Classical in
  if h : ∃ v : ℝ → E, v p.1 = p.2 ∧ SolOn F W c p.1 v then (Classical.choose h) c else 0

/-- The autonomous field on space-time. -/
def field (F : ℝ → E → E) (p : ℝ × E) : ℝ × E := (1, F p.1 p.2)

variable {F : ℝ → E → E} {W V : ℝ → Set E} {c a b C M : ℝ}

/-- Of three real numbers, one lies between the other two. -/
theorem mem_uIcc_cases (c s t : ℝ) : s ∈ uIcc c t ∨ t ∈ uIcc c s ∨ c ∈ uIcc s t := by
  simp only [mem_uIcc]
  rcases le_total c s with h1 | h1 <;> rcases le_total s t with h2 | h2 <;>
    rcases le_total c t with h3 | h3 <;> grind

/-- A solution restricts to a sub-interval. -/
theorem SolOn.mono {s t s' t' : ℝ} {v : ℝ → E} (sol : SolOn F W s t v)
    (h : uIcc s' t' ⊆ uIcc s t) : SolOn F W s' t' v :=
  fun τ hτ => ⟨(sol τ (h hτ)).1.mono h, (sol τ (h hτ)).2⟩

/-- The interval of a solution may be written in either order. -/
theorem SolOn.symm {s t : ℝ} {v : ℝ → E} (sol : SolOn F W s t v) : SolOn F W t s v :=
  sol.mono (by rw [uIcc_comm])

/-- Mean value inequality for a solution in a tube where the field is bounded by `M`. -/
theorem SolOn.norm_sub_le {s t : ℝ} {v : ℝ → E} (sol : SolOn F W s t v)
    (bound : ∀ τ ∈ uIcc s t, ∀ x ∈ W τ, ‖F τ x‖ ≤ M) : ‖v t - v s‖ ≤ M * |t - s| := by
  have h := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := v) (f' := fun τ => F τ (v τ)) (C := M) (fun τ hτ => (sol τ hτ).1)
    (fun τ hτ => bound τ hτ _ (sol τ hτ).2) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-- The inner tube lies in the outer tube. -/
theorem Tube.subset (tube : Tube F c a b W V C M) {t : ℝ} (ht : t ∈ Ioo a b) : V t ⊆ W t := by
  intro x hx
  obtain ⟨v, hv, sol⟩ := tube.reach t ht x hx
  simpa [hv] using (sol t right_mem_uIcc).2

/-- A solution in the outer tube moves at speed at most `M`. -/
theorem Tube.norm_sub_le (tube : Tube F c a b W V C M) {s t : ℝ} (hs : s ∈ Ioo a b)
    (ht : t ∈ Ioo a b) {v : ℝ → E} (sol : SolOn F W s t v) : ‖v t - v s‖ ≤ M * |t - s| :=
  sol.norm_sub_le fun τ hτ => tube.speed τ (ordConnected_Ioo.uIcc_subset hs ht hτ)

/-- Comparison at the section of two solutions given at the times `s` and `t`, when `s` lies
between the section and `t`. -/
theorem Tube.norm_sub_le_of_mem_uIcc (tube : Tube F c a b W V C M) {s t : ℝ} (hs : s ∈ Ioo a b)
    (ht : t ∈ Ioo a b) (hst : s ∈ uIcc c t) {u v : ℝ → E} (su : SolOn F W c s u)
    (sv : SolOn F W c t v) : ‖u c - v c‖ ≤ C * (‖u s - v t‖ + M * |s - t|) := by
  have h1 := tube.contract s hs u v su (sv.mono (uIcc_subset_uIcc left_mem_uIcc hst))
  have h2 := tube.norm_sub_le hs ht (sv.mono (uIcc_subset_uIcc hst right_mem_uIcc))
  have h3 : ‖u s - v s‖ ≤ ‖u s - v t‖ + ‖v t - v s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hC : 0 ≤ C := by linarith [tube.one_le]
  rw [abs_sub_comm s t]
  calc ‖u c - v c‖ ≤ C * ‖u s - v s‖ := h1
    _ ≤ C * (‖u s - v t‖ + M * |t - s|) := by gcongr; linarith

/-- The label is the section value of any solution in the outer tube through the point. -/
theorem label_eq (tube : Tube F c a b W V C M) {p : ℝ × E} (hp : p.1 ∈ Ioo a b) {v : ℝ → E}
    (hv : v p.1 = p.2) (sol : SolOn F W c p.1 v) : label F W c p = v c := by
  have h : ∃ v : ℝ → E, v p.1 = p.2 ∧ SolOn F W c p.1 v := ⟨v, hv, sol⟩
  rw [label, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hu, su⟩ := Classical.choose_spec h
  exact tube.unique p.1 hp c left_mem_uIcc _ v su sol (hu.trans hv.symm)

/-- The label is Lipschitz in the space-time point. -/
theorem norm_label_sub_le (tube : Tube F c a b W V C M) {p q : ℝ × E} (hp : p ∈ region a b V)
    (hq : q ∈ region a b V) :
    ‖label F W c p - label F W c q‖ ≤ C * (‖p.2 - q.2‖ + M * |p.1 - q.1|) := by
  obtain ⟨u, hu, su⟩ := tube.reach p.1 hp.1 p.2 hp.2
  obtain ⟨v, hv, sv⟩ := tube.reach q.1 hq.1 q.2 hq.2
  rw [label_eq tube hp.1 hu su, label_eq tube hq.1 hv sv]
  rcases mem_uIcc_cases c p.1 q.1 with h | h | h
  · have key := tube.norm_sub_le_of_mem_uIcc hp.1 hq.1 h su sv
    rwa [hu, hv] at key
  · have key := tube.norm_sub_le_of_mem_uIcc hq.1 hp.1 h sv su
    rw [hu, hv] at key
    rwa [norm_sub_rev, norm_sub_rev p.2, abs_sub_comm]
  · have h1 := tube.norm_sub_le tube.section_mem hp.1 su
    have h2 := tube.norm_sub_le tube.section_mem hq.1 sv
    rw [hu] at h1
    rw [hv] at h2
    have h3 : |p.1 - c| + |q.1 - c| = |p.1 - q.1| := by
      rcases mem_uIcc.mp h with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith),
          abs_of_nonpos (by linarith)]
        ring
      · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith),
          abs_of_nonneg (by linarith)]
        ring
    have tri : ‖u c - v c‖ ≤ ‖p.2 - u c‖ + ‖p.2 - q.2‖ + ‖q.2 - v c‖ := by
      calc ‖u c - v c‖ = ‖-(p.2 - u c) + (p.2 - q.2) + (q.2 - v c)‖ := by
            congr 1
            abel
        _ ≤ ‖-(p.2 - u c)‖ + ‖p.2 - q.2‖ + ‖q.2 - v c‖ := norm_add₃_le
        _ = ‖p.2 - u c‖ + ‖p.2 - q.2‖ + ‖q.2 - v c‖ := by rw [norm_neg]
    have hM := tube.speed_nonneg
    have hR : 0 ≤ ‖p.2 - q.2‖ + M * |p.1 - q.1| := by positivity
    calc ‖u c - v c‖ ≤ ‖p.2 - q.2‖ + M * |p.1 - q.1| := by
          rw [← h3]
          linarith
      _ ≤ C * (‖p.2 - q.2‖ + M * |p.1 - q.1|) := le_mul_of_one_le_left hR tube.one_le

/-- A functional of norm at most one of the label is Lipschitz on the region, for the sup norm
on space-time. -/
theorem lipschitzOnWith (tube : Tube F c a b W V C M) (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
    LipschitzOnWith (Real.toNNReal (C * (1 + M))) (fun p => ℓ (label F W c p))
      (region a b V) := by
  have hC : 0 ≤ C := by linarith [tube.one_le]
  have hM := tube.speed_nonneg
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm, ← map_sub]
  have h1 : |ℓ (label F W c p - label F W c q)| ≤ ‖label F W c p - label F W c q‖ := by
    simpa using ℓ.le_of_opNorm_le hℓ (label F W c p - label F W c q)
  have h2 := norm_label_sub_le tube hp hq
  have h3 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  have h4 : |p.1 - q.1| ≤ ‖p - q‖ := norm_fst_le (p - q)
  calc |ℓ (label F W c p - label F W c q)| ≤ C * (‖p.2 - q.2‖ + M * |p.1 - q.1|) := h1.trans h2
    _ ≤ C * (‖p - q‖ + M * ‖p - q‖) := by gcongr
    _ = C * (1 + M) * ‖p - q‖ := by ring

/-- The label is constant on the integral curves of the space-time field inside the region. -/
theorem label_invariant (tube : Tube F c a b W V C M) {γ : ℝ → ℝ × E} {a' b' : ℝ} (hab : a' ≤ b')
    (mem : ∀ τ ∈ Icc a' b', γ τ ∈ region a b V)
    (der : ∀ τ ∈ Icc a' b', HasDerivAt γ (field F (γ τ)) τ) :
    label F W c (γ a') = label F W c (γ b') := by
  have ha' : a' ∈ Icc a' b' := left_mem_Icc.mpr hab
  have hb' : b' ∈ Icc a' b' := right_mem_Icc.mpr hab
  -- the time component advances at unit rate
  have time : ∀ τ ∈ Icc a' b', (γ τ).1 = (γ a').1 + (τ - a') := by
    intro τ hτ
    have h := (convex_Icc a' b').norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ => (γ τ).1 - τ) (f' := fun _ => (0 : ℝ)) (C := 0)
      (fun σ hσ => by
        have h1 : HasDerivAt (fun τ => (γ τ).1) 1 σ := by
          simpa [field, Function.comp_def] using
            (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt σ (der σ hσ)
        have h : HasDerivAt (fun τ => (γ τ).1 - τ) (1 - 1) σ := h1.sub (hasDerivAt_id' σ)
        simpa using h.hasDerivWithinAt (s := Icc a' b'))
      (fun _ _ => by simp) ha' hτ
    have : (γ τ).1 - τ - ((γ a').1 - a') = 0 := by simpa using h
    linarith
  have tb : (γ b').1 = (γ a').1 + (b' - a') := time b' hb'
  have le : (γ a').1 ≤ (γ b').1 := by linarith
  have hA := mem a' ha'
  have hB := mem b' hb'
  -- the space component, reparametrised by the time component, is a solution
  let x : ℝ → E := fun t => (γ (t - (γ a').1 + a')).2
  have xa : x (γ a').1 = (γ a').2 := by simp [x]
  have xb : x (γ b').1 = (γ b').2 := by
    change (γ ((γ b').1 - (γ a').1 + a')).2 = (γ b').2
    rw [show (γ b').1 - (γ a').1 + a' = b' by linarith]
  have solx : SolOn F W (γ a').1 (γ b').1 x := by
    intro t ht
    rw [uIcc_of_le le] at ht ⊢
    have hτ : t - (γ a').1 + a' ∈ Icc a' b' := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht' : (γ (t - (γ a').1 + a')).1 = t := by
      rw [time _ hτ]
      ring
    have inner : HasDerivAt (fun t : ℝ => t - (γ a').1 + a') 1 t := by
      simpa using ((hasDerivAt_id t).sub_const (γ a').1).add_const a'
    have d2 := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt _ (der _ hτ)
    have d := HasDerivAt.scomp t d2 inner
    have hR := mem _ hτ
    have hI : t ∈ Ioo a b := by simpa [ht'] using hR.1
    have hV : x t ∈ V t := by simpa [ht'] using hR.2
    refine ⟨?_, tube.subset hI hV⟩
    have dx : HasDerivAt x (F t (x t)) t := by
      simpa [field, ht', x, Function.comp_def] using d
    exact dx.hasDerivWithinAt
  rcases mem_uIcc_cases c (γ a').1 (γ b').1 with h | h | h
  · obtain ⟨v, hv, sv⟩ := tube.reach _ hB.1 _ hB.2
    have e := tube.unique _ hB.1 _ h x v solx (sv.mono (uIcc_subset_uIcc h right_mem_uIcc))
      (xb.trans hv.symm)
    rw [label_eq tube hA.1 (e.symm.trans xa) (sv.mono (uIcc_subset_uIcc left_mem_uIcc h)),
      label_eq tube hB.1 hv sv]
  · obtain ⟨v, hv, sv⟩ := tube.reach _ hA.1 _ hA.2
    have e := tube.unique _ hA.1 _ h x v solx.symm
      (sv.mono (uIcc_subset_uIcc h right_mem_uIcc)) (xa.trans hv.symm)
    rw [label_eq tube hA.1 hv sv,
      label_eq tube hB.1 (e.symm.trans xb) (sv.mono (uIcc_subset_uIcc left_mem_uIcc h))]
  · rw [label_eq tube hA.1 xa (solx.mono (uIcc_subset_uIcc h left_mem_uIcc)),
      label_eq tube hB.1 xb (solx.mono (uIcc_subset_uIcc h right_mem_uIcc))]

/-- A continuous linear functional of the label is an invariant of the space-time field. -/
theorem invariantOn [CompleteSpace E] (tube : Tube F c a b W V C M) (ℓ : E →L[ℝ] ℝ) :
    LipschitzLabel.InvariantOn (field F) (fun p => ℓ (label F W c p)) (region a b V) :=
  fun _ _ _ hab mem der => congrArg ℓ (label_invariant tube hab mem der)

/-- **Drift of the section label.** A space-time path whose velocity differs from a multiple of
the field `(1, F)` by `w` moves the label by at most `κ t` when `C (1 + M) ‖w‖ ≤ κ`. -/
theorem displacement_le [CompleteSpace E] (tube : Tube F c a b W V C M)
    (hopen : IsOpen (region a b V)) (smooth : ∀ p ∈ region a b V, ContDiffAt ℝ 1 (field F) p)
    {X : ℝ → ℝ × E} {lam : ℝ → ℝ} {w : ℝ → ℝ × E} {κ T : ℝ}
    (inU : ∀ t ∈ Icc 0 T, X t ∈ region a b V)
    (ode : ∀ t ∈ Icc 0 T, HasDerivAt X (lam t • field F (X t) + w t) t)
    (small : ∀ t ∈ Icc 0 T, C * (1 + M) * ‖w t‖ ≤ κ) :
    ∀ t ∈ Icc 0 T, ‖label F W c (X t) - label F W c (X 0)‖ ≤ κ * t := by
  intro t ht
  obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' ℝ (label F W c (X t) - label F W c (X 0))
  have hC : 0 ≤ C := by linarith [tube.one_le]
  have hM := tube.speed_nonneg
  have h := LipschitzLabel.displacement_le (K := Real.toNNReal (C * (1 + M))) hopen smooth
    (fun p hp => ⟨region a b V, hopen.mem_nhds hp, lipschitzOnWith tube ℓ hℓ⟩)
    (invariantOn tube ℓ) inU ode
    (fun s hs => by simpa [Real.coe_toNNReal _ (by positivity : 0 ≤ C * (1 + M))] using small s hs)
    t ht
  have hval' : ℓ (label F W c (X t)) - ℓ (label F W c (X 0))
      = ‖label F W c (X t) - label F W c (X 0)‖ := by
    rw [← map_sub]
    simpa using hval
  rw [← hval']
  exact (le_abs_self _).trans h

/-- A function with zero derivative within an interval takes the same value at its ends. -/
theorem SolOn.eq_of_zero {s t : ℝ} {v : ℝ → E}
    (sol : SolOn (fun _ _ => (0 : E)) (fun _ => univ) s t v) : v s = v t := by
  have h := sol.norm_sub_le (M := 0) (fun _ _ _ _ => by simp)
  have : v t - v s = 0 := by simpa using h
  exact (sub_eq_zero.mp this).symm

/-- Sanity: the zero field, with both tubes the whole space, satisfies the hypotheses with
contraction factor one and speed zero. -/
theorem tube_zero (a c b : ℝ) (h : c ∈ Ioo a b) :
    Tube (fun _ _ => (0 : E)) c a b (fun _ => univ) (fun _ => univ) 1 0 where
  section_mem := h
  one_le := le_rfl
  speed_nonneg := le_rfl
  reach _ _ x _ := ⟨fun _ => x, rfl, fun τ _ => ⟨hasDerivWithinAt_const τ _ x, mem_univ _⟩⟩
  contract _ _ u v su sv := by rw [su.eq_of_zero, sv.eq_of_zero, one_mul]
  unique _ _ _ _ u v su sv huv := by rw [su.eq_of_zero, sv.eq_of_zero, huv]
  speed _ _ _ _ := by simp

/-- Sanity: the label of the zero field is the space component. -/
theorem label_zero {a c b : ℝ} (h : c ∈ Ioo a b) {p : ℝ × E} (hp : p.1 ∈ Ioo a b) :
    label (fun _ _ => (0 : E)) (fun _ => univ) c p = p.2 :=
  label_eq (tube_zero a c b h) hp (v := fun _ => p.2) rfl
    (fun τ _ => ⟨hasDerivWithinAt_const τ _ p.2, mem_univ _⟩)

end PlasmaLean.Fields.FlowLabel
