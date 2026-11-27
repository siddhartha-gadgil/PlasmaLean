/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FlowLabel

/-!
# A two-sided flow tube from a one-sided tube and a time-reversal symmetry

For the equation `x' = F t x` and a section time `c`, a `HalfTube` collects the hypotheses of
`FlowLabel.Tube` on the times `t ≥ c` only, together with a linear isometric involution `σ` that
conjugates the field to its time reversal about `c`: `F (2 c - t) (σ x) = -σ (F t x)`. Reflecting
solutions by `τ ↦ σ (v (2 c - τ))` carries the hypotheses to the times `t ≤ c`.

* `HalfTube.double`: the reflected tubes `doubleW`, `doubleV` satisfy `Tube` on `(2 c - b, b)`.
* `isOpen_region_double`: the doubled inner region is open when the half region is relatively
  open in the half-space `t ≥ c`.
* `halfTube_zero`: the zero field with the identity reflection satisfies the hypotheses.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.FlowLabel
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `v` solves the equation on `[s, t]` and lies in the tube at the interior times. -/
def SolIn (F : ℝ → E → E) (W : ℝ → Set E) (s t : ℝ) (v : ℝ → E) : Prop :=
  (∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ) ∧ ∀ τ ∈ Ioo s t, v τ ∈ W τ

/-- One-sided tube after the section time `c`, with a reflection `σ` conjugating the field to its
time reversal about `c`. -/
structure HalfTube (F : ℝ → E → E) (σ : E ≃ₗᵢ[ℝ] E) (c b : ℝ) (W V : ℝ → Set E) (C M : ℝ) :
    Prop where
  /-- the time interval is nonempty -/
  lt : c < b
  /-- the contraction factor is at least one -/
  one_le : 1 ≤ C
  /-- the speed bound is nonnegative -/
  speed_nonneg : 0 ≤ M
  /-- the reflection is an involution -/
  involutive : ∀ x, σ (σ x) = x
  /-- from every point of the inner tube a solution reaches the section inside the outer tube -/
  reach : ∀ t ∈ Ico c b, ∀ x ∈ V t, ∃ v : ℝ → E, v t = x ∧ SolOn F W c t v
  /-- solutions in the outer tube at the interior times are no further apart at the section than
  `C` times their distance at time `t` -/
  contract : ∀ t ∈ Ico c b, ∀ u v : ℝ → E, SolIn F W c t u → SolIn F W c t v →
    ‖u c - v c‖ ≤ C * ‖u t - v t‖
  /-- uniqueness towards the section from any intermediate time -/
  unique : ∀ t ∈ Ico c b, ∀ s ∈ Icc c t, ∀ u v : ℝ → E, SolIn F W s t u → SolIn F W s t v →
    u t = v t → u s = v s
  /-- the field is bounded by `M` on the outer tube -/
  speed : ∀ t ∈ Ico c b, ∀ x ∈ W t, ‖F t x‖ ≤ M
  /-- the reflection conjugates the field to its time reversal about `c` -/
  symm : ∀ t ∈ Ico c b, ∀ x ∈ W t, F (2 * c - t) (σ x) = -σ (F t x)

/-- The outer tube extended to earlier times by reflection. -/
def doubleW (σ : E ≃ₗᵢ[ℝ] E) (c : ℝ) (W : ℝ → Set E) (t : ℝ) : Set E :=
  if c < t then W t else if t < c then σ '' W (2 * c - t) else W c ∪ σ '' W c

/-- The inner tube extended to earlier times by reflection. -/
def doubleV (σ : E ≃ₗᵢ[ℝ] E) (c : ℝ) (V : ℝ → Set E) (t : ℝ) : Set E :=
  if c < t then V t else if t < c then σ '' V (2 * c - t) else V c ∩ σ '' V c

/-- The part of space-time over the inner tube of a half tube. -/
def halfRegion (c b : ℝ) (V : ℝ → Set E) : Set (ℝ × E) := {p | p.1 ∈ Ico c b ∧ p.2 ∈ V p.1}

variable {F : ℝ → E → E} {σ : E ≃ₗᵢ[ℝ] E} {W V : ℝ → Set E} {c b C M : ℝ}

/-- After the section time the doubled outer tube is the given one. -/
theorem doubleW_of_lt {t : ℝ} (h : c < t) : doubleW σ c W t = W t := ite_eq_left h

/-- Before the section time the doubled outer tube is the reflected one. -/
theorem doubleW_of_gt {t : ℝ} (h : t < c) : doubleW σ c W t = σ '' W (2 * c - t) := by
  rw [doubleW, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]

/-- At the section time the doubled outer tube is the union of the two. -/
theorem doubleW_self : doubleW σ c W c = W c ∪ σ '' W c := by
  rw [doubleW, ite_eq_right (lt_irrefl c), ite_eq_right (lt_irrefl c)]

/-- After the section time the doubled inner tube is the given one. -/
theorem doubleV_of_lt {t : ℝ} (h : c < t) : doubleV σ c V t = V t := ite_eq_left h

/-- Before the section time the doubled inner tube is the reflected one. -/
theorem doubleV_of_gt {t : ℝ} (h : t < c) : doubleV σ c V t = σ '' V (2 * c - t) := by
  rw [doubleV, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]

/-- At the section time the doubled inner tube is the intersection of the two. -/
theorem doubleV_self : doubleV σ c V c = V c ∩ σ '' V c := by
  rw [doubleV, ite_eq_right (lt_irrefl c), ite_eq_right (lt_irrefl c)]

/-- From the section time on, the outer tube lies in the doubled one. -/
theorem subset_doubleW {t : ℝ} (h : c ≤ t) : W t ⊆ doubleW σ c W t := by
  rcases h.lt_or_eq with h | h
  · rw [doubleW_of_lt h]
  · rw [← h, doubleW_self]
    exact subset_union_left

/-- Membership in the image of a set under an involution. -/
theorem mem_image_involution (inv : ∀ x, σ (σ x) = x) {S : Set E} {x : E} :
    x ∈ σ '' S ↔ σ x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [inv]
  · exact fun hx => ⟨σ x, hx, inv x⟩

/-- A solution inside a tube lies in it at the interior times. -/
theorem SolOn.solIn {s t : ℝ} {v : ℝ → E} (hst : s ≤ t) (sol : SolOn F W s t v) :
    SolIn F W s t v := by
  have sol' : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ ∧ v τ ∈ W τ := by
    simpa only [SolOn, uIcc_of_le hst] using sol
  exact ⟨fun τ hτ => (sol' τ hτ).1, fun τ hτ => (sol' τ (Ioo_subset_Icc_self hτ)).2⟩

/-- A solution in the doubled tube after the section time lies in the given tube at the interior
times. -/
theorem SolOn.solIn_of_doubleW {s t : ℝ} {v : ℝ → E} (hcs : c ≤ s) (hst : s ≤ t)
    (sol : SolOn F (doubleW σ c W) s t v) : SolIn F W s t v := by
  have h := sol.solIn hst
  refine ⟨h.1, fun τ hτ => ?_⟩
  have hm := h.2 τ hτ
  rwa [doubleW_of_lt (lt_of_le_of_lt hcs hτ.1)] at hm

/-- A function with zero derivative within an interval takes the same value at its ends. -/
theorem SolIn.eq_of_zero {s t : ℝ} {v : ℝ → E} (hst : s ≤ t)
    (sol : SolIn (fun _ _ => (0 : E)) W s t v) : v s = v t := by
  have h := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := v) (f' := fun _ => (0 : E)) (C := 0) sol.1 (fun _ _ => by simp)
    (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  have : v t - v s = 0 := by simpa using h
  exact (sub_eq_zero.mp this).symm

/-- Derivative of the reflection `τ ↦ σ (v (2 c - τ))` of a curve. -/
theorem hasDerivWithinAt_reflect (σ : E ≃ₗᵢ[ℝ] E) {c s t τ : ℝ} {v : ℝ → E} {f' : E}
    (h : HasDerivWithinAt v f' (Icc s t) (2 * c - τ)) :
    HasDerivWithinAt (fun τ => σ (v (2 * c - τ))) (-σ f') (Icc (2 * c - t) (2 * c - s)) τ := by
  have inner : HasDerivWithinAt (fun τ : ℝ => 2 * c - τ) (-1) (Icc (2 * c - t) (2 * c - s)) τ := by
    simpa using ((hasDerivAt_id τ).const_sub (2 * c)).hasDerivWithinAt
  have maps : MapsTo (fun τ : ℝ => 2 * c - τ) (Icc (2 * c - t) (2 * c - s)) (Icc s t) :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have d := HasDerivWithinAt.scomp τ h inner maps
  have d2 := σ.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt τ d
  simpa [Function.comp_def] using d2

/-- The reflection of a solution is a solution when the field has the reflection symmetry along
it. -/
theorem hasDerivWithinAt_reflect_sol (σ : E ≃ₗᵢ[ℝ] E) {c s t s' t' : ℝ} {v : ℝ → E}
    (hs' : s' = 2 * c - t) (ht' : t' = 2 * c - s)
    (der : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (sym : ∀ τ ∈ Icc s t, F (2 * c - τ) (σ (v τ)) = -σ (F τ (v τ))) :
    ∀ τ ∈ Icc s' t', HasDerivWithinAt (fun τ => σ (v (2 * c - τ)))
      (F τ (σ (v (2 * c - τ)))) (Icc s' t') τ := by
  subst hs' ht'
  intro τ hτ
  have hτ' : 2 * c - τ ∈ Icc s t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have d := hasDerivWithinAt_reflect σ (der _ hτ')
  have e := sym _ hτ'
  rw [show 2 * c - (2 * c - τ) = τ by ring] at e
  rwa [← e] at d

namespace HalfTube

/-- The reflection symmetry of the field holds on the doubled outer tube. -/
theorem symm_double (h : HalfTube F σ c b W V C M) {t : ℝ} (ht : t ∈ Ioo (2 * c - b) b) {x : E}
    (hx : x ∈ doubleW σ c W t) : F (2 * c - t) (σ x) = -σ (F t x) := by
  rcases lt_trichotomy c t with hct | heq | htc
  · rw [doubleW_of_lt hct] at hx
    exact h.symm t ⟨hct.le, ht.2⟩ x hx
  · rw [← heq, doubleW_self] at hx
    rw [← heq]
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact h.symm c ⟨le_rfl, h.lt⟩ x hx
    · have key := h.symm c ⟨le_rfl, h.lt⟩ y hy
      rw [show 2 * c - c = c by ring] at key ⊢
      rw [h.involutive, key, map_neg, neg_neg, h.involutive]
  · rw [doubleW_of_gt htc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have key := h.symm (2 * c - t) ⟨by linarith, by linarith [ht.1]⟩ y hy
    rw [show 2 * c - (2 * c - t) = t by ring] at key
    rw [h.involutive, key, map_neg, neg_neg, h.involutive]

/-- A solution in the doubled tube before the section time reflects to a solution lying in the
given tube at the interior times. -/
theorem solIn_reflect (h : HalfTube F σ c b W V C M) {s t s' : ℝ} {v : ℝ → E}
    (ht : 2 * c - b < t) (hts : t ≤ s) (hsc : s ≤ c) (hs' : s' = 2 * c - s)
    (sol : SolOn F (doubleW σ c W) s t v) :
    SolIn F W s' (2 * c - t) (fun τ => σ (v (2 * c - τ))) := by
  subst hs'
  have sol' : ∀ τ ∈ Icc t s,
      HasDerivWithinAt v (F τ (v τ)) (Icc t s) τ ∧ v τ ∈ doubleW σ c W τ := by
    simpa only [SolOn, uIcc_of_ge hts] using sol
  refine ⟨hasDerivWithinAt_reflect_sol σ rfl rfl (fun τ hτ => (sol' τ hτ).1)
    (fun τ hτ => h.symm_double ⟨by linarith [hτ.1], by linarith [hτ.2, h.lt]⟩ (sol' τ hτ).2),
    fun τ hτ => ?_⟩
  have hm := (sol' (2 * c - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩).2
  rw [doubleW_of_gt (by linarith [hτ.1]), mem_image_involution h.involutive,
    show 2 * c - (2 * c - τ) = τ by ring] at hm
  exact hm

/-- A solution in the given tube after the section time reflects to a solution in the doubled
tube. -/
theorem solOn_reflect (h : HalfTube F σ c b W V C M) {t : ℝ} {w : ℝ → E} (htc : t < c)
    (hb : 2 * c - t < b) (sol : SolOn F W c (2 * c - t) w) :
    SolOn F (doubleW σ c W) c t (fun τ => σ (w (2 * c - τ))) := by
  have sol' : ∀ τ ∈ Icc c (2 * c - t),
      HasDerivWithinAt w (F τ (w τ)) (Icc c (2 * c - t)) τ ∧ w τ ∈ W τ := by
    simpa only [SolOn, uIcc_of_le (show c ≤ 2 * c - t by linarith)] using sol
  have der := hasDerivWithinAt_reflect_sol σ (s' := t) (t' := c) (c := c) (by ring) (by ring)
    (fun τ hτ => (sol' τ hτ).1)
    (fun τ hτ => h.symm τ ⟨hτ.1, by linarith [hτ.2]⟩ _ (sol' τ hτ).2)
  intro τ hτ
  rw [uIcc_of_ge htc.le] at hτ ⊢
  refine ⟨der τ hτ, ?_⟩
  have hm := (sol' (2 * c - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩).2
  change σ (w (2 * c - τ)) ∈ doubleW σ c W τ
  rcases hτ.2.lt_or_eq with hlt | heq
  · rw [doubleW_of_gt hlt]
    exact mem_image_of_mem σ hm
  · have e : 2 * c - τ = c := by linarith
    rw [e] at hm ⊢
    rw [heq, doubleW_self]
    exact Or.inr (mem_image_of_mem σ hm)

/-- **Doubling.** A one-sided tube with a time-reversal symmetry gives a two-sided tube around
the section time. -/
theorem double (h : HalfTube F σ c b W V C M) :
    Tube F c (2 * c - b) b (doubleW σ c W) (doubleV σ c V) C M where
  section_mem := ⟨by linarith [h.lt], h.lt⟩
  one_le := h.one_le
  speed_nonneg := h.speed_nonneg
  reach := by
    intro t ht x hx
    have lift : ∀ v : ℝ → E, c ≤ t → SolOn F W c t v → SolOn F (doubleW σ c W) c t v := by
      intro v hct sol τ hτ
      refine ⟨(sol τ hτ).1, subset_doubleW ?_ (sol τ hτ).2⟩
      rw [uIcc_of_le hct] at hτ
      exact hτ.1
    rcases lt_trichotomy c t with hct | heq | htc
    · rw [doubleV_of_lt hct] at hx
      obtain ⟨v, hv, sol⟩ := h.reach t ⟨hct.le, ht.2⟩ x hx
      exact ⟨v, hv, lift v hct.le sol⟩
    · rw [← heq, doubleV_self] at hx
      obtain ⟨v, hv, sol⟩ := h.reach t ⟨heq.le, ht.2⟩ x (heq ▸ hx.1)
      exact ⟨v, hv, lift v heq.le sol⟩
    · rw [doubleV_of_gt htc] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hb : 2 * c - t < b := by linarith [ht.1]
      obtain ⟨w, hw, sol⟩ := h.reach (2 * c - t) ⟨by linarith, hb⟩ y hy
      exact ⟨_, congrArg σ hw, h.solOn_reflect htc hb sol⟩
  contract := by
    intro t ht u v su sv
    rcases lt_trichotomy c t with hct | heq | htc
    · exact h.contract t ⟨hct.le, ht.2⟩ u v (su.solIn_of_doubleW le_rfl hct.le)
        (sv.solIn_of_doubleW le_rfl hct.le)
    · rw [← heq]
      exact le_mul_of_one_le_left (norm_nonneg _) h.one_le
    · have e1 : c = 2 * c - c := by ring
      have key := h.contract (2 * c - t) ⟨by linarith, by linarith [ht.1]⟩ _ _
        (h.solIn_reflect ht.1 htc.le le_rfl e1 su) (h.solIn_reflect ht.1 htc.le le_rfl e1 sv)
      beta_reduce at key
      rw [show 2 * c - c = c by ring, show 2 * c - (2 * c - t) = t by ring] at key
      rwa [← map_sub, ← map_sub, σ.norm_map, σ.norm_map] at key
  unique := by
    intro t ht s hs u v su sv huv
    rcases lt_trichotomy c t with hct | heq | htc
    · rw [uIcc_of_le hct.le] at hs
      exact h.unique t ⟨hct.le, ht.2⟩ s hs u v (su.solIn_of_doubleW hs.1 hs.2)
        (sv.solIn_of_doubleW hs.1 hs.2) huv
    · rw [← heq, uIcc_self, mem_singleton_iff] at hs
      rw [hs, heq]
      exact huv
    · rw [uIcc_of_ge htc.le] at hs
      have e : 2 * c - (2 * c - t) = t := by ring
      have e' : 2 * c - (2 * c - s) = s := by ring
      have key := h.unique (2 * c - t) ⟨by linarith, by linarith [ht.1]⟩ (2 * c - s)
        ⟨by linarith [hs.2], by linarith [hs.1]⟩ _ _
        (h.solIn_reflect ht.1 hs.1 hs.2 rfl su) (h.solIn_reflect ht.1 hs.1 hs.2 rfl sv)
        (by rw [e, huv])
      beta_reduce at key
      rw [e'] at key
      exact σ.injective key
  speed := by
    intro t ht x hx
    have key := h.symm_double ht hx
    have norm : ‖F t x‖ = ‖F (2 * c - t) (σ x)‖ := by rw [key, norm_neg, σ.norm_map]
    rcases lt_trichotomy c t with hct | heq | htc
    · rw [doubleW_of_lt hct] at hx
      exact h.speed t ⟨hct.le, ht.2⟩ x hx
    · rw [← heq, doubleW_self] at hx
      rcases hx with hx | hx
      · exact h.speed t ⟨heq.le, ht.2⟩ x (heq ▸ hx)
      · rw [mem_image_involution h.involutive] at hx
        rw [norm, ← heq, show 2 * c - c = c by ring]
        exact h.speed c ⟨le_rfl, h.lt⟩ _ hx
    · rw [doubleW_of_gt htc, mem_image_involution h.involutive] at hx
      rw [norm]
      exact h.speed (2 * c - t) ⟨by linarith, by linarith [ht.1]⟩ _ hx

end HalfTube

omit [NormedSpace ℝ E] in
/-- The half region together with the earlier half-space is open when the half region is
relatively open in the later half-space. -/
theorem isOpen_halfRegion_union
    (rel : ∀ p ∈ halfRegion c b V, halfRegion c b V ∈ 𝓝[{q : ℝ × E | c ≤ q.1}] p) :
    IsOpen (halfRegion c b V ∪ {q : ℝ × E | q.1 < c}) := by
  rw [isOpen_iff_mem_nhds]
  rintro p (hp | hp)
  · obtain ⟨U, hU, hpU, hsub⟩ := mem_nhdsWithin.mp (rel p hp)
    refine mem_of_superset (hU.mem_nhds hpU) fun q hq => ?_
    rcases le_or_gt c q.1 with hq' | hq'
    · exact Or.inl (hsub ⟨hq, hq'⟩)
    · exact Or.inr hq'
  · exact mem_of_superset ((isOpen_lt continuous_fst continuous_const).mem_nhds hp)
      subset_union_right

/-- **Openness of the doubled region.** If the half region is relatively open in the half-space
`t ≥ c`, the region over the doubled inner tube is open. -/
theorem isOpen_region_double (σ : E ≃ₗᵢ[ℝ] E) (inv : ∀ x, σ (σ x) = x) (hcb : c < b)
    (rel : ∀ p ∈ halfRegion c b V, halfRegion c b V ∈ 𝓝[{q : ℝ × E | c ≤ q.1}] p) :
    IsOpen (region (2 * c - b) b (doubleV σ c V)) := by
  have hA := isOpen_halfRegion_union rel
  have hΦ : Continuous fun q : ℝ × E => ((2 * c - q.1, σ q.2) : ℝ × E) :=
    (continuous_const.sub continuous_fst).prodMk (σ.continuous.comp continuous_snd)
  convert hA.inter (hA.preimage hΦ) using 1
  ext ⟨t, x⟩
  simp only [region, halfRegion, mem_ofPred_eq, mem_inter_iff, mem_union, mem_preimage, mem_Ioo,
    mem_Ico]
  rcases lt_trichotomy c t with hct | heq | htc
  · rw [doubleV_of_lt hct]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨Or.inl ⟨⟨hct.le, h2⟩, h3⟩, Or.inr (by linarith)⟩
    · rintro ⟨⟨⟨_, h2⟩, h3⟩ | h1, _⟩
      · exact ⟨⟨by linarith, h2⟩, h3⟩
      · linarith
  · rw [← heq, doubleV_self, mem_inter_iff, mem_image_involution inv,
      show 2 * c - c = c by ring]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨Or.inl ⟨⟨le_rfl, hcb⟩, h1⟩, Or.inl ⟨⟨le_rfl, hcb⟩, h2⟩⟩
    · rintro ⟨⟨_, h1⟩ | h1, ⟨_, h2⟩ | h2⟩
      · exact ⟨⟨by linarith, hcb⟩, h1, h2⟩
      · exact absurd h2 (lt_irrefl c)
      · exact absurd h1 (lt_irrefl c)
      · exact absurd h1 (lt_irrefl c)
  · rw [doubleV_of_gt htc, mem_image_involution inv]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨Or.inr htc, Or.inl ⟨⟨by linarith, by linarith⟩, h3⟩⟩
    · rintro ⟨_, ⟨⟨_, h2⟩, h3⟩ | h1⟩
      · exact ⟨⟨by linarith, by linarith⟩, h3⟩
      · linarith

/-- Sanity: the zero field, with the identity reflection and both tubes the whole space,
satisfies the hypotheses with contraction factor one and speed zero. -/
theorem halfTube_zero (hcb : c < b) :
    HalfTube (fun _ _ => (0 : E)) (LinearIsometryEquiv.refl ℝ E) c b (fun _ => univ)
      (fun _ => univ) 1 0 where
  lt := hcb
  one_le := le_rfl
  speed_nonneg := le_rfl
  involutive _ := rfl
  reach _ _ x _ := ⟨fun _ => x, rfl, fun τ _ => ⟨hasDerivWithinAt_const τ _ x, mem_univ _⟩⟩
  contract t ht u v su sv := by rw [su.eq_of_zero ht.1, sv.eq_of_zero ht.1, one_mul]
  unique t _ s hs u v su sv huv := by rw [su.eq_of_zero hs.2, sv.eq_of_zero hs.2, huv]
  speed _ _ _ _ := by simp
  symm _ _ _ _ := by simp

/-- Sanity: the doubled zero half tube is a two-sided tube for the zero field. -/
theorem tube_double_zero (hcb : c < b) :
    Tube (fun _ _ => (0 : E)) c (2 * c - b) b
      (doubleW (LinearIsometryEquiv.refl ℝ E) c fun _ => univ)
      (doubleV (LinearIsometryEquiv.refl ℝ E) c fun _ => univ) 1 0 :=
  (halfTube_zero hcb).double

end PlasmaLean.Fields.FlowLabel
