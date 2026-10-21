/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedPeriodic
public import PlasmaLean.Theory.Fields.FieldLineExistence

/-!
# Existence and uniqueness of the exact-QA reference orbits of trapped alphas

Companion to `notes/theory/trapped-alpha-status.md` (§3 item 4). Model only: the exactly
quasi-axisymmetric member `exactQA` of the reactor near-axis family, vacuum Boozer guiding-centre
equations. The re-anchored bounce scheme (`NearAxisQATrappedReanchor`) restarts an exact-QA
reference orbit at every upper turning point. Until now these references were *supplied* (the
`Setup` hypothesis); here they are constructed.

Results:

* `exactQA_reference_exists`: for every tip state `(ψ₀, θ₀, φ₀)` with `ψ₀ ∈ [4.75, 5.79]`,
  `θ₀ ∈ (0, π/2)` and magnetic moment `μ = E/B_exact(ψ₀, θ₀)` in the pitch window, there is an
  **all-time** exact-QA guiding-centre orbit (`BoozerGCOrbit`) through it with `ρ(0) = 0`. It
  satisfies `Setup μ T` for every `T`, so every theorem stated for `Setup` applies to it
  unconditionally (`exactQA_bounce_precession`, `exactQA_bounce_period`, `reference_kick_tight`).
* `exactQA_reference_unique`: two orbits in the setting `Setup μ T` with the same initial state
  coincide on `[0, T]`.

**Method.** The reduced field `vred μ` (`NearAxisQATrappedPeriodic`) is `C¹` on the open half-space
`ψ > 0` and does not depend on `φ`. The set
`refSet μ ψ₀ = {E_red = E, ρ − kinv ψ = −kinv ψ₀, ψ ∈ [ψ_lo, ψ_a], |θ| ≤ π/2}`
lies in the compact box `redBox`. It is invariant for local solutions in both time directions:

* the energy `E_red` and the helical momentum `ρ − kinv ψ` are conserved wherever `ψ > 0`
  (`hasDerivAt_Ered`, `hasDerivAt_Pred`);
* on the level set the closed constraints hold strictly (`refSet_strict`: `|ρ| ≤ ρ_max` gives
  `ψ ∈ (ψ_lo, ψ_a)`, and `μB ≤ E < μB(θ = ±π/2)` gives `|θ| < π/2`);
* so a first exit is impossible (`refSet_forward`). Backward time follows from the reflection
  symmetry `(ψ, θ, ρ)(t) ↦ (ψ, −θ, ρ)(−t)` of the reduced equations (`vred_reflect`).

Global existence and uniqueness then follow from `ODEGlobal.existsUnique_global`
(`Theory/Fields/FieldLineExistence`). The toroidal angle is recovered by quadrature,
`φ = φ₀ + ∫₀ᵗ wred`.
-/

public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedReference
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Design.NearAxisQATrappedResonance PlasmaLean.Design.NearAxisQATrappedPeriodic
  PlasmaLean.Fields Real Set

/-! ## Reduced conserved quantities -/

/-- The reduced energy `q²ρ²B²/(2m) + μB` of a reduced state `(ψ, θ, ρ)`. -/
@[expose] def Ered (μ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  qα ^ 2 * p.2.2 ^ 2 * Bf p.1 p.2.1 ^ 2 / (2 * mα) + μ * Bf p.1 p.2.1

/-- The reduced helical momentum `ρ − (ι₀/G) ψ` (exact QA). -/
@[expose] def Pred (p : ℝ × ℝ × ℝ) : ℝ := p.2.2 - kinv * p.1

/-- The invariant set of the reference orbit with constants `μ` and tip flux `ψ₀`. -/
@[expose] def refSet (μ ψ₀ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | Ered μ p = Eα ∧ Pred p = -(kinv * ψ₀) ∧ p.1 ∈ Icc psiLo psiEdge ∧ |p.2.1| ≤ π / 2}

/-- `B` of exact QA is `Bf`. -/
theorem exactQA_B_Bf (x th φ : ℝ) : exactQA.B x th φ = Bf x th := by rw [exactQA_B_eq]; rfl

/-- `∂_ψB` of exact QA is `Bψf`. -/
theorem exactQA_Bψ_Bψf (x th φ : ℝ) : exactQA.Bψ x th φ = Bψf x th := by
  rw [exactQA_Bψ_eq]; rfl

/-- `∂_θB` of exact QA is `Bθf`. -/
theorem exactQA_Bθ_Bθf (x th φ : ℝ) : exactQA.Bθ x th φ = Bθf x th := by
  rw [exactQA_Bθ_eq]; rfl

/-- First component of a derivative. -/
theorem hasDerivAt_c1 {α : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ} (hα : HasDerivAt α v t) :
    HasDerivAt (fun s => (α s).1) v.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t hα

/-- Second component of a derivative. -/
theorem hasDerivAt_c2 {α : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ} (hα : HasDerivAt α v t) :
    HasDerivAt (fun s => (α s).2.1) v.2.1 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t hα)

/-- Third component of a derivative. -/
theorem hasDerivAt_c3 {α : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ} (hα : HasDerivAt α v t) :
    HasDerivAt (fun s => (α s).2.2) v.2.2 t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t hα)

/-- Chain rule for `Bf` along a curve in the half-space `ψ > 0`. -/
theorem hasDerivAt_Bf {α : ℝ → ℝ × ℝ × ℝ} {v : ℝ × ℝ × ℝ} {t : ℝ} (hα : HasDerivAt α v t)
    (hp : 0 < (α t).1) :
    HasDerivAt (fun s => Bf (α s).1 (α s).2.1)
      (Bψf (α t).1 (α t).2.1 * v.1 + Bθf (α t).1 (α t).2.1 * v.2.1) t := by
  have hc : HasDerivAt (fun s => ((α s).1, (α s).2.1, (0 : ℝ))) (v.1, v.2.1, 0) t :=
    (hasDerivAt_c1 hα).prodMk ((hasDerivAt_c2 hα).prodMk (hasDerivAt_const t 0))
  have h := (exactQA.hasFDerivAt_B ((α t).1, (α t).2.1, 0) hp).comp_hasDerivAt t hc
  simp only [Function.comp_def, gradCLM_apply, mul_zero, add_zero, exactQA_B_Bf, exactQA_Bψ_Bψf,
    exactQA_Bθ_Bθf] at h
  exact h

/-- **Energy conservation** for the reduced equations (where `ψ > 0`). -/
theorem hasDerivAt_Ered {μ : ℝ} {α : ℝ → ℝ × ℝ × ℝ} {t : ℝ}
    (hα : HasDerivAt α (vred μ (α t)) t) (hp : 0 < (α t).1) :
    HasDerivAt (fun s => Ered μ (α s)) 0 t := by
  have hB := hasDerivAt_Bf hα hp
  have hρ := hasDerivAt_c3 hα
  have h := ((((hρ.pow 2).mul (hB.pow 2)).const_mul (qα ^ 2)).div_const (2 * mα)).add
    (hB.const_mul μ)
  have e : (fun s => Ered μ (α s)) = fun s => qα ^ 2 * ((α s).2.2 ^ 2 *
      Bf (α s).1 (α s).2.1 ^ 2) / (2 * mα) + μ * Bf (α s).1 (α s).2.1 := by
    funext s; unfold Ered; ring
  rw [e]
  refine h.congr_deriv ?_
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  simp only [vred, Pi.pow_apply]
  norm_num
  field_simp
  ring

/-- **Helical momentum conservation** for the reduced equations. -/
theorem hasDerivAt_Pred {μ : ℝ} {α : ℝ → ℝ × ℝ × ℝ} {t : ℝ}
    (hα : HasDerivAt α (vred μ (α t)) t) :
    HasDerivAt (fun s => Pred (α s)) 0 t := by
  have h := (hasDerivAt_c3 hα).sub ((hasDerivAt_c1 hα).const_mul kinv)
  refine h.congr_deriv ?_
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  simp only [vred, kinv]
  field_simp
  ring

/-- `Bf` is continuous. -/
theorem continuous_Bf : Continuous fun p : ℝ × ℝ × ℝ => Bf p.1 p.2.1 := by
  unfold Bf; fun_prop

/-- `Ered μ` is continuous. -/
theorem continuous_Ered (μ : ℝ) : Continuous (Ered μ) := by
  have := continuous_Bf
  unfold Ered; fun_prop

/-- `wred` is continuous. -/
theorem continuous_wred : Continuous wred := by
  have := continuous_Bf
  unfold wred; fun_prop

/-- **Conservation on an interval**: if `α` solves the reduced equations on `[0, b]` and
`ψ > 0` on `[0, b)`, then `E_red` and `ρ − kinv ψ` are constant on `[0, b]`. -/
theorem conserved_on {μ b : ℝ} {α : ℝ → ℝ × ℝ × ℝ}
    (hα : ∀ t ∈ Icc 0 b, HasDerivAt α (vred μ (α t)) t) (hpos : ∀ t ∈ Ico 0 b, 0 < (α t).1) :
    ∀ t ∈ Icc 0 b, Ered μ (α t) = Ered μ (α 0) ∧ Pred (α t) = Pred (α 0) := by
  have hαc : ContinuousOn α (Icc 0 b) := fun t ht => (hα t ht).continuousAt.continuousWithinAt
  have h1 := constant_of_has_deriv_right_zero (f := fun s => Ered μ (α s)) (a := 0) (b := b)
    ((continuous_Ered μ).comp_continuousOn hαc)
    (fun x hx => (hasDerivAt_Ered (hα x (Ico_subset_Icc_self hx)) (hpos x hx)).hasDerivWithinAt)
  have hPc : Continuous Pred := by unfold Pred; fun_prop
  have h2 := constant_of_has_deriv_right_zero (f := fun s => Pred (α s)) (a := 0) (b := b)
    (hPc.comp_continuousOn hαc)
    (fun x hx => (hasDerivAt_Pred (hα x (Ico_subset_Icc_self hx))).hasDerivWithinAt)
  exact fun t ht => ⟨h1 t ht, h2 t ht⟩

/-! ## The invariant set -/

/-- **Strictness on the level set.** A point of `refSet μ ψ₀` (pitch window, start window) has
`ψ ∈ (ψ_lo, ψ_a)`, `|θ| < π/2` and `|ρ| ≤ ρ_max`. -/
theorem refSet_strict {μ ψ₀ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) {p : ℝ × ℝ × ℝ} (hp : p ∈ refSet μ ψ₀) :
    p.1 ∈ Ioo psiLo psiEdge ∧ |p.2.1| < π / 2 ∧ |p.2.2| ≤ rhoMax := by
  obtain ⟨hE, hP, hψ, hθ⟩ := hp
  have W := qaField_window (b₁ := 0) (by norm_num) hμ
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hB : 493 / 100 ≤ Bf p.1 p.2.1 := by
    rw [← exactQA_B_Bf p.1 p.2.1 0]
    exact qaField_B_ge (by norm_num) (le_trans (by norm_num [psiLo]) hψ.1) hψ.2 _ _
  have hρ : |p.2.2| ≤ rhoMax :=
    abs_rho_le_of_energy (F := exactQA) (ψ := fun _ => p.1) (θ := fun _ => p.2.1)
      (φ := fun _ => 0) (ρ := fun _ => p.2.2) (t := 0) (by norm_num [mα]) (by norm_num [qα])
      hμ0.le (by norm_num) (by norm_num [rhoMax])
      (by simp only [along]; rw [exactQA_B_Bf]; exact hB)
      (by simp only [along]; rw [exactQA_B_Bf]; exact hE) W.rho_bound
  have hρψ : p.2.2 = kinv * (p.1 - ψ₀) := by unfold Pred at hP; linarith
  refine ⟨?_, ?_, hρ⟩
  · have hk : 211 / 29050 * |p.1 - ψ₀| ≤ 177 / 10000 := by
      have := hρ
      rw [hρψ, abs_mul, abs_of_pos (by norm_num [kinv])] at this
      simpa [kinv, rhoMax] using this
    have hd : |p.1 - ψ₀| ≤ 177 / 10000 * (29050 / 211) := by linarith
    have := abs_le.mp hd
    constructor
    · unfold psiLo; linarith [hψ₀.1, this.1]
    · unfold psiEdge; linarith [hψ₀.2, this.2]
  · rcases lt_or_eq_of_le hθ with h | h
    · exact h
    · exfalso
      have hkin : μ * Bf p.1 p.2.1 ≤ Eα := by
        have : 0 ≤ qα ^ 2 * p.2.2 ^ 2 * Bf p.1 p.2.1 ^ 2 / (2 * mα) := by
          have : (0 : ℝ) < mα := by norm_num [mα]
          positivity
        unfold Ered at hE; linarith
      rcases abs_eq (by positivity : (0 : ℝ) ≤ π / 2) |>.mp h with h' | h'
      · have := W.forbid_pos p.1 hψ 0
        rw [show (qaField 0).B p.1 (π / 2) 0 = Bf p.1 (π / 2) from exactQA_B_Bf _ _ _, ← h']
          at this
        linarith
      · have := W.forbid_neg p.1 hψ 0
        rw [show (qaField 0).B p.1 (-(π / 2)) 0 = Bf p.1 (-(π / 2)) from exactQA_B_Bf _ _ _,
          ← h'] at this
        linarith

/-- The open window `ψ ∈ (ψ_lo, ψ_a)`, `|θ| < π/2`. -/
@[expose] def openWin : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Ioo psiLo psiEdge ∧ |p.2.1| < π / 2}

/-- The closed window `ψ ∈ [ψ_lo, ψ_a]`, `|θ| ≤ π/2`. -/
@[expose] def closedWin : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Icc psiLo psiEdge ∧ |p.2.1| ≤ π / 2}

/-- `openWin` is open. -/
theorem isOpen_openWin : IsOpen openWin := by
  unfold openWin
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const)

/-- `closedWin` is closed. -/
theorem isClosed_closedWin : IsClosed closedWin := by
  unfold closedWin
  exact (isClosed_Icc.preimage continuous_fst).inter
    (isClosed_le (continuous_abs.comp (continuous_fst.comp continuous_snd)) continuous_const)

/-- **Forward invariance** (first-exit argument): a solution of the reduced equations on
`[0, b]` starting in `refSet μ ψ₀` stays in it. -/
theorem refSet_forward {μ ψ₀ b : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) {α : ℝ → ℝ × ℝ × ℝ}
    (hα : ∀ t ∈ Icc 0 b, HasDerivAt α (vred μ (α t)) t) (h0 : α 0 ∈ refSet μ ψ₀) :
    ∀ t ∈ Icc 0 b, α t ∈ refSet μ ψ₀ := by
  have hαc : ContinuousOn α (Icc 0 b) := fun t ht => (hα t ht).continuousAt.continuousWithinAt
  have hpsi : ∀ p ∈ openWin, 0 < p.1 := fun p hp => lt_trans (by norm_num [psiLo]) hp.1.1
  have hsub : openWin ⊆ closedWin := fun p hp =>
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.le⟩
  have h0W : α 0 ∈ openWin := by
    obtain ⟨h1, h2, -⟩ := refSet_strict hμ hψ₀ h0
    exact ⟨h1, h2⟩
  -- the reduced state never leaves the open window
  have key : ∀ t ∈ Icc 0 b, α t ∈ openWin := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, hW⟩ := hcon
    set C := {t | t ∈ Icc 0 b ∧ α t ∉ openWin} with hC
    have hCc : IsClosed C := hαc.preimage_isClosed_of_isClosed isClosed_Icc
      isOpen_openWin.isClosed_compl
    have hne : C.Nonempty := ⟨t₁, ht₁, hW⟩
    have hbdd : BddBelow C := ⟨0, fun t ht => ht.1.1⟩
    set s := sInf C with hs
    have hsC : s ∈ C := hCc.csInf_mem hne hbdd
    have hs0 : 0 < s := by
      rcases eq_or_lt_of_le hsC.1.1 with h | h
      · exfalso; rw [← h] at hsC; exact hsC.2 h0W
      · exact h
    have hbefore : ∀ t ∈ Ico 0 s, α t ∈ openWin := by
      intro t ht
      by_contra h
      have : s ≤ t := csInf_le hbdd ⟨⟨ht.1, ht.2.le.trans hsC.1.2⟩, h⟩
      linarith [ht.2]
    -- conservation on `[0, s]`
    have hcons := conserved_on (b := s) (fun t ht => hα t ⟨ht.1, ht.2.trans hsC.1.2⟩)
      (fun t ht => hpsi _ (hbefore t ht))
    -- the closed window at `s`, by continuity
    have hD : IsClosed {t | t ∈ Icc 0 s ∧ α t ∈ closedWin} :=
      (hαc.mono (Icc_subset_Icc le_rfl hsC.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_closedWin
    have hIco : Ico 0 s ⊆ {t | t ∈ Icc 0 s ∧ α t ∈ closedWin} := fun t ht =>
      ⟨⟨ht.1, ht.2.le⟩, hsub (hbefore t ht)⟩
    have hcl := hD.closure_subset_iff.mpr hIco
    rw [closure_Ico hs0.ne] at hcl
    have hsW := (hcl ⟨hs0.le, le_rfl⟩).2
    obtain ⟨hE0, hP0, -, -⟩ := h0
    have hsR : α s ∈ refSet μ ψ₀ :=
      ⟨(hcons s ⟨hs0.le, le_rfl⟩).1.trans hE0, (hcons s ⟨hs0.le, le_rfl⟩).2.trans hP0,
        hsW.1, hsW.2⟩
    obtain ⟨h1, h2, -⟩ := refSet_strict hμ hψ₀ hsR
    exact hsC.2 ⟨h1, h2⟩
  have hcons := conserved_on hα (fun t ht => hpsi _ (key t (Ico_subset_Icc_self ht)))
  obtain ⟨hE0, hP0, -, -⟩ := h0
  intro t ht
  exact ⟨(hcons t ht).1.trans hE0, (hcons t ht).2.trans hP0, (hsub (key t ht)).1,
    (hsub (key t ht)).2⟩

/-! ## Reflection symmetry and two-sided invariance -/

/-- The reflection `(ψ, θ, ρ) ↦ (ψ, −θ, ρ)`. -/
@[expose] def refl (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, -p.2.1, p.2.2)

/-- **Reflection symmetry of the reduced field**: `vred (ψ, −θ, ρ) = (−v₁, v₂, −v₃)(ψ, θ, ρ)`. -/
theorem vred_reflect (μ : ℝ) (p : ℝ × ℝ × ℝ) :
    vred μ (refl p) = (-(vred μ p).1, (vred μ p).2.1, -(vred μ p).2.2) := by
  obtain ⟨x, th, r⟩ := p
  simp only [vred, refl, Bf, Bψf, Bθf, cos_neg, sin_neg, Prod.mk.injEq]
  exact ⟨by ring, trivial, by ring⟩

/-- `refSet` is invariant under the reflection. -/
theorem refl_mem {μ ψ₀ : ℝ} {p : ℝ × ℝ × ℝ} (hp : p ∈ refSet μ ψ₀) : refl p ∈ refSet μ ψ₀ := by
  obtain ⟨hE, hP, hψ, hθ⟩ := hp
  refine ⟨?_, hP, hψ, by simpa [refl] using hθ⟩
  simpa [Ered, refl, Bf, cos_neg] using hE

/-- **Two-sided invariance**: `refSet μ ψ₀` is invariant for local solutions of the reduced
equations on any closed interval `[a, b] ∋ 0` (the hypothesis of `ODEGlobal.exists_global`). -/
theorem refSet_locallyInvariant {μ ψ₀ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) :
    ODEGlobal.LocallyInvariant (vred μ) (refSet μ ψ₀) := by
  intro a b α ha hb h0 hα t ht
  rcases le_total 0 t with h | h
  · exact refSet_forward hμ hψ₀ (fun s hs => hα s ⟨ha.trans hs.1, hs.2⟩) h0 t ⟨h, ht.2⟩
  · -- the reflected, time-reversed curve
    set β : ℝ → ℝ × ℝ × ℝ := fun s => refl (α (-s)) with hβ
    have hβd : ∀ s ∈ Icc 0 (-a), HasDerivAt β (vred μ (β s)) s := by
      intro s hs
      have hs' : -s ∈ Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hc := (hα (-s) hs').scomp s (hasDerivAt_neg s)
      have h1 := hasDerivAt_c1 hc
      have h2 := (hasDerivAt_c2 hc).neg
      have h3 := hasDerivAt_c3 hc
      have := h1.prodMk (h2.prodMk h3)
      convert this using 1
      · rw [hβ]; funext x; simp [refl]
      · change vred μ (refl (α (-s))) = _
        rw [vred_reflect]
        simp
    have hβ0 : β 0 ∈ refSet μ ψ₀ := by
      simp only [hβ, neg_zero]; exact refl_mem h0
    have := refSet_forward hμ hψ₀ hβd hβ0 (-t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [hβ, neg_neg] at this
    have h2 := refl_mem this
    simpa [refl] using h2

/-- `refSet μ ψ₀ ⊆ redBox`. -/
theorem refSet_subset_redBox {μ ψ₀ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) : refSet μ ψ₀ ⊆ redBox := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := refSet_strict hμ hψ₀ hp
  have hπ := pi_lt_d2
  have hθ := abs_lt.mp h2
  have hρ := abs_le.mp (h3.trans (by norm_num [rhoMax] : rhoMax ≤ 1))
  exact ⟨⟨h1.1.le, h1.2.le⟩, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hρ.1, hρ.2⟩

/-! ## Existence and uniqueness -/

/-- **Global existence of the exact-QA reference orbit.** Let `(ψ₀, θ₀, φ₀)` be an upper tip
state of the start window (`ψ₀ ∈ [4.75, 5.79] T m²`, `θ₀ ∈ (0, π/2)`) and let the magnetic moment
`μ` (pitch window `E/μ ∈ [5.4, 5.5] T`) satisfy `μ B_exact(ψ₀, θ₀) = E`, so the tip is a turning
point. Then there is an all-time exact-QA guiding-centre orbit through the tip with `ρ(0) = 0`.
It satisfies `Setup μ T` for every `T`, and it stays in `ψ ∈ (ψ_lo, ψ_a)`, `|θ| < π/2` for all
`t ∈ ℝ`. -/
theorem exactQA_reference_exists {μ ψ₀ θ₀ φ₀ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) (hθ₀ : θ₀ ∈ Ioo 0 (π / 2))
    (hE : μ * exactQA.B ψ₀ θ₀ φ₀ = Eα) :
    ∃ ψ θ φ ρ : ℝ → ℝ, BoozerGCOrbit exactQA mα qα μ ψ θ φ ρ ∧ ψ 0 = ψ₀ ∧ θ 0 = θ₀ ∧
      φ 0 = φ₀ ∧ ρ 0 = 0 ∧ (∀ T, Setup μ T ψ θ φ ρ) ∧
      ∀ t, ψ t ∈ Ioo psiLo psiEdge ∧ |θ t| < π / 2 := by
  have hx₀ : ((ψ₀, θ₀, 0) : ℝ × ℝ × ℝ) ∈ refSet μ ψ₀ := by
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simp only [Ered]; rw [← exactQA_B_Bf ψ₀ θ₀ φ₀]; simpa using hE
    · simp [Pred]
    · unfold psiLo; linarith [hψ₀.1]
    · unfold psiEdge; linarith [hψ₀.2]
    · rw [abs_of_pos hθ₀.1]; exact hθ₀.2.le
  have hU : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hf : ContDiffOn ℝ 1 (vred μ) {p : ℝ × ℝ × ℝ | 0 < p.1} :=
    fun p hp => (vred_contDiffAt μ hp).contDiffWithinAt
  have hK : IsCompact redBox := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKU : redBox ⊆ {p : ℝ × ℝ × ℝ | 0 < p.1} := fun p hp =>
    lt_of_lt_of_le (by norm_num [psiLo]) hp.1.1
  obtain ⟨⟨γ, ⟨hγ0, hγ⟩, -⟩, hmem⟩ := ODEGlobal.existsUnique_global hU hf hK hKU
    (refSet_subset_redBox hμ hψ₀) (refSet_locallyInvariant hμ hψ₀) hx₀
  have hγΩ : ∀ t, γ t ∈ refSet μ ψ₀ := hmem γ hγ0 hγ
  have hstrict : ∀ t, (γ t).1 ∈ Ioo psiLo psiEdge ∧ |(γ t).2.1| < π / 2 ∧ |(γ t).2.2| ≤ rhoMax :=
    fun t => refSet_strict hμ hψ₀ (hγΩ t)
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  have hwc : Continuous fun s => wred (γ s) := continuous_wred.comp hγc
  set φ : ℝ → ℝ := fun t => φ₀ + ∫ s in (0 : ℝ)..t, wred (γ s) with hφ
  have hφd : ∀ t, HasDerivAt φ (wred (γ t)) t := fun t =>
    ((hwc.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add φ₀
  have hpos : ∀ t, 0 < (γ t).1 := fun t => lt_trans (by norm_num [psiLo]) (hstrict t).1.1
  have hφ0 : φ 0 = φ₀ := by simp [hφ]
  have horbit : BoozerGCOrbit exactQA mα qα μ (fun t => (γ t).1) (fun t => (γ t).2.1) φ
      (fun t => (γ t).2.2) := by
    refine ⟨hpos, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · convert hasDerivAt_c1 (hγ t) using 1
      simp only [along, exactQA_B_Bf, exactQA_Bθ_Bθf, vred]
    · convert hasDerivAt_c2 (hγ t) using 1
      simp only [along, exactQA_B_Bf, exactQA_Bψ_Bψf, vred, show exactQA.ι ((γ t).1) = 211 / 500
        from rfl, show exactQA.G = 581 / 10 from rfl]
    · convert hφd t using 1
      simp only [along, exactQA_B_Bf, wred, show exactQA.G = 581 / 10 from rfl]
    · convert hasDerivAt_c3 (hγ t) using 1
      simp only [along, exactQA_B_Bf, exactQA_Bθ_Bθf, exactQA_Bφ, vred,
        show exactQA.ι ((γ t).1) = 211 / 500 from rfl, show exactQA.G = 581 / 10 from rfl]
  refine ⟨fun t => (γ t).1, fun t => (γ t).2.1, φ, fun t => (γ t).2.2, horbit,
    by simp [hγ0], by simp [hγ0], hφ0, by simp [hγ0], fun T => ?_,
    fun t => ⟨(hstrict t).1, (hstrict t).2.1⟩⟩
  refine ⟨hμ, horbit.on T, ?_, by simp [hγ0], by simpa [hγ0] using hψ₀, by simpa [hγ0] using hθ₀⟩
  simp only [boozerEnergy, along, hγ0, hφ0]
  simpa using hE

/-- **Uniqueness of the exact-QA reference orbit on `[0, T]`.** Two orbits in the setting
`Setup μ T` (same `μ`) with the same initial state `(ψ, θ, φ, ρ)(0)` coincide on `[0, T]`
(Grönwall uniqueness with the Lipschitz constant of `vred μ` on `redBox`, and quadrature
for `φ`). -/
theorem exactQA_reference_unique {μ T : ℝ} {ψ θ φ ρ ψ' θ' φ' ρ' : ℝ → ℝ}
    (S : Setup μ T ψ θ φ ρ) (S' : Setup μ T ψ' θ' φ' ρ')
    (hψ : ψ' 0 = ψ 0) (hθ : θ' 0 = θ 0) (hφ : φ' 0 = φ 0) (hρ : ρ' 0 = ρ 0) :
    ∀ t ∈ Icc 0 T, ψ' t = ψ t ∧ θ' t = θ t ∧ φ' t = φ t ∧ ρ' t = ρ t := by
  obtain ⟨K, hK⟩ := exists_lipschitz_vred μ
  have hred := ODE_solution_unique_of_mem_Icc_right (v := fun _ => vred μ) (s := fun _ => redBox)
    (K := K) (f := fun s => (ψ' s, θ' s, ρ' s)) (g := fun s => (ψ s, θ s, ρ s)) (a := 0) (b := T)
    (fun _ _ => hK)
    (fun u hu => (S'.hasDerivAt_red hu).continuousAt.continuousWithinAt)
    (fun u hu => (S'.hasDerivAt_red (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => S'.mem_redBox (Ico_subset_Icc_self hu))
    (fun u hu => (S.hasDerivAt_red hu).continuousAt.continuousWithinAt)
    (fun u hu => (S.hasDerivAt_red (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => S.mem_redBox (Ico_subset_Icc_self hu))
    (by simp only [hψ, hθ, hρ])
  have hstate : ∀ t ∈ Icc 0 T, ψ' t = ψ t ∧ θ' t = θ t ∧ ρ' t = ρ t := by
    intro t ht
    have := hred ht
    simp only [Prod.mk.injEq] at this
    exact this
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => φ' s - φ s) 0 t := by
    intro t ht
    have h := (S'.hasDerivAt_phi ht).sub (S.hasDerivAt_phi ht)
    obtain ⟨e1, e2, e3⟩ := hstate t ht
    rw [e1, e2, e3, sub_self] at h
    exact h
  have hc := constant_of_has_deriv_right_zero (f := fun s => φ' s - φ s) (a := 0) (b := T)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
  intro t ht
  obtain ⟨e1, e2, e3⟩ := hstate t ht
  have := hc t ht
  simp only [hφ, sub_self] at this
  exact ⟨e1, e2, by linarith, e3⟩

/-- **Existence and uniqueness, combined.** For an upper tip state of the start window with
`μ B_exact(tip) = E` in the pitch window, the exact-QA reference orbit through the tip exists for
all time, satisfies `Setup μ T` for every `T`, and every orbit in the setting `Setup μ T` with the
same initial state coincides with it on `[0, T]`. In particular the hypothesis "the fresh
reference `Setup` exists" of the re-anchored scheme is discharged, with `μ_k = E/B_exact(tip_k)`. -/
theorem exactQA_reference_existsUnique {μ ψ₀ θ₀ φ₀ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) (hθ₀ : θ₀ ∈ Ioo 0 (π / 2))
    (hE : μ * exactQA.B ψ₀ θ₀ φ₀ = Eα) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = ψ₀ ∧ θ 0 = θ₀ ∧ φ 0 = φ₀ ∧ ρ 0 = 0 ∧ (∀ T, Setup μ T ψ θ φ ρ) ∧
      ∀ (T : ℝ) (ψ' θ' φ' ρ' : ℝ → ℝ), Setup μ T ψ' θ' φ' ρ' → ψ' 0 = ψ₀ → θ' 0 = θ₀ →
        φ' 0 = φ₀ → ρ' 0 = 0 →
          ∀ t ∈ Icc 0 T, ψ' t = ψ t ∧ θ' t = θ t ∧ φ' t = φ t ∧ ρ' t = ρ t := by
  obtain ⟨ψ, θ, φ, ρ, -, h1, h2, h3, h4, hS, -⟩ := exactQA_reference_exists hμ hψ₀ hθ₀ hE
  refine ⟨ψ, θ, φ, ρ, h1, h2, h3, h4, hS, fun T ψ' θ' φ' ρ' S' e1 e2 e3 e4 => ?_⟩
  exact exactQA_reference_unique (hS T) S' (e1.trans h1.symm) (e2.trans h2.symm)
    (e3.trans h3.symm) (e4.trans h4.symm)

/-! ## Sanity checks -/

/-- Sanity (degenerate case): the reflection is an involution. -/
theorem refl_refl (p : ℝ × ℝ × ℝ) : refl (refl p) = p := by simp [refl]

/-- Sanity (special case): at a turning point (`ρ = 0`) the reduced energy is `μ B`. -/
theorem Ered_turning (μ x th : ℝ) : Ered μ (x, th, 0) = μ * Bf x th := by simp [Ered]

/-- Sanity (rejected fixture): a state at `θ = π/2` is never in the invariant set (it would need
`μ B ≤ E < μ B(π/2)`). -/
theorem refSet_excludes_pi_div_two {μ ψ₀ x ρ : ℝ} (hμ : μ ∈ Icc muLo muHi)
    (hψ₀ : ψ₀ ∈ Icc (475 / 100) (579 / 100)) : (x, π / 2, ρ) ∉ refSet μ ψ₀ := by
  intro h
  have := (refSet_strict hμ hψ₀ h).2.1
  simp only [abs_of_pos (by positivity : (0 : ℝ) < π / 2)] at this
  exact lt_irrefl _ this

end PlasmaLean.Design.NearAxisQATrappedReference
