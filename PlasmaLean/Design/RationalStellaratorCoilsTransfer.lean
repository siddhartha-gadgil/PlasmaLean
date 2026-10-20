/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorCoils
public import PlasmaLean.Design.RationalStellaratorCoilsTF
public import PlasmaLean.Design.VacuumPairVolumeError

/-!
# Coil-produced fields for the rational stellarator: maximum-principle transfer

Step 2 of the coil link of `notes/theory/first-stellarator-rung.md` §3. The coil field is

`coilField Bh = tfField + Bh`,

where `tfField` is the closed rectangular filament of `RationalStellaratorCoilsTF` (it reproduces
the line-current part `∇φ` of `field (1/4)` to `ζ = 2.5 × 10⁻⁶` on the tube) and `Bh` is the
field of the helical/modular windings, required to approximate the helical part
`hel = field (1/4) - ∇φ = (1/16)∇H`.

* `Ωa a = {|s| < a, |z| < a}` (`1/10 < a ≤ 1/4`): a bounded open tube containing the
  confinement tube `T`; its frontier lies on the four faces `|s| = a` or `|z| = a`
  (`frontier_Ωa`).
* `helical_error_on_tube` (**maximum principle**, `Vacuum.VacuumField.error_le_of_frontier`): if
  `Bh` is a vacuum field on an open `U ⊇ {|s|, |z| ≤ a}` and `‖Bh - hel‖ ≤ η` on the frontier of
  `Ωa a`, then `‖Bh - hel‖ ≤ η` on all of `T` (`hel` is a vacuum field off the `z`-axis).
* `coil_stellarator_confined`: if moreover `η ≤ 5.6 × 10⁻⁵`, every field line of the coil field
  on `[0, 80]` from the start tube stays in `T` and makes **at least 10 toroidal transits**;
  `coil_stellarator_confined_one`: `η ≤ 6.5 × 10⁻⁴` gives one transit.
* `filaments_vacuumField`, `coil_filaments_confined`: the same for windings that are any finite
  family of closed `C¹` filaments avoiding `U` (`Sanity.filamentField_vacuumField'`), so the only
  remaining hypothesis is the frontier error bound.
* `exact_helical_confined`: non-vacuous instance (`Bh = hel` itself, `η = 0`).

What is *not* proved here: a frontier bound `η ≤ 5.6 × 10⁻⁵` for a concrete finite set of helical
filaments (see `scripts/rational_stellarator_coils/README.md` for an untrusted numerical design
and the size of the certification gap).
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellarator.Coils
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.RationalStellarator.Confined
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Fields PlasmaLean.Vacuum

/-! ## The region `Ωa` -/

/-- The open tube `{|s| < a, |z| < a}`. -/
@[expose] def Ωa (a : ℝ) : Set Space := {y | |sc y| < a ∧ |y 2| < a}

/-- The closed tube `{|s| ≤ a, |z| ≤ a}`. -/
@[expose] def Ka (a : ℝ) : Set Space := {y | |sc y| ≤ a ∧ |y 2| ≤ a}

/-- `Ωa a` is open. -/
theorem isOpen_Ωa (a : ℝ) : IsOpen (Ωa a) :=
  (isOpen_lt (continuous_abs.comp continuous_sc) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ => ℝ) 2)) continuous_const)

/-- `Ka a` is closed. -/
theorem isClosed_Ka (a : ℝ) : IsClosed (Ka a) :=
  (isClosed_le (continuous_abs.comp continuous_sc) continuous_const).inter
    (isClosed_le (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ => ℝ) 2)) continuous_const)

/-- `closure (Ωa a) ⊆ Ka a`. -/
theorem closure_Ωa_sub (a : ℝ) : closure (Ωa a) ⊆ Ka a :=
  closure_minimal (fun _ hy => ⟨hy.1.le, hy.2.le⟩) (isClosed_Ka a)

/-- The confinement tube lies in `Ωa a` for `a > 1/10`. -/
theorem tube_sub_Ωa {a : ℝ} (ha : 1 / 10 < a) : tubeT ⊆ Ωa a :=
  fun _ hy => ⟨lt_of_le_of_lt hy.1 ha, lt_of_le_of_lt hy.2 ha⟩

/-- `Ka a` avoids the `z`-axis for `a < 1/2`. -/
theorem Ka_sub_domain {a : ℝ} (ha : a < 1 / 2) : Ka a ⊆ domain := by
  intro y hy
  have := (abs_le.mp hy.1).1
  change 0 < r2 y
  rw [r2_eq]; linarith

/-- `Ωa a` is bounded for `a ≤ 1/4`. -/
theorem isBounded_Ωa {a : ℝ} (ha : a ≤ 1 / 4) : Bornology.IsBounded (Ωa a) := by
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := 2)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs := abs_lt.mp hy.1
  have hz := abs_lt.mp hy.2
  have hn : ‖y‖ ^ 2 = r2 y + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; rfl
  rw [r2_eq] at hn
  nlinarith [norm_nonneg y]

/-- **The frontier of `Ωa a` lies on its four faces.** -/
theorem frontier_Ωa {a : ℝ} {y : Space} (hy : y ∈ frontier (Ωa a)) :
    y ∈ Ka a ∧ (|sc y| = a ∨ |y 2| = a) := by
  have hc : y ∈ Ka a := closure_Ωa_sub a (frontier_subset_closure hy)
  refine ⟨hc, ?_⟩
  have hn : y ∉ Ωa a := by
    rw [frontier, (isOpen_Ωa a).interior_eq] at hy
    exact hy.2
  by_contra h
  push Not at h
  exact hn ⟨lt_of_le_of_ne hc.1 h.1, lt_of_le_of_ne hc.2 h.2⟩

/-! ## The helical part of the field and the maximum principle -/

/-- The helical part of the target field, `hel = field (1/4) - ∇φ = (1/16) ∇H`. -/
@[expose] def hel (y : Space) : Space := field (1 / 4) y - toroidal y

/-- `field (1/4) = ∇φ + hel`. -/
theorem field_eq_toroidal_add_hel (y : Space) : field (1 / 4) y = toroidal y + hel y := by
  simp [hel]

/-- The helical part is a vacuum field off the `z`-axis. -/
theorem hel_vacuum : VacuumField domain hel :=
  (field_vacuum (1 / 4)).sub toroidal_vacuum

/-- **Maximum-principle transfer.** If the winding field `Bh` is a vacuum field on an open set
`U ⊇ Ka a` (`1/10 < a ≤ 1/4`) and `‖Bh - hel‖ ≤ η` on the frontier of `Ωa a`, then
`‖Bh - hel‖ ≤ η` on the whole confinement tube `T`. -/
theorem helical_error_on_tube {a η : ℝ} (ha1 : 1 / 10 < a) (ha2 : a ≤ 1 / 4) (hη : 0 ≤ η)
    {U : Set Space} {Bh : Space → Space} (hBh : VacuumField U Bh) (hKU : Ka a ⊆ U)
    (hfront : ∀ y ∈ frontier (Ωa a), ‖Bh y - hel y‖ ≤ η) :
    ∀ y ∈ tubeT, ‖Bh y - hel y‖ ≤ η := by
  have hΩK : Ωa a ⊆ Ka a := fun _ hy => ⟨hy.1.le, hy.2.le⟩
  have hdom : Ka a ⊆ domain := Ka_sub_domain (by linarith)
  have h₁ : VacuumField (Ωa a) Bh := hBh.mono (isOpen_Ωa a) (hΩK.trans hKU)
  have h₂ : VacuumField (Ωa a) hel := hel_vacuum.mono (isOpen_Ωa a) (hΩK.trans hdom)
  have hc₁ : ContinuousOn Bh (closure (Ωa a)) :=
    hBh.contDiffOn.continuousOn.mono ((closure_Ωa_sub a).trans hKU)
  have hc₂ : ContinuousOn hel (closure (Ωa a)) :=
    hel_vacuum.contDiffOn.continuousOn.mono ((closure_Ωa_sub a).trans hdom)
  have h := VacuumField.error_le_of_frontier h₁ h₂ (isBounded_Ωa ha2) hc₁ hc₂ hη hfront
  exact fun y hy => h y (subset_closure (tube_sub_Ωa ha1 hy))

/-! ## The coil field -/

/-- **The coil field**: the closed TF filament plus the winding field `Bh`. -/
@[expose] def coilField (Bh : Space → Space) (y : Space) : Space := tfField y + Bh y

/-- The tube lies in the observation region of the TF filament. -/
theorem tube_sub_obs {y : Space} (hy : y ∈ tubeT) : y ∈ obsRegion := by
  have hs := abs_le.mp hy.1
  refine ⟨?_, ?_, hy.2⟩ <;> rw [r2_eq] <;> linarith

/-- The open region `{r₂ > 0, ‖y‖ < 2}` avoids the TF filament. -/
@[expose] def nearRegion : Set Space := {y | 0 < r2 y ∧ ‖y‖ < 2}

/-- `nearRegion` is open. -/
theorem isOpen_nearRegion : IsOpen nearRegion := by
  have hr : Continuous r2 := by unfold r2; fun_prop
  exact (isOpen_lt continuous_const hr).inter (isOpen_lt continuous_norm continuous_const)

/-- A point of norm `< 2` differs from every point with a coordinate of size `Λ`. -/
theorem ne_of_far {x c : Space} (hx : ‖x‖ < 2) (i : Fin 3) (hc : Λ ≤ |c i|) : x - c ≠ 0 := by
  intro h
  obtain rfl := sub_eq_zero.mp h
  have h1 := abs_coord_le x i
  have : (2 : ℝ) < Λ := by norm_num [Λ]
  linarith

/-- The TF field is continuous on the tube. -/
theorem continuousOn_tfField : ContinuousOn tfField tubeT := by
  have hsub : tubeT ⊆ nearRegion := by
    intro y hy
    refine ⟨r2_pos_of_tube hy, ?_⟩
    have hs := abs_le.mp hy.1
    have hz := abs_le.mp hy.2
    have hn : ‖y‖ ^ 2 = r2 y + y 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; rfl
    rw [r2_eq] at hn
    nlinarith [norm_nonneg y]
  have hΛ : (1 : ℝ) ≤ Λ := by norm_num [Λ]
  have hdc : ∀ p q : Space, ContinuousOn (deriv (seg p q)) (Set.uIcc 0 1) := fun p q => by
    rw [show deriv (seg p q) = fun _ => q - p from funext (deriv_seg p q)]
    exact continuousOn_const
  have one : ∀ p q : Space, (∀ x ∈ nearRegion, ∀ t ∈ Set.uIcc (0 : ℝ) 1, x - seg p q t ≠ 0) →
      ContinuousOn (segField p q) tubeT := fun p q hsep =>
    ((filamentField_contDiffOn 1 (2 * Real.pi) (seg p q) 0 1 isOpen_nearRegion
      (continuous_seg p q).continuousOn (hdc p q) hsep).continuousOn).mono hsub
  have h01 : ContinuousOn (segField P0 P1) tubeT := one P0 P1 fun x hx t _ h => by
    have e : x = seg P0 P1 t := sub_eq_zero.mp h
    have h0 : x 0 = 0 := by rw [e]; simp [seg, P0, P1]
    have h1 : x 1 = 0 := by rw [e]; simp [seg, P0, P1]
    have : r2 x = 0 := by simp [r2, h0, h1]
    linarith [hx.1]
  have h12 : ContinuousOn (segField P1 P2) tubeT := one P1 P2 fun x hx t _ =>
    ne_of_far hx.2 2 (by simp [seg, P1, P2, Λ])
  have h23 : ContinuousOn (segField P2 P3) tubeT := one P2 P3 fun x hx t _ =>
    ne_of_far hx.2 0 (by simp [seg, P2, P3, Λ])
  have h30 : ContinuousOn (segField P3 P0) tubeT := one P3 P0 fun x hx t _ =>
    ne_of_far hx.2 2 (by simp [seg, P3, P0, Λ])
  exact ((h01.add h12).add h23).add h30

/-- **Field error of the coil field on the tube**: `ζ + η`. -/
theorem coil_error {Bh : Space → Space} {η : ℝ} (hBh : ∀ y ∈ tubeT, ‖Bh y - hel y‖ ≤ η) :
    ∀ y ∈ tubeT, ‖coilField Bh y - field (1 / 4) y‖ ≤ ζ + η := by
  intro y hy
  have e : coilField Bh y - field (1 / 4) y = (tfField y - toroidal y) + (Bh y - hel y) := by
    rw [field_eq_toroidal_add_hel]; unfold coilField; abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (tfField_error (tube_sub_obs hy)) (hBh y hy))

/-- **Coil-field stellarator confinement over 10 transits.** Let `Bh` (the windings) be a vacuum
field on an open `U ⊇ {|s|, |z| ≤ a}`, `1/10 < a ≤ 1/4`, within `η ≤ 5.6 × 10⁻⁵` of the helical
part `hel` of `field (1/4)` on the frontier of `{|s| < a, |z| < a}`. Then every curve that is a
field line of the coil field `tfField + Bh` on `[0, 80]` starting in the start tube stays in the
tube `T` and its toroidal angle advances by at least `2π · 10`. -/
theorem coil_stellarator_confined {a η : ℝ} (ha1 : 1 / 10 < a) (ha2 : a ≤ 1 / 4) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 56 / 1000000) {U : Set Space} {Bh : Space → Space} (hBh : VacuumField U Bh)
    (hKU : Ka a ⊆ U) (hfront : ∀ y ∈ frontier (Ωa a), ‖Bh y - hel y‖ ≤ η)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 80, HasDerivAt γ (coilField Bh (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 80, γ s ∈ tubeT) ∧
      2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80, phiRateOf (coilField Bh) (γ u) := by
  have herr := coil_error (helical_error_on_tube ha1 ha2 hη0 hBh hKU hfront)
  have hcont : ContinuousOn (coilField Bh) tubeT := by
    have hB : ContinuousOn Bh tubeT := hBh.contDiffOn.continuousOn.mono fun y hy =>
      hKU ⟨hy.1.trans ha1.le, hy.2.trans ha1.le⟩
    exact continuousOn_tfField.add hB
  exact confined_of_error_ten (by unfold ζ; positivity) (by unfold ζ; linarith) herr hcont hγ h0

/-- **Coil-field confinement over one transit** for winding errors `η ≤ 6.5 × 10⁻⁴`. -/
theorem coil_stellarator_confined_one {a η : ℝ} (ha1 : 1 / 10 < a) (ha2 : a ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 65 / 100000) {U : Set Space} {Bh : Space → Space}
    (hBh : VacuumField U Bh) (hKU : Ka a ⊆ U)
    (hfront : ∀ y ∈ frontier (Ωa a), ‖Bh y - hel y‖ ≤ η)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 8, HasDerivAt γ (coilField Bh (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 8, γ s ∈ tubeT) ∧
      2 * Real.pi ≤ ∫ u in (0 : ℝ)..8, phiRateOf (coilField Bh) (γ u) := by
  have herr := coil_error (helical_error_on_tube ha1 ha2 hη0 hBh hKU hfront)
  have hcont : ContinuousOn (coilField Bh) tubeT := by
    have hB : ContinuousOn Bh tubeT := hBh.contDiffOn.continuousOn.mono fun y hy =>
      hKU ⟨hy.1.trans ha1.le, hy.2.trans ha1.le⟩
    exact continuousOn_tfField.add hB
  exact confined_of_error_one (by unfold ζ; positivity) (by unfold ζ; linarith) herr hcont hγ h0

/-! ## Windings made of closed filaments -/

/-- The zero field is a vacuum field. -/
theorem vacuumField_zero {U : Set Space} (hU : IsOpen U) : VacuumField U (fun _ => 0) := by
  refine ⟨hU, contDiffOn_const, fun x _ => ?_, fun x _ => ?_⟩
  · simp [fieldDiv, divOp]
  · simp only [fieldCurl, fderiv_fun_const, Pi.zero_apply]
    ext i; fin_cases i <;> simp [curlOp]

/-- **Finite families of closed `C¹` filaments** avoiding an open set `U` give a vacuum field on
`U` (superposition of `Sanity.filamentField_vacuumField'`). -/
theorem filaments_vacuumField {U : Set Space} (hU : IsOpen U) (μ₀ : ℝ) (n : ℕ) (I : ℕ → ℝ)
    (c : ℕ → ℝ → Space)
    (hc : ∀ k < n, ∀ t ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ (c k) t)
    (ht : ∀ k < n, ContinuousOn (deriv (c k)) (Set.uIcc 0 1))
    (hsep : ∀ k < n, ∀ x ∈ U, ∀ t ∈ Set.uIcc (0 : ℝ) 1, x - c k t ≠ 0)
    (hclosed : ∀ k < n, c k 0 = c k 1) :
    VacuumField U (fun y => ∑ k ∈ Finset.range n, filamentField μ₀ (I k) (c k) 0 1 y) := by
  induction n with
  | zero => simpa using vacuumField_zero hU
  | succ n ih =>
    have h1 := ih (fun k hk => hc k (by omega)) (fun k hk => ht k (by omega))
      (fun k hk => hsep k (by omega)) (fun k hk => hclosed k (by omega))
    have h2 := Sanity.filamentField_vacuumField' μ₀ (I n) (c n) 0 1 hU (hc n (by omega))
      (ht n (by omega)) (hsep n (by omega)) (hclosed n (by omega))
    have := Design.VacuumPair.vacuumField_add h1 h2
    have e : (fun y => ∑ k ∈ Finset.range (n + 1), filamentField μ₀ (I k) (c k) 0 1 y) =
        (fun y => ∑ k ∈ Finset.range n, filamentField μ₀ (I k) (c k) 0 1 y) +
          filamentField μ₀ (I n) (c n) 0 1 := by
      funext y; simp [Finset.sum_range_succ]
    rw [e]; exact this

/-- **Confinement for a coil set made of the TF filament and `n` closed `C¹` winding filaments**
(10 transits), given only the frontier error bound `η ≤ 5.6 × 10⁻⁵` of the windings. -/
theorem coil_filaments_confined {a η : ℝ} (ha1 : 1 / 10 < a) (ha2 : a ≤ 1 / 4) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 56 / 1000000) {U : Set Space} (hU : IsOpen U) (hKU : Ka a ⊆ U) (μ₀ : ℝ) (n : ℕ)
    (I : ℕ → ℝ) (c : ℕ → ℝ → Space)
    (hc : ∀ k < n, ∀ t ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ (c k) t)
    (ht : ∀ k < n, ContinuousOn (deriv (c k)) (Set.uIcc 0 1))
    (hsep : ∀ k < n, ∀ x ∈ U, ∀ t ∈ Set.uIcc (0 : ℝ) 1, x - c k t ≠ 0)
    (hclosed : ∀ k < n, c k 0 = c k 1)
    (hfront : ∀ y ∈ frontier (Ωa a),
      ‖(∑ k ∈ Finset.range n, filamentField μ₀ (I k) (c k) 0 1 y) - hel y‖ ≤ η)
    {γ : ℝ → Space}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 80, HasDerivAt γ
      (coilField (fun y => ∑ k ∈ Finset.range n, filamentField μ₀ (I k) (c k) 0 1 y) (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 80, γ s ∈ tubeT) ∧
      2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80,
        phiRateOf (coilField (fun y => ∑ k ∈ Finset.range n, filamentField μ₀ (I k) (c k) 0 1 y))
          (γ u) :=
  coil_stellarator_confined ha1 ha2 hη0 hη1
    (filaments_vacuumField hU μ₀ n I c hc ht hsep hclosed) hKU hfront hγ h0

/-! ## Sanity checks -/

/-- Non-vacuous instance (`η = 0`): the exact helical field `hel` itself (a vacuum field off the
`z`-axis) as the winding field satisfies all hypotheses of `coil_stellarator_confined`, so field
lines of `tfField + hel` from the start tube make 10 transits in `T`. -/
theorem exact_helical_confined {γ : ℝ → Space}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 80, HasDerivAt γ (coilField hel (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 80, γ s ∈ tubeT) ∧
      2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80, phiRateOf (coilField hel) (γ u) :=
  coil_stellarator_confined (a := 1 / 5) (by norm_num) (by norm_num) le_rfl (by norm_num)
    hel_vacuum (Ka_sub_domain (by norm_num)) (fun y _ => by simp) hγ h0

/-- Rejected fixture: the frontier hypothesis cannot be dropped, since the zero winding field
violates the needed bound by the size of the helical field: at `(√(6/5), 0, 0)` (on the face
`s = 1/10`), `hel` has `x`-component `(1/16)(11/18)√(6/5) ≈ 0.042`, far above
`η = 5.6 × 10⁻⁵`. -/
theorem zero_winding_fails : ¬ ∀ y ∈ tubeT, ‖(0 : Space) - hel y‖ ≤ 56 / 1000000 := by
  intro h
  set y : Space := WithLp.toLp 2 ![Real.sqrt (6 / 5), 0, 0] with hy
  have h0 : y 0 = Real.sqrt (6 / 5) := by simp [hy]
  have h1 : y 1 = 0 := by simp [hy]
  have h2 : y 2 = 0 := by simp [hy]
  have hsq : Real.sqrt (6 / 5) ^ 2 = 6 / 5 := Real.sq_sqrt (by norm_num)
  have hr : r2 y = 6 / 5 := by rw [r2, h0, h1, hsq]; norm_num
  have hT : y ∈ tubeT := ⟨by rw [sc, hr]; norm_num, by rw [h2]; norm_num⟩
  have hb := h y hT
  have hc := abs_coord_le ((0 : Space) - hel y) 0
  have hx : ((0 : Space) - hel y) 0 = -(1 / 4 / 4 * G 0 y) := by
    simp [hel, field, gradH, toroidal, h1]
  have hG : G 0 y = 11 / 18 * Real.sqrt (6 / 5) := by
    have hw : winv y = 5 / 6 := by rw [winv, hr]; norm_num
    have h3 : Real.sqrt (6 / 5) ^ 3 = 6 / 5 * Real.sqrt (6 / 5) := by
      rw [pow_succ, hsq]
    simp only [G, Hd, cv, H0, Hnum, Aq, Bq, Xd, Yp, Matrix.cons_val_zero, h0, h1, h2, hw, hr]
    linear_combination (4 / 1 * (6 / 5 - 1) * (25 / 36) - 4 * (6 / 5 - 1) ^ 2 * (125 / 216)) * h3
  have hs : (1 : ℝ) ≤ Real.sqrt (6 / 5) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  rw [hx, hG, abs_neg, abs_of_pos (by positivity)] at hc
  nlinarith

end PlasmaLean.Design.RationalStellarator.Coils
