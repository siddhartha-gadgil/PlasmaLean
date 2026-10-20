/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.FullOrbit
public import PlasmaLean.Theory.Kinetic.CanonicalMomentum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Guiding-centre reduction with explicit finite-time error (track T8, problem R6)

Model: non-relativistic Newton–Lorentz orbits `x' = v`, `m v' = q (E(x) + v × B(x))` in static
fields (`LorentzOrbit`), SI units. Orbits are supplied, not constructed.

The first-order guiding centre is `X = x + ρ`, `ρ = (m/q) v × B/|B|²`. (The vector from the
guiding centre to the particle is `(m/(q|B|²)) B × v`; `helix_guidingCentre` checks the sign
against the exact helix.)

Results:

* **(a)** `exbGuidingCentre_hasDerivAt`, `exbGuidingCentre_exact`: in uniform `B₀` and
  uniform `E₀ ⊥ B₀`, `X = x + (m/q)(v - v_E) × B₀/|B₀|²` moves *exactly* with
  `v_E + v_∥ b` for every orbit (straight line, all times).
* **(b)** `guidingCentre_hasDerivAt`: exact identity
  `dX/dt = v_∥ b(x) + (m/q) v × d(B/|B|²)/dt` for static `C¹` `B` and `E = 0`.
  `guidingCentre_reduction_bound`: if `|B| ≥ B_min > 0` and `‖DB‖ ≤ G` along the orbit on
  `[0,T]`, then `|X(t) - X(0) - ∫₀ᵗ v_∥ b(x(τ)) dτ| ≤ ρ_L (G/B_min) s t` with
  `ρ_L = |m| s/(|q| B_min)`, `s = |v|`: constant `C = 1` (the `∇(1/|B|²)`
  correction is a reflection, an isometry — `norm_invFieldRate`; the cross-product and
  operator-norm steps are not sharp). The along-orbit hypotheses are shown satisfiable
  only for `G = 0` (`uniform_field_exact`); orbits in non-uniform fields are assumed.
  `particle_fieldline_bound` adds the oscillation `2 ρ_L`. `guidingCentre_flux_drift`
  turns this into drift of a field-line first integral `ψ`: `|Δψ(X)| ≤ (H + Ψ G/B_min) ρ_L s t`.
* **(c)** `magneticMoment_drift`: `|μ(t) - μ(0)| ≤ 6 μ_s (G/B_min) s t`,
  `μ_s = m s²/(2 B_min)` — honest linear drift only.
* **(d)** uniform-field exactness, a dimensionless example, and 3.5 MeV alphas at 5 T with
  `L_B = B_min/G = 1 m`.

Honest assessment. The secular error `ρ_L s t/L_B` has the physically correct order (it is the
size of grad-B/curvature drift displacement), but it is not averaged: no gyro- or
bounce-averaging, so the drift is not shown to be along flux surfaces. For the alpha the rate
is `7 × 10⁵ m/s`; 10 cm is reached after `≈ 1.4 × 10⁻⁷ s` (≈ 1.86 m of path). This beats the
ballistic bound by about `L_B/ρ_L` (≈ 9–18) but is ~10⁶–10⁷ times shorter than slowing-down
times. The `μ` bound is weaker than one gyroperiod at reactor scale. Exponential adiabatic
invariance and bounce-averaged (omnigeneous/quasisymmetric) radial drift remain open (M4).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.GuidingCentre
open PlasmaLean.Fields PlasmaLean.Kinetic WithLp Matrix
open scoped RealInnerProductSpace

/-- Vector triple product `(u × w) × z = ⟪u, z⟫ w - ⟪w, z⟫ u`. -/
theorem cross_cross_eq (u w z : Space) :
    cross (cross u w) z = ⟪u, z⟫ • w - ⟪w, z⟫ • u := by
  ext i
  fin_cases i <;>
  simp [cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
    dotProduct] <;> ring

-- The coordinate goals differ per case; a uniform `simp` followed by `convert` is clearest.
set_option linter.flexible false in
/-- Product rule for the cross product of two differentiable curves. -/
theorem hasDerivAt_cross {a b : ℝ → Space} {a' b' : Space} {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => cross (a s) (b s)) (cross a' (b t) + cross (a t) b') t := by
  have hc : HasDerivAt (fun s => ofLp (a s) ⨯₃ ofLp (b s))
      (ofLp (cross a' (b t) + cross (a t) b')) t := by
    rw [hasDerivAt_pi]
    intro i
    have h := fun j k => (hasDerivAt_coord ha j).mul (hasDerivAt_coord hb k)
    fin_cases i <;> simp [cross, cross_apply] <;>
    [convert (h 1 2).sub (h 2 1) using 1; convert (h 2 0).sub (h 0 2) using 1;
     convert (h 0 1).sub (h 1 0) using 1] <;> simp <;> ring
  simpa [cross] using hasDerivAt_toLp hc

/-- The cross product is homogeneous in its first argument. -/
theorem cross_smul_left' (c : ℝ) (u w : Space) : cross (c • u) w = c • cross u w := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- The cross product is homogeneous in its second argument. -/
theorem cross_smul_right' (c : ℝ) (u w : Space) : cross u (c • w) = c • cross u w := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- The cross product is additive (subtraction) in its first argument. -/
theorem cross_sub_left' (u u' w : Space) : cross (u - u') w = cross u w - cross u' w := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- The reflection `u ↦ u - 2⟪β̂,u⟫β̂` in the plane orthogonal to `β ≠ 0` is an isometry. -/
theorem norm_reflect (β u : Space) (hβ : β ≠ 0) :
    ‖u - (2 * ⟪β, u⟫ / ‖β‖ ^ 2) • β‖ = ‖u‖ := by
  have hn : ‖β‖ ^ 2 ≠ 0 := by positivity
  have h : ‖u - (2 * ⟪β, u⟫ / ‖β‖ ^ 2) • β‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_right,
      real_inner_comm]
    field_simp
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The field `B/|B|²` (zero where `B` vanishes, by Lean's conventions). -/
@[expose] def invField (B : Space → Space) (y : Space) : Space := (‖B y‖ ^ 2)⁻¹ • B y

/-- Time derivative of `B/|B|²` along a curve on which `B` has value `β` and rate `β'`. -/
@[expose] def invFieldRate (β β' : Space) : Space :=
  (‖β‖ ^ 2)⁻¹ • β' + (-(2 * ⟪β, β'⟫) / (‖β‖ ^ 2) ^ 2) • β

/-- `|d(B/|B|²)/dt| = |dB/dt|/|B|²` exactly: the correction term is a reflection. -/
theorem norm_invFieldRate (β β' : Space) (hβ : β ≠ 0) :
    ‖invFieldRate β β'‖ = ‖β'‖ / ‖β‖ ^ 2 := by
  have hn : ‖β‖ ^ 2 ≠ 0 := by positivity
  have : invFieldRate β β' = (‖β‖ ^ 2)⁻¹ • (β' - (2 * ⟪β, β'⟫ / ‖β‖ ^ 2) • β) := by
    rw [invFieldRate, smul_sub, smul_smul, neg_div, neg_smul, ← sub_eq_add_neg]
    congr 2
    field_simp
  rw [this, norm_smul, norm_reflect β β' hβ, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- Chain rule for `B/|B|²` along a curve, where `B` does not vanish. -/
theorem hasDerivAt_invField {B : Space → Space} {DB : Space → Space →L[ℝ] Space}
    {x : ℝ → Space} {v : Space} {t : ℝ} (hB : HasFDerivAt B (DB (x t)) (x t))
    (hx : HasDerivAt x v t) (h0 : B (x t) ≠ 0) :
    HasDerivAt (fun s => invField B (x s)) (invFieldRate (B (x t)) (DB (x t) v)) t := by
  have hβ : HasDerivAt (fun s => B (x s)) (DB (x t) v) t := hB.comp_hasDerivAt t hx
  have hn := hβ.norm_sq
  have hn0 : ‖B (x t)‖ ^ 2 ≠ 0 := by positivity
  have hi := hn.inv hn0
  exact hi.smul hβ

/-- The parallel velocity vector `v_∥ b = (⟪v, B⟫/|B|²) B` at position `y`. -/
@[expose] def parallelVelocity (B : Space → Space) (y v : Space) : Space :=
  (⟪v, B y⟫ / ‖B y‖ ^ 2) • B y

/-- The gyro-vector `ρ(y, v) = (m/q) v × B(y)/|B(y)|²`, the displacement from the particle to its
guiding centre. (Equivalently `-(m/(q|B|²)) B × v`; the vector from the guiding centre to the
particle is `(m/(q|B|²)) B × v`.) -/
@[expose] def gyroVector (m q : ℝ) (B : Space → Space) (y v : Space) : Space :=
  (m / q) • cross v (invField B y)

/-- The first-order guiding centre `X = y + ρ(y, v)`. -/
@[expose] def guidingCentre (m q : ℝ) (B : Space → Space) (y v : Space) : Space :=
  y + gyroVector m q B y v

/-- Algebraic heart of the guiding-centre identity: `v + (v × β) × β/|β|² = v_∥ b`. -/
theorem lorentz_gyro_identity (v β : Space) (hβ : β ≠ 0) :
    v + cross (cross v β) ((‖β‖ ^ 2)⁻¹ • β) = (⟪v, β⟫ / ‖β‖ ^ 2) • β := by
  have hn : ‖β‖ ^ 2 ≠ 0 := by positivity
  rw [cross_cross_eq, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
    inv_mul_cancel₀ hn, one_smul]
  rw [div_eq_inv_mul]; abel

/-- **Exact guiding-centre velocity** (static `B`, `E = 0`). Along every Newton–Lorentz orbit,
wherever `B ≠ 0`, `dX/dt = v_∥ b(x) + (m/q) v × d(B/|B|²)/dt`, the last term being the only
one involving `∇B`. -/
theorem guidingCentre_hasDerivAt {m q : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space} (hm : m ≠ 0) (hq : q ≠ 0)
    (horbit : LorentzOrbit m q (fun _ => 0) B x v) (hB : ∀ y, HasFDerivAt B (DB y) y)
    {t : ℝ} (h0 : B (x t) ≠ 0) :
    HasDerivAt (fun s => guidingCentre m q B (x s) (v s))
      (parallelVelocity B (x t) (v t) +
        (m / q) • cross (v t) (invFieldRate (B (x t)) (DB (x t) (v t)))) t := by
  obtain ⟨a, ha, hlaw⟩ := horbit.newton t
  have ha' : a = (q / m) • cross (v t) (B (x t)) := by
    rw [zero_add] at hlaw
    rw [div_eq_inv_mul, mul_smul, ← hlaw, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hW := hasDerivAt_invField (hB (x t)) (horbit.position t) h0
  have hc := (hasDerivAt_cross ha hW).const_smul (m / q)
  have := (horbit.position t).add hc
  convert this using 1
  · funext s; simp [guidingCentre, gyroVector]
  rw [ha', cross_smul_left', smul_add, smul_smul, div_mul_div_comm, mul_comm m q,
    div_self (mul_ne_zero hq hm), one_smul, ← add_assoc]
  congr 1
  rw [invField, lorentz_gyro_identity _ _ h0, parallelVelocity]

/-- The gyro-vector is bounded by the Larmor radius `|m||v|/(|q| B_min)`. -/
theorem norm_gyroVector_le {m q Bmin : ℝ} {B : Space → Space} {y v : Space}
    (hBmin : 0 < Bmin) (hlow : Bmin ≤ ‖B y‖) :
    ‖gyroVector m q B y v‖ ≤ |m| * ‖v‖ / (|q| * Bmin) := by
  have hpos : 0 < ‖B y‖ := lt_of_lt_of_le hBmin hlow
  have hW : ‖invField B y‖ = 1 / ‖B y‖ := by
    rw [invField, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  rw [gyroVector, norm_smul, Real.norm_eq_abs, abs_div]
  calc |m| / |q| * ‖cross v (invField B y)‖ ≤ |m| / |q| * (‖v‖ * (1 / ‖B y‖)) := by
        gcongr; rw [← hW]; exact norm_cross_le _ _
    _ ≤ |m| / |q| * (‖v‖ * (1 / Bmin)) := by gcongr
    _ = |m| * ‖v‖ / (|q| * Bmin) := by
        rcases eq_or_ne q 0 with h | h
        · simp [h]
        · field_simp

/-! ## (b) Reduction-error bound in a nonuniform static field -/

/-- Bound on the `∇B` residual: `|(m/q) v × d(B/|B|²)/dt| ≤ ρ (G/B_min) |v|` with `ρ =
|m||v|/(|q|B_min)`, if `‖DB‖ ≤ G` and `|B| ≥ B_min`. -/
theorem norm_residual_le {m q G Bmin : ℝ} {β : Space} {L : Space →L[ℝ] Space} {v : Space}
    (hBmin : 0 < Bmin) (hlow : Bmin ≤ ‖β‖) (hgrad : ‖L‖ ≤ G) :
    ‖(m / q) • cross v (invFieldRate β (L v))‖ ≤
      (|m| * ‖v‖ / (|q| * Bmin)) * (G / Bmin) * ‖v‖ := by
  have hpos : 0 < ‖β‖ := lt_of_lt_of_le hBmin hlow
  have hβ : β ≠ 0 := norm_pos_iff.mp hpos
  have hG : 0 ≤ G := (norm_nonneg _).trans hgrad
  have hLv : ‖L v‖ ≤ G * ‖v‖ := (L.le_opNorm v).trans (by gcongr)
  rw [norm_smul, Real.norm_eq_abs, abs_div]
  calc |m| / |q| * ‖cross v (invFieldRate β (L v))‖
      ≤ |m| / |q| * (‖v‖ * (G * ‖v‖ / Bmin ^ 2)) := by
        gcongr
        refine (norm_cross_le _ _).trans ?_
        gcongr
        rw [norm_invFieldRate β _ hβ]
        calc ‖L v‖ / ‖β‖ ^ 2 ≤ G * ‖v‖ / ‖β‖ ^ 2 := by gcongr
          _ ≤ G * ‖v‖ / Bmin ^ 2 := by gcongr
    _ = (|m| * ‖v‖ / (|q| * Bmin)) * (G / Bmin) * ‖v‖ := by
        rcases eq_or_ne q 0 with h | h
        · simp [h]
        · field_simp

/-- The parallel velocity along a continuous orbit is continuous wherever `B ≠ 0`. -/
theorem continuousAt_parallelVelocity {B : Space → Space} {x v : ℝ → Space} {τ : ℝ}
    (hB : Continuous B) (hx : Continuous x) (hv : Continuous v) (h0 : B (x τ) ≠ 0) :
    ContinuousAt (fun s => parallelVelocity B (x s) (v s)) τ := by
  have hβ : Continuous (fun s => B (x s)) := hB.comp hx
  unfold parallelVelocity
  have hn : ‖B (x τ)‖ ^ 2 ≠ 0 := by positivity
  exact ((hv.inner hβ).continuousAt.div (hβ.norm.pow 2).continuousAt hn).smul hβ.continuousAt

/-- **Finite-time guiding-centre reduction error (R6, restricted smooth regime).** For a
Newton–Lorentz orbit in a static `C¹` magnetic field with `|B(x(τ))| ≥ B_min > 0` and
`‖DB(x(τ))‖ ≤ G` for `τ ∈ [0,T]`, and `t ∈ [0,T]`,
`|X(t) - X(0) - ∫₀ᵗ v_∥ b(x(τ)) dτ| ≤ ρ_L · (G/B_min) · s · t`, where `s = |v(0)|`
(conserved) and `ρ_L = |m| s/(|q| B_min)`. The constant is `1`. -/
theorem guidingCentre_reduction_bound {m q G Bmin T t : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (horbit : LorentzOrbit m q (fun _ => 0) B x v)
    (hB : ∀ y, HasFDerivAt B (DB y) y)
    (hBmin : 0 < Bmin) (hlow : ∀ τ ∈ Set.Icc 0 T, Bmin ≤ ‖B (x τ)‖)
    (hgrad : ∀ τ ∈ Set.Icc 0 T, ‖DB (x τ)‖ ≤ G) (ht : t ∈ Set.Icc 0 T) :
    ‖guidingCentre m q B (x t) (v t) - guidingCentre m q B (x 0) (v 0)
       - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ)‖
      ≤ (|m| * ‖v 0‖ / (|q| * Bmin)) * (G / Bmin) * ‖v 0‖ * t := by
  have hBc : Continuous B := continuous_iff_continuousAt.mpr fun y => (hB y).continuousAt
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun s =>
    (horbit.position s).continuousAt
  have hvc : Continuous v := horbit.velocity_differentiable.continuous
  have hne : ∀ τ ∈ Set.Icc 0 T, B (x τ) ≠ 0 := fun τ hτ =>
    norm_pos_iff.mp (lt_of_lt_of_le hBmin (hlow τ hτ))
  set f := fun s => parallelVelocity B (x s) (v s) with hf
  set U : Set ℝ := {s | B (x s) ≠ 0} with hU
  have hUopen : IsOpen U := isOpen_ne_fun (hBc.comp hxc) continuous_const
  have hfU : ContinuousOn f U := fun s hs =>
    (continuousAt_parallelVelocity hBc hxc hvc hs).continuousWithinAt
  have hsub : Set.Icc 0 T ⊆ U := fun s hs => hne s hs
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hint : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun u => ∫ τ in (0:ℝ)..u, f τ) (f s) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · apply (hfU.mono _).intervalIntegrable
      intro r hr
      rw [Set.uIcc_of_le hs.1] at hr
      exact hsub ⟨hr.1, hr.2.trans hs.2⟩
    · exact hfU.stronglyMeasurableAtFilter hUopen s (hsub hs)
    · exact continuousAt_parallelVelocity hBc hxc hvc (hne s hs)
  set K := (|m| * ‖v 0‖ / (|q| * Bmin)) * (G / Bmin) * ‖v 0‖
  set g := fun u => guidingCentre m q B (x u) (v u) - guidingCentre m q B (x 0) (v 0)
       - ∫ τ in (0:ℝ)..u, f τ with hg
  have hgd : ∀ s ∈ Set.Icc 0 T, HasDerivAt g
      ((m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))) s := by
    intro s hs
    have h1 := ((guidingCentre_hasDerivAt hm hq horbit hB (hne s hs)).sub_const
      (guidingCentre m q B (x 0) (v 0))).sub (hint s hs)
    convert h1 using 1
    simp [hf]
  have hbound : ∀ s ∈ Set.Ico 0 T,
      ‖(m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))‖ ≤ K := by
    intro s hs
    have hs' := Set.Ico_subset_Icc_self hs
    have := norm_residual_le (m := m) (q := q) (v := v s) hBmin (hlow s hs') (hgrad s hs')
    rwa [speed_conserved hm horbit s 0] at this
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => (hgd s hs).hasDerivWithinAt) hbound t ht
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero] at hmv
  simpa [hg] using hmv

/-- Particle version: `|x(t) - x(0) - ∫₀ᵗ v_∥ b| ≤ 2 ρ_L + ρ_L (G/B_min) s t` (gyration
oscillation plus the secular reduction error). -/
theorem particle_fieldline_bound {m q G Bmin T t : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (horbit : LorentzOrbit m q (fun _ => 0) B x v)
    (hB : ∀ y, HasFDerivAt B (DB y) y)
    (hBmin : 0 < Bmin) (hlow : ∀ τ ∈ Set.Icc 0 T, Bmin ≤ ‖B (x τ)‖)
    (hgrad : ∀ τ ∈ Set.Icc 0 T, ‖DB (x τ)‖ ≤ G) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - x 0 - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ)‖
      ≤ 2 * (|m| * ‖v 0‖ / (|q| * Bmin)) +
        (|m| * ‖v 0‖ / (|q| * Bmin)) * (G / Bmin) * ‖v 0‖ * t := by
  have hmain := guidingCentre_reduction_bound hm hq horbit hB hBmin hlow hgrad ht
  have h0 : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have g1 := norm_gyroVector_le (m := m) (q := q) (v := v t) hBmin (hlow t ht)
  have g0 := norm_gyroVector_le (m := m) (q := q) (v := v 0) hBmin (hlow 0 h0)
  rw [speed_conserved hm horbit t 0] at g1
  have hsplit : x t - x 0 - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ) =
      (guidingCentre m q B (x t) (v t) - guidingCentre m q B (x 0) (v 0)
        - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ))
      - gyroVector m q B (x t) (v t) + gyroVector m q B (x 0) (v 0) := by
    simp only [guidingCentre]; abel
  rw [hsplit]
  calc _ ≤ ‖(guidingCentre m q B (x t) (v t) - guidingCentre m q B (x 0) (v 0)
        - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ))
      - gyroVector m q B (x t) (v t)‖ + ‖gyroVector m q B (x 0) (v 0)‖ := norm_add_le _ _
    _ ≤ _ := by
      have := norm_sub_le (guidingCentre m q B (x t) (v t) - guidingCentre m q B (x 0) (v 0)
        - ∫ τ in (0:ℝ)..t, parallelVelocity B (x τ) (v τ)) (gyroVector m q B (x t) (v t))
      linarith

/-! ## (a) Exact guiding centre in uniform crossed fields -/

/-- The `E × B` drift velocity `E₀ × B₀/|B₀|²`. -/
@[expose] def exbDrift (E₀ B₀ : Space) : Space := (‖B₀‖ ^ 2)⁻¹ • cross E₀ B₀

/-- Guiding centre in uniform crossed fields: `X = x + (m/q)(v - v_E) × B₀/|B₀|²`. -/
@[expose] def exbGuidingCentre (m q : ℝ) (E₀ B₀ y v : Space) : Space :=
  y + (m / q) • cross (v - exbDrift E₀ B₀) ((‖B₀‖ ^ 2)⁻¹ • B₀)

/-- The cross product is additive in its first argument. -/
theorem cross_add_left' (u u' w : Space) : cross (u + u') w = cross u w + cross u' w := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- Cross product with zero. -/
theorem cross_zero_right' (u : Space) : cross u 0 = 0 := by
  ext i; fin_cases i <;> simp [cross, cross_apply]

/-- **Exact `E × B` guiding centre** in uniform fields: for every Newton–Lorentz orbit, `dX/dt =
v_E + v_∥ b`. (No orthogonality of `E₀` and `B₀` is needed for this identity.) -/
theorem exbGuidingCentre_hasDerivAt {m q : ℝ} {E₀ B₀ : Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (hB₀ : B₀ ≠ 0)
    (horbit : LorentzOrbit m q (fun _ => E₀) (fun _ => B₀) x v) (t : ℝ) :
    HasDerivAt (fun s => exbGuidingCentre m q E₀ B₀ (x s) (v s))
      (exbDrift E₀ B₀ + (⟪v t, B₀⟫ / ‖B₀‖ ^ 2) • B₀) t := by
  obtain ⟨a, ha, hlaw⟩ := horbit.newton t
  have ha' : a = (q / m) • (E₀ + cross (v t) B₀) := by
    rw [div_eq_inv_mul, mul_smul, ← hlaw, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hc := (hasDerivAt_cross (ha.sub_const (exbDrift E₀ B₀))
    (hasDerivAt_const t ((‖B₀‖ ^ 2)⁻¹ • B₀))).const_smul (m / q)
  have := (horbit.position t).add hc
  convert this using 1
  · funext s; simp [exbGuidingCentre]
  rw [ha', cross_zero_right', add_zero, cross_smul_left', smul_smul, div_mul_div_comm,
    mul_comm m q, div_self (mul_ne_zero hq hm), one_smul, cross_add_left',
    ← add_assoc, add_comm (v t), add_assoc, lorentz_gyro_identity _ _ hB₀, exbDrift,
    cross_smul_right']

/-- With `E₀ ⊥ B₀` uniform, the parallel velocity `⟪v, B₀⟫` is constant. -/
theorem exb_parallel_conserved {m q : ℝ} {E₀ B₀ : Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hperp : ⟪E₀, B₀⟫ = 0)
    (horbit : LorentzOrbit m q (fun _ => E₀) (fun _ => B₀) x v) (s t : ℝ) :
    ⟪v s, B₀⟫ = ⟪v t, B₀⟫ := by
  have hd (r : ℝ) : HasDerivAt (fun u => ⟪v u, B₀⟫) 0 r := by
    obtain ⟨a, ha, hlaw⟩ := horbit.newton r
    have ha' : a = (q / m) • (E₀ + cross (v r) B₀) := by
      rw [div_eq_inv_mul, mul_smul, ← hlaw, smul_smul, inv_mul_cancel₀ hm, one_smul]
    have := ha.inner ℝ (hasDerivAt_const r B₀)
    convert this using 1
    rw [ha', inner_zero_right, zero_add, inner_smul_left, inner_add_left, hperp,
      real_inner_comm, inner_cross_self']
    simp
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s t

/-- With `E₀ ⊥ B₀` uniform, the guiding centre moves exactly on the straight line `X(t) = X(0) + t
(v_E + v_∥ b)` for all real `t`. -/
theorem exbGuidingCentre_exact {m q : ℝ} {E₀ B₀ : Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (hB₀ : B₀ ≠ 0) (hperp : ⟪E₀, B₀⟫ = 0)
    (horbit : LorentzOrbit m q (fun _ => E₀) (fun _ => B₀) x v) (t : ℝ) :
    exbGuidingCentre m q E₀ B₀ (x t) (v t) = exbGuidingCentre m q E₀ B₀ (x 0) (v 0) +
      t • (exbDrift E₀ B₀ + (⟪v 0, B₀⟫ / ‖B₀‖ ^ 2) • B₀) := by
  set c := exbDrift E₀ B₀ + (⟪v 0, B₀⟫ / ‖B₀‖ ^ 2) • B₀
  have hd (r : ℝ) : HasDerivAt (fun s => exbGuidingCentre m q E₀ B₀ (x s) (v s) - s • c) 0 r := by
    have h1 := exbGuidingCentre_hasDerivAt hm hq hB₀ horbit r
    rw [exb_parallel_conserved hm hperp horbit r 0] at h1
    have h2 := h1.sub ((hasDerivAt_id r).smul_const c)
    rw [one_smul, sub_self] at h2
    exact h2
  have := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simp only [zero_smul, sub_zero] at this
  rw [← this]; abel

/-! ## (c) Magnetic moment over finite time -/

/-- Magnetic moment `μ = m v_⊥²/(2|B|)`, written as `m(|v|²/|B| - ⟪v,B⟫²/|B|³)/2`. -/
@[expose] def magneticMoment (m : ℝ) (B : Space → Space) (y v : Space) : ℝ :=
  m * (‖v‖ ^ 2 / ‖B y‖ - ⟪v, B y⟫ ^ 2 / ‖B y‖ ^ 3) / 2

/-- Sanity: the magnetic moment is `m |v - v_∥ b|²/(2|B|)`. -/
theorem magneticMoment_eq_perp (m : ℝ) (B : Space → Space) (y v : Space) (h : B y ≠ 0) :
    magneticMoment m B y v = m * ‖v - parallelVelocity B y v‖ ^ 2 / (2 * ‖B y‖) := by
  have hp : 0 < ‖B y‖ := norm_pos_iff.mpr h
  rw [magneticMoment, parallelVelocity, @norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, inner_smul_right]
  field_simp
  ring

/-- Derivative of `|β(t)|` along a curve where `β ≠ 0`. -/
theorem hasDerivAt_norm_curve {β : ℝ → Space} {β' : Space} {t : ℝ} (hβ : HasDerivAt β β' t)
    (h0 : β t ≠ 0) : HasDerivAt (fun r => ‖β r‖) (⟪β t, β'⟫ / ‖β t‖) t := by
  have hn := hβ.norm_sq
  have hpos : ‖β t‖ ^ 2 ≠ 0 := by positivity
  have := hn.sqrt hpos
  have heq : (fun r => √(‖β r‖ ^ 2)) = fun r => ‖β r‖ := by
    funext r; exact Real.sqrt_sq (norm_nonneg _)
  rw [heq, Real.sqrt_sq (norm_nonneg _)] at this
  convert this using 1
  have : ‖β t‖ ≠ 0 := by positivity
  field_simp

/-- Pointwise bound on `dμ/dt` along the orbit: `|dμ/dt| ≤ 3|m| G s³/B_min²`. -/
theorem magneticMoment_deriv_bound {m q G Bmin T : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (horbit : LorentzOrbit m q (fun _ => 0) B x v)
    (hB : ∀ y, HasFDerivAt B (DB y) y)
    (hBmin : 0 < Bmin) (hlow : ∀ τ ∈ Set.Icc 0 T, Bmin ≤ ‖B (x τ)‖)
    (hgrad : ∀ τ ∈ Set.Icc 0 T, ‖DB (x τ)‖ ≤ G) :
    ∀ t ∈ Set.Icc 0 T, ∃ μ', HasDerivAt (fun r => magneticMoment m B (x r) (v r)) μ' t ∧
      |μ'| ≤ 3 * |m| * G * ‖v 0‖ ^ 3 / Bmin ^ 2 := by
  intro t ht
  set S := ‖v 0‖
  have hspeed : ∀ r, ‖v r‖ = S := fun r => speed_conserved hm horbit r 0
  set β := fun r => B (x r) with hβdef
  set β' := DB (x t) (v t)
  have hβd : HasDerivAt β β' t := (hB (x t)).comp_hasDerivAt t (horbit.position t)
  have hNpos : 0 < ‖β t‖ := lt_of_lt_of_le hBmin (hlow t ht)
  have h0 : β t ≠ 0 := norm_pos_iff.mp hNpos
  have hN := hasDerivAt_norm_curve hβd h0
  obtain ⟨a, ha, hlaw⟩ := horbit.newton t
  have ha' : a = (q / m) • cross (v t) (β t) := by
    rw [zero_add] at hlaw
    rw [div_eq_inv_mul, mul_smul, ← hlaw, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hp := ha.inner ℝ hβd
  have hp' : ⟪v t, β'⟫ + ⟪a, β t⟫ = ⟪v t, β'⟫ := by
    rw [ha', inner_smul_left, real_inner_comm (β t) (cross (v t) (β t)), inner_cross_self']
    simp
  rw [hp'] at hp
  set N := ‖β t‖
  set p := ⟪v t, β t⟫
  set N' := ⟪β t, β'⟫ / N
  set w := ⟪v t, β'⟫
  have hfun : (fun r => magneticMoment m B (x r) (v r)) =
      fun r => m * (S ^ 2 / ‖β r‖ - ⟪v r, β r⟫ ^ 2 / ‖β r‖ ^ 3) / 2 := by
    funext r; simp [magneticMoment, hspeed r, hβdef]
  have hN0 : N ≠ 0 := hNpos.ne'
  have hd := ((((hasDerivAt_const t (S ^ 2)).div hN hN0).sub
    ((hp.pow 2).div (hN.pow 3) (pow_ne_zero 3 hN0))).const_mul m).div_const 2
  refine ⟨m / (2 * N ^ 2) * (-(S ^ 2 * N') - 2 * (p / N) * w + 3 * (p / N) ^ 2 * N'), ?_, ?_⟩
  · rw [hfun]
    convert hd using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  -- bounds on the pieces
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgrad t ht)
  have hβ'le : ‖β'‖ ≤ G * S := by
    rw [← hspeed t]
    exact ((DB (x t)).le_opNorm (v t)).trans (by gcongr; exact hgrad t ht)
  have hN'le : |N'| ≤ G * S := by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    calc |⟪β t, β'⟫| ≤ N * ‖β'‖ := abs_real_inner_le_norm _ _
      _ ≤ N * (G * S) := by gcongr
      _ = G * S * N := by ring
  have hple : |p| ≤ S * N := by
    rw [← hspeed t]; exact abs_real_inner_le_norm _ _
  have hwle : |w| ≤ S * (G * S) := by
    calc |w| ≤ ‖v t‖ * ‖β'‖ := abs_real_inner_le_norm _ _
      _ ≤ S * (G * S) := by rw [hspeed t]; gcongr
  have hS : 0 ≤ S := norm_nonneg _
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * N ^ 2)]
  have hu : |p / N| ≤ S := by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]; exact hple
  have hinner : |-(S ^ 2 * N') - 2 * (p / N) * w + 3 * (p / N) ^ 2 * N'| ≤ 6 * G * S ^ 3 := by
    have e1 : |S ^ 2 * N'| ≤ S ^ 2 * (G * S) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]; gcongr
    have e2 : |2 * (p / N) * w| ≤ 2 * S * (S * (G * S)) := by
      rw [abs_mul, abs_mul, abs_two]; gcongr
    have e3 : |3 * (p / N) ^ 2 * N'| ≤ 3 * S ^ 2 * (G * S) := by
      rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      gcongr
    calc _ ≤ |-(S ^ 2 * N') - 2 * (p / N) * w| + |3 * (p / N) ^ 2 * N'| := abs_add_le _ _
      _ ≤ |S ^ 2 * N'| + |2 * (p / N) * w| + |3 * (p / N) ^ 2 * N'| := by
        gcongr
        calc _ ≤ |-(S ^ 2 * N')| + |2 * (p / N) * w| := abs_sub _ _
          _ = _ := by rw [abs_neg]
      _ ≤ _ := by nlinarith
  calc |m| / (2 * N ^ 2) * |-(S ^ 2 * N') - 2 * (p / N) * w + 3 * (p / N) ^ 2 * N'|
      ≤ |m| / (2 * N ^ 2) * (6 * G * S ^ 3) := by gcongr
    _ ≤ |m| / (2 * Bmin ^ 2) * (6 * G * S ^ 3) := by
        gcongr
        exact hlow t ht
    _ = 3 * |m| * G * S ^ 3 / Bmin ^ 2 := by field_simp; ring

/-- **Crude finite-time magnetic-moment control**: `|μ(t) - μ(0)| ≤ 3|m| G s³ t/B_min² = 6 μ_s
(G/B_min) s t` with `μ_s = m s²/(2B_min)`. This is linear drift, not adiabatic invariance: it
does not use gyro-averaging. -/
theorem magneticMoment_drift {m q G Bmin T t : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (horbit : LorentzOrbit m q (fun _ => 0) B x v)
    (hB : ∀ y, HasFDerivAt B (DB y) y)
    (hBmin : 0 < Bmin) (hlow : ∀ τ ∈ Set.Icc 0 T, Bmin ≤ ‖B (x τ)‖)
    (hgrad : ∀ τ ∈ Set.Icc 0 T, ‖DB (x τ)‖ ≤ G) (ht : t ∈ Set.Icc 0 T) :
    |magneticMoment m B (x t) (v t) - magneticMoment m B (x 0) (v 0)| ≤
      3 * |m| * G * ‖v 0‖ ^ 3 / Bmin ^ 2 * t := by
  have h := magneticMoment_deriv_bound hm horbit hB hBmin hlow hgrad
  choose! μ' hμ' hb using h
  have := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => magneticMoment m B (x r) (v r))
    (fun s hs => (hμ' s hs).hasDerivWithinAt)
    (fun s hs => by simpa [Real.norm_eq_abs] using hb s (Set.Ico_subset_Icc_self hs)) t ht
  simpa [Real.norm_eq_abs] using this

/-- The parallel velocity is no larger than the speed. -/
theorem norm_parallelVelocity_le (B : Space → Space) (y v : Space) :
    ‖parallelVelocity B y v‖ ≤ ‖v‖ := by
  rw [parallelVelocity, norm_smul, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖B y‖ ^ 2)]
  rcases eq_or_ne ‖B y‖ 0 with h | h
  · simp [h]
  · have hp : 0 < ‖B y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    calc |⟪v, B y⟫| / ‖B y‖ ^ 2 * ‖B y‖ ≤ ‖v‖ * ‖B y‖ / ‖B y‖ ^ 2 * ‖B y‖ := by
          gcongr; exact abs_real_inner_le_norm _ _
      _ = ‖v‖ := by field_simp

/-- **Guiding-centre flux drift.** If `ψ` is a field-line first integral (`⟪∇ψ, B⟫ = 0`) with
`|∇ψ(X)| ≤ Ψ` and `|∇ψ(X) - ∇ψ(x)| ≤ H|X - x|` along the orbit, then `|ψ(X(t)) - ψ(X(0))| ≤ (H
+ Ψ G/B_min) ρ_L s t`. No symmetry is assumed. -/
theorem guidingCentre_flux_drift {m q G Bmin Ψ H T t : ℝ} {B : Space → Space}
    {DB : Space → Space →L[ℝ] Space} {x v : ℝ → Space} {ψ : Space → ℝ} {gψ : Space → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (horbit : LorentzOrbit m q (fun _ => 0) B x v)
    (hB : ∀ y, HasFDerivAt B (DB y) y)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (gψ y)) y) (hfirst : ∀ y, ⟪gψ y, B y⟫ = 0)
    (hBmin : 0 < Bmin) (hlow : ∀ τ ∈ Set.Icc 0 T, Bmin ≤ ‖B (x τ)‖)
    (hgrad : ∀ τ ∈ Set.Icc 0 T, ‖DB (x τ)‖ ≤ G)
    (hΨ : ∀ τ ∈ Set.Icc 0 T, ‖gψ (guidingCentre m q B (x τ) (v τ))‖ ≤ Ψ)
    (hH : ∀ τ ∈ Set.Icc 0 T, ‖gψ (guidingCentre m q B (x τ) (v τ)) - gψ (x τ)‖ ≤
      H * ‖guidingCentre m q B (x τ) (v τ) - x τ‖)
    (hH0 : 0 ≤ H) (ht : t ∈ Set.Icc 0 T) :
    |ψ (guidingCentre m q B (x t) (v t)) - ψ (guidingCentre m q B (x 0) (v 0))| ≤
      (H + Ψ * (G / Bmin)) * (|m| * ‖v 0‖ / (|q| * Bmin)) * ‖v 0‖ * t := by
  set ρ := |m| * ‖v 0‖ / (|q| * Bmin)
  set X := fun r => guidingCentre m q B (x r) (v r) with hX
  have hne : ∀ τ ∈ Set.Icc 0 T, B (x τ) ≠ 0 := fun τ hτ =>
    norm_pos_iff.mp (lt_of_lt_of_le hBmin (hlow τ hτ))
  have hd : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => ψ (X r))
      (⟪gψ (X s), parallelVelocity B (x s) (v s) +
        (m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))⟫) s := by
    intro s hs
    have := (hψ (X s)).comp_hasDerivAt s (guidingCentre_hasDerivAt hm hq horbit hB (hne s hs))
    rw [innerSL_apply_apply] at this
    exact this
  have hbound : ∀ s ∈ Set.Ico 0 T, ‖⟪gψ (X s), parallelVelocity B (x s) (v s) +
        (m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))⟫‖ ≤
      (H + Ψ * (G / Bmin)) * ρ * ‖v 0‖ := by
    intro s hs
    have hs' := Set.Ico_subset_Icc_self hs
    have hρ : ‖X s - x s‖ ≤ ρ := by
      have := norm_gyroVector_le (m := m) (q := q) (v := v s) hBmin (hlow s hs')
      rw [speed_conserved hm horbit s 0] at this
      simpa [hX, guidingCentre] using this
    have hpar : |⟪gψ (X s), parallelVelocity B (x s) (v s)⟫| ≤ H * ρ * ‖v 0‖ := by
      have h0 : ⟪gψ (x s), parallelVelocity B (x s) (v s)⟫ = 0 := by
        rw [parallelVelocity, inner_smul_right, hfirst, mul_zero]
      have : ⟪gψ (X s), parallelVelocity B (x s) (v s)⟫ =
          ⟪gψ (X s) - gψ (x s), parallelVelocity B (x s) (v s)⟫ := by
        rw [inner_sub_left, h0, sub_zero]
      rw [this]
      calc _ ≤ ‖gψ (X s) - gψ (x s)‖ * ‖parallelVelocity B (x s) (v s)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ (H * ρ) * ‖v 0‖ := by
            gcongr
            · exact (hH s hs').trans (by gcongr)
            · rw [← speed_conserved hm horbit s 0]; exact norm_parallelVelocity_le _ _ _
    have hres := norm_residual_le (m := m) (q := q) (v := v s) hBmin (hlow s hs') (hgrad s hs')
    rw [speed_conserved hm horbit s 0] at hres
    have hR : |⟪gψ (X s), (m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))⟫| ≤
        Ψ * (ρ * (G / Bmin) * ‖v 0‖) := by
      calc _ ≤ ‖gψ (X s)‖ * ‖(m / q) • cross (v s) (invFieldRate (B (x s)) (DB (x s) (v s)))‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ Ψ * (ρ * (G / Bmin) * ‖v 0‖) := by
            gcongr
            · exact (norm_nonneg _).trans (hΨ s hs')
            · exact hΨ s hs'
    rw [Real.norm_eq_abs, inner_add_right]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ H * ρ * ‖v 0‖ + Ψ * (ρ * (G / Bmin) * ‖v 0‖) := add_le_add hpar hR
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (fun s hs => (hd s hs).hasDerivWithinAt)
    hbound t ht
  simpa [Real.norm_eq_abs] using this

/-! ## (d) Sanity checks and realistic numbers -/

/-- Sanity: the guiding centre of the explicit helix in a uniform field is exactly its axis point
`X + (0, 0, w t)`, confirming the sign convention. -/
theorem helix_guidingCentre {m q B₀ : ℝ} (hq : q ≠ 0) (hB₀ : B₀ ≠ 0)
    (X : Space) (u w t : ℝ) :
    guidingCentre m q (uniformField B₀) (helixPosition X u w (q * B₀ / m) t)
      (helixVelocity u w (q * B₀ / m) t) = X + toLp 2 ![0, 0, w * t] := by
  have hn : ‖(toLp 2 ![0, 0, B₀] : Space)‖ ^ 2 = B₀ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three]
  ext i
  fin_cases i <;>
    simp [guidingCentre, gyroVector, invField, uniformField, hn, helixPosition, helixVelocity,
      cross, cross_apply] <;> field_simp <;> ring

/-- Sanity: in a uniform field (`G = 0`) the reduction error vanishes: `X(t) - X(0) = ∫₀ᵗ v_∥ b`
exactly. -/
theorem uniform_field_exact {m q T t : ℝ} {B₀ : Space} {x v : ℝ → Space}
    (hm : m ≠ 0) (hq : q ≠ 0) (hB₀ : B₀ ≠ 0)
    (horbit : LorentzOrbit m q (fun _ => 0) (fun _ => B₀) x v) (ht : t ∈ Set.Icc 0 T) :
    guidingCentre m q (fun _ => B₀) (x t) (v t) - guidingCentre m q (fun _ => B₀) (x 0) (v 0)
       = ∫ τ in (0:ℝ)..t, parallelVelocity (fun _ => B₀) (x τ) (v τ) := by
  have hpos : 0 < ‖B₀‖ := norm_pos_iff.mpr hB₀
  have h := guidingCentre_reduction_bound (G := 0) (DB := fun _ => 0) hm hq horbit
    (fun y => hasFDerivAt_const B₀ y) hpos (fun _ _ => le_rfl) (fun _ _ => by simp) ht
  simp only [zero_div, mul_zero, zero_mul] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- The reduction-error rate `ρ_L (G/B_min) s` of `guidingCentre_reduction_bound`. -/
@[expose] def reductionRate (m q s Bmin G : ℝ) : ℝ :=
  (|m| * s / (|q| * Bmin)) * (G / Bmin) * s

/-- For `m > 0`, `ρ_L s = 2K/(|q| B_min)` with `K = m s²/2`, so the rate needs no square root. -/
theorem reductionRate_eq_energy (m q s Bmin G : ℝ) (hm : 0 < m) :
    reductionRate m q s Bmin G = 2 * (m * s ^ 2 / 2) / (|q| * Bmin) * (G / Bmin) := by
  unfold reductionRate
  rw [abs_of_pos hm]
  rcases eq_or_ne (|q| * Bmin) 0 with h | h
  · simp [h]
  · field_simp

/-- The magnetic-moment drift rate in units of `μ_s = m s²/(2B_min)`: `3 m G s³/B_min² = 6 μ_s
(G/B_min) s`. -/
theorem moment_rate_eq (m s Bmin G : ℝ) (hm : 0 < m) (hB : 0 < Bmin) :
    3 * |m| * G * s ^ 3 / Bmin ^ 2 = 6 * (m * s ^ 2 / (2 * Bmin)) * (G / Bmin) * s := by
  rw [abs_of_pos hm]; field_simp; ring

/-- Dimensionless example: `m = q = s = B_min = 1`, `G = 1/100`; deviation at most `1/10` up to `t
= 10`. -/
theorem dimensionless_example (t : ℝ) (ht : t ≤ 10) :
    reductionRate 1 1 1 1 (1 / 100) * t ≤ 1 / 10 := by
  norm_num [reductionRate]; linarith

/-- A 3.5 MeV alpha (rounded CODATA mass and charge) with `B_min = 5 T`, `G/B_min = 1 m⁻¹`: the
reduction-error rate is exactly `7 × 10⁵ m/s`. -/
theorem alpha_reductionRate {s : ℝ} (hs : 6.6447e-27 * s ^ 2 / 2 = 3.5e6 * 1.6022e-19) :
    reductionRate 6.6447e-27 (2 * 1.6022e-19) s 5 5 = 7e5 := by
  rw [reductionRate_eq_energy _ _ _ _ _ (by norm_num), hs]
  norm_num

/-- For the 3.5 MeV alpha at 5 T with `L_B = 1 m`, the guiding centre stays within 10 cm of
field-line following for `t ≤ 1/(7 × 10⁶) s ≈ 1.43 × 10⁻⁷ s`. -/
theorem alpha_horizon {s t : ℝ} (hs : 6.6447e-27 * s ^ 2 / 2 = 3.5e6 * 1.6022e-19)
    (ht : t ≤ 1 / 7e6) : reductionRate 6.6447e-27 (2 * 1.6022e-19) s 5 5 * t ≤ 1 / 10 := by
  rw [alpha_reductionRate hs]
  have := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 7e5)
  norm_num at this ⊢; linarith

/-- The 3.5 MeV alpha speed lies between `1.29 × 10⁷` and `1.30 × 10⁷ m/s`. -/
theorem alpha_speed_sq :
    (1.29e7 : ℝ) ^ 2 < 2 * (3.5e6 * 1.6022e-19) / 6.6447e-27 ∧
      2 * (3.5e6 * 1.6022e-19) / 6.6447e-27 < (1.30e7 : ℝ) ^ 2 := by
  norm_num

/-- Within the horizon `1/(7 × 10⁶) s` the alpha travels between 1.85 m and 1.86 m: the bound
covers about `L_B · δ/ρ_L` of path length. -/
theorem alpha_horizon_distance :
    (1.85 : ℝ) ^ 2 < 2 * (3.5e6 * 1.6022e-19) / 6.6447e-27 * (1 / 7e6) ^ 2 ∧
      2 * (3.5e6 * 1.6022e-19) / 6.6447e-27 * (1 / 7e6 : ℝ) ^ 2 < 1.86 ^ 2 := by
  norm_num

/-- The 3.5 MeV alpha gyroperiod at 5 T is between `2.6 × 10⁻⁸` and `2.7 × 10⁻⁸ s`. -/
theorem alpha_gyroperiod :
    (2.6e-8 : ℝ) < 2 * 3.1415 * 6.6447e-27 / (2 * 1.6022e-19 * 5) ∧
      2 * 3.1416 * 6.6447e-27 / (2 * 1.6022e-19 * 5) < (2.7e-8 : ℝ) := by
  norm_num

/-- The crude `μ` bound keeps `|Δμ| ≤ μ_s/10` only for `t ≤ 1.28 × 10⁻⁹ s`, shorter than one
gyroperiod. -/
theorem alpha_moment_horizon :
    6 * (1 : ℝ) * (1.30e7 * 1.28e-9) < 1 / 10 := by
  norm_num

/-- Flux-drift horizon for the alpha with `H = Ψ · 1 m⁻¹`, `G/B_min = 1 m⁻¹`: the normalized flux
shift is at most 10 cm for `t ≤ 1/(1.4 × 10⁷) s ≈ 7.1 × 10⁻⁸ s`. -/
theorem alpha_flux_horizon {s t : ℝ} (hs : 6.6447e-27 * s ^ 2 / 2 = 3.5e6 * 1.6022e-19)
    (ht : t ≤ 1 / 1.4e7) :
    (1 + 1 * ((5 : ℝ) / 5)) * (|(6.6447e-27 : ℝ)| * s / (|(2 * 1.6022e-19 : ℝ)| * 5)) * s * t
      ≤ 1 / 10 := by
  have h := alpha_reductionRate hs
  unfold reductionRate at h
  have e : (1 + 1 * ((5 : ℝ) / 5)) * (|(6.6447e-27 : ℝ)| * s / (|(2 * 1.6022e-19 : ℝ)| * 5)) * s
      = 2 * 7e5 := by rw [← h]; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2 * 7e5)
  norm_num at this ⊢; linarith

/-- Comparison with the ballistic time for 10 cm (`≈ 7.7 × 10⁻⁹ s`): the guiding-centre horizon is
better by a factor above 9 (about `L_B/(2ρ_L)`), still about seven orders of magnitude short
of slowing-down times. -/
theorem alpha_ballistic_comparison :
    (1 / 10 : ℝ) / 1.29e7 < 7.8e-9 ∧ (7.1e-8 : ℝ) < 1 / 1.4e7 ∧ (7.1e-8 : ℝ) / 7.8e-9 > 9 := by
  norm_num

end PlasmaLean.Kinetic.GuidingCentre
