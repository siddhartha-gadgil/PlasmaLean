/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.GuidingCentreLittlejohn
public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre

/-!
# Strict model audit: orbit models `LittlejohnOrbit`, `LorentzOrbit`, `BoozerGCOrbit`

Added by the first strict audit of the model layer outside `Kernel/` (finding H-1 of
`notes/audit/2026-10-30-repository-audit.md`; record in `notes/audit/2026-10-30-model-audit.md`,
commit `cda8bd0`). The source modules already prove energy conservation, a uniform-field
instance and (Boozer) the momentum identity. This module adds:

**Littlejohn guiding centre** (`Kinetic.GCLittlejohn.LittlejohnOrbit`)
* totalization regression (finding MA-L2): in the zero field `B*_∥ = 0`, so `(B*_∥)⁻¹ = 0` and
  every motionless pair `(X ≡ X₀, v_∥ ≡ v₀)`, also with `v₀ ≠ 0`, is an orbit
  (`littlejohn_zero_field_static`);
* counterexample: in a uniform nonzero field a guiding centre with `v_∥ ≠ 0` cannot stand still
  (`littlejohn_static_not_orbit`);
* symmetry: charge conjugation `(q, B, v_∥) ↦ (−q, −B, −v_∥)` maps orbits to orbits
  (`LittlejohnOrbit.charge_conj`);
* exact solution, sign of the drift: in `B = e^{x₁} e_z` the orbit
  `X(t) = X₀ + t ((μ/q) e_y + v₀ e_z)` is exact, i.e. the drift is the textbook grad-B drift
  `(μ/(qB)) b × ∇B` with the correct sign and magnitude (`gradB_drift_orbit`).

**Newton–Lorentz** (`Kinetic.LorentzOrbit`)
* degenerate case: free straight-line motion in zero fields (`lorentz_free_particle`);
* orientation of `cross` (right-hand rule, `cross_e1_e3`) and a counterexample: uniform straight
  motion across a uniform field is not an orbit (`lorentz_straight_not_orbit`).

**Boozer guiding centre** (`Kinetic.Boozer.BoozerGCOrbit`)
* characterization: the toroidal transit rate is `φ̇ = v_∥ B/G` (`BoozerGCOrbit.toroidal_rate`),
  which for `G = B₀R₀` and constant `B = B₀` is `v_∥/R₀` (`constField_transit_rate`);
* totalization regression (finding MA-L3): with `G = 0` every constant state, even with
  `ρ_∥ ≠ 0`, is an orbit (`boozer_G_zero_static`); counterexample for `G ≠ 0`
  (`boozer_static_not_orbit`);
* structure of the radial drift: if `∂_θ B ≡ 0` then `ψ` is constant along every orbit
  (`BoozerGCOrbit.psi_const_of_Btheta_zero`).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditModel
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Kinetic.GCLittlejohn WithLp

/-! ### Littlejohn guiding-centre orbits -/

/-- Regression (MA-L2, totalized `(B*_∥)⁻¹`): in the zero field every motionless state, with any
parallel velocity `v₀` (also `v₀ ≠ 0`), is a `LittlejohnOrbit`. Physical orbits need `B*_∥ ≠ 0`,
which every downstream confinement theorem imposes through its rate hypothesis. -/
theorem littlejohn_zero_field_static (m q μ v₀ : ℝ) (X₀ : Space) :
    LittlejohnOrbit m q μ (fun _ => 0) (fun _ => X₀) (fun _ => v₀) := by
  have hb : ∀ x, bhat (fun _ : Space => (0 : Space)) x = 0 := fun x => by simp [bhat]
  have hp : ∀ v x, BstarPar m q (fun _ : Space => (0 : Space)) v x = 0 := fun v x => by
    simp [BstarPar, hb]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simpa [hp] using hasDerivAt_const t X₀
  · simpa [hp] using hasDerivAt_const t v₀

/-- Counterexample: in a uniform nonzero field a guiding centre with `v_∥ = v₀ ≠ 0` cannot stay
at rest, so `LittlejohnOrbit` has content. -/
theorem littlejohn_static_not_orbit (m q μ : ℝ) {v₀ : ℝ} (hv : v₀ ≠ 0) {B₀ : Space}
    (hB : B₀ ≠ 0) (X₀ : Space) :
    ¬ LittlejohnOrbit m q μ (fun _ => B₀) (fun _ => X₀) (fun _ => v₀) := by
  intro h
  have h1 := (h.hX 0).unique (hasDerivAt_const 0 X₀)
  have hg : gradAbsB (fun _ : Space => B₀) X₀ = 0 := by simp [gradAbsB]
  have hx : cross (bhat (fun _ : Space => B₀) X₀) 0 = 0 := by simp [cross]
  rw [BstarPar_const _ _ _ hB, hg, hx] at h1
  simp only [Bstar, curlb_const, smul_zero, add_zero, smul_smul] at h1
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hB)) hv h2
  · exact hB h2

/-- `b(−B) = −b(B)`. -/
theorem bhat_neg (B : Space → Space) : bhat (fun x => -B x) = fun x => -bhat B x := by
  funext x; simp [bhat]

/-- `∇ × b(−B) = −∇ × b(B)` (no differentiability needed: `fderiv` of a negation). -/
theorem curlb_neg (B : Space → Space) : curlb (fun x => -B x) = fun x => -curlb B x := by
  funext x
  rw [curlb, curlb, bhat_neg, fderiv_fun_neg]
  simp [curl]

/-- `∇|−B| = ∇|B|`. -/
theorem gradAbsB_neg (B : Space → Space) : gradAbsB (fun x => -B x) = gradAbsB B := by
  funext x; simp [gradAbsB]

/-- `B*` under charge conjugation. -/
theorem Bstar_charge_conj (m q : ℝ) (B : Space → Space) (v : ℝ) (x : Space) :
    Bstar m (-q) (fun x => -B x) (-v) x = -Bstar m q B v x := by
  rw [Bstar, Bstar, curlb_neg, show m * -v / -q = m * v / q by ring]
  simp only [smul_neg, neg_add]

/-- `B*_∥` is invariant under charge conjugation. -/
theorem BstarPar_charge_conj (m q : ℝ) (B : Space → Space) (v : ℝ) (x : Space) :
    BstarPar m (-q) (fun x => -B x) (-v) x = BstarPar m q B v x := by
  rw [BstarPar, BstarPar, Bstar_charge_conj, bhat_neg]
  exact inner_neg_neg _ _

/-- `(−u) × w = −(u × w)`. -/
theorem cross_neg_left (u w : Space) : cross (-u) w = -cross u w := by
  apply space_ext <;> simp [cross, cross_apply]

/-- **Charge-conjugation symmetry** of the Littlejohn equations: if `(X, v_∥)` is an orbit of a
charge `q` in `B`, then `(X, −v_∥)` is an orbit of the charge `−q` in `−B` (the same particle
path). This checks the relative signs of `v_∥ B*`, `(μ/q) b × ∇|B|` and the mirror force. -/
theorem LittlejohnOrbit.charge_conj {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B X v) :
    LittlejohnOrbit m (-q) μ (fun x => -B x) X (fun t => -v t) where
  hX t := by
    convert h.hX t using 1
    rw [BstarPar_charge_conj, Bstar_charge_conj, gradAbsB_neg, bhat_neg]
    simp only [cross_neg_left, div_neg, neg_smul, smul_neg, neg_neg]
  hv t := by
    convert (h.hv t).neg using 1
    rw [BstarPar_charge_conj, Bstar_charge_conj, gradAbsB_neg, inner_neg_left]
    ring

/-- The field `B(x) = e^{x₁} e_z` (strength increasing along `e_x`, straight lines). -/
@[expose] def gradBField (x : Space) : Space := Real.exp (x 0) • basis 2

/-- In `gradBField`, `b = e_z` everywhere. -/
theorem bhat_gradBField : bhat gradBField = fun _ => basis 2 := by
  funext x
  have hn : ‖gradBField x‖ = Real.exp (x 0) := by
    simp [gradBField, norm_smul]
  rw [bhat, hn, gradBField, smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]

/-- In `gradBField`, `∇ × b = 0`. -/
theorem curlb_gradBField (x : Space) : curlb gradBField x = 0 := by
  rw [curlb, bhat_gradBField]
  simp [curl]

/-- In `gradBField`, `∇|B| = e^{x₁} e_x`. -/
theorem gradAbsB_gradBField (x : Space) : gradAbsB gradBField x = Real.exp (x 0) • basis 0 := by
  have hn : (fun y => ‖gradBField y‖) = fun y : Space => Real.exp (y 0) := by
    funext y
    simp [gradBField, norm_smul]
  have hf : HasFDerivAt (fun y : Space => Real.exp (y 0))
      (Real.exp (x 0) • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) x :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.exp
  have hg : HasGradientAt (fun y : Space => Real.exp (y 0)) (Real.exp (x 0) • basis 0) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hf using 1
    ext y
    simp [EuclideanSpace.inner_single_left]
  rw [gradAbsB, hn]
  exact hg.gradient

/-- `e_z × e_x = e_y`. -/
theorem cross_e3_e1 : cross (basis 2) (basis 0) = basis 1 := by
  apply space_ext <;> simp [cross, cross_apply]

/-- **Exact grad-B drift (sign and magnitude of the drift term).** In `B = e^{x₁} e_z` the state
`X(t) = X₀ + t ((μ/q) e_y + v₀ e_z)`, `v_∥ ≡ v₀` is an exact Littlejohn orbit for every
`m, q, μ, v₀`: the guiding centre drifts with the textbook grad-B velocity
`(μ/(qB)) b × ∇B = (μ/q) e_y` (here `|∇B|/B = 1`), and the mirror force vanishes since
`B* ⊥ ∇|B|`. -/
theorem gradB_drift_orbit (m q μ v₀ : ℝ) (X₀ : Space) :
    LittlejohnOrbit m q μ gradBField (fun t => X₀ + t • ((μ / q) • basis 1 + v₀ • basis 2))
      (fun _ => v₀) := by
  have hX0 : ∀ t : ℝ, (X₀ + t • ((μ / q) • basis 1 + v₀ • basis 2)) 0 = X₀ 0 := fun t => by
    simp
  have hBs : ∀ v x, Bstar m q gradBField v x = Real.exp (x 0) • basis 2 := fun v x => by
    simp [Bstar, curlb_gradBField, gradBField]
  have hBp : ∀ v x, BstarPar m q gradBField v x = Real.exp (x 0) := fun v x => by
    rw [BstarPar, hBs, bhat_gradBField]
    simp [inner_smul_right]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hd := ((hasDerivAt_id' t).smul_const ((μ / q) • basis 1 + v₀ • basis 2)).const_add X₀
    refine hd.congr_deriv ?_
    rw [hBp, hBs, gradAbsB_gradBField, bhat_gradBField, hX0]
    have he := (Real.exp_pos (X₀ 0)).ne'
    rw [show cross (basis 2) (Real.exp (X₀ 0) • basis 0) = Real.exp (X₀ 0) • basis 1 by
      rw [← cross_e3_e1]; apply space_ext <;> simp [cross, cross_apply]]
    have hc : ∀ c : ℝ, (Real.exp (X₀ 0))⁻¹ * (c * Real.exp (X₀ 0)) = c := fun c => by
      field_simp
    simp only [one_mul, smul_add, smul_smul, hc]
    exact add_comm _ _
  · rw [hBs, gradAbsB_gradBField]
    simpa [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left] using
      hasDerivAt_const t v₀

/-! ### Newton–Lorentz orbits -/

/-- Degenerate case: with `E = 0` and `B = 0` uniform straight-line motion is a Newton–Lorentz
orbit (for every mass and charge). -/
theorem lorentz_free_particle (m q : ℝ) (X₀ u : Space) :
    LorentzOrbit m q (fun _ => 0) (fun _ => 0) (fun t => X₀ + t • u) (fun _ => u) where
  position t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add X₀
  newton t := ⟨0, hasDerivAt_const t u, by simp [cross]⟩

/-- Orientation of `cross` (right-hand rule): `e_x × e_z = −e_y`, so the magnetic force
`q v × B` on a positive charge moving along `+e_x` in `B ∥ +e_z` points along `−e_y`. -/
theorem cross_e1_e3 : cross (basis 0) (basis 2) = -basis 1 := by
  apply space_ext <;> simp [cross, cross_apply]

/-- Counterexample: uniform straight motion across a uniform field `B₀ e_z` (`q B₀ ≠ 0`,
`u ≠ 0`) is not a Newton–Lorentz orbit. -/
theorem lorentz_straight_not_orbit {m q B₀ u : ℝ} (hqB : q * B₀ ≠ 0) (hu : u ≠ 0) (X₀ : Space) :
    ¬ LorentzOrbit m q (fun _ => 0) (uniformField B₀) (fun t => X₀ + t • (u • basis 0))
      (fun _ => u • basis 0) := by
  intro h
  obtain ⟨a, ha, hlaw⟩ := h.newton 0
  have ha0 : a = 0 := ha.unique (hasDerivAt_const 0 _)
  rw [ha0, smul_zero] at hlaw
  have h1 : q = 0 ∨ u = 0 ∨ B₀ = 0 := by
    simpa [cross, cross_apply, uniformField] using congrArg (fun w : Space => w 1) hlaw
  rcases h1 with h1 | h1 | h1
  · exact hqB (by rw [h1, zero_mul])
  · exact hu h1
  · exact hqB (by rw [h1, mul_zero])

/-! ### Boozer guiding-centre orbits -/

section Boozer
open PlasmaLean.Kinetic.Boozer

/-- **Toroidal transit rate**: along every Boozer guiding-centre orbit `φ̇ = v_∥ B/G`. -/
theorem BoozerGCOrbit.toroidal_rate {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (t : ℝ) :
    HasDerivAt φ (parallelVelocity F m q ψ θ φ ρ t * along F.B ψ θ φ t / F.G) t := by
  convert h.dφ t using 1
  simp only [parallelVelocity]
  ring

/-- With `B ≡ B₀ ≠ 0` and the vacuum value `G = B₀R₀` (`B = G ∇φ`, `|∇φ| = 1/R₀`), the transit
rate is `v_∥/R₀`, the Littlejohn/Lorentz value: the units of `G` and `ρ_∥` are consistent. -/
theorem constField_transit_rate {B₀ ι₀ R₀ m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hB : B₀ ≠ 0)
    (hR : R₀ ≠ 0) (h : BoozerGCOrbit (constField B₀ ι₀ (B₀ * R₀)) m q μ ψ θ φ ρ) (t : ℝ) :
    HasDerivAt φ (parallelVelocity (constField B₀ ι₀ (B₀ * R₀)) m q ψ θ φ ρ t / R₀) t := by
  convert BoozerGCOrbit.toroidal_rate h t using 1
  simp only [along, constField]
  field_simp

/-- Regression (MA-L3, totalized division by `G`): with `G = 0` every constant state with
`ψ₀ > 0`, including `ρ₀ ≠ 0` (nonzero parallel velocity), is a Boozer orbit. Every downstream
theorem assumes `G ≠ 0` (`reactorQA.G = 58.1`). -/
theorem boozer_G_zero_static (B₀ ι₀ m q μ : ℝ) {ψ₀ : ℝ} (hψ : 0 < ψ₀) (θ₀ φ₀ ρ₀ : ℝ) :
    BoozerGCOrbit (constField B₀ ι₀ 0) m q μ (fun _ => ψ₀) (fun _ => θ₀) (fun _ => φ₀)
      (fun _ => ρ₀) where
  pos _ := hψ
  dψ t := by simpa [constField, along] using hasDerivAt_const t ψ₀
  dθ t := by simpa [constField, along] using hasDerivAt_const t θ₀
  dφ t := by simpa [constField, along] using hasDerivAt_const t φ₀
  dρ t := by simpa [constField, along] using hasDerivAt_const t ρ₀

/-- Counterexample: for `G, m, q, B₀, ρ₀ ≠ 0` the constant state is not an orbit (the
toroidal angle must advance). -/
theorem boozer_static_not_orbit {B₀ ι₀ G m q μ ψ₀ θ₀ φ₀ ρ₀ : ℝ} (hB : B₀ ≠ 0) (hG : G ≠ 0)
    (hm : m ≠ 0) (hq : q ≠ 0) (hρ : ρ₀ ≠ 0) :
    ¬ BoozerGCOrbit (constField B₀ ι₀ G) m q μ (fun _ => ψ₀) (fun _ => θ₀) (fun _ => φ₀)
      (fun _ => ρ₀) := by
  intro h
  have h1 := (h.dφ 0).unique (hasDerivAt_const 0 φ₀)
  simp only [along, constField] at h1
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hq hρ) (pow_ne_zero 2 hB)) (mul_ne_zero hG hm) h1

/-- Structure of the radial drift: if `∂_θ B ≡ 0`, the flux label is constant along every orbit
(the radial drift is driven only by `∂_θ B`). -/
theorem BoozerGCOrbit.psi_const_of_Btheta_zero {F : BoozerField} {m q μ : ℝ}
    {ψ θ φ ρ : ℝ → ℝ} (h : BoozerGCOrbit F m q μ ψ θ φ ρ) (hθ : ∀ x y z, F.Bθ x y z = 0)
    (s t : ℝ) : ψ s = ψ t := by
  have hd (r : ℝ) : HasDerivAt ψ 0 r := by simpa [along, hθ] using h.dψ r
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s t

end Boozer

end PlasmaLean.Sanity.AuditModel
