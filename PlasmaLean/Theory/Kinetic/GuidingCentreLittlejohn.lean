/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.Maxwell
public import PlasmaLean.Theory.Fields.InvariantBarrier
public import PlasmaLean.Theory.Kinetic.FullOrbit
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Littlejohn guiding-centre equations and the modified field `B̃ = B + ρ ∇×b`

**This is a supplied MODEL, not a theorem about the Lorentz force** (compare
`Kinetic/BoozerGuidingCentre`). The state is the guiding-centre position `X ∈ ℝ³` and the parallel
velocity `v = v_∥`; the magnetic moment `μ`, mass `m` and charge `q` are constants. For a static
magnetic field `B` and `E = 0`, the Littlejohn guiding-centre equations
(R. G. Littlejohn, J. Plasma Phys. 29 (1983) 111; J. R. Cary and A. J. Brizard,
Rev. Mod. Phys. 81 (2009) 693, guiding-centre equations of motion) are

    b = B/|B|,   B* = B + (m v_∥/q) ∇×b,   B*_∥ = b · B*,
    B*_∥ dX/dt   = v_∥ B* + (μ/q) b × ∇|B|,
    m B*_∥ dv_∥/dt = −μ B* · ∇|B|,

with Hamiltonian `H = m v_∥²/2 + μ|B|`. In `LittlejohnOrbit` they are stated with `(B*_∥)⁻¹`
multiplying the right-hand side (Lean's `0⁻¹ = 0` convention; physically `B*_∥ ≠ 0`). The derivation
of these equations from the Newton–Lorentz equations (guiding-centre asymptotics, adiabatic
invariance of `μ`) is **not formalized**. Orbits are supplied, not constructed. Derivatives are
Fréchet derivatives on `Space = EuclideanSpace ℝ (Fin 3)`, with `divergence`/`curl` from
`Fields/Maxwell` (these agree with the kernel's `Vacuum.divOp`/`Vacuum.curlOp`, see
`Sanity/Vacuum`), and `∇|B|` is Mathlib's `gradient`.

Results.

* `energy_const`: `H` is conserved along every orbit (`m ≠ 0`, `|B|` differentiable along it).
* `vpar_const_of_mu_zero`: for `μ = 0`, `v_∥` is constant.
* `velocity_eq_modField`: for `μ = 0`, `dX/dt = (v_∥/B*_∥) B̃(X)` with
  `B̃ = modField ρ_s B = B + ρ_s ∇×b`, `ρ_s = m v_∥(0)/q`
  (exact, since `B* = B̃` for constant `v_∥`).
* `modField_divFree`: `∇·B̃ = 0` when `∇·B = 0` and `b` is `C²` (via `divergence_curl`:
  `∇·(∇×b) = 0`, symmetry of second derivatives).
* `isFieldLine_of_timeChange`, `isFieldLine_of_rate_ge`: a solution of `dX/dt = λ(t) V(X)` with
  `λ > 0` is a time-changed `IsFieldLine` of `V` (for `λ < 0` use `V ↦ −V`).
* `littlejohn_mu0_isFieldLine`, `littlejohn_mu0_confined`: a `μ = 0` guiding centre with
  `0 < c ≤ v_∥/B*_∥(X(t))` is a reparametrized field line of `B̃`; any all-time field-line
  confinement theorem for `B̃` therefore transfers to the guiding-centre orbit.
  `littlejohn_mu0_isFieldLine_neg` treats `v_∥/B*_∥ ≤ −c < 0` with the field `−B̃`.
* sanity: `modField_zero` (`ρ_s = 0` recovers `B`), uniform field (`curlb_const`,
  `modField_const`, `BstarPar_const`, explicit orbit `uniform_orbit`, non-vacuity).

Not covered here: the general-`μ` identity `B*_∥ Ẋ = v_∥ ∇×(A + (m v_∥(X)/q) b)` (needs the
product rule for `∇×(f b)`); in this file the reduction is proved for `μ = 0`.
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace PlasmaLean.Kinetic.GCLittlejohn
open PlasmaLean.Fields PlasmaLean.Kinetic Filter

/-- Unit vector along the field, `b = B/|B|` (zero where `B = 0`). -/
@[expose] def bhat (B : Space → Space) (x : Space) : Space := ‖B x‖⁻¹ • B x

/-- Curl of the unit vector, `∇ × b`. -/
@[expose] def curlb (B : Space → Space) (x : Space) : Space := curl (fderiv ℝ (bhat B) x)

/-- Gradient of the field strength, `∇|B|`. -/
@[expose] def gradAbsB (B : Space → Space) (x : Space) : Space := gradient (fun y => ‖B y‖) x

/-- The Littlejohn effective field `B* = B + (m v_∥/q) ∇×b`. -/
@[expose] def Bstar (m q : ℝ) (B : Space → Space) (v : ℝ) (x : Space) : Space :=
  B x + (m * v / q) • curlb B x

/-- The parallel component `B*_∥ = b · B*`. -/
@[expose] def BstarPar (m q : ℝ) (B : Space → Space) (v : ℝ) (x : Space) : ℝ :=
  ⟪bhat B x, Bstar m q B v x⟫

/-- Guiding-centre Hamiltonian `H = m v_∥²/2 + μ|B(X)|`. -/
@[expose] def hamiltonian (m μ : ℝ) (B : Space → Space) (x : Space) (v : ℝ) : ℝ :=
  m * v ^ 2 / 2 + μ * ‖B x‖

/-- The modified field `B̃ = B + ρ ∇×b`. With `ρ = ρ_s = m v_∥/q` it is the field whose lines are
the passing `μ = 0` guiding-centre orbits. -/
@[expose] def modField (ρ : ℝ) (B : Space → Space) (x : Space) : Space := B x + ρ • curlb B x

/-- **Littlejohn guiding-centre orbit** (supplied model; static `B`, `E = 0`):
`dX/dt = (B*_∥)⁻¹ (v_∥ B* + (μ/q) b × ∇|B|)` and `dv_∥/dt = −(μ/m) (B*_∥)⁻¹ B* · ∇|B|`,
at all times. -/
structure LittlejohnOrbit (m q μ : ℝ) (B : Space → Space) (X : ℝ → Space) (v : ℝ → ℝ) :
    Prop where
  /-- Guiding-centre velocity equation. -/
  hX : ∀ t, HasDerivAt X ((BstarPar m q B (v t) (X t))⁻¹ •
    (v t • Bstar m q B (v t) (X t) + (μ / q) • cross (bhat B (X t)) (gradAbsB B (X t)))) t
  /-- Parallel-velocity equation (mirror force along `B*`). -/
  hv : ∀ t, HasDerivAt v (-(μ / m) * (BstarPar m q B (v t) (X t))⁻¹ *
    ⟪Bstar m q B (v t) (X t), gradAbsB B (X t)⟫) t

/-- `B*` is the modified field with `ρ = m v_∥/q`. -/
theorem Bstar_eq_modField (m q : ℝ) (B : Space → Space) (v : ℝ) (x : Space) :
    Bstar m q B v x = modField (m * v / q) B x := rfl

/-- The time derivative of the Hamiltonian along an orbit vanishes. -/
theorem hamiltonian_hasDerivAt {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q μ B X v) (hm : m ≠ 0)
    (hd : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t)) (t : ℝ) :
    HasDerivAt (fun s => hamiltonian m μ B (X s) (v s)) 0 t := by
  have hn : HasDerivAt (fun s => ‖B (X s)‖)
      (⟪gradAbsB B (X t), (BstarPar m q B (v t) (X t))⁻¹ •
        (v t • Bstar m q B (v t) (X t) + (μ / q) • cross (bhat B (X t)) (gradAbsB B (X t)))⟫)
      t := by
    exact ((hd t).hasGradientAt.hasFDerivAt).comp_hasDerivAt t (h.hX t)
  have hH := (((h.hv t).pow 2).const_mul m |>.div_const 2).add (hn.const_mul μ)
  convert hH using 1
  · funext s; simp [hamiltonian]
  rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_cross_self', real_inner_comm (gradAbsB B (X t))]
  field_simp
  push_cast
  ring

/-- **Energy conservation**: `H = m v_∥²/2 + μ|B(X)|` is constant along every Littlejohn orbit. -/
theorem energy_const {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q μ B X v) (hm : m ≠ 0)
    (hd : ∀ t, DifferentiableAt ℝ (fun y => ‖B y‖) (X t)) (t : ℝ) :
    m * v t ^ 2 / 2 + μ * ‖B (X t)‖ = m * v 0 ^ 2 / 2 + μ * ‖B (X 0)‖ := by
  have hD := hamiltonian_hasDerivAt h hm hd
  exact is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t 0

/-- For `μ = 0` the parallel velocity is constant. -/
theorem vpar_const_of_mu_zero {m q : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 B X v) (t : ℝ) : v t = v 0 := by
  have hD : ∀ s, HasDerivAt v 0 s := fun s => by simpa using h.hv s
  exact is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t 0

/-- **Guiding-centre velocity along the modified field** (`μ = 0`):
`dX/dt = (v_∥/B*_∥) B̃(X)` with `B̃ = B + ρ_s ∇×b`, `ρ_s = m v_∥/q`. -/
theorem velocity_eq_modField {m q : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 B X v) (t : ℝ) :
    HasDerivAt X ((v 0 / BstarPar m q B (v 0) (X t)) • modField (m * v 0 / q) B (X t)) t := by
  have h1 := h.hX t
  rw [vpar_const_of_mu_zero h t] at h1
  convert h1 using 1
  simp [Bstar_eq_modField, smul_smul, div_eq_mul_inv, mul_comm]

/-- `deriv` form of `velocity_eq_modField`. -/
theorem deriv_eq_modField {m q : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 B X v) (t : ℝ) :
    deriv X t = (v 0 / BstarPar m q B (v 0) (X t)) • modField (m * v 0 / q) B (X t) :=
  (velocity_eq_modField h t).deriv

/-! ### Divergence of the modified field -/

/-- `∇ · (∇ × b) = 0` at a point where `b` is `C²` (symmetry of second derivatives). -/
theorem divergence_curl {b : Space → Space} {x : Space} (hb : ContDiffAt ℝ 2 b x) :
    divergence (fderiv ℝ (fun y => curl (fderiv ℝ b y)) x) = 0 := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ b) x :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF : HasFDerivAt (fun y => curl (fderiv ℝ b y)) (curlCLM.comp (fderiv ℝ (fderiv ℝ b) x))
      x := curlCLM.hasFDerivAt.comp x hdd.hasFDerivAt
  have hsym := hb.isSymmSndFDerivAt (by simp)
  rw [hF.fderiv, divergence_apply]
  set D := fderiv ℝ (fderiv ℝ b) x
  change curl (D (basis 0)) 0 + curl (D (basis 1)) 1 + curl (D (basis 2)) 2 = 0
  rw [(curl_coords _).1, (curl_coords _).2.1, (curl_coords _).2.2,
    hsym (basis 0) (basis 1), hsym (basis 1) (basis 2), hsym (basis 0) (basis 2)]
  ring

/-- **The modified field is divergence free**: `∇·B̃ = ∇·B + ρ ∇·(∇×b) = 0` when `∇·B = 0`,
`B` is differentiable and `b` is `C²` at the point. -/
theorem modField_divFree {ρ : ℝ} {B : Space → Space} {x : Space} (hB : DifferentiableAt ℝ B x)
    (hb : ContDiffAt ℝ 2 (bhat B) x) (hdiv : divergence (fderiv ℝ B x) = 0) :
    divergence (fderiv ℝ (modField ρ B) x) = 0 := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ (bhat B)) x :=
    (hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (curlb B) x := curlCLM.differentiableAt.comp x hdd
  rw [show modField ρ B = B + ρ • curlb B from rfl,
    (hB.hasFDerivAt.add (hc.hasFDerivAt.const_smul ρ)).fderiv]
  have hlin : ∀ L M : Space →L[ℝ] Space, divergence (L + ρ • M) =
      divergence L + ρ * divergence M := fun L M => by
    simp [divergence, map_add, map_smul]
  rw [hlin, hdiv, show curlb B = fun y => curl (fderiv ℝ (bhat B) y) from rfl,
    divergence_curl hb]
  ring

/-! ### Time change: from `dX/dt = λ V(X)` to a field line of `V` -/

/-- **Time change.** If `dX/dt = λ(t) V(X(t))` with `λ > 0`, and `S' = λ` with `S` onto `ℝ`, then
`X = γ ∘ S` for a two-sided field line `γ` of `V`. (For `λ < 0` apply this to `−λ`, `−V`.) -/
theorem isFieldLine_of_timeChange {V : Space → Space} {X : ℝ → Space} {S lam : ℝ → ℝ}
    (hS : ∀ t, HasDerivAt S (lam t) t) (hpos : ∀ t, 0 < lam t) (hsurj : Function.Surjective S)
    (hX : ∀ t, HasDerivAt X (lam t • V (X t)) t) :
    ∃ γ : ℝ → Space, IsFieldLine V γ ∧ ∀ t, X t = γ (S t) := by
  have hmono : StrictMono S :=
    strictMono_of_deriv_pos fun t => (hS t).deriv ▸ hpos t
  set e := StrictMono.orderIsoOfSurjective S hmono hsurj
  have he : ∀ t, e t = S t := fun t => rfl
  refine ⟨X ∘ e.symm, ?_, fun t => ?_⟩
  · intro s
    have hinv : HasDerivAt e.symm (lam (e.symm s))⁻¹ s :=
      HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
        (hS (e.symm s)) (hpos _).ne' (Eventually.of_forall fun y => by
          rw [← he]; exact e.apply_symm_apply y)
    have := (hX (e.symm s)).scomp s hinv
    rwa [smul_smul, inv_mul_cancel₀ (hpos _).ne', one_smul] at this
  · simp only [Function.comp_apply, ← he, OrderIso.symm_apply_apply]

/-- Time change with a continuous rate bounded below, `λ ≥ c > 0`: `X = γ ∘ S` for a field line `γ`
of `V`, with `S(0) = 0` (so `γ(0) = X(0)`). -/
theorem isFieldLine_of_rate_ge {V : Space → Space} {X : ℝ → Space} {lam : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hcont : Continuous lam) (hge : ∀ t, c ≤ lam t)
    (hX : ∀ t, HasDerivAt X (lam t • V (X t)) t) :
    ∃ (γ : ℝ → Space) (S : ℝ → ℝ), IsFieldLine V γ ∧ S 0 = 0 ∧ ∀ t, X t = γ (S t) := by
  set S : ℝ → ℝ := fun t => ∫ τ in (0 : ℝ)..t, lam τ
  have hS : ∀ t, HasDerivAt S (lam t) t := fun t =>
    (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hSc : Continuous S := continuous_iff_continuousAt.2 fun t => (hS t).continuousAt
  -- `S t - c t` is monotone, so `S` grows at least linearly in both directions.
  have hmon : Monotone fun t => S t - c * t := by
    have hd : ∀ t, HasDerivAt (fun t => S t - c * t) (lam t - c) t := fun t => by
      exact (hS t).sub (((hasDerivAt_id' t).const_mul c).congr_deriv (mul_one c))
    exact monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
      fun t => (hd t).deriv ▸ sub_nonneg.2 (hge t)
  have hS0 : S 0 = 0 := by simp [S]
  have hup : ∀ t, 0 ≤ t → c * t ≤ S t := fun t ht => by
    have := hmon ht; simp only [hS0] at this; linarith
  have hlo : ∀ t, t ≤ 0 → S t ≤ c * t := fun t ht => by
    have := hmon ht; simp only [hS0] at this; linarith
  have hsurj : Function.Surjective S := by
    refine hSc.surjective ?_ ?_
    · refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hc)
      filter_upwards [eventually_ge_atTop 0] with t ht using hup t ht
    · refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hc)
      filter_upwards [eventually_le_atBot 0] with t ht using hlo t ht
  obtain ⟨γ, hγ, hXγ⟩ := isFieldLine_of_timeChange hS (fun t => hc.trans_le (hge t)) hsurj hX
  exact ⟨γ, S, hγ, hS0, hXγ⟩

/-! ### Passing guiding centres are field lines of `B̃` -/

/-- **`μ = 0` guiding centres are reparametrized field lines of `B̃ = B + ρ_s ∇×b`**,
`ρ_s = m v_∥/q`, provided `t ↦ B*_∥(X(t))` is continuous and the rate `v_∥/B*_∥` is bounded
below by `c > 0` (e.g. `v_∥ > 0` and `0 < B*_∥ ≤ K`). -/
theorem littlejohn_mu0_isFieldLine {m q : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    {c : ℝ} (h : LittlejohnOrbit m q 0 B X v) (hc : 0 < c)
    (hcont : Continuous fun t => BstarPar m q B (v 0) (X t))
    (hge : ∀ t, c ≤ v 0 / BstarPar m q B (v 0) (X t)) :
    ∃ (γ : ℝ → Space) (S : ℝ → ℝ), IsFieldLine (modField (m * v 0 / q) B) γ ∧ S 0 = 0 ∧
      ∀ t, X t = γ (S t) := by
  have hne : ∀ t, BstarPar m q B (v 0) (X t) ≠ 0 := fun t hz => by
    have := hge t; rw [hz, div_zero] at this; linarith
  exact isFieldLine_of_rate_ge hc (continuous_const.div hcont hne) hge (velocity_eq_modField h)

/-- Negative-rate version (`v_∥/B*_∥ ≤ −c < 0`): the orbit is a reparametrized field line of
`−B̃`. -/
theorem littlejohn_mu0_isFieldLine_neg {m q : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} {c : ℝ} (h : LittlejohnOrbit m q 0 B X v) (hc : 0 < c)
    (hcont : Continuous fun t => BstarPar m q B (v 0) (X t))
    (hle : ∀ t, v 0 / BstarPar m q B (v 0) (X t) ≤ -c) :
    ∃ (γ : ℝ → Space) (S : ℝ → ℝ), IsFieldLine (fun x => -modField (m * v 0 / q) B x) γ ∧
      S 0 = 0 ∧ ∀ t, X t = γ (S t) := by
  have hne : ∀ t, BstarPar m q B (v 0) (X t) ≠ 0 := fun t hz => by
    have := hle t; rw [hz, div_zero] at this; linarith
  refine isFieldLine_of_rate_ge (lam := fun t => -(v 0 / BstarPar m q B (v 0) (X t))) hc
    (continuous_const.div hcont hne).neg (fun t => by linarith [hle t]) fun t => ?_
  simpa [neg_smul, smul_neg] using velocity_eq_modField h t

/-- **Confinement transfer.** If every field line of `B̃ = B + ρ_s ∇×b` starting in `Ω` stays in
`Ω` for all time, then so does every `μ = 0` guiding centre satisfying the hypotheses of
`littlejohn_mu0_isFieldLine`. -/
theorem littlejohn_mu0_confined {m q : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    {c : ℝ} {Ω : Set Space} (h : LittlejohnOrbit m q 0 B X v) (hc : 0 < c)
    (hcont : Continuous fun t => BstarPar m q B (v 0) (X t))
    (hge : ∀ t, c ≤ v 0 / BstarPar m q B (v 0) (X t))
    (hconf : ∀ γ : ℝ → Space, IsFieldLine (modField (m * v 0 / q) B) γ → γ 0 ∈ Ω → ∀ s, γ s ∈ Ω)
    (h0 : X 0 ∈ Ω) (t : ℝ) : X t ∈ Ω := by
  obtain ⟨γ, S, hγ, hS0, hXγ⟩ := littlejohn_mu0_isFieldLine h hc hcont hge
  rw [hXγ]
  exact hconf γ hγ (by rw [← hS0, ← hXγ]; exact h0) (S t)

/-! ### Sanity checks -/

/-- `ρ_s = 0` recovers the magnetic field: `B̃ = B`. -/
theorem modField_zero (B : Space → Space) : modField 0 B = B := by
  funext x; simp [modField]

/-- With `ρ_s = 0`, field lines of `B̃` are exactly field lines of `B`. -/
theorem isFieldLine_modField_zero (B : Space → Space) (γ : ℝ → Space) :
    IsFieldLine (modField 0 B) γ ↔ IsFieldLine B γ := by
  rw [modField_zero]

/-- A uniform field has `∇ × b = 0`. -/
theorem curlb_const (B₀ : Space) (x : Space) : curlb (fun _ => B₀) x = 0 := by
  have : bhat (fun _ : Space => B₀) = fun _ => ‖B₀‖⁻¹ • B₀ := rfl
  simp [curlb, this, curl]

/-- In a uniform field, `B̃ = B` for every `ρ`. -/
theorem modField_const (ρ : ℝ) (B₀ : Space) : modField ρ (fun _ => B₀) = fun _ => B₀ := by
  funext x; simp [modField, curlb_const]

/-- In a uniform nonzero field, `B*_∥ = |B₀|`. -/
theorem BstarPar_const (m q v : ℝ) {B₀ : Space} (hB : B₀ ≠ 0) (x : Space) :
    BstarPar m q (fun _ => B₀) v x = ‖B₀‖ := by
  have hn : ‖B₀‖ ≠ 0 := norm_ne_zero_iff.2 hB
  simp only [BstarPar, Bstar, curlb_const, smul_zero, add_zero, bhat, inner_smul_left,
    real_inner_self_eq_norm_sq]
  field_simp
  simp [hn]

/-- **Non-vacuity.** In a uniform nonzero field `B₀`, `X(t) = X₀ + t v₀ b`, `v_∥ ≡ v₀` is a
Littlejohn orbit for every `m, q, μ`. -/
theorem uniform_orbit (m q μ v₀ : ℝ) {B₀ : Space} (hB : B₀ ≠ 0) (X₀ : Space) :
    LittlejohnOrbit m q μ (fun _ => B₀) (fun t => X₀ + (t * v₀) • (‖B₀‖⁻¹ • B₀))
      (fun _ => v₀) := by
  have hg : ∀ x, gradAbsB (fun _ : Space => B₀) x = 0 := fun x => by
    simp [gradAbsB]
  have hx : ∀ u, cross u 0 = 0 := fun u => by simp [cross]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have := (((hasDerivAt_id' t).mul_const v₀).smul_const (‖B₀‖⁻¹ • B₀)).const_add X₀
    convert this using 1
    rw [BstarPar_const _ _ _ hB, hg, hx]
    simp only [Bstar, curlb_const, smul_zero, add_zero, smul_smul, one_mul]
    rw [mul_comm]
  · simp only [hg, inner_zero_right, mul_zero]
    exact hasDerivAt_const t v₀

/-- In a uniform field the guiding-centre orbit is a field line of `B̃ = B` after the time change
`s = v₀ t/|B₀|` (explicit check of `velocity_eq_modField`). -/
theorem uniform_velocity (m q v₀ : ℝ) {B₀ : Space} (hB : B₀ ≠ 0) (X₀ : Space) (t : ℝ) :
    HasDerivAt (fun t => X₀ + (t * v₀) • (‖B₀‖⁻¹ • B₀))
      ((v₀ / ‖B₀‖) • modField (m * v₀ / q) (fun _ => B₀) (X₀ + (t * v₀) • (‖B₀‖⁻¹ • B₀))) t := by
  have := velocity_eq_modField (uniform_orbit m q 0 v₀ hB X₀) t
  simpa [BstarPar_const _ _ _ hB] using this

end PlasmaLean.Kinetic.GCLittlejohn
