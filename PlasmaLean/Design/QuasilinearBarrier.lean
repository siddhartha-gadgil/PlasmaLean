/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.TransportBarrier
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity
public import PlasmaLean.Certificates.KernelFact

/-!
# A two-sided transport band with temperature-dependent diffusivity (kernel change K2)

Labels: *idealized geometry* (the M2 cylinder of `Design.TransportBarrier`), *synthetic
reactor-scale data*, Bosch–Hale reactivity as *supplied data* (`BoschHaleDT`), quasilinear
transport law *supplied* (a rational stand-in for gyro-Bohm scaling).

## Model

Same cylinder, plasma, sources and edge as rung M2 (`TransportBarrier.cylCoeffs`: `a = 5/2 m`,
`R₀ = 13/2 m`, `ψ = r²/a²`, `n = 10²⁰ m⁻³`, `Z_eff = 1.7`, auxiliary heating `≈ 70 MW`), but the
diffusivity now increases with the temperature:

  `χ(T) = χ₀ χ̂(T)`, `χ̂(T) = 1/10 + T²/100` (`chiHat`, `T` in keV),

a rational stand-in for the gyro-Bohm-like law `χ₀ (1/10 + (T/10)^{3/2})` of
`notes/theory/transport-mhd-coupling.md` (they agree at `T = 10 keV`; the loss exponent
`δ = 1 + T χ̂'/χ̂` is `2.9` at `15 keV`). The certificates below are for this `T²` stand-in
**only**: it is stiffer than `T^{3/2}` above `10 keV`, and no statement about the gyro-Bohm law
itself is made. Then `D(ψ,T) = 4χ₀ψ χ̂(T)/a²`,
`∂ψD = 4χ₀χ̂(T)/a²`, `∂TD = 4χ₀ψ (T/50)/a²` (`qcylCoeffs`, a genuinely quasilinear kernel
instance, `qcylCoeffs_transportLaws`, `qcylCoeffs_not_semilinear`).

## The Kirchhoff transform

With `Φ(T) = ∫₀ᵀ χ̂ = T/10 + T³/300` (`kirchhoff`), the flux is `ψ χ̂(T) T' = ψ Φ(T)'`, so the
conduction term is linear in `Φ(T)`. For a polynomial `F` the profile `T = Φ⁻¹ ∘ F`
(`kProf`, with `Φ⁻¹` the order isomorphism `kirchhoffInv`) is smooth (`kProf_regular`) and

  `N[Φ⁻¹ ∘ F] = (4χ₀/a²)(ψ F'' + F') + R(ψ, Φ⁻¹(F))`  (`qcylCoeffs_op_kProf`):

an exact polynomial conduction term even though the temperature profile is not a polynomial.
This is what makes the barrier certificates cheap: the steep edge layer of `T` (the edge
diffusivity `χ̂(1 keV) = 0.11` is small) is invisible in `F`. The labels of the two-label
checker `pieceCheck2` are levels `Φ(k)`, so `k ≤ T ⇔ Φ(k) ≤ F`.

## Results

* `tsubq_margin`, `tsupq_margin`: for every supplied reactivity and every `χ₀ ∈ [1/2, 4/5]`
  m²/s, `N[T_sub] ≥ 1/20` and `N[T_sup] ≤ −1/20` keV/s on `[0,1]`, from four exact rational
  certificates (`fsub_check_lo/hi`, `fsup_check_lo/hi`: the operator is affine in `χ₀`, so the
  two corners suffice). Lower barrier: Bosch–Hale floors at integer keV, `√T ≤ (K+4)/4` on
  pieces with `T ≤ K`. Upper barrier: Bosch–Hale **ceilings** `⟨σv⟩(T) ≤ ⟨σv⟩(K) ≤ svHi` for
  `1 ≤ T ≤ K ≤ 60` (`sv_le_svCeil`), bremsstrahlung dropped.
* `quasilinear_band` (**two-sided band, rung C2 in the cylinder**): every kernel solution on all
  horizons with edge temperature `T_edge(t) ∈ [1, 3/2]` keV and initial data in the band
  stays in the band `T_sub ≤ T ≤ T_sup` for all time; in particular `T ≥ 10 keV` on the core
  `ψ ≤ 3/10` and `T ≤ 47/2 keV` everywhere. Profiles: `T_sub(0) ≈ 14.2`,
  `T_sub(3/10) ≈ 11.8`, `T_sub(1) = 1`; `T_sup(0) ≈ 23.4`, `T_sup(3/10) ≈ 20.2`,
  `T_sup(1) = 3/2` keV.
* `quasilinear_band_nonempty`: `T_sub ≤ T_sup` on `[0,1]` (the band is not empty).

## The 0-D obstruction is lifted (numerical observation, untrusted oracle `/tmp/k2`)

With fixed `χ` an ordered sub/supersolution pair forces `Q ≤ 5/(γ − 1) ≈ 6` on `[10,15]` keV
(note §3.2, Finding 2). Here the steady states (finite volumes, implicit time marching from a
cold and a hot start, which agree) have `T(0) = 16.3`/`21.7` keV, fusion-alpha power
`P_α ≈ 132`/`235 MW` at `χ₀ = 4/5`/`1/2` with `P_aux ≈ 70 MW`, i.e. `Q = 5P_α/P_aux ≈ 9.5–17`,
and both are bracketed by the certified band. (Not a compiled statement: `P_α` and `Q` are not
formalized here.)

## Honest limitations

* Classical solutions are supplied; existence is not proved. `χ̂` is a rational stand-in,
  `χ₀` is constant in space and time, density and composition are fixed, the geometry is a
  straight cylinder.
* The upper barrier needs `T_edge ≤ 3/2 keV`; the lower barrier `T_edge ≥ 1 keV`.
* No transport–MHD coupling here (that is `solovev_one_plasma`, still open); this module
  supplies the two-sided band technique for it.
-/

public section

noncomputable section

namespace PlasmaLean.Design.QuasilinearBarrier

open Set Filter Topology PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates
  PlasmaLean.Design.TransportBarrier

/-! ### The temperature-dependent diffusivity and its Kirchhoff transform -/

/-- Normalized diffusivity `χ̂(T) = 1/10 + T²/100` (`T` in keV): `χ = χ₀ χ̂(T)`. -/
@[expose] def chiHat (T : ℝ) : ℝ := 1 / 10 + T ^ 2 / 100

/-- `χ̂ > 0`. -/
theorem chiHat_pos (T : ℝ) : 0 < chiHat T := by unfold chiHat; positivity

/-- `χ̂' = T/50`. -/
theorem hasDerivAt_chiHat (T : ℝ) : HasDerivAt chiHat (T / 50) T := by
  have h := ((hasDerivAt_pow 2 T).div_const 100).const_add (1 / 10)
  have e : chiHat = fun x => 1 / 10 + x ^ 2 / 100 := rfl
  rw [e]; convert h using 1; push_cast; ring

/-- `χ̂` is increasing for `T ≥ 0` (sanity: temperature-dependent transport worsens with `T`). -/
theorem chiHat_mono {T T' : ℝ} (h0 : 0 ≤ T) (h : T ≤ T') : chiHat T ≤ chiHat T' := by
  unfold chiHat; nlinarith

/-- Kirchhoff transform `Φ(T) = ∫₀ᵀ χ̂ = T/10 + T³/300`. -/
@[expose] def kirchhoff (T : ℝ) : ℝ := T / 10 + T ^ 3 / 300

/-- The Kirchhoff transform on rationals (used as the level map of the certificates). -/
@[expose] def kirchhoffQ (T : ℚ) : ℚ := T / 10 + T ^ 3 / 300

/-- The rational and real transforms agree. -/
theorem kirchhoffQ_cast (T : ℚ) : ((kirchhoffQ T : ℚ) : ℝ) = kirchhoff T := by
  simp [kirchhoffQ, kirchhoff]

/-- `Φ' = χ̂`. -/
theorem hasDerivAt_kirchhoff (T : ℝ) : HasDerivAt kirchhoff (chiHat T) T := by
  have h := ((hasDerivAt_id' T).div_const 10).add ((hasDerivAt_pow 3 T).div_const 300)
  have e : kirchhoff = fun x => x / 10 + x ^ 3 / 300 := rfl
  rw [e]; convert h using 1; unfold chiHat; push_cast; ring

/-- `Φ` is strictly increasing. -/
theorem kirchhoff_strictMono : StrictMono kirchhoff := fun a b hab => by
  unfold kirchhoff
  nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, mul_pos (sub_pos.2 hab)
    (show (0 : ℝ) < 30 + a ^ 2 + a * b + b ^ 2 by nlinarith [sq_nonneg (a + b)])]

/-- `Φ` is continuous. -/
theorem kirchhoff_continuous : Continuous kirchhoff := by unfold kirchhoff; fun_prop

/-- `Φ` is surjective (continuous, tending to `±∞`). -/
theorem kirchhoff_surjective : Function.Surjective kirchhoff := by
  refine kirchhoff_continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 10))
    filter_upwards [eventually_ge_atTop 0] with T hT
    unfold kirchhoff; simp only [id]; have := pow_nonneg hT 3; linarith
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_id.atBot_div_const (by norm_num : (0 : ℝ) < 10))
    filter_upwards [eventually_le_atBot 0] with T hT
    unfold kirchhoff; simp only [id]
    nlinarith [pow_two_nonneg T, mul_nonpos_of_nonneg_of_nonpos (pow_two_nonneg T) hT]

/-- `Φ` as an order isomorphism of `ℝ`. -/
@[expose] def kirchhoffIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective kirchhoff kirchhoff_strictMono kirchhoff_surjective

/-- The inverse Kirchhoff transform `Φ⁻¹`. -/
@[expose] def kirchhoffInv (F : ℝ) : ℝ := kirchhoffIso.symm F

/-- `Φ(Φ⁻¹ F) = F`. -/
theorem kirchhoff_kirchhoffInv (F : ℝ) : kirchhoff (kirchhoffInv F) = F :=
  StrictMono.orderIsoOfSurjective_self_symm_apply kirchhoff kirchhoff_strictMono
    kirchhoff_surjective F

/-- `Φ⁻¹(Φ T) = T`. -/
theorem kirchhoffInv_kirchhoff (T : ℝ) : kirchhoffInv (kirchhoff T) = T :=
  StrictMono.orderIsoOfSurjective_symm_apply_self kirchhoff kirchhoff_strictMono
    kirchhoff_surjective T

/-- `Φ⁻¹` is continuous. -/
theorem kirchhoffInv_continuous : Continuous kirchhoffInv := kirchhoffIso.symm.continuous

/-- Levels: `k ≤ Φ⁻¹(F) ↔ Φ(k) ≤ F`. -/
theorem le_kirchhoffInv_iff {k F : ℝ} : k ≤ kirchhoffInv F ↔ kirchhoff k ≤ F := by
  rw [← kirchhoff_strictMono.le_iff_le, kirchhoff_kirchhoffInv]

/-- Levels: `Φ⁻¹(F) ≤ K ↔ F ≤ Φ(K)`. -/
theorem kirchhoffInv_le_iff {K F : ℝ} : kirchhoffInv F ≤ K ↔ F ≤ kirchhoff K := by
  rw [← kirchhoff_strictMono.le_iff_le, kirchhoff_kirchhoffInv]

/-- `(Φ⁻¹)' = 1/χ̂(Φ⁻¹)` (inverse function theorem in one variable). -/
theorem hasDerivAt_kirchhoffInv (F : ℝ) :
    HasDerivAt kirchhoffInv (chiHat (kirchhoffInv F))⁻¹ F :=
  HasDerivAt.of_local_left_inverse kirchhoffInv_continuous.continuousAt
    (hasDerivAt_kirchhoff (kirchhoffInv F)) (chiHat_pos _).ne'
    (Eventually.of_forall kirchhoff_kirchhoffInv)

/-! ### Kirchhoff profiles -/

/-- The profile `T = Φ⁻¹ ∘ F` of a polynomial level function `F`. -/
@[expose] def kProf (F : List ℚ) (ψ : ℝ) : ℝ := kirchhoffInv (QPoly.eval F ψ)

/-- Its derivative `T' = F'/χ̂(T)`. -/
@[expose] def kProf' (F : List ℚ) (ψ : ℝ) : ℝ :=
  QPoly.eval (QPoly.deriv F) ψ / chiHat (kProf F ψ)

/-- Its second derivative `T'' = (F'' − χ̂'(T) T'²)/χ̂(T)`. -/
@[expose] def kProf'' (F : List ℚ) (ψ : ℝ) : ℝ :=
  (QPoly.eval (QPoly.deriv (QPoly.deriv F)) ψ - kProf F ψ / 50 * kProf' F ψ ^ 2) /
    chiHat (kProf F ψ)

/-- `Φ(T(ψ)) = F(ψ)`. -/
theorem kirchhoff_kProf (F : List ℚ) (ψ : ℝ) : kirchhoff (kProf F ψ) = QPoly.eval F ψ :=
  kirchhoff_kirchhoffInv _

/-- `T` is continuous. -/
theorem kProf_continuous (F : List ℚ) : Continuous (kProf F) :=
  kirchhoffInv_continuous.comp (QPoly.continuous_eval F)

/-- `χ̂(T(ψ))` is continuous. -/
theorem chiHat_kProf_continuous (F : List ℚ) : Continuous fun ψ => chiHat (kProf F ψ) := by
  have := kProf_continuous F
  unfold chiHat; fun_prop

/-- `T'` is continuous. -/
theorem kProf'_continuous (F : List ℚ) : Continuous (kProf' F) :=
  (QPoly.continuous_eval _).div (chiHat_kProf_continuous F) (fun _ => (chiHat_pos _).ne')

/-- `T''` is continuous. -/
theorem kProf''_continuous (F : List ℚ) : Continuous (kProf'' F) := by
  have h1 := kProf_continuous F
  have h2 := kProf'_continuous F
  exact (((QPoly.continuous_eval _).sub ((h1.div_const 50).mul (h2.pow 2)))).div
    (chiHat_kProf_continuous F) (fun _ => (chiHat_pos _).ne')

/-- `T'` is the derivative of `T`. -/
theorem hasDerivAt_kProf (F : List ℚ) (ψ : ℝ) : HasDerivAt (kProf F) (kProf' F ψ) ψ := by
  have h2 : HasDerivAt (fun x => kirchhoffInv (QPoly.eval F x))
      ((chiHat (kirchhoffInv (QPoly.eval F ψ)))⁻¹ * QPoly.eval (QPoly.deriv F) ψ) ψ :=
    (hasDerivAt_kirchhoffInv _).comp ψ (QPoly.hasDerivAt_eval F ψ)
  change HasDerivAt (fun x => kirchhoffInv (QPoly.eval F x)) _ ψ
  convert h2 using 1
  simp only [kProf', kProf]; rw [div_eq_mul_inv, mul_comm]

/-- `T''` is the derivative of `T'`. -/
theorem hasDerivAt_kProf' (F : List ℚ) (ψ : ℝ) : HasDerivAt (kProf' F) (kProf'' F ψ) ψ := by
  have hc : HasDerivAt (fun x => chiHat (kProf F x)) (kProf F ψ / 50 * kProf' F ψ) ψ :=
    (hasDerivAt_chiHat (kProf F ψ)).comp ψ (hasDerivAt_kProf F ψ)
  have h2 := (QPoly.hasDerivAt_eval (QPoly.deriv F) ψ).div hc (chiHat_pos _).ne'
  change HasDerivAt (fun x => QPoly.eval (QPoly.deriv F) x / chiHat (kProf F x)) _ ψ
  convert h2 using 1
  have hne := (chiHat_pos (kProf F ψ)).ne'
  simp only [kProf'', kProf']
  field_simp

/-- Kirchhoff profiles are regular. -/
theorem kProf_regular (F : List ℚ) : ProfileRegular (kProf F) (kProf' F) (kProf'' F) :=
  ⟨fun ψ _ => (hasDerivAt_kProf F ψ).hasDerivWithinAt,
    fun ψ _ => (hasDerivAt_kProf' F ψ).hasDerivWithinAt⟩

/-- An antitone level function gives an antitone profile. -/
theorem kProf_antitoneOn {F : List ℚ} (h : AntitoneOn (QPoly.eval F) (Icc 0 1)) :
    AntitoneOn (kProf F) (Icc 0 1) := fun _ ha _ hb hab =>
  kirchhoffIso.symm.monotone (h ha hb hab)

/-! ### Quasilinear cylinder coefficients -/

/-- **Quasilinear cylinder coefficients** for reactivity `sv` and diffusivity scale `χ₀`:
`V' = 2π²R₀a²`, `V'' = 0`, `D(ψ,T) = 4χ₀ψ χ̂(T)/a²`, `∂ψD = 4χ₀χ̂(T)/a²`,
`∂TD = 4χ₀ψ (T/50)/a²`, `R = netSource sv` posed for `T > 0`, degenerate axis. -/
@[expose] def qcylCoeffs (sv : ℝ → ℝ) (χ₀ : ℝ) : RadialCoefficients where
  Vp := fun _ => volumeDeriv
  dVp := fun _ => 0
  D := fun ψ T => 4 * χ₀ * ψ * chiHat T / minorRadius ^ 2
  dD := fun _ T => 4 * χ₀ * chiHat T / minorRadius ^ 2
  dDT := fun ψ T => 4 * χ₀ * ψ * (T / 50) / minorRadius ^ 2
  R := netSource sv
  Tdom := Ioi 0
  axis := .degenerate

/-- The quasilinear cylinder operator:
`N[T] = (4χ₀/a²)(ψ χ̂(T) T'' + (χ̂(T) + ψ (T/50) T') T') + R`, i.e.
`(4χ₀/a²) ∂ψ(ψ χ̂(T) ∂ψT) + R`. -/
theorem qcylCoeffs_op (sv : ℝ → ℝ) (χ₀ ψ u uψ uψψ : ℝ) :
    (qcylCoeffs sv χ₀).op ψ u uψ uψψ = 4 * χ₀ / minorRadius ^ 2 *
      (ψ * chiHat u * uψψ + (chiHat u + ψ * (u / 50) * uψ) * uψ) + netSource sv ψ u := by
  simp only [RadialCoefficients.op, qcylCoeffs, mul_zero, zero_div, add_zero]; ring

/-- **The quasilinear cylinder is a kernel instance** (K2 laws) for `χ₀ ≥ 0`. -/
theorem qcylCoeffs_transportLaws (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (hχ : 0 ≤ χ₀) :
    TransportLaws (qcylCoeffs sv χ₀) where
  Vp_pos := fun _ _ => volumeDeriv_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  D_deriv := fun ψ _ T => by
    have := (((hasDerivAt_id ψ).const_mul (4 * χ₀)).mul_const (chiHat T)).div_const
      (minorRadius ^ 2)
    convert this.hasDerivWithinAt using 1
    · funext x; simp [qcylCoeffs]
    · simp [qcylCoeffs]
  DT_deriv := fun ψ _ T => by
    have := ((hasDerivAt_chiHat T).const_mul (4 * χ₀ * ψ)).div_const (minorRadius ^ 2)
    convert this using 1
    · funext x; simp [qcylCoeffs]
    · simp [qcylCoeffs]
  D_nonneg := fun ψ hψ T => by
    have := chiHat_pos T; have := hψ.1
    simp only [qcylCoeffs, minorRadius]; positivity
  D_axis := fun _ _ => by simp [qcylCoeffs]
  D_axis_regular := fun h => absurd h (by simp [qcylCoeffs])
  Tdom_open := isOpen_Ioi
  R_cont := netSource_continuousOn sv

/-- For `χ₀ > 0` the coefficients are genuinely quasilinear (not semilinear). -/
theorem qcylCoeffs_not_semilinear (sv : ℝ → ℝ) {χ₀ : ℝ} (hχ : 0 < χ₀) :
    ¬ (qcylCoeffs sv χ₀).IsSemilinear := fun h => by
  have := (h 1 ⟨zero_le_one, le_rfl⟩ 0 10).1
  simp only [qcylCoeffs, chiHat, minorRadius] at this
  norm_num at this
  linarith

/-- **Kirchhoff form of the operator.** On a Kirchhoff profile `T = Φ⁻¹ ∘ F`,
`N[T] = (4χ₀/a²)(ψ F'' + F') + R(ψ, T)`. -/
theorem qcylCoeffs_op_kProf (sv : ℝ → ℝ) (χ₀ : ℝ) (F : List ℚ) (ψ : ℝ) :
    (qcylCoeffs sv χ₀).op ψ (kProf F ψ) (kProf' F ψ) (kProf'' F ψ) =
      4 * χ₀ / minorRadius ^ 2 * (ψ * QPoly.eval (QPoly.deriv (QPoly.deriv F)) ψ +
        QPoly.eval (QPoly.deriv F) ψ) + netSource sv ψ (kProf F ψ) := by
  rw [qcylCoeffs_op]
  have hne := (chiHat_pos (kProf F ψ)).ne'
  unfold kProf'' kProf'
  congr 2
  field_simp
  ring

/-- **Shift control along Kirchhoff profiles** (needed by the margin theorems for quasilinear
coefficients): the operator along `Φ⁻¹ ∘ F` is jointly continuous in `(ψ,T)` on
`[0,1] × (0,∞)`. -/
theorem qcyl_opShiftControl (sv : ℝ → ℝ) [BoschHaleDT sv] (χ₀ : ℝ) (F : List ℚ)
    (hpos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < kProf F ψ) :
    OpShiftControl (qcylCoeffs sv χ₀) (kProf F) (kProf' F) (kProf'' F) := by
  refine opShiftControl_of_continuousOn (kProf_continuous F).continuousOn isOpen_Ioi hpos ?_
  have h1 := kProf'_continuous F
  have h2 := kProf''_continuous F
  have hA : Continuous fun p : ℝ × ℝ => 4 * χ₀ / minorRadius ^ 2 *
      (p.1 * chiHat p.2 * kProf'' F p.1 + (chiHat p.2 + p.1 * (p.2 / 50) * kProf' F p.1) *
        kProf' F p.1) := by
    unfold chiHat; fun_prop
  refine (hA.continuousOn.add (netSource_continuousOn sv)).congr (fun p _ => ?_)
  simp only [qcylCoeffs_op]; rfl

/-! ### Reactivity ceilings -/

/-- Reactivity ceiling for the label `K` (keV): the upper enclosure `svHi` of the Bosch–Hale
window ending at `K`, or `0` if there is none. -/
@[expose] def svCeil (K : ℚ) : ℚ :=
  match boschHaleWindows.find? (fun w => w.hi == K) with
  | some w => w.svHi
  | none => 0

/-- **Reactivity ceiling.** If a window ends at `K ≤ 60` and `1 ≤ T ≤ K`, then
`⟨σv⟩(T) ≤ svCeil K`: `⟨σv⟩` is increasing on `[1,60]` and the window bounds `⟨σv⟩(K)`. -/
theorem sv_le_svCeil (sv : ℝ → ℝ) [BoschHaleDT sv] {K : ℚ}
    (hK : (boschHaleWindows.find? (fun w => w.hi == K)).isSome = true) (hK60 : K ≤ 60)
    {T : ℝ} (h1 : 1 ≤ T) (hTK : T ≤ K) : sv T ≤ (svCeil K : ℝ) := by
  unfold svCeil
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hK
  rw [hw]
  have hmem := List.mem_of_find?_eq_some hw
  have hhi : w.hi = K := by simpa using List.find?_some hw
  have hwf := List.all_eq_true.1 boschHaleWindows_wf w hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hlo : (1 : ℝ) ≤ w.lo := by exact_mod_cast hwf.1
  have hlohi : (w.lo : ℝ) ≤ w.hi := by exact_mod_cast hwf.2
  have hK' : (K : ℝ) ≤ 60 := by exact_mod_cast hK60
  have hwK := (BoschHaleDT.windows (sv := sv) w hmem (K : ℝ) (by rw [← hhi]; exact hlohi)
    (by rw [hhi])).2
  have hmono := BoschHaleDT.monotoneOn (sv := sv) ⟨h1, hTK.trans hK'⟩
    ⟨h1.trans hTK, hK'⟩ hTK
  linarith

/-! ### Certificates -/

/-- `ψ F'' + F'` as a polynomial (the Kirchhoff conduction bracket). -/
@[expose] def condPoly (F : List ℚ) : List ℚ :=
  QPoly.add (QPoly.mul [0, 1] (QPoly.deriv (QPoly.deriv F))) (QPoly.deriv F)

/-- Evaluation of the conduction bracket. -/
theorem condPoly_eval (F : List ℚ) (ψ : ℝ) : QPoly.eval (condPoly F) ψ =
    ψ * QPoly.eval (QPoly.deriv (QPoly.deriv F)) ψ + QPoly.eval (QPoly.deriv F) ψ := by
  simp [condPoly]

/-- Lower-barrier polynomial at diffusivity `χ`: `(16χ/25)(ψF'' + F') + q_aux` (alpha heating
and bremsstrahlung enter through the bonus). -/
@[expose] def lowQ (F : List ℚ) (χ : ℚ) : List ℚ :=
  QPoly.add (QPoly.scale (16 * χ / 25) (condPoly F)) auxRateCoeffs

/-- Upper-barrier polynomial at diffusivity `χ`: `−(16χ/25)(ψF'' + F') − q_aux`. -/
@[expose] def upQ (F : List ℚ) (χ : ℚ) : List ℚ := QPoly.scale (-1) (lowQ F χ)

/-- Lower-barrier bonus: alpha floor at `k` minus the bremsstrahlung bound `0.201 (K+4)/4`. -/
@[expose] def lowBonus (k K : ℚ) : ℚ :=
  229 / 10 * 10 ^ 21 * svFloor k - 201 / 1000 * ((K + 4) / 4)

/-- Upper-barrier bonus: minus the alpha ceiling `2.291·10²² · svCeil K`. -/
@[expose] def upBonus (_k K : ℚ) : ℚ := -(2291 / 100 * 10 ^ 21 * svCeil K)

/-- Level function of the lower barrier, `F_sub = Φ(T_sub)` (Python oracle: least-squares fit
of `Φ` of a steady state of a source-reduced problem at `χ₀ = 4/5`; untrusted). -/
@[expose] def fsubCoeffs : List ℚ :=
  [8269039/750000, -7857583/1000000, -12912793/200000, 15046197/62500, -482921161/1000000,
   648132107/1000000, -124281249/200000, 218224459/500000, -220078689/1000000, 17971123/250000,
   -5649539/500000]

/-- Level function of the upper barrier, `F_sup = Φ(T_sup)` (oracle: steady state of a
source-increased problem at `χ₀ = 1/2`, edge `3/2 keV`; untrusted). -/
@[expose] def fsupCoeffs : List ℚ :=
  [45243813/1000000, -41760869/1000000, -102245869/1000000, 383682051/1000000, -155353719/200000,
   67111531/62500, -546922777/500000, 425772149/500000, -490964039/1000000, 5750659/31250,
   -3252957/100000]

/-- Pieces `(right end, lower label k, upper label K)` of the lower-barrier certificate. -/
@[expose] def subPieces : List (ℚ × ℚ × ℚ) :=
  [(461/10000, 14, 57/4), (217/1250, 13, 281/20), (2791/10000, 12, 261/20),
   (3799/10000, 11, 241/20), (2391/5000, 10, 221/20), (5727/10000, 9, 201/20),
   (661/1000, 8, 181/20), (7409/10000, 7, 161/20), (1621/2000, 6, 141/20), (4343/5000, 5, 121/20),
   (9153/10000, 4, 101/20), (9203/10000, 3, 81/20), (2313/2500, 3, 39/10), (93/100, 3, 19/5),
   (1869/2000, 3, 73/20), (939/1000, 3, 71/20), (1179/1250, 3, 17/5), (4737/5000, 3, 33/10),
   (4757/5000, 3, 63/20), (597/625, 2, 61/20), (9589/10000, 2, 29/10), (77/80, 2, 14/5),
   (483/500, 2, 53/20), (9693/10000, 2, 51/20), (4863/5000, 2, 12/5), (9757/10000, 2, 23/10),
   (9787/10000, 2, 43/20), (9817/10000, 1, 41/20), (1969/2000, 1, 19/10), (9873/10000, 1, 9/5),
   (9899/10000, 1, 33/20), (397/400, 1, 31/20), (9951/10000, 1, 7/5), (399/400, 1, 13/10),
   (1, 1, 23/20)]

/-- Pieces of the upper-barrier certificate (upper labels end Bosch–Hale windows). -/
@[expose] def supPieces : List (ℚ × ℚ × ℚ) :=
  [(259/5000, 22, 24), (1493/10000, 21, 23), (1179/5000, 20, 22), (317/1000, 19, 21),
   (493/1250, 18, 20), (4677/10000, 17, 19), (671/1250, 16, 18), (6011/10000, 15, 17),
   (1651/2500, 14, 16), (893/1250, 13, 15), (477/625, 12, 14), (4033/5000, 11, 13),
   (8449/10000, 10, 12), (439/500, 9, 11), (9063/10000, 8, 10), (9299/10000, 7, 9),
   (4747/5000, 6, 8), (9649/10000, 5, 7), (977/1000, 4, 6), (4931/5000, 3, 5), (993/1000, 2, 4),
   (499/500, 1, 3), (1, 1, 2)]

/-- The lower barrier `T_sub = Φ⁻¹ ∘ F_sub` (keV). -/
@[expose] def Tsubq (ψ : ℝ) : ℝ := kProf fsubCoeffs ψ

/-- The upper barrier `T_sup = Φ⁻¹ ∘ F_sup` (keV). -/
@[expose] def Tsupq (ψ : ℝ) : ℝ := kProf fsupCoeffs ψ

/-- Certificate: lower barrier at `χ₀ = 1/2` (35 pieces). -/
theorem fsub_check_lo :
    pieceCheck2 (lowQ fsubCoeffs (1 / 2)) fsubCoeffs kirchhoffQ (1 / 20) lowBonus 0 subPieces
      = true := by
  kernel_fact

/-- Certificate: lower barrier at `χ₀ = 4/5`. -/
theorem fsub_check_hi :
    pieceCheck2 (lowQ fsubCoeffs (4 / 5)) fsubCoeffs kirchhoffQ (1 / 20) lowBonus 0 subPieces
      = true := by
  kernel_fact

/-- Certificate: upper barrier at `χ₀ = 1/2` (23 pieces). -/
theorem fsup_check_lo :
    pieceCheck2 (upQ fsupCoeffs (1 / 2)) fsupCoeffs kirchhoffQ (1 / 20) upBonus 0 supPieces
      = true := by
  kernel_fact

/-- Certificate: upper barrier at `χ₀ = 4/5`. -/
theorem fsup_check_hi :
    pieceCheck2 (upQ fsupCoeffs (4 / 5)) fsupCoeffs kirchhoffQ (1 / 20) upBonus 0 supPieces
      = true := by
  kernel_fact

/-- Grid with `n` equal steps on `[0,1]`. -/
@[expose] def gridN (n : ℕ) : List ℚ := (List.range n).map (fun i : ℕ => ((i : ℚ) + 1) / n)

/-- Monotonicity certificate: `−F_sub' ≥ 0` on `[0,1]`. -/
theorem fsub_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv fsubCoeffs)) 0 0 1 (gridN 8) = true := by
  kernel_fact

/-- Monotonicity certificate: `−F_sup' ≥ 0` on `[0,1]`. -/
theorem fsup_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv fsupCoeffs)) 0 0 1 (gridN 8) = true := by
  kernel_fact

/-- Ordering certificate: `F_sup − F_sub ≥ 0` on `[0,1]`. -/
theorem gap_check :
    QPoly.checkOn (QPoly.add fsupCoeffs (QPoly.scale (-1) fsubCoeffs)) 0 0 1 (gridN 16)
      = true := by
  kernel_fact

/-- Label and endpoint facts, checked once: lower labels `k ≥ 0`; upper labels end a window
and are `≤ 60`; both piece lists end at `1`; `F_sub(1) = Φ(1)`, `F_sup(1) = Φ(3/2)`,
`F_sub(0) ≤ Φ(60)`, `Φ(10) ≤ F_sub(3/10)`, `F_sup(0) ≤ Φ(47/2)`. -/
theorem labels_check :
    (subPieces.all (fun p => decide (0 ≤ p.2.1)) &&
      supPieces.all (fun p => (boschHaleWindows.find? (fun w => w.hi == p.2.2)).isSome &&
        decide (p.2.2 ≤ 60)) &&
      decide (pieceEnd2 0 subPieces = 1) && decide (pieceEnd2 0 supPieces = 1) &&
      decide (QPoly.evalQ fsubCoeffs 1 = kirchhoffQ 1) &&
      decide (QPoly.evalQ fsupCoeffs 1 = kirchhoffQ (3 / 2)) &&
      decide (QPoly.evalQ fsubCoeffs 0 ≤ kirchhoffQ 60) &&
      decide (kirchhoffQ 10 ≤ QPoly.evalQ fsubCoeffs (3 / 10)) &&
      decide (QPoly.evalQ fsupCoeffs 0 ≤ kirchhoffQ (47 / 2))) = true := by
  kernel_fact

/-! ### Consequences of the certificates -/

/-- Unpacked label and endpoint facts. -/
theorem labels_facts :
    (∀ p ∈ subPieces, 0 ≤ p.2.1) ∧
      (∀ p ∈ supPieces, (boschHaleWindows.find? (fun w => w.hi == p.2.2)).isSome = true ∧
        p.2.2 ≤ 60) ∧
      pieceEnd2 0 subPieces = 1 ∧ pieceEnd2 0 supPieces = 1 ∧
      QPoly.evalQ fsubCoeffs 1 = kirchhoffQ 1 ∧ QPoly.evalQ fsupCoeffs 1 = kirchhoffQ (3 / 2) ∧
      QPoly.evalQ fsubCoeffs 0 ≤ kirchhoffQ 60 ∧
      kirchhoffQ 10 ≤ QPoly.evalQ fsubCoeffs (3 / 10) ∧
      QPoly.evalQ fsupCoeffs 0 ≤ kirchhoffQ (47 / 2) := by
  have h := labels_check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, fun p hp => h2 p hp, h3, h4, h5, h6, h7, h8, h9⟩

/-- Real evaluation at a rational point. -/
theorem eval_ratCast (F : List ℚ) (q : ℚ) : QPoly.eval F (q : ℝ) = (QPoly.evalQ F q : ℝ) :=
  QPoly.eval_cast F q

/-- `F_sub` is antitone on `[0,1]`. -/
theorem fsub_antitone : AntitoneOn (QPoly.eval fsubCoeffs) (Icc 0 1) := by
  have := antitoneOn_eval_of_check fsub_deriv_check
  intro a ha b hb hab; exact this (by simpa using ha) (by simpa using hb) hab

/-- `F_sup` is antitone on `[0,1]`. -/
theorem fsup_antitone : AntitoneOn (QPoly.eval fsupCoeffs) (Icc 0 1) := by
  have := antitoneOn_eval_of_check fsup_deriv_check
  intro a ha b hb hab; exact this (by simpa using ha) (by simpa using hb) hab

/-- Edge and axis values of the barriers: `T_sub(1) = 1`, `T_sup(1) = 3/2`. -/
theorem barrier_edges : Tsubq 1 = 1 ∧ Tsupq 1 = 3 / 2 := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := labels_facts
  constructor
  · have : QPoly.eval fsubCoeffs ((1 : ℚ) : ℝ) = kirchhoff ((1 : ℚ) : ℝ) := by
      rw [eval_ratCast, h5, kirchhoffQ_cast]
    simp only [Tsubq, kProf]; push_cast at this; rw [this, kirchhoffInv_kirchhoff]
  · have : QPoly.eval fsupCoeffs ((1 : ℚ) : ℝ) = kirchhoff ((3 / 2 : ℚ) : ℝ) := by
      rw [eval_ratCast, h6, kirchhoffQ_cast]
    simp only [Tsupq, kProf]; push_cast at this; rw [this, kirchhoffInv_kirchhoff]

/-- `1 ≤ T_sub ≤ 60` on `[0,1]`. -/
theorem tsubq_bounds {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : 1 ≤ Tsubq ψ ∧ Tsubq ψ ≤ 60 := by
  obtain ⟨-, -, -, -, h5, -, h7, -⟩ := labels_facts
  have hm1 := fsub_antitone hψ ⟨zero_le_one, le_rfl⟩ hψ.2
  have hm0 := fsub_antitone ⟨le_rfl, zero_le_one⟩ hψ hψ.1
  rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, eval_ratCast, h5, kirchhoffQ_cast] at hm1
  rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm0
  have h7' : ((QPoly.evalQ fsubCoeffs 0 : ℚ) : ℝ) ≤ kirchhoff 60 := by
    rw [← show ((60 : ℚ) : ℝ) = 60 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h7
  refine ⟨le_kirchhoffInv_iff.2 (by simpa using hm1), kirchhoffInv_le_iff.2 (hm0.trans h7')⟩

/-- `1 ≤ T_sup ≤ 47/2` on `[0,1]`. -/
theorem tsupq_bounds {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : 1 ≤ Tsupq ψ ∧ Tsupq ψ ≤ 47 / 2 := by
  obtain ⟨-, -, -, -, -, h6, -, -, h9⟩ := labels_facts
  have hm1 := fsup_antitone hψ ⟨zero_le_one, le_rfl⟩ hψ.2
  have hm0 := fsup_antitone ⟨le_rfl, zero_le_one⟩ hψ hψ.1
  rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, eval_ratCast, h6, kirchhoffQ_cast] at hm1
  rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm0
  have h9' : ((QPoly.evalQ fsupCoeffs 0 : ℚ) : ℝ) ≤ kirchhoff (47 / 2) := by
    rw [← show ((47 / 2 : ℚ) : ℝ) = 47 / 2 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h9
  refine ⟨?_, kirchhoffInv_le_iff.2 (hm0.trans h9')⟩
  have : (1 : ℝ) ≤ 3 / 2 := by norm_num
  exact this.trans (le_kirchhoffInv_iff.2 (by push_cast at hm1; exact hm1))

/-- **Core temperature.** `T_sub ≥ 10 keV` on `ψ ≤ 3/10`. -/
theorem tsubq_core {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 3 / 10) : 10 ≤ Tsubq ψ := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := labels_facts
  have hm := fsub_antitone ⟨h0, h1.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ h1
  rw [show ((3 : ℝ) / 10) = ((3 / 10 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm
  have h8' : kirchhoff 10 ≤ ((QPoly.evalQ fsubCoeffs (3 / 10) : ℚ) : ℝ) := by
    rw [← show ((10 : ℚ) : ℝ) = 10 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h8
  exact le_kirchhoffInv_iff.2 (h8'.trans hm)

/-- Sanity: the band is not empty, `T_sub ≤ T_sup` on `[0,1]`. -/
theorem quasilinear_band_nonempty {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : Tsubq ψ ≤ Tsupq ψ := by
  have := QPoly.checkOn_sound gap_check ψ (by simpa using hψ)
  simp only [QPoly.eval_add, QPoly.eval_scale] at this
  push_cast at this
  exact kirchhoffIso.symm.monotone (by linarith)

/-- Piece soundness specialized to the barriers: at every `ψ ∈ [0,1]` the certificate gives
labels with `k ≤ T ≤ K` and the polynomial inequality. -/
theorem piece_at {Q F : List ℚ} {bonus : ℚ → ℚ → ℚ} {ps : List (ℚ × ℚ × ℚ)}
    (hc : pieceCheck2 Q F kirchhoffQ (1 / 20) bonus 0 ps = true) (hne : ps ≠ [])
    (hend : pieceEnd2 0 ps = 1) (hF : AntitoneOn (QPoly.eval F) (Icc 0 1)) {ψ : ℝ}
    (hψ : ψ ∈ Icc (0 : ℝ) 1) :
    ∃ k K : ℚ, (∃ d, (d, k, K) ∈ ps) ∧ (k : ℝ) ≤ kProf F ψ ∧ kProf F ψ ≤ K ∧
      ((1 / 20 - bonus k K : ℚ) : ℝ) ≤ QPoly.eval Q ψ := by
  obtain ⟨k, K, hmem, h1, h2, h3⟩ := pieceCheck2_sound 0 ps hc hne
    (fun a ha b hb hab => hF (by simpa [hend] using ha) (by simpa [hend] using hb) hab) ψ
    (by simpa [hend] using hψ)
  rw [kirchhoffQ_cast] at h1 h2
  exact ⟨k, K, hmem, le_kirchhoffInv_iff.2 h1, kirchhoffInv_le_iff.2 h2, h3⟩

/-! ### Margins -/

/-- `16χ₀/25 = 4χ₀/a²`. -/
theorem four_chi_div (χ₀ : ℝ) : 4 * χ₀ / minorRadius ^ 2 = 16 * χ₀ / 25 := by
  unfold minorRadius; ring

/-- **Lower-barrier margin.** For every supplied reactivity and `χ₀ ∈ [1/2, 4/5]`,
`N[T_sub] ≥ 1/20 keV/s` on `[0,1]`. -/
theorem tsubq_margin (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 1 / 2 ≤ χ₀)
    (h2 : χ₀ ≤ 4 / 5) : ∀ ψ ∈ Icc (0 : ℝ) 1,
      (1 / 20 : ℝ) ≤ (qcylCoeffs sv χ₀).op ψ (Tsubq ψ) (kProf' fsubCoeffs ψ)
        (kProf'' fsubCoeffs ψ) := by
  intro ψ hψ
  obtain ⟨hl, -, hend, -⟩ := labels_facts
  have hne : subPieces ≠ [] := by simp [subPieces]
  -- the conduction bracket and the chosen corner
  set C := ψ * QPoly.eval (QPoly.deriv (QPoly.deriv fsubCoeffs)) ψ +
    QPoly.eval (QPoly.deriv fsubCoeffs) ψ with hC
  have key : ∀ χ : ℚ, (χ : ℝ) * C ≤ χ₀ * C →
      pieceCheck2 (lowQ fsubCoeffs χ) fsubCoeffs kirchhoffQ (1 / 20) lowBonus 0 subPieces =
        true → (1 / 20 : ℝ) ≤ (qcylCoeffs sv χ₀).op ψ (Tsubq ψ) (kProf' fsubCoeffs ψ)
          (kProf'' fsubCoeffs ψ) := by
    intro χ hχC hc
    obtain ⟨k, K, ⟨d, hmem⟩, hk, hK, hQ⟩ := piece_at hc hne hend fsub_antitone hψ
    obtain ⟨hT1, hT60⟩ := tsubq_bounds hψ
    change (k : ℝ) ≤ Tsubq ψ at hk
    change Tsubq ψ ≤ K at hK
    have hk0 : (0 : ℚ) ≤ k := hl _ hmem
    have hfl := svFloor_le sv hk0 hk hT60
    have hsv0 : 0 ≤ sv (Tsubq ψ) := BoschHaleDT.nonneg _ (by linarith)
    have hα : (229 / 10 * 10 ^ 21 : ℝ) * svFloor k ≤ alphaRate * sv (Tsubq ψ) :=
      (mul_le_mul_of_nonneg_left hfl (by norm_num)).trans
        (mul_le_mul_of_nonneg_right alphaRate_ge hsv0)
    have hsq := sqrt_le_quarter (T := Tsubq ψ) (by linarith)
    have hbr : bremsRate * Real.sqrt (Tsubq ψ) ≤ 201 / 1000 * ((K + 4) / 4) :=
      mul_le_mul bremsRate_le (hsq.trans (by linarith)) (Real.sqrt_nonneg _) (by norm_num)
    have hQ' := hQ
    simp only [lowQ, QPoly.eval_add, QPoly.eval_scale, condPoly_eval, lowBonus] at hQ'
    push_cast at hQ'
    rw [← hC] at hQ'
    have e : (qcylCoeffs sv χ₀).op ψ (Tsubq ψ) (kProf' fsubCoeffs ψ) (kProf'' fsubCoeffs ψ) =
        16 * χ₀ / 25 * C + (alphaRate * sv (Tsubq ψ) + QPoly.eval auxRateCoeffs ψ -
          bremsRate * Real.sqrt (Tsubq ψ)) := by
      rw [Tsubq, qcylCoeffs_op_kProf, four_chi_div, netSource_eq]
    rw [e]
    linarith
  rcases le_total 0 C with hC0 | hC0
  · exact key (1 / 2) (by push_cast; nlinarith) fsub_check_lo
  · exact key (4 / 5) (by push_cast; nlinarith) fsub_check_hi

/-- **Upper-barrier margin.** For every supplied reactivity and `χ₀ ∈ [1/2, 4/5]`,
`N[T_sup] ≤ −1/20 keV/s` on `[0,1]` (alpha heating bounded by Bosch–Hale ceilings,
bremsstrahlung dropped). -/
theorem tsupq_margin (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 1 / 2 ≤ χ₀)
    (h2 : χ₀ ≤ 4 / 5) : ∀ ψ ∈ Icc (0 : ℝ) 1,
      (qcylCoeffs sv χ₀).op ψ (Tsupq ψ) (kProf' fsupCoeffs ψ) (kProf'' fsupCoeffs ψ) ≤
        -(1 / 20) := by
  intro ψ hψ
  obtain ⟨-, hu, -, hend, -⟩ := labels_facts
  have hne : supPieces ≠ [] := by simp [supPieces]
  set C := ψ * QPoly.eval (QPoly.deriv (QPoly.deriv fsupCoeffs)) ψ +
    QPoly.eval (QPoly.deriv fsupCoeffs) ψ with hC
  have key : ∀ χ : ℚ, χ₀ * C ≤ (χ : ℝ) * C →
      pieceCheck2 (upQ fsupCoeffs χ) fsupCoeffs kirchhoffQ (1 / 20) upBonus 0 supPieces =
        true → (qcylCoeffs sv χ₀).op ψ (Tsupq ψ) (kProf' fsupCoeffs ψ)
          (kProf'' fsupCoeffs ψ) ≤ -(1 / 20) := by
    intro χ hχC hc
    obtain ⟨k, K, ⟨d, hmem⟩, -, hK, hQ⟩ := piece_at hc hne hend fsup_antitone hψ
    obtain ⟨hT1, -⟩ := tsupq_bounds hψ
    change Tsupq ψ ≤ K at hK
    obtain ⟨hw, hK60⟩ := hu _ hmem
    have hsv := sv_le_svCeil sv hw hK60 hT1 hK
    have hsv0 : 0 ≤ sv (Tsupq ψ) := BoschHaleDT.nonneg _ (by linarith)
    have hc0 : (0 : ℝ) ≤ svCeil K := hsv0.trans hsv
    have hα : alphaRate * sv (Tsupq ψ) ≤ 2291 / 100 * 10 ^ 21 * svCeil K :=
      mul_le_mul alphaRate_le hsv hsv0 (by norm_num)
    have hbr : 0 ≤ bremsRate * Real.sqrt (Tsupq ψ) :=
      mul_nonneg bremsRate_nonneg (Real.sqrt_nonneg _)
    have hQ' := hQ
    simp only [upQ, lowQ, QPoly.eval_add, QPoly.eval_scale, condPoly_eval, upBonus] at hQ'
    push_cast at hQ'
    rw [← hC] at hQ'
    have e : (qcylCoeffs sv χ₀).op ψ (Tsupq ψ) (kProf' fsupCoeffs ψ) (kProf'' fsupCoeffs ψ) =
        16 * χ₀ / 25 * C + (alphaRate * sv (Tsupq ψ) + QPoly.eval auxRateCoeffs ψ -
          bremsRate * Real.sqrt (Tsupq ψ)) := by
      rw [Tsupq, qcylCoeffs_op_kProf, four_chi_div, netSource_eq]
    rw [e]
    linarith
  rcases le_total 0 C with hC0 | hC0
  · exact key (4 / 5) (by push_cast; nlinarith) fsup_check_hi
  · exact key (1 / 2) (by push_cast; nlinarith) fsup_check_lo

/-! ### The two-sided band for all time -/

/-- **Two-sided quasilinear transport band (rung C2 in the cylinder).** For every reactivity
satisfying the supplied Bosch–Hale enclosures, every `χ₀ ∈ [1/2, 4/5]` m²/s (temperature
diffusivity `χ₀ (1/10 + T²/100)`), and every kernel solution of the quasilinear cylinder law on
all horizons with edge temperature in `[1, 3/2]` keV and initial profile between `T_sub` and
`T_sup`: for all `t ≥ 0` the temperature stays between `T_sub` and `T_sup`, the core
`ψ ≤ 3/10` stays at `T ≥ 10 keV`, and `T ≤ 47/2 keV` everywhere. -/
theorem quasilinear_band (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 1 / 2 ≤ χ₀)
    (h2 : χ₀ ≤ 4 / 5) {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (qcylCoeffs sv χ₀) Tedge τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsubq ψ ≤ u.T ψ 0 ∧ u.T ψ 0 ≤ Tsupq ψ)
    (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) :
    (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsubq ψ ≤ u.T ψ t ∧ u.T ψ t ≤ Tsupq ψ) ∧
      (∀ ψ, 0 ≤ ψ → ψ ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T ψ t) ∧
      (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ 47 / 2) := by
  have hL := qcylCoeffs_transportLaws sv (by linarith : (0 : ℝ) ≤ χ₀)
  have hk : (qcylCoeffs sv χ₀).axis = .regular → False := fun h => by
    simp [qcylCoeffs] at h
  have hlow : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsubq ψ ≤ u.T ψ t :=
    le_of_lowerMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fsubCoeffs) (fun h => (hk h).elim)
      (qcyl_opShiftControl sv χ₀ fsubCoeffs (fun ψ hψ => by
        linarith [(tsubq_bounds hψ).1, show Tsubq ψ = kProf fsubCoeffs ψ from rfl]))
      (by norm_num) (tsubq_margin sv h1 h2) (fun ψ hψ => (h0 ψ hψ).1)
      (fun t ht => by
        rw [barrier_edges.1]; exact (hedge t ht).1)
  have hup : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ Tsupq ψ :=
    le_of_upperMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fsupCoeffs) (fun h => (hk h).elim)
      (qcyl_opShiftControl sv χ₀ fsupCoeffs (fun ψ hψ => by
        linarith [(tsupq_bounds hψ).1, show Tsupq ψ = kProf fsupCoeffs ψ from rfl]))
      (by norm_num) (tsupq_margin sv h1 h2) (fun ψ hψ => (h0 ψ hψ).2)
      (fun t ht => by
        rw [barrier_edges.2]; exact (hedge t ht).2)
  refine ⟨fun ψ hψ t ht => ⟨hlow ψ hψ t ht, hup ψ hψ t ht⟩, fun ψ h0' h1' t ht => ?_,
    fun ψ hψ t ht => (hup ψ hψ t ht).trans (tsupq_bounds hψ).2⟩
  exact (tsubq_core h0' h1').trans (hlow ψ ⟨h0', h1'.trans (by norm_num)⟩ t ht)

/-- **Inequality hypotheses only (non-vacuity of the band hypotheses).** The lower barrier
itself, with constant edge data `1 keV`, satisfies the inequality hypotheses of
`quasilinear_band`. It is **not** admissible initial data: a classical solution with
`T_edge ≡ 1` must satisfy the corner compatibility `N[u₀](1) = T_edge'(0) = 0`
(`AxisFreeSolution.corner_compatibility`), whereas `N[T_sub](1) ≥ 1/20` (`tsubq_margin`).
Existence of solutions is not proved. -/
theorem quasilinear_band_hypotheses_satisfiable :
    (∀ ψ ∈ Icc (0 : ℝ) 1, Tsubq ψ ≤ Tsubq ψ ∧ Tsubq ψ ≤ Tsupq ψ) ∧
      ∀ t : ℝ, 0 ≤ t → (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 3 / 2 :=
  ⟨fun _ hψ => ⟨le_rfl, quasilinear_band_nonempty hψ⟩, fun _ _ => ⟨le_rfl, by norm_num⟩⟩

end PlasmaLean.Design.QuasilinearBarrier
