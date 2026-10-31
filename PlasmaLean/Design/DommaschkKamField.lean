/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamFieldCheck
public import PlasmaLean.Design.KamFlowFieldG

/-!
# The Dommaschk QA target in flow form for the generalised KAM interface (N-33 plan item 5)

The certification target `DommaschkQA2R.field candidate` (`B = ∇(φ + V)`, NFP 2, the 9 log
potentials exactly 0) in the flow form of `Design/KamFlowFieldG`, with
* the radial centre `R₀ = 29/32` (`dkR0`; the middle of the `R`-range `[0.816, 1.001]` of torus A,
  N-33 §2.2), so `u = R − R₀`;
* the density exponent `p = k_a = k_b = 7` (`w = D/R⁷ = R B^φ`);
* the `φ`-dependence through `c = cos 2φ`, `s = sin 2φ` (`φ` the cylindrical angle; the strip
  algebra's `cS`, `sS`), the harmonics `cos 2kφ`, `sin 2kφ` written as `Re`, `Im (c + i s)^k`;
* the polynomials (`DommaschkKamFieldData`, generated and validated by
  `scripts/dommaschk_kam/emit_flowfield.py`)
  - `Dp`: `D = R⁶(1 + ∂_φV) = R⁷B_φ`, `nRp`: `n_R = R⁸B_R`, `nZp`: `n_z = R⁸B_z`,
  - `Pap`, `Pbp`: the numerators of the flux primitive `α = (P_a/R⁷) dR + (P_b/R⁷) dz + P_c dφ`,
    `P_a = R⁸∂_zW − zR⁶`, `P_b = −R⁸∂_RW` (`W` the `φ`-antiderivative of the oscillating part of
    `V`), and `Pcp`: `P_c = −c₀R²/2` (`c₀` the coefficient of the axisymmetric potential `z`);
  - `Pp aR aZ`: the torsion numerator about a moving frame centre given by two angle-only sparse
    polynomials `aR`, `aZ`, *defined* by its formula (so it is valid for every centre).

**Identities (the fields of `FlowFieldG`, at every torus point `xB u z` of the strip algebra).**
* `divFree` (exactly the field `FlowFieldG.divFree` for `R₀ = 29/32`, `p = 7`);
* `flux_a` (exactly `FlowFieldG.flux_a`, `k_a = k_b = p = 7`);
* `flux_b'`, `flux_c'`: the flux identities **with the `dφ`-component** `P_c`,
  `∂_φa − ∂_R P_c = w X_z`, `∂_φb − ∂_z P_c = −w X_R`;
* `torsion_poly` (exactly `FlowFieldG.torsion_poly` for the centre `(toPE aR, toPE aZ)`);
* `noW_*`, `real_*`.

**Obstruction (`no_primitive_without_dphi`, `no_flowFieldG`).** No `FlowFieldG` has
`R₀ = 29/32` and this `n_z`, whatever its other data: `FlowFieldG.flux_b` asks for a primitive
without `dφ`-component, so `∂_φ a = w X_z` would force the `φ`-mean of `w X_z = R B_z` to vanish,
while on the circle `R = R₀, z = 0` it is `c₀R₀ ≠ 0` (`c₀ = −0.0239…`; the vertical flux of `B`
through the annulus swept by a horizontal segment is `π c₀ (R₂² − R₁²) ≠ 0`). Hence
`dkField : FlowFieldG` **cannot exist with the current interface**. It needs the `dφ`-component
`P_c` that `FlowFieldS` already has (`α = … + P_c dφ`). That changes only `flux_b`, `flux_c` and
the frame's `B = a ∂_φR + b ∂_φz + P_c(K)` (`eta2_flux`); `⟨η₂⟩ = 0` is unaffected. With that
extension the instance is `{ R₀ := dkR0, p := 7, …, flux_b := flux_b', flux_c := flux_c' }`
(`notes/theory/kamflow-g-status.md`, item 5).

**Identification with `field candidate`.** `Design/DommaschkKamIdent`: `D = R⁷B_φ`,
`n_R = R⁸B_R`, `n_z = R⁸B_z` at every point with `R > 0` (`Dp_ident`, `nRp_ident`, `nZp_ident`,
`flow_ident`).

**Sanity.** `R_eq` (`R = R₀ + u` is the sparse `Rl`), `Pp_zero_centre` (about the zero centre the
torsion numerator is the one of the fixed frame `V₀ = (u, z)`), and the rejected fixture
`no_flowFieldG` itself.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKam

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PolyExpr DkPoly

/-- The radial centre `R₀ = 29/32`. -/
def dkR0 : ℝ := 29 / 32

/-- `D = R⁶(1 + ∂_φV) = R⁷B_φ`. -/
def Dp : PolyExpr ℂ (Fin 6) := toPE dD
/-- `n_R = R⁸B_R`. -/
def nRp : PolyExpr ℂ (Fin 6) := toPE dnR
/-- `n_z = R⁸B_z`. -/
def nZp : PolyExpr ℂ (Fin 6) := toPE dnZ
/-- `P_a`: the flux primitive has `dR`-coefficient `P_a/R⁷`. -/
def Pap : PolyExpr ℂ (Fin 6) := toPE dPa
/-- `P_b`: the flux primitive has `dz`-coefficient `P_b/R⁷`. -/
def Pbp : PolyExpr ℂ (Fin 6) := toPE dPb
/-- `P_c = −c₀R²/2`: the `dφ`-coefficient of the flux primitive. -/
def Pcp : PolyExpr ℂ (Fin 6) := toPE dPc

/-- The torsion numerator `P = (D² (X − A' − DX·V₀)) × V₀` about the moving centre
`A = (R₀ + a_R, a_z)`, `a_R = toPE aR`, `a_z = toPE aZ` (angle-only), *defined* by its formula:
`P = Y_R V₀_z − Y_z V₀_R`, `Y = n D − D ∇n·V₀ + n ∇D·V₀ − D² A'`. -/
def Pp (aR aZ : SP) : PolyExpr ℂ (Fin 6) :=
  let vR := sub (var 0) (toPE aR)
  let vZ := sub (var 1) (toPE aZ)
  let Y (n : SP) (a : SP) : PolyExpr ℂ (Fin 6) :=
    sub (add (sub (mul (toPE n) Dp)
        (mul Dp (add (mul (toPE (dU n)) vR) (mul (toPE (dZ n)) vZ))))
        (mul (toPE n) (add (mul (toPE (dU dD)) vR) (mul (toPE (dZ dD)) vZ))))
      (mul (mul Dp Dp) (toPE (phiS a)))
  sub (mul (Y dnR aR) vZ) (mul (Y dnZ aZ) vR)

/-! ## The radial coordinate -/

/-- `R₀ = 29/32` as a complex number. -/
theorem R0q_cast : ((R0q : ℚ) : ℂ) = ((dkR0 : ℝ) : ℂ) := by
  simp only [R0q, dkR0]; push_cast; ring

/-- `R = R₀ + u` is the sparse polynomial `Rl`. -/
theorem R_eq (u z : FA) : RofG dkR0 u = ev (xB u z) Rl := by
  simp [Rl, Tm.ev, RofG, xB, R0q_cast]

/-- `R⁷` is the sparse polynomial `R7l`. -/
theorem R7_eq (u z : FA) : RofG dkR0 u ^ 7 = ev (xB u z) R7l := by
  simp only [R7l, ev_mul, ← R_eq u z]
  simp [Tm.ev]; ring

/-! ## The identities -/

/-- **Divergence-free identity** `R ∂_φD − 7 n_R + R ∂_u n_R + R ∂_z n_z = 0` (the field
`FlowFieldG.divFree` with `R₀ = 29/32`, `p = 7`). -/
theorem divFree (u z : FA) :
    RofG dkR0 u * phiD (xB u z) Dp - ((7 : ℕ) : FA) * PolyExpr.eval (xB u z) nRp +
      RofG dkR0 u * pd (xB u z) 0 nRp + RofG dkR0 u * pd (xB u z) 1 nZp = 0 := by
  have h := congrArg (ev (xB u z)) divCombo_eq
  simp only [divCombo, ev_merge, ev_mul, ev_scale, ev_nil] at h
  rw [Dp, nRp, nZp, phiD_toPE, eval_toPE, pd_toPE_U, pd_toPE_Z, R_eq u z]
  push_cast at h ⊢
  simp only [map_ofNat] at h
  linear_combination h

/-- **Flux identity (a)** `∂_R b − ∂_z a = w` in solved form (the field `FlowFieldG.flux_a` with
`k_a = k_b = p = 7`). -/
theorem flux_a (u z : FA) (hR : IsUnit (RofG dkR0 u)) :
    pd (xB u z) 0 Pbp * Ring.inverse (RofG dkR0 u) ^ 7 -
        ((7 : ℕ) : FA) * PolyExpr.eval (xB u z) Pbp * Ring.inverse (RofG dkR0 u) ^ (7 + 1) -
      pd (xB u z) 1 Pap * Ring.inverse (RofG dkR0 u) ^ 7 =
        PolyExpr.eval (xB u z) Dp * Ring.inverse (RofG dkR0 u) ^ 7 := by
  have h := congrArg (ev (xB u z)) faCombo_eq
  simp only [faCombo, ev_merge, ev_mul, ev_scale, ev_nil] at h
  have hr := Ring.mul_inverse_cancel _ hR
  rw [Dp, Pap, Pbp, eval_toPE, eval_toPE, pd_toPE_U, pd_toPE_Z]
  rw [← R_eq u z] at h
  set r := Ring.inverse (RofG dkR0 u)
  set R := RofG dkR0 u
  push_cast at h ⊢
  simp only [map_ofNat] at h
  linear_combination r ^ 8 * h -
    (ev (xB u z) (dU dPb) - ev (xB u z) (dZ dPa) - ev (xB u z) dD) * r ^ 7 * hr

/-- **Flux identity (b) with the `dφ`-component**: `∂_φa − ∂_R P_c = w X_z`, i.e.
`∂_φP_a R⁻⁷ − ∂_u P_c = n_z R⁻⁷` (`FlowFieldG.flux_b` has no `P_c` term and fails:
`no_flowFieldG`). -/
theorem flux_b' (u z : FA) (hR : IsUnit (RofG dkR0 u)) :
    phiD (xB u z) Pap * Ring.inverse (RofG dkR0 u) ^ 7 - pd (xB u z) 0 Pcp =
      PolyExpr.eval (xB u z) nZp * Ring.inverse (RofG dkR0 u) ^ 7 := by
  have h := congrArg (ev (xB u z)) fbCombo_eq
  simp only [fbCombo, ev_merge, ev_mul, ev_scale, ev_nil] at h
  have hr := Ring.mul_inverse_cancel _ hR
  rw [Pap, Pcp, nZp, phiD_toPE, eval_toPE, pd_toPE_U]
  rw [← R7_eq u z] at h
  set r := Ring.inverse (RofG dkR0 u)
  set R := RofG dkR0 u
  push_cast at h ⊢
  linear_combination r ^ 7 * h + ev (xB u z) (dU dPc) *
    (1 + R * r + (R * r) ^ 2 + (R * r) ^ 3 + (R * r) ^ 4 + (R * r) ^ 5 + (R * r) ^ 6) * hr

/-- **Flux identity (c) with the `dφ`-component**: `∂_φb − ∂_z P_c = −w X_R`. -/
theorem flux_c' (u z : FA) (hR : IsUnit (RofG dkR0 u)) :
    phiD (xB u z) Pbp * Ring.inverse (RofG dkR0 u) ^ 7 - pd (xB u z) 1 Pcp =
      -(PolyExpr.eval (xB u z) nRp * Ring.inverse (RofG dkR0 u) ^ 7) := by
  have h := congrArg (ev (xB u z)) fcCombo_eq
  simp only [fcCombo, ev_merge, ev_mul, ev_scale, ev_nil] at h
  have hr := Ring.mul_inverse_cancel _ hR
  rw [Pbp, Pcp, nRp, phiD_toPE, eval_toPE, pd_toPE_Z]
  rw [← R7_eq u z] at h
  set r := Ring.inverse (RofG dkR0 u)
  set R := RofG dkR0 u
  push_cast at h ⊢
  linear_combination r ^ 7 * h + ev (xB u z) (dZ dPc) *
    (1 + R * r + (R * r) ^ 2 + (R * r) ^ 3 + (R * r) ^ 4 + (R * r) ^ 5 + (R * r) ^ 6) * hr

/-- The value of an angle-only polynomial at a torus point is the centre `cen`. -/
theorem eval_AO {a : SP} (ha : AO a = true) (u z : FA) :
    PolyExpr.eval (xB u z) (toPE a) = cen (toPE a) := by
  rw [cen, eval_toPE, eval_toPE]
  exact ev_congr_AO ha (by simp [xB]) (by simp [xB])

/-- The centre's derivative `cenD` at a torus point. -/
theorem cenD_AO {a : SP} (ha : AO a = true) (u z : FA) :
    cenD (toPE a) = PolyExpr.eval (xB u z) (toPE (phiS a)) := by
  rw [cenD, phiD_toPE, eval_toPE]
  exact ev_congr_AO (AO_phiS ha) (by simp [xB]) (by simp [xB])

/-- **The torsion numerator** (the field `FlowFieldG.torsion_poly` for the centre
`(toPE aR, toPE aZ)`, angle-only). -/
theorem torsion_poly (aR aZ : SP) (hR : AO aR = true) (hZ : AO aZ = true) (u z : FA) :
    PolyExpr.eval (xB u z) (Pp aR aZ) =
      (PolyExpr.eval (xB u z) nRp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp *
            (pd (xB u z) 0 nRp * V0of (toPE aR) u + pd (xB u z) 1 nRp * V0of (toPE aZ) z) +
          PolyExpr.eval (xB u z) nRp *
            (pd (xB u z) 0 Dp * V0of (toPE aR) u + pd (xB u z) 1 Dp * V0of (toPE aZ) z) -
          PolyExpr.eval (xB u z) Dp ^ 2 * cenD (toPE aR)) * V0of (toPE aZ) z -
        (PolyExpr.eval (xB u z) nZp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp *
            (pd (xB u z) 0 nZp * V0of (toPE aR) u + pd (xB u z) 1 nZp * V0of (toPE aZ) z) +
          PolyExpr.eval (xB u z) nZp *
            (pd (xB u z) 0 Dp * V0of (toPE aR) u + pd (xB u z) 1 Dp * V0of (toPE aZ) z) -
          PolyExpr.eval (xB u z) Dp ^ 2 * cenD (toPE aZ)) * V0of (toPE aR) u := by
  rw [cenD_AO hR u z, cenD_AO hZ u z]
  simp only [Pp, PolyExpr.eval, V0of, ← eval_AO hR u z, ← eval_AO hZ u z, nRp, nZp, Dp,
    pd_toPE_U, pd_toPE_Z, eval_toPE]
  simp only [xB, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Side conditions -/

/-- `D` does not involve the velocities. -/
theorem noW_Dp : NoW Dp := noW_toPE _
/-- `n_R` does not involve the velocities. -/
theorem noW_nRp : NoW nRp := noW_toPE _
/-- `n_z` does not involve the velocities. -/
theorem noW_nZp : NoW nZp := noW_toPE _
/-- `D` has real (rational) coefficients. -/
theorem real_Dp : Dp.RealConsts := realConsts_toPE _
/-- `n_R` has real (rational) coefficients. -/
theorem real_nRp : nRp.RealConsts := realConsts_toPE _
/-- `n_z` has real (rational) coefficients. -/
theorem real_nZp : nZp.RealConsts := realConsts_toPE _

/-- The torsion numerator has real constants. -/
theorem real_Pp (aR aZ : SP) : (Pp aR aZ).RealConsts := by
  simp only [Pp, PolyExpr.RealConsts, Dp]
  simp only [realConsts_toPE, and_self]

/-! ## The obstruction: no primitive without `dφ`-component -/

/-- The inverse of a nonzero constant of the strip algebra is a constant. -/
theorem ringInverse_algebraMap {c : ℂ} (hc : c ≠ 0) :
    Ring.inverse (algebraMap ℂ FA c) = algebraMap ℂ FA c⁻¹ := by
  have hu : IsUnit (algebraMap ℂ FA c) := (isUnit_iff_ne_zero.2 hc).map _
  have hr := Ring.mul_inverse_cancel _ hu
  calc Ring.inverse (algebraMap ℂ FA c)
      = (algebraMap ℂ FA c⁻¹ * algebraMap ℂ FA c) * Ring.inverse (algebraMap ℂ FA c) := by
        rw [← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    _ = algebraMap ℂ FA c⁻¹ := by rw [mul_assoc, hr, mul_one]

/-- The `φ`-mean `c₀R₀⁸` is not zero. -/
theorem Kq_ne : ((Kq : ℚ) : ℂ) ≠ 0 := by
  rw [Ne, Rat.cast_eq_zero]
  simp only [Kq, Rat.mkRat_eq_div]
  norm_num

/-- **The `φ`-mean of `n_z` on the circle `R = R₀, z = 0` is `c₀R₀⁸ ≠ 0`.** -/
theorem avg_nZ : avg (PolyExpr.eval (xB 0 0) nZp) = ((Kq : ℚ) : ℂ) := by
  have h := congrArg (ev (xB 0 0)) obsCombo_eq
  simp only [obsCombo, ev_merge, ev_scale, ev_nil, ev_cons] at h
  rw [ev_atZero (by simp [xB]) (by simp [xB])] at h
  have hQ : ev (xB 0 0) (phiS dQ) = dPh (cen (toPE dQ)) := by
    rw [dPh_cen, cenD, phiD_toPE]
  rw [hQ] at h
  have h' : PolyExpr.eval (xB 0 0) nZp =
      algebraMap ℂ FA (Kq : ℂ) + dPh (cen (toPE dQ)) := by
    rw [nZp, eval_toPE]
    simp only [Tm.ev, pow_zero, mul_one] at h
    push_cast at h
    linear_combination h
  rw [h', avg_add, avg_algebraMap, dPh, avg_dS, add_zero]

/-- **Obstruction: no flux primitive without `dφ`-component.** For no exponents `k_a`, `p` and
no polynomial `P_a` does `∂_φ(P_a R^{-k_a}) = n_z R^{-p}` hold at every torus point: at the circle
`u = z = 0` the `φ`-mean gives `0 = R₀^{-p} c₀R₀⁸`. -/
theorem no_primitive_without_dphi (ka p : ℕ) (Pa : PolyExpr ℂ (Fin 6)) :
    ¬ ∀ u z : FA, IsUnit (RofG dkR0 u) →
      phiD (xB u z) Pa * Ring.inverse (RofG dkR0 u) ^ ka =
        PolyExpr.eval (xB u z) nZp * Ring.inverse (RofG dkR0 u) ^ p := by
  intro hall
  have hc : ((dkR0 : ℝ) : ℂ) ≠ 0 := by norm_num [dkR0]
  have hRe : RofG dkR0 0 = algebraMap ℂ FA ((dkR0 : ℝ) : ℂ) := by rw [RofG, add_zero]
  have hu : IsUnit (RofG dkR0 0) := by rw [hRe]; exact (isUnit_iff_ne_zero.2 hc).map _
  have hb := hall 0 0 hu
  rw [hRe, ringInverse_algebraMap hc, ← map_pow, ← map_pow] at hb
  have hcen : phiD (xB 0 0) Pa = dPh (cen Pa) := by rw [dPh_cen]; rfl
  rw [hcen, mul_comm, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def] at hb
  have ha := congrArg avg hb
  rw [avg_smul, avg_smul, avg_nZ, dPh, avg_dS, mul_zero] at ha
  have : ((dkR0 : ℝ) : ℂ)⁻¹ ^ p * ((Kq : ℚ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) Kq_ne
  exact this ha.symm

/-- **A `dφ`-component of the flux primitive is necessary**: the Dommaschk target admits no
`FlowFieldG` instance with `P_c = 0` (`R₀ = 29/32`, this `n_z`), whatever its other data; the mean
`⟨B_z⟩ = c₀ ≠ 0` forces it. -/
theorem no_flowFieldG (F : FlowFieldG) (hR : F.R₀ = dkR0) (hn : F.nZp = nZp)
    (hc : F.Pcp = PolyExpr.const 0) : False :=
  no_primitive_without_dphi F.ka F.p F.Pap fun u z hu => by
    have h := F.flux_b u z (by rw [hR]; exact hu)
    rw [hc, show pd (xB u z) 0 (PolyExpr.const 0 : PolyExpr ℂ (Fin 6)) = 0 from rfl, sub_zero] at h
    rw [← hn, ← hR]; exact h

/-! ## The instance -/

/-- **The Dommaschk certification target as a `FlowFieldG`**, for an angle-only moving frame
centre `(aR, aZ)` (chosen with the torus data, N-33 items 6–8): `R₀ = 29/32`, exponents
`p = ka = kb = 7`, flux primitive with the `dφ`-component `P_c = −c₀R²/2`. -/
def dkFieldC (aR aZ : SP) (hR : AO aR = true) (hZ : AO aZ = true) : FlowFieldG where
  R₀ := dkR0; p := 7; ka := 7; kb := 7
  Dp := Dp; nRp := nRp; nZp := nZp; Pap := Pap; Pbp := Pbp; Pcp := Pcp; Pp := Pp aR aZ
  aRp := toPE aR; aZp := toPE aZ
  noW_Dp := noW_Dp; noW_nRp := noW_nRp; noW_nZp := noW_nZp
  real_Dp := real_Dp; real_nRp := real_nRp; real_nZp := real_nZp; real_Pp := real_Pp aR aZ
  real_aRp := realConsts_toPE aR; real_aZp := realConsts_toPE aZ
  divFree := divFree; flux_a := flux_a; flux_b := flux_b'; flux_c := flux_c'
  torsion_poly := torsion_poly aR aZ hR hZ

/-- The instance with the fixed centre `(R₀, 0)`. -/
def dkField : FlowFieldG := dkFieldC [] [] rfl rfl

/-! ## Sanity -/

/-- **Sanity**: about the zero centre, the torsion numerator is the one of the fixed frame
`V₀ = (u, z)` (as for `FlowField`, `KamNewtonField.torsion_poly`). -/
theorem Pp_zero_centre (u z : FA) :
    PolyExpr.eval (xB u z) (Pp [] []) =
      (PolyExpr.eval (xB u z) nRp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp * (pd (xB u z) 0 nRp * u + pd (xB u z) 1 nRp * z) +
          PolyExpr.eval (xB u z) nRp * (pd (xB u z) 0 Dp * u + pd (xB u z) 1 Dp * z)) * z -
        (PolyExpr.eval (xB u z) nZp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp * (pd (xB u z) 0 nZp * u + pd (xB u z) 1 nZp * z) +
          PolyExpr.eval (xB u z) nZp * (pd (xB u z) 0 Dp * u + pd (xB u z) 1 Dp * z)) * u := by
  rw [torsion_poly [] [] rfl rfl u z]
  have h0 : toPE ([] : SP) = const 0 := rfl
  rw [h0, V0of_zero, V0of_zero, cenD_const]
  ring

end PlasmaLean.Design.DommaschkKam
