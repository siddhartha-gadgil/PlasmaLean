/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamNewtonField

/-!
# Fields in flow form with a general centre, density exponent and moving frame (`FlowFieldG`)

The interface `FlowField` of `Design/KamFlowField` hard-codes three choices that fit the rational
stellarator but not the Dommaschk QA target (`notes/theory/dommaschk-kam-certificate.md`, N-33
§2.2, obstacles O1 and O2):
* the radial coordinate is `R = 1 + u`;
* the invariant area density is `w = D/R³` (exponent `3`), with the flux primitive
  `α = (P_a/R) dR + (P_b/R²) dz`;
* the frame vector is `V₀ = (u, z)`, the radial vector from the fixed circle `R = 1, z = 0`.

`FlowFieldG` replaces them by
* `R = R₀ + u` with a real centre `R₀` (`RofG R₀ u`);
* `w = D/R^p` with a natural exponent `p`, and the primitive
  `α = (P_a/R^{k_a}) dR + (P_b/R^{k_b}) dz` with natural exponents `k_a, k_b`; the flux
  identities are stated in solved form at every torus point where `R` is invertible
  (`dα = w dR∧dz + …`), so every polynomial clearing of
  them implies them (`FlowFieldG.eq_of_pow_mul`);
* the frame vector `V₀ = K − A(φ) = (u − a_R, z − a_z)` about a **moving centre** `A(φ)`, given by
  two polynomial expressions `a_R, a_z` evaluated at `(u, z, c, s) = (0, 0, cos 2φ, sin 2φ)`
  (`cen`): trigonometric polynomials in `ψ`, independent of the torus. The centre's
  `φ`-derivative is the polynomial `A' = cenD a` (`Lt_cen`: `𝓛 a = ∂_φ a = A'`, `dTh_cen`:
  `∂_θ a = 0`). The torsion numerator is `P = (D² (X − A' − DX·V₀)) × V₀`.

The polynomial data `D, n_R, n_z, P_a, P_b, P` are in the variables `(u, z, c, s, w_R, w_z)` of
`Design/KamFlowField`, whose field-independent layer (operators, `pd`, `phiD`, `xB`, `xK`) is
reused unchanged. The derived objects are `F.Dof`, `F.Pof`, `F.resRp`, `F.resZp`, `F.resR`,
`F.resZ` as before, and the frame quantities `F.V0R`, `F.V0Z` and `F.W0` (`W₀ = ∂_θK × V₀`).

**Reduction to the existing interface.** `FlowField.toG` embeds every `FlowField` (`R₀ = 1`,
`p = 3`, `k_a = 1`, `k_b = 2`, centre `0`); the residuals, `D`, `P`, `V₀` and `W₀` agree
(`FlowField.toG_resR`, `toG_resZ`, `toG_Dof`, `toG_Pof`, `toG_V0R`, `toG_V0Z`, `toG_W0`), so the
invariant tori agree (`FlowField.toG_invariant_iff`). The rational field is `field14G`
(`field14G_invariant_iff`).

**Sanity.** `FlowFieldG.toroidal R₀` (`D = 1`, `n = 0`, centre `0`, `resR = 𝓛u`), and the
toroidal field about the moving centre `a_R = sin 2φ` (`toroidalShift`), whose torsion numerator
`P = −2 cos 2φ · z` is produced by the centre alone (`toroidalShift_Pof`,
`toroidalShift_Pof_ne`: it does not vanish).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PolyExpr Complex WEll1Z2

/-! ## The radial coordinate and the moving centre -/

/-- The radial coordinate `R = R₀ + u` of a torus point. -/
def RofG (R₀ : ℝ) (u : FA) : FA := algebraMap ℂ FA (R₀ : ℂ) + u

/-- For the centre `R₀ = 1`, `R = 1 + u` (the convention of `FlowField`). -/
theorem Rof_one (u : FA) : RofG 1 u = 1 + u := by simp [RofG]

/-- `R = R₀ + u` is analytic when `u` is. -/
theorem ana_RofG (R₀ : ℝ) {u : FA} (hu : Ana u) : Ana (RofG R₀ u) := (Ana.algebraMap _).add hu

/-- `R = R₀ + u` is real when `u` is. -/
theorem isReal_RofG (R₀ : ℝ) {u : FA} (hu : IsReal u) : IsReal (RofG R₀ u) :=
  (IsReal.algebraMap R₀).add hu

/-- Derivatives of `R = R₀ + u` are those of `u`. -/
theorem dS_RofG (a b : ℂ) (R₀ : ℝ) {u : FA} (hu : Ana u) : dS a b (RofG R₀ u) = dS a b u := by
  rw [RofG, dS_add _ _ (Ana.algebraMap _) hu, dS_algebraMap, zero_add]

/-- Pointwise value of `R = R₀ + u`. -/
theorem eval_RofG (R₀ : ℝ) (u : FA) (θ ψ : ℝ) : eval (RofG R₀ u) θ ψ = R₀ + eval u θ ψ := by
  rw [RofG, eval_add', eval_algebraMap]

/-- The value `a(φ)` of a centre polynomial: `a` evaluated at `(u, z, c, s) = (0, 0, cos 2φ,
sin 2φ)` (velocities `0`). It depends on `φ` only. -/
def cen (a : PolyExpr ℂ (Fin 6)) : FA := PolyExpr.eval (xB 0 0) a

/-- The `φ`-derivative `a'(φ) = ∂_c a·(−2s) + ∂_s a·(2c)` of a centre polynomial. -/
def cenD (a : PolyExpr ℂ (Fin 6)) : FA := phiD (xB 0 0) a

/-- The variables of the centre are analytic. -/
theorem ana_xB00 : ∀ i, Ana (xB 0 0 i) := fun i => by
  fin_cases i
  · exact Ana.zero
  · exact Ana.zero
  · exact ana_cS
  · exact ana_sS
  · exact Ana.zero
  · exact Ana.zero

/-- The centre is analytic. -/
theorem ana_cen (a : PolyExpr ℂ (Fin 6)) : Ana (cen a) := Ana.eval ana_xB00 a

/-- The centre is real when its polynomial has real coefficients. -/
theorem isReal_cen {a : PolyExpr ℂ (Fin 6)} (ha : a.RealConsts) : IsReal (cen a) :=
  IsReal.eval (fun i => by
    fin_cases i
    · exact map_zero cjHom
    · exact map_zero cjHom
    · exact isReal_cS
    · exact isReal_sS
    · exact map_zero cjHom
    · exact map_zero cjHom) a ha

/-- Chain rule for the centre: only the angle variables move. -/
theorem dS_cen (α β : ℂ) (a : PolyExpr ℂ (Fin 6)) :
    dS α β (cen a) = pd (xB 0 0) 2 a * dS α β cS + pd (xB 0 0) 3 a * dS α β sS := by
  have h0 : dS α β (0 : FA) = 0 := by simpa using dS_algebraMap α β 0
  rw [cen, dS_eval α β ana_xB00, deriv_eq_sum, Fin.sum_univ_six]
  simp only [xB, Matrix.cons_val, Fin.isValue, h0, zero_mul, zero_add, add_zero]
  ring

/-- **The centre does not depend on `θ`**: `∂_θ a = 0`. -/
theorem dTh_cen (a : PolyExpr ℂ (Fin 6)) : dTh (cen a) = 0 := by
  rw [dTh, dS_cen, show dS 1 0 cS = 0 from dTh_cS, show dS 1 0 sS = 0 from dTh_sS]
  simp

/-- **The transport of the centre is its `φ`-derivative**: `𝓛 a = a'`. -/
theorem Lt_cen (ι : ℝ) (a : PolyExpr ℂ (Fin 6)) : Lt ι (cen a) = cenD a := by
  rw [Lt, dS_cen, show dS (ι : ℂ) 2 cS = Lt ι cS from rfl, show dS (ι : ℂ) 2 sS = Lt ι sS from rfl,
    Lt_cS, Lt_sS, cenD, phiD]
  simp only [xB, Matrix.cons_val, Fin.isValue, Algebra.smul_def, map_ofNat]
  ring

/-- `∂_φ a = a'`. -/
theorem dPh_cen (a : PolyExpr ℂ (Fin 6)) : dPh (cen a) = cenD a := by
  have := Lt_cen 0 a
  rwa [Lt, Complex.ofReal_zero] at this

/-- The centre's derivative is analytic. -/
theorem ana_cenD (a : PolyExpr ℂ (Fin 6)) : Ana (cenD a) := by
  rw [← Lt_cen 0 a]; exact (ana_cen a).d _ _

/-- A constant centre is constant. -/
theorem cen_const (c : ℂ) : cen (const c) = algebraMap ℂ FA c := rfl

/-- A constant centre does not move. -/
theorem cenD_const (c : ℂ) : cenD (const c) = 0 := by
  simp [cenD, phiD, pd, PolyExpr.deriv]

/-- A frame-vector component `x − a(φ)` about the moving centre. -/
def V0of (a : PolyExpr ℂ (Fin 6)) (x : FA) : FA := x - cen a

/-- About the zero centre, the frame vector is the coordinate itself. -/
theorem V0of_zero (x : FA) : V0of (const 0) x = x := by
  simp [V0of, cen_const]

/-! ## The interface -/

/-- **A field in flow form with a general centre `R₀`, density exponent `p` and a moving frame
centre** (the generalisation of `FlowField` needed for the Dommaschk QA target, N-33 O1/O2).

The polynomials are in the variables `(u, z, c, s, w_R, w_z)` with `u = R − R₀`, `c = cos 2φ`,
`s = sin 2φ`:
* `Dp = D`, `nRp = n_R`, `nZp = n_z` (so `X = n/D` is the field-line vector field `dK/dφ`), with
  the invariant area density `w = D/R^p`;
* `Pap`, `Pbp`: the numerators of the primitive `α = (P_a/R^{k_a}) dR + (P_b/R^{k_b}) dz` of the
  flux 2-form `β = w (dR − X_R dφ) ∧ (dz − X_z dφ)`;
* `aRp`, `aZp`: the moving frame centre `A(φ) = (R₀ + a_R, a_z)` (evaluated by `cen`, so only
  the angle variables matter); the frame vector is `V₀ = (u − a_R, z − a_z)`;
* `Pp`: the torsion numerator `P = (D²(X − A' − DX·V₀)) × V₀`.

The divergence-free and torsion identities are required at every torus point `xB u z`; the flux
identities at every torus point where `R` is invertible (this is all the Newton step uses), in
the solved form `∂_R b − ∂_z a = w`, `∂_φ a = w X_z`, `∂_φ b = −w X_R`. -/
structure FlowFieldG where
  /-- The radial centre: `R = R₀ + u`. -/
  R₀ : ℝ
  /-- The density exponent: `w = D/R^p`. -/
  p : ℕ
  /-- The exponent of the `dR`-coefficient `a = P_a/R^{k_a}` of the flux primitive. -/
  ka : ℕ
  /-- The exponent of the `dz`-coefficient `b = P_b/R^{k_b}` of the flux primitive. -/
  kb : ℕ
  /-- `D` (the `φ`-component of the field, times a power of `R`). -/
  Dp : PolyExpr ℂ (Fin 6)
  /-- `n_R` (the `R`-component of the field, with the same factor). -/
  nRp : PolyExpr ℂ (Fin 6)
  /-- `n_z` (the `z`-component of the field, with the same factor). -/
  nZp : PolyExpr ℂ (Fin 6)
  /-- Numerator `R^{k_a}·a` of the `dR`-coefficient of the flux primitive. -/
  Pap : PolyExpr ℂ (Fin 6)
  /-- Numerator `R^{k_b}·b` of the `dz`-coefficient of the flux primitive. -/
  Pbp : PolyExpr ℂ (Fin 6)
  /-- The `dφ`-coefficient `P_c` of the flux primitive (`0` for fields whose vertical and radial
  fluxes through rotated annuli vanish; needed for the Dommaschk target, whose `B_z` has nonzero
  `φ`-mean). -/
  Pcp : PolyExpr ℂ (Fin 6)
  /-- The torsion numerator `P = (D² (X − A' − DX·V₀)) × V₀`. -/
  Pp : PolyExpr ℂ (Fin 6)
  /-- The radial offset `a_R(φ)` of the moving frame centre (from `R₀`). -/
  aRp : PolyExpr ℂ (Fin 6)
  /-- The vertical position `a_z(φ)` of the moving frame centre. -/
  aZp : PolyExpr ℂ (Fin 6)
  /-- `D` does not involve the velocities. -/
  noW_Dp : NoW Dp
  /-- `n_R` does not involve the velocities. -/
  noW_nRp : NoW nRp
  /-- `n_z` does not involve the velocities. -/
  noW_nZp : NoW nZp
  /-- `D` has real coefficients. -/
  real_Dp : Dp.RealConsts
  /-- `n_R` has real coefficients. -/
  real_nRp : nRp.RealConsts
  /-- `n_z` has real coefficients. -/
  real_nZp : nZp.RealConsts
  /-- `P` has real coefficients. -/
  real_Pp : Pp.RealConsts
  /-- `a_R` has real coefficients. -/
  real_aRp : aRp.RealConsts
  /-- `a_z` has real coefficients. -/
  real_aZp : aZp.RealConsts
  /-- **Divergence-free identity** `R ∂_φD − p n_R + R ∂_u n_R + R ∂_z n_z = 0` (the flux form
  `(D/R^p) dR∧dz` is invariant). -/
  divFree : ∀ u z : FA,
    RofG R₀ u * phiD (xB u z) Dp - (p : FA) * PolyExpr.eval (xB u z) nRp +
      RofG R₀ u * pd (xB u z) 0 nRp + RofG R₀ u * pd (xB u z) 1 nZp = 0
  /-- **Flux primitive identity** (a): `∂_R b − ∂_z a = w` (the `dR∧dz`-coefficient of `dα`). -/
  flux_a : ∀ u z : FA, IsUnit (RofG R₀ u) →
    pd (xB u z) 0 Pbp * Ring.inverse (RofG R₀ u) ^ kb -
        (kb : FA) * PolyExpr.eval (xB u z) Pbp * Ring.inverse (RofG R₀ u) ^ (kb + 1) -
      pd (xB u z) 1 Pap * Ring.inverse (RofG R₀ u) ^ ka =
        PolyExpr.eval (xB u z) Dp * Ring.inverse (RofG R₀ u) ^ p
  /-- **Flux primitive identity** (b): `∂_φ a − ∂_R P_c = w X_z`. -/
  flux_b : ∀ u z : FA, IsUnit (RofG R₀ u) →
    phiD (xB u z) Pap * Ring.inverse (RofG R₀ u) ^ ka - pd (xB u z) 0 Pcp =
      PolyExpr.eval (xB u z) nZp * Ring.inverse (RofG R₀ u) ^ p
  /-- **Flux primitive identity** (c): `∂_φ b − ∂_z P_c = −w X_R`. -/
  flux_c : ∀ u z : FA, IsUnit (RofG R₀ u) →
    phiD (xB u z) Pbp * Ring.inverse (RofG R₀ u) ^ kb - pd (xB u z) 1 Pcp =
      -(PolyExpr.eval (xB u z) nRp * Ring.inverse (RofG R₀ u) ^ p)
  /-- **The torsion numerator** `P = Y_R V₀_z − Y_z V₀_R` with
  `Y = n D − D ∇n·V₀ + n ∇D·V₀ − D² A'` (`= D² (X − DX·V₀ − A')`). -/
  torsion_poly : ∀ u z : FA,
    PolyExpr.eval (xB u z) Pp =
      (PolyExpr.eval (xB u z) nRp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp *
            (pd (xB u z) 0 nRp * V0of aRp u + pd (xB u z) 1 nRp * V0of aZp z) +
          PolyExpr.eval (xB u z) nRp *
            (pd (xB u z) 0 Dp * V0of aRp u + pd (xB u z) 1 Dp * V0of aZp z) -
          PolyExpr.eval (xB u z) Dp ^ 2 * cenD aRp) * V0of aZp z -
        (PolyExpr.eval (xB u z) nZp * PolyExpr.eval (xB u z) Dp -
          PolyExpr.eval (xB u z) Dp *
            (pd (xB u z) 0 nZp * V0of aRp u + pd (xB u z) 1 nZp * V0of aZp z) +
          PolyExpr.eval (xB u z) nZp *
            (pd (xB u z) 0 Dp * V0of aRp u + pd (xB u z) 1 Dp * V0of aZp z) -
          PolyExpr.eval (xB u z) Dp ^ 2 * cenD aZp) * V0of aRp u

namespace FlowFieldG

variable (F : FlowFieldG)

/-- The flow-form residual polynomial `D w_R − n_R`. -/
def resRp : PolyExpr ℂ (Fin 6) := sub (mul F.Dp (var 4)) F.nRp

/-- The flow-form residual polynomial `D w_z − n_z`. -/
def resZp : PolyExpr ℂ (Fin 6) := sub (mul F.Dp (var 5)) F.nZp

/-- `D(K)`. -/
def Dof (u z : FA) : FA := PolyExpr.eval (xB u z) F.Dp

/-- The torsion numerator `P(K)`. -/
def Pof (u z : FA) : FA := PolyExpr.eval (xB u z) F.Pp

/-- The `R`-residual `D 𝓛R − n_R` of a torus `K = (R₀ + u, z)`. -/
def resR (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) F.resRp

/-- The `z`-residual `D 𝓛z − n_z`. -/
def resZ (ι : ℝ) (u z : FA) : FA := PolyExpr.eval (xK ι u z) F.resZp

/-- `R = R₀ + u` of the field. -/
def R (u : FA) : FA := RofG F.R₀ u

/-- `R⁻¹`. -/
def Ri (u : FA) : FA := Ring.inverse (RofG F.R₀ u)

/-- The radial frame-vector component `V₀_R = u − a_R(φ)`. -/
def V0R (u : FA) : FA := V0of F.aRp u

/-- The vertical frame-vector component `V₀_z = z − a_z(φ)`. -/
def V0Z (z : FA) : FA := V0of F.aZp z

/-- `W₀ = ∂_θK × V₀ = ∂_θR · V₀_z − ∂_θz · V₀_R` (minus the winding rate about the moving
centre). -/
def W0 (u z : FA) : FA := dTh u * F.V0Z z - dTh z * F.V0R u

/-- `resR = D 𝓛u − n_R`. -/
theorem resR_eq (ι : ℝ) (u z : FA) :
    F.resR ι u z = F.Dof u z * Lt ι u - PolyExpr.eval (xB u z) F.nRp := by
  rw [resR, resRp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z F.noW_Dp, eval_xK_xB ι u z F.noW_nRp]
  rfl

/-- `resZ = D 𝓛z − n_z`. -/
theorem resZ_eq (ι : ℝ) (u z : FA) :
    F.resZ ι u z = F.Dof u z * Lt ι z - PolyExpr.eval (xB u z) F.nZp := by
  rw [resZ, resZp, Dof]
  simp only [PolyExpr.eval, eval_xK_xB ι u z F.noW_Dp, eval_xK_xB ι u z F.noW_nZp]
  rfl

/-- The residual polynomials have real coefficients. -/
theorem real_resRp : F.resRp.RealConsts := ⟨⟨F.real_Dp, True.intro⟩, F.real_nRp⟩

/-- The residual polynomials have real coefficients. -/
theorem real_resZp : F.resZp.RealConsts := ⟨⟨F.real_Dp, True.intro⟩, F.real_nZp⟩

/-- **Sanity**: the residual polynomials do involve the velocities. -/
theorem not_noW_resRp : ¬ NoW F.resRp := by
  simp [resRp, NoW]

/-- `𝓛V₀_R = 𝓛u − a_R'` (the moving centre contributes its `φ`-derivative). -/
theorem Lt_V0R (ι : ℝ) {u : FA} (hu : Ana u) : Lt ι (F.V0R u) = Lt ι u - cenD F.aRp := by
  rw [V0R, V0of, Lt, dS_sub _ _ hu (ana_cen _), ← Lt, ← Lt, Lt_cen]

/-- `𝓛V₀_z = 𝓛z − a_z'`. -/
theorem Lt_V0Z (ι : ℝ) {z : FA} (hz : Ana z) : Lt ι (F.V0Z z) = Lt ι z - cenD F.aZp := by
  rw [V0Z, V0of, Lt, dS_sub _ _ hz (ana_cen _), ← Lt, ← Lt, Lt_cen]

/-- `∂_θV₀_R = ∂_θu`. -/
theorem dTh_V0R {u : FA} (hu : Ana u) : dTh (F.V0R u) = dTh u := by
  rw [V0R, V0of, dTh, dS_sub _ _ hu (ana_cen _), ← dTh, ← dTh, dTh_cen, sub_zero]

/-- `∂_θV₀_z = ∂_θz`. -/
theorem dTh_V0Z {z : FA} (hz : Ana z) : dTh (F.V0Z z) = dTh z := by
  rw [V0Z, V0of, dTh, dS_sub _ _ hz (ana_cen _), ← dTh, ← dTh, dTh_cen, sub_zero]

/-- `V₀_R` is analytic. -/
theorem ana_V0R {u : FA} (hu : Ana u) : Ana (F.V0R u) := hu.sub (ana_cen _)

/-- `V₀_z` is analytic. -/
theorem ana_V0Z {z : FA} (hz : Ana z) : Ana (F.V0Z z) := hz.sub (ana_cen _)

/-- `V₀_R` is real. -/
theorem isReal_V0R {u : FA} (hu : IsReal u) : IsReal (F.V0R u) := hu.sub (isReal_cen F.real_aRp)

/-- `V₀_z` is real. -/
theorem isReal_V0Z {z : FA} (hz : IsReal z) : IsReal (F.V0Z z) := hz.sub (isReal_cen F.real_aZp)

/-- Cancel a unit power: a helper to obtain the solved flux identities from any polynomial
clearing (`R^m x = R^m y → x = y`). -/
theorem eq_of_pow_mul {r x y : FA} (hr : IsUnit r) (m : ℕ) (h : r ^ m * x = r ^ m * y) : x = y :=
  (hr.pow m).mul_left_cancel h

/-! ## Sanity: the toroidal field -/

/-- **Sanity: the purely toroidal flow field** about the radial centre `R₀` (`D = 1`, `n = 0`,
`p = 3`, primitive `α = −dz/(2R²)`, frame centre `0`, torsion `0`). -/
def toroidal (R₀ : ℝ) : FlowFieldG where
  R₀ := R₀
  p := 3
  ka := 1
  kb := 2
  Dp := const 1
  nRp := const 0
  nZp := const 0
  Pap := const 0
  Pbp := const (-1 / 2)
  Pcp := const 0
  Pp := const 0
  aRp := const 0
  aZp := const 0
  noW_Dp := by simp [NoW]
  noW_nRp := by simp [NoW]
  noW_nZp := by simp [NoW]
  real_Dp := by simp [PolyExpr.RealConsts]
  real_nRp := by simp [PolyExpr.RealConsts]
  real_nZp := by simp [PolyExpr.RealConsts]
  real_Pp := by simp [PolyExpr.RealConsts]
  real_aRp := by simp [PolyExpr.RealConsts]
  real_aZp := by simp [PolyExpr.RealConsts]
  divFree := fun u z => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  flux_a := fun u z _ => by
    have h : (2 : FA) * algebraMap ℂ FA (-1 / 2) = -1 := by
      rw [← map_ofNat (algebraMap ℂ FA) 2, ← map_mul]; norm_num
    simp only [pd, PolyExpr.deriv, PolyExpr.eval, map_one]
    push_cast
    linear_combination (-(Ring.inverse (RofG R₀ u)) ^ 3) * h
  flux_b := fun u z _ => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  flux_c := fun u z _ => by simp [phiD, pd, PolyExpr.deriv, PolyExpr.eval]
  torsion_poly := fun u z => by simp [pd, PolyExpr.deriv, PolyExpr.eval, cenD_const]

/-- **Sanity**: the residual of the toroidal field is `𝓛u`. -/
theorem toroidal_resR (R₀ ι : ℝ) (u z : FA) : (toroidal R₀).resR ι u z = Lt ι u := by
  rw [resR_eq]
  simp [toroidal, Dof, PolyExpr.eval]

/-- **Sanity: the toroidal field about a moving centre** `a_R = sin 2φ` (frame centre
`(R₀ + sin 2φ, 0)`). Its torsion numerator is `P = −D² a_R' V₀_z = −2 cos 2φ · z`, produced by the
centre alone. -/
def toroidalShift (R₀ : ℝ) : FlowFieldG where
  __ := toroidal R₀
  Pp := mul (const (-2)) (mul (var 2) (var 1))
  aRp := var 3
  real_Pp := by norm_num [PolyExpr.RealConsts, Complex.ext_iff]
  real_aRp := by simp [PolyExpr.RealConsts]
  torsion_poly := fun u z => by
    simp only [toroidal, cenD, phiD, pd, PolyExpr.deriv, PolyExpr.eval, V0of_zero, xB,
      Matrix.cons_val, Fin.isValue]
    simp [map_neg, map_ofNat]
    ring

/-- **Sanity**: the torsion numerator of `toroidalShift` is `−2 cos 2φ · z`. -/
theorem toroidalShift_Pof (R₀ : ℝ) (u z : FA) : (toroidalShift R₀).Pof u z = -2 * (cS * z) := by
  simp [toroidalShift, Pof, PolyExpr.eval, xB, map_neg, map_ofNat]

/-- **Sanity (rejected fixture)**: the moving centre does change the torsion; for the torus
point `z = 1` it is `−2 cos 2φ ≠ 0`, while the fixed-centre toroidal torsion vanishes. -/
theorem toroidalShift_Pof_ne (R₀ : ℝ) (u : FA) :
    (toroidalShift R₀).Pof u 1 ≠ (toroidal R₀).Pof u 1 := by
  rw [toroidalShift_Pof]
  simp only [toroidal, Pof, PolyExpr.eval, map_zero, mul_one]
  intro h
  have h1 := congrArg (fun x => eval x 0 (Real.pi / 2)) h
  simp only [eval_mul, eval_neg', eval_cS, eval_ofNat', eval_zero', Real.sin_pi_div_two] at h1
  norm_num at h1

end FlowFieldG

/-! ## Reduction to the existing interface -/

namespace FlowField

variable (F : FlowField)

/-- **Every `FlowField` is a `FlowFieldG`** with `R₀ = 1`, `p = 3`, `k_a = 1`, `k_b = 2` and
the frame centre `0`. -/
def toG : FlowFieldG where
  R₀ := 1
  p := 3
  ka := 1
  kb := 2
  Dp := F.Dp
  nRp := F.nRp
  nZp := F.nZp
  Pap := F.Pap
  Pbp := F.Pbp
  Pcp := const 0
  Pp := F.Pp
  aRp := const 0
  aZp := const 0
  noW_Dp := F.noW_Dp
  noW_nRp := F.noW_nRp
  noW_nZp := F.noW_nZp
  real_Dp := F.real_Dp
  real_nRp := F.real_nRp
  real_nZp := F.real_nZp
  real_Pp := F.real_Pp
  real_aRp := by simp [PolyExpr.RealConsts]
  real_aZp := by simp [PolyExpr.RealConsts]
  divFree := fun u z => by
    have h := F.divFree u z
    rw [Rof_one]; push_cast; exact h
  flux_a := fun u z hu => by
    rw [Rof_one] at hu ⊢
    have h := F.flux_a u z
    have hr := Ring.mul_inverse_cancel _ hu
    set r := Ring.inverse (1 + u)
    push_cast
    linear_combination r ^ 3 * h + (-(pd (xB u z) 0 F.Pbp * r ^ 2) +
      pd (xB u z) 1 F.Pap * r * ((1 + u) * r + 1)) * hr
  flux_b := fun u z hu => by
    rw [Rof_one] at hu ⊢
    rw [show pd (xB u z) 0 (const 0 : PolyExpr ℂ (Fin 6)) = 0 from rfl, sub_zero]
    have h := F.flux_b u z
    have hr := Ring.mul_inverse_cancel _ hu
    set r := Ring.inverse (1 + u)
    linear_combination r ^ 3 * h - phiD (xB u z) F.Pap * r * ((1 + u) * r + 1) * hr
  flux_c := fun u z hu => by
    rw [Rof_one] at hu ⊢
    rw [show pd (xB u z) 1 (const 0 : PolyExpr ℂ (Fin 6)) = 0 from rfl, sub_zero]
    have h := F.flux_c u z
    have hr := Ring.mul_inverse_cancel _ hu
    set r := Ring.inverse (1 + u)
    linear_combination r ^ 3 * h - phiD (xB u z) F.Pbp * r ^ 2 * hr
  torsion_poly := fun u z => by
    rw [F.torsion_poly u z]
    simp only [V0of_zero, cenD_const, mul_zero, sub_zero]

/-- The generalised `D(K)` is the old one. -/
theorem toG_Dof (u z : FA) : F.toG.Dof u z = F.Dof u z := rfl

/-- The generalised torsion numerator is the old one. -/
theorem toG_Pof (u z : FA) : F.toG.Pof u z = F.Pof u z := rfl

/-- The generalised `R`-residual is the old one. -/
theorem toG_resR (ι : ℝ) (u z : FA) : F.toG.resR ι u z = F.resR ι u z := rfl

/-- The generalised `z`-residual is the old one. -/
theorem toG_resZ (ι : ℝ) (u z : FA) : F.toG.resZ ι u z = F.resZ ι u z := rfl

/-- The generalised radial coordinate is `1 + u`. -/
theorem toG_R (u : FA) : F.toG.R u = 1 + u := Rof_one u

/-- The generalised frame vector is `V₀ = (u, z)` (`R` component). -/
theorem toG_V0R (u : FA) : F.toG.V0R u = u := V0of_zero u

/-- The generalised frame vector is `V₀ = (u, z)` (`z` component). -/
theorem toG_V0Z (z : FA) : F.toG.V0Z z = z := V0of_zero z

/-- The generalised winding form is the old `W₀`. -/
theorem toG_W0 (u z : FA) : F.toG.W0 u z = W0of u z := by
  rw [FlowFieldG.W0, toG_V0R, toG_V0Z, W0of]

/-- **Reduction**: the invariant tori of `F.toG` are those of `F`. -/
theorem toG_invariant_iff (ι : ℝ) (u z : FA) :
    (F.toG.resR ι u z = 0 ∧ F.toG.resZ ι u z = 0) ↔ (F.resR ι u z = 0 ∧ F.resZ ι u z = 0) :=
  Iff.rfl

end FlowField

/-- The rational stellarator `field (1/4)` as a generalised flow field (`R₀ = 1`, `p = 3`,
fixed centre). -/
def field14G : FlowFieldG := field14.toG

/-- **Sanity: the rational field reduces** — `field14G` has `R₀ = 1`, `p = 3` and the zero
centre, and its residuals are those of `field14`. -/
theorem field14G_data :
    field14G.R₀ = 1 ∧ field14G.p = 3 ∧ field14G.aRp = const 0 ∧ field14G.aZp = const 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Sanity: the rational field reduces** — the invariant tori of `field14G` are those of
`field14` (the certified `KamTorusAExact.torusA_exact` torus is one of them). -/
theorem field14G_invariant_iff (ι : ℝ) (u z : FA) :
    (field14G.resR ι u z = 0 ∧ field14G.resZ ι u z = 0) ↔
      (field14.resR ι u z = 0 ∧ field14.resZ ι u z = 0) :=
  field14.toG_invariant_iff ι u z

end PlasmaLean.Design.KamNewton
