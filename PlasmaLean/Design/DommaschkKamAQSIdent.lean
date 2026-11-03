/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAContract
public import PlasmaLean.Design.DommaschkKamAQSTransfer
public import PlasmaLean.Theory.Fields.VacuumBoozerTorus
public import PlasmaLean.Theory.Fields.BoozerWirtinger

/-!
# The QA defect on the exact torus A: identification and the chart hypotheses (N-34, D6)

**On-demand module** (imports the on-demand `Design/DommaschkKamAContract` and
`Design/DommaschkKamAQSTransfer`). Build: `lake build PlasmaLean.Design.DommaschkKamAQSIdent`.
Research note `notes/theory/dommaschk-qs-defect.md` (N-34), module D6.

For every exact torus `ExactTorusA u z` of the Dommaschk target (the conclusion of
`dk_exact_of_res`), with the cylindrical torus `K = cylTorus (RofC u) (Zof z)`, the field
`B = DommaschkQA2R.field candidate`, its potential `V = DommaschkQA2R.potential candidate` and
`ι = ι_A`:

* `ExactTorusA.vacuumPotentialOn`: `VacuumPotentialOn B V K`;
* **the identification** `ExactTorusA.torusQADefect_eq`:
  `torusQADefect B ι_A K θ φ = qsDefA u z θ φ = N_g/(2Q√Q R⁹)`, evaluated at the real leaf vector
  `lvA u z θ φ` (the values `Re F(θ, ψ(φ))` of the strip-algebra leaf vector `lvI u z`, which is
  the vector `lvS u z` of `Design/DommaschkKamAQSTransfer`), with `u_θ = ∂_θR`, `z_θ = ∂_θz`, in
  the straight-line program `qsQ`, `qsNg` of `Design/DommaschkKamAQSDefOut`. The strip forms
  `ExactTorusA.eval_Ng` (`N_g` is the value of the strip element `qsNg (lvI u z) ι (∂_θu) (∂_θz)`),
  `eval_Q`, `eval_leaf` are the interface to the ball chain;
* the flow-form torus quantities: `normSq_eq` (`|B|² = Q/R¹⁶`), `modB_eq` (`|B| = √Q/R⁸`),
  `boozerA_eq` (`a = (n_R u_θ + n_z z_θ)/R⁸`), `toroidalComp_eq` (`B^φ = B_φ/R`), `boozerJac_eq`
  (`J = Q/(R⁸D)`), `lvA_D` (`D = R⁷B_φ`), `lvA_nR`, `lvA_nZ`, `lvA_R`, `Q_pos`; the chain rule
  along the torus `hasDerivAt_Q_θ`, `hasDerivAt_Q_line` (through `dTh_evalB`, `Lt_evalB` and the
  partials `pd_QpI_U`, `pd_QpI_Z`, `phiD_QpI` of the polynomial expression `QpI` of `Q`);
* the algebra `qsiSq_eq`, `qsi_eq_real` (the leaf-vector form of
  `DommaschkKamCQSPoly.qsDefect_eq_real`; that module cannot be imported together with the
  admissibility chain, whose `Qp` has the same name);
* the chart hypotheses of the Wirtinger bound (module A2): `contDiff_torusPot` (`V ∘ K` is `C²`),
  `contDiff_torusModB` (`|B| ∘ K` is `C¹`), `torusPeriodic_torusPot`, `torusPeriodic_torusModB`
  (periods `2π` in `θ` and `2π/N = π` in `φ`), and, given `D > 0` on the torus, `Bphi_pos`,
  `toroidalComp_pos` (`B^φ > 0`), `boozerJac_pos` and **`boozerChartHyp`**:
  `BoozerChartHyp 2 ι_A (torusPot V K) (torusModB B K)`.

**Periodicity of `V ∘ K` in `φ` by `π`** without the field-period symmetry of `V` (not proved for
the Dommaschk potentials): `w(θ, φ) = v(θ, φ + π) − v(θ, φ)` has derivative zero, because
`v_θ = a` and `v_φ = J − 1 − ι a` (A1, `boozerJac_eq_partials`) and `a`, `J` are the flow-form
expressions above, which depend on `φ` only through `cos 2φ`, `sin 2φ` and the `π`-periodic torus;
so `w ≡ c`, and `2c = v(θ, φ + 2π) − v(θ, φ) = 0` because `K` is `2π`-periodic and `V` is
single-valued (`torusPot_add_pi`).

**The sign `B^φ > 0`.** `Bphi_ne` (C1 chain) gives `B^φ ≠ 0` only; the positivity is taken from
`D > 0` on the torus (`Bphi_pos`), which the D4/D5 chain certifies: `QSDefBounds.pointwise` gives
`|D − c_D| ≤ e_D` with `c_D − e_D ≥ D_min = 0.1116` (`ExactTorusA.Dmin_le`, `D_pos`).

**With the D4/D5 bounds** (`qsd_bounds` on the exact torus, `ExactTorusA.qsDefBounds`):
`torusQADefectLe_delta` (`TorusQADefectLe B ι_A K δ_∞`, `δ_∞ = 0.031258`), `torusQADefectLe_032`,
`Bmin_le` (`|B| ≥ B_min = 1.02656`), `toroidalComp_pos'` (`B^φ > 0`), `boozerChartHyp'`
(unconditional chart hypotheses), `oracleDefect_le` (oracle-normalised defect
`≤ √2 δ_∞/(2 B_min)`, sup route), and `dommaschkA_qaDefect` (the existential form, conditional only
on the initial residual bounds `e0R`, `e0Z`, as `dommaschk_iotaOnTorus`).

**Sanity.** `hasDerivAt_sqrt_div_pow_instance` (concrete instance of the chain rule for `√Q/R⁸`),
`torusPeriodic_cos_two` (accepted: `cos 2φ` has the two-field-period periodicity) and
`not_torusPeriodic_four` (rejected: it does not have the four-field-period one).
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Design.DommaschkKam DkPoly
open PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Design.KamTorusA (psi hasDerivAt_line hasDerivAt_toLp3)

/-! ## The program under ring homomorphisms -/

section Prog
variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (l : Fin 13 → A)

/-- Ring homomorphisms commute with `Q_u`. -/
theorem qsQu_map : f (qsQu l) = qsQu (fun i => f (l i)) := by simp [qsQu, map_ofNat]

/-- Ring homomorphisms commute with `Q_z`. -/
theorem qsQz_map : f (qsQz l) = qsQz (fun i => f (l i)) := by simp [qsQz, map_ofNat]

/-- Ring homomorphisms commute with `Q_φ`. -/
theorem qsQf_map : f (qsQf l) = qsQf (fun i => f (l i)) := by simp [qsQf, map_ofNat]

end Prog

/-! ## The algebraic identity (the vector form of `DommaschkKamCQSPoly.qsDefect_eq_real`) -/

/-- **The QA-defect identity for `|B|²`** on a leaf vector (`l 0 = D`, `l 4 = n_R`, `l 8 = n_z`,
`l 12 = R`): on an invariant torus (`D 𝓛u = n_R`, `D 𝓛z = n_z`), with `a = (n_R u_θ + n_z z_θ)/R⁸`,
`J = Q/(R⁸D)` and the chain-rule values of `𝓛(Q/R¹⁶)`, `∂_θ(Q/R¹⁶)`,
`[(1 + ιa)𝓛|B|² − ιJ∂_θ|B|²]/J = N_g/(Q R¹⁷)`. -/
theorem qsiSq_eq {K : Type*} [Field K] (l : Fin 13 → K) (ι uθ zθ Lu Lz : K) (hR : l 12 ≠ 0)
    (hD : l 0 ≠ 0) (hQ : qsQ l ≠ 0) (hLu : l 0 * Lu = l 4) (hLz : l 0 * Lz = l 8) :
    ((1 + ι * ((l 4 * uθ + l 8 * zθ) / l 12 ^ 8)) *
          ((qsQu l * Lu + qsQz l * Lz + qsQf l) / l 12 ^ 16 - 16 * qsQ l * Lu / l 12 ^ 17) -
        ι * (qsQ l / (l 12 ^ 8 * l 0)) *
          ((qsQu l * uθ + qsQz l * zθ) / l 12 ^ 16 - 16 * qsQ l * uθ / l 12 ^ 17)) /
        (qsQ l / (l 12 ^ 8 * l 0)) =
      qsNg l ι uθ zθ / (qsQ l * l 12 ^ 17) := by
  have hLu' : Lu = l 4 / l 0 := by field_simp; linear_combination hLu
  have hLz' : Lz = l 8 / l 0 := by field_simp; linear_combination hLz
  rw [hLu', hLz']
  simp only [qsNg, qsN0, qsN1, qsN2, qsML, qsPL]
  field_simp
  ring

/-- **The QA-defect identity for `|B| = √Q/R⁸`** on a real leaf vector:
`[(1 + ιa)𝓛|B| − ιJ∂_θ|B|]/J = N_g/(2Q√Q R⁹)` given the chain-rule values of `𝓛|B|`, `∂_θ|B|`. -/
theorem qsi_eq_real (l : Fin 13 → ℝ) (ι uθ zθ Lu Lz Lb tb : ℝ) (hR : 0 < l 12) (hD : l 0 ≠ 0)
    (hQ : 0 < qsQ l) (hLu : l 0 * Lu = l 4) (hLz : l 0 * Lz = l 8)
    (hLb : 2 * (Real.sqrt (qsQ l) / l 12 ^ 8) * Lb =
      (qsQu l * Lu + qsQz l * Lz + qsQf l) / l 12 ^ 16 - 16 * qsQ l * Lu / l 12 ^ 17)
    (htb : 2 * (Real.sqrt (qsQ l) / l 12 ^ 8) * tb =
      (qsQu l * uθ + qsQz l * zθ) / l 12 ^ 16 - 16 * qsQ l * uθ / l 12 ^ 17) :
    ((1 + ι * ((l 4 * uθ + l 8 * zθ) / l 12 ^ 8)) * Lb -
        ι * (qsQ l / (l 12 ^ 8 * l 0)) * tb) / (qsQ l / (l 12 ^ 8 * l 0)) =
      qsNg l ι uθ zθ / (2 * qsQ l * Real.sqrt (qsQ l) * l 12 ^ 9) := by
  have h := qsiSq_eq l ι uθ zθ Lu Lz hR.ne' hD hQ.ne' hLu hLz
  rw [← hLb, ← htb] at h
  have hs : 0 < Real.sqrt (qsQ l) := Real.sqrt_pos.2 hQ
  have hR' : l 12 ≠ 0 := hR.ne'
  have hQ' : qsQ l ≠ 0 := hQ.ne'
  have hJ : qsQ l / (l 12 ^ 8 * l 0) ≠ 0 := div_ne_zero hQ' (mul_ne_zero (pow_ne_zero _ hR') hD)
  have hb : (2 : ℝ) * (Real.sqrt (qsQ l) / l 12 ^ 8) ≠ 0 := by positivity
  rw [show qsNg l ι uθ zθ / (2 * qsQ l * Real.sqrt (qsQ l) * l 12 ^ 9) =
      qsNg l ι uθ zθ / (qsQ l * l 12 ^ 17) / (2 * (Real.sqrt (qsQ l) / l 12 ^ 8)) by
    field_simp, ← h]
  field_simp

/-! ## `Q` as a polynomial expression and its partial derivatives -/

/-- `R = R₀ + u` as a polynomial expression. -/
def RpI : PolyExpr ℂ (Fin 6) := toPE Rl

/-- `Q = n_R² + R²D² + n_z²` as a polynomial expression in `(u, z, c, s)` (not expanded). -/
def QpI : PolyExpr ℂ (Fin 6) :=
  .add (.add (.mul DommaschkKam.nRp DommaschkKam.nRp)
    (.mul (.mul RpI RpI) (.mul DommaschkKam.Dp DommaschkKam.Dp)))
    (.mul DommaschkKam.nZp DommaschkKam.nZp)

/-- `∂_φD = dDf` (kernel check of the generated data). -/
theorem qsi_dDf_eq : phiS dD = dDf := by kernel_fact
/-- `∂_φn_R = dnRf` (kernel check). -/
theorem qsi_dnRf_eq : phiS dnR = dnRf := by kernel_fact
/-- `∂_φn_z = dnZf` (kernel check). -/
theorem qsi_dnZf_eq : phiS dnZ = dnZf := by kernel_fact

/-- The leaf vector at a torus `(u, z)` in the strip frame (the vector `lvS` of
`Design/DommaschkKamAQSTransfer`, and the fields of `leavesAt (xB u z)` of
`Design/DommaschkKamCQSPoly`): `D, D_u, D_z, D_φ, n_R, …, n_z,φ, R` at `xB u z`. -/
def lvI (u z : FA) : Fin 13 → FA :=
  ![ev (xB u z) dD, ev (xB u z) (dU dD), ev (xB u z) (dZ dD), ev (xB u z) dDf,
    ev (xB u z) dnR, ev (xB u z) (dU dnR), ev (xB u z) (dZ dnR), ev (xB u z) dnRf,
    ev (xB u z) dnZ, ev (xB u z) (dU dnZ), ev (xB u z) (dZ dnZ), ev (xB u z) dnZf,
    ev (xB u z) Rl]

section Partials
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] (x : Fin 6 → A)

/-- The partial derivative of a product. -/
theorem pdI_mul (i : Fin 6) (p q : PolyExpr ℂ (Fin 6)) :
    pd x i (.mul p q) = pd x i p * PolyExpr.eval x q + PolyExpr.eval x p * pd x i q := rfl

/-- The partial derivative of a sum. -/
theorem pdI_add (i : Fin 6) (p q : PolyExpr ℂ (Fin 6)) :
    pd x i (.add p q) = pd x i p + pd x i q := rfl

/-- `phiD` of a product. -/
theorem phiDI_mul (p q : PolyExpr ℂ (Fin 6)) :
    phiD x (.mul p q) = phiD x p * PolyExpr.eval x q + PolyExpr.eval x p * phiD x q := by
  simp only [phiD, pdI_mul]; ring

/-- `phiD` of a sum. -/
theorem phiDI_add (p q : PolyExpr ℂ (Fin 6)) : phiD x (.add p q) = phiD x p + phiD x q := by
  simp only [phiD, pdI_add]; ring

/-- `R` at a point. -/
theorem eval_RpI : PolyExpr.eval x RpI = ev x Rl := eval_toPE x Rl

/-- `∂_u R = 1`. -/
theorem pd_RpI_U : pd x 0 RpI = 1 := by
  rw [RpI, pd_toPE_U]; simp [Rl, dU, Tm.dU, Tm.ev]

/-- `∂_z R = 0`. -/
theorem pd_RpI_Z : pd x 1 RpI = 0 := by
  rw [RpI, pd_toPE_Z]; simp [Rl, dZ, Tm.dZ]

/-- `∂_φ R = 0`. -/
theorem phiD_RpI : phiD x RpI = 0 := by
  rw [RpI, phiD_toPE]; simp [Rl, phiS, dC, DkPoly.dS, Tm.dC, Tm.dS, merge, mergeF, mulMono]

end Partials

/-- `Q` at the torus. -/
theorem eval_QpI (u z : FA) : PolyExpr.eval (xB u z) QpI = qsQ (lvI u z) := by
  simp only [QpI, PolyExpr.eval, eval_RpI, DommaschkKam.Dp, DommaschkKam.nRp, DommaschkKam.nZp,
    eval_toPE, qsQ, lvI]
  simp
  ring

/-- **`∂_u Q = Q_u`** at the torus. -/
theorem pd_QpI_U (u z : FA) : pd (xB u z) 0 QpI = qsQu (lvI u z) := by
  simp only [QpI, pdI_add, pdI_mul, pd_RpI_U, eval_RpI, DommaschkKam.Dp, DommaschkKam.nRp,
    DommaschkKam.nZp, PolyExpr.eval, eval_toPE, pd_toPE_U, qsQu, lvI]
  simp
  ring

/-- **`∂_z Q = Q_z`** at the torus. -/
theorem pd_QpI_Z (u z : FA) : pd (xB u z) 1 QpI = qsQz (lvI u z) := by
  simp only [QpI, pdI_add, pdI_mul, pd_RpI_Z, eval_RpI, DommaschkKam.Dp, DommaschkKam.nRp,
    DommaschkKam.nZp, PolyExpr.eval, eval_toPE, pd_toPE_Z, qsQz, lvI]
  simp
  ring

/-- **`∂_φ Q = Q_φ`** at the torus. -/
theorem phiD_QpI (u z : FA) : phiD (xB u z) QpI = qsQf (lvI u z) := by
  simp only [QpI, phiDI_add, phiDI_mul, phiD_RpI, eval_RpI, DommaschkKam.Dp, DommaschkKam.nRp,
    DommaschkKam.nZp, PolyExpr.eval, eval_toPE, phiD_toPE, qsi_dDf_eq, qsi_dnRf_eq, qsi_dnZf_eq,
    qsQf, lvI]
  simp
  ring

/-! ## The real leaves at a torus point and the closed form of the defect -/

/-- The field `B = ∇φ + Σ a_k ∇V_k` of the Dommaschk target (local notation). -/
local notation "Bdk" => DommaschkQA2R.field DommaschkQA2R.candidate

/-- The rotational transform `ι_A = −(19 + √5)/89` of torus A (local notation). -/
local notation "ιA" => DommaschkKamDio.dkIotaA

/-- The real leaves at the torus point `(θ, φ)`: `Re F(θ, ψ(φ))` of the strip leaves `lvI u z`. -/
def lvA (u z : FA) (θ φ : ℝ) : Fin 13 → ℝ := fun i => Zof (lvI u z i) θ φ

/-- The QA-defect numerator `N_g = N₀ + ι(N₁ ∂_θR + N₂ ∂_θz)` at the torus point `(θ, φ)`. -/
def ngA (u z : FA) (θ φ : ℝ) : ℝ := qsNg (lvA u z θ φ) ιA (Zof (dTh u) θ φ) (Zof (dTh z) θ φ)

/-- **The closed form of the QA defect** `N_g/(2Q√Q R⁹)` at the torus point `(θ, φ)`. -/
def qsDefA (u z : FA) (θ φ : ℝ) : ℝ :=
  ngA u z θ φ /
    (2 * qsQ (lvA u z θ φ) * Real.sqrt (qsQ (lvA u z θ φ)) * lvA u z θ φ 12 ^ 9)

/-! ## Real calculus on the strip -/

/-- `Re F` is `π`-periodic in `φ` (`ψ(φ + π) = ψ(φ) + 2π`). -/
theorem Zof_add_pi (x : FA) (θ φ : ℝ) : Zof x θ (φ + Real.pi) = Zof x θ φ := by
  simp only [Zof, psi_add_pi, eval_periodic_ψ]

/-- `Re F` is `2π`-periodic in `θ`. -/
theorem Zof_add_two_pi (x : FA) (θ φ : ℝ) : Zof x (θ + 2 * Real.pi) φ = Zof x θ φ := by
  simp only [Zof, eval_periodic_θ]

/-- `Re 𝓛F = ι Re ∂_θF + Re ∂_φF`. -/
theorem Zof_Lt {x : FA} (hx : Ana x) (ι θ φ : ℝ) :
    Zof (Lt ι x) θ φ = ι * Zof (dTh x) θ φ + Zof (dPh x) θ φ := by
  simp only [Zof, Lt_eq ι hx, eval_add', eval_smul', Complex.add_re, Complex.re_ofReal_mul]

/-- The derivative of `Re F` along the line of slope `ι` is `Re 𝓛F`. -/
theorem hasDerivAt_Zof_line {x : FA} (hx : Ana x) (ι θ φ : ℝ) :
    HasDerivAt (fun t => Zof x (θ + t * ι) (φ + t)) (Zof (Lt ι x) θ φ) 0 := by
  have h1 := hasDerivAt_line ((contDiff_Zof hx).differentiable (by norm_num)) θ φ ι 1
  rw [(hasDerivAt_Zof_θ hx θ φ).deriv, (hasDerivAt_Zof_φ hx θ φ).deriv] at h1
  simp only [mul_one, one_mul] at h1
  rw [Zof_Lt hx]
  exact h1

/-- **The chain rule for `√q/r⁸`** (the form `|B| = √Q/R⁸`):
`2 (√q/r⁸) · (√q/r⁸)' = q'/r¹⁶ − 16 q r'/r¹⁷`. -/
theorem hasDerivAt_sqrt_div_pow {q r : ℝ → ℝ} {q' r' x : ℝ} (hq : HasDerivAt q q' x)
    (hr : HasDerivAt r r' x) (hq0 : 0 < q x) (hr0 : 0 < r x) :
    ∃ b', HasDerivAt (fun t => Real.sqrt (q t) / r t ^ 8) b' x ∧
      2 * (Real.sqrt (q x) / r x ^ 8) * b' = q' / r x ^ 16 - 16 * q x * r' / r x ^ 17 := by
  refine ⟨_, (hq.sqrt hq0.ne').div (hr.pow 8) (pow_ne_zero _ hr0.ne'), ?_⟩
  have hs : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 hq0
  have hss : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt hq0.le
  have hr' : r x ≠ 0 := hr0.ne'
  field_simp
  push_cast
  linear_combination (-(16 : ℝ) * r' * r x ^ 7) * hss

/-- **Sanity (concrete instance)** of `hasDerivAt_sqrt_div_pow`: `q = 4`, `r = 1` constant. -/
theorem hasDerivAt_sqrt_div_pow_instance :
    ∃ b', HasDerivAt (fun _ : ℝ => Real.sqrt 4 / (1 : ℝ) ^ 8) b' 0 ∧
      2 * (Real.sqrt 4 / (1 : ℝ) ^ 8) * b' = 0 := by
  obtain ⟨b, hb, hb'⟩ := hasDerivAt_sqrt_div_pow (q := fun _ => (4 : ℝ)) (r := fun _ => (1 : ℝ))
    (hasDerivAt_const (0 : ℝ) (4 : ℝ)) (hasDerivAt_const (0 : ℝ) (1 : ℝ)) (by norm_num)
    (by norm_num)
  exact ⟨b, hb, by rw [hb']; ring⟩

/-! ## Cylindrical components -/

/-- The point of the cylindrical torus. -/
theorem cylTorus_apply (R z : ℝ → ℝ → ℝ) (θ φ : ℝ) :
    cylTorus R z θ φ = cylPoint (R θ φ) φ (z θ φ) := rfl

/-- `|B|² = B_R² + B_φ² + B_z²`. -/
theorem norm_field_sq (R φ Z : ℝ) :
    ‖Bdk (cylPoint R φ Z)‖ ^ 2 = cylBR R φ Z ^ 2 + cylBphi R φ Z ^ 2 + cylBz R φ Z ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, cylBR, cylBphi, cylBz]
  linear_combination (-((DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ Z)) 0 ^ 2 +
    (DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ Z)) 1 ^ 2)) *
    Real.sin_sq_add_cos_sq φ

/-- `B · (a cos φ, a sin φ, b) = a B_R + b B_z`. -/
theorem inner_field_toLp (R φ Z a b : ℝ) :
    ⟪Bdk (cylPoint R φ Z), WithLp.toLp 2 ![a * Real.cos φ, a * Real.sin φ, b]⟫ =
      cylBR R φ Z * a + cylBz R φ Z * b := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, cylBR, cylBz,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, RCLike.inner_apply, conj_trivial]
  ring

/-- `B^φ = B · ∇φ = B_φ/R`. -/
theorem inner_toroidal_field {R : ℝ} (hR : 0 < R) (φ Z : ℝ) :
    ⟪RationalStellarator.toroidal (cylPoint R φ Z), Bdk (cylPoint R φ Z)⟫ =
      cylBphi R φ Z / R := by
  rw [toroidal_cylPoint hR]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, cylBphi,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, RCLike.inner_apply, conj_trivial]
  field_simp
  ring

/-! ## The exact torus -/

namespace ExactTorusA

variable {u z : FA} (h : ExactTorusA u z)
include h

/-- The value at a torus point of a sparse polynomial of `xB u z` is real. -/
theorem eval_ev (p : SP) (θ φ : ℝ) :
    eval (ev (xB u z) p) θ (psi φ) =
      ((evR (RofC u θ φ - dkR0) (Zof z θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) p : ℝ) :
        ℂ) := by
  rw [← eval_toPE (xB u z) p, eval_polyExpr, h.eval_xB_pt, eval_toPE]
  exact ev_ofReal _ _ _ _ p

/-- The leaf values are real: `F(θ, ψ(φ)) = Re F(θ, ψ(φ))`. -/
theorem evalHom_ev (p : SP) (θ φ : ℝ) :
    evalHom θ (psi φ) (ev (xB u z) p) = Complex.ofRealHom (Zof (ev (xB u z) p) θ φ) := by
  change eval _ θ (psi φ) = (((eval _ θ (psi φ)).re : ℝ) : ℂ)
  rw [h.eval_ev p]
  simp

/-- **The leaves at the torus point are the real leaves.** -/
theorem lvI_eval (θ φ : ℝ) :
    (fun i => evalHom θ (psi φ) (lvI u z i)) = fun i => Complex.ofRealHom (lvA u z θ φ i) := by
  funext i
  fin_cases i <;> exact h.evalHom_ev _ θ φ

/-- `Q` at the torus point. -/
theorem eval_Q (θ φ : ℝ) :
    eval (qsQ (lvI u z)) θ (psi φ) = ((qsQ (lvA u z θ φ) : ℝ) : ℂ) := by
  change evalHom θ (psi φ) _ = Complex.ofRealHom _
  rw [qsQ_map, h.lvI_eval, ← qsQ_map]

/-- `Q_u` at the torus point. -/
theorem eval_Qu (θ φ : ℝ) :
    eval (qsQu (lvI u z)) θ (psi φ) = ((qsQu (lvA u z θ φ) : ℝ) : ℂ) := by
  change evalHom θ (psi φ) _ = Complex.ofRealHom _
  rw [qsQu_map, h.lvI_eval, ← qsQu_map]

/-- `Q_z` at the torus point. -/
theorem eval_Qz (θ φ : ℝ) :
    eval (qsQz (lvI u z)) θ (psi φ) = ((qsQz (lvA u z θ φ) : ℝ) : ℂ) := by
  change evalHom θ (psi φ) _ = Complex.ofRealHom _
  rw [qsQz_map, h.lvI_eval, ← qsQz_map]

/-- `Q_φ` at the torus point. -/
theorem eval_Qf (θ φ : ℝ) :
    eval (qsQf (lvI u z)) θ (psi φ) = ((qsQf (lvA u z θ φ) : ℝ) : ℂ) := by
  change evalHom θ (psi φ) _ = Complex.ofRealHom _
  rw [qsQf_map, h.lvI_eval, ← qsQf_map]

/-- A leaf at the torus point (strip form). -/
theorem eval_leaf (i : Fin 13) (θ φ : ℝ) :
    eval (lvI u z i) θ (psi φ) = ((lvA u z θ φ i : ℝ) : ℂ) :=
  congrFun (h.lvI_eval θ φ) i

/-- **The numerator at the torus point** (strip form): the value of the strip-algebra element
`qsNg (lvI u z) ι (∂_θu) (∂_θz)` is `N_g`. -/
theorem eval_Ng (θ φ : ℝ) :
    eval (qsNg (lvI u z) (algebraMap ℂ FA (ιA : ℂ)) (dTh u) (dTh z)) θ (psi φ) =
      ((ngA u z θ φ : ℝ) : ℂ) := by
  change evalHom θ (psi φ) _ = Complex.ofRealHom _
  have e1 : evalHom θ (psi φ) (algebraMap ℂ FA (ιA : ℂ)) = Complex.ofRealHom ιA :=
    eval_algebraMap _ θ (psi φ)
  have e2 : evalHom θ (psi φ) (dTh u) = Complex.ofRealHom (Zof (dTh u) θ φ) :=
    eval_ofReal_re (isReal_dTh h.real_u) θ (psi φ)
  have e3 : evalHom θ (psi φ) (dTh z) = Complex.ofRealHom (Zof (dTh z) θ φ) :=
    eval_ofReal_re (isReal_dTh h.real_z) θ (psi φ)
  rw [qsNg_map, e1, e2, e3, h.lvI_eval, ngA, ← qsNg_map]

/-- `Re Q` of the strip element is the real `Q`. -/
theorem Zof_Q (θ φ : ℝ) : Zof (qsQ (lvI u z)) θ φ = qsQ (lvA u z θ φ) := by
  simp only [Zof, h.eval_Q, Complex.ofReal_re]

/-- `D = R⁷B_φ` at the torus point. -/
theorem lvA_D (θ φ : ℝ) :
    lvA u z θ φ 0 = RofC u θ φ ^ 7 * cylBphi (RofC u θ φ) φ (Zof z θ φ) := by
  change (eval (ev (xB u z) dD) θ (psi φ)).re = _
  rw [← eval_toPE, ← DommaschkKam.Dp]
  change (eval (dkFieldTC.Dof u z) θ (psi φ)).re = _
  rw [h.eval_Dof, Complex.ofReal_re]

/-- `n_R = R⁸B_R` at the torus point. -/
theorem lvA_nR (θ φ : ℝ) :
    lvA u z θ φ 4 = RofC u θ φ ^ 8 * cylBR (RofC u θ φ) φ (Zof z θ φ) := by
  change (eval (ev (xB u z) dnR) θ (psi φ)).re = _
  rw [← eval_toPE, ← DommaschkKam.nRp, eval_polyExpr, h.eval_xB_pt, nRp_ident (h.R_pos θ φ),
    Complex.ofReal_re]

/-- `n_z = R⁸B_z` at the torus point. -/
theorem lvA_nZ (θ φ : ℝ) :
    lvA u z θ φ 8 = RofC u θ φ ^ 8 * cylBz (RofC u θ φ) φ (Zof z θ φ) := by
  change (eval (ev (xB u z) dnZ) θ (psi φ)).re = _
  rw [← eval_toPE, ← DommaschkKam.nZp, eval_polyExpr, h.eval_xB_pt, nZp_ident (h.R_pos θ φ),
    Complex.ofReal_re]

/-- The leaf `R` is the radius of the torus. -/
theorem lvA_R (θ φ : ℝ) : lvA u z θ φ 12 = RofC u θ φ := by
  change (eval (ev (xB u z) Rl) θ (psi φ)).re = _
  rw [← eval_toPE, eval_polyExpr, h.eval_xB_pt, eval_toPE, ev_Rl]
  simp [DommaschkKam.ptC, R0q, dkR0]

/-- `R > 0` at the leaves. -/
theorem lvA_R_pos (θ φ : ℝ) : 0 < lvA u z θ φ 12 := by
  rw [h.lvA_R]; exact h.R_pos θ φ

/-- `D ≠ 0` at the leaves. -/
theorem lvA_D_ne (θ φ : ℝ) : lvA u z θ φ 0 ≠ 0 := by
  rw [h.lvA_D]
  exact mul_ne_zero (pow_ne_zero _ (h.R_pos θ φ).ne') (h.Bphi_ne θ φ)

/-- `Q = n_R² + R²D² + n_z² > 0` on the torus. -/
theorem Q_pos (θ φ : ℝ) : 0 < qsQ (lvA u z θ φ) := by
  have hR := h.lvA_R_pos θ φ
  have hD := h.lvA_D_ne θ φ
  have h1 : 0 < lvA u z θ φ 12 ^ 2 * lvA u z θ φ 0 ^ 2 := by positivity
  rw [qsQ]
  positivity

/-- **`|B|² = Q/R¹⁶`** on the torus. -/
theorem normSq_eq (θ φ : ℝ) :
    ‖Bdk (cylTorus (RofC u) (Zof z) θ φ)‖ ^ 2 = qsQ (lvA u z θ φ) / lvA u z θ φ 12 ^ 16 := by
  have hR := h.R_pos θ φ
  rw [cylTorus_apply, norm_field_sq, qsQ, h.lvA_nR, h.lvA_D, h.lvA_nZ, h.lvA_R]
  field_simp

/-- **`|B| = √Q/R⁸`** on the torus. -/
theorem modB_eq (θ φ : ℝ) :
    modB Bdk (cylTorus (RofC u) (Zof z)) θ φ =
      Real.sqrt (qsQ (lvA u z θ φ)) / lvA u z θ φ 12 ^ 8 := by
  have hR := h.lvA_R_pos θ φ
  rw [modB, ← Real.sqrt_sq (norm_nonneg _), h.normSq_eq,
    Real.sqrt_div' _ (by positivity), show lvA u z θ φ 12 ^ 16 =
      (lvA u z θ φ 12 ^ 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- The `θ`-derivative of the torus: `∂_θK = (∂_θR cos φ, ∂_θR sin φ, ∂_θz)`. -/
theorem hasDerivAt_torus_θ (θ φ : ℝ) :
    HasDerivAt (fun t => cylTorus (RofC u) (Zof z) t φ)
      (WithLp.toLp 2 ![Zof (dTh u) θ φ * Real.cos φ, Zof (dTh u) θ φ * Real.sin φ,
        Zof (dTh z) θ φ]) θ :=
  hasDerivAt_toLp3 ((hasDerivAt_RofC_θ h.ana_u θ φ).mul_const _)
    ((hasDerivAt_RofC_θ h.ana_u θ φ).mul_const _) (hasDerivAt_Zof_θ h.ana_z θ φ)

/-- **`a = B · ∂_θK = (n_R u_θ + n_z z_θ)/R⁸`** on the torus. -/
theorem boozerA_eq (θ φ : ℝ) :
    boozerA Bdk (cylTorus (RofC u) (Zof z)) θ φ =
      (lvA u z θ φ 4 * Zof (dTh u) θ φ + lvA u z θ φ 8 * Zof (dTh z) θ φ) /
        lvA u z θ φ 12 ^ 8 := by
  have hR := h.R_pos θ φ
  rw [boozerA, thetaDeriv, (h.hasDerivAt_torus_θ θ φ).deriv, cylTorus_apply, inner_field_toLp,
    h.lvA_nR, h.lvA_nZ, h.lvA_R]
  field_simp

/-- **`B^φ = B · ∇φ = B_φ/R`** on the torus. -/
theorem toroidalComp_eq (θ φ : ℝ) :
    toroidalComp Bdk (cylTorus (RofC u) (Zof z)) θ φ =
      cylBphi (RofC u θ φ) φ (Zof z θ φ) / RofC u θ φ := by
  rw [toroidalComp, cylTorus_apply]
  exact inner_toroidal_field (h.R_pos θ φ) _ _

/-- **`J = B · 𝓛K = Q/(R⁸D)`** on the torus. -/
theorem boozerJac_eq (θ φ : ℝ) :
    boozerJac Bdk ιA (cylTorus (RofC u) (Zof z)) θ φ =
      qsQ (lvA u z θ φ) / (lvA u z θ φ 12 ^ 8 * lvA u z θ φ 0) := by
  rw [boozerJac_eq_normSq_div h.fieldTorus, h.normSq_eq, h.toroidalComp_eq, h.lvA_D, h.lvA_R]
  have hR := (h.R_pos θ φ).ne'
  have hB := h.Bphi_ne θ φ
  field_simp

/-- Invariance in leaf form: `D 𝓛R = n_R` with `𝓛R = Re 𝓛u`. -/
theorem inv_R' (θ φ : ℝ) : lvA u z θ φ 0 * Zof (Lt ιA u) θ φ = lvA u z θ φ 4 := by
  have e := h.inv_R θ φ
  rw [(hasDerivAt_RofC_φ h.ana_u θ φ).deriv, (hasDerivAt_RofC_θ h.ana_u θ φ).deriv] at e
  rw [h.lvA_D, h.lvA_nR, Zof_Lt h.ana_u]
  simp only [Zof] at e ⊢
  linear_combination e

/-- Invariance in leaf form: `D 𝓛z = n_z` with `𝓛z = Re 𝓛z`. -/
theorem inv_Z' (θ φ : ℝ) : lvA u z θ φ 0 * Zof (Lt ιA z) θ φ = lvA u z θ φ 8 := by
  have e := h.inv_Z θ φ
  rw [(hasDerivAt_Zof_φ h.ana_z θ φ).deriv, (hasDerivAt_Zof_θ h.ana_z θ φ).deriv] at e
  rw [h.lvA_D, h.lvA_nZ, Zof_Lt h.ana_z]
  simp only [Zof] at e ⊢
  linear_combination e

/-- The strip element `Q(xB u z)` is analytic. -/
theorem ana_Q : Ana (qsQ (lvI u z)) := by
  rw [← eval_QpI]; exact h.adm.frame.ana_evalB QpI

/-- **`∂_θQ = Q_u ∂_θR + Q_z ∂_θz`** along the torus (chain rule in the strip algebra). -/
theorem hasDerivAt_Q_θ (θ φ : ℝ) :
    HasDerivAt (fun t => qsQ (lvA u z t φ))
      (qsQu (lvA u z θ φ) * Zof (dTh u) θ φ + qsQz (lvA u z θ φ) * Zof (dTh z) θ φ) θ := by
  have h1 := hasDerivAt_Zof_θ h.ana_Q θ φ
  have e2 : dTh (qsQ (lvI u z)) = qsQu (lvI u z) * dTh u + qsQz (lvI u z) * dTh z := by
    rw [← eval_QpI, h.adm.frame.dTh_evalB, pd_QpI_U, pd_QpI_Z]; rfl
  simp only [h.Zof_Q] at h1
  convert h1 using 1
  rw [e2]
  simp only [Zof, eval_add', eval_mul, h.eval_Qu, h.eval_Qz, Complex.add_re,
    Complex.re_ofReal_mul]

/-- **`𝓛Q = Q_u 𝓛R + Q_z 𝓛z + Q_φ`** along the torus. -/
theorem hasDerivAt_Q_line (θ φ : ℝ) :
    HasDerivAt (fun t => qsQ (lvA u z (θ + t * ιA) (φ + t)))
      (qsQu (lvA u z θ φ) * Zof (Lt ιA u) θ φ + qsQz (lvA u z θ φ) * Zof (Lt ιA z) θ φ +
        qsQf (lvA u z θ φ)) 0 := by
  have h1 := hasDerivAt_Zof_line h.ana_Q ιA θ φ
  have e2 : Lt ιA (qsQ (lvI u z)) =
      qsQu (lvI u z) * Lt ιA u + qsQz (lvI u z) * Lt ιA z + qsQf (lvI u z) := by
    rw [← eval_QpI, h.adm.frame.Lt_evalB, pd_QpI_U, pd_QpI_Z, phiD_QpI]; rfl
  simp only [h.Zof_Q] at h1
  convert h1 using 1
  rw [e2]
  simp only [Zof, eval_add', eval_mul, h.eval_Qu, h.eval_Qz, h.eval_Qf, Complex.add_re,
    Complex.re_ofReal_mul, Complex.ofReal_re]

/-- `∂_θR` along the torus (leaf form). -/
theorem hasDerivAt_R_θ (θ φ : ℝ) :
    HasDerivAt (fun t => lvA u z t φ 12) (Zof (dTh u) θ φ) θ := by
  simp only [h.lvA_R]
  exact hasDerivAt_RofC_θ h.ana_u θ φ

/-- `𝓛R` along the torus (leaf form). -/
theorem hasDerivAt_R_line (θ φ : ℝ) :
    HasDerivAt (fun t => lvA u z (θ + t * ιA) (φ + t) 12) (Zof (Lt ιA u) θ φ) 0 := by
  simp only [h.lvA_R]
  exact (hasDerivAt_Zof_line h.ana_u ιA θ φ).const_add _

/-- **The identification of the QA defect on the exact torus** (N-34 D6):
`torusQADefect B ι_A K θ φ = N_g/(2Q√Q R⁹)` at the real leaves of the torus point. -/
theorem torusQADefect_eq (θ φ : ℝ) :
    torusQADefect Bdk ιA (cylTorus (RofC u) (Zof z)) θ φ = qsDefA u z θ φ := by
  have hR := h.lvA_R_pos θ φ
  have hQ := h.Q_pos θ φ
  obtain ⟨tb, htb, htb'⟩ := hasDerivAt_sqrt_div_pow (h.hasDerivAt_Q_θ θ φ) (h.hasDerivAt_R_θ θ φ)
    hQ hR
  obtain ⟨Lb, hLb, hLb'⟩ := hasDerivAt_sqrt_div_pow (h.hasDerivAt_Q_line θ φ)
    (h.hasDerivAt_R_line θ φ) (by simpa using hQ) (by simpa using hR)
  simp only [zero_mul, add_zero] at hLb'
  have em : modB Bdk (cylTorus (RofC u) (Zof z)) =
      fun θ' φ' => Real.sqrt (qsQ (lvA u z θ' φ')) / lvA u z θ' φ' 12 ^ 8 :=
    funext fun θ' => funext fun φ' => h.modB_eq θ' φ'
  have e1 : thetaDeriv (modB Bdk (cylTorus (RofC u) (Zof z))) θ φ = tb := by
    rw [thetaDeriv, em]; exact htb.deriv
  have e2 : lineDeriv ιA (modB Bdk (cylTorus (RofC u) (Zof z))) θ φ = Lb := by
    rw [PlasmaLean.Fields.VacuumBoozer.lineDeriv, em]; exact hLb.deriv
  rw [torusQADefect, e1, e2, h.boozerA_eq, h.boozerJac_eq, boozerDeriv]
  exact qsi_eq_real (lvA u z θ φ) ιA _ _ _ _ Lb tb hR (h.lvA_D_ne θ φ) hQ
    (h.inv_R' θ φ) (h.inv_Z' θ φ) hLb' htb'

end ExactTorusA

/-! ## Regularity and periodicity: the hypotheses of the Wirtinger bound -/

/-- The potential `V = Σ a_k V_k` of the Dommaschk target (local notation). -/
local notation "Vdk" => DommaschkQA2R.potential DommaschkQA2R.candidate

/-- The real leaves are `π`-periodic in `φ`. -/
theorem lvA_add_pi (u z : FA) (θ φ : ℝ) : lvA u z θ (φ + Real.pi) = lvA u z θ φ := by
  funext i; exact Zof_add_pi _ _ _

/-- `perPhi 2 = π`. -/
theorem perPhi_two : perPhi 2 = Real.pi := by
  rw [perPhi]; push_cast; ring

/-- `r² = R²` at a cylindrical point (the `CylAlgebra` form). -/
theorem cyl_r2_cylPoint (R φ Z : ℝ) : PlasmaLean.Fields.CylAlgebra.r2 (cylPoint R φ Z) = R ^ 2 :=
  r2_cylPoint R φ Z

/-- The potential is `C²` off the axis. -/
theorem contDiffAt_Vdk {x : PlasmaLean.Fields.Space} (hx : PlasmaLean.Fields.CylAlgebra.r2 x ≠ 0) :
    ContDiffAt ℝ 2 Vdk x := by
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin 42)),
      ContDiffAt ℝ 2 (fun y => (DommaschkQA2R.candidate k : ℝ) * DommaschkQA2R.V k y) x :=
    fun k _ => contDiffAt_const.mul
      (contDiffAt_const.mul (PlasmaLean.Fields.CylAlgebra.contDiffAt_eval _ hx))
  exact ContDiffAt.sum hk

namespace ExactTorusA

variable {u z : FA} (h : ExactTorusA u z)
include h

/-- **Vacuum along the torus**: `B = ∇φ + ∇V` at every point of the exact torus. -/
theorem vacuumPotentialOn : VacuumPotentialOn Bdk Vdk (cylTorus (RofC u) (Zof z)) := fun θ φ => by
  have hx : cylTorus (RofC u) (Zof z) θ φ ∈ PlasmaLean.Fields.CylAlgebra.domain := by
    change 0 < PlasmaLean.Fields.CylAlgebra.r2 (cylPoint _ _ _)
    rw [cyl_r2_cylPoint]; exact pow_pos (h.R_pos θ φ) 2
  have e : Bdk (cylTorus (RofC u) (Zof z) θ φ) -
      RationalStellarator.toroidal (cylTorus (RofC u) (Zof z) θ φ) =
      DommaschkQA2R.gradPart DommaschkQA2R.candidate (cylTorus (RofC u) (Zof z) θ φ) := by
    rw [DommaschkQA2R.field_split]; abel
  rw [e]
  exact DommaschkQA2R.hasFDerivAt_potential _ hx

/-- The torus is a `C²` map of the chart `ℝ²`. -/
theorem contDiff_torus :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => cylTorus (RofC u) (Zof z) p.1 p.2) := by
  have hR := contDiff_RofC h.ana_u
  have hZ := contDiff_Zof h.ana_z
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · exact hR.mul (Real.contDiff_cos.comp contDiff_snd)
  · exact hR.mul (Real.contDiff_sin.comp contDiff_snd)
  · exact hZ

/-- **`v = V ∘ K` is `C²`** on the chart. -/
theorem contDiff_torusPot : ContDiff ℝ 2 (torusPot Vdk (cylTorus (RofC u) (Zof z))) := by
  refine contDiff_iff_contDiffAt.2 fun p => ?_
  have hx : PlasmaLean.Fields.CylAlgebra.r2 (cylTorus (RofC u) (Zof z) p.1 p.2) ≠ 0 := by
    change PlasmaLean.Fields.CylAlgebra.r2 (cylPoint _ _ _) ≠ 0
    rw [cyl_r2_cylPoint]; exact pow_ne_zero _ (h.R_pos _ _).ne'
  exact (contDiffAt_Vdk hx).comp p h.contDiff_torus.contDiffAt

/-- `|B| ∘ K = √Q/R⁸` on the chart (strip form). -/
theorem torusModB_eq : torusModB Bdk (cylTorus (RofC u) (Zof z)) =
    fun p => Real.sqrt (Zof (qsQ (lvI u z)) p.1 p.2) / RofC u p.1 p.2 ^ 8 :=
  funext fun p => by
    change modB _ _ p.1 p.2 = _
    rw [h.modB_eq, h.lvA_R, h.Zof_Q]

/-- **`|B| ∘ K` is `C¹`** on the chart. -/
theorem contDiff_torusModB : ContDiff ℝ 1 (torusModB Bdk (cylTorus (RofC u) (Zof z))) := by
  rw [h.torusModB_eq]
  have hq : ∀ p : ℝ × ℝ, Zof (qsQ (lvI u z)) p.1 p.2 ≠ 0 := fun p => by
    rw [h.Zof_Q]; exact (h.Q_pos _ _).ne'
  exact (((contDiff_Zof h.ana_Q).sqrt hq).div ((contDiff_RofC h.ana_u).pow 8)
    fun p => pow_ne_zero _ (h.R_pos _ _).ne').of_le (by norm_num)

/-- **`|B| ∘ K` is doubly periodic** (`2π` in `θ`, `π` in `φ`). -/
theorem torusPeriodic_torusModB : TorusPeriodic 2 (torusModB Bdk (cylTorus (RofC u) (Zof z))) := by
  rw [h.torusModB_eq]
  refine ⟨fun p => ?_, fun p => ?_⟩
  · simp only [Prod.fst_add, Prod.snd_add, add_zero, RofC, Zof_add_two_pi]
  · simp only [Prod.fst_add, Prod.snd_add, add_zero, perPhi_two, RofC, Zof_add_pi]

/-- `a` is `π`-periodic in `φ`. -/
theorem boozerA_add_pi (θ φ : ℝ) :
    boozerA Bdk (cylTorus (RofC u) (Zof z)) θ (φ + Real.pi) =
      boozerA Bdk (cylTorus (RofC u) (Zof z)) θ φ := by
  rw [h.boozerA_eq, h.boozerA_eq, lvA_add_pi, Zof_add_pi, Zof_add_pi]

/-- `J` is `π`-periodic in `φ`. -/
theorem boozerJac_add_pi (θ φ : ℝ) :
    boozerJac Bdk ιA (cylTorus (RofC u) (Zof z)) θ (φ + Real.pi) =
      boozerJac Bdk ιA (cylTorus (RofC u) (Zof z)) θ φ := by
  rw [h.boozerJac_eq, h.boozerJac_eq, lvA_add_pi]

/-- The partial derivatives of `v`: `v_θ = a`, `v_φ = J − 1 − ι a`. -/
theorem fderiv_torusPot (θ φ : ℝ) :
    fderiv ℝ (torusPot Vdk (cylTorus (RofC u) (Zof z))) (θ, φ) (1, 0) =
        boozerA Bdk (cylTorus (RofC u) (Zof z)) θ φ ∧
      fderiv ℝ (torusPot Vdk (cylTorus (RofC u) (Zof z))) (θ, φ) (0, 1) =
        boozerJac Bdk ιA (cylTorus (RofC u) (Zof z)) θ φ - 1 -
          ιA * boozerA Bdk (cylTorus (RofC u) (Zof z)) θ φ := by
  have hv := (h.contDiff_torusPot.differentiable (by norm_num) (θ, φ)).hasFDerivAt
  obtain ⟨ha, hJ⟩ := boozerJac_eq_partials h.vacuumPotentialOn hv
    (h.hasDerivAt_torus_θ θ φ).differentiableAt (h.fieldTorus.differentiableAt_line θ φ)
    (h.R_pos θ φ)
  rw [← ha] at hJ
  exact ⟨ha.symm, by linarith⟩

/-- The torus is `2π`-periodic in `φ`. -/
theorem torus_add_two_pi (θ φ : ℝ) :
    cylTorus (RofC u) (Zof z) θ (φ + 2 * Real.pi) = cylTorus (RofC u) (Zof z) θ φ := by
  simp only [cylTorus, cylPoint, h.fieldTorus.per_φ_R, h.fieldTorus.per_φ_z, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

/-- **`v = V ∘ K` is `π`-periodic in `φ`** (from `v_θ = a`, `v_φ = J − 1 − ιa`, the
`π`-periodicity of `a` and `J`, and the `2π`-periodicity of `K`). -/
theorem torusPot_add_pi (θ φ : ℝ) :
    torusPot Vdk (cylTorus (RofC u) (Zof z)) (θ, φ + Real.pi) =
      torusPot Vdk (cylTorus (RofC u) (Zof z)) (θ, φ) := by
  set v := torusPot Vdk (cylTorus (RofC u) (Zof z)) with hvdef
  have hd : Differentiable ℝ v := h.contDiff_torusPot.differentiable (by norm_num)
  set c : ℝ × ℝ := (0, Real.pi)
  set w : ℝ × ℝ → ℝ := fun p => v (p + c) - v p with hwdef
  have hL : ∀ p : ℝ × ℝ, fderiv ℝ v (p + c) = fderiv ℝ v p := fun p => by
    obtain ⟨θ', φ'⟩ := p
    have e : (θ', φ') + c = (θ', φ' + Real.pi) := by simp [c]
    obtain ⟨a1, b1⟩ := h.fderiv_torusPot θ' (φ' + Real.pi)
    obtain ⟨a2, b2⟩ := h.fderiv_torusPot θ' φ'
    simp only [h.boozerA_add_pi, h.boozerJac_add_pi] at a1 b1
    rw [e]
    refine ContinuousLinearMap.ext fun q => ?_
    rw [clm_apply_pair, clm_apply_pair (fderiv ℝ v (θ', φ')), hvdef, a1, b1, a2, b2]
  have hw : ∀ p, HasFDerivAt w (0 : ℝ × ℝ →L[ℝ] ℝ) p := fun p => by
    have h1 := ((hd (p + c)).hasFDerivAt.comp p ((hasFDerivAt_id p).add_const c)).sub
      (hd p).hasFDerivAt
    rw [ContinuousLinearMap.comp_id, hL p, sub_self] at h1
    exact h1
  have hwd : Differentiable ℝ w := fun p => (hw p).differentiableAt
  have hw0 : ∀ p, fderiv ℝ w p = 0 := fun p => (hw p).fderiv
  have hconst := is_const_of_fderiv_eq_zero hwd hw0 (θ, φ) (θ, φ + Real.pi)
  have h2 : v (θ, φ + Real.pi + Real.pi) = v (θ, φ) := by
    have e : φ + Real.pi + Real.pi = φ + 2 * Real.pi := by ring
    simp only [hvdef, torusPot, e, h.torus_add_two_pi]
  have e1 : (θ, φ) + c = (θ, φ + Real.pi) := by simp [c]
  have e2 : (θ, φ + Real.pi) + c = (θ, φ + Real.pi + Real.pi) := by simp [c]
  simp only [hwdef, e1, e2, h2] at hconst
  linarith

/-- **`v = V ∘ K` is doubly periodic** (`2π` in `θ`, `π` in `φ`). -/
theorem torusPeriodic_torusPot : TorusPeriodic 2 (torusPot Vdk (cylTorus (RofC u) (Zof z))) := by
  refine ⟨fun p => ?_, fun p => ?_⟩
  · simp only [torusPot, Prod.fst_add, Prod.snd_add, add_zero, cylTorus, RofC, Zof_add_two_pi]
  · obtain ⟨θ, φ⟩ := p
    have e : (θ, φ) + (0, perPhi 2) = (θ, φ + Real.pi) := by simp [perPhi_two]
    rw [e, h.torusPot_add_pi]

/-! ### The sign of `B^φ` and the chart hypotheses -/

/-- **`B^φ > 0`** (as `B_φ > 0`) on the torus when `D = R⁷B_φ > 0` there. -/
theorem Bphi_pos (hD : ∀ θ φ, 0 < lvA u z θ φ 0) (θ φ : ℝ) :
    0 < cylBphi (RofC u θ φ) φ (Zof z θ φ) := by
  have h1 := hD θ φ
  rw [h.lvA_D] at h1
  exact pos_of_mul_pos_right h1 (pow_pos (h.R_pos θ φ) 7).le

/-- **`B^φ = B · ∇φ > 0`** on the torus when `D > 0` there. -/
theorem toroidalComp_pos (hD : ∀ θ φ, 0 < lvA u z θ φ 0) (θ φ : ℝ) :
    0 < toroidalComp Bdk (cylTorus (RofC u) (Zof z)) θ φ := by
  rw [h.toroidalComp_eq]
  exact div_pos (h.Bphi_pos hD θ φ) (h.R_pos θ φ)

/-- **`J > 0`** on the torus when `D > 0` there (`J = Q/(R⁸D)`). -/
theorem boozerJac_pos (hD : ∀ θ φ, 0 < lvA u z θ φ 0) (θ φ : ℝ) :
    0 < boozerJac Bdk ιA (cylTorus (RofC u) (Zof z)) θ φ := by
  rw [h.boozerJac_eq]
  exact div_pos (h.Q_pos θ φ) (mul_pos (pow_pos (h.lvA_R_pos θ φ) 8) (hD θ φ))

/-- **The hypotheses of the Wirtinger bound on the exact torus** (two field periods), given
`D > 0` on the torus. -/
theorem boozerChartHyp (hD : ∀ θ φ, 0 < lvA u z θ φ 0) :
    BoozerChartHyp 2 ιA (torusPot Vdk (cylTorus (RofC u) (Zof z)))
      (torusModB Bdk (cylTorus (RofC u) (Zof z))) :=
  BoozerChartHyp.of_torus (by norm_num) h.fieldTorus h.vacuumPotentialOn
    (fun θ φ => (h.hasDerivAt_torus_θ θ φ).differentiableAt) h.contDiff_torusPot
    h.torusPeriodic_torusPot h.contDiff_torusModB h.torusPeriodic_torusModB (h.boozerJac_pos hD)

end ExactTorusA

/-! ## Sanity -/

/-- **Sanity (accepted)**: `cos 2φ` has the two-field-period chart periodicity. -/
theorem torusPeriodic_cos_two : TorusPeriodic 2 (fun p : ℝ × ℝ => Real.cos (2 * p.2)) := by
  refine ⟨fun p => by simp, fun p => ?_⟩
  simp only [Prod.snd_add, perPhi_two, mul_add]
  rw [show 2 * Real.pi = (1 : ℕ) * (2 * Real.pi) by ring, Real.cos_add_nat_mul_two_pi]

/-- **Sanity (rejected)**: `cos 2φ` does not have the chart periodicity of four field periods
(`2π/4 = π/2`), so `TorusPeriodic N` really encodes the field-period number. -/
theorem not_torusPeriodic_four : ¬ TorusPeriodic 4 (fun p : ℝ × ℝ => Real.cos (2 * p.2)) := by
  intro hP
  have h1 := hP.phi (0, 0)
  have e : perPhi 4 = Real.pi / 2 := by rw [perPhi]; push_cast; ring
  simp only [Prod.mk_add_mk, add_zero, zero_add, e, mul_zero, Real.cos_zero] at h1
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi] at h1
  norm_num at h1

/-! ## The certified bounds of D4/D5 on the exact torus -/

/-- The leaf vector of D4/D5 is the leaf vector `lvI` of the identification. -/
theorem lvS_eq_lvI (u z : FA) : lvS u z = lvI u z := rfl

namespace ExactTorusA

variable {u z : FA} (h : ExactTorusA u z)
include h

/-- The D4/D5 bounds (`QSDefBounds`) hold on the exact torus. -/
theorem qsDefBounds : QSDefBounds u z :=
  qsd_bounds (by norm_num) le_rfl h.ana_u h.ana_z h.close


/-- **`D ≥ D_min = 0.1116 > 0`** on the exact torus (from `|D − c_D| ≤ e_D`). -/
theorem Dmin_le (θ φ : ℝ) : (Dminq : ℝ) ≤ lvA u z θ φ 0 := by
  have h3 := (h.qsDefBounds.pointwise θ (psi φ)).2.2
  have e : eval (lvS u z 0) θ (psi φ) = ((lvA u z θ φ 0 : ℝ) : ℂ) := h.eval_leaf 0 θ φ
  rw [e, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h3
  have hn : (Dminq : ℝ) ≤ cDq - eDq := by exact_mod_cast qsd_numbers.2.2.2.2.2.1
  linarith [(abs_le.1 h3).1]

/-- `D > 0` on the exact torus. -/
theorem D_pos (θ φ : ℝ) : 0 < lvA u z θ φ 0 :=
  lt_of_lt_of_le (by exact_mod_cast qsd_numbers.2.2.2.2.2.2.1) (h.Dmin_le θ φ)

/-- **`B_min² ≤ |B|²`** on the exact torus. -/
theorem Bmin_sq_le (θ φ : ℝ) :
    (Bminq : ℝ) ^ 2 ≤ qsQ (lvA u z θ φ) / lvA u z θ φ 12 ^ 16 := by
  have h2 := (h.qsDefBounds.pointwise θ (psi φ)).2.1.2
  have hR := h.lvA_R_pos θ φ
  have e : eval (qsQ (lvS u z)) θ (psi φ) / eval (lvS u z 12 ^ 16) θ (psi φ) =
      ((qsQ (lvA u z θ φ) / lvA u z θ φ 12 ^ 16 : ℝ) : ℂ) := by
    rw [lvS_eq_lvI, h.eval_Q, eval_pow', h.eval_leaf 12]
    push_cast; rfl
  rw [e, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h2
  have hn : (Bminq : ℝ) ^ 2 ≤ cBq - eBpq := by exact_mod_cast qsd_numbers.1
  linarith [(abs_le.1 h2).1]

/-- **`|B| ≥ B_min = 1.02656`** on the exact torus. -/
theorem Bmin_le (θ φ : ℝ) : (Bminq : ℝ) ≤ ‖Bdk (cylTorus (RofC u) (Zof z) θ φ)‖ := by
  have h1 := h.Bmin_sq_le θ φ
  rw [← h.normSq_eq] at h1
  have hb : (0 : ℝ) ≤ Bminq := by exact_mod_cast (show (0 : ℚ) ≤ Bminq by norm_num [Bminq])
  exact (pow_le_pow_iff_left₀ hb (norm_nonneg _) two_ne_zero).1 h1

/-- **The certified QA-defect bound on the exact torus**: `|torusQADefect| ≤ δ_∞ = 0.031258`. -/
theorem torusQADefectLe_delta :
    TorusQADefectLe Bdk ιA (cylTorus (RofC u) (Zof z)) (deltaq : ℝ) := fun θ φ => by
  rw [h.torusQADefect_eq]
  have h1 := (h.qsDefBounds.pointwise θ (psi φ)).1.2
  have hR := h.lvA_R_pos θ φ
  have hQ := h.Q_pos θ φ
  have e : eval (qsNg (lvS u z) iotaF (dTh u) (dTh z)) θ (psi φ) /
      eval (qsQ (lvS u z) * lvS u z 12 ^ 17) θ (psi φ) =
      ((ngA u z θ φ / (qsQ (lvA u z θ φ) * lvA u z θ φ 12 ^ 17) : ℝ) : ℂ) := by
    rw [lvS_eq_lvI, show iotaF = algebraMap ℂ FA (ιA : ℂ) from rfl, h.eval_Ng, eval_mul,
      h.eval_Q, eval_pow', h.eval_leaf 12]
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h1
  have hb : (0 : ℝ) < Bminq := by exact_mod_cast (show (0 : ℚ) < Bminq by norm_num [Bminq])
  have h3 := qsd_defect_real hR hQ hb h1 (h.Bmin_sq_le θ φ)
  have hn : (d1q : ℝ) / (2 * Bminq) ≤ deltaq := by exact_mod_cast qsd_numbers.2.1
  exact h3.trans hn

/-- `|torusQADefect| ≤ 0.032` on the exact torus. -/
theorem torusQADefectLe_032 : TorusQADefectLe Bdk ιA (cylTorus (RofC u) (Zof z)) (32 / 1000) :=
  fun θ φ => (h.torusQADefectLe_delta θ φ).trans
    (by
      have h3 : ((deltaq : ℚ) : ℝ) ≤ ((32 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr qsd_numbers.2.2.1
      push_cast at h3
      exact h3)

/-- **`B^φ > 0`** on the exact torus. -/
theorem toroidalComp_pos' (θ φ : ℝ) : 0 < toroidalComp Bdk (cylTorus (RofC u) (Zof z)) θ φ :=
  h.toroidalComp_pos h.D_pos θ φ

/-- **The chart hypotheses of the Wirtinger bound on the exact torus** (unconditional in the
torus): `BoozerChartHyp 2 ι_A (V ∘ K) (|B| ∘ K)`. -/
theorem boozerChartHyp' :
    BoozerChartHyp 2 ιA (torusPot Vdk (cylTorus (RofC u) (Zof z)))
      (torusModB Bdk (cylTorus (RofC u) (Zof z))) :=
  h.boozerChartHyp h.D_pos

/-- **The oracle-normalised Boozer defect of the exact torus** (sup route, N-34 §2(3)): for every
finite set `S` of half-lattice off-QA modes, `defect ≤ √2 δ_∞/(2 B_min)`. -/
theorem oracleDefect_le (S : Finset (ℤ × ℤ)) (hS : ∀ q ∈ S, OracleOffQA q) :
    oracleDefect 2 ιA (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (torusModB Bdk (cylTorus (RofC u) (Zof z))) S ≤
      Real.sqrt 2 * deltaq / ((2 : ℕ) * Bminq) :=
  (torus_oracleDefect_le h.fieldTorus h.vacuumPotentialOn
    (fun θ φ => (h.hasDerivAt_torus_θ θ φ).differentiableAt) h.boozerChartHyp'
    h.torusQADefectLe_delta (by exact_mod_cast (show (0 : ℚ) < Bminq by norm_num [Bminq]))
    h.Bmin_le S hS).2

end ExactTorusA

/-- **The QA defect on the certified Dommaschk torus A** (conditional only on the initial residual
bounds of the KAM iteration, as `dommaschk_iotaOnTorus`): there is an exact invariant torus with
rotational transform `ι_A` on which `|∂_{φ_B}|B|| ≤ 0.032`, `|B| ≥ 1.02656`, `B^φ > 0`, and the
chart hypotheses of the Wirtinger bound hold. -/
theorem dommaschkA_qaDefect
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ)) :
    ∃ R Z : ℝ → ℝ → ℝ, IotaOnTorus Bdk R Z ιA ∧
      TorusQADefectLe Bdk ιA (cylTorus R Z) (32 / 1000) ∧
      (∀ θ φ, (Bminq : ℝ) ≤ ‖Bdk (cylTorus R Z θ φ)‖) ∧
      (∀ θ φ, 0 < toroidalComp Bdk (cylTorus R Z) θ φ) ∧
      BoozerChartHyp 2 ιA (torusPot Vdk (cylTorus R Z)) (torusModB Bdk (cylTorus R Z)) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res e0R e0Z
  have h : ExactTorusA u z := ⟨hu, hz, hur, hzr, hR, hZ, hC⟩
  exact ⟨_, _, h.iotaOnTorus, h.torusQADefectLe_032, h.Bmin_le, h.toroidalComp_pos',
    h.boozerChartHyp'⟩

end PlasmaLean.Design.DommaschkKamA
