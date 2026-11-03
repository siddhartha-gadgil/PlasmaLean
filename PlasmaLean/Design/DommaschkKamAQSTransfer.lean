/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAQSDefOut
public import PlasmaLean.Theory.KAM.AnalyticComposition
public import PlasmaLean.Theory.KAM.StripEval

/-!
# The certified QA defect of Dommaschk torus A on every close torus (N-34, D4–D5)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamAQSTransfer` (after the admissibility chain
`Design/DommaschkKamAAdm`; the new modules take about 15 CPU-min on the laptop, peak 4.3 GB);
axioms are checked in `scripts/check_axioms_heavy.lean`.

**Main theorem `qsd_bounds`.** For every analytic torus `(u, z)` that is `μ`-close (`Close ρ ι_A`,
`ρ ≥ 0`, `μ ≤ 10⁻¹²`; only `u, z, ∂_θu, ∂_θz` are used) to the data torus `(u₀A, z₀A)` (strip
frame), with the leaf vector `l = lvS u z` (`D, D_u, D_z, D_φ, n_R, n_R,u, n_R,z, n_R,φ, n_z,
n_z,u, n_z,z, n_z,φ, R` evaluated at `xB u z`, the fields of `leavesAt (xB u z)` of
`Design/DommaschkKamCQSPoly`), the QA-defect numerator `N_g = qsNg l ι_A (∂_θu) (∂_θz)` and
`Q = qsQ l`, the structure `QSDefBounds u z` holds: with the fixed approximate inverses
`qGs ≈ 1/(Q R¹⁷)`, `qBs ≈ 1/R¹⁶`, `qDs ≈ 1/D` (rotated surrogate centres), in the `ℓ¹` norm of the
Fourier coefficients (`Bd 0`):
* `‖qGs N_g‖₀ ≤ η_G = 0.0641756`, `‖qGs Q R¹⁷ − 1‖₀ ≤ ε_G = 4.17e-06`;
* `‖Q qBs − c_B‖₀ ≤ e_B = 0.09016`, `‖qBs R¹⁶ − 1‖₀ ≤ ε_B = 2.33e-09` (`c_B = 1.14401`);
* `‖D − c_D‖₀ ≤ e_D = 0.5441` (`c_D = 0.655712`);
* `|⟨(qGs N_g)² R⁸ qDs⟩| ≤ m_F = 3.872e-05`, `‖qDs D − 1‖₀ ≤ ε_D = 4.02e-09`.

**Pointwise consequences** (`QSDefBounds.pointwise`, at every `(θ, ψ) ∈ ℝ²`, in `ℂ`):
`Q R¹⁷ ≠ 0` and `|N_g/(Q R¹⁷)| ≤ d₁ = 0.0641759` (`∂_{φ_B}|B|² = N_g/(Q R¹⁷)`);
`R¹⁶ ≠ 0` and `|Q/R¹⁶ − c_B| ≤ e_B'` (so `|B|² = Q/R¹⁶ ≥ B_min² `, `B_min = 1.02656`, at real
points); `|D − c_D| ≤ e_D` (so `D ≥ 0.1116 > 0`, i.e. `B_φ > 0` and `J > 0`). With
`qsd_defect_real` (`|N_g/(2Q√Q R⁹)| ≤ d₁/(2 B_min)` for real `N_g`, `Q, R > 0`,
`Q/R¹⁶ ≥ B_min²`): **`sup |torusQADefect| ≤ δ_∞ = 0.031258`** (`qsd_numbers`);
with `|ι_A| ≥ 1193/5000`: `κ = 2δ_∞/(B_min |ι|) ≤ 0.2552`, `δ_∞/|ι| ≤ 0.131`. `L²(J)`: pointwise
`4 g² J = F/((qG Q R¹⁷)²(qD D))` with `F = (qG N_g)² R⁸ qD ≥ 0`, so
`⟨g² J⟩ ≤ m_F/(4(1 − ε_G)²(1 − ε_D)) ≤ δ₂²` with **`δ₂ = 0.0031112`**; with the Wirtinger bound
of N-34 §2(3) the oracle-normalised defect is `≤ (√2/2) δ₂/(B_min |ι|) ≤ 0.008983`
(`qsd_numbers`).

**Route.** The chain (`Design/DommaschkKamAQSDefOut`: `surr_G`, …) gives the bounds at the
surrogate torus `(xA 4, xA 5)` (oracle frame). The closeness inputs are those of the
admissibility transfer (`dk_adm`): `‖uₒ − xA 4‖ ≤ μ + t_U`, … (tails `Bd_tg_U`, …). The leaves move
by their Lipschitz majorants (`fld_D`, …, and `fldQ` for the new leaves, `lipQ`), the program by
the majorant derivative of its polynomial expression (`Bd.eval_add_sub` on `qsdToC peNg`, the
rational mirror `qsdMj`, kernel-checked), the approximate inverses by `approx_near`, and
`ι_A − ι_q` by `iotaqA_close`. The strip frame is reached by `rotψ`.

**Sanity.** `qsdMj_const` (degenerate), `eval_peQ_instance` (concrete), `qsd_numbers` (the
accepted values) and `qsd_not_tiny` (rejected: the certified numbers do not prove a defect below
`10⁻³`, consistent with `surr_G_ne`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam
  PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall
  WEll1Z2 Complex

/-! ## Rational majorants of polynomial expressions -/

/-- A rational polynomial expression read with complex constants. -/
def qsdToC {σ : Type*} : PolyExpr ℚ σ → PolyExpr ℂ σ
  | .const c => .const (c : ℂ)
  | .var i => .var i
  | .add p q => .add (qsdToC p) (qsdToC q)
  | .sub p q => .sub (qsdToC p) (qsdToC q)
  | .mul p q => .mul (qsdToC p) (qsdToC q)

/-- The pair `(P̂(a), P̂'(a)·b)` with rational data (kernel-computable mirror of `PolyExpr.maj`,
`PolyExpr.majD`). -/
def qsdMj {σ : Type*} (a b : σ → ℚ) : PolyExpr ℚ σ → ℚ × ℚ
  | .const c => (|c|, 0)
  | .var i => (a i, b i)
  | .add p q => ((qsdMj a b p).1 + (qsdMj a b q).1, (qsdMj a b p).2 + (qsdMj a b q).2)
  | .sub p q => ((qsdMj a b p).1 + (qsdMj a b q).1, (qsdMj a b p).2 + (qsdMj a b q).2)
  | .mul p q => ((qsdMj a b p).1 * (qsdMj a b q).1,
      (qsdMj a b p).2 * (qsdMj a b q).1 + (qsdMj a b p).1 * (qsdMj a b q).2)

/-- **The rational mirror is the real majorant.** -/
theorem qsdMj_spec {σ : Type*} (a b : σ → ℚ) (e : PolyExpr ℚ σ) :
    PolyExpr.maj (fun i => ((a i : ℚ) : ℝ)) (qsdToC e) = ((qsdMj a b e).1 : ℝ) ∧
      PolyExpr.majD (fun i => ((a i : ℚ) : ℝ)) (fun i => ((b i : ℚ) : ℝ)) (qsdToC e) =
        ((qsdMj a b e).2 : ℝ) := by
  induction e with
  | const c =>
    refine ⟨?_, ?_⟩
    · simp only [qsdToC, qsdMj, PolyExpr.maj, Complex.norm_ratCast]; push_cast; rfl
    · simp [qsdToC, qsdMj, PolyExpr.majD]
  | var i => exact ⟨rfl, rfl⟩
  | add p q hp hq =>
    simp only [qsdToC, qsdMj, PolyExpr.maj, PolyExpr.majD, hp.1, hp.2, hq.1, hq.2]; push_cast
    exact ⟨rfl, rfl⟩
  | sub p q hp hq =>
    simp only [qsdToC, qsdMj, PolyExpr.maj, PolyExpr.majD, hp.1, hp.2, hq.1, hq.2]; push_cast
    exact ⟨rfl, rfl⟩
  | mul p q hp hq =>
    simp only [qsdToC, qsdMj, PolyExpr.maj, PolyExpr.majD, hp.1, hp.2, hq.1, hq.2]; push_cast
    exact ⟨rfl, rfl⟩

/-- **Sanity (degenerate)**: a constant has majorant `|c|` and no derivative. -/
theorem qsdMj_const {σ : Type*} (a b : σ → ℚ) (c : ℚ) : qsdMj a b (.const c) = (|c|, 0) := rfl

/-! ## The program as polynomial expressions in 16 variables

Variables: the 13 leaves (`QSLeaves` order), then `ι` (13), `u_θ` (14), `z_θ` (15). -/

/-- `Q`. -/
def peQ : PolyExpr ℚ (Fin 16) :=
  .add (.add (.mul (.var 4) (.var 4)) (.mul (.mul (.var 12) (.var 12)) (.mul (.var 0) (.var 0))))
    (.mul (.var 8) (.var 8))
/-- `Q_u`. -/
def peQu : PolyExpr ℚ (Fin 16) :=
  .mul (.const 2) (.add (.add (.add (.mul (.var 4) (.var 5))
    (.mul (.var 12) (.mul (.var 0) (.var 0)))) (.mul (.mul (.var 12) (.var 12))
    (.mul (.var 0) (.var 1)))) (.mul (.var 8) (.var 9)))
/-- `Q_z`. -/
def peQz : PolyExpr ℚ (Fin 16) :=
  .mul (.const 2) (.add (.add (.mul (.var 4) (.var 6)) (.mul (.mul (.var 12) (.var 12))
    (.mul (.var 0) (.var 2)))) (.mul (.var 8) (.var 10)))
/-- `Q_φ`. -/
def peQf : PolyExpr ℚ (Fin 16) :=
  .mul (.const 2) (.add (.add (.mul (.var 4) (.var 7)) (.mul (.mul (.var 12) (.var 12))
    (.mul (.var 0) (.var 3)))) (.mul (.var 8) (.var 11)))
/-- `P_L`. -/
def pePL : PolyExpr ℚ (Fin 16) :=
  .add (.add (.mul peQu (.var 4)) (.mul peQz (.var 8))) (.mul (.var 0) peQf)
/-- `M_L`. -/
def peML : PolyExpr ℚ (Fin 16) := .sub (.mul (.var 12) pePL) (.mul (.mul (.const 16) peQ) (.var 4))
/-- `R⁸`. -/
def peR8 : PolyExpr ℚ (Fin 16) :=
  .mul (.mul (.mul (.mul (.mul (.mul (.mul (.var 12) (.var 12)) (.var 12)) (.var 12)) (.var 12))
    (.var 12)) (.var 12)) (.var 12)
/-- `N₀`. -/
def peN0 : PolyExpr ℚ (Fin 16) := .mul peR8 peML
/-- `N₁`. -/
def peN1 : PolyExpr ℚ (Fin 16) :=
  .sub (.mul (.var 4) peML) (.mul peQ (.sub (.mul (.var 12) peQu) (.mul (.const 16) peQ)))
/-- `N₂`. -/
def peN2 : PolyExpr ℚ (Fin 16) := .sub (.mul (.var 8) peML) (.mul (.mul (.var 12) peQ) peQz)
/-- **`N_g`.** -/
def peNg : PolyExpr ℚ (Fin 16) :=
  .add peN0 (.mul (.var 13) (.add (.mul peN1 (.var 14)) (.mul peN2 (.var 15))))

/-- The 16 variables. -/
def v16 (l : Fin 13 → FA) (ι uθ zθ : FA) : Fin 16 → FA :=
  ![l 0, l 1, l 2, l 3, l 4, l 5, l 6, l 7, l 8, l 9, l 10, l 11, l 12, ι, uθ, zθ]

section EvalPE

variable (l : Fin 13 → FA) (ι uθ zθ : FA)

/-- The expression of `Q` evaluates to the program. -/
theorem eval_peQ : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peQ) = qsQ l := by
  simp [peQ, qsdToC, PolyExpr.eval, v16, qsQ]; ring

/-- The expression of `Q_u` evaluates to the program. -/
theorem eval_peQu : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peQu) = qsQu l := by
  simp [peQu, qsdToC, PolyExpr.eval, v16, qsQu, map_ofNat]; ring

/-- The expression of `Q_z` evaluates to the program. -/
theorem eval_peQz : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peQz) = qsQz l := by
  simp [peQz, qsdToC, PolyExpr.eval, v16, qsQz, map_ofNat]; ring

/-- The expression of `Q_φ` evaluates to the program. -/
theorem eval_peQf : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peQf) = qsQf l := by
  simp [peQf, qsdToC, PolyExpr.eval, v16, qsQf, map_ofNat]; ring

/-- The expression of `P_L` evaluates to the program. -/
theorem eval_pePL : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC pePL) = qsPL l := by
  simp only [pePL, qsdToC, PolyExpr.eval, eval_peQu, eval_peQz, eval_peQf, qsPL]
  simp [v16]

/-- The expression of `M_L` evaluates to the program. -/
theorem eval_peML : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peML) = qsML l := by
  simp only [peML, qsdToC, PolyExpr.eval, eval_pePL, eval_peQ, qsML]
  simp [v16, map_ofNat]

/-- The expression of `N₀` evaluates to the program. -/
theorem eval_peN0 : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peN0) = qsN0 l := by
  simp only [peN0, peR8, qsdToC, PolyExpr.eval, eval_peML, qsN0]
  simp [v16]; ring

/-- The expression of `N₁` evaluates to the program. -/
theorem eval_peN1 : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peN1) = qsN1 l := by
  simp only [peN1, qsdToC, PolyExpr.eval, eval_peML, eval_peQ, eval_peQu, qsN1]
  simp [v16, map_ofNat]

/-- The expression of `N₂` evaluates to the program. -/
theorem eval_peN2 : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peN2) = qsN2 l := by
  simp only [peN2, qsdToC, PolyExpr.eval, eval_peML, eval_peQ, eval_peQz, qsN2]
  simp [v16]

/-- **The polynomial expression of the numerator evaluates to `qsNg`.** -/
theorem eval_peNg : PolyExpr.eval (v16 l ι uθ zθ) (qsdToC peNg) = qsNg l ι uθ zθ := by
  simp only [peNg, qsdToC, PolyExpr.eval, eval_peN0, eval_peN1, eval_peN2, qsNg]
  simp [v16]

end EvalPE

/-- **Sanity (concrete)**: `Q` at `n_R = R = D = 1` (other leaves `0`) is `2`. -/
theorem eval_peQ_instance :
    PolyExpr.eval (v16 ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1] 0 0 0) (qsdToC peQ) = 2 := by
  rw [eval_peQ]; norm_num [qsQ]

/-! ## The constants of the transfer (validated in exact arithmetic by the generator) -/

/-- Lipschitz majorant of `D_φ`. -/
def dlDf : ℚ := (10969 / 10 ^ 13 : ℚ)
/-- Lipschitz majorant of `n_{R,φ}`. -/
def dlnRf : ℚ := (22637 / 10 ^ 13 : ℚ)
/-- Lipschitz majorant of `n_{z,φ}`. -/
def dlnZf : ℚ := (1137 / 500000000000 : ℚ)
/-- The deviation bound of `N_g`. -/
def dNgq : ℚ := (293 / 4000000000 : ℚ)
/-- The deviation bound of `Q`. -/
def dQq : ℚ := (4677 / 5000000000000 : ℚ)
/-- `η_G`: the bound of `qG N_g` at every close torus. -/
def etaGq : ℚ := (160439 / 2500000 : ℚ)
/-- `ε_G`: the bound of `qG Q R¹⁷ − 1`. -/
def epsGq : ℚ := (4169 / 10 ^ 9 : ℚ)
/-- `e_B`: the bound of `Q qB − c_B`. -/
def eBq : ℚ := (1127 / 12500 : ℚ)
/-- `ε_B`: the bound of `qB R¹⁶ − 1`. -/
def epsBq : ℚ := (4669 / 2000000000000 : ℚ)
/-- `e_D`: the bound of `D − c_D`. -/
def eDq : ℚ := (5441 / 10 ^ 4 : ℚ)
/-- `m_F`: the bound of `|⟨(qG N_g)² R⁸ qD⟩|`. -/
def mFq : ℚ := (387169 / 10 ^ 10 : ℚ)
/-- `ε_D`: the bound of `qD D − 1`. -/
def epsDq : ℚ := (20079 / 5000000000000 : ℚ)

/-- The bounds of the 16 variables at the surrogate. -/
def aV : Fin 16 → ℚ := ![BA 106 + EA 106, BA 115 + EA 115, BA 123 + EA 123, BQ 204 + EQ 204,
  BA 133 + EA 133, BA 143 + EA 143, BA 151 + EA 151, BQ 214 + EQ 214, BA 159 + EA 159,
  BA 167 + EA 167, BA 173 + EA 173, BQ 222 + EQ 222, BA 10 + EA 10, 2387 / 10000, BA 6, BA 7]

/-- The deviations of the 16 variables. -/
def bV : Fin 16 → ℚ := ![dlD, dlDu, dlDz, dlDf, dlnR, dlnRu, dlnRz, dlnRf, dlnZ, dlnZu, dlnZz,
  dlnZf, muq + tU, 0, muq + tAU, muq + tAZ]

/-- The strip-algebra `ι_A`. -/
def iotaF : FA := algebraMap ℂ FA ((DommaschkKamDio.dkIotaA : ℝ) : ℂ)

/-! ## The new leaves near the surrogate -/

/-- **The deviation of a new leaf** (Lipschitz majorant, angle variables fixed). -/
theorem fldQ {p : DkPoly.SP} {dl : ℚ}
    (hdl : lipQ (BA 4) (BA 5) (muq + tU) (muq + tZ) ((68553 : ℕ) / 2 ^ 16) p ≤ dl) {uo zo : FA}
    (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ)) (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd 0 (Fo p uo zo - Fo p (xA 4) (xA 5)) (dl : ℝ) := by
  have h := Bd_ev_sub (x := xBo (xA 4) (xA 5)) (y := xBo uo zo) le_rfl rfl rfl
    (normA hq0A 4 (by norm_num)) (normA hq0A 5 (by norm_num)) hU hZ (Bd_cSo_q hq0A)
    (Bd_sSo_q hq0A) p
  rw [lipR_cast] at h
  exact h.le (qleA hdl)

set_option maxRecDepth 100000 in
/-- The deviation of `D_φ`. -/
theorem fld_Df {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd 0 (Fo dDf uo zo - Fo dDf (xA 4) (xA 5)) (dlDf : ℝ) := fldQ (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The deviation of `n_{R,φ}`. -/
theorem fld_nRf {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd 0 (Fo dnRf uo zo - Fo dnRf (xA 4) (xA 5)) (dlnRf : ℝ) := fldQ (by kernel_fact) hU hZ

set_option maxRecDepth 100000 in
/-- The deviation of `n_{z,φ}`. -/
theorem fld_nZf {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ)) :
    Bd 0 (Fo dnZf uo zo - Fo dnZf (xA 4) (xA 5)) (dlnZf : ℝ) := fldQ (by kernel_fact) hU hZ

/-! ## The transfer in the oracle frame -/

set_option linter.style.longLine false in
/-- The surrogate variables are bounded by `aV`. -/
theorem hx16 : ∀ i, Bd 0 (v16 lS iotaF (xA 6) (xA 7) i) ((aV i : ℚ) : ℝ) := by
  have sA0 := fun k (hk : k < 195) => sA le_rfl hq0A k hk
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := lS_vals
  intro i
  fin_cases i
  · simp only [v16, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, aV, Rat.cast_add]; rw [h0]; exact_mod_cast sA0 106 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h1]; exact_mod_cast sA0 115 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h2]; exact_mod_cast sA0 123 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h3]; exact_mod_cast valQ_le 204 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h4]; exact_mod_cast sA0 133 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h5]; exact_mod_cast sA0 143 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h6]; exact_mod_cast sA0 151 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h7]; exact_mod_cast valQ_le 214 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h8]; exact_mod_cast sA0 159 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h9]; exact_mod_cast sA0 167 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h10]; exact_mod_cast sA0 173 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h11]; exact_mod_cast valQ_le 222 (by norm_num)
  · simp only [v16, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, aV, Rat.cast_add]
    rw [h12]; exact_mod_cast sA0 10 (by norm_num)
  · change Bd 0 iotaF ((2387 / 10000 : ℚ) : ℝ)
    refine (Bd_algebraMap 0 _).le ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact dkIotaA_abs_le
  · change Bd 0 (xA 6) ((BA 6 : ℚ) : ℝ); exact normA hq0A 6 (by norm_num)
  · change Bd 0 (xA 7) ((BA 7 : ℚ) : ℝ); exact normA hq0A 7 (by norm_num)

/-- The leaf `R` moves with `u`. -/
theorem RofG_sub (uo : FA) : RofG dkR0 uo - RofG dkR0 (xA 4) = uo - xA 4 := by
  simp only [RofG]; ring

set_option maxRecDepth 100000 in
/-- The deviations of the 16 variables between a close torus and the surrogate. -/
theorem hh16 {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ))
    (hA : Bd 0 (dTh uo - xA 6) ((muq + tAU : ℚ) : ℝ))
    (hB : Bd 0 (dTh zo - xA 7) ((muq + tAZ : ℚ) : ℝ)) :
    ∀ i, Bd 0 ((fun i => v16 (lvO uo zo) iotaF (dTh uo) (dTh zo) i -
      v16 lS iotaF (xA 6) (xA 7) i) i) ((bV i : ℚ) : ℝ) := by
  intro i
  fin_cases i
  · exact (fld_D le_rfl hq0A hU hZ).1
  · exact (fld_Du le_rfl hq0A hU hZ).1
  · exact (fld_Dz le_rfl hq0A hU hZ).1
  · exact fld_Df hU hZ
  · exact (fld_nR le_rfl hq0A hU hZ).1
  · exact (fld_nRu le_rfl hq0A hU hZ).1
  · exact (fld_nRz le_rfl hq0A hU hZ).1
  · exact fld_nRf hU hZ
  · exact (fld_nZ le_rfl hq0A hU hZ).1
  · exact (fld_nZu le_rfl hq0A hU hZ).1
  · exact (fld_nZz le_rfl hq0A hU hZ).1
  · exact fld_nZf hU hZ
  · change Bd 0 (RofG dkR0 uo - RofG dkR0 (xA 4)) _
    rw [RofG_sub]; exact hU
  · change Bd 0 (iotaF - iotaF) _
    rw [sub_self]; exact (Bd_zero 0).le (by norm_num [bV])
  · exact hA
  · exact hB

/-- The program moves by its majorant derivative. -/
theorem pe_near {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
    (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ))
    (hA : Bd 0 (dTh uo - xA 6) ((muq + tAU : ℚ) : ℝ))
    (hB : Bd 0 (dTh zo - xA 7) ((muq + tAZ : ℚ) : ℝ)) (e : PolyExpr ℚ (Fin 16)) :
    Bd 0 (PolyExpr.eval (v16 (lvO uo zo) iotaF (dTh uo) (dTh zo)) (qsdToC e) -
      PolyExpr.eval (v16 lS iotaF (xA 6) (xA 7)) (qsdToC e)) ((qsdMj (aV + bV) bV e).2 : ℝ) := by
  have h := Bd.eval_add_sub le_rfl hx16 (hh16 hU hZ hA hB) (qsdToC e)
  rw [show (v16 lS iotaF (xA 6) (xA 7) + fun i => v16 (lvO uo zo) iotaF (dTh uo) (dTh zo) i -
      v16 lS iotaF (xA 6) (xA 7) i) = v16 (lvO uo zo) iotaF (dTh uo) (dTh zo) by
    funext i; simp,
    show ((fun i => ((aV i : ℚ) : ℝ)) + fun i => ((bV i : ℚ) : ℝ)) =
      fun i => (((aV + bV) i : ℚ) : ℝ) by funext i; simp,
    (qsdMj_spec (aV + bV) bV e).2] at h
  exact h

/-- `‖ι_A − ι_q‖ ≤ 2^{−128}`. -/
theorem Bd_iota_sub : Bd 0 (iotaF - iotaqF) ((1 / 2 ^ 128 : ℚ) : ℝ) := by
  rw [iotaF, iotaqF, ← map_sub]
  refine (Bd_algebraMap 0 _).le ?_
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have := iotaqA_close
  simp only [Qc] at this
  push_cast
  exact this

section Near

variable {uo zo : FA} (hU : Bd 0 (uo - xA 4) ((muq + tU : ℚ) : ℝ))
  (hZ : Bd 0 (zo - xA 5) ((muq + tZ : ℚ) : ℝ))
  (hA : Bd 0 (dTh uo - xA 6) ((muq + tAU : ℚ) : ℝ))
  (hB : Bd 0 (dTh zo - xA 7) ((muq + tAZ : ℚ) : ℝ))

include hU hZ hA hB in
/-- The deviation of the numerator. -/
theorem qsd_dNg : Bd 0 (qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) -
    qsNg lS iotaF (xA 6) (xA 7)) (dNgq : ℝ) := by
  have h := pe_near hU hZ hA hB peNg
  rw [eval_peNg, eval_peNg] at h
  exact h.le (qleA (by kernel_fact))

include hU hZ hA hB in
/-- The deviation of `Q`. -/
theorem qsd_dQ : Bd 0 (qsQ (lvO uo zo) - qsQ lS) (dQq : ℝ) := by
  have h := pe_near hU hZ hA hB peQ
  rw [eval_peQ, eval_peQ] at h
  exact h.le (qleA (by kernel_fact))

include hU in
/-- The deviation of `R`. -/
theorem qsd_dR : Bd 0 (lvO uo zo 12 - lS 12) ((muq + tU : ℚ) : ℝ) := by
  change Bd 0 (RofG dkR0 uo - RofG dkR0 (xA 4)) _
  rw [RofG_sub]; exact hU

/-- The bound of `R` at the surrogate. -/
theorem qsd_bR : Bd 0 (lS 12) ((BA 10 + EA 10 : ℚ) : ℝ) := by
  rw [lS12]; exact sA le_rfl hq0A 10 (by norm_num)

/-- The bound of `Q` at the surrogate. -/
theorem qsd_bQS : Bd 0 (qsQ lS) ((BQ 226 + EQ 226 : ℚ) : ℝ) := by
  rw [← Qnq_eq]; exact valQ_le 226 (by norm_num)

set_option linter.style.longLine false in
include hU hZ hA hB in
/-- The deviation of `qG N_g` from the surrogate value with `ι_q`. -/
theorem qsd_dG : Bd 0 (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) -
    xQ 238 * qsNg lS iotaqF (xA 6) (xA 7))
    (((1 / 2 ^ 128 : ℚ) : ℝ) * (((557473 / 5000000 : ℚ) : ℚ) : ℝ) + ((BQ 238 : ℚ) : ℝ) * (dNgq : ℝ)) := by
  have eNg : xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) =
      xQ 238 * qsNg lS iotaqF (xA 6) (xA 7) +
        ((iotaF - iotaqF) * (xQ 238 * (qsN1 lS * xA 6 + qsN2 lS * xA 7)) +
        xQ 238 * (qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) - qsNg lS iotaF (xA 6) (xA 7))) := by
    simp only [qsNg]; ring
  rw [eNg, add_sub_cancel_left]
  exact (Bd_iota_sub.mul le_rfl surr_GI).add ((normQ 238 (by norm_num)).mul le_rfl
    (qsd_dNg hU hZ hA hB))

set_option linter.style.longLine false in
include hU hZ hA hB in
/-- **`qG N_g` at the torus.** -/
theorem qsd_hG : Bd 0 (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) (etaGq : ℝ) := by
  have h := Bd_near surr_G (qsd_dG hU hZ hA hB)
  refine h.le ?_
  have := qleA (show ((801563 / 12500000 : ℚ) : ℚ) + (1 / 2 ^ 128 * (557473 / 5000000 : ℚ) + BQ 238 * dNgq) ≤ etaGq by kernel_fact)
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
include hU hZ hA hB in
/-- **The approximate inverse of `Q R¹⁷` at the torus.** -/
theorem qsd_heG : Bd 0 (xQ 238 * (qsQ (lvO uo zo) * lvO uo zo 12 ^ 17) - 1) (epsGq : ℝ) := by
  have hR := qsd_dR (zo := zo) hU
  have bRE := Bd_near qsd_bR hR
  have dR17 := Bd_pow_sub le_rfl qsd_bR hR 17
  have dQR := ((qsd_dQ hU hZ hA hB).mul le_rfl (bRE.pow le_rfl 17)).add (qsd_bQS.mul le_rfl dR17)
  rw [show (qsQ (lvO uo zo) - qsQ lS) * lvO uo zo 12 ^ 17 + qsQ lS * (lvO uo zo 12 ^ 17 -
    lS 12 ^ 17) = qsQ (lvO uo zo) * lvO uo zo 12 ^ 17 - qsQ lS * lS 12 ^ 17 by ring] at dQR
  have h := surr_eG.add ((normQ 238 (by norm_num)).mul le_rfl dQR)
  rw [show xQ 238 * (qsQ lS * lS 12 ^ 17) - 1 + xQ 238 * (qsQ (lvO uo zo) * lvO uo zo 12 ^ 17 -
    qsQ lS * lS 12 ^ 17) = xQ 238 * (qsQ (lvO uo zo) * lvO uo zo 12 ^ 17) - 1 by ring] at h
  refine h.le ?_
  have := qleA (show ((110727 / 50000000000 : ℚ) : ℚ) + BQ 238 * (dQq * ((BA 10 + EA 10) + (muq + tU)) ^ 17 +
    (BQ 226 + EQ 226) * (((BA 10 + EA 10) + (muq + tU)) ^ 17 - (BA 10 + EA 10) ^ 17)) ≤ epsGq by
    kernel_fact)
  exact_mod_cast this

include hU hZ hA hB in
/-- **`|B|²` at the torus.** -/
theorem qsd_hB : Bd 0 (qsQ (lvO uo zo) * xQ 241 - cBF) (eBq : ℝ) := by
  have h := surr_bB.add ((qsd_dQ hU hZ hA hB).mul le_rfl (normQ 241 (by norm_num)))
  rw [show qsQ lS * xQ 241 - cBF + (qsQ (lvO uo zo) - qsQ lS) * xQ 241 =
    qsQ (lvO uo zo) * xQ 241 - cBF by ring] at h
  refine h.le ?_
  have := qleA (show ((387202000 : ℚ) : ℚ) / 2 ^ 32 + dQq * BQ 241 ≤ eBq by kernel_fact)
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
include hU in
/-- **The approximate inverse of `R¹⁶` at the torus.** -/
theorem qsd_heB : Bd 0 (xQ 241 * lvO uo zo 12 ^ 16 - 1) (epsBq : ℝ) := by
  have h := surr_eB.add ((normQ 241 (by norm_num)).mul le_rfl
    (Bd_pow_sub le_rfl qsd_bR (qsd_dR (zo := zo) hU) 16))
  rw [show xQ 241 * lS 12 ^ 16 - 1 + xQ 241 * (lvO uo zo 12 ^ 16 - lS 12 ^ 16) =
    xQ 241 * lvO uo zo 12 ^ 16 - 1 by ring] at h
  refine h.le ?_
  have := qleA (show ((374733 / 2500000000000000 : ℚ) : ℚ) + BQ 241 * (((BA 10 + EA 10) + (muq + tU)) ^ 16 -
    (BA 10 + EA 10) ^ 16) ≤ epsBq by kernel_fact)
  exact_mod_cast this

set_option linter.style.longLine false in
include hU hZ in
/-- **`D` at the torus.** -/
theorem qsd_hD : Bd 0 (lvO uo zo 0 - cDF) (eDq : ℝ) := by
  have h := surr_dM.add (fld_D le_rfl hq0A hU hZ).1
  rw [show lS 0 - cDF + (Fo dD uo zo - Fo dD (xA 4) (xA 5)) = lvO uo zo 0 - cDF by
    rw [show Fo dD (xA 4) (xA 5) = lS 0 from rfl, show Fo dD uo zo = lvO uo zo 0 from rfl]; ring] at h
  refine h.le ?_
  have := qleA (show ((2336851000 : ℚ) : ℚ) / 2 ^ 32 + dlD ≤ eDq by kernel_fact)
  push_cast at this ⊢
  linarith

include hU hZ in
/-- **The approximate inverse of `D` at the torus.** -/
theorem qsd_heD : Bd 0 (xA 186 * lvO uo zo 0 - 1) (epsDq : ℝ) := by
  have h0 : Bd 0 (xA iqD * Fo dD (xA 4) (xA 5) - 1) ((epsD : ℚ) : ℝ) := by
    have h := nA_eD le_rfl hq0A
    rw [eval_eD] at h
    exact h
  have h := h0.add ((normA hq0A 186 (by norm_num)).mul le_rfl (fld_D le_rfl hq0A hU hZ).1)
  rw [show xA iqD * Fo dD (xA 4) (xA 5) - 1 + xA 186 * (Fo dD uo zo - Fo dD (xA 4) (xA 5)) =
    xA 186 * lvO uo zo 0 - 1 by rw [show Fo dD uo zo = lvO uo zo 0 from rfl]; ring] at h
  refine h.le ?_
  have := qleA (show epsD + BA 186 * dlD ≤ epsDq by kernel_fact)
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
include hU hZ hA hB in
/-- **The `L²(J)` integrand at the torus.** -/
theorem qsd_hF : ‖avg ((xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 *
    (lvO uo zo 12 ^ 8 * xA 186))‖ ≤ (mFq : ℝ) := by
  have dG := qsd_dG hU hZ hA hB
  have bGS : Bd 0 (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) (((801563 / 12500000 : ℚ) : ℚ) : ℝ) := surr_G
  have dG2 := dG.mul le_rfl ((bGS.add bGS).add dG)
  rw [show (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) -
      xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) * (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7) +
      xQ 238 * qsNg lS iotaqF (xA 6) (xA 7) + (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo) -
      xQ 238 * qsNg lS iotaqF (xA 6) (xA 7))) =
      (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 -
      (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 by ring] at dG2
  have bGG : Bd 0 ((xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2) ((BQ 242 + EQ 242 : ℚ) : ℝ) := by
    have h := valQ_le 242 (by norm_num)
    rw [show XQ 242 = GGq from rfl, GGq, Gq_eq] at h
    rw [pow_two]; exact h
  have bH : Bd 0 (lS 12 ^ 8 * xA 186) ((BQ 243 + EQ 243 : ℚ) : ℝ) := by
    have h := valQ_le 243 (by norm_num)
    rw [show XQ 243 = H8q from rfl, H8q, XA_R8, ← lS12, show XA 186 = xA 186 from rfl] at h
    exact h
  have dH := (Bd_pow_sub le_rfl qsd_bR (qsd_dR (zo := zo) hU) 8).mul le_rfl (normA hq0A 186 (by norm_num))
  rw [show (lvO uo zo 12 ^ 8 - lS 12 ^ 8) * xA 186 = lvO uo zo 12 ^ 8 * xA 186 -
    lS 12 ^ 8 * xA 186 by ring] at dH
  have dF := (dG2.mul le_rfl (Bd_near bH dH)).add (bGG.mul le_rfl dH)
  rw [show ((xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 -
      (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2) * (lvO uo zo 12 ^ 8 * xA 186) +
      (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 * (lvO uo zo 12 ^ 8 * xA 186 -
      lS 12 ^ 8 * xA 186) = (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 *
      (lvO uo zo 12 ^ 8 * xA 186) - (xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 *
      (lS 12 ^ 8 * xA 186) by ring] at dF
  have h1 := dF.norm_avg_le le_rfl
  rw [avg_sub] at h1
  have h2 := surr_F
  have h3 := norm_sub_norm_le (avg ((xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 *
      (lvO uo zo 12 ^ 8 * xA 186))) (avg ((xQ 238 * qsNg lS iotaqF (xA 6) (xA 7)) ^ 2 *
      (lS 12 ^ 8 * xA 186)))
  have := qleA (show ((321161 / 10 ^ 10 : ℚ) : ℚ) + ((1 / 2 ^ 128 * (557473 / 5000000 : ℚ) + BQ 238 * dNgq) *
    (2 * (801563 / 12500000 : ℚ) + (1 / 2 ^ 128 * (557473 / 5000000 : ℚ) + BQ 238 * dNgq)) *
    ((BQ 243 + EQ 243) + (((BA 10 + EA 10) + (muq + tU)) ^ 8 - (BA 10 + EA 10) ^ 8) * BA 186) +
    (BQ 242 + EQ 242) * ((((BA 10 + EA 10) + (muq + tU)) ^ 8 - (BA 10 + EA 10) ^ 8) * BA 186))
    ≤ mFq by kernel_fact)
  push_cast at this h1 h2 ⊢
  linarith

include hU hZ hA hB in
/-- **The QA-defect bounds at every torus near the surrogate** (oracle frame, strip `0`). -/
theorem qsd_near :
    Bd 0 (xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) (etaGq : ℝ) ∧
      Bd 0 (xQ 238 * (qsQ (lvO uo zo) * lvO uo zo 12 ^ 17) - 1) (epsGq : ℝ) ∧
      Bd 0 (qsQ (lvO uo zo) * xQ 241 - cBF) (eBq : ℝ) ∧
      Bd 0 (xQ 241 * lvO uo zo 12 ^ 16 - 1) (epsBq : ℝ) ∧
      Bd 0 (lvO uo zo 0 - cDF) (eDq : ℝ) ∧
      ‖avg ((xQ 238 * qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) ^ 2 *
        (lvO uo zo 12 ^ 8 * xA 186))‖ ≤ (mFq : ℝ) ∧
      Bd 0 (xA 186 * lvO uo zo 0 - 1) (epsDq : ℝ) :=
  ⟨qsd_hG hU hZ hA hB, qsd_heG hU hZ hA hB, qsd_hB hU hZ hA hB, qsd_heB hU, qsd_hD hU hZ,
    qsd_hF hU hZ hA hB, qsd_heD hU hZ⟩

end Near

/-! ## The strip frame -/

/-- The leaf vector at a torus `(u, z)` in the strip frame: the fields of
`leavesAt (xB u z)` (`Design/DommaschkKamCQSPoly`), in the order of `QSLeaves`. -/
def lvS (u z : FA) : Fin 13 → FA :=
  ![DkPoly.ev (xB u z) dD, DkPoly.ev (xB u z) (DkPoly.dU dD), DkPoly.ev (xB u z) (DkPoly.dZ dD),
    DkPoly.ev (xB u z) dDf, DkPoly.ev (xB u z) dnR, DkPoly.ev (xB u z) (DkPoly.dU dnR),
    DkPoly.ev (xB u z) (DkPoly.dZ dnR), DkPoly.ev (xB u z) dnRf, DkPoly.ev (xB u z) dnZ,
    DkPoly.ev (xB u z) (DkPoly.dU dnZ), DkPoly.ev (xB u z) (DkPoly.dZ dnZ),
    DkPoly.ev (xB u z) dnZf, DkPoly.ev (xB u z) Rl]

/-- The strip-frame leaves of a rotated torus are the rotated oracle-frame leaves. -/
theorem lvS_rot (uo zo : FA) : lvS (rotψ uo) (rotψ zo) = fun i => rotψ (lvO uo zo i) := by
  funext i
  have e : ∀ p, DkPoly.ev (xB (rotψ uo) (rotψ zo)) p = rotψ (Fo p uo zo) := fun p => by
    rw [xB_rot, ev_rot]; rfl
  fin_cases i
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · exact e _
  · change DkPoly.ev (xB (rotψ uo) (rotψ zo)) Rl = rotψ (RofG dkR0 uo)
    rw [e, Fo, ev_Rl_A, RofG, rotψ_add, rotψ_add, rotψ_algebraMap, R0q_cast, rotψ_algebraMap]
    rfl

/-- The rotated approximate inverse of `Q R¹⁷`. -/
def qGs : FA := rotψ (xQ 238)
/-- The rotated approximate inverse of `R¹⁶`. -/
def qBs : FA := rotψ (xQ 241)
/-- The rotated approximate inverse of `D` (the Adm `qD`). -/
def qDs : FA := rotψ (xA 186)

/-- **The certified QA-defect bounds of a torus** (strip frame, `ℓ¹` norms). -/
structure QSDefBounds (u z : FA) : Prop where
  /-- The numerator times the approximate inverse of `Q R¹⁷`. -/
  hG : Bd 0 (qGs * qsNg (lvS u z) iotaF (dTh u) (dTh z)) (etaGq : ℝ)
  /-- The approximate inverse of `Q R¹⁷`. -/
  heG : Bd 0 (qGs * (qsQ (lvS u z) * lvS u z 12 ^ 17) - 1) (epsGq : ℝ)
  /-- `|B|² ≈ c_B`. -/
  hB : Bd 0 (qsQ (lvS u z) * qBs - cBF) (eBq : ℝ)
  /-- The approximate inverse of `R¹⁶`. -/
  heB : Bd 0 (qBs * lvS u z 12 ^ 16 - 1) (epsBq : ℝ)
  /-- `D ≈ c_D`. -/
  hD : Bd 0 (lvS u z 0 - cDF) (eDq : ℝ)
  /-- The mean of the `L²(J)` integrand. -/
  hF : ‖avg ((qGs * qsNg (lvS u z) iotaF (dTh u) (dTh z)) ^ 2 * (lvS u z 12 ^ 8 * qDs))‖ ≤
    (mFq : ℝ)
  /-- The approximate inverse of `D`. -/
  heD : Bd 0 (qDs * lvS u z 0 - 1) (epsDq : ℝ)

set_option maxRecDepth 100000 in
/-- **The QA defect on every close torus (N-34 D5).** Every analytic torus `(u, z)` that is
`μ`-close (`μ ≤ 10⁻¹²`, any strip `ρ ≥ 0`) to the data torus `(u₀A, z₀A)` satisfies
`QSDefBounds u z`. -/
theorem qsd_bounds {ρ μ : ℝ} (hρ : 0 ≤ ρ) (hμ : μ ≤ (muq : ℝ)) {u z : FA} (hu : Ana u)
    (hz : Ana z) (hC : Close ρ DommaschkKamDio.dkIotaA u z u₀A z₀A μ) : QSDefBounds u z := by
  have eU0 : rotψi u₀A = Uo := rotψi_rotψ Uo
  have eZ0 : rotψi z₀A = Zo := rotψi_rotψ Zo
  have cU : Bd 0 (rotψi u - Uo) μ := by
    rw [← eU0, ← rotψi_sub]; exact (Bd_rotψi hC.du).strip hρ
  have cZ : Bd 0 (rotψi z - Zo) μ := by
    rw [← eZ0, ← rotψi_sub]; exact (Bd_rotψi hC.dz).strip hρ
  have cA : Bd 0 (dTh (rotψi u) - dTh Uo) μ := by
    have h := Bd_rotψi hC.dut
    rw [rotψi_sub] at h
    change Bd 0 (dS 1 0 (rotψi u) - dS 1 0 Uo) μ
    rw [dS_rotψi 1 0 hu, ← eU0, dS_rotψi 1 0 ana_u₀A]; exact h.strip hρ
  have cB : Bd 0 (dTh (rotψi z) - dTh Zo) μ := by
    have h := Bd_rotψi hC.dzt
    rw [rotψi_sub] at h
    change Bd 0 (dS 1 0 (rotψi z) - dS 1 0 Zo) μ
    rw [dS_rotψi 1 0 hz, ← eZ0, dS_rotψi 1 0 ana_z₀A]; exact h.strip hρ
  have gtU := Bd_tg_U hq0A
  have gtZ := Bd_tg_Z hq0A
  have gtAU := Bd_tg_AU hq0A
  have gtAZ := Bd_tg_AZ hq0A
  rw [← Uo_sub_xA] at gtU
  rw [← Zo_sub_xA] at gtZ
  rw [← dTh_tailU] at gtAU
  rw [← dTh_tailZ] at gtAZ
  have inp : ∀ {X Y W : FA} {t : ℚ}, Bd 0 (X - Y) μ → Bd 0 (Y - W) (t : ℝ) →
      Bd 0 (X - W) ((muq + t : ℚ) : ℝ) := fun h1 h2 => by
    have := h1.add h2
    rw [sub_add_sub_cancel] at this
    exact this.le (by push_cast; linarith)
  obtain ⟨hG, heG, hBE, heB, hDE, hF, heD⟩ :=
    qsd_near (inp cU gtU) (inp cZ gtZ) (inp cA gtAU) (inp cB gtAZ)
  have hu' := ana_rotψi hu
  have hz' := ana_rotψi hz
  set uo := rotψi u
  set zo := rotψi z
  have eu : u = rotψ uo := (rotψ_rotψi u).symm
  have ez : z = rotψ zo := (rotψ_rotψi z).symm
  have el : lvS u z = fun i => rotψ (lvO uo zo i) := by rw [eu, ez, lvS_rot]
  have eθu : dTh u = rotψ (dTh uo) := by rw [eu]; exact dTh_rot hu'
  have eθz : dTh z = rotψ (dTh zo) := by rw [ez]; exact dTh_rot hz'
  have eι : rotψ iotaF = iotaF := rotψ_algebraMap _
  have eN : qsNg (lvS u z) iotaF (dTh u) (dTh z) =
      rotψ (qsNg (lvO uo zo) iotaF (dTh uo) (dTh zo)) := by
    have h := qsNg_map rotψHom.toRingHom (lvO uo zo) iotaF (dTh uo) (dTh zo)
    change rotψ _ = qsNg (fun i => rotψ (lvO uo zo i)) (rotψ iotaF) (rotψ (dTh uo))
      (rotψ (dTh zo)) at h
    rw [eι] at h
    rw [el, eθu, eθz, h]
  have eQ : qsQ (lvS u z) = rotψ (qsQ (lvO uo zo)) := by
    have h := qsQ_map rotψHom.toRingHom (lvO uo zo)
    change rotψ _ = qsQ (fun i => rotψ (lvO uo zo i)) at h
    rw [el, h]
  have e12 : lvS u z 12 = rotψ (lvO uo zo 12) := by rw [el]
  have e0 : lvS u z 0 = rotψ (lvO uo zo 0) := by rw [el]
  have eB : rotψ cBF = cBF := rotψ_algebraMap _
  have eD : rotψ cDF = cDF := rotψ_algebraMap _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eN, qGs, ← rotψ_mul]; exact Bd_rotψ hG
  · rw [eQ, e12, qGs, ← rotψ_pow, ← rotψ_mul, ← rotψ_mul, ← rotψ_one, ← rotψ_sub]
    exact Bd_rotψ heG
  · rw [eQ, qBs, ← eB, ← rotψ_mul, ← rotψ_sub]; exact Bd_rotψ hBE
  · rw [e12, qBs, ← rotψ_pow, ← rotψ_mul, ← rotψ_one, ← rotψ_sub]; exact Bd_rotψ heB
  · rw [e0, ← eD, ← rotψ_sub]; exact Bd_rotψ hDE
  · rw [eN, e12, qGs, qDs, ← rotψ_mul, ← rotψ_pow, ← rotψ_pow, ← rotψ_mul, ← rotψ_mul, avg_rotψ]
    exact hF
  · rw [e0, qDs, ← rotψ_mul, ← rotψ_one, ← rotψ_sub]; exact Bd_rotψ heD

/-! ## Pointwise consequences -/

/-- A quotient from an approximate inverse: from `|a n| ≤ η` and `|a w − 1| ≤ ε < 1`,
`w ≠ 0` and `|n/w| ≤ η/(1 − ε)`. -/
theorem norm_div_of_approx {a n w : ℂ} {η ε : ℝ} (hn : ‖a * n‖ ≤ η) (hw : ‖a * w - 1‖ ≤ ε)
    (hε : ε < 1) : w ≠ 0 ∧ ‖n / w‖ ≤ η / (1 - ε) := by
  have h1 : 1 - ε ≤ ‖a * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - a * w)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hpos : 0 < ‖a * w‖ := by linarith
  have haw : a * w ≠ 0 := norm_pos_iff.1 hpos
  have hw0 : w ≠ 0 := right_ne_zero_of_mul haw
  refine ⟨hw0, ?_⟩
  have ha : a ≠ 0 := left_ne_zero_of_mul haw
  rw [show n / w = (a * n) / (a * w) by field_simp, norm_div]
  exact div_le_div₀ ((norm_nonneg _).trans hn) hn (by linarith) h1

/-- A quotient near a constant: from `|Q q − c| ≤ e` and `|q w − 1| ≤ ε < 1`,
`w ≠ 0` and `|Q/w − c| ≤ (e + |c| ε)/(1 − ε)`. -/
theorem norm_div_sub_of_approx {q Q w c : ℂ} {e ε : ℝ} (hQ : ‖Q * q - c‖ ≤ e)
    (hw : ‖q * w - 1‖ ≤ ε) (hε : ε < 1) : w ≠ 0 ∧ ‖Q / w - c‖ ≤ (e + ‖c‖ * ε) / (1 - ε) := by
  have h := norm_div_of_approx (a := q) (n := Q - c * w) (η := e + ‖c‖ * ε)
    (by
      rw [show q * (Q - c * w) = (Q * q - c) - c * (q * w - 1) by ring]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      exact add_le_add hQ (mul_le_mul_of_nonneg_left hw (norm_nonneg _))) hw hε
  refine ⟨h.1, ?_⟩
  rw [show Q / w - c = (Q - c * w) / w by field_simp [h.1]]
  exact h.2

/-- The supremum bound of the defect quotient. -/
def d1q : ℚ := (641759 / 10 ^ 7 : ℚ)
/-- The bound of `|Q/R¹⁶ − c_B|`. -/
def eBpq : ℚ := (9017 / 10 ^ 5 : ℚ)
/-- The constant `c_B ∈ ℚ`. -/
def cBq : ℚ := 4913473139 / 2 ^ 32
/-- The constant `c_D ∈ ℚ`. -/
def cDq : ℚ := 2816261147 / 2 ^ 32

set_option linter.style.longLine false in
/-- **Pointwise consequences of `QSDefBounds`** at every `(θ, ψ)`: `Q R¹⁷ ≠ 0`,
`|N_g/(Q R¹⁷)| ≤ d₁`; `R¹⁶ ≠ 0`, `|Q/R¹⁶ − c_B| ≤ e_B'`; `|D − c_D| ≤ e_D`. -/
theorem QSDefBounds.pointwise {u z : FA} (h : QSDefBounds u z) (θ ψ : ℝ) :
    (eval (qsQ (lvS u z) * lvS u z 12 ^ 17) θ ψ ≠ 0 ∧
      ‖eval (qsNg (lvS u z) iotaF (dTh u) (dTh z)) θ ψ /
        eval (qsQ (lvS u z) * lvS u z 12 ^ 17) θ ψ‖ ≤ (d1q : ℝ)) ∧
    (eval (lvS u z 12 ^ 16) θ ψ ≠ 0 ∧
      ‖eval (qsQ (lvS u z)) θ ψ / eval (lvS u z 12 ^ 16) θ ψ - ((cBq : ℚ) : ℂ)‖ ≤ (eBpq : ℝ)) ∧
    ‖eval (lvS u z 0) θ ψ - ((cDq : ℚ) : ℂ)‖ ≤ (eDq : ℝ) := by
  have m : ∀ x y : FA, eval (x * y) θ ψ = eval x θ ψ * eval y θ ψ :=
    fun x y => map_mul (evalHom θ ψ) x y
  have hG := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.hG θ ψ
  have heG := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.heG θ ψ
  have hB := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.hB θ ψ
  have heB := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.heB θ ψ
  have hD := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.hD θ ψ
  rw [m] at hG
  rw [eval_sub', m, eval_one] at heG heB
  rw [eval_sub', m, cBF, eval_algebraMap] at hB
  rw [eval_sub', cDF, eval_algebraMap] at hD
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := norm_div_of_approx hG heG (by exact_mod_cast (show epsGq < 1 by kernel_fact))
    exact ⟨h1, h2.trans (div_cast_le (show etaGq / (1 - epsGq) ≤ d1q by kernel_fact))⟩
  · obtain ⟨h1, h2⟩ := norm_div_sub_of_approx hB heB
      (by exact_mod_cast (show epsBq < 1 by kernel_fact))
    refine ⟨h1, h2.trans ?_⟩
    rw [Complex.norm_ratCast]
    have := div_cast_le (show (eBq + |4913473139 / 2 ^ 32| * epsBq) / (1 - epsBq) ≤ eBpq by kernel_fact)
    push_cast at this ⊢
    exact this
  · exact hD

set_option linter.style.longLine false in
/-- **The defect from the two pointwise bounds** (real form, for D6): if `R, Q > 0`,
`|N_g/(Q R¹⁷)| ≤ d₁` and `Q/R¹⁶ ≥ b² > 0`, then `|N_g/(2Q√Q R⁹)| ≤ d₁/(2b)`. -/
theorem qsd_defect_real {Ng Q R d1 b : ℝ} (hR : 0 < R) (hQ : 0 < Q) (hb : 0 < b)
    (h1 : |Ng / (Q * R ^ 17)| ≤ d1) (h2 : b ^ 2 ≤ Q / R ^ 16) :
    |Ng / (2 * Q * Real.sqrt Q * R ^ 9)| ≤ d1 / (2 * b) := by
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
  have hR8 : 0 < R ^ 8 := pow_pos hR 8
  have hx : 0 < Real.sqrt Q / R ^ 8 := div_pos hs hR8
  have hbB : b ≤ Real.sqrt Q / R ^ 8 := by
    refine (pow_le_pow_iff_left₀ hb.le hx.le two_ne_zero).1 ?_
    rw [div_pow, Real.sq_sqrt hQ.le, ← pow_mul]
    exact h2
  have e : Ng / (2 * Q * Real.sqrt Q * R ^ 9) = (Ng / (Q * R ^ 17)) / (2 * (Real.sqrt Q / R ^ 8)) := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (Real.sqrt Q / R ^ 8))]
  exact div_le_div₀ ((abs_nonneg _).trans h1) h1 (by positivity) (by linarith)

/-! ## The certified numbers -/

/-- `B_min`: a lower bound of `|B|` on every close torus. -/
def Bminq : ℚ := (3208 / 3125 : ℚ)
/-- `δ_∞`: the bound of the supremum of the QA defect. -/
def deltaq : ℚ := (15629 / 500000 : ℚ)
/-- `D_min`: a lower bound of `D = R⁷B_φ`. -/
def Dminq : ℚ := (11161 / 10 ^ 5 : ℚ)
/-- `δ₂`: the bound of `‖g‖_{L²(J)}`. -/
def delta2q : ℚ := (3889 / 1250000 : ℚ)

/-- **The certified numbers of torus A** (closed rational facts):
`B_min² ≤ c_B − e_B'`, `d₁/(2B_min) ≤ δ_∞ ≤ 0.032`, `B_min ≥ 1.026`,
`κ = 2δ_∞/(B_min · 1193/5000) ≤ 0.26` (`|ι_A| ≥ 1193/5000`), `D ≥ c_D − e_D ≥ D_min > 0`,
`m_F/(4(1 − ε_G)²(1 − ε_D)) ≤ δ₂²`, and the oracle-normalised defect
`(√2/2) δ₂/(B_min · 1193/5000) ≤ 0.01` (with `√2/2 ≤ 0.7072`). -/
theorem qsd_numbers :
    Bminq ^ 2 ≤ cBq - eBpq ∧ d1q / (2 * Bminq) ≤ deltaq ∧ deltaq ≤ 32 / 1000 ∧
      1026 / 1000 ≤ Bminq ∧ 2 * deltaq / (Bminq * (1193 / 5000)) ≤ 26 / 100 ∧
      Dminq ≤ cDq - eDq ∧ 0 < Dminq ∧
      mFq / (4 * (1 - epsGq) ^ 2 * (1 - epsDq)) ≤ delta2q ^ 2 ∧
      7072 / 10000 * delta2q / (Bminq * (1193 / 5000)) ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_fact

/-- **Sanity (rejected fixture)**: the certified bound is not below `10⁻³` (and cannot be: the
surrogate numerator is not zero, `surr_G_ne`). -/
theorem qsd_not_tiny : ¬ deltaq ≤ 1 / 1000 := by
  norm_num [deltaq]

end PlasmaLean.Design.DommaschkKamA
