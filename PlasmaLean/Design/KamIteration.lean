/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamNewtonStep
public import PlasmaLean.Theory.KAM.KamSequence

/-!
# The KAM iteration and its limit: an exact invariant torus (KAM route, K3d, `kam_flow_torus`)

Iterating the Newton step `kam_step` (`Design/KamNewtonStep`) with losses `δ_j = δ₀ 2^{−j}` and
strips `ρ_{j+1} = ρ_j − 3δ_j` (`kamRadius ρ₀ 3 δ₀`), the errors are dominated by the extremal
sequence `ē_{j+1} = κ ē_j²/δ_j⁴` (`kamExact`), which tends to `0` super-exponentially under the
smallness condition `32 κ e₀/δ₀⁴ ≤ 1` (`Theory/KAM/KamSequence`). The corrections are summable in
the strip norm of width `ρ_∞ = ρ₀ − 6δ₀ > 0`, so the iterates converge in the Banach space
`ℓ¹_{ρ_∞}(ℤ²)`, and the limit solves the flow-form equation **exactly** (`kam_flow_torus`).

**Admissibility.** The step needs bounds on the frame quantities at every iterate (`AdmBounds`).
They are supplied by an *admissibility* hypothesis: every analytic torus that is `μ`-close to the
initial torus in the six quantities `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` (`Close`) on a strip
`ρ ∈ [ρ_∞, ρ₀]` satisfies the bounds with the fixed constants `c : SC`. The total displacement is
at most `2 cK e₀/δ₀²` (and `2 (cK/e) e₀/δ₀³`, `2 cL e₀/δ₀²` for the derivatives), which must be
`≤ μ` (`hμ`), so all iterates stay admissible.

**Sanity.** `stepK` is a genuine map (defined for every pair), and `kamExact_le_θ`: the normalized
errors `ē_j/δ_j⁴` decrease.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM WEll1Z2 Filter Topology

/-- `μ`-closeness of a torus `(u, z)` to `(u₀, z₀)` on the strip `ρ`, in the six quantities used by
the Newton step. -/
structure Close (ρ ι : ℝ) (u z u₀ z₀ : FA) (μ : ℝ) : Prop where
  /-- `u`. -/
  du : Bd ρ (u - u₀) μ
  /-- `z`. -/
  dz : Bd ρ (z - z₀) μ
  /-- `∂_θ u`. -/
  dut : Bd ρ (dTh u - dTh u₀) μ
  /-- `∂_θ z`. -/
  dzt : Bd ρ (dTh z - dTh z₀) μ
  /-- `𝓛 u`. -/
  duL : Bd ρ (Lt ι u - Lt ι u₀) μ
  /-- `𝓛 z`. -/
  dzL : Bd ρ (Lt ι z - Lt ι z₀) μ

/-- The torus and frame bounds required by a Newton step, at strip width `ρ`, with the constants
of `c`. -/
structure AdmBounds (c : SC) (ι ρ : ℝ) (u z : FA) : Prop where
  /-- Frame hypotheses. -/
  frame : FrameHyp u z
  /-- Torus bound. -/
  hu : Bd ρ u c.au
  /-- Torus bound. -/
  hz : Bd ρ z c.az
  /-- Torus bound. -/
  hRt : Bd ρ (Rt u) c.aRt
  /-- Torus bound. -/
  hzt : Bd ρ (zt z) c.azt
  /-- Torus bound. -/
  hLR : Bd ρ (LR ι u) c.aLR
  /-- Torus bound. -/
  hLz : Bd ρ (Lz ι z) c.aLz
  /-- Field bound. -/
  hbD : Bd ρ (Dof u z) c.bD
  /-- Field bound. -/
  hbDu : Bd ρ (Du u z) c.bDu
  /-- Field bound. -/
  hbDz : Bd ρ (Dz u z) c.bDz
  /-- Field bound. -/
  hbnR : Bd ρ (nR u z) c.bnR
  /-- Field bound. -/
  hbnRu : Bd ρ (nRu u z) c.bnRu
  /-- Field bound. -/
  hbnRz : Bd ρ (nRz u z) c.bnRz
  /-- Field bound. -/
  hbnZ : Bd ρ (nZ u z) c.bnZ
  /-- Field bound. -/
  hbnZu : Bd ρ (nZu u z) c.bnZu
  /-- Field bound. -/
  hbnZz : Bd ρ (nZz u z) c.bnZz
  /-- Inverse bound. -/
  hsD : Bd ρ (Di u z) c.sD
  /-- Inverse bound. -/
  hsR : Bd ρ (Ri u) c.sR
  /-- Inverse bound. -/
  hsW : Bd ρ (Wi u z) c.sW
  /-- Torsion bound. -/
  hT : Bd ρ (Talg u z) c.tT
  /-- Twist. -/
  hτ : c.τ ≤ ‖avg (Talg u z)‖

/-- The step constants with the strip width replaced by `ρ` (all derived constants are
unchanged). -/
def SC.withρ (c : SC) (ρ : ℝ) : SC := { c with ρ := ρ }

/-- The global (numerical) conditions on the constants. -/
structure GlobalH (c : SC) (ι : ℝ) : Prop where
  /-- Diophantine frequency. -/
  dio : Diophantine (ι / 2) c.γ 1
  /-- `γ > 0`. -/
  γ_pos : 0 < c.γ
  /-- Twist margin. -/
  hτ' : 0 < c.τ'
  /-- Taylor constant (`R`). -/
  hC2R : PolyExpr.majD2 (c.avec + c.Tq • c.mvec) c.mvec resRp / 2 ≤ c.C2
  /-- Taylor constant (`z`). -/
  hC2Z : PolyExpr.majD2 (c.avec + c.Tq • c.mvec) c.mvec resZp / 2 ≤ c.C2
  /-- Rüssmann range. -/
  hδ2 : c.δ0 ≤ 2 / Real.exp 1
  /-- Bound of `cos 2φ`, `sin 2φ` on the initial strip. -/
  hac : Real.exp c.ρ ≤ c.ac
  /-- `0 < E1 ≤ e`. -/
  hE1 : 0 < c.E1 ∧ c.E1 ≤ Real.exp 1
  /-- `cK ≤ cKb`, `cL ≤ cLb`. -/
  hcb : c.cK ≤ c.cKb ∧ c.cL ≤ c.cLb

/-- **A step is admissible**: from the bounds at strip `ρ ≤ ρ₀`, the global conditions and the
error conditions, the hypotheses `StepH` of `kam_step` hold. -/
theorem stepH_of_adm {c : SC} {ι ρ : ℝ} {u z : FA} {e δ : ℝ} (G : GlobalH c ι)
    (A : AdmBounds c ι ρ u z) (hρ : ρ ≤ c.ρ) (heR : Bd ρ (resR ι u z) e)
    (heZ : Bd ρ (resZ ι u z) e) (heθ : e ≤ c.θ * δ ^ 4) (hδ : 0 < δ) (hδ0 : δ ≤ c.δ0)
    (h3δ : 3 * δ ≤ ρ) : StepH (c.withρ ρ) ι u z e δ where
  frame := A.frame
  dio := G.dio
  γ_pos := G.γ_pos
  hu := A.hu
  hz := A.hz
  hRt := A.hRt
  hzt := A.hzt
  hLR := A.hLR
  hLz := A.hLz
  hac := (Real.exp_le_exp.2 hρ).trans G.hac
  hbD := A.hbD
  hbDu := A.hbDu
  hbDz := A.hbDz
  hbnR := A.hbnR
  hbnRu := A.hbnRu
  hbnRz := A.hbnRz
  hbnZ := A.hbnZ
  hbnZu := A.hbnZu
  hbnZz := A.hbnZz
  hsD := A.hsD
  hsR := A.hsR
  hsW := A.hsW
  hT := A.hT
  hτ := A.hτ
  hτ' := G.hτ'
  hC2R := G.hC2R
  hC2Z := G.hC2Z
  heR := heR
  heZ := heZ
  heθ := heθ
  hδ := hδ
  hδ0 := hδ0
  h3δ := h3δ
  hδ2 := G.hδ2
  hE1 := G.hE1
  hcb := G.hcb

/-- The Cauchy estimate in the form used by the iteration. -/
theorem cauchy_conv {E1 δ K e : ℝ} (hE1 : 0 < E1) (hE : E1 ≤ Real.exp 1) (hδ : 0 < δ)
    (hK : 0 ≤ K) (he : 0 ≤ e) :
    max ‖(1 : ℂ)‖ ‖(0 : ℂ)‖ / (Real.exp 1 * δ) * (K * e / δ ^ 2) ≤ K / E1 * e / δ ^ 3 := by
  have he1 := Real.exp_pos 1
  have h1 : max ‖(1 : ℂ)‖ ‖(0 : ℂ)‖ / (Real.exp 1 * δ) * (K * e / δ ^ 2) =
      K * e / (Real.exp 1 * δ ^ 3) := by
    simp only [norm_one, norm_zero, max_eq_left zero_le_one]
    field_simp
  rw [h1, show K / E1 * e / δ ^ 3 = K * e / (E1 * δ ^ 3) by field_simp]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)

/-! ## The iteration -/

/-- One Newton step `(u, z) ↦ (u + ΔR, z + Δz)`. -/
def stepK (ι : ℝ) (p : FA × FA) : FA × FA := (p.1 + dRs ι p.1 p.2, p.2 + dZs ι p.1 p.2)

/-- The KAM iterates. -/
def iterK (ι : ℝ) (u₀ z₀ : FA) : ℕ → FA × FA
  | 0 => (u₀, z₀)
  | n + 1 => stepK ι (iterK ι u₀ z₀ n)

/-! ### The scalar sequences -/

section Scalar

variable {κ δ₀ e₀ : ℝ}

/-- Nonnegativity of the extremal errors. -/
theorem kamExact_nonneg' (hκ : 0 ≤ κ) (he : 0 ≤ e₀) (n : ℕ) : 0 ≤ kamExact κ δ₀ e₀ n :=
  kamExact_nonneg hκ he n

/-- The extremal errors satisfy the recursion with equality. -/
theorem kamExact_rec (n : ℕ) :
    kamExact κ δ₀ e₀ (n + 1) ≤ κ * kamExact κ δ₀ e₀ n ^ 2 / kamDelta δ₀ n ^ 4 := le_rfl

/-- **Sanity: the normalized errors decrease**, `ē_n ≤ (e₀/δ₀⁴) δ_n⁴`. -/
theorem kamExact_le_θ (hκ : 0 < κ) (hδ : 0 < δ₀) (he : 0 ≤ e₀)
    (hsmall : 32 * κ * e₀ / δ₀ ^ 4 ≤ 1) (n : ℕ) :
    kamExact κ δ₀ e₀ n ≤ e₀ / δ₀ ^ 4 * kamDelta δ₀ n ^ 4 := by
  have hnn : ∀ j, 0 ≤ kamExact κ δ₀ e₀ j := kamExact_nonneg hκ.le he
  have hpow := kamEps_le_pow hκ.le hδ hnn (kamExact_rec (κ := κ) (δ₀ := δ₀) (e₀ := e₀)) n
  have h0 := kamEps_zero_le_half (e := kamExact κ δ₀ e₀) hsmall
  have hnn0 := kamEps_nonneg (δ₀ := δ₀) hκ.le hnn 0
  have hle : kamEps κ δ₀ (kamExact κ δ₀ e₀) 0 ^ (2 ^ n) ≤ kamEps κ δ₀ (kamExact κ δ₀ e₀) 0 := by
    calc _ ≤ kamEps κ δ₀ (kamExact κ δ₀ e₀) 0 ^ 1 :=
          pow_le_pow_of_le_one hnn0 (by linarith) (Nat.one_le_two_pow)
      _ = _ := pow_one _
  have h1 := hpow.trans hle
  unfold kamEps at h1
  rw [kamDelta_zero] at h1
  have hd := kamDelta_pos hδ n
  have hk : (kamExact κ δ₀ e₀ 0) = e₀ := rfl
  rw [hk] at h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end Scalar

/-! ### The invariant of the iteration -/

section Iter

variable (c : SC) (ι : ℝ) (u₀ z₀ : FA) (e₀ μ : ℝ)

/-- The strip widths `ρ_n`. -/
def rhoN (n : ℕ) : ℝ := kamRadius c.ρ 3 c.δ0 n
/-- The losses `δ_n`. -/
def delN (n : ℕ) : ℝ := kamDelta c.δ0 n
/-- The extremal errors `ē_n`. -/
def eN (n : ℕ) : ℝ := kamExact c.kap c.δ0 e₀ n
/-- Partial displacement sum (torus). -/
def SK (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cK * eN c e₀ j / delN c j ^ 2
/-- Partial displacement sum (`θ`-derivatives). -/
def St (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cK / c.E1 * eN c e₀ j / delN c j ^ 3
/-- Partial displacement sum (transport). -/
def SL (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cL * eN c e₀ j / delN c j ^ 2

/-- The hypotheses of the KAM iteration. -/
structure KamH : Prop where
  /-- Global numerical conditions. -/
  G : GlobalH c ι
  /-- `δ₀ > 0`. -/
  hδ0 : 0 < c.δ0
  /-- Room for the losses: `ρ_∞ = ρ₀ − 6δ₀ > 0`. -/
  hρ6 : 6 * c.δ0 < c.ρ
  /-- The error scale. -/
  hθ : c.θ = e₀ / c.δ0 ^ 4
  /-- `e₀ ≥ 0`. -/
  he₀ : 0 ≤ e₀
  /-- `κ > 0`. -/
  hκ : 0 < c.kap
  /-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1`. -/
  hsmall : 32 * c.kap * e₀ / c.δ0 ^ 4 ≤ 1
  /-- `cK ≥ 0`. -/
  hcK : 0 ≤ c.cK
  /-- `cL ≥ 0`. -/
  hcL : 0 ≤ c.cL
  /-- Displacement budget (torus). -/
  hμK : 2 * c.cK * e₀ / c.δ0 ^ 2 ≤ μ
  /-- Displacement budget (`θ`-derivatives). -/
  hμt : 2 * (c.cK / c.E1) * e₀ / c.δ0 ^ 3 ≤ μ
  /-- Displacement budget (transport). -/
  hμL : 2 * c.cL * e₀ / c.δ0 ^ 2 ≤ μ
  /-- **Admissibility** of every `μ`-close analytic torus on the strips `[ρ_∞, ρ₀]`. -/
  hadm : ∀ ρ u z, c.ρ - 6 * c.δ0 ≤ ρ → ρ ≤ c.ρ → Ana u → Ana z →
    Close ρ ι u z u₀ z₀ μ → AdmBounds c ι ρ u z
  /-- The initial torus is analytic. -/
  ana_u₀ : Ana u₀
  /-- The initial torus is analytic. -/
  ana_z₀ : Ana z₀
  /-- The initial torus is real. -/
  real_u₀ : IsReal u₀
  /-- The initial torus is real. -/
  real_z₀ : IsReal z₀
  /-- Initial error. -/
  e0R : Bd c.ρ (resR ι u₀ z₀) e₀
  /-- Initial error. -/
  e0Z : Bd c.ρ (resZ ι u₀ z₀) e₀

/-- The invariant of the iteration at step `n`. -/
structure Inv (n : ℕ) : Prop where
  /-- Analytic. -/
  ana_u : Ana (iterK ι u₀ z₀ n).1
  /-- Analytic. -/
  ana_z : Ana (iterK ι u₀ z₀ n).2
  /-- Real. -/
  real_u : IsReal (iterK ι u₀ z₀ n).1
  /-- Real. -/
  real_z : IsReal (iterK ι u₀ z₀ n).2
  /-- Error. -/
  eR : Bd (rhoN c n) (resR ι (iterK ι u₀ z₀ n).1 (iterK ι u₀ z₀ n).2) (eN c e₀ n)
  /-- Error. -/
  eZ : Bd (rhoN c n) (resZ ι (iterK ι u₀ z₀ n).1 (iterK ι u₀ z₀ n).2) (eN c e₀ n)
  /-- Displacement. -/
  du : Bd (rhoN c n) ((iterK ι u₀ z₀ n).1 - u₀) (SK c e₀ n)
  /-- Displacement. -/
  dz : Bd (rhoN c n) ((iterK ι u₀ z₀ n).2 - z₀) (SK c e₀ n)
  /-- Displacement. -/
  dut : Bd (rhoN c n) (dTh (iterK ι u₀ z₀ n).1 - dTh u₀) (St c e₀ n)
  /-- Displacement. -/
  dzt : Bd (rhoN c n) (dTh (iterK ι u₀ z₀ n).2 - dTh z₀) (St c e₀ n)
  /-- Displacement. -/
  duL : Bd (rhoN c n) (Lt ι (iterK ι u₀ z₀ n).1 - Lt ι u₀) (SL c e₀ n)
  /-- Displacement. -/
  dzL : Bd (rhoN c n) (Lt ι (iterK ι u₀ z₀ n).2 - Lt ι z₀) (SL c e₀ n)

variable {c ι u₀ z₀ e₀ μ}

namespace KamH

variable (K : KamH c ι u₀ z₀ e₀ μ)
include K

/-- The scalar hypotheses of `kam_sequence` for the extremal errors. -/
theorem seq :
    (∀ j, eN c e₀ j ≤ e₀ * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j) ∧
    Tendsto (eN c e₀) atTop (𝓝 0) ∧
    (∀ (τ : ℕ) (C' : ℝ), τ ≤ 4 → 0 ≤ C' →
      Summable (fun j => C' * eN c e₀ j / kamDelta c.δ0 j ^ τ) ∧
      ∑' j, C' * eN c e₀ j / kamDelta c.δ0 j ^ τ ≤ 2 * C' * eN c e₀ 0 / c.δ0 ^ τ ∧
      ∀ n, ∑' j, C' * eN c e₀ (j + n) / kamDelta c.δ0 (j + n) ^ τ ≤
        2 * C' * eN c e₀ 0 / c.δ0 ^ τ * (1 / 2) ^ n) :=
  kam_sequence K.hκ K.hδ0 (kamExact_nonneg K.hκ.le K.he₀) (fun _ => le_rfl) K.hsmall

/-- Partial sums are bounded by the total displacement. -/
theorem partial_le (τ : ℕ) (hτ : τ ≤ 4) {C' : ℝ} (hC : 0 ≤ C') (n : ℕ) :
    ∑ j ∈ Finset.range n, C' * eN c e₀ j / delN c j ^ τ ≤ 2 * C' * e₀ / c.δ0 ^ τ := by
  obtain ⟨hs, htot, -⟩ := K.seq.2.2 τ C' hτ hC
  have hnn : ∀ j, 0 ≤ C' * eN c e₀ j / kamDelta c.δ0 j ^ τ := fun j => by
    have := kamExact_nonneg K.hκ.le K.he₀ (δ₀ := c.δ0) j
    have := kamDelta_pos K.hδ0 j
    unfold eN; positivity
  calc _ ≤ ∑' j, C' * eN c e₀ j / kamDelta c.δ0 j ^ τ := hs.sum_le_tsum _ (fun i _ => hnn i)
    _ ≤ _ := htot

/-- `ρ_n > ρ_∞`. -/
theorem rho_gt (n : ℕ) : c.ρ - 6 * c.δ0 < rhoN c n := by
  have := kamRadius_gt (r₀ := c.ρ) (c := 3) (δ₀ := c.δ0) (by norm_num) K.hδ0 n
  unfold rhoN; linarith

/-- `ρ_n ≤ ρ₀`. -/
theorem rho_le (n : ℕ) : rhoN c n ≤ c.ρ := by
  induction n with
  | zero => simp [rhoN, kamRadius]
  | succ n ih =>
    have := kamRadius_succ_le (r₀ := c.ρ) (c := 3) (δ₀ := c.δ0) (by norm_num) K.hδ0.le n
    unfold rhoN at *; linarith

omit K in
/-- `ρ_{n+1} = ρ_n − 3δ_n`. -/
theorem rho_succ (n : ℕ) : rhoN c (n + 1) = rhoN c n - 3 * delN c n := rfl

/-- `3δ_n ≤ ρ_n`. -/
theorem three_del_le (n : ℕ) : 3 * delN c n ≤ rhoN c n := by
  have h1 := K.rho_gt (n + 1)
  rw [rho_succ] at h1
  have := K.hρ6; have := K.hδ0
  linarith

/-- `δ_n ≤ δ₀`. -/
theorem del_le (n : ℕ) : delN c n ≤ c.δ0 := by
  unfold delN kamDelta
  have := K.hδ0
  exact div_le_self this.le (one_le_pow₀ (by norm_num))

/-- The errors stay on the scale `θ δ_n⁴`. -/
theorem eN_le_θ (n : ℕ) : eN c e₀ n ≤ c.θ * delN c n ^ 4 := by
  rw [K.hθ]; exact kamExact_le_θ K.hκ K.hδ0 K.he₀ K.hsmall n

/-- The iterates are `μ`-close to the initial torus. -/
theorem close_of_inv {n : ℕ} (I : Inv c ι u₀ z₀ e₀ n) :
    Close (rhoN c n) ι (iterK ι u₀ z₀ n).1 (iterK ι u₀ z₀ n).2 u₀ z₀ μ := by
  have hK := K.partial_le 2 (by norm_num) K.hcK n
  have ht := K.partial_le 3 (by norm_num) (div_nonneg K.hcK K.G.hE1.1.le) n
  have hL := K.partial_le 2 (by norm_num) K.hcL n
  exact ⟨I.du.le (hK.trans K.hμK), I.dz.le (hK.trans K.hμK), I.dut.le (ht.trans K.hμt),
    I.dzt.le (ht.trans K.hμt), I.duL.le (hL.trans K.hμL), I.dzL.le (hL.trans K.hμL)⟩

/-- The base case. -/
theorem inv_zero : Inv c ι u₀ z₀ e₀ 0 where
  ana_u := K.ana_u₀
  ana_z := K.ana_z₀
  real_u := K.real_u₀
  real_z := K.real_z₀
  eR := K.e0R
  eZ := K.e0Z
  du := by simpa [SK, iterK] using Bd_zero (rhoN c 0)
  dz := by simpa [SK, iterK] using Bd_zero (rhoN c 0)
  dut := by simpa [St, iterK] using Bd_zero (rhoN c 0)
  dzt := by simpa [St, iterK] using Bd_zero (rhoN c 0)
  duL := by simpa [SL, iterK] using Bd_zero (rhoN c 0)
  dzL := by simpa [SL, iterK] using Bd_zero (rhoN c 0)

omit K in
/-- `∂_θ` and `𝓛` of a sum of analytic elements. -/
theorem d_add {a b : ℂ} {x y : FA} (hx : Ana x) (hy : Ana y) :
    dS a b (x + y) = dS a b x + dS a b y := dS_add a b hx hy

/-- **The inductive step of the iteration.** -/
theorem inv_succ {n : ℕ} (I : Inv c ι u₀ z₀ e₀ n) : Inv c ι u₀ z₀ e₀ (n + 1) := by
  set u := (iterK ι u₀ z₀ n).1 with hu
  set z := (iterK ι u₀ z₀ n).2 with hz
  have A := K.hadm (rhoN c n) u z (K.rho_gt n).le (K.rho_le n) I.ana_u I.ana_z (K.close_of_inv I)
  have hδn : 0 < delN c n := kamDelta_pos K.hδ0 n
  have SH := stepH_of_adm K.G A (K.rho_le n) I.eR I.eZ (K.eN_le_θ n) hδn (K.del_le n)
    (K.three_del_le n)
  have hρ1 : rhoN c (n + 1) ≤ rhoN c n - 2 * delN c n := by
    rw [rho_succ]; linarith
  have hρ0 : rhoN c (n + 1) ≤ rhoN c n := hρ1.trans (by linarith)
  have hdR : Bd (rhoN c n - 2 * delN c n) (dRs ι u z) (c.cK * eN c e₀ n / delN c n ^ 2) :=
    SH.bdR
  have hdZ : Bd (rhoN c n - 2 * delN c n) (dZs ι u z) (c.cK * eN c e₀ n / delN c n ^ 2) :=
    SH.bdZ
  have hLR : Bd (rhoN c n - 2 * delN c n) (Lt ι (dRs ι u z)) (c.cL * eN c e₀ n / delN c n ^ 2) :=
    SH.bLdR
  have hLZ : Bd (rhoN c n - 2 * delN c n) (Lt ι (dZs ι u z)) (c.cL * eN c e₀ n / delN c n ^ 2) :=
    SH.bLdZ
  have hER : Bd (rhoN c n - 2 * delN c n) (resR ι (u + dRs ι u z) (z + dZs ι u z))
      (eN c e₀ (n + 1)) := SH.bER'
  have hEZ : Bd (rhoN c n - 2 * delN c n) (resZ ι (u + dRs ι u z) (z + dZs ι u z))
      (eN c e₀ (n + 1)) := SH.bEZ'
  have h3 : delN c n ≤ rhoN c n - 2 * delN c n := by
    have := K.three_del_le n; linarith
  have hθR : Bd (rhoN c n - 2 * delN c n - delN c n) (dTh (dRs ι u z))
      (c.cK / c.E1 * eN c e₀ n / delN c n ^ 3) := by
    exact (hdR.dS hδn h3 1 0).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hθZ : Bd (rhoN c n - 2 * delN c n - delN c n) (dTh (dZs ι u z))
      (c.cK / c.E1 * eN c e₀ n / delN c n ^ 3) := by
    exact (hdZ.dS hδn h3 1 0).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hρ3 : rhoN c n - 2 * delN c n - delN c n = rhoN c (n + 1) := by
    rw [rho_succ]; ring
  rw [hρ3] at hθR hθZ
  have hana1 := A.frame.ana_dRs K.G.dio K.G.γ_pos
  have hana2 := A.frame.ana_dZs K.G.dio K.G.γ_pos
  have hreal := A.frame.isReal_dRs (ι := ι) I.real_u I.real_z
  refine ⟨I.ana_u.add hana1, I.ana_z.add hana2, I.real_u.add hreal.1, I.real_z.add hreal.2,
    hER.strip hρ1, hEZ.strip hρ1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Bd (rhoN c (n + 1)) (u + dRs ι u z - u₀) (SK c e₀ (n + 1))
    rw [show u + dRs ι u z - u₀ = (u - u₀) + dRs ι u z by ring, SK, Finset.sum_range_succ]
    exact (I.du.strip hρ0).add (hdR.strip hρ1)
  · change Bd (rhoN c (n + 1)) (z + dZs ι u z - z₀) (SK c e₀ (n + 1))
    rw [show z + dZs ι u z - z₀ = (z - z₀) + dZs ι u z by ring, SK, Finset.sum_range_succ]
    exact (I.dz.strip hρ0).add (hdZ.strip hρ1)
  · change Bd (rhoN c (n + 1)) (dS 1 0 (u + dRs ι u z) - dTh u₀) (St c e₀ (n + 1))
    rw [d_add I.ana_u hana1,
      show dS 1 0 u + dS 1 0 (dRs ι u z) - dTh u₀ = (dTh u - dTh u₀) + dTh (dRs ι u z) by
        simp only [dTh]; ring,
      St, Finset.sum_range_succ]
    exact (I.dut.strip hρ0).add hθR
  · change Bd (rhoN c (n + 1)) (dS 1 0 (z + dZs ι u z) - dTh z₀) (St c e₀ (n + 1))
    rw [d_add I.ana_z hana2,
      show dS 1 0 z + dS 1 0 (dZs ι u z) - dTh z₀ = (dTh z - dTh z₀) + dTh (dZs ι u z) by
        simp only [dTh]; ring,
      St, Finset.sum_range_succ]
    exact (I.dzt.strip hρ0).add hθZ
  · change Bd (rhoN c (n + 1)) (dS ι 2 (u + dRs ι u z) - Lt ι u₀) (SL c e₀ (n + 1))
    rw [d_add I.ana_u hana1,
      show dS ι 2 u + dS ι 2 (dRs ι u z) - Lt ι u₀ = (Lt ι u - Lt ι u₀) + Lt ι (dRs ι u z) by
        simp only [Lt]; ring,
      SL, Finset.sum_range_succ]
    exact (I.duL.strip hρ0).add (hLR.strip hρ1)
  · change Bd (rhoN c (n + 1)) (dS ι 2 (z + dZs ι u z) - Lt ι z₀) (SL c e₀ (n + 1))
    rw [d_add I.ana_z hana2,
      show dS ι 2 z + dS ι 2 (dZs ι u z) - Lt ι z₀ = (Lt ι z - Lt ι z₀) + Lt ι (dZs ι u z) by
        simp only [Lt]; ring,
      SL, Finset.sum_range_succ]
    exact (I.dzL.strip hρ0).add (hLZ.strip hρ1)

/-- **The invariant holds at every step.** -/
theorem inv_all (n : ℕ) : Inv c ι u₀ z₀ e₀ n := by
  induction n with
  | zero => exact K.inv_zero
  | succ n ih => exact K.inv_succ ih

end KamH

end Iter

/-! ## Limits in a strip -/

/-- Partial sums of increments bound the distance to the start. -/
theorem Bd_sub_zero_of_incr {r : ℝ} {x : ℕ → FA} {d : ℕ → ℝ}
    (hd : ∀ n, Bd r (x (n + 1) - x n) (d n)) (n : ℕ) :
    Bd r (x n - x 0) (∑ j ∈ Finset.range n, d j) := by
  induction n with
  | zero => simpa using Bd_zero r
  | succ n ih =>
    rw [Finset.sum_range_succ, show x (n + 1) - x 0 = (x n - x 0) + (x (n + 1) - x n) by ring]
    exact ih.add (hd n)

/-- **Limits in a strip.** If the increments of a sequence in `𝔸` are summable in the strip norm
of width `r ≥ 0` and the first term is bounded there, the sequence converges in that norm, with
the tail bounds `‖x_∞ − x_n‖_r ≤ ∑_{m ≥ 0} d_{n+m}`. -/
theorem strip_limit {r : ℝ} (hr : 0 ≤ r) {x : ℕ → FA} {d : ℕ → ℝ} {B : ℝ}
    (h0 : Bd r (x 0) B) (hd : ∀ n, Bd r (x (n + 1) - x n) (d n)) (hs : Summable d) :
    ∃ y : FA, ∀ n, Bd r (y - x n) (∑' m, d (n + m)) := by
  have : Fact (0 ≤ r) := ⟨hr⟩
  have hw : ∀ n, InWeighted r (coeff (x n)) := fun n => by
    have h1 := (Bd_sub_zero_of_incr hd n).add h0
    rw [sub_add_cancel] at h1
    exact h1.1
  set X : ℕ → WEll1Z2 r := fun n => liftS (x n) (hw n) with hX
  have hXd : ∀ n, dist (X n) (X (n + 1)) ≤ d n := fun n => by
    rw [dist_comm, dist_eq_norm]
    have e : X (n + 1) - X n = liftS (x (n + 1) - x n) (hd n).1 :=
      ext_coeff fun k => by simp [hX, liftS]
    rw [e, norm_liftS]; exact (hd n).2
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hXd hs)
  refine ⟨toFA hr Y, fun n => ?_⟩
  have hdist := dist_le_tsum_of_dist_le_of_tendsto d hXd hs hY n
  rw [dist_comm, dist_eq_norm] at hdist
  have e : toFA hr Y - x n = toFA hr (Y - X n) := by
    rw [map_sub, hX, toFA_liftS]
  rw [e]
  exact (Bd_toFA hr _).le hdist

/-- Coefficients converge along a sequence converging in a strip norm (`r ≥ 0`). -/
theorem tendsto_coeff_of_Bd {r : ℝ} (hr : 0 ≤ r) {x : ℕ → FA} {y : FA} {t : ℕ → ℝ}
    (h : ∀ n, Bd r (y - x n) (t n)) (ht : Tendsto t atTop (𝓝 0)) (k : ℤ × ℤ) :
    Tendsto (fun n => coeff (x n) k) atTop (𝓝 (coeff y k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ht
  have := (h n).norm_coeff_le hr k
  rw [coeff_sub] at this
  rw [norm_sub_rev]; exact this

/-- **Derivatives pass to the limit.** If `x_n → y` and `dS a b x_n → y'` in a strip norm, and
`y` is analytic, then `dS a b y = y'`. -/
theorem dS_limit {r : ℝ} (hr : 0 ≤ r) {a b : ℂ} {x : ℕ → FA} {y y' : FA} {t t' : ℕ → ℝ}
    (hx : ∀ n, Ana (x n)) (hy : Ana y) (h : ∀ n, Bd r (y - x n) (t n))
    (h' : ∀ n, Bd r (y' - dS a b (x n)) (t' n)) (ht : Tendsto t atTop (𝓝 0))
    (ht' : Tendsto t' atTop (𝓝 0)) : dS a b y = y' := by
  refine ext_coeff fun k => ?_
  have h1 := tendsto_coeff_of_Bd hr h ht k
  have h2 := tendsto_coeff_of_Bd hr h' ht' k
  have h3 : Tendsto (fun n => coeff (dS a b (x n)) k) atTop
      (𝓝 (Complex.I * (a * k.1 + b * k.2) * coeff y k)) := by
    have := h1.const_mul (Complex.I * (a * k.1 + b * k.2))
    refine this.congr fun n => ?_
    rw [(hx n).coeff_dS]; rfl
  rw [hy.coeff_dS]
  exact tendsto_nhds_unique h3 h2

/-- An element bounded by a sequence tending to `0` (on a strip `r ≥ 0`) is `0`. -/
theorem eq_zero_of_Bd_tendsto {r : ℝ} (hr : 0 ≤ r) {x : FA} {t : ℕ → ℝ}
    (h : ∀ n, Bd r x (t n)) (ht : Tendsto t atTop (𝓝 0)) : x = 0 := by
  refine ext_coeff fun k => ?_
  rw [coeff_zero, ← norm_eq_zero]
  refine le_antisymm (ge_of_tendsto' ht fun n => (h n).norm_coeff_le hr k) (norm_nonneg _)

/-- Tails of a summable nonnegative series tend to `0`. -/
theorem tail_tendsto (d : ℕ → ℝ) : Tendsto (fun n => ∑' m, d (n + m)) atTop (𝓝 0) := by
  have := tendsto_sum_nat_add d
  simpa only [add_comm] using this

/-- Tails are bounded by the total sum. -/
theorem tail_le_total {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (hs : Summable d) (n : ℕ) :
    ∑' m, d (n + m) ≤ ∑' m, d m := by
  have h := hs.sum_add_tsum_nat_add n
  have h1 : 0 ≤ ∑ i ∈ Finset.range n, d i := Finset.sum_nonneg fun i _ => hd i
  simp only [add_comm _ n] at h
  linarith

/-- Tails are nonnegative. -/
theorem tail_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) (n : ℕ) : 0 ≤ ∑' m, d (n + m) :=
  tsum_nonneg fun m => hd (n + m)

/-- Reality passes to coefficientwise limits. -/
theorem isReal_limit {r : ℝ} (hr : 0 ≤ r) {x : ℕ → FA} {y : FA} {t : ℕ → ℝ}
    (hx : ∀ n, IsReal (x n)) (h : ∀ n, Bd r (y - x n) (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    IsReal y := by
  refine IsReal.of_coeff fun k => ?_
  have h1 := tendsto_coeff_of_Bd hr h ht (-k)
  have h2 := (Complex.continuous_conj.tendsto _).comp (tendsto_coeff_of_Bd hr h ht k)
  have h3 : (fun n => coeff (x n) (-k)) = (starRingEnd ℂ) ∘ fun n => coeff (x n) k := by
    funext n; exact (hx n).coeff_neg k
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-! ## The limit torus -/

/-- The limiting strip width `ρ_∞ = ρ₀ − 6δ₀`. -/
def rInf (c : SC) : ℝ := c.ρ - 6 * c.δ0

namespace KamH

variable {c : SC} {ι : ℝ} {u₀ z₀ : FA} {e₀ μ : ℝ} (K : KamH c ι u₀ z₀ e₀ μ)
include K

/-- The bounds at every iterate. -/
theorem adm_n (n : ℕ) : AdmBounds c ι (rhoN c n) (iterK ι u₀ z₀ n).1 (iterK ι u₀ z₀ n).2 :=
  K.hadm _ _ _ (K.rho_gt n).le (K.rho_le n) (K.inv_all n).ana_u (K.inv_all n).ana_z
    (K.close_of_inv (K.inv_all n))

/-- The step hypotheses at every iterate. -/
theorem stepH_n (n : ℕ) : StepH (c.withρ (rhoN c n)) ι (iterK ι u₀ z₀ n).1 (iterK ι u₀ z₀ n).2
    (eN c e₀ n) (delN c n) :=
  stepH_of_adm K.G (K.adm_n n) (K.rho_le n) (K.inv_all n).eR (K.inv_all n).eZ (K.eN_le_θ n)
    (kamDelta_pos K.hδ0 n) (K.del_le n) (K.three_del_le n)

/-- `ρ_∞ > 0`. -/
theorem rInf_pos : 0 < rInf c := by unfold rInf; linarith [K.hρ6]

/-- `ρ_∞ ≤ ρ_{n+1} ≤ ρ_n − 2δ_n`. -/
theorem rInf_le (n : ℕ) : rInf c ≤ rhoN c (n + 1) ∧ rhoN c (n + 1) ≤ rhoN c n - 2 * delN c n := by
  have hδn : 0 < delN c n := kamDelta_pos K.hδ0 n
  refine ⟨(K.rho_gt (n + 1)).le, ?_⟩
  rw [rho_succ]; linarith

/-- **The increments of the iteration** on the limiting strip. -/
theorem incr (n : ℕ) :
    Bd (rInf c) ((iterK ι u₀ z₀ (n + 1)).1 - (iterK ι u₀ z₀ n).1)
        (c.cK * eN c e₀ n / delN c n ^ 2) ∧
      Bd (rInf c) ((iterK ι u₀ z₀ (n + 1)).2 - (iterK ι u₀ z₀ n).2)
        (c.cK * eN c e₀ n / delN c n ^ 2) ∧
      Bd (rInf c) (dTh (iterK ι u₀ z₀ (n + 1)).1 - dTh (iterK ι u₀ z₀ n).1)
        (c.cK / c.E1 * eN c e₀ n / delN c n ^ 3) ∧
      Bd (rInf c) (dTh (iterK ι u₀ z₀ (n + 1)).2 - dTh (iterK ι u₀ z₀ n).2)
        (c.cK / c.E1 * eN c e₀ n / delN c n ^ 3) ∧
      Bd (rInf c) (Lt ι (iterK ι u₀ z₀ (n + 1)).1 - Lt ι (iterK ι u₀ z₀ n).1)
        (c.cL * eN c e₀ n / delN c n ^ 2) ∧
      Bd (rInf c) (Lt ι (iterK ι u₀ z₀ (n + 1)).2 - Lt ι (iterK ι u₀ z₀ n).2)
        (c.cL * eN c e₀ n / delN c n ^ 2) := by
  set u := (iterK ι u₀ z₀ n).1
  set z := (iterK ι u₀ z₀ n).2
  have SH := K.stepH_n n
  have I := K.inv_all n
  have hδn : 0 < delN c n := kamDelta_pos K.hδ0 n
  obtain ⟨h1, h2⟩ := K.rInf_le n
  have hs : ∀ {x : FA} {B : ℝ}, Bd (rhoN c n - 2 * delN c n) x B → Bd (rInf c) x B :=
    fun hx => hx.strip (h1.trans h2)
  have hdR : Bd (rhoN c n - 2 * delN c n) (dRs ι u z) (c.cK * eN c e₀ n / delN c n ^ 2) :=
    SH.bdR
  have hdZ : Bd (rhoN c n - 2 * delN c n) (dZs ι u z) (c.cK * eN c e₀ n / delN c n ^ 2) :=
    SH.bdZ
  have h3 : delN c n ≤ rhoN c n - 2 * delN c n := by
    have := K.three_del_le n; linarith
  have hρ3 : rInf c ≤ rhoN c n - 2 * delN c n - delN c n := by
    have := h1; rw [rho_succ] at this; linarith
  have hθ : ∀ {x : FA}, Bd (rhoN c n - 2 * delN c n) x (c.cK * eN c e₀ n / delN c n ^ 2) →
      Bd (rInf c) (dTh x) (c.cK / c.E1 * eN c e₀ n / delN c n ^ 3) := fun hx => by
    exact ((hx.dS hδn h3 1 0).strip hρ3).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hana1 := (K.adm_n n).frame.ana_dRs K.G.dio K.G.γ_pos
  have hana2 := (K.adm_n n).frame.ana_dZs K.G.dio K.G.γ_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Bd (rInf c) (u + dRs ι u z - u) _
    rw [add_sub_cancel_left]; exact hs hdR
  · change Bd (rInf c) (z + dZs ι u z - z) _
    rw [add_sub_cancel_left]; exact hs hdZ
  · change Bd (rInf c) (dS 1 0 (u + dRs ι u z) - dS 1 0 u) _
    rw [dS_add _ _ I.ana_u hana1, add_sub_cancel_left]; exact hθ hdR
  · change Bd (rInf c) (dS 1 0 (z + dZs ι u z) - dS 1 0 z) _
    rw [dS_add _ _ I.ana_z hana2, add_sub_cancel_left]; exact hθ hdZ
  · change Bd (rInf c) (dS ι 2 (u + dRs ι u z) - dS ι 2 u) _
    rw [dS_add _ _ I.ana_u hana1, add_sub_cancel_left]; exact hs SH.bLdR
  · change Bd (rInf c) (dS ι 2 (z + dZs ι u z) - dS ι 2 z) _
    rw [dS_add _ _ I.ana_z hana2, add_sub_cancel_left]; exact hs SH.bLdZ

/-- The displacement series are summable. -/
theorem summ (τ : ℕ) (hτ : τ ≤ 4) {C' : ℝ} (hC : 0 ≤ C') :
    Summable (fun j => C' * eN c e₀ j / delN c j ^ τ) ∧
      ∑' j, C' * eN c e₀ j / delN c j ^ τ ≤ 2 * C' * e₀ / c.δ0 ^ τ := by
  obtain ⟨hs, htot, -⟩ := K.seq.2.2 τ C' hτ hC
  exact ⟨hs, htot⟩

/-- Nonnegativity of the displacement terms. -/
theorem term_nonneg (τ : ℕ) {C' : ℝ} (hC : 0 ≤ C') (j : ℕ) :
    0 ≤ C' * eN c e₀ j / delN c j ^ τ := by
  have := kamExact_nonneg K.hκ.le K.he₀ (δ₀ := c.δ0) j
  have := kamDelta_pos K.hδ0 j
  unfold eN delN; positivity

/-- **The KAM theorem for the flow form (`kam_flow_torus`).** Under the hypotheses `KamH` the
iteration converges on the strip `ρ_∞ = ρ₀ − 6δ₀` to an analytic, real torus `(u, z)` that solves
the flow-form invariance equation **exactly**, `D 𝓛K = n` (`resR = resZ = 0`), and stays
`μ`-close to the initial torus in `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z`. -/
theorem kam_flow_torus :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resR ι u z = 0 ∧ resZ ι u z = 0 ∧
      Close (rInf c) ι u z u₀ z₀ μ := by
  have hr := K.rInf_pos
  have hr0 := hr.le
  -- the six sequences and their increments
  set xu : ℕ → FA := fun n => (iterK ι u₀ z₀ n).1 with hxu
  set xz : ℕ → FA := fun n => (iterK ι u₀ z₀ n).2 with hxz
  have hcKe : 0 ≤ c.cK / c.E1 := div_nonneg K.hcK K.G.hE1.1.le
  obtain ⟨sK, tK⟩ := K.summ 2 (by norm_num) K.hcK
  obtain ⟨st, tt⟩ := K.summ 3 (by norm_num) hcKe
  obtain ⟨sL, tL⟩ := K.summ 2 (by norm_num) K.hcL
  have A0 := K.adm_n 0
  have hrr0 : rInf c ≤ rhoN c 0 := by unfold rInf rhoN kamRadius; linarith [K.hδ0]
  have b0 : ∀ {x : FA} {B : ℝ}, Bd (rhoN c 0) x B → Bd (rInf c) x B := fun hx => hx.strip hrr0
  obtain ⟨yu, hyu⟩ := strip_limit hr0 (x := xu) (b0 A0.hu) (fun n => (K.incr n).1) sK
  obtain ⟨yz, hyz⟩ := strip_limit hr0 (x := xz) (b0 A0.hz) (fun n => (K.incr n).2.1) sK
  obtain ⟨yut, hyut⟩ := strip_limit hr0 (x := fun n => dTh (xu n)) (b0 A0.hRt)
    (fun n => (K.incr n).2.2.1) st
  obtain ⟨yzt, hyzt⟩ := strip_limit hr0 (x := fun n => dTh (xz n)) (b0 A0.hzt)
    (fun n => (K.incr n).2.2.2.1) st
  obtain ⟨yuL, hyuL⟩ := strip_limit hr0 (x := fun n => Lt ι (xu n)) (b0 A0.hLR)
    (fun n => (K.incr n).2.2.2.2.1) sL
  obtain ⟨yzL, hyzL⟩ := strip_limit hr0 (x := fun n => Lt ι (xz n)) (b0 A0.hLz)
    (fun n => (K.incr n).2.2.2.2.2) sL
  have tKt := tail_tendsto (fun j => c.cK * eN c e₀ j / delN c j ^ 2)
  have ttt := tail_tendsto (fun j => c.cK / c.E1 * eN c e₀ j / delN c j ^ 3)
  have tLt := tail_tendsto (fun j => c.cL * eN c e₀ j / delN c j ^ 2)
  -- analyticity and reality of the limits
  have hBu : Bd (rInf c) yu (∑' m, c.cK * eN c e₀ (0 + m) / delN c (0 + m) ^ 2 + c.au) := by
    have := (hyu 0).add (b0 A0.hu); rwa [sub_add_cancel] at this
  have hBz : Bd (rInf c) yz (∑' m, c.cK * eN c e₀ (0 + m) / delN c (0 + m) ^ 2 + c.az) := by
    have := (hyz 0).add (b0 A0.hz); rwa [sub_add_cancel] at this
  have ana_u : Ana yu := ⟨_, _, hr, hBu⟩
  have ana_z : Ana yz := ⟨_, _, hr, hBz⟩
  have real_u : IsReal yu := isReal_limit hr0 (fun n => (K.inv_all n).real_u) hyu tKt
  have real_z : IsReal yz := isReal_limit hr0 (fun n => (K.inv_all n).real_z) hyz tKt
  -- derivatives of the limits
  have eut : dTh yu = yut := dS_limit hr0 (fun n => (K.inv_all n).ana_u) ana_u hyu hyut tKt ttt
  have ezt : dTh yz = yzt := dS_limit hr0 (fun n => (K.inv_all n).ana_z) ana_z hyz hyzt tKt ttt
  have euL : Lt ι yu = yuL := dS_limit hr0 (fun n => (K.inv_all n).ana_u) ana_u hyu hyuL tKt tLt
  have ezL : Lt ι yz = yzL := dS_limit hr0 (fun n => (K.inv_all n).ana_z) ana_z hyz hyzL tKt tLt
  -- closeness
  have hK0 : ∑' m, c.cK * eN c e₀ (0 + m) / delN c (0 + m) ^ 2 ≤ μ := by
    simp only [zero_add]; exact tK.trans K.hμK
  have ht0 : ∑' m, c.cK / c.E1 * eN c e₀ (0 + m) / delN c (0 + m) ^ 3 ≤ μ := by
    simp only [zero_add]; exact tt.trans K.hμt
  have hL0 : ∑' m, c.cL * eN c e₀ (0 + m) / delN c (0 + m) ^ 2 ≤ μ := by
    simp only [zero_add]; exact tL.trans K.hμL
  have hclose : Close (rInf c) ι yu yz u₀ z₀ μ :=
    ⟨(hyu 0).le hK0, (hyz 0).le hK0, by rw [eut]; exact (hyut 0).le ht0,
      by rw [ezt]; exact (hyzt 0).le ht0, by rw [euL]; exact (hyuL 0).le hL0,
      by rw [ezL]; exact (hyzL 0).le hL0⟩
  -- exactness: the residuals vanish
  set m1 : Fin 6 → ℝ := ![1, 1, 0, 0, 1, 1] with hm1
  have m1nn : ∀ i, 0 ≤ m1 i := fun i => by fin_cases i <;> simp [hm1]
  set sq : ℕ → ℝ := fun n => (∑' m, c.cK * eN c e₀ (n + m) / delN c (n + m) ^ 2) +
    (∑' m, c.cL * eN c e₀ (n + m) / delN c (n + m) ^ 2) with hsq
  have sqt : Tendsto sq atTop (𝓝 0) := by simpa using tKt.add tLt
  have sqnn : ∀ n, 0 ≤ sq n := fun n => add_nonneg
    (tail_nonneg (K.term_nonneg 2 K.hcK) n) (tail_nonneg (K.term_nonneg 2 K.hcL) n)
  have sqle : ∀ n, sq n ≤ sq 0 := fun n => by
    have h1 := tail_le_total (K.term_nonneg 2 K.hcK) sK n
    have h2 := tail_le_total (K.term_nonneg 2 K.hcL) sL n
    simp only [hsq, zero_add]; linarith
  have hb : ∀ n, ∀ i, Bd (rInf c) ((xK ι yu yz - xK ι (xu n) (xz n)) i) ((sq n • m1) i) := by
    intro n i
    have tK0 := tail_nonneg (K.term_nonneg 2 K.hcK) n
    have tL0 := tail_nonneg (K.term_nonneg 2 K.hcL) n
    fin_cases i
    · exact (hyu n).le (by simp [hm1, hsq]; linarith)
    · exact (hyz n).le (by simp [hm1, hsq]; linarith)
    · simpa [xK, hm1] using Bd_zero (rInf c)
    · simpa [xK, hm1] using Bd_zero (rInf c)
    · have := (hyuL n).le (B' := sq n) (by simp only [hsq]; linarith)
      rw [← euL] at this; simpa [xK, hm1] using this
    · have := (hyzL n).le (B' := sq n) (by simp only [hsq]; linarith)
      rw [← ezL] at this; simpa [xK, hm1] using this
  have hx : ∀ n, ∀ i, Bd (rInf c) (xK ι (xu n) (xz n) i) (c.avec i) := by
    intro n i
    have A := K.adm_n n
    have hs : ∀ {x : FA} {B : ℝ}, Bd (rhoN c n) x B → Bd (rInf c) x B :=
      fun hx => hx.strip (K.rho_gt n).le
    have hc : Real.exp (rInf c) ≤ c.ac :=
      (Real.exp_le_exp.2 (by unfold rInf; linarith [K.hδ0])).trans K.G.hac
    fin_cases i
    · exact hs A.hu
    · exact hs A.hz
    · exact (Bd_cS _).le hc
    · exact (Bd_sS _).le hc
    · exact hs A.hLR
    · exact hs A.hLz
  have av : ∀ i, 0 ≤ c.avec i := fun i => (hx 0 i).nonneg
  have exact_res : ∀ e : PolyExpr ℂ (Fin 6),
      (∀ n, Bd (rInf c) (PolyExpr.eval (xK ι (xu n) (xz n)) e) (eN c e₀ n)) →
      PolyExpr.eval (xK ι yu yz) e = 0 := by
    intro e he
    refine eq_zero_of_Bd_tendsto hr0
      (t := fun n => eN c e₀ n + sq n * PolyExpr.majD (c.avec + sq 0 • m1) m1 e)
      (fun n => ?_) ?_
    · have hL := Bd.eval_add_sub hr0 (hx n) (hb n) e
      rw [add_sub_cancel] at hL
      have e1 : PolyExpr.eval (xK ι yu yz) e = PolyExpr.eval (xK ι (xu n) (xz n)) e +
          (PolyExpr.eval (xK ι yu yz) e - PolyExpr.eval (xK ι (xu n) (xz n)) e) := by ring
      rw [e1]
      refine ((he n).add hL).le (add_le_add le_rfl ?_)
      rw [majD_smul]
      refine mul_le_mul_of_nonneg_left (PolyExpr.majD_mono (fun i => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have := av i; have := m1nn i; have := sqnn n; positivity) m1nn
        (fun i => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have := m1nn i; have := sqle n; nlinarith) (fun i => le_rfl) e) (sqnn n)
    · simpa using (K.seq.2.1).add (sqt.mul_const (PolyExpr.majD (c.avec + sq 0 • m1) m1 e))
  have eR : resR ι yu yz = 0 := exact_res resRp (fun n => ((K.inv_all n).eR).strip
    (K.rho_gt n).le)
  have eZ : resZ ι yu yz = 0 := exact_res resZp (fun n => ((K.inv_all n).eZ).strip
    (K.rho_gt n).le)
  exact ⟨yu, yz, ana_u, ana_z, real_u, real_z, eR, eZ, hclose⟩

end KamH

end PlasmaLean.Design.KamNewton
