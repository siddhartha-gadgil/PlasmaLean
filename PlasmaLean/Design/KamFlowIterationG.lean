/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamFlowStepG
public import PlasmaLean.Design.KamFlowIteration

/-!
# The KAM iteration for a generalised flow field: an exact invariant torus

The iteration of `Design/KamFlowIteration` for a field `F : FlowFieldG` (`Design/KamFlowFieldG`:
centre `R₀`, density exponent `p`, moving frame centre `A(φ)`), with the generalised Newton step
`FlowFieldG.StepH.kam_step` (`Design/KamFlowStepG`): losses `δ_j = δ₀ 2^{−j}`, strips
`ρ_{j+1} = ρ_j − 3δ_j`, errors dominated by `ē_{j+1} = κ ē_j²/δ_j⁴` (`SCG.eN`, with the
generalised `κ = SCG.kap`), convergence in `ℓ¹_{ρ_∞}(ℤ²)` under `32 κ e₀/δ₀⁴ ≤ 1`, and an
**exact** solution of the flow-form equation of `F` in the limit
(`FlowFieldG.KamHG.kam_flow_torus`).

Differences from `FlowField.KamH`:
* the constants are `c : SCG` (`Design/KamFlowStepG`), with exponent `c.p = F.p` (`GlobalHG.hp`);
* the Diophantine condition is split (`DiophantineSplit (ι/2) dlow γ 1 Klow`, with `1 ≤ Klow`,
  `0 < dlow` and the loss threshold `e γ δ₀ ≤ dlow`, which then holds at every `δ_j ≤ δ₀`); the
  Rüssmann range `δ₀ ≤ 2/e` is no longer needed;
* the admissibility bounds (`AdmBoundsG`) also bound the frame vector `V₀ = K − A` and `R`.
  Since the centre does not depend on the torus, `V₀ − V₀⁽⁰⁾ = u − u₀`, so for `μ`-close tori
  these follow from bounds at the initial torus (`AdmBoundsG.bV0R_of_close`, `bR_of_close`).

**Reduction.** `FlowField.GlobalH.toG`, `FlowField.AdmBounds.toG`, `FlowField.KamH.toG`: the
hypotheses of `FlowField.KamH` for `F` and `c : SC` give those of `KamHG` for `F.toG` and
`c.toSCG` as soon as `e δ₀ ≤ 1` (the iterates and the limit are then the same:
`FlowField.toG_stepK`). The torus-A instance is `Design/KamTorusAExactG`.

**Sanity.** `FlowFieldG.iterK_zero`, `FlowField.toG_stepK`, `SCG.withρ_ρ`, `SCG.withρ_kap`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM WEll1Z2 Filter Topology

/-! ### The constants -/

namespace SCG

variable (c : SCG) (e₀ : ℝ)

/-- The generalised step constants with the strip width replaced by `ρ` (all derived constants
are unchanged). -/
def withρ (ρ : ℝ) : SCG := { c with ρ := ρ }

/-- **Sanity**: the strip width of `c.withρ ρ` is `ρ`. -/
theorem withρ_ρ (ρ : ℝ) : (c.withρ ρ).ρ = ρ := rfl

/-- **Sanity**: `κ` does not depend on the strip width. -/
theorem withρ_kap (ρ : ℝ) : (c.withρ ρ).kap = c.kap := rfl

/-- The extremal errors `ē_n` (with the generalised `κ`). -/
def eN (n : ℕ) : ℝ := kamExact c.kap c.δ0 e₀ n
/-- Partial displacement sum (torus). -/
def SK (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cK * c.eN e₀ j / delN c.toSC j ^ 2
/-- Partial displacement sum (`θ`-derivatives). -/
def St (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cK / c.E1 * c.eN e₀ j / delN c.toSC j ^ 3
/-- Partial displacement sum (transport). -/
def SL (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c.cL * c.eN e₀ j / delN c.toSC j ^ 2

end SCG

namespace FlowFieldG

variable (F : FlowFieldG)

/-- The torus, frame-vector and frame bounds required by a generalised Newton step, at strip
width `ρ`, with the constants of `c`. -/
structure AdmBoundsG (c : SCG) (ι ρ : ℝ) (u z : FA) : Prop where
  /-- Frame hypotheses. -/
  frame : F.FrameHyp u z
  /-- Torus bound. -/
  hu : Bd ρ u c.au
  /-- Torus bound. -/
  hz : Bd ρ z c.az
  /-- Frame-vector bound. -/
  hV0R : Bd ρ (F.V0R u) c.avR
  /-- Frame-vector bound. -/
  hV0Z : Bd ρ (F.V0Z z) c.avZ
  /-- Bound of `R = R₀ + u`. -/
  hR : Bd ρ (F.R u) c.aR
  /-- Torus bound. -/
  hRt : Bd ρ (Rt u) c.aRt
  /-- Torus bound. -/
  hzt : Bd ρ (zt z) c.azt
  /-- Torus bound. -/
  hLR : Bd ρ (LR ι u) c.aLR
  /-- Torus bound. -/
  hLz : Bd ρ (Lz ι z) c.aLz
  /-- Field bound. -/
  hbD : Bd ρ (F.Dof u z) c.bD
  /-- Field bound. -/
  hbDu : Bd ρ (F.Du u z) c.bDu
  /-- Field bound. -/
  hbDz : Bd ρ (F.Dz u z) c.bDz
  /-- Field bound. -/
  hbnR : Bd ρ (F.nR u z) c.bnR
  /-- Field bound. -/
  hbnRu : Bd ρ (F.nRu u z) c.bnRu
  /-- Field bound. -/
  hbnRz : Bd ρ (F.nRz u z) c.bnRz
  /-- Field bound. -/
  hbnZ : Bd ρ (F.nZ u z) c.bnZ
  /-- Field bound. -/
  hbnZu : Bd ρ (F.nZu u z) c.bnZu
  /-- Field bound. -/
  hbnZz : Bd ρ (F.nZz u z) c.bnZz
  /-- Inverse bound. -/
  hsD : Bd ρ (F.Di u z) c.sD
  /-- Inverse bound. -/
  hsR : Bd ρ (F.Ri u) c.sR
  /-- Inverse bound. -/
  hsW : Bd ρ (F.Wi u z) c.sW
  /-- Torsion bound. -/
  hT : Bd ρ (F.Talg u z) c.tT
  /-- Twist. -/
  hτ : c.τ ≤ ‖avg (F.Talg u z)‖

/-- **The frame vector of a close torus.** Since the centre does not depend on the torus,
`V₀_R(u) − V₀_R(u₀) = u − u₀`, so `‖V₀_R(u)‖ ≤ ‖V₀_R(u₀)‖ + μ`. -/
theorem AdmBoundsG.bV0R_of_close {ρ ι μ a : ℝ} {u z u₀ z₀ : FA} (h0 : Bd ρ (F.V0R u₀) a)
    (hC : Close ρ ι u z u₀ z₀ μ) : Bd ρ (F.V0R u) (a + μ) := by
  have e : F.V0R u = F.V0R u₀ + (u - u₀) := by simp only [V0R, V0of]; ring
  rw [e]; exact h0.add hC.du

/-- The vertical frame vector of a close torus: `‖V₀_z(z)‖ ≤ ‖V₀_z(z₀)‖ + μ`. -/
theorem AdmBoundsG.bV0Z_of_close {ρ ι μ a : ℝ} {u z u₀ z₀ : FA} (h0 : Bd ρ (F.V0Z z₀) a)
    (hC : Close ρ ι u z u₀ z₀ μ) : Bd ρ (F.V0Z z) (a + μ) := by
  have e : F.V0Z z = F.V0Z z₀ + (z - z₀) := by simp only [V0Z, V0of]; ring
  rw [e]; exact h0.add hC.dz

/-- `R` of a close torus: `‖R(u)‖ ≤ ‖R(u₀)‖ + μ`. -/
theorem AdmBoundsG.bR_of_close {ρ ι μ a : ℝ} {u z u₀ z₀ : FA} (h0 : Bd ρ (F.R u₀) a)
    (hC : Close ρ ι u z u₀ z₀ μ) : Bd ρ (F.R u) (a + μ) := by
  have e : F.R u = F.R u₀ + (u - u₀) := by simp only [R, RofG]; ring
  rw [e]; exact h0.add hC.du

/-- The global (numerical) conditions on the generalised constants. -/
structure GlobalHG (c : SCG) (ι : ℝ) : Prop where
  /-- The exponent of the constants is that of the field. -/
  hp : F.p = c.p
  /-- Split Diophantine frequency. -/
  dio : DiophantineSplit (ι / 2) c.dlow c.γ 1 c.Klow
  /-- At least one low mode. -/
  hK : 1 ≤ c.Klow
  /-- `dlow > 0`. -/
  hd : 0 < c.dlow
  /-- `γ > 0`. -/
  γ_pos : 0 < c.γ
  /-- The loss threshold of the low modes at the initial loss: `e γ δ₀ ≤ dlow`. -/
  hlow : Real.exp 1 * c.γ * c.δ0 ≤ c.dlow
  /-- Twist margin. -/
  hτ' : 0 < c.τ'
  /-- Taylor constant (`R`). -/
  hC2R : PolyExpr.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resRp / 2 ≤ c.C2
  /-- Taylor constant (`z`). -/
  hC2Z : PolyExpr.majD2 (c.avec + c.Tq • c.mvec) c.mvec F.resZp / 2 ≤ c.C2
  /-- Bound of `cos 2φ`, `sin 2φ` on the initial strip. -/
  hac : Real.exp c.ρ ≤ c.ac
  /-- `0 < E1 ≤ e`. -/
  hE1 : 0 < c.E1 ∧ c.E1 ≤ Real.exp 1
  /-- `cK ≤ cKb`, `cL ≤ cLb`. -/
  hcb : c.cK ≤ c.cKb ∧ c.cL ≤ c.cLb

/-- **A generalised step is admissible**: from the bounds at strip `ρ ≤ ρ₀`, the global
conditions and the error conditions, the hypotheses `StepH` of `kam_step` hold. -/
theorem stepH_of_admG {F : FlowFieldG} {c : SCG} {ι ρ : ℝ} {u z : FA} {e δ : ℝ}
    (G : F.GlobalHG c ι) (A : F.AdmBoundsG c ι ρ u z) (hρ : ρ ≤ c.ρ)
    (heR : Bd ρ (F.resR ι u z) e) (heZ : Bd ρ (F.resZ ι u z) e) (heθ : e ≤ c.θ * δ ^ 4)
    (hδ : 0 < δ) (hδ0 : δ ≤ c.δ0) (h3δ : 3 * δ ≤ ρ) : F.StepH (c.withρ ρ) ι u z e δ where
  frame := A.frame
  hp := G.hp
  dio := G.dio
  hK := G.hK
  hd := G.hd
  γ_pos := G.γ_pos
  hlow := G.hlow
  hu := A.hu
  hz := A.hz
  hV0R := A.hV0R
  hV0Z := A.hV0Z
  hR := A.hR
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
  hE1 := G.hE1
  hcb := G.hcb

/-! ## The iteration -/

/-- One generalised Newton step `(u, z) ↦ (u + ΔR, z + Δz)`. -/
def stepK (ι : ℝ) (q : FA × FA) : FA × FA := (q.1 + F.dRs ι q.1 q.2, q.2 + F.dZs ι q.1 q.2)

/-- The KAM iterates. -/
def iterK (ι : ℝ) (u₀ z₀ : FA) : ℕ → FA × FA
  | 0 => (u₀, z₀)
  | n + 1 => F.stepK ι (iterK ι u₀ z₀ n)

/-- **Sanity**: the iteration starts at the initial torus. -/
theorem iterK_zero (ι : ℝ) (u₀ z₀ : FA) : F.iterK ι u₀ z₀ 0 = (u₀, z₀) := rfl

section Iter

variable (c : SCG) (ι : ℝ) (u₀ z₀ : FA) (e₀ μ : ℝ)

/-- The hypotheses of the generalised KAM iteration. -/
structure KamHG : Prop where
  /-- Global numerical conditions. -/
  G : F.GlobalHG c ι
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
    Close ρ ι u z u₀ z₀ μ → F.AdmBoundsG c ι ρ u z
  /-- The initial torus is analytic. -/
  ana_u₀ : Ana u₀
  /-- The initial torus is analytic. -/
  ana_z₀ : Ana z₀
  /-- The initial torus is real. -/
  real_u₀ : IsReal u₀
  /-- The initial torus is real. -/
  real_z₀ : IsReal z₀
  /-- Initial error. -/
  e0R : Bd c.ρ (F.resR ι u₀ z₀) e₀
  /-- Initial error. -/
  e0Z : Bd c.ρ (F.resZ ι u₀ z₀) e₀

/-- The invariant of the generalised iteration at step `n`. -/
structure InvG (n : ℕ) : Prop where
  /-- Analytic. -/
  ana_u : Ana (F.iterK ι u₀ z₀ n).1
  /-- Analytic. -/
  ana_z : Ana (F.iterK ι u₀ z₀ n).2
  /-- Real. -/
  real_u : IsReal (F.iterK ι u₀ z₀ n).1
  /-- Real. -/
  real_z : IsReal (F.iterK ι u₀ z₀ n).2
  /-- Error. -/
  eR : Bd (rhoN c.toSC n) (F.resR ι (F.iterK ι u₀ z₀ n).1 (F.iterK ι u₀ z₀ n).2) (c.eN e₀ n)
  /-- Error. -/
  eZ : Bd (rhoN c.toSC n) (F.resZ ι (F.iterK ι u₀ z₀ n).1 (F.iterK ι u₀ z₀ n).2) (c.eN e₀ n)
  /-- Displacement. -/
  du : Bd (rhoN c.toSC n) ((F.iterK ι u₀ z₀ n).1 - u₀) (c.SK e₀ n)
  /-- Displacement. -/
  dz : Bd (rhoN c.toSC n) ((F.iterK ι u₀ z₀ n).2 - z₀) (c.SK e₀ n)
  /-- Displacement. -/
  dut : Bd (rhoN c.toSC n) (dTh (F.iterK ι u₀ z₀ n).1 - dTh u₀) (c.St e₀ n)
  /-- Displacement. -/
  dzt : Bd (rhoN c.toSC n) (dTh (F.iterK ι u₀ z₀ n).2 - dTh z₀) (c.St e₀ n)
  /-- Displacement. -/
  duL : Bd (rhoN c.toSC n) (Lt ι (F.iterK ι u₀ z₀ n).1 - Lt ι u₀) (c.SL e₀ n)
  /-- Displacement. -/
  dzL : Bd (rhoN c.toSC n) (Lt ι (F.iterK ι u₀ z₀ n).2 - Lt ι z₀) (c.SL e₀ n)

variable {F c ι u₀ z₀ e₀ μ}

namespace KamHG

variable (K : F.KamHG c ι u₀ z₀ e₀ μ)
include K

/-- The scalar hypotheses of `kam_sequence` for the extremal errors. -/
theorem seq :
    (∀ j, c.eN e₀ j ≤ e₀ * (1 / 2) ^ (2 ^ j - 1) / 16 ^ j) ∧
    Tendsto (c.eN e₀) atTop (𝓝 0) ∧
    (∀ (τ : ℕ) (C' : ℝ), τ ≤ 4 → 0 ≤ C' →
      Summable (fun j => C' * c.eN e₀ j / kamDelta c.δ0 j ^ τ) ∧
      ∑' j, C' * c.eN e₀ j / kamDelta c.δ0 j ^ τ ≤ 2 * C' * c.eN e₀ 0 / c.δ0 ^ τ ∧
      ∀ n, ∑' j, C' * c.eN e₀ (j + n) / kamDelta c.δ0 (j + n) ^ τ ≤
        2 * C' * c.eN e₀ 0 / c.δ0 ^ τ * (1 / 2) ^ n) :=
  kam_sequence K.hκ K.hδ0 (kamExact_nonneg K.hκ.le K.he₀) (fun _ => le_rfl) K.hsmall

/-- Partial sums are bounded by the total displacement. -/
theorem partial_le (τ : ℕ) (hτ : τ ≤ 4) {C' : ℝ} (hC : 0 ≤ C') (n : ℕ) :
    ∑ j ∈ Finset.range n, C' * c.eN e₀ j / delN c.toSC j ^ τ ≤ 2 * C' * e₀ / c.δ0 ^ τ := by
  obtain ⟨hs, htot, -⟩ := K.seq.2.2 τ C' hτ hC
  have hnn : ∀ j, 0 ≤ C' * c.eN e₀ j / kamDelta c.δ0 j ^ τ := fun j => by
    have := kamExact_nonneg K.hκ.le K.he₀ (δ₀ := c.δ0) j
    have := kamDelta_pos K.hδ0 j
    unfold SCG.eN; positivity
  calc _ ≤ ∑' j, C' * c.eN e₀ j / kamDelta c.δ0 j ^ τ := hs.sum_le_tsum _ (fun i _ => hnn i)
    _ ≤ _ := htot

/-- `ρ_n > ρ_∞`. -/
theorem rho_gt (n : ℕ) : c.ρ - 6 * c.δ0 < rhoN c.toSC n := by
  have := kamRadius_gt (r₀ := c.ρ) (c := 3) (δ₀ := c.δ0) (by norm_num) K.hδ0 n
  unfold rhoN; linarith

/-- `ρ_n ≤ ρ₀`. -/
theorem rho_le (n : ℕ) : rhoN c.toSC n ≤ c.ρ := by
  induction n with
  | zero => simp [rhoN, kamRadius]
  | succ n ih =>
    have := kamRadius_succ_le (r₀ := c.ρ) (c := 3) (δ₀ := c.δ0) (by norm_num) K.hδ0.le n
    unfold rhoN at *; linarith

omit K in
/-- `ρ_{n+1} = ρ_n − 3δ_n`. -/
theorem rho_succ (n : ℕ) : rhoN c.toSC (n + 1) = rhoN c.toSC n - 3 * delN c.toSC n := rfl

/-- `3δ_n ≤ ρ_n`. -/
theorem three_del_le (n : ℕ) : 3 * delN c.toSC n ≤ rhoN c.toSC n := by
  have h1 := K.rho_gt (n + 1)
  rw [rho_succ] at h1
  have := K.hρ6; have := K.hδ0
  linarith

/-- `δ_n ≤ δ₀`. -/
theorem del_le (n : ℕ) : delN c.toSC n ≤ c.δ0 := by
  unfold delN kamDelta
  have := K.hδ0
  exact div_le_self this.le (one_le_pow₀ (by norm_num))

/-- The errors stay on the scale `θ δ_n⁴`. -/
theorem eN_le_θ (n : ℕ) : c.eN e₀ n ≤ c.θ * delN c.toSC n ^ 4 := by
  rw [K.hθ]; exact kamExact_le_θ K.hκ K.hδ0 K.he₀ K.hsmall n

/-- The iterates are `μ`-close to the initial torus. -/
theorem close_of_inv {n : ℕ} (I : F.InvG c ι u₀ z₀ e₀ n) :
    Close (rhoN c.toSC n) ι (F.iterK ι u₀ z₀ n).1 (F.iterK ι u₀ z₀ n).2 u₀ z₀ μ := by
  have hK := K.partial_le 2 (by norm_num) K.hcK n
  have ht := K.partial_le 3 (by norm_num) (div_nonneg K.hcK K.G.hE1.1.le) n
  have hL := K.partial_le 2 (by norm_num) K.hcL n
  exact ⟨I.du.le (hK.trans K.hμK), I.dz.le (hK.trans K.hμK), I.dut.le (ht.trans K.hμt),
    I.dzt.le (ht.trans K.hμt), I.duL.le (hL.trans K.hμL), I.dzL.le (hL.trans K.hμL)⟩

/-- The base case. -/
theorem inv_zero : F.InvG c ι u₀ z₀ e₀ 0 where
  ana_u := K.ana_u₀
  ana_z := K.ana_z₀
  real_u := K.real_u₀
  real_z := K.real_z₀
  eR := K.e0R
  eZ := K.e0Z
  du := by simpa [SCG.SK, iterK] using Bd_zero (rhoN c.toSC 0)
  dz := by simpa [SCG.SK, iterK] using Bd_zero (rhoN c.toSC 0)
  dut := by simpa [SCG.St, iterK] using Bd_zero (rhoN c.toSC 0)
  dzt := by simpa [SCG.St, iterK] using Bd_zero (rhoN c.toSC 0)
  duL := by simpa [SCG.SL, iterK] using Bd_zero (rhoN c.toSC 0)
  dzL := by simpa [SCG.SL, iterK] using Bd_zero (rhoN c.toSC 0)

/-- **The inductive step of the iteration.** -/
theorem inv_succ {n : ℕ} (I : F.InvG c ι u₀ z₀ e₀ n) : F.InvG c ι u₀ z₀ e₀ (n + 1) := by
  set u := (F.iterK ι u₀ z₀ n).1 with hu
  set z := (F.iterK ι u₀ z₀ n).2 with hz
  have A := K.hadm (rhoN c.toSC n) u z (K.rho_gt n).le (K.rho_le n) I.ana_u I.ana_z
    (K.close_of_inv I)
  have hδn : 0 < delN c.toSC n := kamDelta_pos K.hδ0 n
  have SH := stepH_of_admG K.G A (K.rho_le n) I.eR I.eZ (K.eN_le_θ n) hδn (K.del_le n)
    (K.three_del_le n)
  have hρ1 : rhoN c.toSC (n + 1) ≤ rhoN c.toSC n - 2 * delN c.toSC n := by
    rw [rho_succ]; linarith
  have hρ0 : rhoN c.toSC (n + 1) ≤ rhoN c.toSC n := hρ1.trans (by linarith)
  have hdR : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (F.dRs ι u z)
      (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bdR
  have hdZ : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (F.dZs ι u z)
      (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bdZ
  have hLR : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (Lt ι (F.dRs ι u z))
      (c.cL * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bLdR
  have hLZ : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (Lt ι (F.dZs ι u z))
      (c.cL * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bLdZ
  have hER : Bd (rhoN c.toSC n - 2 * delN c.toSC n)
      (F.resR ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.eN e₀ (n + 1)) := SH.bER'
  have hEZ : Bd (rhoN c.toSC n - 2 * delN c.toSC n)
      (F.resZ ι (u + F.dRs ι u z) (z + F.dZs ι u z)) (c.eN e₀ (n + 1)) := SH.bEZ'
  have h3 : delN c.toSC n ≤ rhoN c.toSC n - 2 * delN c.toSC n := by
    have := K.three_del_le n; linarith
  have hθR : Bd (rhoN c.toSC n - 2 * delN c.toSC n - delN c.toSC n) (dTh (F.dRs ι u z))
      (c.cK / c.E1 * c.eN e₀ n / delN c.toSC n ^ 3) := by
    exact (hdR.dS hδn h3 1 0).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hθZ : Bd (rhoN c.toSC n - 2 * delN c.toSC n - delN c.toSC n) (dTh (F.dZs ι u z))
      (c.cK / c.E1 * c.eN e₀ n / delN c.toSC n ^ 3) := by
    exact (hdZ.dS hδn h3 1 0).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hρ3 : rhoN c.toSC n - 2 * delN c.toSC n - delN c.toSC n = rhoN c.toSC (n + 1) := by
    rw [rho_succ]; ring
  rw [hρ3] at hθR hθZ
  have hana1 : Ana (F.dRs ι u z) := SH.kam_step.1
  have hana2 : Ana (F.dZs ι u z) := SH.kam_step.2.1
  have hreal := A.frame.isReal_dRs (ι := ι) I.real_u I.real_z
  refine ⟨I.ana_u.add hana1, I.ana_z.add hana2, I.real_u.add hreal.1, I.real_z.add hreal.2,
    hER.strip hρ1, hEZ.strip hρ1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Bd (rhoN c.toSC (n + 1)) (u + F.dRs ι u z - u₀) (c.SK e₀ (n + 1))
    rw [show u + F.dRs ι u z - u₀ = (u - u₀) + F.dRs ι u z by ring, SCG.SK,
      Finset.sum_range_succ]
    exact (I.du.strip hρ0).add (hdR.strip hρ1)
  · change Bd (rhoN c.toSC (n + 1)) (z + F.dZs ι u z - z₀) (c.SK e₀ (n + 1))
    rw [show z + F.dZs ι u z - z₀ = (z - z₀) + F.dZs ι u z by ring, SCG.SK,
      Finset.sum_range_succ]
    exact (I.dz.strip hρ0).add (hdZ.strip hρ1)
  · change Bd (rhoN c.toSC (n + 1)) (dS 1 0 (u + F.dRs ι u z) - dTh u₀) (c.St e₀ (n + 1))
    rw [dS_add 1 0 I.ana_u hana1,
      show dS 1 0 u + dS 1 0 (F.dRs ι u z) - dTh u₀ = (dTh u - dTh u₀) + dTh (F.dRs ι u z) by
        simp only [dTh]; ring,
      SCG.St, Finset.sum_range_succ]
    exact (I.dut.strip hρ0).add hθR
  · change Bd (rhoN c.toSC (n + 1)) (dS 1 0 (z + F.dZs ι u z) - dTh z₀) (c.St e₀ (n + 1))
    rw [dS_add 1 0 I.ana_z hana2,
      show dS 1 0 z + dS 1 0 (F.dZs ι u z) - dTh z₀ = (dTh z - dTh z₀) + dTh (F.dZs ι u z) by
        simp only [dTh]; ring,
      SCG.St, Finset.sum_range_succ]
    exact (I.dzt.strip hρ0).add hθZ
  · change Bd (rhoN c.toSC (n + 1)) (dS ι 2 (u + F.dRs ι u z) - Lt ι u₀) (c.SL e₀ (n + 1))
    rw [dS_add ι 2 I.ana_u hana1,
      show dS ι 2 u + dS ι 2 (F.dRs ι u z) - Lt ι u₀ = (Lt ι u - Lt ι u₀) + Lt ι (F.dRs ι u z) by
        simp only [Lt]; ring,
      SCG.SL, Finset.sum_range_succ]
    exact (I.duL.strip hρ0).add (hLR.strip hρ1)
  · change Bd (rhoN c.toSC (n + 1)) (dS ι 2 (z + F.dZs ι u z) - Lt ι z₀) (c.SL e₀ (n + 1))
    rw [dS_add ι 2 I.ana_z hana2,
      show dS ι 2 z + dS ι 2 (F.dZs ι u z) - Lt ι z₀ = (Lt ι z - Lt ι z₀) + Lt ι (F.dZs ι u z) by
        simp only [Lt]; ring,
      SCG.SL, Finset.sum_range_succ]
    exact (I.dzL.strip hρ0).add (hLZ.strip hρ1)

/-- **The invariant holds at every step.** -/
theorem inv_all (n : ℕ) : F.InvG c ι u₀ z₀ e₀ n := by
  induction n with
  | zero => exact K.inv_zero
  | succ n ih => exact K.inv_succ ih

/-- The bounds at every iterate. -/
theorem adm_n (n : ℕ) :
    F.AdmBoundsG c ι (rhoN c.toSC n) (F.iterK ι u₀ z₀ n).1 (F.iterK ι u₀ z₀ n).2 :=
  K.hadm _ _ _ (K.rho_gt n).le (K.rho_le n) (K.inv_all n).ana_u (K.inv_all n).ana_z
    (K.close_of_inv (K.inv_all n))

/-- The step hypotheses at every iterate. -/
theorem stepH_n (n : ℕ) :
    F.StepH (c.withρ (rhoN c.toSC n)) ι (F.iterK ι u₀ z₀ n).1 (F.iterK ι u₀ z₀ n).2
      (c.eN e₀ n) (delN c.toSC n) :=
  stepH_of_admG K.G (K.adm_n n) (K.rho_le n) (K.inv_all n).eR (K.inv_all n).eZ (K.eN_le_θ n)
    (kamDelta_pos K.hδ0 n) (K.del_le n) (K.three_del_le n)

/-- `ρ_∞ > 0`. -/
theorem rInf_pos : 0 < rInf c.toSC := by unfold rInf; linarith [K.hρ6]

/-- `ρ_∞ ≤ ρ_{n+1} ≤ ρ_n − 2δ_n`. -/
theorem rInf_le (n : ℕ) :
    rInf c.toSC ≤ rhoN c.toSC (n + 1) ∧
      rhoN c.toSC (n + 1) ≤ rhoN c.toSC n - 2 * delN c.toSC n := by
  have hδn : 0 < delN c.toSC n := kamDelta_pos K.hδ0 n
  refine ⟨(K.rho_gt (n + 1)).le, ?_⟩
  rw [rho_succ]; linarith

/-- **The increments of the iteration** on the limiting strip. -/
theorem incr (n : ℕ) :
    Bd (rInf c.toSC) ((F.iterK ι u₀ z₀ (n + 1)).1 - (F.iterK ι u₀ z₀ n).1)
        (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) ∧
      Bd (rInf c.toSC) ((F.iterK ι u₀ z₀ (n + 1)).2 - (F.iterK ι u₀ z₀ n).2)
        (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) ∧
      Bd (rInf c.toSC) (dTh (F.iterK ι u₀ z₀ (n + 1)).1 - dTh (F.iterK ι u₀ z₀ n).1)
        (c.cK / c.E1 * c.eN e₀ n / delN c.toSC n ^ 3) ∧
      Bd (rInf c.toSC) (dTh (F.iterK ι u₀ z₀ (n + 1)).2 - dTh (F.iterK ι u₀ z₀ n).2)
        (c.cK / c.E1 * c.eN e₀ n / delN c.toSC n ^ 3) ∧
      Bd (rInf c.toSC) (Lt ι (F.iterK ι u₀ z₀ (n + 1)).1 - Lt ι (F.iterK ι u₀ z₀ n).1)
        (c.cL * c.eN e₀ n / delN c.toSC n ^ 2) ∧
      Bd (rInf c.toSC) (Lt ι (F.iterK ι u₀ z₀ (n + 1)).2 - Lt ι (F.iterK ι u₀ z₀ n).2)
        (c.cL * c.eN e₀ n / delN c.toSC n ^ 2) := by
  set u := (F.iterK ι u₀ z₀ n).1
  set z := (F.iterK ι u₀ z₀ n).2
  have SH := K.stepH_n n
  have I := K.inv_all n
  have hδn : 0 < delN c.toSC n := kamDelta_pos K.hδ0 n
  obtain ⟨h1, h2⟩ := K.rInf_le n
  have hs : ∀ {x : FA} {B : ℝ}, Bd (rhoN c.toSC n - 2 * delN c.toSC n) x B →
      Bd (rInf c.toSC) x B := fun hx => hx.strip (h1.trans h2)
  have hdR : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (F.dRs ι u z)
      (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bdR
  have hdZ : Bd (rhoN c.toSC n - 2 * delN c.toSC n) (F.dZs ι u z)
      (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) := SH.bdZ
  have h3 : delN c.toSC n ≤ rhoN c.toSC n - 2 * delN c.toSC n := by
    have := K.three_del_le n; linarith
  have hρ3 : rInf c.toSC ≤ rhoN c.toSC n - 2 * delN c.toSC n - delN c.toSC n := by
    have := h1; rw [rho_succ] at this; linarith
  have hθ : ∀ {x : FA}, Bd (rhoN c.toSC n - 2 * delN c.toSC n) x
      (c.cK * c.eN e₀ n / delN c.toSC n ^ 2) →
      Bd (rInf c.toSC) (dTh x) (c.cK / c.E1 * c.eN e₀ n / delN c.toSC n ^ 3) := fun hx => by
    exact ((hx.dS hδn h3 1 0).strip hρ3).le (cauchy_conv K.G.hE1.1 K.G.hE1.2 hδn K.hcK
      (kamExact_nonneg K.hκ.le K.he₀ n))
  have hana1 : Ana (F.dRs ι u z) := SH.kam_step.1
  have hana2 : Ana (F.dZs ι u z) := SH.kam_step.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Bd (rInf c.toSC) (u + F.dRs ι u z - u) _
    rw [add_sub_cancel_left]; exact hs hdR
  · change Bd (rInf c.toSC) (z + F.dZs ι u z - z) _
    rw [add_sub_cancel_left]; exact hs hdZ
  · change Bd (rInf c.toSC) (dS 1 0 (u + F.dRs ι u z) - dS 1 0 u) _
    rw [dS_add _ _ I.ana_u hana1, add_sub_cancel_left]; exact hθ hdR
  · change Bd (rInf c.toSC) (dS 1 0 (z + F.dZs ι u z) - dS 1 0 z) _
    rw [dS_add _ _ I.ana_z hana2, add_sub_cancel_left]; exact hθ hdZ
  · change Bd (rInf c.toSC) (dS ι 2 (u + F.dRs ι u z) - dS ι 2 u) _
    rw [dS_add _ _ I.ana_u hana1, add_sub_cancel_left]; exact hs SH.bLdR
  · change Bd (rInf c.toSC) (dS ι 2 (z + F.dZs ι u z) - dS ι 2 z) _
    rw [dS_add _ _ I.ana_z hana2, add_sub_cancel_left]; exact hs SH.bLdZ

/-- The displacement series are summable. -/
theorem summ (τ : ℕ) (hτ : τ ≤ 4) {C' : ℝ} (hC : 0 ≤ C') :
    Summable (fun j => C' * c.eN e₀ j / delN c.toSC j ^ τ) ∧
      ∑' j, C' * c.eN e₀ j / delN c.toSC j ^ τ ≤ 2 * C' * e₀ / c.δ0 ^ τ := by
  obtain ⟨hs, htot, -⟩ := K.seq.2.2 τ C' hτ hC
  exact ⟨hs, htot⟩

/-- Nonnegativity of the displacement terms. -/
theorem term_nonneg (τ : ℕ) {C' : ℝ} (hC : 0 ≤ C') (j : ℕ) :
    0 ≤ C' * c.eN e₀ j / delN c.toSC j ^ τ := by
  have := kamExact_nonneg K.hκ.le K.he₀ (δ₀ := c.δ0) j
  have := kamDelta_pos K.hδ0 j
  unfold SCG.eN delN; positivity

/-- **The KAM theorem for a generalised flow field (`kam_flow_torus`).** Under the hypotheses
`KamHG` the iteration converges on the strip `ρ_∞ = ρ₀ − 6δ₀` to an analytic, **real** torus
`(u, z)` that solves the flow-form invariance equation of `F` **exactly**, `D 𝓛K = n`
(`resR = resZ = 0`), and stays `μ`-close to the initial torus in
`u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z`. -/
theorem kam_flow_torus :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ F.resR ι u z = 0 ∧ F.resZ ι u z = 0 ∧
      Close (rInf c.toSC) ι u z u₀ z₀ μ := by
  have hr := K.rInf_pos
  have hr0 := hr.le
  -- the six sequences and their increments
  set xu : ℕ → FA := fun n => (F.iterK ι u₀ z₀ n).1 with hxu
  set xz : ℕ → FA := fun n => (F.iterK ι u₀ z₀ n).2 with hxz
  have hcKe : 0 ≤ c.cK / c.E1 := div_nonneg K.hcK K.G.hE1.1.le
  obtain ⟨sK, tK⟩ := K.summ 2 (by norm_num) K.hcK
  obtain ⟨st, tt⟩ := K.summ 3 (by norm_num) hcKe
  obtain ⟨sL, tL⟩ := K.summ 2 (by norm_num) K.hcL
  have A0 := K.adm_n 0
  have hrr0 : rInf c.toSC ≤ rhoN c.toSC 0 := by
    unfold rInf rhoN kamRadius; linarith [K.hδ0]
  have b0 : ∀ {x : FA} {B : ℝ}, Bd (rhoN c.toSC 0) x B → Bd (rInf c.toSC) x B :=
    fun hx => hx.strip hrr0
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
  have tKt := tail_tendsto (fun j => c.cK * c.eN e₀ j / delN c.toSC j ^ 2)
  have ttt := tail_tendsto (fun j => c.cK / c.E1 * c.eN e₀ j / delN c.toSC j ^ 3)
  have tLt := tail_tendsto (fun j => c.cL * c.eN e₀ j / delN c.toSC j ^ 2)
  -- analyticity and reality of the limits
  have hBu : Bd (rInf c.toSC) yu
      (∑' m, c.cK * c.eN e₀ (0 + m) / delN c.toSC (0 + m) ^ 2 + c.au) := by
    have := (hyu 0).add (b0 A0.hu); rwa [sub_add_cancel] at this
  have hBz : Bd (rInf c.toSC) yz
      (∑' m, c.cK * c.eN e₀ (0 + m) / delN c.toSC (0 + m) ^ 2 + c.az) := by
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
  have hK0 : ∑' m, c.cK * c.eN e₀ (0 + m) / delN c.toSC (0 + m) ^ 2 ≤ μ := by
    simp only [zero_add]; exact tK.trans K.hμK
  have ht0 : ∑' m, c.cK / c.E1 * c.eN e₀ (0 + m) / delN c.toSC (0 + m) ^ 3 ≤ μ := by
    simp only [zero_add]; exact tt.trans K.hμt
  have hL0 : ∑' m, c.cL * c.eN e₀ (0 + m) / delN c.toSC (0 + m) ^ 2 ≤ μ := by
    simp only [zero_add]; exact tL.trans K.hμL
  have hclose : Close (rInf c.toSC) ι yu yz u₀ z₀ μ :=
    ⟨(hyu 0).le hK0, (hyz 0).le hK0, by rw [eut]; exact (hyut 0).le ht0,
      by rw [ezt]; exact (hyzt 0).le ht0, by rw [euL]; exact (hyuL 0).le hL0,
      by rw [ezL]; exact (hyzL 0).le hL0⟩
  -- exactness: the residuals vanish
  set m1 : Fin 6 → ℝ := ![1, 1, 0, 0, 1, 1] with hm1
  have m1nn : ∀ i, 0 ≤ m1 i := fun i => by fin_cases i <;> simp [hm1]
  set sq : ℕ → ℝ := fun n => (∑' m, c.cK * c.eN e₀ (n + m) / delN c.toSC (n + m) ^ 2) +
    (∑' m, c.cL * c.eN e₀ (n + m) / delN c.toSC (n + m) ^ 2) with hsq
  have sqt : Tendsto sq atTop (𝓝 0) := by simpa using tKt.add tLt
  have sqnn : ∀ n, 0 ≤ sq n := fun n => add_nonneg
    (tail_nonneg (K.term_nonneg 2 K.hcK) n) (tail_nonneg (K.term_nonneg 2 K.hcL) n)
  have sqle : ∀ n, sq n ≤ sq 0 := fun n => by
    have h1 := tail_le_total (K.term_nonneg 2 K.hcK) sK n
    have h2 := tail_le_total (K.term_nonneg 2 K.hcL) sL n
    simp only [hsq, zero_add]; linarith
  have hb : ∀ n, ∀ i, Bd (rInf c.toSC) ((xK ι yu yz - xK ι (xu n) (xz n)) i)
      ((sq n • m1) i) := by
    intro n i
    have tK0 := tail_nonneg (K.term_nonneg 2 K.hcK) n
    have tL0 := tail_nonneg (K.term_nonneg 2 K.hcL) n
    fin_cases i
    · exact (hyu n).le (by simp [hm1, hsq]; linarith)
    · exact (hyz n).le (by simp [hm1, hsq]; linarith)
    · simpa [xK, hm1] using Bd_zero (rInf c.toSC)
    · simpa [xK, hm1] using Bd_zero (rInf c.toSC)
    · have := (hyuL n).le (B' := sq n) (by simp only [hsq]; linarith)
      rw [← euL] at this; simpa [xK, hm1] using this
    · have := (hyzL n).le (B' := sq n) (by simp only [hsq]; linarith)
      rw [← ezL] at this; simpa [xK, hm1] using this
  have hx : ∀ n, ∀ i, Bd (rInf c.toSC) (xK ι (xu n) (xz n) i) (c.avec i) := by
    intro n i
    have A := K.adm_n n
    have hs : ∀ {x : FA} {B : ℝ}, Bd (rhoN c.toSC n) x B → Bd (rInf c.toSC) x B :=
      fun hx => hx.strip (K.rho_gt n).le
    have hc : Real.exp (rInf c.toSC) ≤ c.ac :=
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
      (∀ n, Bd (rInf c.toSC) (PolyExpr.eval (xK ι (xu n) (xz n)) e) (c.eN e₀ n)) →
      PolyExpr.eval (xK ι yu yz) e = 0 := by
    intro e he
    refine eq_zero_of_Bd_tendsto hr0
      (t := fun n => c.eN e₀ n + sq n * PolyExpr.majD (c.avec + sq 0 • m1) m1 e)
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
  have eR : F.resR ι yu yz = 0 := exact_res F.resRp (fun n => ((K.inv_all n).eR).strip
    (K.rho_gt n).le)
  have eZ : F.resZ ι yu yz = 0 := exact_res F.resZp (fun n => ((K.inv_all n).eZ).strip
    (K.rho_gt n).le)
  exact ⟨yu, yz, ana_u, ana_z, real_u, real_z, eR, eZ, hclose⟩

end KamHG

end Iter

end FlowFieldG

/-! ## Reduction: the old KAM hypotheses through the generalised interface -/

namespace FlowField

variable {F : FlowField} {c : SC} {ι : ℝ}

/-- **Reduction of the global conditions.** For `F : FlowField` and `c : SC`, the old global
conditions give the generalised ones for `F.toG` and `c.toSCG` (`p = 3`, split Diophantine data
of `Diophantine.toSplit` with one low mode), provided `e δ₀ ≤ 1`. -/
theorem GlobalH.toG (G : F.GlobalH c ι) (hδe : Real.exp 1 * c.δ0 ≤ 1) :
    F.toG.GlobalHG c.toSCG ι where
  hp := rfl
  dio := by
    have := G.dio.toSplit G.γ_pos.le 1
    change DiophantineSplit (ι / 2) c.γ c.γ 1 1
    simpa using this
  hK := le_rfl
  hd := G.γ_pos
  γ_pos := G.γ_pos
  hlow := by
    have hγ := G.γ_pos
    change Real.exp 1 * c.γ * c.δ0 ≤ c.γ
    nlinarith
  hτ' := G.hτ'
  hC2R := G.hC2R
  hC2Z := G.hC2Z
  hac := G.hac
  hE1 := G.hE1
  hcb := G.hcb

/-- `T₀` of `F.toG` is that of `F`. -/
theorem toG_Talg (F : FlowField) (u z : FA) : F.toG.Talg u z = F.Talg u z := by
  rw [FlowFieldG.Talg, FlowFieldG.Wi, F.toG_W0, F.toG_R]; rfl

/-- **Reduction of the admissibility bounds**: `V₀ = (u, z)`, `R = 1 + u`. -/
theorem AdmBounds.toG {ρ : ℝ} {u z : FA} (A : F.AdmBounds c ι ρ u z) :
    F.toG.AdmBoundsG c.toSCG ι ρ u z where
  frame := (F.toG_frameHyp_iff u z).2 A.frame
  hu := A.hu
  hz := A.hz
  hV0R := by rw [F.toG_V0R]; exact A.hu
  hV0Z := by rw [F.toG_V0Z]; exact A.hz
  hR := by rw [F.toG_R]; exact (Bd_one ρ).add A.hu
  hRt := A.hRt
  hzt := A.hzt
  hLR := A.hLR
  hLz := A.hLz
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
  hsR := by rw [FlowFieldG.Ri, ← FlowFieldG.R, F.toG_R]; exact A.hsR
  hsW := by rw [FlowFieldG.Wi, F.toG_W0]; exact A.hsW
  hT := by rw [F.toG_Talg]; exact A.hT
  hτ := by rw [F.toG_Talg]; exact A.hτ

/-- **Reduction of the KAM hypotheses.** The old hypotheses `FlowField.KamH` for `F` and `c`
give the generalised ones `KamHG` for `F.toG` and `c.toSCG` when `e δ₀ ≤ 1`; the constants
`cK`, `cL`, `κ` are the same (`SC.toSCG_cK`, `toSCG_cL`, `toSCG_kap`). -/
theorem KamH.toG {u₀ z₀ : FA} {e₀ μ : ℝ} (K : F.KamH c ι u₀ z₀ e₀ μ)
    (hδe : Real.exp 1 * c.δ0 ≤ 1) : F.toG.KamHG c.toSCG ι u₀ z₀ e₀ μ where
  G := K.G.toG hδe
  hδ0 := K.hδ0
  hρ6 := K.hρ6
  hθ := K.hθ
  he₀ := K.he₀
  hκ := by rw [c.toSCG_kap]; exact K.hκ
  hsmall := by rw [c.toSCG_kap]; exact K.hsmall
  hcK := K.hcK
  hcL := by rw [c.toSCG_cL]; exact K.hcL
  hμK := K.hμK
  hμt := K.hμt
  hμL := by rw [c.toSCG_cL]; exact K.hμL
  hadm := fun ρ u z h1 h2 hu hz hC => (K.hadm ρ u z h1 h2 hu hz hC).toG
  ana_u₀ := K.ana_u₀
  ana_z₀ := K.ana_z₀
  real_u₀ := K.real_u₀
  real_z₀ := K.real_z₀
  e0R := K.e0R
  e0Z := K.e0Z

/-- **Sanity: the generalised correction of `F.toG` is the old one** (`z` component). -/
theorem toG_dZs (F : FlowField) (ι : ℝ) (u z : FA) : F.toG.dZs ι u z = F.dZs ι u z := by
  have hN : F.toG.NZ u z = F.NZ u z := by
    rw [FlowFieldG.NZ, F.toG_hN, F.toG_V0Z]; rfl
  have h20 : F.toG.xi20 ι u z = F.xi20 ι u z := by
    rw [FlowFieldG.xi20, F.toG_eta2]; rfl
  have h2 : F.toG.xi2 ι u z = F.xi2 ι u z := by
    rw [FlowFieldG.xi2, FlowFieldG.cbar, h20, F.toG_eta1, F.toG_Tor]; rfl
  have h1 : F.toG.xi1 ι u z = F.xi1 ι u z := by
    rw [FlowFieldG.xi1, h2, F.toG_eta1, F.toG_Tor]; rfl
  rw [FlowFieldG.dZs, h1, h2, hN]; rfl

/-- **Sanity: the generalised iteration of `F.toG` is the old one**: same Newton map, hence the
same iterates (and the same limit torus). -/
theorem toG_stepK (F : FlowField) (ι : ℝ) (q : FA × FA) : F.toG.stepK ι q = F.stepK ι q := by
  simp only [FlowFieldG.stepK, FlowField.stepK, F.toG_dRs, F.toG_dZs]

/-- The iterates agree. -/
theorem toG_iterK (F : FlowField) (ι : ℝ) (u₀ z₀ : FA) (n : ℕ) :
    F.toG.iterK ι u₀ z₀ n = F.iterK ι u₀ z₀ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [FlowFieldG.iterK, FlowField.iterK, ih, toG_stepK]

end FlowField

end PlasmaLean.Design.KamNewton
