/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamData

/-!
# The coarse sampled certificate: grid points and rows

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). The coarse instance uses the
torus `ckRecs` (`Design/CoilKamData`), scale `D = 2¹⁰⁰`, the `16 × 32` grid
`(θ_j, φ_l) = (2πj/16, 2πl/32)`, tube half-width `w₀ = ⌊D/5⌋/D`, displacement bound
`⌊D/100⌋/D` and Lipschitz constant `2·10⁶` (`coil_lip`).

* `ckPt j l`: the grid-point checker `pointAP` with these parameters;
* `CkHyp`: the two analytic inputs (the exponential table and the enclosure of `ι_A`), proved in
  `Design/CoilKamCert`;
* `ckPt_sound`: a point value `some (s₁, s₂)` bounds `|E_R|` by `s₁/D` and `|E_z|` by `s₂/D`;
* `row_bound`: a row of 32 point values bounds the row sums.

The 512 kernel evaluations (one theorem per grid point, so that each kernel check stays below
the memory budget) are in `Design/CoilKamPts0`–`7`; the rows are assembled in
`Design/CoilKamRows`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open PlasmaLean.Fields PlasmaLean.Design.CoilFieldComplex

/-- `D₀ = 2⁶⁸` (`D = 2³² D₀ = 2¹⁰⁰`). -/
def ckD₀ : ℕ := 2 ^ 68
/-- The scale `D = 2¹⁰⁰`. -/
def ckD : ℕ := 4294967296 * ckD₀
/-- The tube half-width numerator `⌊D/5⌋`. -/
def ckWN : ℕ := ckD / 5
/-- The displacement bound numerator `⌊D/100⌋`. -/
def ckDN : ℕ := ckD / 100
/-- The Lipschitz constant `2·10⁶`. -/
def ckLip : ℕ := 2000000

/-- The grid-point checker of the coarse instance. -/
def ckPt (j l : ℕ) : Option (ℕ × ℕ) :=
  pointAP ckD₀ 32 2 ckE ckIq ckTbl ckRecs ckWN ckDN ckLip j l

/-- The analytic inputs of the grid checker. -/
structure CkHyp : Prop where
  /-- The exponential table. -/
  tbl : ∀ t < 32, ‖gexp 32 t - gauss ckD (tget ckTbl t)‖ ≤ (ckE : ℝ) / ckD
  /-- The enclosure of `ι_A`. -/
  iota : Approx ckD PlasmaLean.Theory.KAM.torusAIota (ckIq, 1)

theorem ckD_pos : 0 < ckD := by unfold ckD ckD₀; positivity

theorem ckWN_le : (ckWN : ℝ) / ckD ≤ 1 / 5 := by
  have hD : (0 : ℝ) < ckD := by exact_mod_cast ckD_pos
  rw [div_le_div_iff₀ hD (by norm_num)]
  have : ckWN * 5 ≤ ckD := Nat.div_mul_le_self _ _
  have : ((ckWN * 5 : ℕ) : ℝ) ≤ ckD := by exact_mod_cast this
  push_cast at this; linarith

theorem ckDN_le : (ckDN : ℝ) / ckD ≤ 1 / 100 := by
  have hD : (0 : ℝ) < ckD := by exact_mod_cast ckD_pos
  rw [div_le_div_iff₀ hD (by norm_num)]
  have : ckDN * 100 ≤ ckD := Nat.div_mul_le_self _ _
  have : ((ckDN * 100 : ℕ) : ℝ) ≤ ckD := by exact_mod_cast this
  push_cast at this; linarith

/-- The Lipschitz hypothesis of `pointAP_sound` for the coarse parameters (from `coil_lip`). -/
theorem ck_lip : ∀ y y' : Space, y' ∈ realTube ((ckWN : ℝ) / ckD) →
    ‖y - y'‖ ≤ (ckDN : ℝ) / ckD → ∀ i, |Bc y i - Bc y' i| ≤ ckLip * ‖y - y'‖ := by
  intro y y' hy' hyy i
  have := coil_lip (realTube_mono ckWN_le hy') (hyy.trans ckDN_le) i
  simpa [ckLip] using this

/-- Soundness of one grid point of the coarse instance. -/
theorem ckPt_sound (H : CkHyp) {j l : ℕ} {s : ℕ × ℕ} (h : ckPt j l = some s) :
    |resR ckD PlasmaLean.Theory.KAM.torusAIota ckRecs (2 * Real.pi * j / 16)
        (2 * Real.pi * l / 32)| ≤ (s.1 : ℝ) / ckD ∧
      |resZ ckD PlasmaLean.Theory.KAM.torusAIota ckRecs (2 * Real.pi * j / 16)
        (2 * Real.pi * l / 32)| ≤ (s.2 : ℝ) / ckD := by
  obtain ⟨s₁, s₂⟩ := s
  have hw : (ckWN : ℝ) / ckD < 7 / 20 := ckWN_le.trans_lt (by norm_num)
  have := pointAP_sound (D₀ := ckD₀) (L := 32) (q := 2) (N₁ := 16) (by unfold ckD₀; positivity)
    (by norm_num) (by norm_num) H.tbl H.iota ckRecs hw ck_lip h
  exact this

/-- The residual `|E_R|` on row `j` as a function of `l`. -/
def rowR (j l : ℕ) : ℝ :=
  |resR ckD PlasmaLean.Theory.KAM.torusAIota ckRecs (2 * Real.pi * j / 16)
    (2 * Real.pi * (l : ℝ) / 32)|

/-- The residual `|E_z|` on row `j` as a function of `l`. -/
def rowZ (j l : ℕ) : ℝ :=
  |resZ ckD PlasmaLean.Theory.KAM.torusAIota ckRecs (2 * Real.pi * j / 16)
    (2 * Real.pi * (l : ℝ) / 32)|

theorem sum_range_getD (f : ℕ × ℕ → ℝ) :
    ∀ vs : List (ℕ × ℕ), ∑ l ∈ Finset.range vs.length, f (vs.getD l (0, 0)) = (vs.map f).sum
  | [] => by simp
  | v :: vs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_range_getD f vs]

/-- **A row from its point evaluations**: if `ckPt j l = some (vs_l)` for `l < 32` then the row
sums of `|E_R|`, `|E_z|` are bounded by the sums of the values (over `D`). -/
theorem row_bound (H : CkHyp) (j : ℕ) (vs : List (ℕ × ℕ)) (hlen : vs.length = 32)
    (h : ∀ l < 32, ckPt j l = some (vs.getD l (0, 0))) :
    ∑ l ∈ Finset.range 32, rowR j l ≤ ((vs.map Prod.fst).sum : ℝ) / ckD ∧
      ∑ l ∈ Finset.range 32, rowZ j l ≤ ((vs.map Prod.snd).sum : ℝ) / ckD := by
  have hD : (0 : ℝ) < ckD := by exact_mod_cast ckD_pos
  have key : ∀ l ∈ Finset.range 32, rowR j l ≤ ((vs.getD l (0, 0)).1 : ℝ) / ckD ∧
      rowZ j l ≤ ((vs.getD l (0, 0)).2 : ℝ) / ckD := by
    intro l hl
    have := ckPt_sound H (h l (Finset.mem_range.1 hl))
    exact ⟨by simpa [rowR] using this.1, by simpa [rowZ] using this.2⟩
  have e1 : ((vs.map Prod.fst).sum : ℝ) / ckD =
      ∑ l ∈ Finset.range 32, ((vs.getD l (0, 0)).1 : ℝ) / ckD := by
    rw [← Finset.sum_div, ← hlen]
    have := sum_range_getD (fun v => (v.1 : ℝ)) vs
    rw [this, Nat.cast_list_sum, List.map_map]; rfl
  have e2 : ((vs.map Prod.snd).sum : ℝ) / ckD =
      ∑ l ∈ Finset.range 32, ((vs.getD l (0, 0)).2 : ℝ) / ckD := by
    rw [← Finset.sum_div, ← hlen]
    have := sum_range_getD (fun v => (v.2 : ℝ)) vs
    rw [this, Nat.cast_list_sum, List.map_map]; rfl
  rw [e1, e2]
  exact ⟨Finset.sum_le_sum fun l hl => (key l hl).1, Finset.sum_le_sum fun l hl => (key l hl).2⟩

end PlasmaLean.Design.CoilKam
