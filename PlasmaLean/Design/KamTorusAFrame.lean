/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusA
public import PlasmaLean.Design.KamTorusAFrameCheck
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul

/-!
# The symplectic frame of torus A and its torsion (KAM route, K3 lemma 5, part 1)

The Newton step of the K3 plan (`notes/theory/kam-k3-plan.md` §2, step (a)) works in a frame
`M = (∂_θK, N)` of the plane `(R, z)` along the approximate torus `K = (R, z)(θ, φ)` of
`Design/KamTorusA`. This file constructs the frame and certifies its quantitative invertibility,
and defines the torsion (twist density) whose average is certified in `Design/KamTorusATwist`.

**The frame.** The invariant area form of the `φ`-parametrized field-line flow is
`Ω = w dR ∧ dz`, `w = B^φ R = (1 + ε ∂_φ h)/R = D/R³` (`wdens`). The complementary vector is the
radial vector `V₀ = (R − 1, z)` from the exact magnetic axis, normalized symplectically:
`N = V₀ / (w (∂_θK × V₀)) = −V₀ R³ / (D · wind)` (`frameN_R`, `frameN_Z`), where
`wind = (R − 1) ∂_θ z − z ∂_θ R ≥ 0.015` is the winding rate of `Design/KamTorusA`
(`torusA_winding`). Then `Ω(∂_θK, N) = 1` (`frame_symplectic`), and

* `det M = R³/D ∈ [0.37, 2.86]` (`frame_det_bounds`);
* `|M| ≤ 37` entrywise: `|∂_θ R|, |∂_θ z| ≤ 0.2`, `|N_R|, |N_z| ≤ 37` (`frame_entries_le`);
* `M⁻¹ = w [[N_z, −N_R], [−∂_θ z, ∂_θ R]]` (`frame_mul_inv`, `frame_inv_mul`), with entries
  `|w N| ≤ 13` and `|w ∂_θK| ≤ 0.54` (`frameInv_entries_le`).

The plan's normal `J∂_θK / (w |∂_θK|²)` differs from `N` by a multiple of `∂_θK` (both have
`∂_θK × N = 1/w`); its normalization needs `|∂_θK|² ≥ 0.006` (`torusA_dK2_ge`).

**The field and its Jacobian.** `16 X = (A₁, A₂)/D_l` with `D_l = 16 D`, `A₁ = 8 R Ps`,
`A₂ = 4 R² Pz` (`XR`, `XZ`; equal to `XRval`, `XZval` of `Design/KamTorusA` on the torus,
`XR_torus`). The polynomials are the atoms of `Design/KamTorusAFrameData` (`aval`), and their
partial derivatives are atoms as well (`hasDerivAt_aval_R`, `hasDerivAt_aval_z`, proved by a
symbolic derivative `dEx` of the expression trees), so the Jacobian entries `dXRR, dXRz, dXZR,
dXZz` are the true partial derivatives (`hasDerivAt_XR_R`, …).

**The torsion.** For the frame `(∂_θK, N)` the torsion is the `∂_θK`-component of
`M⁻¹(𝓛N − DX·N)`, `𝓛 = ∂_φ + ι ∂_θ` (the plan's `2L`). Since `𝓛V₀ = 𝓛K = X + E`
(`E` the flow-form error of `Design/KamTorusA`) and the frame coordinates are
`α = w (v × N)` (`frame_coord`), it equals, for any value `h'` of `𝓛(1/(w W₀))`,
`T₀ + w h² (E × V₀)` with the algebraic density (`frameTorsion_eq`)

  `T₀ = ((X − DX·V₀) × V₀) / (w W₀²)`,  `W₀ = ∂_θK × V₀`  (`torsion`, `T0`).

`T₀` is the two-dimensional analogue of the ELP-S twist density (Def. 6.1 of Enciso–Luque–
Peralta-Salas), and `|frame torsion − T₀| ≤ 10⁻¹⁸` on torus A (`frameTorsion_sub_T0_le`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA.Frame

open Finset PlasmaLean.Certificates.KronExpr

/-! ## Elementary bounds on torus A -/

/-- `0.81 ≤ R ≤ 1.19` on torus A (from `(R − 1)² + z² ≤ 0.0358`). -/
theorem torusR_bounds (θ φ : ℝ) : 81 / 100 ≤ torusR θ φ ∧ torusR θ φ ≤ 119 / 100 := by
  have h := torusA_rt2_le θ φ
  have hz := sq_nonneg (torusZ θ φ)
  constructor <;> nlinarith [sq_nonneg (torusR θ φ - 1 - 19 / 100),
    sq_nonneg (torusR θ φ - 1 + 19 / 100)]

/-- `|R − 1| ≤ 0.19` on torus A. -/
theorem abs_torusR_sub_one_le (θ φ : ℝ) : |torusR θ φ - 1| ≤ 19 / 100 := by
  have h := torusR_bounds θ φ; rw [abs_le]; constructor <;> linarith

/-- `|z| ≤ 0.19` on torus A. -/
theorem abs_torusZ_le (θ φ : ℝ) : |torusZ θ φ| ≤ 19 / 100 := by
  have h := torusA_rt2_le θ φ
  have h1 := sq_nonneg (torusR θ φ - 1)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (torusZ θ φ - 19 / 100),
    sq_nonneg (torusZ θ φ + 19 / 100)]

/-- `|∂_θ K|² ≥ 0.006` (Cauchy–Schwarz from the winding rate). -/
theorem torusA_dK2_ge (θ φ : ℝ) : 6 / 1000 ≤ torusRθ θ φ ^ 2 + torusZθ θ φ ^ 2 := by
  have hw := torusA_winding θ φ
  have hr := torusA_rt2_le θ φ
  set a := torusR θ φ - 1; set z := torusZ θ φ
  set p := torusRθ θ φ; set q := torusZθ θ φ
  have hcs : (a * q - z * p) ^ 2 ≤ (a ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (a * p + z * q)]
  have h1 : (15 / 1000 : ℝ) ^ 2 ≤ (a * q - z * p) ^ 2 := pow_le_pow_left₀ (by norm_num) hw 2
  by_contra hcon
  push Not at hcon
  have : (a ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2) ≤ 358 / 10000 * (6 / 1000) :=
    mul_le_mul hr hcon.le (by positivity) (by norm_num)
  nlinarith

/-! ## The frame -/

/-- The winding rate `(R − 1) ∂_θ z − z ∂_θ R = −∂_θK × V₀`. -/
def wind (θ φ : ℝ) : ℝ :=
  (torusR θ φ - 1) * torusZθ θ φ - torusZ θ φ * torusRθ θ φ

/-- The density `w = B^φ R = D / R³` of the invariant area form `Ω = w dR ∧ dz`. -/
def wdens (θ φ : ℝ) : ℝ := Dval θ φ / torusR θ φ ^ 3

/-- `R`-component of the normal `N = V₀ / (w (∂_θK × V₀))`. -/
def frameN_R (θ φ : ℝ) : ℝ := -(torusR θ φ - 1) / (wdens θ φ * wind θ φ)

/-- `z`-component of the normal `N`. -/
def frameN_Z (θ φ : ℝ) : ℝ := -torusZ θ φ / (wdens θ φ * wind θ φ)

/-- The frame matrix `M = (∂_θK, N)` (columns). -/
def frameMat (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![torusRθ θ φ, frameN_R θ φ; torusZθ θ φ, frameN_Z θ φ]

/-- The inverse frame `M⁻¹ = w [[N_z, −N_R], [−∂_θ z, ∂_θ R]]`. -/
def frameInv (θ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![wdens θ φ * frameN_Z θ φ, -(wdens θ φ * frameN_R θ φ);
    -(wdens θ φ * torusZθ θ φ), wdens θ φ * torusRθ θ φ]

/-- The winding rate is at least `0.015` (`torusA_winding`). -/
theorem wind_pos (θ φ : ℝ) : 15 / 1000 ≤ wind θ φ := torusA_winding θ φ

/-- `0.35 ≤ w = D/R³ ≤ 2.68`. -/
theorem wdens_bounds (θ φ : ℝ) : 35 / 100 ≤ wdens θ φ ∧ wdens θ φ ≤ 268 / 100 := by
  obtain ⟨hR1, hR2⟩ := torusR_bounds θ φ
  obtain ⟨hD1, hD2⟩ := torusA_D_bounds θ φ
  have hD2' : Dval θ φ ≤ 142 / 100 := (le_abs_self _).trans hD2
  have hR3 : 0 < torusR θ φ ^ 3 := by positivity
  have h3a : (81 / 100 : ℝ) ^ 3 ≤ torusR θ φ ^ 3 := pow_le_pow_left₀ (by norm_num) hR1 3
  have h3b : torusR θ φ ^ 3 ≤ (119 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hR2 3
  unfold wdens
  constructor
  · rw [le_div_iff₀ hR3]; nlinarith
  · rw [div_le_iff₀ hR3]; nlinarith

/-- `w > 0`. -/
theorem wdens_pos (θ φ : ℝ) : 0 < wdens θ φ := by linarith [(wdens_bounds θ φ).1]

/-- **`det M = 1/w = R³/D`.** -/
theorem frame_det (θ φ : ℝ) : (frameMat θ φ).det = 1 / wdens θ φ := by
  have hw := wdens_pos θ φ
  have hW : 0 < wind θ φ := by linarith [wind_pos θ φ]
  rw [frameMat, Matrix.det_fin_two_of, frameN_R, frameN_Z]
  field_simp
  unfold wind; ring

/-- **Symplectic normalization** `Ω(∂_θK, N) = w det M = 1`. -/
theorem frame_symplectic (θ φ : ℝ) : wdens θ φ * (frameMat θ φ).det = 1 := by
  rw [frame_det]; have := wdens_pos θ φ; field_simp

/-- **`0.37 ≤ det M ≤ 2.86`.** -/
theorem frame_det_bounds (θ φ : ℝ) :
    37 / 100 ≤ (frameMat θ φ).det ∧ (frameMat θ φ).det ≤ 286 / 100 := by
  rw [frame_det]
  obtain ⟨hR1, hR2⟩ := torusR_bounds θ φ
  obtain ⟨hD1, hD2⟩ := torusA_D_bounds θ φ
  have hD2' : Dval θ φ ≤ 142 / 100 := (le_abs_self _).trans hD2
  have hDp : 0 < Dval θ φ := by linarith
  have h3a : (81 / 100 : ℝ) ^ 3 ≤ torusR θ φ ^ 3 := pow_le_pow_left₀ (by norm_num) hR1 3
  have h3b : torusR θ φ ^ 3 ≤ (119 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hR2 3
  have e : 1 / wdens θ φ = torusR θ φ ^ 3 / Dval θ φ := by
    unfold wdens; have : 0 < torusR θ φ ^ 3 := by positivity
    field_simp
  rw [e]
  constructor
  · rw [le_div_iff₀ hDp]; nlinarith
  · rw [div_le_iff₀ hDp]; nlinarith

/-- `w · |V₀| / (w wind) ≤ 0.19/0.015`, the common bound behind the frame estimates. -/
theorem abs_div_wind_le {x : ℝ} (hx : |x| ≤ 19 / 100) (θ φ : ℝ) :
    |x / wind θ φ| ≤ 13 := by
  have hW := wind_pos θ φ
  have hWp : 0 < wind θ φ := by linarith
  rw [abs_div, abs_of_pos hWp, div_le_iff₀ hWp]
  linarith

/-- **Frame entries**: `|∂_θ R|, |∂_θ z| ≤ 1/5`, `|N_R|, |N_z| ≤ 37`. -/
theorem frame_entries_le (θ φ : ℝ) :
    |torusRθ θ φ| ≤ 1 / 5 ∧ |torusZθ θ φ| ≤ 1 / 5 ∧ |frameN_R θ φ| ≤ 37 ∧
      |frameN_Z θ φ| ≤ 37 := by
  refine ⟨torusRθ_le θ φ, torusZθ_le θ φ, ?_, ?_⟩
  all_goals
    obtain ⟨hw1, hw2⟩ := wdens_bounds θ φ
    have hW := wind_pos θ φ
    have hden : 0 < wdens θ φ * wind θ φ := by positivity
  · rw [frameN_R, abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
    have := abs_torusR_sub_one_le θ φ
    nlinarith
  · rw [frameN_Z, abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
    have := abs_torusZ_le θ φ
    nlinarith

/-- **Inverse frame entries**: `|w N_R|, |w N_z| ≤ 13`, `|w ∂_θ R|, |w ∂_θ z| ≤ 0.54`. -/
theorem frameInv_entries_le (θ φ : ℝ) :
    |wdens θ φ * frameN_R θ φ| ≤ 13 ∧ |wdens θ φ * frameN_Z θ φ| ≤ 13 ∧
      |wdens θ φ * torusRθ θ φ| ≤ 54 / 100 ∧ |wdens θ φ * torusZθ θ φ| ≤ 54 / 100 := by
  have hw := wdens_pos θ φ
  have hW : 0 < wind θ φ := by linarith [wind_pos θ φ]
  have e1 : wdens θ φ * frameN_R θ φ = -((torusR θ φ - 1) / wind θ φ) := by
    rw [frameN_R]; field_simp
  have e2 : wdens θ φ * frameN_Z θ φ = -(torusZ θ φ / wind θ φ) := by
    rw [frameN_Z]; field_simp
  obtain ⟨-, hw2⟩ := wdens_bounds θ φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, abs_neg]; exact abs_div_wind_le (abs_torusR_sub_one_le θ φ) θ φ
  · rw [e2, abs_neg]; exact abs_div_wind_le (abs_torusZ_le θ φ) θ φ
  · rw [abs_mul, abs_of_pos hw]
    have := torusRθ_le θ φ
    nlinarith [abs_nonneg (torusRθ θ φ)]
  · rw [abs_mul, abs_of_pos hw]
    have := torusZθ_le θ φ
    nlinarith [abs_nonneg (torusZθ θ φ)]

/-- Auxiliary identities of the frame: `w N = −V₀/wind` and the winding identity. -/
theorem frame_aux (θ φ : ℝ) :
    wdens θ φ * frameN_R θ φ = -((torusR θ φ - 1) / wind θ φ) ∧
      wdens θ φ * frameN_Z θ φ = -(torusZ θ φ / wind θ φ) ∧
      (-(torusRθ θ φ * torusZ θ φ) + torusZθ θ φ * (torusR θ φ - 1)) / wind θ φ = 1 := by
  have hw := wdens_pos θ φ
  have hW : 0 < wind θ φ := by linarith [wind_pos θ φ]
  refine ⟨by rw [frameN_R]; field_simp, by rw [frameN_Z]; field_simp, ?_⟩
  rw [div_eq_one_iff_eq hW.ne']; unfold wind; ring

/-- Entrywise equality of `2 × 2` matrices. -/
theorem mat2_eq {a b c d e f g h : ℝ} (h1 : a = e) (h2 : b = f) (h3 : c = g) (h4 : d = h) :
    !![a, b; c, d] = !![e, f; g, h] := by rw [h1, h2, h3, h4]

/-- **`M M⁻¹ = 1`.** -/
theorem frame_mul_inv (θ φ : ℝ) : frameMat θ φ * frameInv θ φ = 1 := by
  obtain ⟨e1, e2, hq⟩ := frame_aux θ φ
  rw [frameMat, frameInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  refine mat2_eq ?_ ?_ ?_ ?_ <;>
    first | ring1 | linear_combination torusRθ θ φ * e2 - torusZθ θ φ * e1 + hq

/-- **`M⁻¹ M = 1`.** -/
theorem frame_inv_mul (θ φ : ℝ) : frameInv θ φ * frameMat θ φ = 1 := by
  obtain ⟨e1, e2, hq⟩ := frame_aux θ φ
  rw [frameMat, frameInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  refine mat2_eq ?_ ?_ ?_ ?_ <;>
    first | ring1 | linear_combination torusRθ θ φ * e2 - torusZθ θ φ * e1 + hq

/-! ## The field-line vector field and its Jacobian -/

/-- Real assignment of the base variables `r = R − 1, z, C, S, t = 1, V = 1`. -/
def xB (R z C S : ℝ) : ℕ → ℝ := envB (R - 1) z C S 1 1

/-- The real value of atom `k` at `(R, z)` with `C = cos 2φ`, `S = sin 2φ`. -/
def aval (k : ℕ) (R z C S : ℝ) : ℝ := Ex.eval (xB R z C S) (atom k)

/-- Expand the evaluation of an atom (or of its symbolic derivative). -/
macro "atom_simp" : tactic =>
  `(tactic| simp [aval, xB, atom, atomDl, atomDlR, atomDlz, atomA1, atomA1R, atomA1z, atomA2,
    atomA2R, atomA2z, Ex.eval, Ex.dEx, sumEx, monoEx, envB, Function.update])

/-- Atom `0` is `16 D`. -/
theorem aval_Dl (R z C S : ℝ) : aval 0 R z C S = 16 * Dfun R z C S := by
  atom_simp; simp only [Dfun, sfun, sgfun, eps]; ring

/-- Atom `3` is `8 R Ps = 16 · 2εR Ps`. -/
theorem aval_A1 (R z C S : ℝ) : aval 3 R z C S = 8 * R * Psfun R z C S := by
  atom_simp; simp only [Psfun, s2fs, s2gs]; ring

/-- Atom `6` is `4 R² Pz = 16 · εR² Pz`. -/
theorem aval_A2 (R z C S : ℝ) : aval 6 R z C S = 4 * R ^ 2 * Pzfun R z C S := by
  atom_simp; simp only [Pzfun, sgz]; ring

/-- Changing `R` in the base assignment. -/
theorem xB_update_R (R z C S : ℝ) :
    xB R z C S = Function.update (xB 1 z C S) 0 (R - 1) := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [xB, envB, Function.update]

/-- Changing `z` in the base assignment. -/
theorem xB_update_z (R z C S : ℝ) :
    xB R z C S = Function.update (xB R 0 C S) 1 z := by
  funext i; rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [xB, envB, Function.update]

/-- `R`-derivative of an atom, as the evaluation of its symbolic derivative. -/
theorem hasDerivAt_atom_R (k : ℕ) (R z C S : ℝ) :
    HasDerivAt (fun R => aval k R z C S) (Ex.eval (xB R z C S) (Ex.dEx 0 (atom k))) R := by
  have h := (Ex.hasDerivAt_eval (xB 1 z C S) 0 (R - 1) (atom k)).comp R
    ((hasDerivAt_id R).sub_const 1)
  rw [← xB_update_R, mul_one] at h
  convert h using 1
  funext R'; simp only [aval, Function.comp, id, xB_update_R R']

/-- `z`-derivative of an atom. -/
theorem hasDerivAt_atom_z (k : ℕ) (R z C S : ℝ) :
    HasDerivAt (fun z => aval k R z C S) (Ex.eval (xB R z C S) (Ex.dEx 1 (atom k))) z := by
  have h := Ex.hasDerivAt_eval (xB R 0 C S) 1 z (atom k)
  rw [← xB_update_z] at h
  convert h using 1
  funext z'; simp only [aval, xB_update_z R z']

/-- Symbolic derivative identity: `∂_R` of atom `D_l` is atom `1`. -/
theorem dEx_Dl_R (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 0 (atom 0)) = aval 1 R z C S := by
  atom_simp; ring
/-- Symbolic derivative identity: `∂_z` of atom `D_l` is atom `2`. -/
theorem dEx_Dl_z (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 1 (atom 0)) = aval 2 R z C S := by
  atom_simp; ring
/-- Symbolic derivative identity: `∂_R` of atom `A₁` is atom `4`. -/
theorem dEx_A1_R (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 0 (atom 3)) = aval 4 R z C S := by
  atom_simp; ring
/-- Symbolic derivative identity: `∂_z` of atom `A₁` is atom `5`. -/
theorem dEx_A1_z (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 1 (atom 3)) = aval 5 R z C S := by
  atom_simp; ring
/-- Symbolic derivative identity: `∂_R` of atom `A₂` is atom `7`. -/
theorem dEx_A2_R (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 0 (atom 6)) = aval 7 R z C S := by
  atom_simp; ring
/-- Symbolic derivative identity: `∂_z` of atom `A₂` is atom `8`. -/
theorem dEx_A2_z (R z C S : ℝ) : Ex.eval (xB R z C S) (Ex.dEx 1 (atom 6)) = aval 8 R z C S := by
  atom_simp; ring

/-- `16 X_R = A₁ / D_l`: the `R`-component of the field-line vector field `dR/dφ`. -/
def XR (R z C S : ℝ) : ℝ := aval 3 R z C S / aval 0 R z C S
/-- The `z`-component `dz/dφ = A₂ / D_l`. -/
def XZ (R z C S : ℝ) : ℝ := aval 6 R z C S / aval 0 R z C S
/-- `∂_R X_R`. -/
def dXRR (R z C S : ℝ) : ℝ :=
  (aval 4 R z C S * aval 0 R z C S - aval 3 R z C S * aval 1 R z C S) / aval 0 R z C S ^ 2
/-- `∂_z X_R`. -/
def dXRz (R z C S : ℝ) : ℝ :=
  (aval 5 R z C S * aval 0 R z C S - aval 3 R z C S * aval 2 R z C S) / aval 0 R z C S ^ 2
/-- `∂_R X_z`. -/
def dXZR (R z C S : ℝ) : ℝ :=
  (aval 7 R z C S * aval 0 R z C S - aval 6 R z C S * aval 1 R z C S) / aval 0 R z C S ^ 2
/-- `∂_z X_z`. -/
def dXZz (R z C S : ℝ) : ℝ :=
  (aval 8 R z C S * aval 0 R z C S - aval 6 R z C S * aval 2 R z C S) / aval 0 R z C S ^ 2

/-- `dXRR` is the partial derivative `∂_R X_R`. -/
theorem hasDerivAt_XR_R {R z C S : ℝ} (h : aval 0 R z C S ≠ 0) :
    HasDerivAt (fun R => XR R z C S) (dXRR R z C S) R := by
  have h1 := hasDerivAt_atom_R 3 R z C S; rw [dEx_A1_R] at h1
  have h0 := hasDerivAt_atom_R 0 R z C S; rw [dEx_Dl_R] at h0
  exact h1.div h0 h

/-- `dXRz` is the partial derivative `∂_z X_R`. -/
theorem hasDerivAt_XR_z {R z C S : ℝ} (h : aval 0 R z C S ≠ 0) :
    HasDerivAt (fun z => XR R z C S) (dXRz R z C S) z := by
  have h1 := hasDerivAt_atom_z 3 R z C S; rw [dEx_A1_z] at h1
  have h0 := hasDerivAt_atom_z 0 R z C S; rw [dEx_Dl_z] at h0
  exact h1.div h0 h

/-- `dXZR` is the partial derivative `∂_R X_z`. -/
theorem hasDerivAt_XZ_R {R z C S : ℝ} (h : aval 0 R z C S ≠ 0) :
    HasDerivAt (fun R => XZ R z C S) (dXZR R z C S) R := by
  have h1 := hasDerivAt_atom_R 6 R z C S; rw [dEx_A2_R] at h1
  have h0 := hasDerivAt_atom_R 0 R z C S; rw [dEx_Dl_R] at h0
  exact h1.div h0 h

/-- `dXZz` is the partial derivative `∂_z X_z`. -/
theorem hasDerivAt_XZ_z {R z C S : ℝ} (h : aval 0 R z C S ≠ 0) :
    HasDerivAt (fun z => XZ R z C S) (dXZz R z C S) z := by
  have h1 := hasDerivAt_atom_z 6 R z C S; rw [dEx_A2_z] at h1
  have h0 := hasDerivAt_atom_z 0 R z C S; rw [dEx_Dl_z] at h0
  exact h1.div h0 h

/-- On torus A the field is the field-line vector field of `Design/KamTorusA`. -/
theorem XR_torus (θ φ : ℝ) :
    XR (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) = XRval θ φ := by
  rw [XR, aval_A1, aval_Dl, XRval, Dval, eps]; ring

/-- On torus A, `XZ` is `XZval` of `Design/KamTorusA`. -/
theorem XZ_torus (θ φ : ℝ) :
    XZ (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) = XZval θ φ := by
  rw [XZ, aval_A2, aval_Dl, XZval, Dval, eps]; ring

/-! ## The torsion -/

/-- **The torsion density** (algebraic form) of the frame `(∂_θK, N)` at a point with
`K = (R, z)`, `∂_θK = (a, b)`:
`T₀ = ((X − DX·V₀) × V₀) / (w W₀²)`, `V₀ = (R − 1, z)`, `W₀ = ∂_θK × V₀`, `w = D/R³`. -/
def torsion (R z a b C S : ℝ) : ℝ :=
  ((XR R z C S - (dXRR R z C S * (R - 1) + dXRz R z C S * z)) * z -
      (XZ R z C S - (dXZR R z C S * (R - 1) + dXZz R z C S * z)) * (R - 1)) /
    (Dfun R z C S / R ^ 3 * (a * z - b * (R - 1)) ^ 2)

/-- The torsion density along torus A. -/
def T0 (θ φ : ℝ) : ℝ :=
  torsion (torusR θ φ) (torusZ θ φ) (torusRθ θ φ) (torusZθ θ φ) (Real.cos (2 * φ))
    (Real.sin (2 * φ))

/-- Coordinates in a frame `(u, N)` with `w (u × N) = 1`:
`v = (w (v × N)) u + (w (u × v)) N`. -/
theorem frame_coord {u1 u2 N1 N2 w : ℝ} (h : w * (u1 * N2 - u2 * N1) = 1) (v1 v2 : ℝ) :
    v1 = w * (v1 * N2 - v2 * N1) * u1 + w * (u1 * v2 - u2 * v1) * N1 ∧
      v2 = w * (v1 * N2 - v2 * N1) * u2 + w * (u1 * v2 - u2 * v1) * N2 :=
  ⟨by linear_combination (-v1) * h, by linear_combination (-v2) * h⟩

/-- The transport `𝓛R = ∂_φ R + ι ∂_θ R` of the torus (`= X_R + E_R`). -/
def LK_R (θ φ : ℝ) : ℝ := torusRφ θ φ + iota * torusRθ θ φ
/-- The transport `𝓛z = ∂_φ z + ι ∂_θ z`. -/
def LK_Z (θ φ : ℝ) : ℝ := torusZφ θ φ + iota * torusZθ θ φ

/-- **The torsion of the frame.** The `∂_θK`-coordinate `w ((𝓛N − DX·N) × N)` (`frame_coord`) of
`𝓛N − DX·N`, where the transport of `N = h V₀`, `h = 1/(w W₀)`, is `𝓛N = h' V₀ + h 𝓛K` by the
product rule (`𝓛V₀ = 𝓛K`), for a value `h'` of `𝓛h` (the result does not depend on `h'`,
`frameTorsion_eq`). -/
def frameTorsion (θ φ h' : ℝ) : ℝ :=
  let R := torusR θ φ
  let z := torusZ θ φ
  let C := Real.cos (2 * φ)
  let S := Real.sin (2 * φ)
  let h := 1 / (wdens θ φ * (torusRθ θ φ * z - torusZθ θ φ * (R - 1)))
  let Y1 := h' * (R - 1) + h * LK_R θ φ -
    (dXRR R z C S * frameN_R θ φ + dXRz R z C S * frameN_Z θ φ)
  let Y2 := h' * z + h * LK_Z θ φ - (dXZR R z C S * frameN_R θ φ + dXZz R z C S * frameN_Z θ φ)
  wdens θ φ * (Y1 * frameN_Z θ φ - Y2 * frameN_R θ φ)

/-- `D_l = 16 D > 0` on torus A. -/
theorem aval0_torus_pos (θ φ : ℝ) :
    0 < aval 0 (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) := by
  rw [aval_Dl]; have := (torusA_D_bounds θ φ).1; unfold Dval at this; linarith

/-- **Frame torsion = `T₀` + error term**: `frameTorsion = T₀ + (E × V₀)/(w W₀²)` with
`E = 𝓛K − X` the flow-form error, for every `h'`. -/
theorem frameTorsion_eq (θ φ h' : ℝ) :
    frameTorsion θ φ h' = T0 θ φ +
      ((LK_R θ φ - XRval θ φ) * torusZ θ φ - (LK_Z θ φ - XZval θ φ) * (torusR θ φ - 1)) /
        (wdens θ φ * wind θ φ ^ 2) := by
  have hw := wdens_pos θ φ
  have hW : 0 < wind θ φ := by linarith [wind_pos θ φ]
  have hR : 0 < torusR θ φ := by linarith [(torusR_bounds θ φ).1]
  have hD : 0 < Dval θ φ := by linarith [(torusA_D_bounds θ φ).1]
  have hA := aval0_torus_pos θ φ
  rw [← XR_torus, ← XZ_torus]
  have hWdef : torusRθ θ φ * torusZ θ φ - torusZθ θ φ * (torusR θ φ - 1) = -wind θ φ := by
    unfold wind; ring
  have hDf : 0 < Dfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) := hD
  simp only [frameTorsion, T0, torsion, frameN_R, frameN_Z, hWdef, wdens, Dval]
  field_simp
  ring

/-- **The frame torsion of torus A is `T₀` up to `10⁻¹⁸`.** -/
theorem frameTorsion_sub_T0_le (θ φ h' : ℝ) : |frameTorsion θ φ h' - T0 θ φ| ≤ 1 / 10 ^ 18 := by
  rw [frameTorsion_eq, add_sub_cancel_left]
  obtain ⟨hE1, hE2⟩ := torusA_flow_error θ φ
  have e1 : LK_R θ φ - XRval θ φ = torusRφ θ φ + iota * torusRθ θ φ - XRval θ φ := rfl
  have e2 : LK_Z θ φ - XZval θ φ = torusZφ θ φ + iota * torusZθ θ φ - XZval θ φ := rfl
  rw [← e1] at hE1; rw [← e2] at hE2
  obtain ⟨hw1, -⟩ := wdens_bounds θ φ
  have hW := wind_pos θ φ
  have hz := abs_torusZ_le θ φ
  have hr := abs_torusR_sub_one_le θ φ
  have hden : (35 / 100) * (15 / 1000) ^ 2 ≤ wdens θ φ * wind θ φ ^ 2 := by
    have : (15 / 1000 : ℝ) ^ 2 ≤ wind θ φ ^ 2 := pow_le_pow_left₀ (by norm_num) hW 2
    exact mul_le_mul hw1 this (by norm_num) (by linarith)
  have hdpos : 0 < wdens θ φ * wind θ φ ^ 2 := lt_of_lt_of_le (by norm_num) hden
  rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  have hnum : |(LK_R θ φ - XRval θ φ) * torusZ θ φ - (LK_Z θ φ - XZval θ φ) * (torusR θ φ - 1)|
      ≤ 21 / 10 ^ 24 * (19 / 100) + 118 / 10 ^ 25 * (19 / 100) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
      exact mul_le_mul (by assumption) (by assumption) (abs_nonneg _) (by positivity)
  nlinarith

end PlasmaLean.Design.KamTorusA.Frame
