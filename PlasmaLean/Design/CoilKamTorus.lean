/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamSeg

/-!
# Rational tori for the coil field and their sampled flow-form residual

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). A torus in the variables
`(θ, φ)` (`φ` the geometric toroidal angle, full period: the coil field has no exact symmetry)
is given by a list of integer records `TRec` `(k, m, a, a', b, b')` at scale `D`:

`R = Σ (a cos x + a' sin x)/D`, `z = Σ (b cos x + b' sin x)/D`, `x = kθ + mφ`

(`Rr`, `Zr`), with the transport derivatives `𝓛 = ∂_φ + ι∂_θ` (`LRr`, `LZr`). The complex
coefficient sequences `uR`, `uZ` (and `uLR`, `uLZ` = `i(m + ιk)·u`) have finite support;
`fourierSumC_uOfG` writes their complex Fourier sums as finite sums, `fourierSumC_uR_ofReal` etc.
identify them with the real torus at real points, and `norm_fourierSumC_uOfG_le`,
`norm_fourierSumC_uOfG_sub_re_le` give the strip bounds needed for the mapping hypothesis.

The **flow form** for the coil field `B` is (no division)

`E_R = B^φ(K)·𝓛R − R·B^R(K)`, `E_z = B^φ(K)·𝓛z − R·B^z(K)`

(`resR`, `resZ` at real points, `B` the real field `tfField + polyCoilFieldC`).

**Sampled evaluation.** `pointAP` computes, at the grid point `(2πj/N₁, 2πl/N₂)` (`N₂ = L`,
`N₁ ∣ L`), approximants of `R, z, 𝓛R, 𝓛z` from a checked exponential table (`expTableOK`), the
dyadic point `ỹ` nearest to the torus point, the coil field at `ỹ` (`fieldAP`), a Lipschitz
transfer to the true torus point, and the two residuals. `pointAP_sound`: if `pointAP` returns
`some (s₁, s₂)` then `|E_R| ≤ s₁/D` and `|E_z| ≤ s₂/D` at that grid point.

**Sanity.** `Rr_nil` (the empty torus), `uOfG_nil` (its coefficient sequence vanishes),
`cos_grid_mod` (periodicity of the grid angles).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open Complex PlasmaLean.Theory.KAM PlasmaLean.Fields PlasmaLean.Design.PolygonCoil
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.CoilFieldComplex
  PlasmaLean.Theory.KAM.FourierSumHolo

/-- A torus record: mode `(k, m)` and the integer coefficients `a, a'` of `R` and `b, b'` of `z`
(of `cos x`, `sin x`, `x = kθ + mφ`) at scale `D`. -/
structure TRec where
  /-- Poloidal mode number. -/
  k : ℤ
  /-- Toroidal mode number. -/
  m : ℤ
  /-- Cosine coefficient of `R`. -/
  a : ℤ
  /-- Sine coefficient of `R`. -/
  a' : ℤ
  /-- Cosine coefficient of `z`. -/
  b : ℤ
  /-- Sine coefficient of `z`. -/
  b' : ℤ

/-- The phase `kθ + mφ`. -/
def TRec.ang (r : TRec) (θ φ : ℝ) : ℝ := r.k * θ + r.m * φ

/-- The real torus coordinate `R(θ, φ)`. -/
def Rr (D : ℕ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  (recs.map fun r => ((r.a : ℝ) * Real.cos (r.ang θ φ) + r.a' * Real.sin (r.ang θ φ)) / D).sum

/-- The real torus coordinate `z(θ, φ)`. -/
def Zr (D : ℕ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  (recs.map fun r => ((r.b : ℝ) * Real.cos (r.ang θ φ) + r.b' * Real.sin (r.ang θ φ)) / D).sum

/-- The transport derivative `𝓛R = (∂_φ + ι∂_θ)R`. -/
def LRr (D : ℕ) (ι : ℝ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  (recs.map fun r => (r.m + ι * r.k) *
    (-(r.a : ℝ) * Real.sin (r.ang θ φ) + r.a' * Real.cos (r.ang θ φ)) / D).sum

/-- The transport derivative `𝓛z`. -/
def LZr (D : ℕ) (ι : ℝ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  (recs.map fun r => (r.m + ι * r.k) *
    (-(r.b : ℝ) * Real.sin (r.ang θ φ) + r.b' * Real.cos (r.ang θ φ)) / D).sum

/-- The real torus point `cyl(R, φ, z)`. -/
def torusPt (D : ℕ) (recs : List TRec) (θ φ : ℝ) : Space := cylR (Rr D recs θ φ) φ (Zr D recs θ φ)

/-- The real coil field. -/
def Bc (y : Space) : Space := tfField y + polyCoilFieldC y

/-- **The real flow-form residual** `E_R = B^φ 𝓛R − R B^R` at the torus point. -/
def resR (D : ℕ) (ι : ℝ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  let B := Bc (torusPt D recs θ φ)
  (-Real.sin φ * B 0 + Real.cos φ * B 1) * LRr D ι recs θ φ -
    Rr D recs θ φ * (Real.cos φ * B 0 + Real.sin φ * B 1)

/-- **The real flow-form residual** `E_z = B^φ 𝓛z − R B^z` at the torus point. -/
def resZ (D : ℕ) (ι : ℝ) (recs : List TRec) (θ φ : ℝ) : ℝ :=
  let B := Bc (torusPt D recs θ φ)
  (-Real.sin φ * B 0 + Real.cos φ * B 1) * LZr D ι recs θ φ - Rr D recs θ φ * B 2

/-! ## List helpers -/

theorem norm_list_sum_le' (l : List ℂ) : ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (by linarith)

theorem list_sum_map_sub {α : Type*} (f g : α → ℂ) (l : List α) :
    (l.map f).sum - (l.map g).sum = (l.map fun x => f x - g x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; ring

theorem ofReal_list_sum' (l : List ℝ) : Complex.ofReal l.sum = (l.map Complex.ofReal).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem list_sum_le_sum {α : Type*} {f g : α → ℝ} (l : List α) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-! ## Complex coefficient sequences -/

/-- The coefficient sequence with the single entry `c` at `n`. -/
def single2 (n : ℤ × ℤ) (c : ℂ) (km : ℤ × ℤ) : ℂ := if km = n then c else 0

/-- `(c - c' i)/(2D)`. -/
def cP (D : ℕ) (c c' : ℤ) : ℂ := ((c : ℂ) - c' * I) / (2 * D)

/-- `(c + c' i)/(2D)`. -/
def cM (D : ℕ) (c c' : ℤ) : ℂ := ((c : ℂ) + c' * I) / (2 * D)

/-- The coefficient sequence `g(n) · Σ_rec [cP e_{(k,m)} + cM e_{(-k,-m)}]` of the selected pair
of coefficients `sel r = (c, c')`. -/
def uOfG (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec) (km : ℤ × ℤ) : ℂ :=
  g km * (recs.map fun r => single2 (r.k, r.m) (cP D (sel r).1 (sel r).2) km +
    single2 (-r.k, -r.m) (cM D (sel r).1 (sel r).2) km).sum

/-- The coefficients of `R`. -/
def uR (D : ℕ) (recs : List TRec) : ℤ × ℤ → ℂ := uOfG (fun _ => 1) D (fun r => (r.a, r.a')) recs

/-- The coefficients of `z`. -/
def uZ (D : ℕ) (recs : List TRec) : ℤ × ℤ → ℂ := uOfG (fun _ => 1) D (fun r => (r.b, r.b')) recs

/-- The transport multiplier `i(m + ιk)` (symbol of `∂_φ + ι∂_θ`). -/
def lsym (ι : ℝ) (km : ℤ × ℤ) : ℂ := I * ((km.2 : ℂ) + ι * km.1)

/-- The coefficients of `𝓛R`. -/
def uLR (D : ℕ) (ι : ℝ) (recs : List TRec) : ℤ × ℤ → ℂ :=
  uOfG (lsym ι) D (fun r => (r.a, r.a')) recs

/-- The coefficients of `𝓛z`. -/
def uLZ (D : ℕ) (ι : ℝ) (recs : List TRec) : ℤ × ℤ → ℂ :=
  uOfG (lsym ι) D (fun r => (r.b, r.b')) recs

/-- The complex term of one record. -/
def termC (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (r : TRec) (θ ψ : ℂ) : ℂ :=
  g (r.k, r.m) * cP D (sel r).1 (sel r).2 * fourierModeC (r.k, r.m) θ ψ +
    g (-r.k, -r.m) * cM D (sel r).1 (sel r).2 * fourierModeC (-r.k, -r.m) θ ψ

theorem hasSum_single2 (g : ℤ × ℤ → ℂ) (n : ℤ × ℤ) (c θ ψ : ℂ) :
    HasSum (fun km => g km * single2 n c km * fourierModeC km θ ψ)
      (g n * c * fourierModeC n θ ψ) := by
  have : (fun km => g km * single2 n c km * fourierModeC km θ ψ) =
      fun km => if km = n then g n * c * fourierModeC n θ ψ else 0 := by
    funext km; unfold single2; split_ifs with h <;> simp [h]
  rw [this]; exact hasSum_ite_eq n _

theorem hasSum_uOfG (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (θ ψ : ℂ) :
    ∀ recs : List TRec, HasSum (fun km => uOfG g D sel recs km * fourierModeC km θ ψ)
      ((recs.map fun r => termC g D sel r θ ψ).sum)
  | [] => by simp [uOfG]
  | r :: rs => by
    have h1 := (hasSum_single2 g (r.k, r.m) (cP D (sel r).1 (sel r).2) θ ψ).add
      (hasSum_single2 g (-r.k, -r.m) (cM D (sel r).1 (sel r).2) θ ψ)
    have h2 := h1.add (hasSum_uOfG g D sel θ ψ rs)
    convert h2 using 1
    · funext km; simp only [uOfG, List.map_cons, List.sum_cons]; ring
    · simp [termC]

/-- The complex Fourier sum of `uOfG` is the finite sum of the record terms. -/
theorem fourierSumC_uOfG (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec)
    (θ ψ : ℂ) : fourierSumC (uOfG g D sel recs) θ ψ = (recs.map fun r => termC g D sel r θ ψ).sum :=
  (hasSum_uOfG g D sel θ ψ recs).tsum_eq

/-- The support of `uOfG` is contained in the record modes and their negatives. -/
theorem uOfG_eq_zero (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec)
    (km : ℤ × ℤ) (h : km ∉ (recs.map fun r => (r.k, r.m)) ++ (recs.map fun r => (-r.k, -r.m))) :
    uOfG g D sel recs km = 0 := by
  unfold uOfG
  rw [mul_eq_zero]; right
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and] at h
  have h1 : km ≠ (r.k, r.m) := fun e => h.1 r hr e.symm
  have h2 : km ≠ (-r.k, -r.m) := fun e => h.2 r hr e.symm
  simp [single2, h1, h2]

/-- Finite support: `uOfG ∈ ℓ¹_ρ` for every `ρ`. -/
theorem inWeighted_uOfG (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec)
    (ρ : ℝ) : InWeighted ρ (uOfG g D sel recs) := by
  unfold InWeighted
  apply summable_of_ne_finset_zero
    (s := ((recs.map fun r => (r.k, r.m)) ++ (recs.map fun r => (-r.k, -r.m))).toFinset)
  intro km hkm
  rw [List.mem_toFinset] at hkm
  rw [uOfG_eq_zero g D sel recs km hkm, norm_zero, zero_mul]

/-! ## Real values -/

theorem fourierModeC_ofReal_pm (k m : ℤ) (θ ψ : ℝ) :
    fourierModeC (k, m) θ ψ = Real.cos (k * θ + m * ψ) + Real.sin (k * θ + m * ψ) * I ∧
    fourierModeC (-k, -m) θ ψ = Real.cos (k * θ + m * ψ) - Real.sin (k * θ + m * ψ) * I := by
  unfold fourierModeC
  constructor
  · rw [show I * (((k, m) : ℤ × ℤ).1 * (θ : ℂ) + ((k, m) : ℤ × ℤ).2 * ψ) =
      ((k * θ + m * ψ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · rw [show I * (((-k, -m) : ℤ × ℤ).1 * (θ : ℂ) + ((-k, -m) : ℤ × ℤ).2 * ψ) =
      ((-(k * θ + m * ψ) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring

theorem termC_one_ofReal (D : ℕ) (sel : TRec → ℤ × ℤ) (r : TRec) (θ ψ : ℝ) :
    termC (fun _ => 1) D sel r θ ψ =
      (((((sel r).1 : ℝ) * Real.cos (r.ang θ ψ) + (sel r).2 * Real.sin (r.ang θ ψ)) / D : ℝ) :
        ℂ) := by
  obtain ⟨h1, h2⟩ := fourierModeC_ofReal_pm r.k r.m θ ψ
  unfold termC cP cM
  rw [h1, h2]
  unfold TRec.ang
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem termC_lsym_ofReal (D : ℕ) (ι : ℝ) (sel : TRec → ℤ × ℤ) (r : TRec) (θ ψ : ℝ) :
    termC (lsym ι) D sel r θ ψ =
      ((((r.m : ℝ) + ι * r.k) * (-((sel r).1 : ℝ) * Real.sin (r.ang θ ψ) +
        (sel r).2 * Real.cos (r.ang θ ψ)) / D : ℝ) : ℂ) := by
  obtain ⟨h1, h2⟩ := fourierModeC_ofReal_pm r.k r.m θ ψ
  unfold termC cP cM lsym
  rw [h1, h2]
  unfold TRec.ang
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

theorem fourierSumC_uR_ofReal (D : ℕ) (recs : List TRec) (θ ψ : ℝ) :
    fourierSumC (uR D recs) θ ψ = (Rr D recs θ ψ : ℂ) := by
  unfold uR Rr
  rw [fourierSumC_uOfG, ofReal_list_sum', List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  rw [termC_one_ofReal]

theorem fourierSumC_uZ_ofReal (D : ℕ) (recs : List TRec) (θ ψ : ℝ) :
    fourierSumC (uZ D recs) θ ψ = (Zr D recs θ ψ : ℂ) := by
  unfold uZ Zr
  rw [fourierSumC_uOfG, ofReal_list_sum', List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  rw [termC_one_ofReal]

theorem fourierSumC_uLR_ofReal (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℝ) :
    fourierSumC (uLR D ι recs) θ ψ = (LRr D ι recs θ ψ : ℂ) := by
  unfold uLR LRr
  rw [fourierSumC_uOfG, ofReal_list_sum', List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  rw [termC_lsym_ofReal]

theorem fourierSumC_uLZ_ofReal (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℝ) :
    fourierSumC (uLZ D ι recs) θ ψ = (LZr D ι recs θ ψ : ℂ) := by
  unfold uLZ LZr
  rw [fourierSumC_uOfG, ofReal_list_sum', List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  rw [termC_lsym_ofReal]

/-! ## Strip bounds -/

theorem norm_cP_le (D : ℕ) (c c' : ℤ) :
    ‖cP D c c'‖ ≤ ((c.natAbs + c'.natAbs : ℕ) : ℝ) / (2 * D) := by
  unfold cP
  rw [norm_div]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have : ‖(2 * (D : ℂ))‖ = 2 * D := by
      rw [norm_mul, Complex.norm_natCast]; norm_num
    rw [this]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast,
      Nat.cast_add, natAbs_cast, natAbs_cast]

theorem norm_cM_le (D : ℕ) (c c' : ℤ) :
    ‖cM D c c'‖ ≤ ((c.natAbs + c'.natAbs : ℕ) : ℝ) / (2 * D) := by
  unfold cM
  rw [norm_div]
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  · have : ‖(2 * (D : ℂ))‖ = 2 * D := by
      rw [norm_mul, Complex.norm_natCast]; norm_num
    rw [this]
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, Complex.norm_intCast,
      Nat.cast_add, natAbs_cast, natAbs_cast]

theorem weight_neg (ρ : ℝ) (k m : ℤ) : weight ρ (-k, -m) = weight ρ (k, m) := by
  simp [weight, modeSize, abs_neg]

/-- **Sup bound on the strip**: `|Σ termC| ≤ Σ G (|c| + |c'|)/D · e^{ρ(|k|+|m|)}` if `|g| ≤ G` on
the record modes and their negatives. -/
theorem norm_fourierSumC_uOfG_le {ρ : ℝ} {θ ψ : ℂ} (hθ : |θ.im| ≤ ρ) (hψ : |ψ.im| ≤ ρ)
    (g : ℤ × ℤ → ℂ) (G : TRec → ℝ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec)
    (hg : ∀ r ∈ recs, ‖g (r.k, r.m)‖ ≤ G r ∧ ‖g (-r.k, -r.m)‖ ≤ G r) :
    ‖fourierSumC (uOfG g D sel recs) θ ψ‖ ≤
      (recs.map fun r => G r * (((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / D *
        weight ρ (r.k, r.m)).sum := by
  rw [fourierSumC_uOfG]
  refine (norm_list_sum_le' _).trans ?_
  simp only [List.map_map]
  apply list_sum_le_sum
  intro r hr
  simp only [Function.comp_apply]
  obtain ⟨hg1, hg2⟩ := hg r hr
  have hG : 0 ≤ G r := (norm_nonneg _).trans hg1
  have m1 := norm_fourierModeC_le hθ hψ (r.k, r.m)
  have m2 := norm_fourierModeC_le hθ hψ (-r.k, -r.m)
  rw [weight_neg] at m2
  have c1 := norm_cP_le D (sel r).1 (sel r).2
  have c2 := norm_cM_le D (sel r).1 (sel r).2
  unfold termC
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hw : 0 ≤ weight ρ (r.k, r.m) := (Real.exp_pos _).le
  have hn : 0 ≤ (((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / (2 * D) := by positivity
  calc ‖g (r.k, r.m)‖ * ‖cP D (sel r).1 (sel r).2‖ * ‖fourierModeC (r.k, r.m) θ ψ‖ +
        ‖g (-r.k, -r.m)‖ * ‖cM D (sel r).1 (sel r).2‖ * ‖fourierModeC (-r.k, -r.m) θ ψ‖
      ≤ G r * ((((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / (2 * D)) * weight ρ (r.k, r.m) +
        G r * ((((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / (2 * D)) *
          weight ρ (r.k, r.m) := by
        gcongr
    _ = _ := by
        rcases Nat.eq_zero_or_pos D with hD | hD
        · subst hD; simp
        · field_simp; ring

/-- **Displacement under complexification**: `|Σ termC(θ,ψ) − Σ termC(Re θ, Re ψ)| ≤
Σ G (|c| + |c'|)/D · (e^{ρ(|k|+|m|)} − 1)`. -/
theorem norm_fourierSumC_uOfG_sub_re_le {ρ : ℝ} {θ ψ : ℂ} (hθ : |θ.im| ≤ ρ) (hψ : |ψ.im| ≤ ρ)
    (g : ℤ × ℤ → ℂ) (G : TRec → ℝ) (D : ℕ) (sel : TRec → ℤ × ℤ) (recs : List TRec)
    (hg : ∀ r ∈ recs, ‖g (r.k, r.m)‖ ≤ G r ∧ ‖g (-r.k, -r.m)‖ ≤ G r) :
    ‖fourierSumC (uOfG g D sel recs) θ ψ - fourierSumC (uOfG g D sel recs) θ.re ψ.re‖ ≤
      (recs.map fun r => G r * (((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / D *
        (weight ρ (r.k, r.m) - 1)).sum := by
  rw [fourierSumC_uOfG, fourierSumC_uOfG, list_sum_map_sub]
  refine (norm_list_sum_le' _).trans ?_
  simp only [List.map_map]
  apply list_sum_le_sum
  intro r hr
  simp only [Function.comp_apply]
  obtain ⟨hg1, hg2⟩ := hg r hr
  have m1 := TorusFieldAna.norm_fourierModeC_sub_re_le hθ hψ (r.k, r.m)
  have m2 := TorusFieldAna.norm_fourierModeC_sub_re_le hθ hψ (-r.k, -r.m)
  rw [weight_neg] at m2
  have c1 := norm_cP_le D (sel r).1 (sel r).2
  have c2 := norm_cM_le D (sel r).1 (sel r).2
  have hw : 0 ≤ weight ρ (r.k, r.m) - 1 := (norm_nonneg _).trans m1
  have e : termC g D sel r θ ψ - termC g D sel r (θ.re : ℂ) (ψ.re : ℂ) =
      g (r.k, r.m) * cP D (sel r).1 (sel r).2 *
        (fourierModeC (r.k, r.m) θ ψ - fourierModeC (r.k, r.m) θ.re ψ.re) +
      g (-r.k, -r.m) * cM D (sel r).1 (sel r).2 *
        (fourierModeC (-r.k, -r.m) θ ψ - fourierModeC (-r.k, -r.m) θ.re ψ.re) := by
    unfold termC; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc ‖g (r.k, r.m)‖ * ‖cP D (sel r).1 (sel r).2‖ *
        ‖fourierModeC (r.k, r.m) θ ψ - fourierModeC (r.k, r.m) θ.re ψ.re‖ +
        ‖g (-r.k, -r.m)‖ * ‖cM D (sel r).1 (sel r).2‖ *
        ‖fourierModeC (-r.k, -r.m) θ ψ - fourierModeC (-r.k, -r.m) θ.re ψ.re‖
      ≤ G r * ((((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / (2 * D)) *
          (weight ρ (r.k, r.m) - 1) +
        G r * ((((sel r).1.natAbs + (sel r).2.natAbs : ℕ) : ℝ) / (2 * D)) *
          (weight ρ (r.k, r.m) - 1) := by
        have hG : 0 ≤ G r := (norm_nonneg _).trans hg1
        gcongr
    _ = _ := by
        rcases Nat.eq_zero_or_pos D with hD | hD
        · subst hD; simp
        · field_simp; ring

/-! ## Grid angles -/

/-- `cos(2πn/L)` depends on `n mod L`. -/
theorem cos_grid_mod (L : ℕ) (hL : 0 < L) (n : ℤ) :
    Real.cos (2 * Real.pi * n / L) = Real.cos (2 * Real.pi * ((n % L).toNat : ℕ) / L) ∧
    Real.sin (2 * Real.pi * n / L) = Real.sin (2 * Real.pi * ((n % L).toNat : ℕ) / L) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hmod : 0 ≤ n % L := Int.emod_nonneg n (by exact_mod_cast hL.ne')
  have e : ((n % L).toNat : ℝ) = (n : ℝ) - L * (n / L : ℤ) := by
    rw [toNat_cast_real hmod, Int.emod_def]; push_cast; ring
  have e2 : 2 * Real.pi * ((n % L).toNat : ℕ) / L =
      2 * Real.pi * n / L + ((-(n / L) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [e]; push_cast; field_simp; ring
  rw [e2, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact ⟨rfl, rfl⟩

/-- The grid index of the phase `k θ_j + m φ_l` (`θ_j = 2πj/N₁`, `φ_l = 2πl/L`, `L = N₁ q`). -/
def gidx (L q : ℕ) (k m : ℤ) (j l : ℕ) : ℕ := ((k * q * j + m * l) % L).toNat

theorem ang_grid (L q N₁ : ℕ) (hq : N₁ * q = L) (hL : 0 < L) (r : TRec) (j l : ℕ) :
    r.ang (2 * Real.pi * j / N₁) (2 * Real.pi * l / L) =
      2 * Real.pi * ((r.k * q * j + r.m * l : ℤ) : ℝ) / L := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hN : (N₁ : ℝ) ≠ 0 := by
    rintro h
    have : (N₁ : ℕ) = 0 := by exact_mod_cast h
    subst this; simp at hq; omega
  have hq0 : (q : ℝ) ≠ 0 := by
    rintro h
    have : (q : ℕ) = 0 := by exact_mod_cast h
    subst this; simp at hq; omega
  unfold TRec.ang
  rw [← hq]; push_cast
  field_simp

theorem re_im_sub_gauss (D : ℕ) (x y : ℝ) (w : ℤ × ℤ) :
    ((x : ℂ) + y * I - gauss D w).re = x - w.1 / D ∧
      ((x : ℂ) + y * I - gauss D w).im = y - w.2 / D := by
  constructor <;> simp [gauss, Complex.div_natCast_re, Complex.div_natCast_im]

/-- Approximants of `cos` and `sin` at a grid angle from the exponential table. -/
theorem cos_sin_approx {D L E : ℕ} {tbl : List (ℤ × ℤ)}
    (htbl : ∀ t < L, ‖gexp L t - gauss D (tget tbl t)‖ ≤ (E : ℝ) / D) (hL : 0 < L) (n : ℤ) :
    Approx D (Real.cos (2 * Real.pi * n / L)) ((tget tbl ((n % L).toNat)).1, E) ∧
    Approx D (Real.sin (2 * Real.pi * n / L)) ((tget tbl ((n % L).toNat)).2, E) := by
  obtain ⟨hc, hs⟩ := cos_grid_mod L hL n
  rw [hc, hs]
  have ht : (n % L).toNat < L := by
    have h1 : n % L < L := Int.emod_lt_of_pos n (by exact_mod_cast hL)
    have h0 : 0 ≤ n % L := Int.emod_nonneg n (by exact_mod_cast hL.ne')
    omega
  have h := htbl _ ht
  rw [gexp_eq] at h
  set t := (n % L).toNat
  have hre := (Complex.abs_re_le_norm _).trans h
  have him := (Complex.abs_im_le_norm _).trans h
  obtain ⟨er, ei⟩ := re_im_sub_gauss D (Real.cos (2 * Real.pi * t / L))
    (Real.sin (2 * Real.pi * t / L)) (tget tbl t)
  rw [er] at hre; rw [ei] at him
  exact ⟨hre, him⟩

/-! ## The torus at a grid point -/

/-- The approximant of `(c cos x + c' sin x)/D` for one record at the grid point. -/
def recAP (D : ℕ) (c c' : ℤ) (cs : ℤ × ℤ) (E : ℕ) : ℤ × ℕ :=
  apAdd (apMul D (c, 0) (cs.1, E)) (apMul D (c', 0) (cs.2, E))

/-- The approximant of `(m + ιk)(-c sin x + c' cos x)/D` for one record. -/
def recLAP (D : ℕ) (Iq : ℤ) (k m c c' : ℤ) (cs : ℤ × ℤ) (E : ℕ) : ℤ × ℕ :=
  apMul D (apAdd (m * D, 0) (apSmul k (Iq, 1)))
    (apAdd (apMul D (-c, 0) (cs.2, E)) (apMul D (c', 0) (cs.1, E)))

/-- Approximants of `R, z, 𝓛R, 𝓛z` at the grid point `(j, l)`. -/
def torusAP (D L q E : ℕ) (Iq : ℤ) (tbl : List (ℤ × ℤ)) (recs : List TRec) (j l : ℕ) :
    (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) :=
  let cs := fun r : TRec => tget tbl (gidx L q r.k r.m j l)
  (apSum (recs.map fun r => recAP D r.a r.a' (cs r) E),
   apSum (recs.map fun r => recAP D r.b r.b' (cs r) E),
   apSum (recs.map fun r => recLAP D Iq r.k r.m r.a r.a' (cs r) E),
   apSum (recs.map fun r => recLAP D Iq r.k r.m r.b r.b' (cs r) E))

theorem recAP_sound {D L E : ℕ} (hD : 0 < D) {tbl : List (ℤ × ℤ)}
    (htbl : ∀ t < L, ‖gexp L t - gauss D (tget tbl t)‖ ≤ (E : ℝ) / D) (hL : 0 < L) (n c c' : ℤ) :
    Approx D (((c : ℝ) * Real.cos (2 * Real.pi * n / L) + c' * Real.sin (2 * Real.pi * n / L)) / D)
      (recAP D c c' (tget tbl ((n % L).toNat)) E) := by
  obtain ⟨hc, hs⟩ := cos_sin_approx htbl hL n
  have e : ((c : ℝ) * Real.cos (2 * Real.pi * n / L) + c' * Real.sin (2 * Real.pi * n / L)) / D =
      (c : ℝ) / D * Real.cos (2 * Real.pi * n / L) +
        (c' : ℝ) / D * Real.sin (2 * Real.pi * n / L) := by
    ring
  rw [e]
  exact ((approx_exact D c).mul hD hc).add ((approx_exact D c').mul hD hs)

theorem recLAP_sound {D L E : ℕ} (hD : 0 < D) {tbl : List (ℤ × ℤ)}
    (htbl : ∀ t < L, ‖gexp L t - gauss D (tget tbl t)‖ ≤ (E : ℝ) / D) (hL : 0 < L) {ι : ℝ}
    {Iq : ℤ} (hι : Approx D ι (Iq, 1)) (n k m c c' : ℤ) :
    Approx D (((m : ℝ) + ι * k) * (-(c : ℝ) * Real.sin (2 * Real.pi * n / L) +
        c' * Real.cos (2 * Real.pi * n / L)) / D)
      (recLAP D Iq k m c c' (tget tbl ((n % L).toNat)) E) := by
  obtain ⟨hc, hs⟩ := cos_sin_approx htbl hL n
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hlam : Approx D ((m : ℝ) + ι * k) (apAdd (m * D, 0) (apSmul k (Iq, 1))) := by
    have h1 : Approx D (m : ℝ) (m * D, 0) := by
      have := approx_exact D (m * D); push_cast at this; rwa [mul_div_cancel_right₀ _ hD'] at this
    have := h1.add (hι.smul k)
    rwa [mul_comm (k : ℝ) ι] at this
  have e : ((m : ℝ) + ι * k) * (-(c : ℝ) * Real.sin (2 * Real.pi * n / L) +
        c' * Real.cos (2 * Real.pi * n / L)) / D =
      ((m : ℝ) + ι * k) * ((-c : ℤ) / D * Real.sin (2 * Real.pi * n / L) +
        (c' : ℝ) / D * Real.cos (2 * Real.pi * n / L)) := by
    push_cast; ring
  rw [e]
  exact hlam.mul hD (((approx_exact D (-c)).mul hD hs).add ((approx_exact D c').mul hD hc))

/-- **Soundness of the torus approximants** at the grid point `(2πj/N₁, 2πl/L)`. -/
theorem torusAP_sound {D L q N₁ E : ℕ} (hD : 0 < D) (hL : 0 < L) (hq : N₁ * q = L)
    {tbl : List (ℤ × ℤ)} (htbl : ∀ t < L, ‖gexp L t - gauss D (tget tbl t)‖ ≤ (E : ℝ) / D)
    {ι : ℝ} {Iq : ℤ} (hι : Approx D ι (Iq, 1)) (recs : List TRec) (j l : ℕ) :
    let θ := 2 * Real.pi * j / N₁
    let φ := 2 * Real.pi * l / L
    Approx D (Rr D recs θ φ) (torusAP D L q E Iq tbl recs j l).1 ∧
    Approx D (Zr D recs θ φ) (torusAP D L q E Iq tbl recs j l).2.1 ∧
    Approx D (LRr D ι recs θ φ) (torusAP D L q E Iq tbl recs j l).2.2.1 ∧
    Approx D (LZr D ι recs θ φ) (torusAP D L q E Iq tbl recs j l).2.2.2 := by
  intro θ φ
  have hang : ∀ r : TRec, r.ang θ φ = 2 * Real.pi * ((r.k * q * j + r.m * l : ℤ) : ℝ) / L :=
    fun r => ang_grid L q N₁ hq hL r j l
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Rr torusAP
    simp only
    refine Approx.sum recs _ _ fun r _ => ?_
    simp only [hang r]
    exact recAP_sound hD htbl hL _ r.a r.a'
  · unfold Zr torusAP
    simp only
    refine Approx.sum recs _ _ fun r _ => ?_
    simp only [hang r]
    exact recAP_sound hD htbl hL _ r.b r.b'
  · unfold LRr torusAP
    simp only
    refine Approx.sum recs _ _ fun r _ => ?_
    simp only [hang r]
    exact recLAP_sound hD htbl hL hι _ r.k r.m r.a r.a'
  · unfold LZr torusAP
    simp only
    refine Approx.sum recs _ _ fun r _ => ?_
    simp only [hang r]
    exact recLAP_sound hD htbl hL hι _ r.k r.m r.b r.b'

/-! ## Sanity -/

/-- The empty torus has the zero coefficient sequence. -/
theorem uOfG_nil (g : ℤ × ℤ → ℂ) (D : ℕ) (sel : TRec → ℤ × ℤ) : uOfG g D sel [] = 0 := by
  funext km; simp [uOfG]

/-- The empty torus has `R = 0`. -/
theorem Rr_nil (D : ℕ) (θ φ : ℝ) : Rr D [] θ φ = 0 := by simp [Rr]

end PlasmaLean.Design.CoilKam
