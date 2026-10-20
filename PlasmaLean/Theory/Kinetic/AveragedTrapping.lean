/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import PlasmaLean.Theory.Kinetic.OscillatoryAveraging
public import Mathlib.Data.List.GetD
public meta import Lean

/-!
# Trapping times from oscillatory averaging (M4/T8)

Source: `notes/theory/guiding-centre-averaging.md` §2.1 and §4. The existing finite-time
trapping theorem `Boozer.boozerGC_trapped_until` bounds the helical-momentum drift by the
worst case `(2H/B_min) ε t`. Here the drift bound is an arbitrary history-conditional bound
`|P t − P 0| ≤ K₀ + K₁ t`, and the iterated oscillatory integration by parts
(`osc_ibp_drift_iter`, Lemma A) supplies one whenever
`P' = a₀ sin Φ + b₀ cos Φ + e` with a phase speed `Ω = Φ' ≥ Ω₀ > 0` and amplitudes bounded
along the orbit while it stays in the region.

* `boozerGC_trapped_until_drift`: trapping until `T` from any drift bound;
* `boozerGC_trapped_until_averaged`: trapping until `T` from `k`-fold oscillatory structure:
  the gap is `|MG| Δρ + (2 (∑_{j<k} Aⱼ)/Ω₀ + (A_k + η) T)/|q| ≤ ι_min (c' − ψ(0))`;
* sanity: `boozerGC_trapped_until_drift_recovers` recovers the worst-case theorem's form, and
  `averaged_gap_k_zero` shows `k = 0` is the unaveraged linear bound;
* `LiePoly`: exact rational polynomials (`Poly`), their Lie derivatives along polynomial
  vector fields with the chain rule `hasDerivAt_eval`, exponent normalization `normWith`, and
  sound ball enclosures (`QBall` exact, `FBall` fixed point `c/2⁶⁴` with outward rounding;
  `FBall.mem_evalT_toFix`), so that amplitude bounds become kernel-checked certificates;
  two-stage enclosures (`stage1` to a ball-coefficient polynomial `BPoly`, then `evalB` on
  each cell; `BPoly.holds_stage1`, `FBall.mem_evalB`) and the literal parsers `fpoly%`,
  `bpoly%`; fixtures `lie_square_fixture`, `addP_cancel_fixture`, `hasDerivAt_sq_via_lie`.

All statements are about the vacuum Boozer guiding-centre **model** (supplied orbits; its
derivation from the Lorentz force is not formalized). The oscillatory hypotheses
(`Ω ≥ Ω₀ > 0`) exclude trapped and barely passing particles, whose phase speed changes sign.
The amplitude bounds are separate obligations; `Design/NearAxisQAAveraged` discharges them by
an exact polynomial Lie-derivative computation and a kernel-checked ball-arithmetic cover.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Kinetic

variable {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- **Trapping until `T` from a drift bound.** If, while the orbit has stayed in `ψ ≤ c`, the
helical momentum satisfies `|P t − P 0| ≤ K₀ + K₁ t` (`K₁ ≥ 0`) and `|ρ t − ρ 0| ≤ Δρ`, and the
gap `|MG| Δρ + (K₀ + K₁ T)/|q| ≤ ι_min (c' − ψ(0))` holds with `c' < c`, then `ψ ≤ c'` on
`[0, T]`. The orbit equations are only used for continuity of `ψ` on `[0, T]`. -/
theorem boozerGC_trapped_until_drift (hq : q ≠ 0)
    {N M c c' ιmin Δρ K₀ K₁ T : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T)
    (hcc : c' < c) (hψ0 : ψ 0 ≤ c') (hι : 0 < ιmin) (hK₁ : 0 ≤ K₁)
    (hmono : ∀ x, ψ 0 ≤ x → x ≤ c →
      ιmin * (x - ψ 0) ≤ |(N * x - M * F.ψp x) - (N * ψ 0 - M * F.ψp (ψ 0))|)
    (hΔρ : ∀ t ∈ Set.Icc 0 T, (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) → |ρ t - ρ 0| ≤ Δρ)
    (hdrift : ∀ t ∈ Set.Icc 0 T, (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) →
      |helicalMomentum F q N M ψ ρ t - helicalMomentum F q N M ψ ρ 0| ≤ K₀ + K₁ * t)
    (hgap : |M * F.G| * Δρ + (K₀ + K₁ * T) / |q| ≤ ιmin * (c' - ψ 0)) :
    ∀ t ∈ Set.Icc 0 T, ψ t ≤ c' := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hT)
  have hqp : 0 < |q| := abs_pos.mpr hq
  set f : ℝ → ℝ := fun s => ψ (Set.projIcc 0 T hT s) with hfdef
  have hψc : ContinuousOn ψ (Set.Icc 0 T) :=
    fun s hs => (h.dψ s hs).continuousAt.continuousWithinAt
  have hfc : Continuous f := hψc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun s => Subtype.mem _)
  have hfeq : ∀ s ∈ Set.Icc 0 T, f s = ψ s := fun s hs => by
    simp only [hfdef, Set.projIcc_of_mem hT hs]
  have hf0 : f 0 = ψ 0 := hfeq 0 ⟨le_rfl, hT⟩
  intro t₀ ht₀
  rw [← hfeq t₀ ht₀]
  refine trapped_until hfc hcc (hf0 ▸ hψ0) (fun t ht hhist' => ?_) t₀ ht₀
  have hsub : ∀ s ∈ Set.Icc 0 t, s ∈ Set.Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hhist : ∀ s ∈ Set.Icc 0 t, ψ s ≤ c := fun s hs => by
    rw [← hfeq s (hsub s hs)]; exact hhist' s hs
  rw [hfeq t ht]
  rcases le_or_gt (ψ t) (ψ 0) with hle | hgt
  · linarith
  have hdr := hdrift t ht hhist
  have hρd := hΔρ t ht hhist
  have hm1 := hmono (ψ t) hgt.le (hhist t ⟨ht.1, le_rfl⟩)
  have e : q * ((N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))) =
      (helicalMomentum F q N M ψ ρ t - helicalMomentum F q N M ψ ρ 0) -
        q * (M * F.G) * (ρ t - ρ 0) := by
    unfold helicalMomentum; ring
  have hqf : |q| * |(N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))| ≤
      (K₀ + K₁ * t) + |q| * (|M * F.G| * Δρ) := by
    rw [← abs_mul, e]
    refine (abs_sub _ _).trans (add_le_add hdr ?_)
    rw [abs_mul, abs_mul, mul_assoc]
    gcongr
  have hKt : K₀ + K₁ * t ≤ K₀ + K₁ * T := by nlinarith [ht.2]
  have hf : |(N * ψ t - M * F.ψp (ψ t)) - (N * ψ 0 - M * F.ψp (ψ 0))| ≤
      (K₀ + K₁ * T) / |q| + |M * F.G| * Δρ := by
    rw [div_add' _ _ _ hqp.ne', le_div_iff₀ hqp]
    nlinarith
  have : ιmin * (ψ t - ψ 0) ≤ ιmin * (c' - ψ 0) := by linarith
  have := le_of_mul_le_mul_left this hι
  linarith

/-- **Trapping until `T` from `k`-fold oscillatory averaging.** Write `R s` for "`s ∈ [0, T]`
and the orbit has stayed in `ψ ≤ c` on `[0, s]`". Suppose that whenever `R s`:
`P' = a₀ sin Φ + b₀ cos Φ + e` with `|e| ≤ η`; `Φ' = Ω ≥ Ω₀ > 0`; the amplitude sequences
satisfy `(aⱼ/Ω)' = bⱼ₊₁`, `(bⱼ/Ω)' = −aⱼ₊₁` (`j < k`) and `|aⱼ| + |bⱼ| ≤ Aⱼ` (`j ≤ k`). With
the orbit-width bound `Δρ` and the gap
`|MG| Δρ + (2 (∑_{j<k} Aⱼ)/Ω₀ + (A_k + η) T)/|q| ≤ ι_min (c' − ψ(0))`, the orbit stays in
`ψ ≤ c'` on `[0, T]`. The secular rate is `A_k + η` instead of the worst-case `2Hε/B_min`. -/
theorem boozerGC_trapped_until_averaged (hq : q ≠ 0)
    {N M c c' ιmin Δρ T Ω₀ η : ℝ} {k : ℕ} {Φ Ω e : ℝ → ℝ} {a b : ℕ → ℝ → ℝ} {A : ℕ → ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T)
    (hcc : c' < c) (hψ0 : ψ 0 ≤ c') (hι : 0 < ιmin) (hΩ₀ : 0 < Ω₀) (hAk : 0 ≤ A k + η)
    (hmono : ∀ x, ψ 0 ≤ x → x ≤ c →
      ιmin * (x - ψ 0) ≤ |(N * x - M * F.ψp x) - (N * ψ 0 - M * F.ψp (ψ 0))|)
    (hΔρ : ∀ t ∈ Set.Icc 0 T, (∀ s ∈ Set.Icc 0 t, ψ s ≤ c) → |ρ t - ρ 0| ≤ Δρ)
    (hP : ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) →
      HasDerivAt (helicalMomentum F q N M ψ ρ)
        (a 0 s * Real.sin (Φ s) + b 0 s * Real.cos (Φ s) + e s) s)
    (he : ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) → |e s| ≤ η)
    (hΦ : ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) → HasDerivAt Φ (Ω s) s)
    (hΩ : ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) → Ω₀ ≤ Ω s)
    (ha : ∀ j < k, ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) →
      HasDerivAt (fun r => a j r / Ω r) (b (j + 1) s) s)
    (hb : ∀ j < k, ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) →
      HasDerivAt (fun r => b j r / Ω r) (-a (j + 1) s) s)
    (hA : ∀ j ≤ k, ∀ s ∈ Set.Icc 0 T, (∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c) →
      |a j s| + |b j s| ≤ A j)
    (hgap : |M * F.G| * Δρ + (2 * (∑ j ∈ Finset.range k, A j) / Ω₀ + (A k + η) * T) / |q| ≤
      ιmin * (c' - ψ 0)) :
    ∀ t ∈ Set.Icc 0 T, ψ t ≤ c' := by
  refine boozerGC_trapped_until_drift hq h hcc hψ0 hι hAk hmono hΔρ (fun t ht hhist => ?_) hgap
  -- on `[0, t]` every point has its history inside the region
  have hR : ∀ s ∈ Set.Icc 0 t, s ∈ Set.Icc 0 T ∧ ∀ s' ∈ Set.Icc 0 s, ψ s' ≤ c :=
    fun s hs => ⟨⟨hs.1, hs.2.trans ht.2⟩, fun s' hs' => hhist s' ⟨hs'.1, hs'.2.trans hs.2⟩⟩
  exact osc_ibp_drift_iter (T := t) hΩ₀ (fun s hs => hΦ s (hR s hs).1 (hR s hs).2)
    (fun s hs => hΩ s (hR s hs).1 (hR s hs).2) (fun s hs => he s (hR s hs).1 (hR s hs).2)
    ⟨ht.1, le_rfl⟩ k _ a b A (fun s hs => hP s (hR s hs).1 (hR s hs).2)
    (fun j hj s hs => ha j hj s (hR s hs).1 (hR s hs).2)
    (fun j hj s hs => hb j hj s (hR s hs).1 (hR s hs).2)
    (fun j hj s hs => hA j hj s (hR s hs).1 (hR s hs).2)

/-- Sanity (`k = 0`): with no integration by parts the averaged gap is the linear worst-case
gap: the constant term vanishes and the secular rate is `A₀ + η`. -/
theorem averaged_gap_k_zero (A : ℕ → ℝ) (Ω₀ η T : ℝ) :
    2 * (∑ j ∈ Finset.range 0, A j) / Ω₀ + (A 0 + η) * T = (A 0 + η) * T := by
  simp

/-- Sanity (the drift version recovers the worst-case theorem): with `K₀ = 0` and
`K₁ = 2H(0) ε/B_min`, the gap of `boozerGC_trapped_until_drift` is exactly the gap of
`boozerGC_trapped_until`. -/
theorem boozerGC_trapped_until_drift_recovers (q H ε Bmin T : ℝ) (hq : q ≠ 0) :
    (0 + 2 * H / Bmin * ε * T) / |q| = 2 * H / (|q| * Bmin) * ε * T := by
  have : |q| ≠ 0 := abs_ne_zero.mpr hq
  rw [zero_add]
  field_simp

end PlasmaLean.Kinetic.Boozer

/-! ## Exact polynomial Lie derivatives and ball enclosures

A polynomial in the variables `x₀, x₁, …` is a list of monomials `(c, e)` with rational
coefficient `c` and exponent list `e` (missing exponents are `0`). Addition merges sorted
monomial lists, so like terms combine and cancel exactly. `lie p F` is the derivative of `p`
along the polynomial vector field `F` (`ẋᵢ = Fᵢ`); `hasDerivAt_eval` is the chain rule along any
curve whose coordinates have these derivatives. `normWith f p` rewrites exponents by an
evaluation-preserving map (e.g. `x y → 1` when `x y = 1`). Enclosures use balls
`|x − c| ≤ r`: `QBall` (exact rationals) and `FBall` (fixed point `c/2⁶⁴`, outward rounding,
only `ℤ` arithmetic, so that the kernel evaluates large certificates quickly). All
computations are exact and checked by the kernel; no floating point is trusted.
-/

namespace PlasmaLean.Kinetic.LiePoly

/-- A monomial: coefficient and exponent list. -/
abbrev Mono := ℚ × List ℕ
/-- A polynomial: a list of monomials. -/
abbrev Poly := List Mono

/-- Value of the monomial `∏ xᵢ^{eᵢ}`. -/
@[expose] def evalMono : List ℕ → (ℕ → ℝ) → ℝ
  | [], _ => 1
  | k :: e, x => x 0 ^ k * evalMono e (fun i => x (i + 1))

/-- Value of a polynomial at `x`. -/
@[expose] def eval (p : Poly) (x : ℕ → ℝ) : ℝ := (p.map fun t => (t.1 : ℝ) * evalMono t.2 x).sum

@[simp] theorem eval_nil (x : ℕ → ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (t : Mono) (p : Poly) (x : ℕ → ℝ) :
    eval (t :: p) x = (t.1 : ℝ) * evalMono t.2 x + eval p x := by
  simp [eval]

/-- Lexicographic comparison of exponent lists. -/
@[expose] def cmpE : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpE as bs

theorem cmpE_eq {e f : List ℕ} (h : cmpE e f = .eq) : e = f := by
  induction e generalizing f with
  | nil => cases f <;> simp_all [cmpE]
  | cons a as ih =>
    cases f with
    | nil => simp [cmpE] at h
    | cons b bs =>
      simp only [cmpE] at h
      split_ifs at h with h1 h2
      have : a = b := by omega
      rw [this, ih h]

/-- Exponent addition (padding the shorter list with zeros). -/
@[expose] def addE : List ℕ → List ℕ → List ℕ
  | [], f => f
  | e, [] => e
  | a :: e, b :: f => (a + b) :: addE e f

theorem evalMono_addE (e f : List ℕ) (x : ℕ → ℝ) :
    evalMono (addE e f) x = evalMono e x * evalMono f x := by
  induction e generalizing f x with
  | nil => simp [addE, evalMono]
  | cons a e ih =>
    cases f with
    | nil => simp [addE, evalMono]
    | cons b f => simp only [addE, evalMono, ih, pow_add]; ring

/-- Merge step (structural helper for `addP`). -/
@[expose] def addAux (a : Mono) (p : Poly) (rec : Poly → Poly) : Poly → Poly
  | [] => a :: p
  | b :: q => match cmpE a.2 b.2 with
    | .lt => a :: rec (b :: q)
    | .gt => b :: addAux a p rec q
    | .eq => if a.1 + b.1 = 0 then rec q else (a.1 + b.1, a.2) :: rec q

/-- Sum of two polynomials (merging like terms of sorted inputs). -/
@[expose] def addP : Poly → Poly → Poly
  | [], q => q
  | a :: p, q => addAux a p (addP p) q

theorem eval_addAux (a : Mono) (p : Poly) (rec : Poly → Poly) (x : ℕ → ℝ)
    (hrec : ∀ q, eval (rec q) x = eval p x + eval q x) (q : Poly) :
    eval (addAux a p rec q) x = (a.1 : ℝ) * evalMono a.2 x + eval p x + eval q x := by
  induction q with
  | nil => simp [addAux]
  | cons b q ih =>
    simp only [addAux]
    split
    · simp [hrec]; ring
    · simp [ih]; ring
    · rename_i hc
      have he := cmpE_eq hc
      split_ifs with h0
      · rw [hrec]; simp only [eval_cons, he]
        have : (a.1 : ℝ) = -b.1 := by
          have : (a.1 : ℝ) + b.1 = 0 := by exact_mod_cast h0
          linarith
        rw [this]; ring
      · simp only [eval_cons, hrec, he]; push_cast; ring

@[simp] theorem eval_addP (p q : Poly) (x : ℕ → ℝ) : eval (addP p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [addP]
  | cons a p ih =>
    simp only [addP]
    rw [eval_addAux a p _ x (fun q => ih q) q]
    simp only [eval_cons]

/-- Product of a monomial and a polynomial. -/
@[expose] def mulMono (t : Mono) (q : Poly) : Poly := q.map fun s => (t.1 * s.1, addE t.2 s.2)

theorem eval_mulMono (t : Mono) (q : Poly) (x : ℕ → ℝ) :
    eval (mulMono t q) x = (t.1 : ℝ) * evalMono t.2 x * eval q x := by
  induction q with
  | nil => simp [mulMono]
  | cons s q ih =>
    simp only [mulMono, List.map_cons, eval_cons, evalMono_addE] at ih ⊢
    rw [ih]; push_cast; ring

/-- Product of polynomials. -/
@[expose] def mulP (p q : Poly) : Poly := p.foldr (fun t acc => addP (mulMono t q) acc) []

@[simp] theorem eval_mulP (p q : Poly) (x : ℕ → ℝ) : eval (mulP p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mulP]
  | cons t p ih =>
    simp only [mulP, List.foldr_cons] at ih ⊢
    rw [eval_addP, eval_mulMono, ih]; simp; ring

/-- Scalar multiple. -/
@[expose] def scP (c : ℚ) (p : Poly) : Poly := p.map fun t => (c * t.1, t.2)

@[simp] theorem eval_scP (c : ℚ) (p : Poly) (x : ℕ → ℝ) : eval (scP c p) x = c * eval p x := by
  induction p with
  | nil => simp [scP]
  | cons t p ih => simp only [scP, List.map_cons, eval_cons] at ih ⊢; rw [ih]; push_cast; ring

/-- Exponent list of the variable `xᵢ` among `n` variables. -/
@[expose] def unitE (n i : ℕ) : List ℕ := (List.range n).map fun j => if j = i then 1 else 0

theorem evalMono_zero_list (l : List ℕ) (hl : ∀ k ∈ l, k = 0) (x : ℕ → ℝ) :
    evalMono l x = 1 := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    simp [evalMono, hl.1, ih hl.2]

theorem evalMono_map_range (n i : ℕ) (hi : i < n) (x : ℕ → ℝ) :
    evalMono ((List.range n).map fun j => if j = i then 1 else 0) x = x i := by
  induction n generalizing i x with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [evalMono, Function.comp_def]
    rcases i with _ | i
    · simp only [ite_true, pow_one]
      rw [evalMono_zero_list _ (by simp) _, mul_one]
    · simp only [show (0 : ℕ) ≠ i + 1 by omega, ite_false, pow_zero, one_mul,
        Nat.succ_inj]
      exact ih i (by omega) _

/-- The variable `c · xᵢ` (among `n` variables). -/
@[expose] def varP (n i : ℕ) (c : ℚ) : Poly := [(c, unitE n i)]
/-- The constant `c` (among `n` variables). -/
@[expose] def cstP (n : ℕ) (c : ℚ) : Poly := [(c, List.replicate n 0)]

@[simp] theorem eval_varP {n i : ℕ} (hi : i < n) (c : ℚ) (x : ℕ → ℝ) :
    eval (varP n i c) x = c * x i := by
  simp [varP, unitE, evalMono_map_range n i hi]

@[simp] theorem eval_cstP (n : ℕ) (c : ℚ) (x : ℕ → ℝ) : eval (cstP n c) x = c := by
  simp [cstP, evalMono_zero_list _ (fun k hk => (List.eq_of_mem_replicate hk))]

/-- Decrement the exponent at position `i`. -/
@[expose] def decAt : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: as, 0 => (a - 1) :: as
  | a :: as, n + 1 => a :: decAt as n

/-- Partial derivative `∂p/∂xᵢ`. -/
@[expose] def pderiv (p : Poly) (i : ℕ) : Poly :=
  p.filterMap fun t => if t.2.getD i 0 = 0 then none else some (t.1 * (t.2.getD i 0), decAt t.2 i)

theorem eval_pderiv (p : Poly) (i : ℕ) (x : ℕ → ℝ) :
    eval (pderiv p i) x =
      (p.map fun t => (t.1 : ℝ) * (t.2.getD i 0) * evalMono (decAt t.2 i) x).sum := by
  induction p with
  | nil => simp [pderiv]
  | cons t p ih =>
    simp only [pderiv, List.filterMap_cons] at ih ⊢
    split_ifs with h
    · simp only [List.map_cons, List.sum_cons, h]; rw [ih]; simp
    · simp only [eval_cons, List.map_cons, List.sum_cons]; rw [ih]; push_cast; ring

/-- Lie derivative helper: `∑_{j} ∂p/∂x_{i₀+j} · F_j`. -/
@[expose] def lieAux (p : Poly) : List Poly → ℕ → Poly
  | [], _ => []
  | f :: fs, i => addP (mulP (pderiv p i) f) (lieAux p fs (i + 1))

/-- Lie derivative of `p` along the polynomial vector field `F` (`ẋᵢ = F[i]`). -/
@[expose] def lie (p : Poly) (F : List Poly) : Poly := lieAux p F 0

/-- Formal time derivative of a monomial along a curve with velocity `x'`. -/
@[expose] def dMono : List ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | [], _, _ => 0
  | k :: e, x, x' => k * x 0 ^ (k - 1) * x' 0 * evalMono e (fun i => x (i + 1)) +
      x 0 ^ k * dMono e (fun i => x (i + 1)) (fun i => x' (i + 1))

/-- Chain rule for a monomial along a curve. -/
theorem hasDerivAt_evalMono (e : List ℕ) {X : ℝ → ℕ → ℝ} {X' : ℕ → ℝ} {t : ℝ}
    (hX : ∀ i, HasDerivAt (fun r => X r i) (X' i) t) :
    HasDerivAt (fun r => evalMono e (X r)) (dMono e (X t) X') t := by
  induction e generalizing X X' with
  | nil => simpa [evalMono, dMono] using hasDerivAt_const t (1 : ℝ)
  | cons k e ih =>
    have h0 := (hX 0).pow k
    have h1 := ih (X := fun r i => X r (i + 1)) (X' := fun i => X' (i + 1)) (fun i => hX (i + 1))
    convert h0.mul h1 using 1
    · funext r; rfl
    · simp [dMono]

/-- The formal derivative as a sum over variables. -/
theorem dMono_eq_sum (e : List ℕ) (x x' : ℕ → ℝ) (n : ℕ) (hn : e.length ≤ n) :
    dMono e x x' = ∑ j ∈ Finset.range n,
      (e.getD j 0 : ℝ) * evalMono (decAt e j) x * x' j := by
  induction e generalizing x x' n with
  | nil => simp [dMono]
  | cons k e ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Finset.sum_range_succ', dMono, ih _ _ n (by simpa using hn)]
    simp only [List.getD_cons_succ, decAt, evalMono, List.getD_cons_zero]
    rw [add_comm, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => by ring
    · ring

theorem eval_lieAux (p : Poly) (F : List Poly) (i₀ : ℕ) (x : ℕ → ℝ) :
    eval (lieAux p F i₀) x = ∑ j ∈ Finset.range F.length,
      eval (pderiv p (i₀ + j)) x * eval (F.getD j []) x := by
  induction F generalizing i₀ with
  | nil => simp [lieAux]
  | cons f F ih =>
    rw [lieAux, eval_addP, eval_mulP, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl fun j _ => by rw [show i₀ + 1 + j = i₀ + (j + 1) by ring]

/-- The Lie derivative evaluates to the formal time derivative. -/
theorem eval_lie (p : Poly) (F : List Poly) (x : ℕ → ℝ) :
    eval (lie p F) x =
      (p.map fun t => (t.1 : ℝ) * dMono t.2 x (fun i => eval (F.getD i []) x)).sum := by
  rw [lie, eval_lieAux]
  simp only [zero_add, eval_pderiv]
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    set N := max t.2.length F.length
    rw [dMono_eq_sum t.2 x _ N (le_max_left _ _), Finset.mul_sum]
    have hsplit : ∀ (n : ℕ) (f : ℕ → ℝ), n ≤ N → (∀ j, n ≤ j → j < N → f j = 0) →
        ∑ j ∈ Finset.range n, f j = ∑ j ∈ Finset.range N, f j := by
      intro n f hn hf
      rw [← Finset.sum_range_add_sum_Ico _ hn]
      rw [Finset.sum_eq_zero (fun j hj => hf j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2),
        add_zero]
    rw [hsplit F.length _ (le_max_right _ _) (fun j hj _ => by
      rw [List.getD_eq_default _ _ hj, eval_nil, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => by ring

/-- **Chain rule along a curve**: if each coordinate satisfies `ẋᵢ = Fᵢ(x)` at `t` (coordinates
beyond the list have derivative `0`), then `d/dt p(x(t)) = (lie p F)(x(t))`. -/
theorem hasDerivAt_eval (p : Poly) (F : List Poly) {X : ℝ → ℕ → ℝ} {t : ℝ}
    (hX : ∀ i, HasDerivAt (fun r => X r i) (eval (F.getD i []) (X t)) t) :
    HasDerivAt (fun r => eval p (X r)) (eval (lie p F) (X t)) t := by
  rw [eval_lie]
  induction p with
  | nil => simpa [eval] using hasDerivAt_const t (0 : ℝ)
  | cons s p ih =>
    simp only [eval_cons, List.map_cons, List.sum_cons]
    exact ((hasDerivAt_evalMono s.2 hX).const_mul (s.1 : ℝ)).add ih

/-- Normalize by an exponent rewrite `f` (re-sorting and merging). -/
@[expose] def normWith (f : List ℕ → List ℕ) (p : Poly) : Poly :=
  p.foldr (fun t acc => addP [(t.1, f t.2)] acc) []

theorem eval_normWith (f : List ℕ → List ℕ) (p : Poly) (x : ℕ → ℝ)
    (hf : ∀ e, evalMono (f e) x = evalMono e x) : eval (normWith f p) x = eval p x := by
  induction p with
  | nil => simp [normWith]
  | cons t p ih =>
    simp only [normWith, List.foldr_cons] at ih ⊢
    rw [eval_addP, ih]; simp [hf]

/-! ### Rational balls -/

/-- A rational ball `{x : |x − c| ≤ r}`. -/
structure QBall where
  /-- centre -/
  c : ℚ
  /-- radius -/
  r : ℚ

/-- Membership of a real number in a rational ball. -/
@[expose] def QBall.Mem (b : QBall) (x : ℝ) : Prop := |x - b.c| ≤ b.r

/-- Ball product. -/
@[expose] def mulQ (a b : QBall) : QBall := ⟨a.c * b.c, |a.c| * b.r + |b.c| * a.r + a.r * b.r⟩

theorem mem_mul_aux {x y ac bc ar br : ℝ} (hx : |x - ac| ≤ ar) (hy : |y - bc| ≤ br) :
    |x * y - ac * bc| ≤ |ac| * br + |bc| * ar + ar * br := by
  have ha : 0 ≤ ar := (abs_nonneg _).trans hx
  have e : x * y - ac * bc = (x - ac) * (y - bc) + ac * (y - bc) + bc * (x - ac) := by ring
  rw [e]
  calc _ ≤ |(x - ac) * (y - bc)| + |ac * (y - bc)| + |bc * (x - ac)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _ ≤ ar * br + |ac| * br + |bc| * ar := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

theorem QBall.mem_mul {a b : QBall} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (mulQ a b).Mem (x * y) := by
  unfold QBall.Mem mulQ at *
  push_cast
  exact mem_mul_aux hx hy

/-- Ball power. -/
@[expose] def powQ (a : QBall) : ℕ → QBall
  | 0 => ⟨1, 0⟩
  | n + 1 => mulQ (powQ a n) a

theorem QBall.mem_pow {a : QBall} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (powQ a n).Mem (x ^ n) := by
  induction n with
  | zero => simp [QBall.Mem, powQ]
  | succ n ih => rw [pow_succ]; exact QBall.mem_mul ih hx

/-- Ball enclosure of a monomial (balls listed by variable; missing balls are `{0}`). -/
@[expose] def monoQ : List ℕ → List QBall → QBall
  | [], _ => ⟨1, 0⟩
  | k :: e, bs => mulQ (powQ (bs.headD ⟨0, 0⟩) k) (monoQ e bs.tail)

theorem QBall.mem_mono (e : List ℕ) {bs : List QBall} {x : ℕ → ℝ}
    (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) : (monoQ e bs).Mem (evalMono e x) := by
  induction e generalizing bs x with
  | nil => simp [QBall.Mem, monoQ, evalMono]
  | cons k e ih =>
    refine QBall.mem_mul (QBall.mem_pow ?_ k) (ih fun i => ?_)
    · have := hx 0; cases bs <;> simpa using this
    · have := hx (i + 1); cases bs <;> simpa using this

/-- Ball enclosure of a polynomial. -/
@[expose] def evalQ (p : Poly) (bs : List QBall) : QBall :=
  p.foldr (fun t acc => let m := mulQ ⟨t.1, 0⟩ (monoQ t.2 bs); ⟨m.c + acc.c, m.r + acc.r⟩) ⟨0, 0⟩

theorem QBall.mem_eval (p : Poly) {bs : List QBall} {x : ℕ → ℝ}
    (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) : (evalQ p bs).Mem (eval p x) := by
  induction p with
  | nil => simp [QBall.Mem, evalQ]
  | cons t p ih =>
    have hm : (mulQ ⟨t.1, 0⟩ (monoQ t.2 bs)).Mem ((t.1 : ℝ) * evalMono t.2 x) :=
      QBall.mem_mul (by simp [QBall.Mem]) (QBall.mem_mono t.2 hx)
    simp only [evalQ, List.foldr_cons] at ih ⊢
    unfold QBall.Mem at ih hm ⊢
    simp only [eval_cons]
    push_cast at ih hm ⊢
    calc _ = |((t.1 : ℝ) * evalMono t.2 x - ((mulQ ⟨t.1, 0⟩ (monoQ t.2 bs)).c : ℝ)) +
          (eval p x - ((evalQ p bs).c : ℝ))| := by simp only [evalQ]; ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hm (by simpa only [evalQ] using ih))

/-- A ball containing a real `x` with `|x| ≤ b`. -/
theorem QBall.mem_of_abs_le {x : ℝ} {b : ℚ} (h : |x| ≤ b) : (QBall.mk 0 b).Mem x := by
  simpa [QBall.Mem] using h

/-- The ball spanning `[lo, hi]`. -/
@[expose] def ivQ (lo hi : ℚ) : QBall := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

theorem QBall.mem_ivQ {x : ℝ} {lo hi : ℚ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    (ivQ lo hi).Mem x := by
  unfold QBall.Mem ivQ; push_cast
  rw [abs_le]; constructor <;> linarith

theorem QBall.le_of_mem {b : QBall} {x : ℝ} (h : b.Mem x) : |x| ≤ |(b.c : ℝ)| + b.r := by
  have := abs_sub_abs_le_abs_sub x b.c
  unfold QBall.Mem at h; linarith

theorem QBall.bounds_of_mem {b : QBall} {x : ℝ} (h : b.Mem x) :
    ((b.c - b.r : ℚ) : ℝ) ≤ x ∧ x ≤ ((b.c + b.r : ℚ) : ℝ) := by
  unfold QBall.Mem at h; rw [abs_le] at h; push_cast; constructor <;> linarith

/-! ### Fixed-point balls -/

/-- Fixed-point scale `D = 2⁶⁴`. -/
@[expose] def Dk : ℕ := 2 ^ 64

theorem Dk_pos : (0 : ℝ) < Dk := by unfold Dk; positivity

/-- A fixed-point ball `{x : |x − c/D| ≤ r/D}` with integer centre and natural radius. -/
structure FBall where
  /-- scaled centre -/
  c : ℤ
  /-- scaled radius -/
  r : ℕ

/-- Decidable equality of fixed-point balls (explicit, so that the kernel can unfold it when
equations between literal ball polynomials are checked by `decide +kernel` in other modules). -/
instance : DecidableEq FBall := fun a b =>
  if h : a.c = b.c ∧ a.r = b.r then isTrue (by cases a; cases b; simp_all)
  else isFalse (by rintro rfl; exact h ⟨rfl, rfl⟩)

/-- Membership in a fixed-point ball. -/
@[expose] def FBall.Mem (b : FBall) (x : ℝ) : Prop := |x - b.c / Dk| ≤ b.r / Dk

/-- Fixed-point ball product with outward rounding (`ℤ`/`ℕ` arithmetic only). -/
@[expose] def mulF (a b : FBall) : FBall :=
  ⟨(a.c * b.c) / (Dk : ℤ), (a.c.natAbs * b.r + b.c.natAbs * a.r + a.r * b.r) / Dk + 2⟩

/-- Fixed-point ball sum. -/
@[expose] def addF (a b : FBall) : FBall := ⟨a.c + b.c, a.r + b.r⟩

theorem int_ediv_bounds (a : ℤ) : ((a / (Dk : ℤ) : ℤ) : ℝ) * Dk ≤ a ∧
    (a : ℝ) < ((a / (Dk : ℤ) : ℤ) + 1 : ℝ) * Dk := by
  have hD : (0 : ℤ) < Dk := by unfold Dk; positivity
  have h1 := Int.ediv_mul_le a hD.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hD
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

theorem cast_natAbs_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem FBall.mem_mul {a b : FBall} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (mulF a b).Mem (x * y) := by
  unfold FBall.Mem mulF at *
  have hD := Dk_pos
  have hm := mem_mul_aux hx hy
  set N : ℕ := a.c.natAbs * b.r + b.c.natAbs * a.r + a.r * b.r
  obtain ⟨c1, c2⟩ := int_ediv_bounds (a.c * b.c)
  have hDn : 0 < Dk := by unfold Dk; positivity
  have n2 : (N : ℝ) < ((N / Dk : ℕ) + 1 : ℝ) * Dk := by
    have := Nat.lt_div_mul_add (a := N) hDn
    have : (N : ℝ) < ((N / Dk * Dk + Dk : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  set C := a.c * b.c / (Dk : ℤ)
  set Q := N / Dk
  have hN : |(a.c : ℝ) / Dk| * (b.r / Dk) + |(b.c : ℝ) / Dk| * (a.r / Dk) +
      (a.r / Dk) * (b.r / Dk) = (N : ℝ) / Dk / Dk := by
    simp only [N]; push_cast
    rw [abs_div, abs_div, abs_of_pos hD, cast_natAbs_real, cast_natAbs_real]; field_simp
  rw [hN] at hm
  have hcen : |(a.c : ℝ) / Dk * (b.c / Dk) - C / Dk| ≤ 1 / Dk := by
    rw [abs_le]
    have e : (a.c : ℝ) / Dk * (b.c / Dk) - C / Dk = ((a.c : ℝ) * b.c - C * Dk) / Dk / Dk := by
      field_simp
    rw [e]
    push_cast at c1 c2
    have hu0 : 0 ≤ (a.c : ℝ) * b.c - C * Dk := by linarith
    have hu1 : (a.c : ℝ) * b.c - C * Dk ≤ Dk := by linarith
    constructor
    · have := div_nonneg (div_nonneg hu0 hD.le) hD.le
      have : 0 ≤ 1 / (Dk : ℝ) := by positivity
      linarith
    · rw [div_le_div_iff_of_pos_right hD, div_le_one hD]; exact hu1
  have hrad : (N : ℝ) / Dk / Dk ≤ (Q + 1) / Dk := by
    rw [div_le_div_iff_of_pos_right hD, div_le_iff₀ hD]
    exact n2.le
  calc |x * y - C / Dk| ≤ |x * y - a.c / Dk * (b.c / Dk)| +
        |(a.c : ℝ) / Dk * (b.c / Dk) - C / Dk| := abs_sub_le _ _ _
    _ ≤ (Q + 1) / Dk + 1 / Dk := add_le_add (hm.trans hrad) hcen
    _ = ((Q + 2 : ℕ) : ℝ) / Dk := by push_cast; ring

theorem FBall.mem_add {a b : FBall} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (addF a b).Mem (x + y) := by
  unfold FBall.Mem addF at *
  push_cast
  calc _ = |(x - a.c / Dk) + (y - b.c / Dk)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by rw [add_div]; exact add_le_add hx hy)

/-- The unit ball `{1}`. -/
@[expose] def oneF : FBall := ⟨Dk, 0⟩

theorem FBall.mem_one : oneF.Mem 1 := by
  simp [FBall.Mem, oneF, Dk_pos.ne']

/-- Fixed-point ball power. -/
@[expose] def powF (a : FBall) : ℕ → FBall
  | 0 => oneF
  | n + 1 => mulF (powF a n) a

theorem FBall.mem_pow {a : FBall} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (powF a n).Mem (x ^ n) := by
  induction n with
  | zero => simpa [powF] using FBall.mem_one
  | succ n ih => rw [pow_succ]; exact FBall.mem_mul ih hx

/-- Precomputed powers `b⁰, …, b⁸` of a ball. -/
@[expose] def powTable (b : FBall) : List FBall := (List.range 9).map (powF b)

theorem powTable_getD (b : FBall) (k : ℕ) : (powTable b).getD k (powF b k) = powF b k := by
  unfold powTable
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge k 9 with h | h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

/-- Fixed-point enclosure of a monomial using power tables (zero exponents are skipped). -/
@[expose] def monoT : List ℕ → List FBall → List (List FBall) → FBall
  | [], _, _ => oneF
  | 0 :: e, bs, ts => monoT e bs.tail ts.tail
  | (k + 1) :: e, bs, ts =>
    mulF ((ts.headD []).getD (k + 1) (powF (bs.headD ⟨0, 0⟩) (k + 1))) (monoT e bs.tail ts.tail)

theorem FBall.mem_monoT (e : List ℕ) {bs : List FBall} {x : ℕ → ℝ}
    (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) :
    (monoT e bs (bs.map powTable)).Mem (evalMono e x) := by
  induction e generalizing bs x with
  | nil => simpa [monoT, evalMono] using FBall.mem_one
  | cons k e ih =>
    have htail : ∀ i, (bs.tail.getD i ⟨0, 0⟩).Mem (x (i + 1)) := fun i => by
      have := hx (i + 1); cases bs <;> simpa using this
    have h0 : (bs.headD ⟨0, 0⟩).Mem (x 0) := by have := hx 0; cases bs <;> simpa using this
    rcases k with _ | k
    · simp only [monoT, evalMono, pow_zero, one_mul, ← List.map_tail]
      exact ih htail
    · simp only [monoT, evalMono, ← List.map_tail]
      refine FBall.mem_mul ?_ (ih htail)
      have hhead : ((bs.map powTable).headD []).getD (k + 1) (powF (bs.headD ⟨0, 0⟩) (k + 1)) =
          powF (bs.headD ⟨0, 0⟩) (k + 1) := by
        cases bs with
        | nil => simp
        | cons b bs => simpa using powTable_getD b (k + 1)
      rw [hhead]
      exact FBall.mem_pow h0 _

/-- A fixed-point polynomial: integer coefficients `K` standing for the balls `K/D ± 1/D`. -/
abbrev FPoly := List (ℤ × List ℕ)

/-- Fixed-point enclosure of a polynomial (power tables computed once). -/
@[expose] def evalT (p : FPoly) (bs : List FBall) : FBall :=
  p.foldr (fun t acc => addF (mulF ⟨t.1, 1⟩ (monoT t.2 bs (bs.map powTable))) acc) ⟨0, 0⟩

/-- Rounding of a rational polynomial scaled by `1/s` to fixed point. -/
@[expose] def toFix (s : ℚ) (p : Poly) : FPoly := p.map fun t => (⌊t.1 / s * Dk⌋, t.2)

theorem FBall.mem_coeff (c : ℚ) : (FBall.mk ⌊c * Dk⌋ 1).Mem c := by
  unfold FBall.Mem
  have hD := Dk_pos
  have h1 := Int.floor_le (c * (Dk : ℚ))
  have h2 := Int.lt_floor_add_one (c * (Dk : ℚ))
  have h1' : ((⌊c * (Dk : ℚ)⌋ : ℤ) : ℝ) ≤ (c : ℝ) * Dk := by exact_mod_cast h1
  have h2' : (c : ℝ) * Dk < ((⌊c * (Dk : ℚ)⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast h2
  have e : (c : ℝ) - ((⌊c * (Dk : ℚ)⌋ : ℤ) : ℝ) / Dk =
      ((c : ℝ) * Dk - ((⌊c * (Dk : ℚ)⌋ : ℤ) : ℝ)) / Dk := by field_simp
  push_cast at e ⊢
  rw [e, abs_le]
  constructor
  · have : 0 ≤ ((c : ℝ) * Dk - ((⌊c * (Dk : ℚ)⌋ : ℤ) : ℝ)) / Dk :=
      div_nonneg (by linarith) hD.le
    have : 0 ≤ 1 / (Dk : ℝ) := by positivity
    linarith
  · rw [div_le_div_iff_of_pos_right hD]; linarith

/-- **Soundness of the fixed-point enclosure**: if every variable lies in its ball, the
value `p(x)/s` lies in `evalT (toFix s p)`. -/
theorem FBall.mem_evalT_toFix (s : ℚ) (hs : s ≠ 0) (p : Poly) {bs : List FBall} {x : ℕ → ℝ}
    (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) :
    (evalT (toFix s p) bs).Mem (eval p x / s) := by
  induction p with
  | nil => simp [FBall.Mem, evalT, toFix]
  | cons t p ih =>
    simp only [toFix, List.map_cons, evalT, List.foldr_cons] at ih ⊢
    have hc := FBall.mem_coeff (t.1 / s)
    have := FBall.mem_add (FBall.mem_mul hc (FBall.mem_monoT t.2 hx)) ih
    convert this using 1
    simp only [eval_cons]; push_cast
    field_simp

/-- Absolute bound from a ball: `|x| ≤ A` when `|c| + r ≤ A D`. -/
theorem FBall.abs_le_of_mem {b : FBall} {x : ℝ} {A : ℕ} (h : b.Mem x)
    (hA : b.c.natAbs + b.r ≤ A * Dk) : |x| ≤ A := by
  unfold FBall.Mem at h
  have hD := Dk_pos
  have h1 := abs_sub_abs_le_abs_sub x (b.c / Dk)
  have h2 : ((b.c.natAbs + b.r : ℕ) : ℝ) ≤ ((A * Dk : ℕ) : ℝ) := by exact_mod_cast hA
  push_cast at h2
  rw [cast_natAbs_real] at h2
  rw [abs_div, abs_of_pos hD] at h1
  have : |(b.c : ℝ)| / Dk + b.r / Dk ≤ A := by
    rw [← add_div, div_le_iff₀ hD]; linarith
  linarith

/-- Conversion of a rational ball to a fixed-point ball (outward). -/
@[expose] def ofQ (b : QBall) : FBall := ⟨⌊b.c * Dk⌋, (⌈b.r * Dk⌉).toNat + 1⟩

theorem FBall.mem_ofQ {b : QBall} {x : ℝ} (h : b.Mem x) : (ofQ b).Mem x := by
  unfold FBall.Mem ofQ
  unfold QBall.Mem at h
  have hD := Dk_pos
  have hc := FBall.mem_coeff b.c
  unfold FBall.Mem at hc
  have h3 := Int.le_ceil (b.r * (Dk : ℚ))
  have h3' : (b.r : ℝ) * Dk ≤ ((⌈b.r * (Dk : ℚ)⌉ : ℤ) : ℝ) := by exact_mod_cast h3
  have h4 : ((⌈b.r * (Dk : ℚ)⌉ : ℤ) : ℝ) ≤ (((⌈b.r * (Dk : ℚ)⌉).toNat : ℕ) : ℝ) := by
    have := Int.self_le_toNat ⌈b.r * (Dk : ℚ)⌉
    exact_mod_cast this
  have hc' : |(b.c : ℝ) - ((⌊b.c * (Dk : ℚ)⌋ : ℤ) : ℝ) / Dk| ≤ 1 / Dk := by simpa using hc
  have hr : (b.r : ℝ) ≤ (((⌈b.r * (Dk : ℚ)⌉).toNat : ℕ) : ℝ) / Dk := by
    rw [le_div_iff₀ hD]; linarith
  calc |x - ((⌊b.c * (Dk : ℚ)⌋ : ℤ) : ℝ) / Dk| ≤
        |x - b.c| + |(b.c : ℝ) - ((⌊b.c * (Dk : ℚ)⌋ : ℤ) : ℝ) / Dk| := abs_sub_le _ _ _
    _ ≤ b.r + 1 / Dk := add_le_add h hc'
    _ ≤ _ := by push_cast; rw [add_div]; linarith

/-! ### Two-stage enclosures (ball-coefficient polynomials)

On a cover only a few variables change from cell to cell. `stage1` encloses, once and for all,
the part of every monomial in the remaining variables (by global balls) and merges monomials
with the same exponents in the cell variables, giving a polynomial `∑ bᵢ xᵉⁱ` with **ball
coefficients** (`BPoly`); `evalB` then encloses it on a cell. `BPoly.Holds` is the semantics. -/

/-- A polynomial with fixed-point ball coefficients. -/
abbrev BPoly := List (FBall × List ℕ)

/-- `v` is a value of the ball polynomial at `x`: `v = ∑ yᵢ xᵉⁱ` for some `yᵢ ∈ bᵢ`. -/
@[expose] def BPoly.Holds : BPoly → ℝ → (ℕ → ℝ) → Prop
  | [], v, _ => v = 0
  | (b, e) :: bp, v, x => ∃ y, b.Mem y ∧ BPoly.Holds bp (v - y * evalMono e x) x

/-- Fixed-point enclosure of a ball polynomial on a box. -/
@[expose] def evalB (bp : BPoly) (bs : List FBall) : FBall :=
  bp.foldr (fun t acc => addF (mulF t.1 (monoT t.2 bs (bs.map powTable))) acc) ⟨0, 0⟩

/-- **Soundness of `evalB`**: a value of the ball polynomial at a point of the box lies in
the enclosure. -/
theorem FBall.mem_evalB (bp : BPoly) {bs : List FBall} {x : ℕ → ℝ}
    (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) {v : ℝ} (h : bp.Holds v x) :
    (evalB bp bs).Mem v := by
  induction bp generalizing v with
  | nil =>
    simp only [BPoly.Holds] at h
    subst h; simp [FBall.Mem, evalB]
  | cons t bp ih =>
    obtain ⟨b, e⟩ := t
    obtain ⟨y, hy, hrest⟩ := h
    have := FBall.mem_add (FBall.mem_mul hy (FBall.mem_monoT e hx)) (ih hrest)
    simp only [evalB, List.foldr_cons] at this ⊢
    convert this using 1
    ring

/-- Exponent equality as a structural Boolean test (cheap in the kernel). -/
@[expose] def eqE : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: e, b :: f => Nat.beq a b && eqE e f
  | _, _ => false

/-- `eqE` is sound for equality. -/
theorem eq_of_eqE {e f : List ℕ} (h : eqE e f = true) : e = f := by
  induction e generalizing f with
  | nil => cases f <;> simp_all [eqE]
  | cons a e ih =>
    cases f with
    | nil => simp [eqE] at h
    | cons b f =>
      simp only [eqE, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, ih h.2]

/-- Add the term `b xᵉ` to a ball polynomial (merging with an equal exponent). -/
@[expose] def insertB (b : FBall) (e : List ℕ) : BPoly → BPoly
  | [] => [(b, e)]
  | (b', e') :: bp => if eqE e' e then (addF b' b, e') :: bp else (b', e') :: insertB b e bp

/-- Rewriting the value in `BPoly.Holds`. -/
theorem BPoly.holds_congr {bp : BPoly} {v w : ℝ} {x : ℕ → ℝ} (h : bp.Holds v x) (hvw : v = w) :
    bp.Holds w x := hvw ▸ h

/-- Inserting the term `b xᵉ` adds `y xᵉ` (with `y ∈ b`) to the value. -/
theorem BPoly.holds_insertB (b : FBall) (e : List ℕ) {bp : BPoly} {v y : ℝ} {x : ℕ → ℝ}
    (h : bp.Holds v x) (hy : b.Mem y) : (insertB b e bp).Holds (v + y * evalMono e x) x := by
  induction bp generalizing v with
  | nil =>
    simp only [BPoly.Holds] at h
    exact ⟨y, hy, by simp only [BPoly.Holds]; rw [h]; ring⟩
  | cons t bp ih =>
    obtain ⟨b', e'⟩ := t
    obtain ⟨y', hy', hrest⟩ := h
    simp only [insertB]
    split_ifs with he
    · rw [eq_of_eqE he] at hrest ⊢
      exact ⟨y' + y, FBall.mem_add hy' hy, BPoly.holds_congr hrest (by ring)⟩
    · exact ⟨y', hy', BPoly.holds_congr (ih hrest) (by ring)⟩

/-- The exponents of the cell variables (`mask = true`); later positions are kept. -/
@[expose] def keepE : List Bool → List ℕ → List ℕ
  | _, [] => []
  | [], e => e
  | b :: m, k :: e => (if b then k else 0) :: keepE m e

/-- The exponents of the remaining variables (`mask = false`). -/
@[expose] def dropE : List Bool → List ℕ → List ℕ
  | _, [] => []
  | [], _ => []
  | b :: m, k :: e => (if b then 0 else k) :: dropE m e

/-- A monomial splits into its non-cell and cell parts. -/
theorem evalMono_keep_drop (m : List Bool) (e : List ℕ) (x : ℕ → ℝ) :
    evalMono e x = evalMono (dropE m e) x * evalMono (keepE m e) x := by
  induction e generalizing m x with
  | nil => cases m <;> simp [keepE, dropE, evalMono]
  | cons k e ih =>
    cases m with
    | nil => simp [keepE, dropE, evalMono]
    | cons b m =>
      simp only [keepE, dropE, evalMono]
      rw [ih m]
      cases b <;> simp <;> ring

/-- Stage one: enclose the non-cell part of every monomial of `p/s` (given in fixed point)
by the balls `bs` and merge monomials with equal cell exponents. -/
@[expose] def stage1 (m : List Bool) (p : FPoly) (bs : List FBall) : BPoly :=
  p.foldr (fun t acc =>
    insertB (mulF ⟨t.1, 1⟩ (monoT (dropE m t.2) bs (bs.map powTable))) (keepE m t.2) acc) []

/-- **Soundness of `stage1`**: if every variable lies in its ball of `bs`, then `p(x)/s` is a
value of the ball polynomial `stage1 m (toFix s p) bs`. -/
theorem BPoly.holds_stage1 (m : List Bool) (s : ℚ) (hs : s ≠ 0) (p : Poly) {bs : List FBall}
    {x : ℕ → ℝ} (hx : ∀ i, (bs.getD i ⟨0, 0⟩).Mem (x i)) :
    (stage1 m (toFix s p) bs).Holds (eval p x / s) x := by
  induction p with
  | nil => simp [stage1, toFix, BPoly.Holds]
  | cons t p ih =>
    simp only [toFix, List.map_cons, stage1, List.foldr_cons] at ih ⊢
    have hc := FBall.mem_coeff (t.1 / s)
    have hy := FBall.mem_mul hc (FBall.mem_monoT (dropE m t.2) hx)
    refine BPoly.holds_congr (BPoly.holds_insertB _ (keepE m t.2) ih hy) ?_
    rw [eval_cons, evalMono_keep_drop m t.2 x]
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    ring

/-! ### Literal ball polynomials

`bpoly% "c r e₀ … eₙ; …"` and `fpoly% "c e₀ … eₙ; …"` elaborate (by a `meta` parser, outside
the trusted kernel) to literal `BPoly`/`FPoly` values, one entry per `;`-separated item. Large
literals are produced this way because elaborating long list literals of numerals directly is
slow; they are always related to computed values by a kernel-checked equation. -/

/-- Parse a `;`-separated list of rows of whitespace-separated integers. -/
meta def parseRows (s : String) : Except String (List (List Int)) :=
  ((s.replace "\n" " ").splitOn ";").filterMap (fun item =>
      match (item.splitOn " ").filter (· ≠ "") with
      | [] => none
      | toks => some toks) |>.mapM fun toks => toks.mapM fun t => match t.toInt? with
    | some k => pure k
    | none => throw s!"bad integer {t}"

/-- Natural-number exponents of a parsed row. -/
meta def rowExps (es : List Int) : Except String (List Nat) :=
  es.mapM fun e => if 0 ≤ e then pure e.toNat else throw s!"negative exponent {e}"

open Lean Elab Term Meta in
/-- Literal ball polynomial: `bpoly% "c r e₀ … eₙ; …"` is `[(⟨c, r⟩, [e₀, …, eₙ]), …]`. -/
elab "bpoly% " s:str : term => do
  let rows ← match parseRows s.getString with
    | .ok rows => pure rows
    | .error err => throwError "bpoly%: {err}"
  let fb := Lean.mkConst ``FBall
  let le := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Nat)
  let ty := mkApp2 (Lean.mkConst ``Prod [0, 0]) fb le
  let elems ← rows.mapM fun row => do
    match row with
    | c :: r :: es =>
      let some es := (rowExps es).toOption | throwError "bpoly%: bad exponents {es}"
      unless 0 ≤ r do throwError "bpoly%: negative radius {r}"
      return mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) fb le
        (mkApp2 (Lean.mkConst ``FBall.mk) (toExpr c) (toExpr r.toNat)) (toExpr es)
    | _ => throwError "bpoly%: bad row {row}"
  mkListLit ty elems

open Lean Elab Term Meta in
/-- Literal fixed-point polynomial: `fpoly% "c e₀ … eₙ; …"` is `[(c, [e₀, …, eₙ]), …]`. -/
elab "fpoly% " s:str : term => do
  let rows ← match parseRows s.getString with
    | .ok rows => pure rows
    | .error err => throwError "fpoly%: {err}"
  let elems ← rows.mapM fun row => do
    match row with
    | c :: es =>
      let some es := (rowExps es).toOption | throwError "fpoly%: bad exponents {es}"
      return toExpr (c, es)
    | _ => throwError "fpoly%: bad row {row}"
  mkListLit (toTypeExpr (Int × List Nat)) elems

/-! ### Fixtures -/

/-- Accepted fixture: `L(x₀²) = 2 x₀` along `ẋ₀ = 1`. -/
theorem lie_square_fixture : lie [(1, [2])] [[(1, [])]] = [(2, [1])] := by decide +kernel

/-- Accepted fixture: like terms cancel exactly. -/
theorem addP_cancel_fixture : addP [(1, [1])] [(-1, [1])] = [] := by decide +kernel

/-- Rejected fixture: distinct monomials do not merge. -/
theorem addP_distinct_fixture : addP [(1, [1])] [(1, [2])] ≠ [(2, [1])] := by decide +kernel

/-- Accepted fixture: `stage1` merges `x₀ x₁` and `x₀ x₁²` into one cell monomial `x₀` with
ball coefficient `x₁ + x₁²` (mask: `x₀` is the cell variable). -/
theorem stage1_merge_fixture :
    (stage1 [true, false] [(1, [1, 1]), (1, [1, 2])] [oneF, oneF]).length = 1 := by decide +kernel

/-- Rejected fixture: distinct cell exponents are not merged. -/
theorem stage1_distinct_fixture :
    (stage1 [true, false] [(1, [1, 1]), (1, [2, 1])] [oneF, oneF]).length ≠ 1 := by decide +kernel

/-- The `bpoly%` parser produces the expected literal. -/
theorem bpoly_fixture : (bpoly% "3 1 0 2; -5 0 1" : BPoly) = [(⟨3, 1⟩, [0, 2]), (⟨-5, 0⟩, [1])] :=
  rfl

/-- The `fpoly%` parser produces the expected literal. -/
theorem fpoly_fixture : (fpoly% "3 0 2; -5 1" : FPoly) = [(3, [0, 2]), (-5, [1])] := rfl

/-- Special case of the chain rule: `d/dt t² = 2t`, obtained from `hasDerivAt_eval`. -/
theorem hasDerivAt_sq_via_lie (t : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * t) t := by
  have h := hasDerivAt_eval [(1, [2])] [[(1, [])]] (X := fun r i => if i = 0 then r else 0)
    (t := t) (fun i => by
      rcases i with _ | i
      · simpa [eval, evalMono] using hasDerivAt_id' t
      · simpa using hasDerivAt_const t (0 : ℝ))
  rw [lie_square_fixture] at h
  simpa [eval, evalMono] using h

end PlasmaLean.Kinetic.LiePoly
