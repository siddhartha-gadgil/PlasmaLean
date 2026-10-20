/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.EReal.Basic
public meta import Lean
public meta import Qq

/-!
# Two-dimensional Lipschitz covers of parametrized surfaces

Extends the one-dimensional `ParametricBounds` to surface patches (track T1 technique
companion). A surface patch is a map `σ : ℝ → ℝ → E` on the parameter square
`[0,1]²` with a Lipschitz-type modulus

`‖σ s t - σ s' t'‖ ≤ A |s - s'| + B |t - t'|`.

If a function `g` on `E` is `L`-Lipschitz on the image (the field error, say) and
`‖g‖ ≤ m` at the `(N+1)(M+1)` grid points `σ (i/N) (j/M)`, then
`‖g‖ ≤ m + L (A/(2N) + B/(2M))` at **every** point of the patch, not only at the
samples.

Main results.
* `exists_near_grid`: every `s ∈ [0,1]` is within `1/(2N)` of a grid point `i/N`.
* `bound_of_cover`: abstract sample cover with Lipschitz interpolation.
* `le_of_grid`: the scalar two-parameter cover (a modulus in each parameter).
* `patch_cover`, `patch_norm_le_of_grid`: the surface version for `σ` and `g`.
* `GridBound`, `GridBound.sound`, `le_of_gridBound`, `patch_norm_le_of_gridBound`:
  a certificate predicate with one constructor step per grid sample, and its
  soundness. The tactic `grid_bound_cert` builds the proof term (SubsetSum pattern,
  see `.claude/skills/plasmalean-lean-proofs`); every sample inequality becomes a side
  goal, typically closed by `norm_num`.

Sanity fixtures (`Sanity` section below): an accepted 121-sample certificate for
`s(1-s) + t(1-t)`, a rejected certificate (bound below an attained sample), and the
degenerate one-cell grid.

Not covered: adaptive (non-uniform) refinement and branch-and-bound; samples are a
uniform grid. Lipschitz constants of the patch and of `g` are hypotheses.
-/

public section

namespace PlasmaLean.Geometry

/-! ### Nearest grid point -/

/-- **Nearest grid point.** Every `s ∈ [0,1]` lies within `1/(2N)` of some grid point
`i/N` with `i ≤ N` (round `sN` to the nearest integer). -/
theorem exists_near_grid {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {N : ℕ} (hN : 0 < N) :
    ∃ i : ℕ, i ≤ N ∧ |s - i / N| ≤ 1 / (2 * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ s * N + 1 / 2 := by positivity
  refine ⟨⌊s * N + 1 / 2⌋₊, ?_, ?_⟩
  · have hlt : (⌊s * N + 1 / 2⌋₊ : ℝ) < N + 1 := by
      have := Nat.floor_le hx
      nlinarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  · have h1 := Nat.floor_le hx
    have h2 := Nat.lt_floor_add_one (s * N + 1 / 2)
    generalize (⌊s * N + 1 / 2⌋₊ : ℝ) = k at h1 h2 ⊢
    have e : s - k / N = (s * N - k) / N := by field_simp
    have e' : 1 / (2 * (N : ℝ)) = (1 / 2) / N := by field_simp
    rw [e, e', abs_div, abs_of_pos hNr]
    apply div_le_div_of_nonneg_right _ hNr.le
    rw [abs_le]
    constructor <;> linarith

/-! ### Abstract cover -/

/-- **Sample cover with Lipschitz interpolation.** If every point of `S` is within `h`
of a sample point, `g` is `L`-Lipschitz between points of `S` and samples, and
`‖g‖ ≤ m` at every sample, then `‖g‖ ≤ m + L h` on all of `S`. -/
theorem bound_of_cover {E F ι : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (S : Set E) (p : ι → E) (g : E → F) {h L m : ℝ} (hL : 0 ≤ L)
    (cover : ∀ y ∈ S, ∃ i, ‖y - p i‖ ≤ h)
    (lip : ∀ y ∈ S, ∀ i, ‖g y - g (p i)‖ ≤ L * ‖y - p i‖)
    (samples : ∀ i, ‖g (p i)‖ ≤ m) : ∀ y ∈ S, ‖g y‖ ≤ m + L * h := by
  intro y hy
  obtain ⟨i, hi⟩ := cover y hy
  have h1 := norm_le_insert' (g y) (g (p i))
  have h2 := lip y hy i
  have h3 := mul_le_mul_of_nonneg_left hi hL
  have h4 := samples i
  linarith [norm_sub_rev (g y) (g (p i))]

/-! ### Scalar two-parameter cover -/

/-- **Two-parameter grid cover (scalar form).** Let `f` satisfy the one-sided modulus
`f s t ≤ f s' t' + K₁|s - s'| + K₂|t - t'|` on `[0,1]²`. If `f (i/N) (j/M) ≤ m` at all
grid points, then `f ≤ m + K₁/(2N) + K₂/(2M)` on the whole square. -/
theorem le_of_grid (f : ℝ → ℝ → ℝ) {K₁ K₂ m : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (modulus : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        f s t ≤ f s' t' + K₁ * |s - s'| + K₂ * |t - t'|)
    (samples : ∀ i ≤ N, ∀ j ≤ M, f (i / N) (j / M) ≤ m) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f s t ≤ m + K₁ / (2 * N) + K₂ / (2 * M) := by
  intro s hs t ht
  obtain ⟨i, hi, his⟩ := exists_near_grid hs.1 hs.2 hN
  obtain ⟨j, hj, hjt⟩ := exists_near_grid ht.1 ht.2 hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hiI : (i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNr).2 (by exact_mod_cast hi)⟩
  have hjI : (j : ℝ) / M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hMr).2 (by exact_mod_cast hj)⟩
  have h := modulus s hs t ht _ hiI _ hjI
  have e1 := mul_le_mul_of_nonneg_left his hK₁
  have e2 := mul_le_mul_of_nonneg_left hjt hK₂
  have hs' := samples i hi j hj
  have r1 : K₁ * (1 / (2 * N)) = K₁ / (2 * N) := by ring
  have r2 : K₂ * (1 / (2 * M)) = K₂ / (2 * M) := by ring
  linarith

/-! ### Surface patches -/

/-- **Patch cover.** A patch `σ` with modulus `A|s-s'| + B|t-t'|` on `[0,1]²` is covered by
its grid samples `σ (i/N) (j/M)` with radius `A/(2N) + B/(2M)`. -/
theorem patch_cover {E : Type*} [SeminormedAddCommGroup E] (σ : ℝ → ℝ → E) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hσ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ‖σ s t - σ s' t'‖ ≤ A * |s - s'| + B * |t - t'|)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i ≤ N, ∃ j ≤ M, (i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 ∧ (j : ℝ) / M ∈ Set.Icc (0 : ℝ) 1 ∧
      ‖σ s t - σ (i / N) (j / M)‖ ≤ A / (2 * N) + B / (2 * M) := by
  obtain ⟨i, hi, his⟩ := exists_near_grid hs.1 hs.2 hN
  obtain ⟨j, hj, hjt⟩ := exists_near_grid ht.1 ht.2 hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hiI : (i : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNr).2 (by exact_mod_cast hi)⟩
  have hjI : (j : ℝ) / M ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hMr).2 (by exact_mod_cast hj)⟩
  refine ⟨i, hi, j, hj, hiI, hjI, ?_⟩
  have h := hσ s hs t ht _ hiI _ hjI
  have e1 := mul_le_mul_of_nonneg_left his hA
  have e2 := mul_le_mul_of_nonneg_left hjt hB
  have r1 : A * (1 / (2 * N)) = A / (2 * N) := by ring
  have r2 : B * (1 / (2 * M)) = B / (2 * M) := by ring
  linarith

/-- **Surface supremum from grid samples.** For a patch `σ` with modulus
`A|s-s'| + B|t-t'|` and a function `g` that is `L`-Lipschitz on the patch image, the
bounds `‖g (σ (i/N) (j/M))‖ ≤ m` at the grid samples give
`‖g (σ s t)‖ ≤ m + L (A/(2N) + B/(2M))` for every `(s,t) ∈ [0,1]²`. -/
theorem patch_norm_le_of_grid {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (σ : ℝ → ℝ → E) (g : E → F) {A B L m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hσ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ‖σ s t - σ s' t'‖ ≤ A * |s - s'| + B * |t - t'|)
    (lip : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ‖g (σ s t) - g (σ s' t')‖ ≤ L * ‖σ s t - σ s' t'‖)
    (samples : ∀ i ≤ N, ∀ j ≤ M, ‖g (σ (i / N) (j / M))‖ ≤ m) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖g (σ s t)‖ ≤ m + L * (A / (2 * N) + B / (2 * M)) := by
  intro s hs t ht
  obtain ⟨i, hi, j, hj, hiI, hjI, hc⟩ := patch_cover σ hA hB hN hM hσ hs ht
  have h1 := norm_le_insert' (g (σ s t)) (g (σ (i / N) (j / M)))
  have h2 := lip s hs t ht _ hiI _ hjI
  have h3 := mul_le_mul_of_nonneg_left hc hL
  have h4 := samples i hi j hj
  linarith [norm_sub_rev (g (σ s t)) (g (σ (i / N) (j / M)))]

/-! ### Certificate predicate and checker -/

/-- The list of all grid indices `(i, j)` with `i ≤ N`, `j ≤ M`. -/
@[expose] def gridIndices (N M : ℕ) : List (ℕ × ℕ) :=
  (List.range (N + 1)).flatMap fun i => (List.range (M + 1)).map fun j => (i, j)

/-- Membership in `gridIndices`. -/
theorem mem_gridIndices {N M i j : ℕ} : (i, j) ∈ gridIndices N M ↔ i ≤ N ∧ j ≤ M := by
  simp [gridIndices, List.mem_flatMap]

/-- **Grid-sample certificate.** `GridBound f N M m l` records, one constructor step per
index `(i, j) ∈ l`, that `f (i/N) (j/M) ≤ m`. The arguments are explicit so that the
proof term can be assembled by `grid_bound_cert`. -/
inductive GridBound (f : ℝ → ℝ → ℝ) (N M : ℕ) (m : ℝ) : List (ℕ × ℕ) → Prop where
  /-- The empty list of samples. -/
  | nil : GridBound f N M m []
  /-- One checked sample, followed by the rest of the certificate. -/
  | cons (i j : ℕ) (l : List (ℕ × ℕ)) :
      f ((i : ℝ) / N) ((j : ℝ) / M) ≤ m → GridBound f N M m l → GridBound f N M m ((i, j) :: l)

/-- Every listed sample of a `GridBound` certificate satisfies the bound. -/
theorem GridBound.mem {f : ℝ → ℝ → ℝ} {N M : ℕ} {m : ℝ} {l : List (ℕ × ℕ)}
    (h : GridBound f N M m l) : ∀ p ∈ l, f ((p.1 : ℝ) / N) ((p.2 : ℝ) / M) ≤ m := by
  induction h <;> grind

/-- **Soundness of the full-grid certificate**: all samples `f (i/N) (j/M)`, `i ≤ N`,
`j ≤ M`, are at most `m`. -/
theorem GridBound.sound {f : ℝ → ℝ → ℝ} {N M : ℕ} {m : ℝ}
    (h : GridBound f N M m (gridIndices N M)) :
    ∀ i ≤ N, ∀ j ≤ M, f ((i : ℝ) / N) ((j : ℝ) / M) ≤ m := fun i hi j hj =>
  h.mem (i, j) (mem_gridIndices.2 ⟨hi, hj⟩)

/-- **Semantic soundness (scalar).** A full-grid certificate and a modulus in each
parameter bound `f` on the whole square `[0,1]²`. -/
theorem le_of_gridBound (f : ℝ → ℝ → ℝ) {K₁ K₂ m : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (modulus : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        f s t ≤ f s' t' + K₁ * |s - s'| + K₂ * |t - t'|)
    (cert : GridBound f N M m (gridIndices N M)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f s t ≤ m + K₁ / (2 * N) + K₂ / (2 * M) :=
  le_of_grid f hK₁ hK₂ hN hM modulus cert.sound

/-- **Semantic soundness (surface).** A full-grid certificate for `‖g ∘ σ‖` on a patch
gives the bound `m + L (A/(2N) + B/(2M))` on the whole patch. -/
theorem patch_norm_le_of_gridBound {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (σ : ℝ → ℝ → E) (g : E → F) {A B L m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hσ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ‖σ s t - σ s' t'‖ ≤ A * |s - s'| + B * |t - t'|)
    (lip : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ‖g (σ s t) - g (σ s' t')‖ ≤ L * ‖σ s t - σ s' t'‖)
    (cert : GridBound (fun s t => ‖g (σ s t)‖) N M m (gridIndices N M)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖g (σ s t)‖ ≤ m + L * (A / (2 * N) + B / (2 * M)) :=
  patch_norm_le_of_grid σ g hA hB hL hN hM hσ lip cert.sound

section Checker
open Lean Meta Elab Tactic Qq

/-- Build the `GridBound` proof term for the index list `l`; each sample inequality
becomes a fresh goal. Untrusted: the kernel checks the produced term. -/
meta def mkGridBound (f N M m : Expr) : List (ℕ × ℕ) → MetaM (Expr × List MVarId)
  | [] => return (← mkAppOptM ``GridBound.nil #[f, N, M, m], [])
  | (i, j) :: l => do
    let pc ← mkAppOptM ``GridBound.cons #[f, N, M, m, toExpr i, toExpr j, toExpr l]
    let ty ← whnfR (← inferType pc)
    let .forallE _ dom _ _ := ty | throwError "grid_bound_cert: unexpected constructor type"
    let mv ← mkFreshExprMVar dom
    let (tl, gs) ← mkGridBound f N M m l
    return (mkApp2 pc mv tl, mv.mvarId! :: gs)

/-- `grid_bound_cert` proves a goal `GridBound f N M m l` (typically
`l = gridIndices N M`) by assembling the certificate term; the remaining goals are the
individual sample inequalities `f (i/N) (j/M) ≤ m`. -/
elab "grid_bound_cert" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr GridBound f N M m l := ty | throwError "grid_bound_cert: expected GridBound f N M m l"
  let lv ← unsafe evalExpr (List (ℕ × ℕ)) q(List (ℕ × ℕ)) l
  let (pf, gs) ← mkGridBound f N M m lv
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal gs

end Checker

/-! ### Sanity fixtures -/

namespace SurfaceCoverSanity

/-- Test function on the square: `s(1-s) + t(1-t)`, maximum `1/2` at `(1/2,1/2)`. -/
@[expose] def bump (s t : ℝ) : ℝ := s * (1 - s) + t * (1 - t)

/-- The bump has modulus `|s-s'| + |t-t'|` on the unit square. -/
theorem bump_modulus : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ s' ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      bump s t ≤ bump s' t' + 1 * |s - s'| + 1 * |t - t'| := by
  intro s hs t ht s' hs' t' ht'
  obtain ⟨hs0, hs1⟩ := hs; obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hs0', hs1'⟩ := hs'; obtain ⟨ht0', ht1'⟩ := ht'
  have e1 : s * (1 - s) - s' * (1 - s') = (s - s') * (1 - s - s') := by ring
  have e2 : t * (1 - t) - t' * (1 - t') = (t - t') * (1 - t - t') := by ring
  have a1 : (s - s') * (1 - s - s') ≤ |s - s'| := by
    calc _ ≤ |(s - s') * (1 - s - s')| := le_abs_self _
      _ = |s - s'| * |1 - s - s'| := abs_mul _ _
      _ ≤ |s - s'| * 1 := by
          gcongr; rw [abs_le]; constructor <;> linarith
      _ = _ := mul_one _
  have a2 : (t - t') * (1 - t - t') ≤ |t - t'| := by
    calc _ ≤ |(t - t') * (1 - t - t')| := le_abs_self _
      _ = |t - t'| * |1 - t - t'| := abs_mul _ _
      _ ≤ |t - t'| * 1 := by
          gcongr; rw [abs_le]; constructor <;> linarith
      _ = _ := mul_one _
  simp only [bump]
  linarith

/-- **Accepted fixture**: a 121-sample certificate built by `grid_bound_cert`. -/
theorem bump_grid : GridBound bump 10 10 (1 / 2) (gridIndices 10 10) := by
  grid_bound_cert
  all_goals norm_num [bump]

/-- The certified continuous bound: `bump ≤ 1/2 + 1/20 + 1/20` on all of `[0,1]²`
(the true maximum is `1/2`). -/
theorem bump_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    bump s t ≤ 1 / 2 + 1 / 20 + 1 / 20 := by
  have h := le_of_gridBound bump zero_le_one zero_le_one (by norm_num : 0 < 10)
    (by norm_num : 0 < 10) bump_modulus bump_grid
  norm_num at h ⊢
  intro s hs0 hs1 t ht0 ht1
  have := h s hs0 hs1 t ht0 ht1
  linarith

/-- **Rejected fixture**: no certificate exists for the bound `2/5`, because the sample
at `(5/10, 5/10)` equals `1/2`. -/
theorem bump_grid_rejected : ¬ GridBound bump 10 10 (2 / 5) (gridIndices 10 10) := by
  intro h
  have := h.sound 5 (by norm_num) 5 (by norm_num)
  norm_num [bump] at this

/-- **Degenerate case**: the one-cell grid (`N = M = 1`, four corner samples) still
gives a valid, if crude, bound. -/
theorem bump_le_coarse : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    bump s t ≤ 0 + 1 / 2 + 1 / 2 := by
  have h := le_of_gridBound bump zero_le_one zero_le_one (N := 1) (M := 1) (m := 0)
    (by norm_num) (by norm_num) bump_modulus (by grid_bound_cert <;> norm_num [bump])
  norm_num at h ⊢
  intro s hs0 hs1 t ht0 ht1
  have := h s hs0 hs1 t ht0 ht1
  linarith

end SurfaceCoverSanity

end PlasmaLean.Geometry
