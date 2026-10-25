/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.PolyExprSMajQ

/-!
# Kernel-computable majorants with one rational bound per inverse-square-root node

`Theory/KAM/PolyExprSMajQ` mirrors the majorants `maj`, `majD`, `majD2` of `Theory/KAM/PolyExprS`
over `ℚ`, evaluating **every** node through one uniform bound `g`. When one node sits inside the
argument of another (the guiding-centre node `(1 − λ|B|)^{−1/2}`, where `|B|` contains the nodes
`(1 + E)^{−1/2}` and `(1 + E₄)^{−1/2}`), a uniform bound must satisfy a fixed-point condition
(`g² (1 − λ m g²) ≥ 1`), which has no solution once `4 λ m > 1`, although each node separately is
harmless. This file removes the uniform bound:

* `PQG σ`: trees with rational constants whose nodes `isqrt c g d` carry their own rational bound
  `g` of `(c − t)^{−1/2}`; the embedding `PQG.toS : PQG σ → PolyExprS ℂ σ` forgets the bounds;
* `PQG.mQ`, `PQG.mDQ`, `PQG.mD2Q`: the majorants over `ℚ`, each node evaluated through its bound;
* `PQG.NodesOK`: every node is valid and its bound dominates `isqG c (maj a d)`;
* **`PQG.maj_le`, `PQG.majD_le`, `PQG.majD2_le`**: the real majorants of `toS e` are bounded by the
  rational ones;
* **`PQG.nodesOK_of_okQ`**: the node conditions follow from a computable check `PQG.okQ`
  (`mQ a d < c`, `0 ≤ g`, `1 ≤ g² (c − mQ a d)` at every node, inner nodes first), so that
  `decide +kernel` proves them;
* `PQG.ofPQS`: attaches bounds to a `PQS` tree (a lookup table by node argument, with a default),
  with `PQG.toS_ofPQS` (the embedding is unchanged), so that existing `PQS` mirrors are reused.

**Sanity.** `mQ_fixture` (a node with bound `2`), `okQ_fixture` (the check accepts
`(1 + (−3/4))^{−1/2} ≤ 2`) and `okQ_reject` (it rejects the bound `1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Theory.KAM

/-- Polynomial expressions with rational constants and inverse-square-root nodes `isqrt c g d`
`= (c + d)^{−1/2}`, each node carrying a rational bound `g` of its majorant. -/
inductive PQG (σ : Type*) where
  /-- A rational constant. -/
  | const (q : ℚ)
  /-- A variable. -/
  | var (i : σ)
  /-- Sum. -/
  | add (p q : PQG σ)
  /-- Difference. -/
  | sub (p q : PQG σ)
  /-- Product. -/
  | mul (p q : PQG σ)
  /-- The node `(c + d)^{−1/2}` with the bound `g` of its majorant. -/
  | isqrt (c g : ℚ) (d : PQG σ)

namespace PQG

variable {σ : Type*}

/-- The embedding into `PolyExprS ℂ σ` (the node bounds are forgotten). -/
def toS : PQG σ → PolyExprS ℂ σ
  | const q => .const (q : ℂ)
  | var i => .var i
  | add p q => .add (toS p) (toS q)
  | sub p q => .sub (toS p) (toS q)
  | mul p q => .mul (toS p) (toS q)
  | isqrt c _ d => .isqrt (c : ℝ) (toS d)

/-- The rational majorant (each node evaluated as its bound). -/
def mQ (a : σ → ℚ) : PQG σ → ℚ
  | const q => |q|
  | var i => a i
  | add p q => mQ a p + mQ a q
  | sub p q => mQ a p + mQ a q
  | mul p q => mQ a p * mQ a q
  | isqrt _ g _ => g

/-- The rational first-derivative majorant. -/
def mDQ (a b : σ → ℚ) : PQG σ → ℚ
  | const _ => 0
  | var i => b i
  | add p q => mDQ a b p + mDQ a b q
  | sub p q => mDQ a b p + mDQ a b q
  | mul p q => mDQ a b p * mQ a q + mQ a p * mDQ a b q
  | isqrt _ g d => g ^ 3 / 2 * mDQ a b d

/-- The rational second-derivative majorant. -/
def mD2Q (a b : σ → ℚ) : PQG σ → ℚ
  | const _ => 0
  | var _ => 0
  | add p q => mD2Q a b p + mD2Q a b q
  | sub p q => mD2Q a b p + mD2Q a b q
  | mul p q => mD2Q a b p * mQ a q + 2 * (mDQ a b p * mDQ a b q) + mQ a p * mD2Q a b q
  | isqrt _ g d => 3 * g ^ 5 / 4 * mDQ a b d ^ 2 + g ^ 3 / 2 * mD2Q a b d

/-- Every node `isqrt c g d` is valid at `a` with `isqG c (maj a d) ≤ g`. -/
def NodesOK (a : σ → ℝ) : PQG σ → Prop
  | const _ => True
  | var _ => True
  | add p q => NodesOK a p ∧ NodesOK a q
  | sub p q => NodesOK a p ∧ NodesOK a q
  | mul p q => NodesOK a p ∧ NodesOK a q
  | isqrt c g d => PolyExprS.maj a (toS d) < c ∧ isqG c (PolyExprS.maj a (toS d)) ≤ g ∧
      NodesOK a d

/-- `NodesOK` implies validity of the embedded tree. -/
theorem valid_of_nodesOK {a : σ → ℝ} : ∀ {e : PQG σ}, NodesOK a e → PolyExprS.Valid a (toS e)
  | const _, _ => trivial
  | var _, _ => trivial
  | add _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | sub _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | mul _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | isqrt _ _ _, h => ⟨valid_of_nodesOK h.2.2, h.1⟩

variable {a b : σ → ℚ}

/-- Rational majorants are nonnegative under the node conditions (each bound dominates
`isqG ≥ 0`). -/
theorem mQ_nonneg (ha : ∀ i, 0 ≤ a i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e → 0 ≤ mQ a e
  | const q, _ => abs_nonneg q
  | var i, _ => ha i
  | add p q, h => add_nonneg (mQ_nonneg ha p h.1) (mQ_nonneg ha q h.2)
  | sub p q, h => add_nonneg (mQ_nonneg ha p h.1) (mQ_nonneg ha q h.2)
  | mul p q, h => mul_nonneg (mQ_nonneg ha p h.1) (mQ_nonneg ha q h.2)
  | isqrt c g d, h => by
    have : (0 : ℝ) ≤ g := (isqG_nonneg _ _).trans h.2.1
    simp only [mQ]; exact_mod_cast this

/-- **The real majorant is at most the rational one.** -/
theorem maj_le (ha : ∀ i, 0 ≤ a i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e →
      PolyExprS.maj (fun i => (a i : ℝ)) (toS e) ≤ (mQ a e : ℝ)
  | const q, _ => by simp only [toS, PolyExprS.maj, mQ, PQS.norm_ratCast, le_refl]
  | var i, _ => le_rfl
  | add p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_add]
    exact add_le_add (maj_le ha p h.1) (maj_le ha q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_add]
    exact add_le_add (maj_le ha p h.1) (maj_le ha q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_mul]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    exact mul_le_mul (maj_le ha p h.1) (maj_le ha q h.2)
      (PolyExprS.maj_nonneg ha' _) (by exact_mod_cast mQ_nonneg ha p h.1)
  | isqrt c g d, h => by simpa [toS, PolyExprS.maj, mQ] using h.2.1

/-- First-derivative majorants are nonnegative under the node conditions. -/
theorem mDQ_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e → 0 ≤ mDQ a b e
  | const _, _ => le_rfl
  | var i, _ => hb i
  | add p q, h => add_nonneg (mDQ_nonneg ha hb p h.1) (mDQ_nonneg ha hb q h.2)
  | sub p q, h => add_nonneg (mDQ_nonneg ha hb p h.1) (mDQ_nonneg ha hb q h.2)
  | mul p q, h => add_nonneg (mul_nonneg (mDQ_nonneg ha hb p h.1) (mQ_nonneg ha q h.2))
      (mul_nonneg (mQ_nonneg ha p h.1) (mDQ_nonneg ha hb q h.2))
  | isqrt c g d, h => by
    have h0 : (0 : ℝ) ≤ g := (isqG_nonneg _ _).trans h.2.1
    have h0' : (0 : ℚ) ≤ g := by exact_mod_cast h0
    simp only [mDQ]
    exact mul_nonneg (by positivity) (mDQ_nonneg ha hb d h.2.2)

/-- **The real first-derivative majorant is at most the rational one.** -/
theorem majD_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e →
      PolyExprS.majD (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) (toS e) ≤ (mDQ a b e : ℝ)
  | const q, _ => by simp [toS, PolyExprS.majD, mDQ]
  | var i, _ => le_rfl
  | add p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add]
    exact add_le_add (majD_le ha hb p h.1) (majD_le ha hb q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add]
    exact add_le_add (majD_le ha hb p h.1) (majD_le ha hb q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add, Rat.cast_mul]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    refine add_le_add (mul_le_mul (majD_le ha hb p h.1) (maj_le ha q h.2)
      (PolyExprS.maj_nonneg ha' _) (by exact_mod_cast mDQ_nonneg ha hb p h.1))
      (mul_le_mul (maj_le ha p h.1) (majD_le ha hb q h.2)
      (PolyExprS.majD_nonneg ha' hb' _) (by exact_mod_cast mQ_nonneg ha p h.1))
  | isqrt c g d, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have h1 := h.2.1
    have h0 := isqG_nonneg (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d))
    have h3 : isqG (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d)) ^ 3 ≤ (g : ℝ) ^ 3 :=
      pow_le_pow_left₀ h0 h1 3
    have h4 := majD_le ha hb d h.2.2
    have h5 := PolyExprS.majD_nonneg ha' hb' (toS d)
    have h6 : (0 : ℝ) ≤ g := h0.trans h1
    gcongr

/-- Second-derivative majorants are nonnegative under the node conditions. -/
theorem mD2Q_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e → 0 ≤ mD2Q a b e
  | const _, _ => le_rfl
  | var _, _ => le_rfl
  | add p q, h => add_nonneg (mD2Q_nonneg ha hb p h.1) (mD2Q_nonneg ha hb q h.2)
  | sub p q, h => add_nonneg (mD2Q_nonneg ha hb p h.1) (mD2Q_nonneg ha hb q h.2)
  | mul p q, h => by
    have := mD2Q_nonneg ha hb p h.1; have := mD2Q_nonneg ha hb q h.2
    have := mDQ_nonneg ha hb p h.1; have := mDQ_nonneg ha hb q h.2
    have := mQ_nonneg ha p h.1; have := mQ_nonneg ha q h.2
    simp only [mD2Q]; positivity
  | isqrt c g d, h => by
    have h0 : (0 : ℝ) ≤ g := (isqG_nonneg _ _).trans h.2.1
    have h0' : (0 : ℚ) ≤ g := by exact_mod_cast h0
    have := mD2Q_nonneg ha hb d h.2.2; have := mDQ_nonneg ha hb d h.2.2
    simp only [mD2Q]; positivity

/-- **The real second-derivative majorant is at most the rational one.** -/
theorem majD2_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ e : PQG σ, NodesOK (fun i => (a i : ℝ)) e →
      PolyExprS.majD2 (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) (toS e) ≤ (mD2Q a b e : ℝ)
  | const q, _ => by simp [toS, PolyExprS.majD2, mD2Q]
  | var i, _ => by simp [toS, PolyExprS.majD2, mD2Q]
  | add p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add]
    exact add_le_add (majD2_le ha hb p h.1) (majD2_le ha hb q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add]
    exact add_le_add (majD2_le ha hb p h.1) (majD2_le ha hb q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have e1 := majD2_le ha hb p h.1
    have e2 := majD2_le ha hb q h.2
    have f1 := maj_le ha p h.1
    have f2 := maj_le ha q h.2
    have d1 := majD_le ha hb p h.1
    have d2 := majD_le ha hb q h.2
    have n1 := PolyExprS.maj_nonneg ha' (toS p)
    have n2 := PolyExprS.maj_nonneg ha' (toS q)
    have n3 := PolyExprS.majD_nonneg ha' hb' (toS p)
    have n4 := PolyExprS.majD_nonneg ha' hb' (toS q)
    have n5 := PolyExprS.majD2_nonneg ha' hb' (toS p)
    have n6 := PolyExprS.majD2_nonneg ha' hb' (toS q)
    have m1 : (0 : ℝ) ≤ mD2Q a b p := by exact_mod_cast mD2Q_nonneg ha hb p h.1
    have m2 : (0 : ℝ) ≤ mQ a p := by exact_mod_cast mQ_nonneg ha p h.1
    have m3 : (0 : ℝ) ≤ mDQ a b p := by exact_mod_cast mDQ_nonneg ha hb p h.1
    gcongr
  | isqrt c g d, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have h1 := h.2.1
    have h0 := isqG_nonneg (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d))
    have d1 := majD_le ha hb d h.2.2
    have e1 := majD2_le ha hb d h.2.2
    have n3 := PolyExprS.majD_nonneg ha' hb' (toS d)
    have n5 := PolyExprS.majD2_nonneg ha' hb' (toS d)
    have h6 : (0 : ℝ) ≤ g := h0.trans h1
    gcongr

/-! ## The computable node check -/

/-- The computable node check: at every node `isqrt c g d` (inner nodes first),
`mQ a d < c`, `0 ≤ g` and `1 ≤ g² (c − mQ a d)`. -/
def okQ (a : σ → ℚ) : PQG σ → Bool
  | const _ => true
  | var _ => true
  | add p q => okQ a p && okQ a q
  | sub p q => okQ a p && okQ a q
  | mul p q => okQ a p && okQ a q
  | isqrt c g d => okQ a d && decide (mQ a d < c) && decide (0 ≤ g) &&
      decide (1 ≤ g ^ 2 * (c - mQ a d))

/-- `isqG c t ≤ g` from a bound `t ≤ m < c` and `1 ≤ g² (c − m)`, `0 ≤ g`. -/
theorem isqG_le_of {c m g t : ℝ} (ht : t ≤ m) (hm : m < c) (hg0 : 0 ≤ g)
    (hg : 1 ≤ g ^ 2 * (c - m)) : isqG c t ≤ g := by
  refine (isqG_mono ht hm).trans ?_
  unfold isqG
  have h1 : 0 < c - m := by linarith
  have hs : 0 < Real.sqrt (c - m) := Real.sqrt_pos.2 h1
  have hgp : 0 < g := by
    rcases hg0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hg; norm_num at hg
  rw [inv_le_comm₀ hs hgp, Real.le_sqrt (by positivity) h1.le, inv_pow,
    inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- **The node conditions from the computable check.** -/
theorem nodesOK_of_okQ (ha : ∀ i, 0 ≤ a i) :
    ∀ e : PQG σ, okQ a e = true → NodesOK (fun i => (a i : ℝ)) e
  | const _, _ => trivial
  | var _, _ => trivial
  | add p q, h => by
    simp only [okQ, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_okQ ha p h.1, nodesOK_of_okQ ha q h.2⟩
  | sub p q, h => by
    simp only [okQ, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_okQ ha p h.1, nodesOK_of_okQ ha q h.2⟩
  | mul p q, h => by
    simp only [okQ, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_okQ ha p h.1, nodesOK_of_okQ ha q h.2⟩
  | isqrt c g d, h => by
    simp only [okQ, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hd, hc⟩, hg0⟩, hg⟩ := h
    have hN := nodesOK_of_okQ ha d hd
    have hm := maj_le ha d hN
    have hc' : (mQ a d : ℝ) < c := by exact_mod_cast hc
    have hg0' : (0 : ℝ) ≤ g := by exact_mod_cast hg0
    have hg' : (1 : ℝ) ≤ (g : ℝ) ^ 2 * ((c : ℝ) - mQ a d) := by exact_mod_cast hg
    exact ⟨hm.trans_lt hc', isqG_le_of hm hc' hg0' hg', hN⟩

/-! ## Attaching bounds to `PQS` trees -/

/-- The bound of a node with argument `d`: the first entry of the table whose argument is `d`,
else the default `g₀`. -/
def lookupG [DecidableEq σ] : List (PQS σ × ℚ) → ℚ → PQS σ → ℚ
  | [], g₀, _ => g₀
  | p :: gs, g₀, d => if p.1 = d then p.2 else lookupG gs g₀ d

/-- A `PQS` tree with node bounds attached by the table `gs` (default `g₀`). -/
def ofPQS [DecidableEq σ] (gs : List (PQS σ × ℚ)) (g₀ : ℚ) : PQS σ → PQG σ
  | .const q => const q
  | .var i => var i
  | .add p q => add (ofPQS gs g₀ p) (ofPQS gs g₀ q)
  | .sub p q => sub (ofPQS gs g₀ p) (ofPQS gs g₀ q)
  | .mul p q => mul (ofPQS gs g₀ p) (ofPQS gs g₀ q)
  | .isqrt c d => isqrt c (lookupG gs g₀ d) (ofPQS gs g₀ d)

/-- **Attaching bounds does not change the embedded tree.** -/
theorem toS_ofPQS [DecidableEq σ] (gs : List (PQS σ × ℚ)) (g₀ : ℚ) :
    ∀ e : PQS σ, toS (ofPQS gs g₀ e) = e.toS
  | .const _ => rfl
  | .var _ => rfl
  | .add p q => by simp only [ofPQS, toS, PQS.toS, toS_ofPQS gs g₀ p, toS_ofPQS gs g₀ q]
  | .sub p q => by simp only [ofPQS, toS, PQS.toS, toS_ofPQS gs g₀ p, toS_ofPQS gs g₀ q]
  | .mul p q => by simp only [ofPQS, toS, PQS.toS, toS_ofPQS gs g₀ p, toS_ofPQS gs g₀ q]
  | .isqrt c d => by simp only [ofPQS, toS, PQS.toS, toS_ofPQS gs g₀ d]

/-! ## Sanity -/

/-- **Sanity** (accepted fixture): a node with bound `2` has majorant `2`, so `3 · node` has `6`. -/
theorem mQ_fixture :
    mQ (fun _ : Unit => (1 / 2 : ℚ)) (mul (const 3) (isqrt 1 2 (var ()))) = 6 := by
  norm_num [mQ]

/-- **Sanity** (accepted fixture): the check accepts `(1 + d)^{−1/2} ≤ 2` for `|d| ≤ 3/4`. -/
theorem okQ_fixture : okQ (fun _ : Unit => (3 / 4 : ℚ)) (isqrt 1 2 (var ())) = true := by
  norm_num [okQ, mQ]

/-- **Sanity** (rejected fixture): the bound `1` is rejected (`(1 − 3/4)^{−1/2} = 2 > 1`). -/
theorem okQ_reject : okQ (fun _ : Unit => (3 / 4 : ℚ)) (isqrt 1 1 (var ())) = false := by
  norm_num [okQ, mQ]

end PQG

end PlasmaLean.Theory.KAM
