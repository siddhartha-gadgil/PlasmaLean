/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.KAM.PolyExprS

/-!
# Kernel-computable majorants of expressions with an inverse-square-root node

The majorants `maj`, `majD`, `majD2` of `Theory/KAM/PolyExprS` are real numbers; for large trees
(for example a deviation polynomial with hundreds of monomials under the node, repeated) their
evaluation by `norm_num` is slow. This file gives a computable mirror:

* `PQS σ`: trees with rational constants and rational node centres, with the embedding
  `PQS.toS : PQS σ → PolyExprS ℂ σ`;
* `PQS.mQ`, `PQS.mDQ`, `PQS.mD2Q`: the majorants over `ℚ`, with every node evaluated through
  a rational bound `g` of `(c − t)^{−1/2}`;
* `PQS.NodesOK`: every node of the tree is valid with `isqG c (maj a d) ≤ g`;
* **`PQS.maj_le`, `PQS.majD_le`, `PQS.majD2_le`**: the real majorants of `toS e` are bounded by the
  rational ones (the latter are computable and checked by kernel evaluation);
* `PQS.nodesOK_of_all`: if all nodes are the same node `isqrt 1 d₀` (`PQS.allNodes`, computable),
  one condition on `d₀` suffices; `PQS.valid_of_nodesOK`.

**Sanity.** `mQ_fixture`, `toS_npowQ` (powers are mirrored), `allNodes_const`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Theory.KAM

/-- Polynomial expressions with an inverse-square-root node and rational constants. -/
inductive PQS (σ : Type*) where
  /-- A rational constant. -/
  | const (q : ℚ)
  /-- A variable. -/
  | var (i : σ)
  /-- Sum. -/
  | add (p q : PQS σ)
  /-- Difference. -/
  | sub (p q : PQS σ)
  /-- Product. -/
  | mul (p q : PQS σ)
  /-- The node `(c + d)^{−1/2}`. -/
  | isqrt (c : ℚ) (d : PQS σ)
  deriving DecidableEq

namespace PQS

variable {σ : Type*}

/-- The embedding into `PolyExprS ℂ σ`. -/
def toS : PQS σ → PolyExprS ℂ σ
  | const q => .const (q : ℂ)
  | var i => .var i
  | add p q => .add (toS p) (toS q)
  | sub p q => .sub (toS p) (toS q)
  | mul p q => .mul (toS p) (toS q)
  | isqrt c d => .isqrt (c : ℝ) (toS d)

/-- Powers `(…(1·p)·p…)·p`. -/
def npowQ (p : PQS σ) : ℕ → PQS σ
  | 0 => const 1
  | k + 1 => mul (npowQ p k) p

/-- Powers are mirrored: `toS (npowQ p k) = ofPoly (npow p' k)` when `toS p = ofPoly p'`. -/
theorem toS_npowQ {p : PQS σ} {p' : PolyExpr ℂ σ} (h : toS p = PolyExprS.ofPoly p') :
    ∀ k : ℕ, toS (npowQ p k) = PolyExprS.ofPoly (PolyExpr.npow p' k)
  | 0 => by simp [npowQ, toS, PolyExpr.npow, PolyExprS.ofPoly]
  | k + 1 => by
    simp only [npowQ, toS, PolyExpr.npow, PolyExprS.ofPoly, toS_npowQ h k, h]

/-- The rational majorant (nodes evaluated as `g`). -/
def mQ (a : σ → ℚ) (g : ℚ) : PQS σ → ℚ
  | const q => |q|
  | var i => a i
  | add p q => mQ a g p + mQ a g q
  | sub p q => mQ a g p + mQ a g q
  | mul p q => mQ a g p * mQ a g q
  | isqrt _ _ => g

/-- The rational first-derivative majorant. -/
def mDQ (a b : σ → ℚ) (g : ℚ) : PQS σ → ℚ
  | const _ => 0
  | var i => b i
  | add p q => mDQ a b g p + mDQ a b g q
  | sub p q => mDQ a b g p + mDQ a b g q
  | mul p q => mDQ a b g p * mQ a g q + mQ a g p * mDQ a b g q
  | isqrt _ d => g ^ 3 / 2 * mDQ a b g d

/-- The rational second-derivative majorant. -/
def mD2Q (a b : σ → ℚ) (g : ℚ) : PQS σ → ℚ
  | const _ => 0
  | var _ => 0
  | add p q => mD2Q a b g p + mD2Q a b g q
  | sub p q => mD2Q a b g p + mD2Q a b g q
  | mul p q => mD2Q a b g p * mQ a g q + 2 * (mDQ a b g p * mDQ a b g q) +
      mQ a g p * mD2Q a b g q
  | isqrt _ d => 3 * g ^ 5 / 4 * mDQ a b g d ^ 2 + g ^ 3 / 2 * mD2Q a b g d

/-- Every node `isqrt c d` is valid at `a` with `isqG c (maj a d) ≤ g`. -/
def NodesOK (a : σ → ℝ) (g : ℝ) : PolyExprS ℂ σ → Prop
  | .const _ => True
  | .var _ => True
  | .add p q => NodesOK a g p ∧ NodesOK a g q
  | .sub p q => NodesOK a g p ∧ NodesOK a g q
  | .mul p q => NodesOK a g p ∧ NodesOK a g q
  | .isqrt c d => PolyExprS.maj a d < c ∧ isqG c (PolyExprS.maj a d) ≤ g ∧ NodesOK a g d

/-- `NodesOK` implies validity. -/
theorem valid_of_nodesOK {a : σ → ℝ} {g : ℝ} : ∀ {e : PolyExprS ℂ σ}, NodesOK a g e →
    PolyExprS.Valid a e
  | .const _, _ => trivial
  | .var _, _ => trivial
  | .add _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | .sub _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | .mul _ _, h => ⟨valid_of_nodesOK h.1, valid_of_nodesOK h.2⟩
  | .isqrt _ _, h => ⟨valid_of_nodesOK h.2.2, h.1⟩

variable {a b : σ → ℚ} {g : ℚ}

/-- The norm of a rational constant. -/
theorem norm_ratCast (q : ℚ) : ‖(q : ℂ)‖ = ((|q| : ℚ) : ℝ) := by
  rw [show ((q : ℚ) : ℂ) = (((q : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_eq_abs, Rat.cast_abs]

/-- Rational majorants are nonnegative. -/
theorem mQ_nonneg (ha : ∀ i, 0 ≤ a i) (hg : 0 ≤ g) : ∀ e : PQS σ, 0 ≤ mQ a g e
  | const q => abs_nonneg q
  | var i => ha i
  | add p q => add_nonneg (mQ_nonneg ha hg p) (mQ_nonneg ha hg q)
  | sub p q => add_nonneg (mQ_nonneg ha hg p) (mQ_nonneg ha hg q)
  | mul p q => mul_nonneg (mQ_nonneg ha hg p) (mQ_nonneg ha hg q)
  | isqrt _ _ => hg

/-- **The real majorant is at most the rational one.** -/
theorem maj_le (ha : ∀ i, 0 ≤ a i) (hg : 0 ≤ g) :
    ∀ e : PQS σ, NodesOK (fun i => (a i : ℝ)) g (toS e) →
      PolyExprS.maj (fun i => (a i : ℝ)) (toS e) ≤ (mQ a g e : ℝ)
  | const q, _ => by simp only [toS, PolyExprS.maj, mQ, norm_ratCast, le_refl]
  | var i, _ => le_rfl
  | add p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_add]
    exact add_le_add (maj_le ha hg p h.1) (maj_le ha hg q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_add]
    exact add_le_add (maj_le ha hg p h.1) (maj_le ha hg q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.maj, mQ, Rat.cast_mul]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    exact mul_le_mul (maj_le ha hg p h.1) (maj_le ha hg q h.2)
      (PolyExprS.maj_nonneg ha' _) (by exact_mod_cast mQ_nonneg ha hg p)
  | isqrt c d, h => by simpa [toS, PolyExprS.maj, mQ] using h.2.1

/-- First-derivative majorants are nonnegative. -/
theorem mDQ_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hg : 0 ≤ g) :
    ∀ e : PQS σ, 0 ≤ mDQ a b g e
  | const _ => le_rfl
  | var i => hb i
  | add p q => add_nonneg (mDQ_nonneg ha hb hg p) (mDQ_nonneg ha hb hg q)
  | sub p q => add_nonneg (mDQ_nonneg ha hb hg p) (mDQ_nonneg ha hb hg q)
  | mul p q => add_nonneg (mul_nonneg (mDQ_nonneg ha hb hg p) (mQ_nonneg ha hg q))
      (mul_nonneg (mQ_nonneg ha hg p) (mDQ_nonneg ha hb hg q))
  | isqrt _ d => mul_nonneg (by positivity) (mDQ_nonneg ha hb hg d)

/-- **The real first-derivative majorant is at most the rational one.** -/
theorem majD_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hg : 0 ≤ g) :
    ∀ e : PQS σ, NodesOK (fun i => (a i : ℝ)) g (toS e) →
      PolyExprS.majD (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) (toS e) ≤ (mDQ a b g e : ℝ)
  | const q, _ => by simp [toS, PolyExprS.majD, mDQ]
  | var i, _ => le_rfl
  | add p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add]
    exact add_le_add (majD_le ha hb hg p h.1) (majD_le ha hb hg q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add]
    exact add_le_add (majD_le ha hb hg p h.1) (majD_le ha hb hg q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_add, Rat.cast_mul]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    refine add_le_add (mul_le_mul (majD_le ha hb hg p h.1) (maj_le ha hg q h.2)
      (PolyExprS.maj_nonneg ha' _) (by exact_mod_cast mDQ_nonneg ha hb hg p))
      (mul_le_mul (maj_le ha hg p h.1) (majD_le ha hb hg q h.2)
      (PolyExprS.majD_nonneg ha' hb' _) (by exact_mod_cast mQ_nonneg ha hg p))
  | isqrt c d, h => by
    simp only [toS, PolyExprS.majD, mDQ, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have h1 := h.2.1
    have h0 := isqG_nonneg (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d))
    have h3 : isqG (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d)) ^ 3 ≤ (g : ℝ) ^ 3 :=
      pow_le_pow_left₀ h0 h1 3
    have h4 := majD_le ha hb hg d h.2.2
    have h5 := PolyExprS.majD_nonneg ha' hb' (toS d)
    have h6 : (0 : ℝ) ≤ g := by exact_mod_cast hg
    gcongr

/-- Second-derivative majorants are nonnegative. -/
theorem mD2Q_nonneg (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hg : 0 ≤ g) :
    ∀ e : PQS σ, 0 ≤ mD2Q a b g e
  | const _ => le_rfl
  | var _ => le_rfl
  | add p q => add_nonneg (mD2Q_nonneg ha hb hg p) (mD2Q_nonneg ha hb hg q)
  | sub p q => add_nonneg (mD2Q_nonneg ha hb hg p) (mD2Q_nonneg ha hb hg q)
  | mul p q => by
    have := mD2Q_nonneg ha hb hg p; have := mD2Q_nonneg ha hb hg q
    have := mDQ_nonneg ha hb hg p; have := mDQ_nonneg ha hb hg q
    have := mQ_nonneg ha hg p; have := mQ_nonneg ha hg q
    simp only [mD2Q]; positivity
  | isqrt _ d => by
    have := mD2Q_nonneg ha hb hg d; have := mDQ_nonneg ha hb hg d
    simp only [mD2Q]; positivity

/-- **The real second-derivative majorant is at most the rational one.** -/
theorem majD2_le (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hg : 0 ≤ g) :
    ∀ e : PQS σ, NodesOK (fun i => (a i : ℝ)) g (toS e) →
      PolyExprS.majD2 (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) (toS e) ≤ (mD2Q a b g e : ℝ)
  | const q, _ => by simp [toS, PolyExprS.majD2, mD2Q]
  | var i, _ => by simp [toS, PolyExprS.majD2, mD2Q]
  | add p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add]
    exact add_le_add (majD2_le ha hb hg p h.1) (majD2_le ha hb hg q h.2)
  | sub p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add]
    exact add_le_add (majD2_le ha hb hg p h.1) (majD2_le ha hb hg q h.2)
  | mul p q, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have e1 := majD2_le ha hb hg p h.1
    have e2 := majD2_le ha hb hg q h.2
    have f1 := maj_le ha hg p h.1
    have f2 := maj_le ha hg q h.2
    have d1 := majD_le ha hb hg p h.1
    have d2 := majD_le ha hb hg q h.2
    have n1 := PolyExprS.maj_nonneg ha' (toS p)
    have n2 := PolyExprS.maj_nonneg ha' (toS q)
    have n3 := PolyExprS.majD_nonneg ha' hb' (toS p)
    have n4 := PolyExprS.majD_nonneg ha' hb' (toS q)
    have n5 := PolyExprS.majD2_nonneg ha' hb' (toS p)
    have n6 := PolyExprS.majD2_nonneg ha' hb' (toS q)
    have m1 : (0 : ℝ) ≤ mD2Q a b g p := by exact_mod_cast mD2Q_nonneg ha hb hg p
    have m2 : (0 : ℝ) ≤ mQ a g p := by exact_mod_cast mQ_nonneg ha hg p
    have m3 : (0 : ℝ) ≤ mDQ a b g p := by exact_mod_cast mDQ_nonneg ha hb hg p
    gcongr
  | isqrt c d, h => by
    simp only [toS, PolyExprS.majD2, mD2Q, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat]
    have ha' : ∀ i, 0 ≤ (a i : ℝ) := fun i => by exact_mod_cast ha i
    have hb' : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
    have h1 := h.2.1
    have h0 := isqG_nonneg (c : ℝ) (PolyExprS.maj (fun i => (a i : ℝ)) (toS d))
    have d1 := majD_le ha hb hg d h.2.2
    have e1 := majD2_le ha hb hg d h.2.2
    have n3 := PolyExprS.majD_nonneg ha' hb' (toS d)
    have n5 := PolyExprS.majD2_nonneg ha' hb' (toS d)
    have h6 : (0 : ℝ) ≤ g := by exact_mod_cast hg
    gcongr

/-- All nodes of the tree are `isqrt 1 d₀` (computable). -/
def allNodes [DecidableEq σ] (d₀ : PQS σ) : PQS σ → Bool
  | const _ => true
  | var _ => true
  | add p q => allNodes d₀ p && allNodes d₀ q
  | sub p q => allNodes d₀ p && allNodes d₀ q
  | mul p q => allNodes d₀ p && allNodes d₀ q
  | isqrt c d => decide (c = 1) && decide (d = d₀)

/-- **Sanity**: constants have no nodes. -/
theorem allNodes_const [DecidableEq σ] (d₀ : PQS σ) (q : ℚ) : allNodes d₀ (const q) = true := rfl

/-- **One node condition suffices** when all nodes are `isqrt 1 d₀` (and `d₀` has no nodes). -/
theorem nodesOK_of_all [DecidableEq σ] {a : σ → ℝ} {g : ℝ} {d₀ : PQS σ}
    (h0 : NodesOK a g (toS d₀)) (hm : PolyExprS.maj a (toS d₀) < 1)
    (hg : isqG 1 (PolyExprS.maj a (toS d₀)) ≤ g) :
    ∀ e : PQS σ, allNodes d₀ e = true → NodesOK a g (toS e)
  | const _, _ => trivial
  | var _, _ => trivial
  | add p q, h => by
    simp only [allNodes, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_all h0 hm hg p h.1, nodesOK_of_all h0 hm hg q h.2⟩
  | sub p q, h => by
    simp only [allNodes, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_all h0 hm hg p h.1, nodesOK_of_all h0 hm hg q h.2⟩
  | mul p q, h => by
    simp only [allNodes, Bool.and_eq_true] at h
    exact ⟨nodesOK_of_all h0 hm hg p h.1, nodesOK_of_all h0 hm hg q h.2⟩
  | isqrt c d, h => by
    simp only [allNodes, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [toS, NodesOK, Rat.cast_one]
    exact ⟨hm, hg, h0⟩

/-- **Sanity** (accepted fixture): the majorant of `2x − 3` at `x ≤ 1/2` is `4`. -/
theorem mQ_fixture :
    mQ (fun _ : Unit => (1 / 2 : ℚ)) 0 (sub (mul (const 2) (var ())) (const 3)) = 4 := by
  norm_num [mQ]

end PQS

end LeanTheory.Theory.KAM
