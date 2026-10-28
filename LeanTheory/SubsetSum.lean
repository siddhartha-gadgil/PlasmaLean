/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public meta import Lean
public meta import Qq
import Mathlib.Data.List.Basic


/-!
# Subset-sum certificates (proof-construction pattern)

Reference example for building large proofs as explicit proof terms rather than by `decide`:
an inductive certificate predicate `HasSubsetSum`, a computable `subsetSum` characterized by
`fun_induction`/`grind`, and `meta` builders that assemble the proof term from a witness.
See the skill `.claude/skills/lean-proofs`. Not part of the physics library.
-/

public section

open Lean Meta Elab Term Tactic Qq
namespace ConcLean
namespace SubsetSum

inductive HasSubsetSum : List Int → Int → Prop where
  | nil : HasSubsetSum [] 0
  | skip (x : Int) (xs : List Int) (s : Int) : -- `x` is explicit to allow building proofs.
      HasSubsetSum xs s → HasSubsetSum (x :: xs) s
  | take (x : Int) (xs : List Int) (s : Int) :
      HasSubsetSum xs s → HasSubsetSum (x :: xs) (x + s)

example : HasSubsetSum [1, 2, 3] 5 := by
    apply HasSubsetSum.skip 1
    apply HasSubsetSum.take 2 (s := 3)
    apply HasSubsetSum.take 3 (s := 0)
    apply HasSubsetSum.nil

-- We can prove a theorem that characterizes the `HasSubsetSum` relation.

def subsetSum (l : List Int) (indices : List Nat) : Int :=
    match l with
    | [] => 0
    | a :: bs =>
        if indices.contains 0 then
            a + subsetSum bs (indices.filterMap (fun i => match i with
                | i' + 1 => some i'
                | 0 => none))
        else
            subsetSum bs (indices.filterMap (fun i => match i with
                | i' + 1 => some i'
                | 0 => none))

private meta def computeSubsetSum (l : List Int) (indices : List Nat) : Int :=
  match l with
  | [] => 0
  | a :: bs =>
      let shifted := indices.filterMap fun i => match i with
        | i' + 1 => some i'
        | 0 => none
      if indices.contains 0 then a + computeSubsetSum bs shifted
      else computeSubsetSum bs shifted

def findSubsetSumIndices? (l : List Int) (s : Int) : Option (List Nat) :=
    match l with
    | [] => if s = 0 then some [] else none
    | a :: bs =>
        match findSubsetSumIndices? bs s with
        | some indices => some (indices.map (fun i => i + 1))
        | none =>
            match findSubsetSumIndices? bs (s - a) with
            | some indices => some (0 :: indices.map (fun i => i + 1))
            | none => none

theorem subsetSum_correct (l : List Int) (indices : List Nat) :
    HasSubsetSum l (subsetSum l indices) := by
    fun_induction subsetSum
    · apply HasSubsetSum.nil
    · rename_i indices' a bs h₁ h₂
      apply HasSubsetSum.take a
      assumption
    · rename_i indices' a bs h₁ h₂
      apply HasSubsetSum.skip a
      assumption

theorem exists_indices_for_subset_sum {l : List Int} {s : Int} :
    HasSubsetSum l s → ∃ indices : List Nat, subsetSum l indices = s := by
    intro h
    induction h with
    | nil =>
        use []
        simp [subsetSum]
    | skip x xs s h₁ ih =>
        match ih with
        | ⟨indices, ih'⟩ =>
            use indices.map (fun i => i + 1)
            grind [subsetSum]
    | take x xs s h₁ ih =>
        match ih with
        | ⟨indices, ih'⟩ =>
            use 0 :: indices.map (fun i => i + 1)
            grind [subsetSum]

meta def mkHasSubsetSumProof (l : List Int) (indices : List Nat) : MetaM Expr := do
    match l with
    | [] => do
        let nilProof := Lean.mkConst ``HasSubsetSum.nil
        return nilProof
    | a :: bs => do
        let shiftedIndices := indices.filterMap (fun i => match i with
            | i' + 1 => some i'
            | 0 => none)
        let tailSum := computeSubsetSum bs shiftedIndices
        let subProof ← mkHasSubsetSumProof bs shiftedIndices
        if indices.contains 0 then
            let takeProof ←
                mkAppM ``HasSubsetSum.take #[toExpr a, toExpr bs, toExpr tailSum,  subProof]
            return takeProof
        else
            let skipProof ←
              mkAppM ``HasSubsetSum.skip #[toExpr a, toExpr bs, toExpr tailSum, subProof]
            return skipProof

meta def mkExistsIndicesForSubsetSumProof (l : List Int) (indices : List Nat) : MetaM Expr := do
    let hasSubsetSumProof ← mkHasSubsetSumProof l indices
    mkAppM ``exists_indices_for_subset_sum #[hasSubsetSumProof]


end SubsetSum
end ConcLean
