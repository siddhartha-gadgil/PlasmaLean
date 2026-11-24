/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCompensatedAction

/-! # Seven angular harmonics with nested spatial Horner evaluation -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkHarmonicHorner
open DommaschkKam DommaschkKam.DkPoly

inductive Wave where
  | one | sin1 | cos1 | sin2 | cos2 | sin3 | cos3
  deriving Repr, Inhabited

/-- The angle is the fundamental doubled toroidal angle. -/
noncomputable def Wave.value : Wave → ℝ → ℝ
  | .one, _ => 1
  | .sin1, θ => Real.sin θ
  | .cos1, θ => Real.cos θ
  | .sin2, θ => Real.sin (2 * θ)
  | .cos2, θ => Real.cos (2 * θ)
  | .sin3, θ => Real.sin (3 * θ)
  | .cos3, θ => Real.cos (3 * θ)

def Wave.expand : Wave → SP
  | .one => [⟨1,0,0,0,0⟩]
  | .sin1 => [⟨1,0,0,0,1⟩]
  | .cos1 => [⟨1,0,0,1,0⟩]
  | .sin2 => [⟨2,0,0,1,1⟩]
  | .cos2 => [⟨-1,0,0,0,2⟩, ⟨1,0,0,2,0⟩]
  | .sin3 => [⟨-1,0,0,0,3⟩, ⟨3,0,0,2,1⟩]
  | .cos3 => [⟨-3,0,0,1,2⟩, ⟨1,0,0,3,0⟩]

theorem Wave.expand_sound (w : Wave) (u z θ : ℝ) :
    evR u z (Real.cos θ) (Real.sin θ) w.expand = w.value θ := by
  cases w <;> simp [Wave.expand, Wave.value, evR,
    show 2 * θ = θ + θ by ring, show 3 * θ = θ + θ + θ by ring,
    Real.sin_add, Real.cos_add] <;> ring

def horner {α : Type*} (zero : α) (step : α → α → α) : List α → α
  | [] => zero
  | q :: qs => qs.foldl step q

theorem map_horner {α β : Type*} (f : α → β) (a : α) (b : β)
    (p : α → α → α) (q : β → β → β) (h0 : f a = b)
    (h : ∀ x y, f (p x y) = q (f x) (f y)) (cs : List α) :
    f (horner a p cs) = horner b q (cs.map f) := by
  cases cs with
  | nil => exact h0
  | cons v vs =>
    change f (vs.foldl p v) = (vs.map f).foldl q (f v)
    induction vs generalizing v with
    | nil => rfl
    | cons w ws ih => simp only [List.foldl_cons, List.map_cons]; rw [ih, h]

abbrev Rows := List (List ℚ)
abbrev Channels := List (Wave × Rows)

def scalar (q : ℚ) : SP := if q == 0 then [] else [⟨q,0,0,0,0⟩]
def xvar : SP := [⟨1,1,0,0,0⟩]
def zvar : SP := [⟨1,0,1,0,0⟩]

def mulAdd (x acc q : SP) : SP := merge (mul x acc) q

def expandRow (qs : List ℚ) : SP := horner [] (mulAdd xvar) (qs.map scalar)
def expandRows (rs : Rows) : SP := horner [] (mulAdd zvar) (rs.map expandRow)
def expand : Channels → SP
  | [] => []
  | (w, rs) :: cs => merge (mul w.expand (expandRows rs)) (expand cs)

noncomputable def rowValue (u : ℝ) (qs : List ℚ) : ℝ :=
  horner 0 (fun a q => a*u+q) (qs.map fun q : ℚ => (q : ℝ))
noncomputable def rowsValue (u z : ℝ) (rs : Rows) : ℝ :=
  horner 0 (fun a q => a*z+q) (rs.map (rowValue u))
noncomputable def value (u z θ : ℝ) : Channels → ℝ
  | [] => 0
  | (w, rs) :: cs => rowsValue u z rs * w.value θ + value u z θ cs

theorem real_merge (u z c s : ℝ) (p q : SP) :
    evR u z c s (merge p q) = evR u z c s p + evR u z c s q := by
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_add, ← ev_ofReal, ev_merge]

theorem real_mul (u z c s : ℝ) (p q : SP) :
    evR u z c s (mul p q) = evR u z c s p * evR u z c s q := by
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_mul, ← ev_ofReal, ev_mul]

theorem scalar_sound (u z c s : ℝ) (q : ℚ) : evR u z c s (scalar q) = (q : ℝ) := by
  by_cases h : q = 0 <;> simp [scalar, h, evR]

theorem expandRow_sound (u z c s : ℝ) (qs : List ℚ) :
    evR u z c s (expandRow qs) = rowValue u qs := by
  unfold expandRow rowValue
  rw [map_horner (evR u z c s) [] 0 (mulAdd xvar) (fun a q : ℝ => a*u+q)
    (by simp [evR]) (by intro a b; rw [mulAdd, real_merge, real_mul,
      show evR u z c s xvar = u by simp [xvar, evR], mul_comm])]
  simp only [List.map_map, Function.comp_def, scalar_sound]

theorem expandRows_sound (u z c s : ℝ) (rs : Rows) :
    evR u z c s (expandRows rs) = rowsValue u z rs := by
  unfold expandRows rowsValue
  rw [map_horner (evR u z c s) [] 0 (mulAdd zvar) (fun a q : ℝ => a*z+q)
    (by simp [evR]) (by intro a b; rw [mulAdd, real_merge, real_mul,
      show evR u z c s zvar = z by simp [zvar, evR], mul_comm])]
  simp only [List.map_map, Function.comp_def, expandRow_sound]

/-- The same angle occurs in all harmonics and the same point in all spatial rows. -/
theorem expand_sound (u z θ : ℝ) (cs : Channels) :
    evR u z (Real.cos θ) (Real.sin θ) (expand cs) = value u z θ cs := by
  induction cs with
  | nil => simp [expand, value, evR]
  | cons ch cs ih =>
    obtain ⟨w, rs⟩ := ch
    simp only [expand, real_merge, real_mul, Wave.expand_sound, expandRows_sound, ih, value]
    ring

def sameTerms : SP → SP → Bool
  | [], [] => true
  | t :: p, v :: q => (t.q == v.q) && t.same v && sameTerms p q
  | _, _ => false

theorem sameTerms_sound {p q : SP} (h : sameTerms p q = true) : p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [sameTerms]
  | cons t p ih =>
    cases q with
    | nil => simp [sameTerms] at h
    | cons v q =>
      obtain ⟨⟨hc, he⟩, ht⟩ := (by simpa only [sameTerms, Bool.and_eq_true,
        beq_iff_eq] using h : (t.q = v.q ∧ t.same v = true) ∧ sameTerms p q = true)
      obtain ⟨ha,hb,hd,hf⟩ := Tm.same_eq he
      have hm : t = v := by cases t; cases v; grind
      rw [hm, ih ht]

end PlasmaLean.Design.DommaschkHarmonicHorner
