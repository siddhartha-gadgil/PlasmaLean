/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialTiles
public import PlasmaLean.Design.DommaschkActionQ0R470
public import PlasmaLean.Design.DommaschkActionQ0R478
public import PlasmaLean.Design.DommaschkActionQ0R523
public import PlasmaLean.Design.DommaschkActionQ0R531
public import PlasmaLean.Design.DommaschkActionQ1R456
public import PlasmaLean.Design.DommaschkActionQ1R464
public import PlasmaLean.Design.DommaschkActionQ1R509
public import PlasmaLean.Design.DommaschkActionQ1R517

/-!
# Assembly of the Dommaschk local action graph certificates

One trace supplies the field strength and arclength density for both heights.
The numerical proofs check both endpoint quadratures and all the radial secants.
The remaining hypotheses specify pointwise bounds on that trace and its derivatives.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkLocalMirrorGraphs

open Set Certificates.RadialTile Certificates.MirrorActionQuadrature DommaschkRadialTiles
open Kinetic.MirrorHeightAction

/-- Coordinate values and trace length for one root bracket. -/
structure Bracket where
  left : ℝ
  right : ℝ
  height : ℝ
  slope : ℝ
  tiles : List Piece

/-- The four brackets use the same two heights on both symmetry sectors. -/
def bracket : Bool → Bool → Bracket
  | false, false => ⟨523/1000,531/1000,low,s0h0Slope,s0h0⟩
  | false, true  => ⟨47/100,239/500,high,s0h1Slope,s0h1⟩
  | true, false  => ⟨509/1000,517/1000,low,s1h0Slope,s1h0⟩
  | true, true   => ⟨57/125,58/125,high,s1h1Slope,s1h1⟩

/-- The angular step count for the negative and positive halves of each endpoint run. -/
def steps : Bool → Bool → Bool → ℕ
  | false, false, true  => 324
  | false, false, false => 325
  | false, true, true   => 325
  | false, true, false  => 327
  | true, false, true   => 327
  | true, false, false  => 328
  | true, true, true    => 328
  | true, true, false   => 329

/-- At the left endpoint an upper bound is needed; at the right a lower bound. -/
def panels : (q h upper : Bool) → List (Block upper)
  | false, false, true  => DommaschkActionQ0R523.slabs
  | false, false, false => DommaschkActionQ0R531.slabs
  | false, true, true   => DommaschkActionQ0R470.slabs
  | false, true, false  => DommaschkActionQ0R478.slabs
  | true, false, true   => DommaschkActionQ1R509.slabs
  | true, false, false  => DommaschkActionQ1R517.slabs
  | true, true, true    => DommaschkActionQ1R456.slabs
  | true, true, false   => DommaschkActionQ1R464.slabs

private theorem packets (q h upper : Bool) :
    Packet upper (panels q h upper) (steps q h upper) (steps q h upper)
      6799610938322487 5000000000000000 := by
  cases q <;> cases h <;> cases upper <;> first
    | exact DommaschkActionQ0R470.checked | exact DommaschkActionQ0R478.checked
    | exact DommaschkActionQ0R523.checked | exact DommaschkActionQ0R531.checked
    | exact DommaschkActionQ1R456.checked | exact DommaschkActionQ1R464.checked
    | exact DommaschkActionQ1R509.checked | exact DommaschkActionQ1R517.checked

private theorem covers (q h : Bool) :
    let b := bracket q h
    Cover low high (dyadic 1) (1/64) (61/10) b.slope b.left b.right b.tiles := by
  cases q <;> cases h <;> first
    | exact s0h0_cover | exact s0h1_cover | exact s1h0_cover | exact s1h1_cover

private theorem tile_at {lo hi unit step limit m a b r : ℝ} {ps : List Piece}
    (C : Cover lo hi unit step limit m a b ps) (ab : a < b) (hr : r ∈ Icc a b) :
    ∃ p ∈ ps, r ∈ Icc p.left p.right ∧ p.backward.Valid lo hi unit step limit ∧
      p.forward.Valid lo hi unit step limit := by
  induction C with
  | nil => exact absurd ab (lt_irrefl _)
  | cons p ord back fwd _ _ ih =>
    by_cases h : r ≤ p.right
    · exact ⟨p,List.mem_cons_self ..,⟨hr.1,h⟩,back,fwd⟩
    · obtain ⟨z,hz,hv⟩ := ih ((lt_of_not_ge h).trans_le hr.2) ⟨(lt_of_not_ge h).le,hr.2⟩
      exact ⟨z,List.mem_cons_of_mem _ hz,hv⟩

variable {X : Type*} [TopologicalSpace X]

/-- Physical inputs to the two compiled quadratures and all four radial tiles of one bracket.
The endpoint caps identify the shorter quadrature integrals with the full clipped action. -/
structure TraceBounds (B A : X → ℝ → ℝ → ℝ) (q h : Bool) : Prop where
  field : ContinuousOn (fun p : (X × ℝ) × ℝ => B p.1.1 p.1.2 p.2)
    ((univ ×ˢ Icc (bracket q h).left (bracket q h).right) ×ˢ Icc (-(61/10)) (61/10))
  density : ContinuousOn (fun p : (X × ℝ) × ℝ => A p.1.1 p.1.2 p.2)
    ((univ ×ˢ Icc (bracket q h).left (bracket q h).right) ×ˢ Icc (-(61/10)) (61/10))
  radial : ∀ x p, p ∈ (bracket q h).tiles →
    p.backward.Encloses (fun r t => B x r (-t)) (fun r t => A x r (-t))
      p.left p.right low high (61/10) ∧
    p.forward.Encloses (B x) (A x) p.left p.right low high (61/10)
  endpoints : ∀ (x : X) (upper : Bool),
    let b := bracket q h
    let r := if upper then b.left else b.right
    let T := (steps q h upper : ℝ) / 64
    Covers upper (A x r) (B x r) b.height (-T) (panels q h upper) ∧
      b.height ≤ B x r (-T) ∧ b.height ≤ B x r T

/-- The common single-passage action target, as an exact rational number. -/
def target : ℝ := 6799610938322487 / 5000000000000000

/-- Physical action on the fixed trace, with one passage between turning points. -/
def J (B A : X → ℝ → ℝ → ℝ) (h : ℝ) (x : X) (u : ℝ) :=
  action (B x u) (A x u) (-(61/10)) (61/10) h

/-- The generated certificates prove a secant bracket from field and density enclosures. -/
theorem TraceBounds.secant {B A : X → ℝ → ℝ → ℝ} {q h : Bool} (E : TraceBounds B A q h) :
    let b := bracket q h
    LocalLevelGraphs.SecantBracket (J B A b.height) b.left b.right target b.slope := by
  let b := bracket q h
  let T : ℝ := 61/10
  have ab : b.left < b.right := by cases q <;> cases h <;> norm_num [b,bracket]
  have hh : b.height ∈ Icc low high := by
    cases q <;> cases h <;> norm_num [b,bracket,low,high]
  have cc {F : X → ℝ → ℝ → ℝ} (H : ContinuousOn (fun p : (X × ℝ) × ℝ => F p.1.1 p.1.2 p.2)
      ((univ ×ˢ Icc b.left b.right) ×ˢ Icc (-T) T)) (x : X) {r : ℝ} (hr : r ∈ Icc b.left b.right) :
      ContinuousOn (F x r) (Icc (-T) T) := H.comp
    (f := fun t : ℝ => ((x,r),t)) (continuous_const.prodMk continuous_id).continuousOn
    (fun _ ht => ⟨⟨trivial,hr⟩,ht⟩)
  have ends (x : X) (upper : Bool) :
      let r := if upper then b.left else b.right
      if upper then J B A b.height x r < target else target < J B A b.height x r := by
    let r := if upper then b.left else b.right
    let τ : ℝ := (steps q h upper : ℝ)/64
    have hr : r ∈ Icc b.left b.right := by cases upper <;> exact ⟨by first | rfl | exact ab.le,
      by first | rfl | exact ab.le⟩
    have ht : τ ∈ Icc 0 T := by cases q <;> cases h <;> cases upper <;> norm_num [τ,steps,T]
    have sub : Icc (-τ) τ ⊆ Icc (-T) T := Icc_subset_Icc (neg_le_neg ht.2) ht.2
    obtain ⟨p,hp,hu,cn,cp⟩ := tile_at (covers q h) ab hr
    obtain ⟨en,ep⟩ := E.radial x p hp
    obtain ⟨quadrature,capL,capR⟩ := E.endpoints x upper
    have hB := cc E.field x hr
    have hA := cc E.density x hr
    have ident := action_eq_short_of_caps cn cp en ep (by norm_num [low]) hh
      (by norm_num) hu hB hA ht ht capL capR
    unfold twoSidedAction at ident
    rw [twoSidedAction_eq (by norm_num) hB hA] at ident
    have positive (t) (hτ : t ∈ Icc (-τ) τ) : 0 ≤ A x r t := by
      have ht' := sub hτ
      by_cases s : 0 ≤ t
      · exact (ep.nonneg r hu t ⟨s,ht'.2⟩).2
      · have htneg : -t ∈ Icc 0 T :=
          ⟨neg_nonneg.mpr (le_of_not_ge s), neg_le.mp ht'.1⟩
        simpa using (en.nonneg r hu (-t) htneg).2
    have e := (packets q h upper).sound (w := A x r) (f := B x r) (h := b.height)
      (by norm_num) (by simpa only [neg_div] using quadrature)
      (by simpa only [neg_div] using positive) (by simpa only [neg_div] using hB.mono sub)
      (by simpa only [neg_div] using hA.mono sub)
    change (if upper then J B A b.height x r < target else target < J B A b.height x r)
    unfold J
    rw [ident]
    norm_num only [τ, neg_div, target, Nat.cast_ofNat] at e ⊢
    exact e
  apply (covers q h).secantBracket (by norm_num [low]) hh (by norm_num)
    (by cases q <;> cases h <;> norm_num [b,bracket,s0h0Slope,s0h1Slope,s1h0Slope,s1h1Slope,dyadic])
    (fun x r t => B x r (-t)) (fun x r t => A x r (-t)) B A E.radial _ _ _ (fun x => ends x true)
    (fun x => ends x false)
  · intro x r hr
    exact (twoSidedAction_eq (by norm_num : (0 : ℝ) ≤ 61/10) (cc E.field x hr) (cc E.density x hr)).symm
  · exact continuousOn_action_family (by norm_num) continuousOn_const E.field E.density

/-- Two sector-local graphs at the same target action, separated by more than 9/200.
Each radius is unique in its own recorded bracket. -/
theorem sector_graphs {B A : X → ℝ → ℝ → ℝ} (q : Bool)
    (hi : TraceBounds B A q true) (lo : TraceBounds B A q false) :
    ∃ u v : X → ℝ, Continuous u ∧ Continuous v ∧ ∀ x,
      u x ∈ Ioo (bracket q true).left (bracket q true).right ∧
      v x ∈ Ioo (bracket q false).left (bracket q false).right ∧
      9/200 < v x - u x ∧ J B A high x (u x) = target ∧ J B A low x (v x) = target ∧
      (∀ r ∈ Icc (bracket q true).left (bracket q true).right, J B A high x r = target ↔ r = u x) ∧
      (∀ r ∈ Icc (bracket q false).left (bracket q false).right,
        J B A low x r = target ↔ r = v x) := by
  have sep : (bracket q true).right < (bracket q false).left := by cases q <;> norm_num [bracket]
  have gap : (bracket q false).left - (bracket q true).right = 9/200 := by
    cases q <;> norm_num [bracket]
  obtain ⟨u,v,cu,cv,_,roots⟩ :=
    LocalLevelGraphs.separated_graphs_of_local_secants hi.secant lo.secant sep
  refine ⟨u,v,cu,cv,fun x => ?_⟩
  obtain ⟨hu,hv,hh,eu,ev,uu,vv⟩ := roots x
  rw [gap] at hh
  cases q <;> exact ⟨hu,hv,hh,eu,ev,fun r hr => (uu r hr).1,fun r hr => (vv r hr).1⟩

end PlasmaLean.Design.DommaschkLocalMirrorGraphs
