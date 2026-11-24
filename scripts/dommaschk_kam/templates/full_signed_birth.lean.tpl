module
public import PlasmaLean.Design.DommaschkSignedBirthApproach
public import PairedPrefixCache.DommaschkPairedPrefix391
public import SignedMirrorCache.DommaschkSignedMirrorBrackets
public import SignedSlopeCache.DommaschkSignedSlope316
public import SignedSlopeCache.DommaschkSignedSlope324
public import SubmirrorPrefixCache.DommaschkSubmirror316Of325
public import SubmirrorPrefixCache.DommaschkUpperSubmirror324Of325

/-! # The same signed QA2R path through each actual Q-16 birth on all 782 archived slabs -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFullSignedBirth
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkMirrorLaunch
open DommaschkSignedMirrorSlope
set_option maxRecDepth 8192

abbrev WholePath (x : Plane) (y : ℝ → Plane) :=
  Path 391 DommaschkPhysicalPrefix391.exitState DommaschkBackwardPrefix391.exitState
    DommaschkPhysicalPrefix391.rows DommaschkBackwardPrefix391.rows x y

def rowsFor (back : Bool) : List Step :=
  if back then DommaschkBackwardPrefix391.rows else DommaschkPhysicalPrefix391.rows

theorem length_rowsFor (back : Bool) : (rowsFor back).length = 391 := by
  cases back <;> with_unfolding_all rfl

/-- Distance to the reference with the specified chronological index on its own branch. -/
def IndexedError (y : ℝ → Plane) : Prop :=
  ∀ (back : Bool) (i : Fin 391) (t : ℝ), t ∈ Set.Icc (i.val / 64 : ℝ) ((i.val + 1 : ℝ) / 64) →
    dist (y (if back then -t else t))
      (reference (i.val / 64) ((rowsFor back)[i.val]'(by rw [length_rowsFor]; exact i.isLt)) t) ≤
      4022059640817442909 / (2 : ℝ)^80

theorem indexed_error {x y} (p : WholePath x y) : IndexedError y := by
  have sizes (b : Bool) : (rowsFor b).all (fun r => r.physicalOut.ble 4022059640817442909) = true := by
    cases b <;> with_unfolding_all rfl
  intro b i t ht
  have hi : i.val < (rowsFor b).length := by rw [length_rowsFor]; exact i.isLt
  obtain ⟨_, prev, tube⟩ := p.at_row i.isLt b hi
  have hrow := Nat.ble_eq.mp (List.all_eq_true.mp (sizes b) _ (List.getElem_mem hi))
  exact (tube t ht).2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hrow) (by positivity))

/-- Both first-contact statements concern the very same signed line as the position estimate. -/
def MirrorContacts (y : ℝ → Plane) : Prop :=
  FirstTransverseBoth (316/64) (317/64) (DommaschkFirstMirrorLaunchSign.height false) (1/128) y ∧
  FirstTransverseBoth (324/64) (325/64) (DommaschkFirstMirrorLaunchSign.height true) (1/400) y

theorem contacts {x y} (p : WholePath x y) : MirrorContacts y := by
  constructor
  · have below := p.below_on (k := 316) (by norm_num) rfl rfl
        DommaschkSubmirror316Of325.fwd_checked DommaschkSubmirror316Of325.back_checked
    apply first_transverse
    · exact DommaschkSignedMirrorBrackets.first316 p (by norm_num)
        (by change 316 < 391; norm_num) (by change 316 < 391; norm_num) rfl rfl below
    · exact DommaschkSignedSlope316.regular p (by norm_num)
        (by change 316 < 391; norm_num) (by change 316 < 391; norm_num) rfl rfl
  · have below := p.below_on (k := 324) (by norm_num) rfl rfl
        DommaschkUpperSubmirror324Of325.fwd_checked DommaschkUpperSubmirror324Of325.back_checked
    apply first_transverse
    · exact DommaschkSignedMirrorBrackets.first324 p (by norm_num)
        (by change 324 < 391; norm_num) (by change 324 < 391; norm_num) rfl rfl below
    · exact DommaschkSignedSlope324.regular p (by norm_num)
        (by change 324 < 391; norm_num) (by change 324 < 391; norm_num) rfl rfl

/-- Every admitted original birth belongs to one full signed solution. Each of its
closed slabs satisfies the explicit error bound, and both heights have their four
certified first, transverse contacts on that solution. -/
theorem through_birth : DommaschkSignedBirthApproach.ThroughBirth (fun _ y =>
    ∃ x, WholePath x y ∧ IndexedError y ∧
      (4022059640817442909 / (2 : ℝ)^80 < 3327 / 1000000000) ∧ MirrorContacts y) := by
  apply DommaschkSignedBirthApproach.from_birthWith
    (birth_with DommaschkPairedPrefix391.exists_nested_paired
      (fun _ _ path => And.intro (indexed_error path) (contacts path))) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  intro φ small x y path info
  exact ⟨x, path, info.1, by norm_num, info.2⟩

end PlasmaLean.Design.DommaschkFullSignedBirth
