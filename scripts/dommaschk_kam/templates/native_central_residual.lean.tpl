module
public import PlasmaLean.Design.DommaschkPhysicalCentralJet
public import PlasmaLean.Design.DommaschkSectionReflection
${field_imports}

/-! # Both physical central defects from one seven-harmonic field evaluation -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.${name}
open Certificates.QPoly Certificates.TrajectoryTaylorModel
open DommaschkKam DommaschkBounceField DommaschkBounceTaylor FramedTaylorResidual
open DommaschkSectionReflection
set_option maxRecDepth 12000

def reference : Inputs := ⟨${fieldInputs}.displacement, ${fieldInputs}.vertical,
  ${fieldInputs}.phase .cos1, ${fieldInputs}.phase .sin1⟩
def backReference : Inputs := ⟨${back_coords}⟩
def frame : Frame := Frame.ofEndpoints (${left}) (${right})
def backFrame : Frame := Frame.ofEndpoints (${back_left}) (${back_right})
def budget : ℚ := ${forward_budget}
def backBudget : ℚ := ${back_budget}
def sharp : ℚ := ${sharp}

theorem exact_pair : CurvePair reference backReference ∧ FramePair frame backFrame := by
  constructor <;> constructor <;> apply eq_of_beq <;> kernel_fact

private def ratio : FramedTaylorResidual.Quotient := ⟨${ratio}⟩
private theorem accepted : Accepts ratio sharp (${x}/2^80) (${y}/2^80) (${den}/2^80)
    [-3/4,-1/2,-1/4,0,1/4,1/2,3/4,1] := by
  constructor <;> kernel_fact

private theorem built :
    build ⟨7,80⟩ false 128 frame reference.u reference.z
      ${fieldR}.model ${fieldZ}.model ${fieldD}.model = ratio := by
  apply Quotient.mk.injEq .. |>.mpr
  refine ⟨Matches.eq ?_, Matches.eq ?_, Matches.eq ?_⟩ <;>
    constructor <;> apply eq_of_beq <;> kernel_fact

private theorem coordinates {s : ℝ} (hs : |s| ≤ 1) :
    0 < position reference s 0 ∧ reference.u.Mem s (position reference s 0 - dkR0) ∧
      reference.z.Mem s (position reference s 1) := by
  have own (m : Model) (h : m.radius = 0) : m.Mem s (eval m.poly s) := by simp [Model.Mem,h]
  have hu : reference.u.Mem s (position reference s 0 - dkR0) := by
    simpa only [position, Matrix.cons_val_zero, add_sub_cancel_left] using
      own reference.u (eq_of_beq (by kernel_fact))
  have hz : reference.z.Mem s (position reference s 1) := own reference.z (eq_of_beq (by kernel_fact))
  have hr := enclose (c := ⟨[0], 1/2⟩) hs hu (by kernel_fact)
  norm_num [Model.Mem, dkR0, abs_le] at hr
  exact ⟨by linarith, hu, hz⟩

private theorem normalized {t : ℝ} (ht : t ∈ Set.Icc (${i}/64:ℝ) (${stop}/64)) :
    |128*t-${off}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem forward_sharp {t : ℝ} (ht : t ∈ Set.Icc (${i}/64:ℝ) (${stop}/64)) :
    let s := 128*t-${off}
    let v := physicalFlow 0 1 t (position reference s) - velocity reference 128 s
    let w := pulled frame s v
    Real.sqrt ((w 0)^2+(w 1)^2) ≤ (sharp:ℝ) := by
  have hs := normalized ht
  obtain ⟨pos, hu, hz⟩ := coordinates hs
  have hcert := accepted
  rw [← built] at hcert
  apply DommaschkPhysicalCentralJet.of_memberships (back := false) (phase := 0) hcert hs pos
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, zero_add, atPoint]
      using ${fieldR}.sound hs hu hz (${fieldInputs}.angles ht)
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, zero_add, atPoint]
      using ${fieldZ}.sound hs hu hz (${fieldInputs}.angles ht)
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, zero_add, atPoint]
      using ${fieldD}.sound hs hu hz (${fieldInputs}.angles ht)
  · exact ⟨by kernel_fact, by kernel_fact, by kernel_fact, by kernel_fact⟩

theorem forward_defect {t : ℝ} (ht : t ∈ Set.Icc (${i}/64:ℝ) (${stop}/64)) :
    let s := 128*t-${off}
    let v := physicalFlow 0 1 t (position reference s) - velocity reference 128 s
    let w := pulled frame s v
    Real.sqrt ((w 0)^2+(w 1)^2) ≤ (budget:ℝ) :=
  (forward_sharp ht).trans (by exact_mod_cast (show sharp ≤ budget by kernel_fact))

theorem backward_defect {t : ℝ} (ht : t ∈ Set.Icc (${i}/64:ℝ) (${stop}/64)) :
    let s := 128*t-${off}
    let v := physicalFlow 0 (-1) t (position backReference s) - velocity backReference 128 s
    let w := pulled backFrame s v
    Real.sqrt ((w 0)^2+(w 1)^2) ≤ (backBudget:ℝ) := by
  have eq := defect_eq exact_pair.1 exact_pair.2 t 128 (128*t-${off}) (coordinates (normalized ht)).1
  dsimp only at eq ⊢
  rw [eq]
  exact (forward_sharp ht).trans (by exact_mod_cast (show sharp ≤ backBudget by kernel_fact))

end PlasmaLean.Design.${name}
