module
public import PlasmaLean.Design.DommaschkPhysicalCentralJet
public import SignedCentralFieldCache.$fieldZ

/-! # Central ODE defect in the original opposite-section time direction -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.$name
open Certificates.QPoly Certificates.TrajectoryTaylorModel
open DommaschkKam DommaschkBounceField DommaschkBounceTaylor FramedTaylorResidual
set_option maxRecDepth 12000

def reference : Inputs := ⟨$input.displacement, $input.vertical, $input.phase .cos1, $input.phase .sin1⟩
def frame : Frame := Frame.ofEndpoints ($left) ($right)
def budget : ℚ := $budget
private def ratio : FramedTaylorResidual.Quotient := ⟨$ratio⟩

private theorem accepted : Accepts ratio budget ($x/2^80) ($y/2^80) ($den/2^80)
    [-3/4,-1/2,-1/4,0,1/4,1/2,3/4,1] := by
  constructor <;> kernel_fact
private theorem built : build ⟨7,80⟩ $back 128 frame reference.u reference.z
    $fieldR.model $fieldZ.model $fieldD.model = ratio := by
  apply Quotient.mk.injEq .. |>.mpr
  refine ⟨Matches.eq ?_, Matches.eq ?_, Matches.eq ?_⟩ <;>
    constructor <;> apply eq_of_beq <;> kernel_fact

theorem physical_defect {t : ℝ} (ht : t ∈ Set.Icc ($i/64:ℝ) ($stop/64)) :
    let s := 128*t-$off
    let v := physicalFlow (Real.pi/2) ($sign) t (position reference s) - velocity reference 128 s
    let w := pulled frame s v
    Real.sqrt ((w 0)^2+(w 1)^2) ≤ (budget:ℝ) := by
  let s := 128*t-$off
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by dsimp [s]; linarith [ht.1], by dsimp [s]; linarith [ht.2]⟩
  have own (m : Model) (h : m.radius = 0) : m.Mem s (eval m.poly s) := by simp [Model.Mem,h]
  have hu : reference.u.Mem s (position reference s 0 - dkR0) := by
    simpa only [position, Matrix.cons_val_zero, add_sub_cancel_left] using
      own reference.u (eq_of_beq (by kernel_fact))
  have hz : reference.z.Mem s (position reference s 1) := own reference.z (eq_of_beq (by kernel_fact))
  have hr := enclose (c := ⟨[0], 1/2⟩) hs hu (by kernel_fact)
  norm_num [Model.Mem, dkR0, abs_le] at hr
  have cert := accepted
  rw [←built] at cert
  apply DommaschkPhysicalCentralJet.of_memberships (back := $back) (phase := Real.pi/2) cert hs (by linarith)
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, atPoint]
      using $fieldR.sound hs hu hz ($input.angles ht)
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, atPoint]
      using $fieldZ.sound hs hu hz ($input.angles ht)
  · simpa only [clockPoly, sign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, atPoint]
      using $fieldD.sound hs hu hz ($input.angles ht)
  · exact ⟨by kernel_fact, by kernel_fact, by kernel_fact, by kernel_fact⟩

end PlasmaLean.Design.$name
