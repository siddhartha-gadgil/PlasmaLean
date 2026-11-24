/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkLowerActionPath
public import PlasmaLean.Certificates.ActionFloorShells

/-! # A lower arclength integral from the physical radial coordinate on every signed slab -/

@[expose] public section
namespace PlasmaLean.Design.DommaschkPilotArcLength
open Set MeasureTheory Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
open Certificates.PolynomialActionFloor DommaschkLowerActionPath DommaschkSignedTraceDensity

/-- The unit-radius center yields a lower endpoint even on a box crossing that center. -/
def lower (r : Step) : ℚ :=
  1 - ((r.physicalOut : ℚ) / 2^80 + magnitude (difference (polynomial r 0) [1]))

def radiusAt (rs : List Step) (i : ℕ) : ℚ := ((rs[i]?).map lower).getD 0

def paired (f b : List Step) (i : ℕ) : ℚ := min (radiusAt f i) (radiusAt b i)

def arcFloor (f b : List Step) : ℕ → ℚ
  | 0 => 0
  | i+1 => arcFloor f b i + paired f b i / 32

noncomputable section

theorem radius_of_mem {r : Step} {s : State} {a t : ℝ} {x : Plane}
    (ht : t ∈ Icc a (a + 1 / 64)) (hx : x ∈ (physicalSlab s r a).tube t) : (lower r : ℝ) ≤ x 0 := by
  have input : (⟨polynomial r 0, (r.physicalOut : ℚ) / 2^80⟩ : Model).Mem (coord a t) (x 0) := by
    have e := DommaschkMirrorEndpointSign.coordinate hx 0
    change |x 0 - Certificates.QPoly.eval (polynomial r 0) (coord a t)| ≤ _ at e
    simpa only [Model.Mem,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using e
  have bounded := abs_le.mp (enclose (c := ⟨[1], (r.physicalOut : ℚ) / 2^80 +
    magnitude (difference (polynomial r 0) [1])⟩) (abs_coord_le ht) input le_rfl)
  simp only [Certificates.QPoly.eval_cons,Certificates.QPoly.eval_nil,
    Rat.cast_one,mul_zero,add_zero] at bounded
  unfold lower
  push_cast
  push_cast at bounded
  linarith only [bounded.1]

/-- Integrate one common lower radius on each pair of original tubes. -/
theorem arclength {f b : List Step} {n : ℕ} {y : ℝ → Plane} {w : ℝ → ℝ}
    (fitF : n ≤ f.length) (fitB : n ≤ b.length) (track : Tracks f b n y)
    (cw : ContinuousOn w (Icc (-(n / 64 : ℝ)) (n / 64)))
    (rad : ∀ t ∈ Icc (-(n / 64 : ℝ)) (n / 64), y t 0 ≤ w t) :
    (arcFloor f b n : ℝ) ≤ ∫ t in -(n / 64 : ℝ)..(n / 64), w t := by
  induction n with
  | zero => simp [arcFloor]
  | succ n ih =>
    have ord : (n / 64 : ℝ) ≤ (n.succ / 64 : ℝ) := by push_cast; linarith
    have pos : (0 : ℝ) ≤ n / 64 := by positivity
    have sub := Icc_subset_Icc (neg_le_neg ord) ord
    have center := ih (Nat.le_of_succ_le fitF) (Nat.le_of_succ_le fitB) (track.mono (Nat.le_succ n))
      (cw.mono sub) (fun t ht => rad t (sub ht))
    have shell : Shell w (n / 64) (n.succ / 64) ((paired f b n : ℝ) / 64) := by
      apply shell_of_bounds pos ord cw (p := fun _ => (paired f b n : ℝ)) continuous_const
      · simp only [intervalIntegral.integral_const,smul_eq_mul,Nat.cast_succ]
        ring
      intro t ht
      have hi : t ∈ Icc ((n : ℝ) / 64) (((n : ℝ) + 1) / 64) := by simpa using ht
      have htime : t ∈ Icc ((n : ℝ) / 64) ((n : ℝ) / 64 + 1 / 64) := by
        convert hi using 2; ring
      have front : n < f.length := fitF
      have back : n < b.length := fitB
      obtain ⟨sp,fp⟩ := track.1 n (Nat.lt_succ_self n) front
      obtain ⟨sm,bm⟩ := track.2 n (Nat.lt_succ_self n) back
      have p : (lower f[n] : ℝ) ≤ y t 0 := radius_of_mem htime (fp t hi)
      have m : (lower b[n] : ℝ) ≤ y (-t) 0 := radius_of_mem htime (bm t hi)
      have v : 0 ≤ t := pos.trans ht.1
      have abs := ht.2
      refine ⟨?_,?_⟩
      · exact (show (paired f b n : ℝ) ≤ _ from by
          unfold paired radiusAt
          simp [front]).trans
          (p.trans (rad t ⟨by linarith,abs⟩))
      · exact (show (paired f b n : ℝ) ≤ _ from by
          unfold paired radiusAt
          simp [back]).trans
          (m.trans (rad (-t) ⟨by linarith,by linarith⟩))
    have total := shell.adjoin pos ord cw center
    simp only [arcFloor,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat]
    linarith only [total]

end
end PlasmaLean.Design.DommaschkPilotArcLength
