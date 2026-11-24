/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAContract
public import PlasmaLean.Design.KamProfileJets

/-!
# First and second fundamental form inputs on Dommaschk torus A

The closeness statement on the Q-16 witness bounds both real profiles, their gradients and
their Hessians uniformly in the geometric angles. The strip radius and error are those of
the torus A certificate.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKamC

/-- Uniform profile, gradient and Hessian error budgets in physical angular coordinates. -/
structure ProfileJetBound (exact seed : ℝ → ℝ → ℝ) (ρ M : ℝ) : Prop where
  value : ∀ θ φ, |exact θ φ - seed θ φ| ≤ M
  first : ∀ (a : ProfileAngle) θ φ,
    |a.partialD exact θ φ - a.partialD seed θ φ| ≤ a.factor / ρ * M
  second : ∀ (a b : ProfileAngle) θ φ,
    |b.partialD (a.partialD exact) θ φ - b.partialD (a.partialD seed) θ φ| ≤
      b.factor / ρ * (a.factor / ρ * M)

/-- Strip closeness bounds the value and the first two jets of an offset profile. -/
theorem profileJetBound {x y : FA} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : Bd ρ (x - y) M) (hy : Ana y) (offset : ℝ) :
    ProfileJetBound (fun θ φ => offset + Zof x θ φ) (fun θ φ => offset + Zof y θ φ) ρ M := by
  have shift (a : ProfileAngle) (w : FA) :
      a.partialD (fun θ φ => offset + Zof w θ φ) = a.partialD (Zof w) := by
    funext θ φ
    cases a <;> exact deriv_const_add _
  constructor
  · intro θ φ
    simpa [Zof, eval_sub'] using (Complex.abs_re_le_norm
      (eval (x - y) θ (PlasmaLean.Design.KamTorusA.psi φ))).trans
      (KamNewton.norm_eval_le_of_Bd hρ.le hd θ _)
  · intro a θ φ
    simpa only [shift] using a.first_error hρ hd hy θ φ
  · intro a b θ φ
    simpa only [shift] using a.second_error b hρ hd hy θ φ

/-- The exact profiles in the Q-16 strip-closeness conclusion have the stated jet bounds
on the whole torus, including the arc used in the pressure-interface screen. -/
theorem profileJets_of_close {u z : FA} {M : ℝ}
    (h : Close (9 / 1400) DommaschkKamDio.dkIotaA u z u₀A z₀A M) :
    ProfileJetBound (RofC u) (RofC u₀A) (9 / 1400) M ∧
    ProfileJetBound (Zof z) (Zof z₀A) (9 / 1400) M := by
  refine ⟨profileJetBound (by norm_num) h.du ana_u₀A _, ?_⟩
  simpa only [zero_add] using profileJetBound (by norm_num) h.dz ana_z₀A 0

/-- Every exact torus A inherits the surface and curvature input bounds from its own KAM data. -/
theorem ExactTorusA.profileJets {u z : FA} (h : ExactTorusA u z) :
    ProfileJetBound (RofC u) (RofC u₀A) (9 / 1400) ((1 / 10 ^ 12 : ℚ) : ℝ) ∧
    ProfileJetBound (Zof z) (Zof z₀A) (9 / 1400) ((1 / 10 ^ 12 : ℚ) : ℝ) :=
  profileJets_of_close h.close

end PlasmaLean.Design.DommaschkKamA
