/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Closed upper bounds from exact action rectangle sums -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.MirrorActionQuadrature
open Set

/-- An upper cover bounds the physical action by the exact rational rectangle sum.
Every rational above that sum is an admissible strict target for the same blocks. -/
theorem exact_upper_mass {bs : List (Block true)} {l r : ℕ} (len : bs.length = l + r)
    {f w : ℝ → ℝ} {h : ℝ} (cells : Covers true w f h (-(l : ℝ) / 64) bs)
    (hn : ∀ t ∈ Icc (-(l : ℝ) / 64) (r / 64), 0 ≤ w t)
    (cf : ContinuousOn f (Icc (-(l : ℝ) / 64) (r / 64)))
    (cw : ContinuousOn w (Icc (-(l : ℝ) / 64) (r / 64))) :
    Kinetic.MirrorHeightAction.action f w (-(l : ℝ) / 64) (r / 64) h ≤
      total bs / (3072 * 1099511627776 : ℝ) := by
  by_contra! bad
  obtain ⟨q, low, high⟩ := exists_rat_btwn bad
  have nz : (0 : ℝ) ≤ total bs / (3072 * 1099511627776 : ℝ) := by positivity
  have qpos : (0 : ℝ) ≤ q := nz.trans low.le
  have nonneg : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast qpos)
  have cast : (q : ℝ) = q.num.toNat / (q.den : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg nonneg).symm
  rw [cast] at low high
  have positive : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have cross := (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3072 * 1099511627776) positive).mp low
  have p : Packet true bs l r q.num.toNat q.den := by
    refine ⟨len, ?_⟩
    change total bs * q.den < q.num.toNat * 3072 * 1099511627776
    rw [mul_assoc]
    exact_mod_cast cross
  exact lt_asymm high (p.sound q.den_pos cells hn cf cw)

end PlasmaLean.Certificates.MirrorActionQuadrature
