/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Engineering.SlabHeat
public import Mathlib.Tactic.NormNum

/-!
# A synthetic component certificate over a continuous input box

This is exactly the invented fixture from note 07, not sourced material data or a
reactor candidate. Its purpose is an end-to-end theorem: every real input in the
box and every spatial point in the slab has the certified temperature margin.
-/
public section

namespace PlasmaLean.Design
open Engineering

/-- Entire-box temperature enclosure, including continuum positions. -/
theorem synthetic_slab_bound (Tc q Q h k hc x : ℝ)
    (hTc : Tc ∈ Set.Icc 300 330)
    (hq : q ∈ Set.Icc 8000000 10000000)
    (hQ : Q ∈ Set.Icc 0 20000000)
    (hh : h ∈ Set.Icc (3 / 1000) (1 / 250))
    (hk : k ∈ Set.Icc 90 110)
    (hhc : hc ∈ Set.Icc 50000 80000)
    (hx : x ∈ Set.Icc 0 h) : slabTemperature Tc q Q h k hc x ≤ 44002 / 45 := by
  have qpos : 0 ≤ q := by linarith [hq.1]
  have hpos : 0 ≤ h := by linarith [hh.1]
  have kpos : 0 < k := by linarith [hk.1]
  have h₁ := slab_le_maximum Tc q Q h k hc x qpos hQ.1 kpos hx.2
  have h₂ := slabMaximum_mono hTc.2 qpos hq.2 hQ.1 hQ.2 hpos hh.2
    (by norm_num : (0 : ℝ) < 90) hk.1 (by norm_num : (0 : ℝ) < 50000) hhc.1
  norm_num [slabMaximum] at h₂
  exact h₁.trans h₂

/-- Exact margin below the synthetic 1000 K limit for every input and position. -/
theorem synthetic_slab_margin (Tc q Q h k hc x : ℝ)
    (hTc : Tc ∈ Set.Icc 300 330)
    (hq : q ∈ Set.Icc 8000000 10000000)
    (hQ : Q ∈ Set.Icc 0 20000000)
    (hh : h ∈ Set.Icc (3 / 1000) (1 / 250))
    (hk : k ∈ Set.Icc 90 110)
    (hhc : hc ∈ Set.Icc 50000 80000)
    (hx : x ∈ Set.Icc 0 h) :
    998 / 45 ≤ 1000 - slabTemperature Tc q Q h k hc x := by
  have hb := synthetic_slab_bound Tc q Q h k hc x hTc hq hQ hh hk hhc hx
  linarith

/-- The worst-case corner attains the bound, checking sharpness of the fixture. -/
theorem synthetic_corner_exact :
    slabTemperature 330 10000000 20000000 (1 / 250) 90 50000 (1 / 250) = 44002 / 45 := by
  norm_num [slabTemperature]

/-- End-to-end margin for any classical solution of the declared physical model
throughout the synthetic input box, not just for an evaluated formula. -/
theorem synthetic_slab_model_margin (T dT : ℝ → ℝ) (Tc q Q h k hc x : ℝ)
    [SteadySlab T dT Tc q Q h k hc]
    (hTc : Tc ∈ Set.Icc 300 330)
    (hq : q ∈ Set.Icc 8000000 10000000)
    (hQ : Q ∈ Set.Icc 0 20000000)
    (hh : h ∈ Set.Icc (3 / 1000) (1 / 250))
    (hk : k ∈ Set.Icc 90 110)
    (hhc : hc ∈ Set.Icc 50000 80000)
    (hx : x ∈ Set.Icc 0 h) : 998 / 45 ≤ 1000 - T x := by
  rw [slab_unique T dT Tc q Q h k hc x hx]
  exact synthetic_slab_margin Tc q Q h k hc x hTc hq hQ hh hk hhc hx

end PlasmaLean.Design
