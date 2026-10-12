/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Supplied steady slab heat laws

Constant conductivity and heat-transfer coefficient; uniform volumetric heating;
one cooled and one loaded face on [0,h]. In SI: T,Tc in K, q in W/m², Q in W/m³,
h in m, k in W/(m K), hc in W/(m² K). Applicability of this one-dimensional model
to a component is a separate empirical/engineering assumption.
-/
public section
namespace PlasmaLean.Engineering

/-- A classical steady heat solution, with an explicit first derivative and boundary laws. -/
class SteadySlab (T dT : ℝ → ℝ) (Tc q Q h k hc : ℝ) : Prop where
  thickness_nonneg : 0 ≤ h
  conductivity_pos : 0 < k
  cooling_pos : 0 < hc
  temperature_derivative : ∀ x ∈ Set.Icc 0 h, HasDerivAt T (dT x) x
  flux_derivative : ∀ x ∈ Set.Icc 0 h, HasDerivAt dT (-Q / k) x
  hot_flux : k * dT h = q
  cold_flux : k * dT 0 = hc * (T 0 - Tc)

end PlasmaLean.Engineering
