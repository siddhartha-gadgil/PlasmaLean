
# Formalization Note: Microturbulent Transport, the Maximum-$J$ Property, and Available Energy ($\mathcal{A}$)

**Workstream:** `particles-and-transport` / `geometry-and-fields`  
**Status:** Blueprint & Small-Kernel Specification  
**Target Module:** `PlasmaLean.Transport.AvailableEnergy`

---

## 1. Motivation & Verification Strategy

In an optimized stellarator where neoclassical (collisional ripple) transport has been suppressed via quasisymmetry or quasi-isodynamicity, **microturbulent transport**—driven by Ion Temperature Gradient (ITG) and Trapped Electron Mode (TEM) instabilities—becomes the primary mechanism limiting energy confinement.

Directly verifying a 5D nonlinear gyrokinetic Vlasov–Maxwell PDE solver in Lean 4 is neither necessary nor optimal for stellarator design. Instead, modern stellarator theory controls microturbulence through **rigorous geometric and thermodynamic bounds** defined directly on the 3D magnetic equilibrium:
1. **The Omnigeneity & Maximum-$J$ Contract:** Certifying that the second adiabatic invariant $\mathcal{J}_\parallel(\psi, \alpha, v, \lambda)$ satisfies $\partial_\alpha \mathcal{J}_\parallel = 0$ (zero bounce-averaged radial drift) and $\partial_\psi \mathcal{J}_\parallel < 0$ (favorable bounce-averaged curvature, reversing trapped-electron precession relative to drift waves).
2. **The Helander–Mackenbach Available Energy ($\mathcal{A}$) Bound:** A closed-form upper bound on the thermal free energy that can be converted into turbulent fluctuations under phase-space rearrangements preserving adiabatic invariants $(\mu, \mathcal{J}_\parallel)$.
3. **Analytic Obstruction Sanity Checks:** In a vacuum magnetic field ($\nabla \cdot \mathbf{B} = 0, \nabla \times \mathbf{B} = 0$), $\vert{}\mathbf{B}\vert{}^2$ is strictly subharmonic ($\Delta (\vert{}\mathbf{B}\vert{}^2) = 2 \Vert{}\nabla \mathbf{B}\Vert{}_{\text{Frob}}^2 \ge 0$), meaning $\vert{}\mathbf{B}\vert{}$ cannot attain a strict local minimum in the interior of a plasma volume. Formalizing this theorem acts as an essential **kernel sanity check** ensuring that our near-axis and finite-$\beta$ contracts do not demand mathematically impossible exact vacuum global minima.

---

## 2. Mathematical Formulation

### 2.1 Clebsch Coordinates & The Second Adiabatic Invariant $\mathcal{J}_\parallel$
Let $U \subset \mathbb{R}^3$ be a toroidal flux-tube domain foliated by flux surfaces $\psi : U \to \mathbb{R}$ and field-line labels $\alpha : U \to \mathbb{R}/2\pi\mathbb{Z}$ such that the magnetic field 2-form is exact in Clebsch representation:
$$\mathbf{B} = \nabla \psi \times \nabla \alpha, \qquad \omega_B = d\psi \wedge d\alpha.$$

Let $l \in [l_-(\psi, \alpha, \lambda), l_+(\psi, \alpha, \lambda)]$ denote arc length along a field line $(\psi, \alpha)$ between consecutive bounce turning points where $1 - \lambda B(\psi, \alpha, l_\pm) = 0$, with pitch-angle parameter $\lambda = \mu / E \in [1/B_{\max}(\psi), 1/B_{\min}(\psi)]$.

The **longitudinal (second) adiabatic invariant** for a particle of mass $m$ and speed $v = \sqrt{2E/m}$ is the action integral:
$$\mathcal{J}_\parallel(\psi, \alpha, v, \lambda) = m v \int_{l_-(\psi, \alpha, \lambda)}^{l_+(\psi, \alpha, \lambda)} \sqrt{1 - \lambda B(\psi, \alpha, l)} \, dl.$$

### 2.2 Bounce-Averaged Hamiltonian Drift Equations
Over a single bounce period $\tau_b = \int_{l_-}^{l_+} \frac{dl}{v_\parallel}$, the net excursions in flux-surface label $\Delta \psi$ and field-line label $\Delta \alpha$ for a particle of charge $q$ are governed by the canonical Hamiltonian system with symplectic form $q \, d\psi \wedge d\alpha$:
$$\Delta \psi = \frac{1}{q} \frac{\partial \mathcal{J}_\parallel}{\partial \alpha}, \qquad \Delta \alpha = -\frac{1}{q} \frac{\partial \mathcal{J}_\parallel}{\partial \psi}.$$

Differentiating under the integral sign (since the integrand vanishes at the endpoints $l_\pm$ where $\lambda B = 1$) yields the fundamental **radial action derivative identity**:
$$\frac{\partial \mathcal{J}_\parallel}{\partial \psi} = -\frac{m v \lambda}{2} \int_{l_-}^{l_+} \left(\frac{\partial B}{\partial \psi}\right)_{\alpha, l} \frac{dl}{\sqrt{1 - \lambda B(\psi, \alpha, l)}}.$$

* **Omnigeneity Criterion:** $\frac{\partial \mathcal{J}_\parallel}{\partial \alpha} = 0$ for all trapped pitch angles $\lambda$ (zero net radial banana drift).
* **Maximum-$J$ Criterion:** $\frac{\partial \mathcal{J}_\parallel}{\partial \psi} < 0$ for all trapped pitch angles $\lambda$. By the radial derivative identity above, a sufficient pointwise condition is the **Minimum-$B$ condition** $\left(\frac{\partial B}{\partial \psi}\right)_{\alpha, l} > 0$ across the magnetic well.

### 2.3 The Helander–Mackenbach Available Energy Functional ($\mathcal{A}$)
Consider an initial local Maxwellian distribution $f_0(\psi, E)$ in a thin flux tube of radial half-width $\Delta \psi$ and binormal width $\Delta \alpha$, characterized by normalized density gradient $\omega_n = -\frac{d \ln n}{d\psi}$ and temperature gradient $\omega_T = -\frac{d \ln T}{d\psi}$.

Under any phase-space rearrangement $f \mapsto f_{\text{ground}}$ that preserves phase-space volume (Liouville's theorem on $d\psi \wedge d\alpha$) and the adiabatic invariants $(\mu, \mathcal{J}_\parallel)$ on each invariant torus, the maximum thermal energy that can be released into turbulent fluctuations (Mackenbach, Proll & Helander, *PRL* 2022; *JPP* 2023) is given in the omnigenous limit by:
$$\widehat{\mathcal{A}} = \int_{1/B_{\max}}^{1/B_{\min}} d\lambda \int_0^\infty dz \, z^{5/2} e^{-z} \, \Theta\!\Big( \hat{\omega}_*(z) \big[ \hat{\omega}_*(z) - \hat{\omega}_\alpha(\lambda) \big] \Big) \, \hat{G}(\lambda),$$
where:
* $z = E / T(\psi)$ is the normalized kinetic energy,
* $\hat{\omega}_*(z) = \omega_n + \left(z - \frac{3}{2}\right) \omega_T$ is the energy-dependent diamagnetic drift frequency,
* $\hat{\omega}_\alpha(\lambda) \propto -\frac{1}{q} \frac{\partial \mathcal{J}_\parallel}{\partial \psi}$ is the normalized bounce-averaged precession frequency, and
* $\Theta(x) = \max(0, x)$ is the positive-part ramp function.

**Key Verification Insight:** Whenever $\hat{\omega}_*(z)$ and $\hat{\omega}_\alpha(\lambda)$ have opposite signs—or when $\vert{}\hat{\omega}_\alpha(\lambda)\vert{} > \vert{}\hat{\omega}_*(z)\vert{}$ with matching signs—the integrand $\Theta(\dots)$ vanishes identically! This provides a rigorous, closed-form integral certificate bounding trapped-electron turbulence.

---

## 3. Small-Kernel Specifications in Lean 4

```lean
/-
  PlasmaLean/Kernel/TurbulenceContracts.lean
  Small-kernel specifications for bounce-action invariants, Maximum-J,
  and the Helander-Mackenbach Available Energy bound.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace PlasmaLean.Kernel

/-- Pitch-angle trapping domain λ ∈ (1 / B_max, 1 / B_min) on a flux surface -/
structure TrappingWell where
  B_min : ℝ
  B_max : ℝ
  h_pos : 0 < B_min
  h_lt  : B_min < B_max

/-- A magnetic well profile B(ψ, α, l) along arc-length l ∈ [l_left, l_right] -/
structure BounceWellProfile (W : TrappingWell) where
  B : ℝ → ℝ → ℝ → ℝ
  dB_dψ : ℝ → ℝ → ℝ → ℝ
  has_deriv_ψ : ∀ ψ α l, HasDerivAt (fun ψ' => B ψ' α l) (dB_dψ ψ α l) ψ

/-- The bounce-averaged longitudinal action integral J_∥(ψ, α, λ) (normalized by m v) -/
noncomputable def NormalizedBounceAction
    (B : ℝ → ℝ → ℝ → ℝ) (l_min l_max : ℝ) (ψ α λ : ℝ) : ℝ :=
  ∫ l in l_min..l_max, Real.sqrt (max 0 (1 - λ * B ψ α l))

/-- Radial derivative of the normalized bounce action ∂J_∥/∂ψ -/
noncomputable def BounceActionRadialDeriv
    (prof : BounceWellProfile W) (l_min l_max : ℝ) (ψ α λ : ℝ) : ℝ :=
  - (λ / 2) * ∫ l in l_min..l_max,
    (prof.dB_dψ ψ α l) / Real.sqrt (max 0 (1 - λ * prof.B ψ α l))

/-- Kernel Contract: A flux surface ψ₀ satisfies the strict Maximum-J criterion
    if it is omnigenous and ∂J_∥/∂ψ < 0 across all trapped pitch angles. -/
structure SatisfiesMaximumJ
    (W : TrappingWell) (prof : BounceWellProfile W)
    (l_min l_max : ℝ → ℝ) (ψ₀ : ℝ) : Prop where
  interval_valid : ∀ λ ∈ Set.Ioo (1 / W.B_max) (1 / W.B_min), l_min λ < l_max λ
  omnigenous : ∀ λ ∈ Set.Ioo (1 / W.B_max) (1 / W.B_min),
    ∀ α₁ α₂ : ℝ, NormalizedBounceAction prof.B (l_min λ) (l_max λ) ψ₀ α₁ λ =
                 NormalizedBounceAction prof.B (l_min λ) (l_max λ) ψ₀ α₂ λ
  strict_max_J : ∀ λ ∈ Set.Ioo (1 / W.B_max) (1 / W.B_min),
    ∀ α : ℝ, BounceActionRadialDeriv prof (l_min λ) (l_max λ) ψ₀ α λ < 0

/-- Kernel Contract: Helander-Mackenbach Available Energy integrand Θ(ω_* (ω_* - ω_α)) -/
def availableEnergyKernel (ω_star ω_alpha : ℝ) : ℝ :=
  max 0 (ω_star * (ω_star - ω_alpha))

end PlasmaLean.Kernel

```

---

## 4. Non-Vacuity Sanity Checks & Obstruction Theorems

To prevent specification bugs (such as demanding exact global Minimum-$B$ in a vacuum field or allowing `Real.sqrt` of negative numbers to silently evaluate to `0` at misordered bounce endpoints), the kernel requires three compiled sanity checks:

### Sanity Check 1: Minimum-$B$ Pointwise Positivity Implies Maximum-$J$

If $\left(\frac{\partial B}{\partial \psi}\right)_{\alpha, l} > 0$ strictly inside the bounce interval $(l_{\min}, l_{\max})$ where $1 - \lambda B > 0$, then `BounceActionRadialDeriv < 0`.

### Sanity Check 2: Zero Available Energy Under Favorable Precession Dominance

```lean
theorem availableEnergyKernel_eq_zero_of_opposing_precession
    (ω_star ω_alpha : ℝ)
    (h_stabilized : ω_star * (ω_star - ω_alpha) ≤ 0) :
    availableEnergyKernel ω_star ω_alpha = 0 := by
  simp [availableEnergyKernel, max_eq_left h_stabilized]

```

### Sanity Check 3: The Vacuum Subharmonicity Obstruction ($\Delta(|\mathbf{B}|^2) \ge 0$)

In a vacuum magnetic field ($\nabla \cdot \mathbf{B} = 0, \nabla \times \mathbf{B} = 0$), the squared field magnitude $f(x) = \|\mathbf{B}(x)\|^2$ satisfies the Bochner-Weitzenböck identity on $\mathbb{R}^3$:


$$\Delta (\|\mathbf{B}\|^2) = 2 \|\nabla \mathbf{B}\|_{\text{Frob}}^2 + 2 \langle \mathbf{B}, \Delta \mathbf{B} \rangle = 2 \|\nabla \mathbf{B}\|_{\text{Frob}}^2 \ge 0.$$


By the Strong Maximum Principle for subharmonic functions, $\|\mathbf{B}\|$ **cannot** achieve a strict local minimum in any open vacuum region $U \subset \mathbb{R}^3$. Consequently, in a vacuum stellarator ($\beta = 0$), the Maximum-$J$ property can only be achieved *approximately* (or across a subset of trapped pitch angles), never via an exact 3D local minimum of $|\mathbf{B}|$.

