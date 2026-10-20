
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
3. **Analytic Obstruction Sanity Checks:** In a vacuum magnetic field ($\nabla \cdot \mathbf{B} = 0, \nabla \times \mathbf{B} = 0$), $\vert{}\mathbf{B}\vert{}^2$ is subharmonic ($\Delta (\vert{}\mathbf{B}\vert{}^2) = 2 \Vert{}\nabla \mathbf{B}\Vert{}_{\text{Frob}}^2 \ge 0$), meaning $\vert{}\mathbf{B}\vert{}$ cannot attain a strict local **maximum** in the interior of a vacuum region. Local minima are possible. The obstruction relevant to maximum-J is different: in vacuum $\nabla_\perp B = B\boldsymbol{\kappa}$, so a local minimum of $|\mathbf{B}|$ at a point of a field line forces zero field-line curvature there (see Sanity Check 3 and `notes/theory/toroidal-min-b-obstruction.md`).
   > **Correction (2026-10-20):** This item previously said subharmonicity forbids a strict interior local *minimum* of |B|. That is false. For example, $\mathbf{B}=(x,y,-2z)$ is a vacuum field with $|\mathbf{B}|^2 = x^2+y^2+4z^2$, and Ioffe–Pritchard traps give minima with $|\mathbf{B}|\neq 0$.

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

> **Correction (2026-10-20), unchecked step:** The boundary terms vanish because the $\mathcal{J}_\parallel$ integrand vanishes at $l_\pm$. But the differentiated integrand has an integrable $1/\sqrt{\cdot}$ singularity there, so the classical Leibniz rule does not apply directly. A valid justification needs simple turning points ($\partial_l B(l_\pm) \neq 0$), for example via the substitution that removes the square-root singularity or via dominated convergence. Without simple turning points (barely trapped particles, flat-bottomed wells) the identity can fail. These hypotheses must be explicit before formalization.

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

> **Correction (2026-10-20), unchecked formula:** The formula for $\widehat{\mathcal{A}}$ above, including the weight $z^{5/2}e^{-z}$, the form of $\hat{G}(\lambda)$, the normalization of $\hat\omega_\alpha$, and whether $\Theta$ is the ramp or the Heaviside step, has **not** been checked against Mackenbach, Proll & Helander, PRL 128, 175001 (2022) (arXiv:2109.01042; erratum PRL 130, 239901 (2023)), and JPP 89, 905890513 (2023). Extract it exactly from the papers, with equation numbers, before any Lean statement depends on it. Only the trivial kernel lemma (Sanity Check 2) is independent of these details.

**Key Verification Insight (corrected):** The integrand $\Theta(\hat{\omega}_*(\hat{\omega}_* - \hat{\omega}_\alpha))$ vanishes exactly when $\hat{\omega}_*(z)$ lies between $0$ and $\hat{\omega}_\alpha(\lambda)$, i.e. when the two frequencies have **matching** signs and $\vert{}\hat{\omega}_\alpha\vert{} \ge \vert{}\hat{\omega}_*\vert{}$ (precession dominance). This gives a closed-form integral certificate bounding trapped-particle available energy.

**Correction (2026-10-20):** The earlier text also claimed the integrand vanishes when $\hat{\omega}_*$ and $\hat{\omega}_\alpha$ have *opposite* signs. That is false: then $\hat{\omega}_*(\hat{\omega}_* - \hat{\omega}_\alpha) \ge \hat{\omega}_*^2 > 0$ whenever $\hat{\omega}_* \ne 0$. This is proved in Lean as `availableEnergyKernel_pos_of_opposite_signs` (`PlasmaLean/Theory/Kinetic/AvailableEnergy.lean`); the zero set is characterized there exactly.

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


By the maximum principle for subharmonic functions, $\|\mathbf{B}\|$ **cannot** achieve a strict local *maximum* in any open vacuum region $U \subset \mathbb{R}^3$ (minima are allowed).

The obstruction that matters for maximum-J is the curvature identity. In vacuum, $\nabla(B^2/2) = (\mathbf{B}\cdot\nabla)\mathbf{B}$, so $\nabla_\perp B = B\boldsymbol{\kappa}$. At finite β the same holds wherever $\nabla p = 0$, for instance on the magnetic axis (Helander 2014, Rep. Prog. Phys. 77 087001, Eq. 24). Two consequences:
- A local minimum of $|\mathbf{B}|$ at a point with $\mathbf{B}\neq 0$ forces $\boldsymbol\kappa = 0$ at that point.
- $|\mathbf{B}|$ cannot be non-decreasing outward from a *closed* magnetic axis in every normal plane, because that would force $\kappa \equiv 0$ on a closed curve.

So the deeply trapped maximum-J condition $\partial_\psi B > 0$ at $B_{\min}$ requires a straight section of axis at the minimum (Helander 2014 §3.7), and exact quasisymmetric fields cannot be maximum-J (Rodríguez, Helander & Goodman, JPP 90, 905900212 (2024)). Details and status are in `notes/theory/toroidal-min-b-obstruction.md`.

> **Correction (2026-10-20):** This check previously said subharmonicity forbids a strict interior local minimum of |B| and drew the maximum-J conclusion from that. The premise is false: $\mathbf{B}=(x,y,-2z)$ is a counterexample. The correct obstruction is the curvature identity stated above.

