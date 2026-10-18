# Formalization Note: Roadmap for Rigorous PDE Bounds, Comparison Theorems, and A Posteriori Certificates

**Workstream:** `verified-numerics` / `plasma-models-and-equilibrium` / `mhd-stability`  
**Status:** Forward Roadmap (Post-Vacuum Demonstrator)  
**Target Modules:** `PlasmaLean.Numerics.RadiiPolynomial`, `PlasmaLean.Stability.SturmComparison`, `PlasmaLean.Transport.BarrierCertificates`

---

## 1. Architectural Philosophy: Untrusted Oracles + Small-Kernel Certificates

With the vacuum Biot–Savart derivatives, Lipschitz coil-tolerance bounds, and vacuum-fixture certificates already compiled, the next phase of **PlasmaLean** addresses systems governed by nonlinear partial differential equations (PDEs):
1. **3D Magnetohydrostatic (MHS) Equilibrium:** $\mathbf{J} \times \mathbf{B} = \nabla p, \quad \nabla \times \mathbf{B} = \mu_0 \mathbf{J}, \quad \nabla \cdot \mathbf{B} = 0$.
2. **Ideal MHD Linear Stability:** Positivity of the second variation of energy $\delta^2 W(\xi, \xi) > 0$ and the 1D ballooning PDE/ODE along field lines.
3. **Nonlinear Radial Energy Transport:** Parabolic reaction-diffusion equations for temperature $T(\psi, t)$ and density $n(\psi, t)$ across nested flux surfaces.

Rather than formalizing finite-element or spectral PDE solvers inside Lean 4, **PlasmaLean** treats external numerical codes (such as `DESC`, `VMEC`, `SIMSOPT`, or AI synthesis agents) as **untrusted oracles**. The oracle emits a concrete finite-dimensional candidate (e.g., Chebyshev–Fourier coefficients $\bar{u}$, a positive Sturm–Liouville test function $X(l)$, or a polynomial barrier profile $\underline{T}(\psi)$), and the **PlasmaLean Small Kernel** verifies an *a posteriori* inequality or comparison theorem that mathematically bounds the true continuum PDE solution.

---

## 2. Stage 1: Elliptic Maximum Principles & Boundary-to-Interior Reduction

### 2.1 Mathematical Formulation
In any current-free region $\Omega \subset \mathbb{R}^3$ where $\nabla \cdot \mathbf{B} = 0$ and $\nabla \times \mathbf{B} = 0$, the components $B_i$ are harmonic ($\Delta B_i = 0$). By the Bochner–Weitzenböck identity on $\mathbb{R}^3$, the squared magnetic field strength $f(x) = \Vert{}\mathbf{B}(x)\Vert{}^2$ is strictly subharmonic:
$$\Delta \big(\Vert{}\mathbf{B}\Vert{}^2\big) = 2 \sum_{i,j=1}^3 \left(\frac{\partial B_i}{\partial x_j}\right)^2 + 2 \langle \mathbf{B}, \Delta \mathbf{B} \rangle = 2 \Vert{}\nabla \mathbf{B}\Vert{}_{\text{Frob}}^2 \ge 0.$$

By the **Elliptic Weak Maximum Principle**, for any bounded open domain $\Omega \subset \mathbb{R}^3$ with smooth boundary $\partial \Omega$:
$$\sup_{x \in \overline{\Omega}} \Vert{}\mathbf{B}(x)\Vert{}^2 = \max_{x \in \partial \Omega} \Vert{}\mathbf{B}(x)\Vert{}^2.$$
Similarly, for the difference $\delta \mathbf{B} = \mathbf{B}_1 - \mathbf{B}_2$ of two vacuum fields, $\Vert{}\delta \mathbf{B}\Vert{}^2$ is subharmonic, so its volumetric $L^\infty(\Omega)$ error is bounded entirely by its surface enclosure on $\partial \Omega$.

### 2.2 Target Kernel Specification & Sanity Check
```lean
/-- Bochner identity and subharmonicity contract for smooth vector fields on Ω ⊂ ℝ³ -/
structure IsSubharmonicScalar (Ω : Set ℝ³) (f : ℝ³ → ℝ) : Prop where
  is_open  : IsOpen Ω
  smooth   : ContDiffOn ℝ 2 f Ω
  lap_nonneg : ∀ x ∈ Ω, laplacian f x ≥ 0

/-- Target Theorem 1.1: Volumetric L∞ bounds reduce to 2D boundary certificates -/
theorem vacuum_field_norm_sq_max_on_boundary
    (Ω : Set ℝ³) (h_bdd : Bornology.IsBounded Ω)
    (B : VectorField) (h_vac : IsVacuumMagneticField Ω B)
    (h_cont : ContinuousOn B (closure Ω)) (M : ℝ)
    (h_bdry : ∀ x ∈ frontier Ω, ‖B x‖ ^ 2 ≤ M) :
    ∀ x ∈ closure Ω, ‖B x‖ ^ 2 ≤ M := by
  sorry

```

* **Sanity Check:** Verify that a constant non-zero field $\mathbf{B}(x) = \mathbf{B}_0$ satisfies `laplacian (fun x => ‖B x‖^2) x = 0` and attains its maximum on $\partial \Omega$, while ruling out strict interior local minima whenever $\nabla \mathbf{B} \neq 0$.

---

## 3. Stage 2: Sturm–Liouville Comparison for Ideal MHD Ballooning & Mercier Stability

### 3.1 Mathematical Formulation

At finite plasma pressure ($\beta > 0$), macroscopic stability against pressure-driven modes localized around bad-curvature field lines is governed by the **Connor–Hastie–Taylor Ideal Ballooning Equation**. Along each magnetic field line parameterized by arc length $l \in [-L, L]$, high-mode-number perturbations reduce to a 1D symmetric Sturm–Liouville eigenvalue problem:


$$\mathcal{L}_{\text{ball}}[X](l) := -\frac{d}{dl}\left( P(l) \frac{dX}{dl} \right) + Q(l) X(l) = \lambda W(l) X(l), \qquad X(\pm L) = 0,$$


where:

* $P(l) = \frac{\Vert{}\nabla \alpha\Vert{}^2}{B(l)} > 0$ is the field-line bending stiffness (strictly positive),
* $Q(l) = -\frac{2 \mu_0}{B(l)^2} \frac{dp}{d\psi} (\mathbf{b} \times \boldsymbol{\kappa}) \cdot \nabla \alpha$ is the normal/geodesic curvature pressure-drive potential, and
* $W(l) > 0$ is a positive inertial weight.

By **Sturm's Comparison Theorem** (and the Barta / Allegretto–Piepenbrink positivity theorem), the lowest eigenvalue satisfies $\lambda_0 > 0$ (meaning the field line is strictly stable to ideal ballooning modes on $[-L, L]$) **if and only if** there exists a smooth witness function $w : [-L, L] \to \mathbb{R}$ such that:


$$w(l) > 0 \quad \text{and} \quad -\frac{d}{dl}\left( P(l) \frac{dw}{dl} \right) + Q(l) w(l) > 0 \qquad \forall l \in [-L, L].$$

**Verification Payoff:** Instead of formalizing an eigenvalue solver in Lean 4, an external oracle supplies a simple finite Fourier/polynomial witness $w(l)$, and Lean 4 certifies the two pointwise interval inequalities $w(l) > 0$ and $\mathcal{L}_{\text{ball}}[w](l) > 0$ on $[-L, L]$.

### 3.2 Target Kernel Specification & Sanity Check

```lean
/-- Coefficients of the 1D Sturm-Liouville ballooning operator on [-L, L] -/
structure BallooningOperator (L : ℝ) where
  P : ℝ → ℝ
  Q : ℝ → ℝ
  hL : 0 < L
  hP_pos : ∀ l ∈ Set.Icc (-L) L, 0 < P l

/-- Sturm-Barta Positivity Certificate: existence of a strictly positive supersolution w -/
structure BallooningStabilityCertificate (op : BallooningOperator L) (w : ℝ → ℝ) : Prop where
  smooth_w : ContDiffOn ℝ 2 w (Set.Icc (-L) L)
  w_pos    : ∀ l ∈ Set.Icc (-L) L, 0 < w l
  super_sol : ∀ l ∈ Set.Icc (-L) L,
    - deriv (fun s => op.P s * deriv w s) l + op.Q l * w l > 0

/-- Target Theorem 2.1: A Barta supersolution certificate implies quadratic form coercivity -/
theorem ballooning_energy_pos_of_certificate
    (op : BallooningOperator L) (w : ℝ → ℝ)
    (cert : BallooningStabilityCertificate op w)
    (ξ : ℝ → ℝ) (hξ_smooth : ContDiffOn ℝ 1 ξ (Set.Icc (-L) L))
    (hξ_bc : ξ (-L) = 0 ∧ ξ L = 0) (hξ_nonzero : ∃ l ∈ Set.Ioo (-L) L, ξ l ≠ 0) :
    ∫ l in (-L)..L, (op.P l * (deriv ξ l) ^ 2 + op.Q l * (ξ l) ^ 2) > 0 := by
  -- Proof via Picone's identity:
  -- P (ξ')² + Q ξ² = P (ξ' - (w'/w) ξ)² + (-(P w')' + Q w)/w * ξ² > 0
  sorry

```

* **Mathematical Elegance (Picone's Identity):** Notice that proving `ballooning_energy_pos_of_certificate` does not even require spectral theory in Mathlib—it follows in 10 lines of algebra from **Picone's differential identity** and integration by parts!
* **Sanity Check:** Verify that if $Q(l) \ge 0$ everywhere (purely favorable curvature), the constant witness $w(l) = 1$ immediately satisfies `BallooningStabilityCertificate` whenever $Q > 0$.

---

## 4. Stage 3: Parabolic Comparison & Barrier Certificates for 1D Radial Transport

### 4.1 Mathematical Formulation

The evolution of the flux-surface-averaged plasma temperature profile $T(\psi, t)$ on $\psi \in [0, 1]$ is governed by the nonlinear parabolic PDE:


$$\frac{\partial T}{\partial t} = \mathcal{N}[T](\psi, t) := \frac{1}{V'(\psi)} \frac{\partial}{\partial \psi}\left( V'(\psi) D(\psi, T, \partial_\psi T) \frac{\partial T}{\partial \psi} \right) + S_{\text{heat}}(\psi, T) - L_{\text{loss}}(\psi, T).$$

By the **Parabolic Comparison Principle (Nagumo's Lemma)**, if a stationary smooth lower-barrier profile $\underline{T} : [0, 1] \to \mathbb{R}_{>0}$ satisfies:

1. **Strict Differential Subsolution:** $\mathcal{N}[\underline{T}](\psi) > 0$ for all $\psi \in (0, 1)$,
2. **Magnetic Axis Neumann Condition:** $\partial_\psi \underline{T}(0) = 0$ with limiting radial flux vanishing, and
3. **Edge Boundary Margin:** $\underline{T}(1) \le T_{\text{edge}}$,

then any classical solution $T(\psi, t)$ starting above the barrier ($T(\psi, 0) \ge \underline{T}(\psi)$) remains strictly above the barrier for all time:


$$T(\psi, t) \ge \underline{T}(\psi) \qquad \forall \psi \in [0, 1], \;\forall t \ge 0.$$


Conversely, a supersolution $\overline{T}(\psi)$ with $\mathcal{N}[\overline{T}](\psi) < 0$ certifies a strict upper bound (preventing thermal runaway or wall heat-flux overload).

### 4.2 Target Kernel Specification & Sanity Check

```lean
/-- Stationary Lower-Barrier Certificate for 1D Radial Transport -/
structure TransportLowerBarrierCertificate
    (N_op : (ℝ → ℝ) → ℝ → ℝ) (T_sub : ℝ → ℝ) (T_edge : ℝ) : Prop where
  pos_profile : ∀ ψ ∈ Set.Icc 0 1, 0 < T_sub ψ
  axis_symm   : deriv T_sub 0 = 0
  edge_bound  : T_sub 1 ≤ T_edge
  strict_sub  : ∀ ψ ∈ Set.Ioo 0 1, N_op T_sub ψ > 0

```

* **Sanity Check:** Prove that at any minimum point $\psi_0 \in (0, 1)$ of the difference $e(\psi, t) = T(\psi, t) - \underline{T}(\psi)$ where $e(\psi_0, t_0) = 0$, $\partial_\psi e(\psi_0, t_0) = 0$, and $\partial_{\psi\psi} e(\psi_0, t_0) \ge 0$, ellipticity of $D > 0$ forces $\partial_t e(\psi_0, t_0) > 0$ (ruling out first-time crossing).

---

## 5. Stage 4: A Posteriori Newton–Kantorovich & Radii Polynomials for 3D Finite-$\beta$ Equilibria

### 5.1 Mathematical Formulation

To certify a full 3D finite-$\beta$ MHD equilibrium computed by a spectral code like `DESC` (which represents flux surfaces $\bar{u} = (R_{l,m,n}, Z_{l,m,n}, \lambda_{l,m,n})$ as Chebyshev–Fourier polynomials), we formulate the equilibrium force balance as a nonlinear zero-finding problem on a Banach algebra of analytic Fourier–Chebyshev sequences $X = \ell^1_\nu$:


$$F(u) := \mathbf{J}(u) \times \mathbf{B}(u) - \nabla p = 0.$$

Given an approximate numerical equilibrium $\bar{u} \in X$ and an approximate finite-dimensional Jacobian inverse $A \approx DF(\bar{u})^{-1}$, we define the Newton-like fixed-point operator $T(u) = u - A F(u)$. Suppose we compute three rigorous interval bounds:

1. **Residual Defect Bound $Y_0$:** $\Vert{}A F(\bar{u})\Vert{}_X \le Y_0$,
2. **Approximate Inverse Defect $Z_0, Z_1$:** $\Vert{}I - A \, DF(\bar{u})\Vert{}_{\mathcal{B}(X)} \le Z_1 < 1$,
3. **Quadratic Lipschitz Hessian Bound $Z_2$:** $\Vert{}A \big(DF(u) - DF(\bar{u})\big)\Vert{}_{\mathcal{B}(X)} \le Z_2 \Vert{}u - \bar{u}\Vert{}_X$ on the ball $\overline{B}_r(\bar{u})$.

Define the **Radii Polynomial**:


$$p(r) := \frac{1}{2} Z_2 r^2 - (1 - Z_1) r + Y_0.$$

**The Radii Polynomial Theorem (van den Berg–Lessard / Nakao–Plum):** If there exists a radius $r_0 > 0$ such that $p(r_0) < 0$, then $T : \overline{B}_{r_0}(\bar{u}) \to \overline{B}_{r_0}(\bar{u})$ is a strict contraction mapping on the complete metric space $\overline{B}_{r_0}(\bar{u}) \subset X$. By Banach's Fixed-Point Theorem (already in `Mathlib.Topology.MetricSpace.Contracting`), there exists a **unique true continuum MHD equilibrium $u^* \in \overline{B}_{r_0}(\bar{u})$** satisfying $F(u^*) = 0$ and:


$$\Vert{}u^* - \bar{u}\Vert{}_X \le r_0.$$

### 5.2 Target Kernel Specification & Sanity Check

```lean
/-- Abstract Radii Polynomial Certificate around an oracle candidate u_bar in a Banach space X -/
structure RadiiPolynomialCertificate
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X) (A : X →L[ℝ] X) (u_bar : X)
    (Y0 Z1 Z2 r0 : ℝ) : Prop where
  r0_pos      : 0 < r0
  A_injective : Function.Injective A
  residual_bd : ‖A (F u_bar)‖ ≤ Y0
  lin_defect  : ∀ v ∈ Metric.closedBall u_bar r0,
    ‖(ContinuousLinearMap.id ℝ X - A.comp (fderiv ℝ F u_bar)) (v - u_bar)‖ ≤ Z1 * ‖v - u_bar‖
  quad_defect : ∀ v w ∈ Metric.closedBall u_bar r0,
    ‖A (fderiv ℝ F v (w - v) - fderiv ℝ F u_bar (w - v))‖ ≤ Z2 * r0 * ‖w - v‖
  poly_neg    : (1 / 2) * Z2 * r0 ^ 2 - (1 - Z1) * r0 + Y0 < 0

/-- Target Theorem 4.1: Radii polynomial negativity implies existence and uniqueness
    of a true continuum PDE solution u* within distance r0 of the oracle candidate u_bar! -/
theorem exists_unique_solution_of_radii_polynomial
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X) (A : X →L[ℝ] X) (u_bar : X) (Y0 Z1 Z2 r0 : ℝ)
    (hF_diff : ∀ v ∈ Metric.closedBall u_bar r0, DifferentiableAt ℝ F v)
    (cert : RadiiPolynomialCertificate F A u_bar Y0 Z1 Z2 r0) :
    ∃! u_star ∈ Metric.closedBall u_bar r0, F u_star = 0 := by
  -- Reduces directly to Mathlib's ContractingWith.fixedPoint on T(u) = u - A(F(u))!
  sorry

```

* **Sanity Check:** Note the explicit hypothesis `A_injective : Function.Injective A` in `RadiiPolynomialCertificate`! Without `A_injective`, setting $A = 0$, $Y_0 = 0$, $Z_1 = 0$ would falsely "certify" a zero of $F$ around *any* point $\bar{u}$. Requiring `A_injective` guarantees $T(u^*) = u^* \iff A(F(u^*)) = 0 \iff F(u^*) = 0$.

---

## 6. Stage 5: KAM & Converse KAM Action-Gradient Certificates for Island Widths

### 6.1 Mathematical Formulation

Magnetic field lines are trajectories of a $1\frac{1}{2}$-degree-of-freedom Hamiltonian flow generated by the poloidal flux $\psi_p(\psi_t, \theta, \phi)$, inducing an area-preserving Poincaré return map $f : A \to A$ on a poloidal annulus $A = [\psi_-, \psi_+] \times S^1$.

* **Converse KAM Non-Existence Bounds (MacKay 1989):** Provides an algebraic certificate proving when invariant flux surfaces are destroyed by resonant island overlap.
* **Resonant Island Half-Width Bound:** Near a rational surface $\iota(\psi_{m,n}) = n/m$ with magnetic shear $\iota'(\psi_{m,n}) \neq 0$ and resonant magnetic perturbation harmonic $b_{m,n}$, the pendulum comparison Hamiltonian bounds the radial island half-width by:

$$\Delta \psi_{\text{island}} \le 2 \sqrt{\left\vert{}\frac{R_0 \, b_{m,n}}{m \, \iota'(\psi_{m,n})}\right\vert{}} + R_{\text{rem}}.$$



Certifying $\sum_{(m,n) \in \mathcal{R}} \Delta \psi_{m,n} < d_{\text{sep}}$ (Chirikov non-overlap margin) guarantees that low-order island chains remain isolated and do not trigger stochastic field-line loss.

---

## 7. Summary of Milestone Deliverables & Dependencies

| Milestone | PDE / Physical Regime | Mathematical Engine | Primary Lean 4 Target |
| --- | --- | --- | --- |
| **Milestone A** *(Short-Term)* | 3D Vacuum Field Bounds ($\Delta \Vert{}\mathbf{B}\Vert{}^2 \ge 0$) | Bochner Identity & Elliptic Maximum Principle | `vacuum_field_norm_sq_max_on_boundary` |
| **Milestone B** *(Short-Term)* | Ideal MHD Ballooning & Mercier Stability | Sturm–Liouville Comparison & Picone's Identity | `ballooning_energy_pos_of_certificate` |
| **Milestone C** *(Medium-Term)* | 1D Nonlinear Radial Transport Profiles | Nagumo Parabolic Comparison & Barrier Functions | `TransportLowerBarrierCertificate` |
| **Milestone D** *(Medium-Term)* | 5D Trapped-Particle Microturbulence Bound | Symplectic Rearrangement & Available Energy $\widehat{\mathcal{A}}$ | `SatisfiesMaximumJ` & `AvailableEnergyFluxTube` |
| **Milestone E** *(Long-Term)* | Full 3D Finite-$\beta$ MHS Equilibrium ($\mathbf{J}\times\mathbf{B}=\nabla p$) | Newton–Kantorovich Radii Polynomials on $\ell^1_\nu$ | `exists_unique_solution_of_radii_polynomial` |

```

```