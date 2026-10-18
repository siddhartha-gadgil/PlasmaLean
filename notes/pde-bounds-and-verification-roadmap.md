# Formalization Note: Roadmap for Rigorous PDE Bounds, Comparison Theorems, and A Posteriori Certificates

**Workstream:** `verified-numerics` / `plasma-models-and-equilibrium` / `mhd-stability`  
**Status:** Forward Roadmap (Post-Vacuum Demonstrator)  
**Target Modules:** `PlasmaLean.Numerics.RadiiPolynomial`, `PlasmaLean.Stability.SturmComparison`, `PlasmaLean.Transport.BarrierCertificates`, `PlasmaLean.Stability.CommutedEnergy`

---

## 1. Architectural Philosophy: Untrusted Oracles + Small-Kernel Certificates

With the vacuum Biot–Savart derivatives, Lipschitz coil-tolerance bounds, and vacuum-fixture certificates already compiled, the next phase of **PlasmaLean** addresses systems governed by nonlinear partial differential equations (PDEs):
1. **3D Magnetohydrostatic (MHS) Equilibrium:** $\mathbf{J} \times \mathbf{B} = \nabla p, \quad \nabla \times \mathbf{B} = \mu_0 \mathbf{J}, \quad \nabla \cdot \mathbf{B} = 0$.
2. **Ideal MHD Linear & Nonlinear Stability:** Positivity of the second variation of energy $\delta^2 W(\xi, \xi) > 0$, 1D ballooning ODEs along field lines, and pointwise $L^\infty$ plasma displacement bounds.
3. **Nonlinear Radial Energy Transport:** Parabolic reaction-diffusion equations for temperature $T(\psi, t)$ and density $n(\psi, t)$ across nested flux surfaces.

Rather than formalizing finite-element or spectral PDE solvers inside Lean 4, **PlasmaLean** treats external numerical codes (such as `DESC`, `VMEC`, `SIMSOPT`, or AI synthesis agents) as **untrusted oracles**. The oracle emits a concrete finite-dimensional candidate (e.g., Chebyshev–Fourier–Zernike coefficients $\bar{u}$, a positive Sturm–Liouville test function $w(l)$, a polynomial barrier profile $\underline{T}(\psi)$, or a Summation-By-Parts operator), and the **PlasmaLean Small Kernel** verifies an *a posteriori* inequality, comparison theorem, or commuted energy estimate that mathematically bounds the true continuum PDE solution.

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
  is_open    : IsOpen Ω
  smooth     : ContDiffOn ℝ 2 f Ω
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
  smooth_w  : ContDiffOn ℝ 2 w (Set.Icc (-L) L)
  w_pos     : ∀ l ∈ Set.Icc (-L) L, 0 < w l
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

To certify a full 3D finite-$\beta$ MHD equilibrium computed by a spectral code like `DESC` (which represents flux surfaces $\bar{u} = (R_{l,m,n}, Z_{l,m,n}, \lambda_{l,m,n})$ as Zernike–Fourier polynomials), we formulate the equilibrium force balance as a nonlinear zero-finding problem on a Banach algebra of analytic sequences $X = \ell^1_\nu$:


$$F(u) := \mathbf{J}(u) \times \mathbf{B}(u) - \nabla p = 0.$$

Given an approximate numerical equilibrium $\bar{u} \in X$ and an approximate finite-dimensional Jacobian inverse $A \approx DF(\bar{u})^{-1}$, we define the Newton-like fixed-point operator $T(u) = u - A F(u)$ and bound:

1. **Residual Defect Bound $Y_0$:** $\Vert{}A F(\bar{u})\Vert{}_X \le Y_0$,
2. **Approximate Inverse Defect $Z_1$:** $\Vert{}I - A \, DF(\bar{u})\Vert{}_{\mathcal{B}(X)} \le Z_1 < 1$,
3. **Quadratic Lipschitz Hessian Bound $Z_2$:** $\Vert{}A \big(DF(u) - DF(\bar{u})\big)\Vert{}_{\mathcal{B}(X)} \le Z_2 \Vert{}u - \bar{u}\Vert{}_X$ on $\overline{B}_r(\bar{u})$.

Define the **Radii Polynomial**:


$$p(r) := \frac{1}{2} Z_2 r^2 - (1 - Z_1) r + Y_0.$$

**The Radii Polynomial Theorem (van den Berg–Lessard / Nakao–Plum):** If there exists $r_0 > 0$ such that $p(r_0) < 0$, then $T : \overline{B}_{r_0}(\bar{u}) \to \overline{B}_{r_0}(\bar{u})$ is a strict contraction on $\overline{B}_{r_0}(\bar{u}) \subset X$. By Banach's Fixed-Point Theorem (`Mathlib.Topology.MetricSpace.Contracting`), there exists a **unique true continuum MHD equilibrium $u^* \in \overline{B}_{r_0}(\bar{u})$** satisfying $F(u^*) = 0$ and $\Vert{}u^* - \bar{u}\Vert{}_X \le r_0$.

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

* **Sanity Check:** The explicit hypothesis `A_injective : Function.Injective A` prevents the vacuous bug $A = 0, Y_0 = 0, Z_1 = 0$, guaranteeing that a fixed point of $T(u) = u - A(F(u))$ is genuinely a root $F(u^*) = 0$.

---

## 6. Stage 5: KAM & Converse KAM Action-Gradient Certificates for Island Widths

### 6.1 Mathematical Formulation

Magnetic field lines are trajectories of a $1\frac{1}{2}$-degree-of-freedom Hamiltonian flow generated by the poloidal flux $\psi_p(\psi_t, \theta, \phi)$.

* **Resonant Island Half-Width Bound:** Near a rational surface $\iota(\psi_{m,n}) = n/m$ with magnetic shear $\iota'(\psi_{m,n}) \neq 0$ and resonant magnetic perturbation harmonic $b_{m,n}$, the pendulum comparison Hamiltonian bounds the radial island half-width by:

$$\Delta \psi_{\text{island}} \le 2 \sqrt{\left\vert{}\frac{R_0 \, b_{m,n}}{m \, \iota'(\psi_{m,n})}\right\vert{}} + R_{\text{rem}}.$$



Certifying $\sum_{(m,n) \in \mathcal{R}} \Delta \psi_{m,n} < d_{\text{sep}}$ (Chirikov non-overlap margin) guarantees that low-order island chains remain isolated.

---

## 7. Stage 6: Klainerman–Sobolev Commuted Vector-Field Estimates & Elsässer Null Structure

### 7.1 Mathematical Formulation (Adapting Mathematical Relativity to Stellarators)

In General Relativity, the Christodoulou–Klainerman proof of the stability of Minkowski space relies on two pillars: **(1) the Vector-Field Method** (commuting the PDE with approximate Killing/conformal symmetries $\mathcal{Z}$ to bound higher Sobolev norms) and **(2) the Null Condition** (which prevents quadratic self-interaction of wave packets traveling along the same characteristic light cone).

Ideal MHD possesses the **exact same algebraic null structure** when written in **Elsässer variables** $\mathbf{z}_\pm = \mathbf{v} \pm \mathbf{b}/\sqrt{\mu_0 \rho}$ around an equilibrium field $\mathbf{B}_0 = \sqrt{\mu_0 \rho}\,\mathbf{v}_A$:


$$\left( \frac{\partial}{\partial t} \mp (\mathbf{v}_A \cdot \nabla) \right) \mathbf{z}_\pm + (\mathbf{z}_\mp \cdot \nabla) \mathbf{z}_\pm = -\nabla P_{\text{tot}}, \qquad \nabla \cdot \mathbf{z}_\pm = 0.$$


Notice that the quadratic nonlinearity $(\mathbf{z}_\mp \cdot \nabla)\mathbf{z}_\pm$ couples only counter-propagating Alfvén waves $\mathbf{z}_+$ and $\mathbf{z}_-$, never co-propagating waves $(\mathbf{z}_+ \cdot \nabla)\mathbf{z}_+$.

While a compact toroidal stellarator $M \cong D^2 \times S^1$ lacks spatial dispersion to infinity, the Klainerman–Sobolev vector-field method adapts directly to **anisotropic foliated Sobolev bounds** and **long-time $L^\infty$ plasma wall-clearance certificates**:

1. **The Quasisymmetry Commutation Vector Field:** In an $(M,N)$-quasisymmetric stellarator (with quasisymmetry defect $\epsilon_{\text{QS}} \ge 0$), the helical symmetry vector field $\mathbf{u} = N \partial_{\theta_B} + M \partial_{\phi_B}$ is tangent to flux surfaces and nearly commutes with the ideal MHD force operator $\mathbf{F}$:

$$\big\Vert{} [\mathbf{F}, \mathcal{L}_{\mathbf{u}}] \xi \big\Vert{}_{L^2(M)} \le C \, \epsilon_{\text{QS}} \, \Vert{}\xi\Vert{}_{H^2(M)}.$$


2. **Higher-Order Commuted Bernstein Energy Functional ($\mathcal{E}_m$):** Standard linear MHD stability ($\delta^2 W(\xi, \xi) \ge \gamma \Vert{}\xi\Vert{}_{H^1}^2$) only controls the $H^1(M)$ norm, which in 3D is insufficient to bound the pointwise displacement $\Vert{}\xi(x,t)\Vert{}_{L^\infty(M)}$ (since $H^1(\mathbb{R}^3) \not\hookrightarrow L^\infty(\mathbb{R}^3)$). By commuting the linearized MHD wave equation $\rho \partial_{tt} \xi = \mathbf{F}(\xi)$ with powers of the Lie derivative $\mathcal{L}_{\mathbf{u}}^k$ and magnetic field-line derivative $\nabla_\parallel^k = (\mathbf{b}_0 \cdot \nabla)^k$, we construct the **Klainerman–Sobolev Commuted Energy**:

$$\mathcal{E}_2(\xi, \dot{\xi}) := \sum_{k=0}^2 \left( \frac{1}{2} \int_M \rho \Vert{}\mathcal{L}_{\mathbf{u}}^k \dot{\xi}\Vert{}^2 \, dV + \delta^2 W\big(\mathcal{L}_{\mathbf{u}}^k \xi, \, \mathcal{L}_{\mathbf{u}}^k \xi\big) \right).$$


3. **Pointwise Wall-Clearance Guarantee via Grönwall & Sobolev Embedding:** Using elliptic regularity across flux surfaces plus 3D Sobolev embedding $H^2(M) \hookrightarrow L^\infty(M)$, bounding $\mathcal{E}_2(t) \le \mathcal{E}_2(0) e^{C \epsilon_{\text{QS}} t}$ yields a rigorous **pointwise $L^\infty$ displacement bound**:

$$\Vert{}\xi(\cdot, t)\Vert{}_{L^\infty(M)} \le C_{\text{Sob}} \sqrt{\frac{\mathcal{E}_2(0)}{\gamma}} \, e^{\frac{1}{2} C \epsilon_{\text{QS}} t} < d_{\text{wall}},$$



certifying that plasma perturbations cannot touch the vacuum vessel wall over long timescales $t \in [0, T_{\text{cert}}]$!

### 7.2 Target Kernel Specification & Sanity Check

```lean
/-- Commutator defect bound between the MHD force operator F and Lie derivative ℒ_u
    along a quasisymmetry (or approximate symmetry) vector field u. -/
structure QuasisymmetricCommutatorBound
    {H2 L2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℝ L2]
    (F : H2 → L2) (Lie_u : H2 → H2) (Lie_u_L2 : L2 → L2) (ε_QS : ℝ) : Prop where
  nonneg_defect : 0 ≤ ε_QS
  comm_bound : ∀ ξ : H2, ‖F (Lie_u ξ) - Lie_u_L2 (F ξ)‖ ≤ ε_QS * ‖ξ‖

/-- Klainerman-Sobolev Commuted Energy Certificate:
    Combines H¹ coercivity of δ²W, commutator defect ε_QS, and 3D Sobolev embedding
    to certify pointwise L∞ plasma-to-wall clearance! -/
structure CommutedWallClearanceCertificate
    (E2_init γ C_Sob ε_QS T_max d_wall : ℝ) : Prop where
  coercive_pos   : 0 < γ
  sob_pos        : 0 < C_Sob
  clearance_safe : C_Sob * Real.sqrt (E2_init / γ) * Real.exp (ε_QS * T_max / 2) < d_wall

```

* **Sanity Check:** Verify that in the limit of exact symmetry ($\epsilon_{\text{QS}} = 0$), the commuted energy $\mathcal{E}_2(t) = \mathcal{E}_2(0)$ is strictly conserved for all $t \ge 0$, and verify the Elsässer algebraic null identity $\langle (\mathbf{z}_\mp \cdot \nabla)\mathbf{z}_\pm, \mathbf{z}_\pm \rangle_{L^2(M)} = 0$ for divergence-free fields with tangent boundary conditions.

---

## 8. Stage 7: Numerical Relativity Methods — Zernike Coordinate Regularity, Constraint Damping & Summation-By-Parts (SBP)

### 8.1 Mathematical Formulation

Three numerical relativity architectures translate directly into machine-checked stellarator certificates in **PlasmaLean**:

1. **Zernike Polynomials for Coordinate-Axis Regularity ($r \to 0$):**
Just as spherical/axisymmetric numerical relativity codes (`SpEC`, `bamps`) must eliminate $1/r$ coordinate singularities at the origin, toroidal flux coordinates $(r, \theta, \phi)$ with $r = \sqrt{\psi}$ have a polar coordinate singularity at the magnetic axis $r = 0$. Expanding equilibrium quantities in **Zernike polynomials** $Z_l^m(r, \theta) = R_l^{\vert{}m\vert{}}(r) e^{i m \theta}$ (where $l - \vert{}m\vert{}$ is even and $l \ge \vert{}m\vert{}$) guarantees **exact $C^\infty$ analyticity across the magnetic axis by basis construction**, eliminating division-by-zero traps at $r = 0$ in the Lean kernel.
2. **Exterior-Calculus Constraint Preservation & Dedner–Z4 Divergence Damping:**
In numerical relativity, naive time evolution violates the Hamiltonian/momentum constraints unless constraint-damping (Generalized Harmonic / Z4) is included. In stellarator MHD, violating $\nabla \cdot \mathbf{B} = 0$ produces unphysical forces parallel to $\mathbf{B}$. In `PlasmaLean`, we enforce $\nabla \cdot \mathbf{B} = 0$ structurally either by representing $\mathbf{B}$ as the exterior derivative of a 1-form ($\omega_B = d\alpha$) or via the **Dedner–GLM hyperbolic divergence-cleaning system**:

$$\partial_t \mathbf{B} + \dots + \nabla \psi_{\text{div}} = 0, \qquad \partial_t \psi_{\text{div}} + c_h^2 \nabla \cdot \mathbf{B} = -\frac{c_h^2}{c_p^2} \psi_{\text{div}},$$



for which an exact energy identity proves that any divergence error $\nabla \cdot \mathbf{B}$ is advected away at speed $c_h$ and damped exponentially at rate $c_h^2 / c_p^2$.
3. **Summation-By-Parts (SBP) Operators for Decidable Discrete Energy Stability:**
Proving continuum integration-by-parts theorems on curved 3D manifolds requires heavy measure-theory machinery. In numerical relativity, **Summation-By-Parts (SBP)** finite-difference and spectral-element operators approximate $\partial_x$ by a matrix $D$ equipped with a symmetric positive-definite norm matrix $P = P^T > 0$ satisfying the exact algebraic identity:

$$P D + D^T P = B_{\text{bdry}} := \mathrm{diag}(-1, 0, \dots, 0, 1).$$



**Why this is ideal for Lean 4:** Because $P D + D^T P = B_{\text{bdry}}$ is a finite rational/interval matrix identity, Lean 4 can verify it **automatically by computation (`norm_num` / `decide`)**, immediately yielding a machine-checked discrete energy conservation or Lyapunov stability theorem for the discretized PDE!

### 8.2 Target Kernel Specification & Sanity Check

```lean
/-- A Summation-By-Parts (SBP) discrete derivative operator on N grid points,
    imported from Numerical Relativity to give decidable energy stability in Lean 4! -/
structure SBPOperator (N : ℕ) where
  D : Matrix (Fin N) (Fin N) ℝ
  P : Matrix (Fin N) (Fin N) ℝ
  B_bdry : Matrix (Fin N) (Fin N) ℝ
  P_symm : P.transpose = P
  P_pos_def : ∀ u : Fin N → ℝ, u ≠ 0 → dotProduct u (P.mulVec u) > 0
  sbp_identity : P * D + D.transpose * P = B_bdry

/-- Target Theorem 7.1: Any linear hyperbolic system du/dt = -c D u discretized with an
    SBP operator satisfies an exact discrete integration-by-parts energy law! -/
theorem sbp_discrete_energy_identity
    {N : ℕ} (sbp : SBPOperator N) (u : Fin N → ℝ) :
    dotProduct u ((sbp.P * sbp.D).mulVec u) =
      (1 / 2) * dotProduct u (sbp.B_bdry.mulVec u) := by
  -- Follows purely from linear algebra and sbp.sbp_identity (no measure theory needed!)
  sorry

```

* **Sanity Check:** Instantiate `SBPOperator` for a small Chebyshev–Gauss–Lobatto spectral differentiation matrix ($N = 4$) and verify `sbp_identity` automatically via `norm_num`.

---

## 9. Summary of Milestone Deliverables & Dependencies

| Milestone | PDE / Physical Regime | Mathematical Engine | Primary Lean 4 Target |
| --- | --- | --- | --- |
| **Milestone A** *(Short-Term)* | 3D Vacuum Field Bounds ($\Delta \Vert{}\mathbf{B}\Vert{}^2 \ge 0$) | Bochner Identity & Elliptic Maximum Principle | `vacuum_field_norm_sq_max_on_boundary` |
| **Milestone B** *(Short-Term)* | Ideal MHD Ballooning & Mercier Stability | Sturm–Liouville Comparison & Picone's Identity | `ballooning_energy_pos_of_certificate` |
| **Milestone C** *(Short-Term)* | Discrete Hyperbolic / Transport Stability | Numerical Relativity Summation-By-Parts (SBP) Matrices | `sbp_discrete_energy_identity` |
| **Milestone D** *(Medium-Term)* | 1D Nonlinear Radial Transport Profiles | Nagumo Parabolic Comparison & Barrier Functions | `TransportLowerBarrierCertificate` |
| **Milestone E** *(Medium-Term)* | 5D Trapped-Particle Microturbulence Bound | Symplectic Rearrangement & Available Energy $\widehat{\mathcal{A}}$ | `SatisfiesMaximumJ` & `AvailableEnergyFluxTube` |
| **Milestone F** *(Long-Term)* | Pointwise $L^\infty$ Plasma Wall-Clearance Stability | Klainerman–Sobolev Commuted Energy & Elsässer Null Structure | `CommutedWallClearanceCertificate` |
| **Milestone G** *(Long-Term)* | Full 3D Finite-$\beta$ MHS Equilibrium ($\mathbf{J}\times\mathbf{B}=\nabla p$) | Zernike Basis + Newton–Kantorovich Radii Polynomials on $\ell^1_\nu$ | `exists_unique_solution_of_radii_polynomial` |
