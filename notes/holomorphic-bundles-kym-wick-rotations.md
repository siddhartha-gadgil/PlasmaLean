# Formalization Note: Holomorphic Foliations, Kähler–Yang–Mills Moment Maps, and Para-Kähler Wick Rotations in PlasmaLean

**Workstream:** `geometry-and-fields` / `plasma-models-and-equilibrium` / `mhd-stability`  
**Status:** Blueprint & Advanced Algebraic-Geometric Specifications  
**Target Modules:**  
- `PlasmaLean.Geometry.HolomorphicFoliation`  
- `PlasmaLean.Equilibrium.KYMMomentMap`  
- `PlasmaLean.Stability.ParaKahlerWick`

---

## 1. Motivation & Advanced Geometric Perspective

When analyzing 3D magnetohydrostatic (MHS) equilibria ($\mathbf{J} \times \mathbf{B} = \nabla p$), quasisymmetry obstructions, and time-dependent MHD stability, standard coordinate vector calculus can obscure deep algebraic invariants. This note provides three structural dictionary bridges—from **Holomorphic Line Bundles**, **Kähler–Yang–Mills (KYM) / Cosmic String Moment Maps**, and **Lorentzian / Para-Kähler Wick Rotations**—enabling agents and mathematicians to import deformation-invariance, Futaki-type obstructions, and Kempf–Ness coercivity bounds directly into **PlasmaLean**.

---

## 2. Module 1: Holomorphic Line Bundles over $\Sigma_\psi \times I$ & Deformation Invariance

### 2.1 Mathematical Formulation
* **Foliation as a Family of Complex Tori:** Every regular toroidal flux surface $\Sigma_\psi \cong T^2$ ($\psi \in I = [\psi_0, \psi_1]$) inherits a Riemannian metric $g_\psi = g\vert{}_{\Sigma_\psi}$. The 2D Hodge star $\star_\psi : \Omega^1(\Sigma_\psi) \to \Omega^1(\Sigma_\psi)$ satisfies $\star_\psi^2 = -\mathrm{Id}$, defining a canonical integrable complex structure $J_\psi$ and identifying $(\Sigma_\psi, J_\psi)$ with a 1D complex torus $\mathcal{E}_\psi = \mathbb{C} / (\mathbb{Z} + \tau(\psi)\mathbb{Z})$ with modular parameter $\tau(\psi) \in \mathbb{H}$.
* **Magnetic Field as Unitary Connection Curvature:** The closed magnetic 2-form $\omega_B = \iota_{\mathbf{B}}\mathrm{vol}_g$ ($d\omega_B = 0$) restricted to $\Sigma_\psi \times I$ represents (up to flux normalization) the curvature $i F_\nabla = \omega_B$ of a Hermitian line bundle $(L, h, \nabla) \to \Sigma_\psi \times I$.
* **Algebro-Geometric Moduli & Perturbation Rigidity:** When equilibrium profiles (such as pressure $p(\psi)$, temperature $T(\psi)$, or Boozer covariant currents $G(\psi), I(\psi)$) are parameterized via cohomological invariants or norms of holomorphic sections $s \in H^0(\mathcal{E}_\psi, L_\psi^{\otimes m})$ (Jacobi theta functions $\vartheta(z; \tau(\psi))$):
  1. By **Riemann–Roch / Siu Deformation Invariance**, the dimension $h^0(\mathcal{E}_\psi, L_\psi^{\otimes m}) = m \cdot \mathrm{deg}(L_\psi)$ is a topological integer invariant under smooth perturbations of the metric $g_\psi$ and modular parameter $\tau(\psi)$.
  2. By **Bergman Kernel / Szegő Projection Coercivity**, holomorphic ansätze on $\mathcal{E}_\psi$ automatically satisfy elliptic interior derivative bounds (Cauchy estimates) without high-frequency numerical ringing.

> **Correction (2026-10-20):** $\mathbf{B}$ is tangent to $\Sigma_\psi$, so for tangent vectors $X, Y$ we get $\omega_B(X,Y) = \mathrm{vol}(\mathbf{B}, X, Y) = 0$: **the restriction $\omega_B|_{\Sigma_\psi}$ vanishes identically.** Any line bundle on $\Sigma_\psi$ whose curvature is $\omega_B|_{\Sigma_\psi}$ is therefore **flat, of degree 0**. That makes the claims above wrong as stated:
> - "$h^0 = m\cdot\deg(L_\psi)$" is wrong. For a flat bundle, $h^0(L^{\otimes m})$ is $1$ if $L^{\otimes m}$ is holomorphically trivial and $0$ otherwise, so it is *not* deformation invariant. It jumps on a dense set of holonomies.
> - A positive degree, and hence theta-function sections, cannot come from $\omega_B$.
> - On the shell $\Sigma\times I$, $H^2(\Sigma\times I)\cong H^2(T^2)$ is detected by restriction to a slice, where $\omega_B$ vanishes. So $\omega_B$ is exact on the shell, and the bundle there is topologically trivial as well.
>
> What survives: the flat connection $A|_{\Sigma_\psi}$ (with $\nabla\times A = \mathbf{B}$) has periods equal to the toroidal flux (poloidal cycle) and the poloidal flux up to an additive gauge constant (toroidal cycle). The rotational transform is the ratio of the periods of the closed 1-form $\iota_{\mathbf{B}}\sigma$ ($\sigma$ the Leray area form, $d\psi\wedge\sigma = \mathrm{vol}$), i.e. $\iota = d\Phi_p/d\Phi_t$. It is *not* the holonomy itself. $\tau(\psi)$ is the conformal modulus. See `notes/theory/flux-surface-holonomy.md` for the verdict and the useful replacement statement (a Hodge period inequality).

### 2.2 Lean 4 kernel contract — REFUTED, not implemented

> **REFUTED / not implemented; see [implementation plan §1](implementation-plan.md).** The original block proposed a structure `HolomorphicFluxFamily` with a positive `flux_degree` and a definition `holomorphicSectionDim fam m := m * flux_degree`, with a "deformation invariance" theorem true by definition. The bundle induced by ω_B on a flux surface has degree 0, so `flux_degree > 0` is false; nothing of this exists in `PlasmaLean/`. The code was removed so that it cannot be mistaken for a live contract.

> **Correction (2026-10-20):** `holomorphicSectionDim` is *defined* as `m * flux_degree`, so `holomorphicSectionDim_deformation_invariant` is true by definition and checks no mathematics: no sections, Riemann–Roch or τ-dependence appear anywhere. The hypothesis `h_deg_pos : 0 < flux_degree` is also physically wrong, because the bundle induced by $\omega_B$ on a flux surface has degree 0 (see the correction above). Do not formalize this structure. Re-target it on flux-surface periods and τ (compare `Challenge6_ConformalTorusModulus`), as described in `notes/theory/flux-surface-holonomy.md`.

---

## 3. Module 2: Kähler–Yang–Mills (KYM), Cosmic Strings, Futaki Obstructions & GIT Stability

### 3.1 Mathematical Formulation

* **Dimensional Reduction to Cosmic Strings / Vortices:** The coupled Kähler–Yang–Mills equations on a fibered manifold dimensionally reduce on a Riemann surface $(\Sigma, \omega_\Sigma)$ to the **gravitating vortex / critical cosmic string equations** (Álvarez-Consul, Garcia-Fernandez, Hitchin):

$$\Lambda_{\omega_\Sigma} F_A + \frac{1}{2}\big(|s|_h^2 - c\big) = 0, \qquad \bar{\partial}_A s = 0, \qquad S(\omega_\Sigma) - \alpha \Delta \ln |s|_h^2 = \text{const}.$$



Under the identification $\psi = \ln |s|_h^2$, this system is the **complex-geometric avatar of the Grad–Shafranov / MHS equilibrium equation** $\Delta^* \psi + \mu_0 R^2 p'(\psi) + I(\psi)I'(\psi) = 0$.
* **MHS Force Balance as an Infinite-Dimensional Moment Map:** Following Arnold and Donaldson–Fujiki, on the space $\mathcal{M}$ of solenoidal fields and adapted surface metrics with symplectic structure $\boldsymbol{\Omega}$, the action of the group $\mathcal{G} = \mathrm{SDiff}(M)$ of volume-preserving diffeomorphisms has moment map:

$$\boldsymbol{\mu}(\mathbf{B}, p) = \mathbf{J} \times \mathbf{B} - \nabla p = 0.$$


* **Futaki-Type Obstruction to Quasisymmetry & Equilibrium:** Let $\mathfrak{h}$ be the Lie algebra of candidate hidden symmetry vector fields $\mathbf{u}$ on $M$ (e.g., $(M,N)$-quasisymmetry generators $\mathbf{u} = N\partial_\theta + M\partial_\phi$). Define the **MHD Futaki Character** $\mathcal{F}_{\text{MHD}} : \mathfrak{h} \to \mathbb{R}$ by integrating the moment-map defect against the Hamiltonian/stream potential $f_{\mathbf{u}}$ of $\mathbf{u}$:

$$\mathcal{F}_{\text{MHD}}(\mathbf{u}) := \int_M \langle \mathbf{J} \times \mathbf{B} - \nabla p, \, \xi_{\mathbf{u}} \rangle \, \mathrm{vol}_g + \int_M f_{\mathbf{u}} \big(\mathcal{L}_{\mathbf{u}} |\mathbf{B}|^2\big) \, \mathrm{vol}_g.$$



If $\mathcal{F}_{\text{MHD}}(\mathbf{u}) \neq 0$, it acts as a **rigorous cohomological obstruction** proving that no exact quasisymmetric equilibrium exists in that ansatz class (explaining the Garren–Boozer $O(r^3)$ obstruction conceptually!).
* **Kempf–Ness & Mabuchi K-Energy Coercivity:** By the infinite-dimensional Kempf–Ness principle, finding a zero of the moment map $\boldsymbol{\mu}(\mathbf{B}, p) = 0$ is equivalent to minimizing a convex **Kempf–Ness / Kruskal–Kulsrud energy functional** $\mathcal{M}_{\text{KN}}$ along the complexified orbit. Proving strong convexity ($D^2 \mathcal{M}_{\text{KN}} \ge \gamma I > 0$) yields both existence and uniqueness of the equilibrium.

### 3.2 Lean 4 kernel contract — REFUTED as a contract, not implemented

> **REFUTED / not implemented; see [implementation plan §1](implementation-plan.md).** The original block proposed `FutakiObstructionCertificate μ u F` (⟪μ x, u⟫ = F for every x, with F ≠ 0) and the trivial consequence `no_equilibrium_of_futaki_obstruction : ¬ ∃ x, μ x = 0`. The implication is correct but vacuous: all the content is in the hypothesis, which no theorem produces for any MHD family. Nothing of this exists in `PlasmaLean/`; the code was removed.

> **Correction (2026-10-20), vacuous contract and unchecked claims:** `no_equilibrium_of_futaki_obstruction` is correct, but its whole content sits in the hypothesis `pairing_const`: ⟪μ x, u_test⟫ must equal the *same* constant for **every** x in the ansatz family. No theorem here produces that hypothesis for any MHD family. The claim that $\mathcal{F}_{\text{MHD}}$ is independent of the representative (needed for it to be an "obstruction") is unproved. So is the claim that it "explains the Garren–Boozer $O(r^3)$ obstruction", and so are the identifications in §3.1 (Grad–Shafranov as the vortex equation via $\psi=\ln|s|_h^2$, and $\mathbf{J}\times\mathbf{B}-\nabla p$ as a moment map with a Kempf–Ness functional). All of these are heuristics. The contract stays out of the library until a theorem derives `pairing_const` for a specific near-axis ansatz. The honest test is whether it reproduces the Garren–Boozer count (implementation plan, track T10).

---

## 4. Module 3: "Wick Rotation" from Elliptic Kähler/Gauge Theory to Hyperbolic MHD

### 4.1 Mathematical Formulation

When moving from 2D elliptic cross-sections to either **(a) 3D steady MHD with real field-line characteristics** or **(b) 3+1D time-dependent hyperbolic MHD**, elliptic Kähler/Yang–Mills invariants survive via two distinct "Wick rotations":

1. **Spatial Wick Rotation ($i^2 = -1 \longrightarrow j^2 = +1$, Para-Kähler Geometry):**
* Replace the complex ring $\mathbb{C} = \mathbb{R}[i]/(i^2 + 1)$ with the **para-complex (split-complex) ring** $\mathbb{D} = \mathbb{R}[j]/(j^2 - 1)$.
* A **Para-Kähler structure** $(M, g, K)$ satisfies $K^2 = +\mathrm{Id}$ and $g(KX, KY) = -g(X, Y)$, splitting $TM = T^+M \oplus T^-M$ into two integrable null/characteristic eigenbundles corresponding to the **forward and backward Alfvén characteristics** $\mathbf{z}_\pm = \mathbf{v} \pm \mathbf{b}/\sqrt{\mu_0 \rho}$!
* The Cauchy–Riemann operator $\bar{\partial} = \partial_x + i\partial_y$ Wick-rotates into the hyperbolic wave/characteristic operator $\partial_x + j\partial_y$, turning holomorphic factorization directly into the **Elsässer null condition** $(\mathbf{z}_\mp \cdot \nabla)\mathbf{z}_\pm$.


2. **Temporal Wick Rotation ($t_{\text{Eucl}} \longrightarrow i t$, Bogomolny $\longrightarrow$ Morawetz/Klainerman Multipliers):**
* In Euclidean Yang–Mills–Higgs theory, completing the square gives the Bogomolny topological lower bound $\frac{1}{2}\int \|F_A \mp \star F_A\|^2 \ge 0$.
* Under Lorentzian Wick rotation, the self-dual completion-of-squares transforms into the **null decomposition of the stress-energy tensor** $T(\mathbf{z}_+, \mathbf{z}_-)$ along the forward and backward Alfvén cones, providing positive-definite commuted energy currents $\nabla^\mu (T_{\mu\nu} X^\nu)$ even in the hyperbolic regime.



### 4.2 Lean 4 kernel contract — historical sketch, not the library API

> **Not implemented in this form.** The original block (a structure `ElsasserParaKahlerState` and an identity left as `sorry`) is superseded: the true algebraic identities ‖z₊‖² + ‖z₋‖² = 2(‖v‖² + ‖b‖²) and ‖z₊‖² − ‖z₋‖² = 4⟪v, b⟫ are proved in `PlasmaLean/Theory/Stability/Elsasser.lean` (`energy_identity`, `cross_helicity_identity`). The "topological degree analogue" reading is a heuristic. The code was removed.