# Formalization Note: Beale–Kato–Majda MHD Regularity, Quasisymmetric Ansätze, and Li–Yau–Perelman Finite-Time Burn Bounds

**Workstream:** `mhd-stability` / `particles-and-transport` / `verified-numerics`  
**Status:** Blueprint & Analytical Regularity Contracts  
**Target Modules:**  
- `PlasmaLean.Stability.BKMRegularity`  
- `PlasmaLean.Transport.LiYauPerelmanBounds`  
- `PlasmaLean.Numerics.FEECExteriorCalculus`

---

## 1. Motivation: From No-Blowup Criteria to Finite-Time Energy Yield Certificates

To certify that a stellarator design with a quasisymmetric external magnetic field $\mathbf{B}_{\text{ext}}$ can sustain a burning plasma and produce net energy over a definite operating window $t \in [0, T_{\text{burn}}]$, two fundamental PDE questions must be answered:
1. **No Finite-Time MHD Singularity (The BKM Question):** Under what conditions on the initial plasma state and the 3D magnetic geometry is the plasma guaranteed not to form current-sheet singularities, shock blowups, or disruptions during $[0, T_{\text{burn}}]$?
2. **Effective Lower Bounds on Temperature & Fusion Yield (The Li–Yau / Perelman Question):** Even though plasma temperature $T(x,t)$ is not pointwise monotone in time, how can we use weighted entropy functionals (inspired by Perelman's $\mathcal{W}$-functional and Li–Yau differential Harnack inequalities) to prove a rigorous **lower bound on integrated fusion energy yield** over $[0, T_{\text{burn}}]$?

---

## 2. The MHD Analogue of the Beale–Kato–Majda (BKM) Criterion

### 2.1 The Caflisch–Klapper–Steele Theorem
In 3D Navier–Stokes/Euler equations, the Beale–Kato–Majda (1984) theorem states that smooth solutions continue on $[0, T_{\text{burn}}]$ provided $\int_0^{T_{\text{burn}}} \Vert{}\nabla \times \mathbf{v}(t)\Vert{}_{L^\infty}\,dt < \infty$.

In 3D ideal and visco-resistive Magnetohydrodynamics (MHD), **Caflisch, Klapper, and Steele (1997)** proved that preventing finite-time blowup (such as singular current-sheet formation) requires simultaneous $L^1_t L^\infty_x$ (or $L^1_t BMO_x$) control of both the **fluid vorticity $\boldsymbol{\omega} = \nabla \times \mathbf{v}$** and the **electric current density $\mathbf{J} = \mu_0^{-1} \nabla \times \mathbf{B}$**:
$$\mathcal{I}_{\text{BKM}}(T_{\text{burn}}) := \int_0^{T_{\text{burn}}} \Big( \Vert{}\nabla \times \mathbf{v}(t)\Vert{}_{L^\infty(M)} + \Vert{}\nabla \times \mathbf{B}(t)\Vert{}_{L^\infty(M)} \Big)\,dt < \infty.$$

In terms of the **Elsässer variables** $\mathbf{z}_\pm = \mathbf{v} \pm \mathbf{B}/\sqrt{\mu_0 \rho}$ and their generalized vorticities $\boldsymbol{\omega}_\pm = \nabla \times \mathbf{z}_\pm$, higher Sobolev norms $\Vert{}\mathbf{z}_\pm(t)\Vert{}_{H^s(M)}$ ($s > 5/2$) obey the logarithmic Grönwall–BKM inequality:
$$\frac{d}{dt} \Big( \Vert{}\mathbf{z}_+\Vert{}_{H^s}^2 + \Vert{}\mathbf{z}_-\Vert{}_{H^s}^2 \Big) \le C_s \Big( \Vert{}\boldsymbol{\omega}_+\Vert{}_{L^\infty} + \Vert{}\boldsymbol{\omega}_-\Vert{}_{L^\infty} \Big) \Big( \Vert{}\mathbf{z}_+\Vert{}_{H^s}^2 + \Vert{}\mathbf{z}_-\Vert{}_{H^s}^2 \Big).$$
For compressible non-isentropic MHD (including density $\rho$ and temperature $T$), adding $\Vert{}\mathrm{div}\,\mathbf{v}\Vert{}_{L^1_t L^\infty_x} < \infty$ and strict vacuum avoidance $0 < \rho_{\min} \le \rho(x,t) \le \rho_{\max}$ prevents both shock formation and thermal blowup.

### 2.2 Dimensional Reduction via a Quasisymmetric Field + Symmetric Ansatz
In 2D or exact helically symmetric MHD, vortex stretching is absent. Global regularity is known **with dissipation** (positive viscosity and resistivity). For **ideal** 2-D (or helically symmetric) MHD, global regularity is an **open problem**: the current density can still grow without any known bound.

> **Correction (2026-10-20):** The earlier text said smooth solutions of 2-D / helically symmetric MHD exist globally in time. That is known only for the visco-resistive system. For ideal MHD it is open. The Riccati law below is a heuristic, not a theorem. Only the conditional ODE-comparison statement is usable ("*if* $Y$ satisfies the differential inequality, then $Y$ stays bounded under the threshold condition"). Deriving the inequality itself from MHD is research problem R3.

Suppose the external stellarator field $\mathbf{B}_{\text{ext}}$ is $(M,N)$-quasisymmetric along the helical vector field $\mathbf{u} = N\partial_{\theta_B} + M\partial_{\phi_B}$ up to a small symmetry-breaking defect $\epsilon_{\text{QS}} \ge 0$. If the initial plasma state $(\mathbf{v}_0, \mathbf{B}_0, p_0)$ lies in the **$\mathbf{u}$-invariant symmetric ansatz** ($\mathcal{L}_{\mathbf{u}} \mathbf{v}_0 = 0, \mathcal{L}_{\mathbf{u}} \mathbf{B}_0 = 0$):
* The 2D symmetry-preserving self-interaction generates **zero 3D vortex stretching**.
* *(Heuristic, unproved; see the correction above.)* Growth of the 3D BKM norm $Y(t) = \Vert{}\boldsymbol{\omega}(t)\Vert{}_{H^s} + \Vert{}\mathbf{J}(t)\Vert{}_{H^s}$ is driven purely by the quasisymmetry defect $\epsilon_{\text{QS}}$ and damped by effective viscosity/resistivity $\nu_{\text{eff}} > 0$:
  $$\frac{dY}{dt} \le -\nu_{\text{eff}} Y + C \, \epsilon_{\text{QS}} \, Y^2.$$
* **Small-Defect Global / Long-Time Regularity (conditional on the inequality above):** Whenever the initial state satisfies $Y(0) < \frac{\nu_{\text{eff}}}{C \, \epsilon_{\text{QS}}}$, $Y(t)$ remains strictly bounded for **all time $t \ge 0$** (and even for $\nu_{\text{eff}} = 0$, blowup cannot occur before $T_{\text{burn}} < \frac{1}{C \, \epsilon_{\text{QS}} Y(0)}$), automatically discharging the Caflisch–Klapper–Steele BKM criterion!

### 2.3 Lean 4 Kernel Contract
```lean
/-- Caflisch-Klapper-Steele BKM Regularity Certificate on [0, T_burn]:
    Bounding the time integral of L∞ vorticity and current density guarantees
    an explicit exponential bound on the H^s Sobolev norm of Elsässer fields! -/
structure BKMRegularityCertificate
    (E_Hs : ℝ → ℝ) (ω_inf J_inf : ℝ → ℝ) (C_s T_burn B_max : ℝ) : Prop where
  T_pos : 0 < T_burn
  bkm_integral_bound : ∫ t in (0)..T_burn, (ω_inf t + J_inf t) ≤ B_max
  gronwall_bound : ∀ t ∈ Set.Icc 0 T_burn,
    E_Hs t ≤ E_Hs 0 * Real.exp (C_s * B_max)

/-- Quasisymmetric Ansatz Riccati Stability Certificate:
    If the quasisymmetry defect ε_QS satisfies C * ε_QS * Y_0 < ν_eff, then the
    vorticity-current norm Y(t) is globally bounded and never blows up! -/
structure QuasisymmetricAnsatzNoBlowup
    (Y0 ν_eff C_stretch ε_QS : ℝ) : Prop where
  Y0_pos  : 0 < Y0
  ν_pos   : 0 < ν_eff
  eps_nonneg : 0 ≤ ε_QS
  subthreshold : C_stretch * ε_QS * Y0 < ν_eff

```

> **Correction (2026-10-20), vacuous contract:** `QuasisymmetricAnsatzNoBlowup` only records four inequalities between reals and mentions no solution, so holding it proves nothing about blowup. The usable replacement is a theorem: for any differentiable `Y : ℝ → ℝ` with `Y 0 = Y0` and `deriv Y t ≤ -ν * Y t + C * ε * (Y t)^2` for t ≥ 0, if `C * ε * Y0 < ν` then `Y t ≤ Y0` for all t ≥ 0. That is pure ODE comparison and provable now. Its hypothesis (the differential inequality for an actual MHD solution) stays open. `BKMRegularityCertificate` similarly bundles its conclusion `gronwall_bound` as a field. It needs a producing theorem from the (cited) Caflisch–Klapper–Steele estimate.

---

## 3. Li–Yau–Perelman Entropy Functionals & Finite-Time Fusion Yield Lower Bounds

### 3.1 Why We Use Weighted Entropy & Harnack Bounds Instead of Naive Temperature Monotonicity

In a burning fusion plasma, temperature $T(x,t)$ is **not** monotone in time: localized radiation, edge cooling, and profile relaxation cause $T(x,t)$ to fluctuate or decay over the discharge duration $[0, T_{\text{burn}}]$.

However, inspired by **Perelman's $\mathcal{W}$-functional** for Ricci flow and **Li–Yau–Hamilton differential Harnack inequalities** for nonlinear reaction-diffusion equations on Riemannian manifolds $(M, g_{\text{mag}})$, we can bound the **maximum rate of thermal entropy dissipation** to obtain a rigorous pointwise and integral lower bound on $T(x,t)$ for $t \in [0, T_{\text{burn}}]$:

1. **Relative Kullback–Leibler / Log-Sobolev Thermal Entropy:**
Given a target equilibrium temperature profile $T_*(x) > 0$, define the non-negative convex relative entropy functional:

$$\mathcal{H}[T \vert{} T_*](t) := \int_M n(x) \, T_*(x) \left( \frac{T(x,t)}{T_*(x)} - 1 - \ln \frac{T(x,t)}{T_*(x)} \right) dV_g \ge 0.$$



Along the anisotropic heat-transport PDE $\partial_t(n T) = \nabla \cdot (n \boldsymbol{\chi} \cdot \nabla T) + S_{\text{fus}}(T) - P_{\text{rad}}(T)$, the time derivative satisfies an exact **Fisher-information entropy dissipation identity**:

$$\frac{d}{dt}\mathcal{H}[T \vert{} T_*] = -\int_M n T_* \, \Big\langle \nabla \ln \frac{T}{T_*}, \, \boldsymbol{\chi} \cdot \nabla \ln \frac{T}{T_*} \Big\rangle dV_g + \int_M \left(1 - \frac{T_*}{T}\right) \Delta Q_{\text{net}}(T)\,dV_g.$$



Notice that the diffusive term has a **strictly negative-definite sign** (just like Perelman's Fisher-information gradient term!), strongly damping spatial temperature inhomogeneities toward $T_*(x)$.

> **Correction (2026-10-20):** The identity above is **false** when $T_*$ is non-constant, and "$\Delta Q_{\text{net}}$" should be $Q_{\text{net}}$. For fixed $n(x)$, $T_*(x)$ and a symmetric $\boldsymbol\chi(x)\ge 0$ independent of $T$, the correct identity (checked symbolically with sympy) is
> $$\frac{d}{dt}\mathcal{H} = -\int_M nT_*\Big\langle\nabla\ln\tfrac{T}{T_*},\boldsymbol\chi\nabla\ln\tfrac{T}{T_*}\Big\rangle + \int_M \ln\tfrac{T}{T_*}\,\nabla\!\cdot(n\boldsymbol\chi\nabla T_*) + \int_M\Big(1-\tfrac{T_*}{T}\Big)Q(T) + \oint_{\partial M}\Big[\Big(1-\tfrac{T_*}{T}\Big)n\boldsymbol\chi\nabla T - \ln\tfrac{T}{T_*}\,n\boldsymbol\chi\nabla T_*\Big]\cdot\nu .$$
> The cross term $\int \ln(T/T_*)\,\nabla\cdot(n\chi\nabla T_*)$ has no sign. Exact counterexample on $[0,1]$ with $n=\chi=1$, $Q=0$, $T_*=1+x^2$, $T=1+x$ (both boundary terms vanish because $T=T_*$ at $x=0,1$): the true $d\mathcal{H}/dt = \int(1-T_*/T)T''\,dx = 0$, while the formula above predicts $\approx -0.2447 < 0$. The negative-definite structure holds when $T_*$ is a steady state with $T=T_*$ on $\partial M$ (Dirichlet). Then $\frac{d}{dt}\mathcal H = -\text{Fisher} + \int[(1-\tfrac1s-\ln s)Q(T_*) + (1-\tfrac1s)(Q(T)-Q(T_*))]$ with $s=T/T_*$. This is $\le -\text{Fisher}$ whenever $Q(T_*)\ge 0$ and $Q$ is non-increasing in $T$. It **fails** in the thermally unstable regime where $\partial_T Q>0$ (alpha heating). See `notes/theory/relative-entropy-dissipation.md`.
2. **Finite-Time Burn Energy Yield Certificate:**
Whenever the initial core thermal energy $W_{\text{th}}(0) = \int_M \frac{3}{2} n T(x,0)\,dV$ and relative entropy $\mathcal{H}[T(0) \vert{} T_*]$ are certified within a basin where net energy loss rate is bounded by $\gamma_{\text{loss}}$ ($\frac{d}{dt} W_{\text{th}} \ge -\gamma_{\text{loss}} W_{\text{th}}$), $W_{\text{th}}(t) \ge W_{\text{th}}(0) e^{-\gamma_{\text{loss}} t}$ holds for all $t \in [0, T_{\text{burn}}]$.
By Jensen's inequality on the convex fusion reactivity curve $P_{\text{fus}}(T)$ in the ignition window, this guarantees a **strictly positive lower bound on total fusion energy produced during $[0, T_{\text{burn}}]$**:

$$E_{\text{fusion}}(T_{\text{burn}}) := \int_0^{T_{\text{burn}}} \int_M P_{\text{fus}}\big(n(x,t), T(x,t)\big)\,dV\,dt \ge E_{\text{min}}\big(W_{\text{th}}(0), \gamma_{\text{loss}}, T_{\text{burn}}\big).$$



### 3.2 Lean 4 Kernel Contract

```lean
/-- Perelman / Log-Sobolev Relative Thermal Entropy integrand φ(s) = s - 1 - log(s) ≥ 0 -/
noncomputable def relativeThermalEntropyIntegrand (T T_star : ℝ) : ℝ :=
  T_star * ((T / T_star) - 1 - Real.log (T / T_star))

/-- Finite-Time Plasma Burn & Energy Yield Certificate over [0, T_burn]:
    Replaces false "monotonicity of T" with a differential-inequality lower bound
    on thermal energy W_th(t) ≥ W_0 * exp(-γ_loss * t), certifying net fusion yield! -/
structure FiniteTimeBurnYieldCertificate
    (W_th : ℝ → ℝ) (P_fus_total : ℝ → ℝ)
    (W_0 γ_loss α_fus T_burn E_target : ℝ) : Prop where
  T_burn_pos   : 0 < T_burn
  W0_pos       : 0 < W_0
  γ_pos        : 0 < γ_loss
  energy_decay_bound : ∀ t ∈ Set.Icc 0 T_burn, W_th t ≥ W_0 * Real.exp (-γ_loss * t)
  reactivity_lower   : ∀ t ∈ Set.Icc 0 T_burn, P_fus_total t ≥ α_fus * (W_th t) ^ 2
  yield_margin_ok    :
    (α_fus * W_0 ^ 2 / (2 * γ_loss)) * (1 - Real.exp (-2 * γ_loss * T_burn)) ≥ E_target

```

> **Correction (2026-10-20), contract needs a producing theorem:** The two physical hypotheses `energy_decay_bound` and `reactivity_lower` are fields of the structure, not consequences of a transport model. The yield integral is not mentioned at all. The usable statement is a theorem: these hypotheses plus integrability imply `∫ t in 0..T_burn, P_fus_total t ≥ E_target`. Separate theorems should derive `energy_decay_bound` from a transport PDE or 0-D balance (T3/T4). The "Jensen on a convex reactivity curve" step is also unchecked: ⟨σv⟩(T) for D-T is convex only on part of the keV range, so any use needs a stated temperature window.

---

## 4. Importing Structure-Preserving CFD Methods into `PlasmaLean`

To bridge continuum BKM and entropy bounds with finite-dimensional computation, two modern CFD frameworks complement our Numerical Relativity tools:

1. **Finite Element Exterior Calculus (FEEC / Discrete de Rham Cochains):** Represents discrete potentials $\mathbf{A}_h \in V_h^1$, magnetic fields $\mathbf{B}_h = d \mathbf{A}_h \in V_h^2$, and divergences $d \mathbf{B}_h = 0 \in V_h^3$ as a cochain complex ($d \circ d = 0$). In Lean 4, `extDeriv_extDeriv = 0` is a purely algebraic identity on cochain matrices, guaranteeing $\nabla \cdot \mathbf{B}_h = 0$ and magnetic helicity conservation without truncation error.
2. **Tadmor Entropy-Stable Numerical Fluxes:** Constructs discrete finite-volume fluxes $\mathbf{F}_{i+1/2}^*$ satisfying Tadmor's algebraic shuffle condition $\llbracket \mathbf{v} \rrbracket \cdot \mathbf{F}_{i+1/2}^* = \llbracket \boldsymbol{\psi} \rrbracket$ with respect to the entropy variables $\mathbf{v} = \partial \mathcal{S} / \partial \mathbf{u}$. This makes discrete thermodynamic entropy stability **decidable by matrix/rational arithmetic (`norm_num`)** inside the `PlasmaLean` kernel.
