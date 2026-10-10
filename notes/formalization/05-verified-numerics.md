# Verified numerics and continuous certificates

External computation proposes candidates. A small proved checker and analytic soundness theorems turn selected candidates into mathematical evidence. This is a development specification, not an assertion that these checkers already exist.

## Contents

- [Exact inputs and interval arithmetic](#exact-inputs-and-interval-arithmetic)
- [Continuous geometry and quadrature](#continuous-geometry-and-quadrature)
- [Finite-dimensional certificates](#finite-dimensional-certificates)
- [Continuum equilibrium validation](#continuum-equilibrium-validation)
- [Continuum stability validation](#continuum-stability-validation)
- [KAM and orbit certificates](#kam-and-orbit-certificates)
- [Uncertainty and certificate identity](#uncertainty-and-certificate-identity)
- [Theorem backlog](#theorem-backlog)

## Exact inputs and interval arithmetic

Use rational/dyadic endpoints and a semantic predicate `x ∈ [l,u]` with `l≤u`. Prove soundness of arithmetic, comparison, powers, roots, and transcendental enclosures. Exclude zero for reciprocals. Rational arithmetic avoids floating-rounding trust initially; faster arithmetic requires its own soundness bridge.

Decode a decimal token as the exact rational it denotes, or as an uncertainty interval if it represents a measurement/rounded quantity. A float converted to a real without a declared interpretation does not identify a physical coefficient.

For a checker `check` prove

$$
\operatorname{check}(c)=\mathrm{true}
\quad\Longrightarrow\quad
\operatorname{Claim}(\operatorname{decode}(c)).
$$

Keep all semantics, domain coverage, and remainder obligations in this theorem. Treat results returned by Python, CUDA, SMT, an optimizer, or an external interval package as certificate data rather than assertions accepted by Lean.

Inspect axioms and execution trust of certificate entry points. Prefer proof-producing arithmetic and a kernel-checked soundness theorem. [Rump](09-literature.md#validated-computation-and-analysis) is the general validated-computation reference.

## Continuous geometry and quadrature

For a Fourier curve `c(t)`, bound `c,c',c''` on every parameter box. Prove regularity `|c'|≥v_*>0` and use

$$
\kappa(t)=\frac{|c'(t)\times c''(t)|}{|c'(t)|^3}.
$$

For disjoint coils/surfaces, cover the entire product parameter domain and bound squared distances. For self-clearance, distinguish neighboring parameters from genuinely separate curve segments and use a tubular-radius/reach argument where necessary.

A simple between-sample lemma is already useful: if `c₁,c₂` have derivative bounds `L₁,L₂`, their parameter grids have fill distances `h₁,h₂`, and every grid-pair distance is at least `d₀`, then

$$
|c_1(t)-c_2(s)|\ge d_0-L_1h_1-L_2h_2.
$$

Prove grid coverage and the mean-value bounds. The same idea certifies a scalar inequality from sampled values plus a Lipschitz bound. Sampling without those ingredients is not a proof.

For integrals use interval quadrature with explicit remainder, or analytic bounds on Fourier tails. For `‖f‖_ν=Σ_k|f_k|ν^{|k|}` with `ν>1`,

$$
\sum_{|k|>N}|f_k|\le\nu^{-N}\|f\|_\nu.
$$

Derivatives require weighted factors `|k|^j` and generally a narrower analyticity strip/weight. Prove convolution-algebra and derivative-loss estimates before using them in a PDE proof. A finite Fourier polynomial has no unknown coefficient tail, but the exact equilibrium validated near it generally does.

For Biot–Savart, prove a positive distance to conductor sources before using integrand derivative and quadrature bounds.

## Finite-dimensional certificates

For a symmetric exact matrix `A`, validate an exact factorization

$$
A=LDL^\mathsf T,\qquad D_{ii}>0,
$$

with diagonal `D` and invertible `L`. This proves positive definiteness. For a claimed quantitative margin use a factorization of `A-cM`, where `M` is the positive inertia/Gram matrix.

If a numerical matrix approximates an exact matrix, prove the enclosure or form error and subtract it from the margin. A floating Cholesky success flag is not a certificate.

For nonlinear finite systems validate a contraction/Newton/Krawczyk-style inclusion with its precise existence and uniqueness theorem. Handle gauge and phase symmetries so that the intended Jacobian/inverse is nonsingular. A root of projected equations is only a projected solution until the continuum/tail conditions are supplied.

## Continuum equilibrium validation

Let `X` be a complete Banach space, `F:X→X` the gauge-fixed continuum equation, `x̂` a candidate, and `A` a bounded linear approximate inverse. Require `F` to be continuously Fréchet differentiable on an open neighborhood of the closed ball used below, so its derivative bound yields a Lipschitz bound along segments. Put

$$
T(x)=x-AF(x).
$$

On the closed radius-`r` ball around `x̂`, prove:

$$
\|T(\hat x)-\hat x\|\le Y,\qquad
\sup\|DT(x)\|\le Z(r)<1,\qquad
Y+Z(r)r\le r.
$$

Then `T` has a unique fixed point in that ball. To conclude `F(x)=0`, additionally prove `AF(x)=0 ⇒ F(x)=0`, for example by injectivity of `A`. Uniqueness is in the certified ball and gauge; it is not global uniqueness of equilibria.

With `Z(r)=Z₀+Z₂r`, an admissible `r>0` satisfying

$$
p(r)=Y+(Z_0-1)r+Z_2r^2<0
$$

implies the required strict inequalities when the bounds are nonnegative and the map/domain hypotheses hold. One needs a negative value at a positive radius, not a “negative root.”

Include:

- finite modes and analytic infinite-tail bounds;
- boundary/interface residuals;
- flux/current/profile constraints;
- coordinate Jacobian and embedding control throughout the ball;
- regularity sufficient to interpret the resulting solution;
- approximate-inverse and derivative estimates in the actual norm.

The equilibrium operator may have derivative loss, small divisors, or lack a bounded inverse in the chosen space. In that case an elementary radii-polynomial argument may be unavailable. Explore an appropriate a posteriori KAM/Nash–Moser theorem, a weaker equilibrium class, or a restricted model; do not invent invertibility.

[Nakao–Plum–Watanabe](09-literature.md#validated-computation-and-analysis) and [Lessard's tutorial](09-literature.md#validated-computation-and-analysis) are entry points for validation methods. Transferring their machinery to full three-dimensional MHD is a research task.

## Continuum stability validation

First validate an actual equilibrium `e` or carry the difference from a valid reference explicitly. Take a Hilbert energy space `V` and a proved orthogonal decomposition `V=V_N⊕V_tail`, so `‖u+v‖²_V=‖u‖²_V+‖v‖²_V`. Suppose the symmetric form satisfies

$$
q(u+v)=q_N(u)+2b(u,v)+q_{\rm tail}(v),
$$
$$
q_N(u)\ge a\|u\|^2,\quad
q_{\rm tail}(v)\ge b_*\|v\|^2,\quad
|b(u,v)|\le\gamma\|u\|\|v\|.
$$

If `a>0`, `b_*>0`, `γ≥0`, and `γ²<a b_*`, then `q(ξ)≥c‖ξ‖²_V`. One explicit margin is

$$
c=\frac{a+b_*-\sqrt{(a-b_*)^2+4\gamma^2}}2>0.
$$

For another decomposition/norm, prove `‖u+v‖_V≤C_d√(‖u‖²+‖v‖²)` and use margin `c/C_d²`. With ambient norms and only the triangle inequality, `C_d=√2` gives `c/2`. Convert the margin to the advertised norm before subtracting form errors.

A rational checker can avoid the square root by accepting a proposed `c>0` when `a-c≥0`, `b_*-c≥0`, and `γ²≤(a-c)(b_*-c)`. For an exact orthogonal two-block sanity example, `a=5`, `b_*=2`, `γ=2` and `c=1` satisfy these inequalities, and

$$
5x^2-4xy+2y^2=x^2+y^2+(2x-y)^2\ge x^2+y^2.
$$

This is finite block algebra; it supplies no missing MHD tail estimate.

This elementary block lemma is an early reusable theorem. For MHD, proving the tail bound in the correct space is the difficult part; ideal MHD is not a uniformly elliptic operator with an automatic increasing high-frequency spectrum.

Subtract rigorous form errors for coefficient enclosure, quadrature, geometry, and approximate-equilibrium replacement. If

$$
|q_e(\xi)-q_{\hat e}(\xi)|\le\varepsilon_{\rm eq}\|\xi\|_V^2,
$$

and every other nonnegative form-error bound is in the same norm, define `ε_tot=Σ_j ε_j`, including `ε_eq` once. The full-space bound is `q_e(ξ)≥(c_eff-ε_tot)‖ξ‖²_V`, with `c_eff=c` in the orthogonal case or `c/C_d²` otherwise. Require `c_eff>ε_tot`; separately exceeding each error is insufficient. Derive the equilibrium estimate from enough derivative/trace control of the validated solution; a small force residual alone is not such control.

Treat generalized eigenproblems with the actual mass/Gram form. Account for neutral modes and boundary/interface terms. Retain the label “finite-dimensional stability” if any continuum transfer ingredient is missing.

## KAM and orbit certificates

For a selected KAM theorem, prove regularity, symplectic/flux-preserving structure, nondegeneracy, residual bounds, and the infinite Diophantine condition. An interval containing an unknown frequency does not certify that every value in it is Diophantine. Use the theorem's frequency/parameter setup correctly.

For finite-time trajectories, enclose the full initial set and every time segment, bound the vector field/Jacobian on the enclosure, and prove the integration remainder and boundary separation. Distinguish numerical integrator error from guiding-centre/full-orbit model error.

## Uncertainty and certificate identity

A design certificate must identify geometry, coefficient serialization, species/profiles, material data version, field conventions, source commit, and checker version. A cryptographic hash can identify bytes but is not itself the theorem linking bytes to semantics; prove/use a well-defined decoder and attach the decoded value to the property.

Define the uncertainty set `U`, including correlations. For boxes, prove a finite box cover and each bound on the full box. An uncertainty parameter may change the equilibrium witness; use a validated branch or a parameter-wise existence theorem.

Monte Carlo confidence intervals require explicit probabilistic/statistical hypotheses and coverage theorems. They are not deterministic enclosures. Physical data intervals remain supplied assumptions unless their derivation is itself formalized.

## Theorem backlog

| ID | Target | Scope |
| --- | --- | --- |
| N1 | Exact rational parser and arithmetic containment | Small trusted certificate core |
| N2 | Grid/Lipschitz and Fourier-tail bounds | Continuous geometric certificates |
| N3 | Matrix factorization and block positivity | Finite algebra and reusable form theory |
| N4 | Generic contraction/radii-polynomial soundness | Banach spaces, explicit hypotheses |
| N5 | A validated scalar/ODE/axisymmetric equilibrium | First continuum examples |
| N6 | MHD equilibrium/operator tail estimates | Substantial analysis/research |
| N7 | All-mode robust energy certificate | N6 plus [03](03-mhd-stability.md) |
| N8 | Invariant-torus and finite-time orbit certificates | Source-specific KAM and validated ODEs |
| N9 | Certificate composition over correlated uncertainty | Common witnesses, norms, and data |
