# How field-profile perturbations change mirror roots and bounce action

Fix a finite arclength measure $\mu$ and a height $h$. For a field-strength profile $B$, write $J(B,h)=\int\sqrt{2(h-B)_+}\,d\mu$. Assume the two profiles are measurable and $|B-C|\le\delta$ almost everywhere. Lean proves the following estimates. [Profile stability theorems](../../PlasmaLean/Theory/Kinetic/MirrorProfileStability.lean)

* **Any finite well.** $|J(B,h)-J(C,h)|\le\mu(X)\sqrt{2\delta}$. A constant well at $h-\delta$ shifted to $h$ attains equality. This includes profiles that put positive arclength at a single field strength.
* **Measured bands.** Suppose $b_0\le B,C$ almost everywhere and $b_0\le h$. If each of the two bands $(b-\delta,b]$ and $(b,b+\delta]$ has reference arclength at most $\varepsilon$ for all $b\in[b_0,h]$, then $|J(B,h)-J(C,h)|\le\varepsilon\sqrt{2(h-b_0)}$. The larger of the two one-sided masses bounds the discrepancy at a threshold, including any mass exactly at the threshold.
* **Arclength branches.** Suppose finitely many branches cover the relevant reference strengths $(b_0-\delta,h+\delta]$ in arclength coordinates. If $|B(s)-B(t)|\ge m_i|s-t|$ on branch $i$, with $m_i>0$, take $\varepsilon=\delta\sum_i 1/m_i$. A signed derivative bound on a convex branch implies this secant bound. The condition can fail at a smooth well bottom.
* **Label derivative.** For a family $B_\alpha$ with fixed $\mu$, assume a uniform lower floor and measurable profiles. If the reference gives at most $K(b-a)$ mass to each band $(a,b]$ and the fields vary locally by at most $L|\beta-\alpha|$ almost everywhere, an existing action derivative satisfies $|\partial_\alpha J|\le KL\sqrt{2(h-b_0)}$. A changing arclength density across physical labels requires an additional estimate.

There is also a geometric estimate for the motion of a mirror point. If the reference has secant lower bound $m$ on a bracket and $B(x)=h$, each perturbed root $C(y)=h'$ in that bracket satisfies $|x-y|\le(|h-h'|+\delta)/m$. Endpoint margins that survive the perturbation imply existence for a continuous $C$. An affine reference and a constant vertical perturbation attain equality. At the local physical mirrors of N-81, the signed slopes concern **squared field strength** in outward angle. An error $\varepsilon$ in squared field strength therefore gives conditional displacements $128\varepsilon$ and $400\varepsilon$ radians at fixed squared height. For a field-strength error $\delta$ the squared error at the root is at most $\delta(2|h|+\delta)$. [Local physical slopes](dommaschk-transverse-physical-mirror-brackets.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-85 |
| Kind | Candidate-independent action stability and root localization |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-72; N-81 supplies the example of an angular slope |
| Dependency requirement | Finite common measure; linear stability additionally needs control of mass in short field-strength bands. |
| Produces | Sharp square-root action bound, linear band and branch bounds, localization of perturbed crossings, and a fixed-measure label derivative estimate. |
| Difficulty | Estimate the relevant concentration and changes in the arclength density for a physical label family. |
| Status | All 17 mathematical theorems built and passed the axiom audit. |
| Lean evidence | `MirrorProfileStability.action_sqrt_bound`, `.action_of_branches`, `.perturbed_roots`, `.squared_field_root_displacement`, `.flat_action_attains`, `.label_derivative_le`. |
| Audit evidence | The concrete equality cases and general implications use only standard Lean axioms. |
| Last updated | 24 November 2026 |
