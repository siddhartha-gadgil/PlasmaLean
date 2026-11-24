# Linear action stability with critical points deep in the well

A smooth magnetic well generally has a critical point at its bottom. A linear perturbation estimate for bounce action only needs quantitative regularity near the **mirror height**. Lean proves a bound in which all deeper points contribute through their total arclength. [Mirror collar theorem](../../PlasmaLean/Theory/Kinetic/MirrorActionCollar.lean)

Let $B,C$ be measurable field-strength profiles on a common finite arclength space, with a common lower bound and $|B-C|\le\delta$ almost everywhere. Write $J(B,h)$ for the clipped one-passage action at height $h$. Choose $w>0$. Assume the two reference bands $(b-\delta,b]$ and $(b,b+\delta]$ each have mass at most $\varepsilon$ whenever $h-w-\delta\le b\le h$. Then

$$
|J(B,h)-J(C,h)|\le
\frac{2\delta}{\sqrt{2w}}\,\mu\{B\le h-w\}
+\varepsilon\sqrt{2(w+\delta)}.
$$

On the deeper set, the positive reference speed lets one rationalize the difference of square roots, even if the perturbed speed is clipped to zero. The rest follows by applying the band estimate with the higher floor $h-w-\delta$. If arclength branches cover the reference strengths $(h-w-2\delta,h+\delta]$ and satisfy $|B(s)-B(t)|\ge m_i|s-t|$ with $m_i>0$, one may set $\varepsilon=\delta\sum_i1/m_i$. This gives linear dependence for small $\delta$ at fixed $w$. Critical points or flat regions deeper in the well introduce no inverse slope in this estimate. [General perturbation bounds](mirror-profile-stability.md)

To apply this to Dommaschk label variation, the next mathematical inputs are a common arclength parametrization or a density-change bound, a profile error between labels, and bounds on the regular branches throughout a collar of positive width. N-81 supplies slopes in geometric angle in the local mirror slabs. A uniform physical collar in arclength still needs a proof. [Local angular slopes](dommaschk-transverse-physical-mirror-brackets.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-87 |
| Kind | Candidate-independent perturbation bound |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-72, N-85 |
| Dependency requirement | Finite common arclength measure, common field floor, uniform field perturbation and quantitative band or branch bounds near the mirror height. |
| Produces | Linear action stability using regularity only near the height, with explicit dependence on deep-well mass. |
| Difficulty | Verify collar size and change of arclength between physical labels. |
| Status | All three Lean declarations compiled and passed axiom checks. |
| Lean evidence | `MirrorActionCollar.deep_speed_bound`, `.action_of_collar` and `.action_of_collar_branches`. |
| Audit evidence | Standard Lean axioms only. |
| Last updated | 24 November 2026 |
