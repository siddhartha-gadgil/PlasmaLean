# Theory notes (lane A output)

Discovery-lane notes in the sense of `notes/implementation-plan.md` §3. Each note keeps sourced theorems, informal proofs,
symbolic checks, conjectures and leads separate. **Nothing here is a compiled Lean theorem** unless a progress report says so.

Status tags: **published** (located in the source, with locator) · **formal asymptotic** (near-axis/ordering result) ·
**proved informally** (complete elementary proof, symbolically checked where possible) · **conjectured** · **refuted** · **lead**
(source suggested, statement not located).

| Note | Track | Main content | Status |
| --- | --- | --- | --- |
| [toroidal-min-b-obstruction.md](toroidal-min-b-obstruction.md) | T1, T8 (§1.1) | Subharmonic ⇒ no interior *max*, with min-B counterexamples (B = (x,y,−2z), Ioffe–Pritchard). Curvature identity ∇⊥B = Bκ (vacuum, or ∇p = 0) ⇒ a min of \|B\| forces κ = 0 ⇒ no min-B around a closed axis. Max-J needs κ = 0 at B_min (Helander 2014 §3.7). QS cannot be max-J (Rodríguez–Helander–Goodman 2024). Exact omnigenity ⇒ QS/nonanalytic (Cary–Shasharina 1997) | identity and corollaries: **proved informally** (Helander 2014 Eq. 24, §3.3); D–F: **published / formal asymptotic**; G: **conjectured**; Hall–McNamara: **lead** |
| [relative-entropy-dissipation.md](relative-entropy-dissipation.md) | T3 (§1.5) | Exact identity dH/dt = −𝓕 + cross + reaction + boundary. The BKM-note version is **refuted** for non-constant T* (exact counterexample). Dissipation holds for constant T*, or for steady Dirichlet-matched T* with Q(T*) ≥ 0 and Q non-increasing in T. It fails on the thermally unstable branch | **proved informally**, sympy-checked; note's claim **refuted** |
| [flux-surface-holonomy.md](flux-surface-holonomy.md) | T10 (§1.2) | The flat bundle's holonomy encodes the fluxes (with one gauge-ambiguous period), not ι. ι is the ratio of the periods of β = ι_Bσ. Riemann bilinear ⇒ V′⟨B²⟩ = μ₀Φ_t′(G+ιI) (known). Hodge period inequalities ∫\|B\|²/\|∇Φ_t\|² ≥ \|ι−τ\|²/Im τ, ∫\|B\|² ≥ μ₀²\|G−τI\|²/Im τ | holonomy↔ι: **refuted** (not useful); periods+τ: **proved informally**, verdict **useful later** |

Recommended next Lean targets are listed at the end of each note. The quickest are `vacuum_minB_counterexample`,
`curvature_zero_of_normSq_critical`, `closed_axis_not_minB`, the 1-D pointwise relative-entropy identity, and the
constant-metric τ/energy identity extending `Challenge6_ConformalTorusModulus`.
