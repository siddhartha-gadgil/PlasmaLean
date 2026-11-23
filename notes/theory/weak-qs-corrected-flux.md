# Corrected full-orbit flux for weak quasisymmetry and an absorbing-core certificate

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-43` |
| Title | Second-order corrected flux for full Lorentz orbits in an exact weakly quasisymmetric field, the finite-time absorbing-core certificate and hot-core moment bounds (method note for N-29 and N-17) |
| Kind | method |
| Addresses | `Q-29` (new); `G-6`, `G-2`; supports `Q-1`, `Q-23`, `Q-28` |
| Depends on | N-42 (source claims S-23 to S-29); N-29, N-17; Lean: `WeakQuasisymmetry.WeakQS`, `GyroNoether.gyroNoether_hasDerivAt`, `gyroNoether_band`, `gyroNoether_trapped_until`, `CanonicalMomentum.canonicalMomentum_conserved` |
| Dependency requirement | none compiled for the algebra; a supplied exact weak-QS field `(B, u, ψ)` and supplied orbits, as in `GyroNoether` |
| Produces | Q-29 statements and Lean targets |
| Difficulty | routine–moderate (Lean); research for any device application (an exact weak-QS equilibrium and a certified buffer) |
| Status | stated; complete mathematical proof checked (N-42); lean-ready |
| Lean evidence | step 1 only: `PlasmaLean.Fields.WeakQS.lieDerivForm_flux_eq_zero`, `WeakQS.lieBracket_eq_zero` (`Theory/Fields/FormCalculus`; they need, beyond `WeakQS`, an open set, `B` differentiable and divergence-free, and a `C²` potential); nothing for steps 2–5 |
| Audit evidence | not audited |
| Last updated | 20 November 2026: created from N-42; 23 November 2026: Lean evidence for step 1 recorded |
| Patched by / Alternatives | method for N-29 and N-17; their compiled results stand |

## Purpose and scope

The compiled gyro-Noether identity (`GyroNoether`) corrects the momentum `p_K = m⟪K, v⟫ + qψ` of
a **Killing** generator `K` when the field has a symmetry defect `δ = B × K + ∇ψ`. The corrector
there is linear in `v`. The source of N-42 (§9.1) treats the complementary case:

- an **exact** weak QS, with `div B = div u = 0`, `B × u = ∇ψ` and `u·∇|B|² = 0`;
- a generator `u` that is **not Killing**, so `S = sym ∇u ≠ 0`.

The defect of `ψ − εu·v` (`ε = m/q`) is then `−εvᵀSv`. Its gyro-average vanishes, and a
corrector quadratic in `v` removes it exactly.

Model: non-relativistic prescribed-field Lorentz orbits, `x' = v`, `v' = ε⁻¹ v × B(x)`, `E = 0`.
The fields are `C³` on a neighbourhood of `Ω̄`, and `B ≠ 0`. A relativistic version holds
verbatim, with the time rescaled by `γ`.

## The construction (source §9.1, checked in N-42)

1. **Weak-QS consequences.** `[B,u] = 0`, `tr S = 0`, and `bᵀSb = (u·∇|B|²)/(2|B|²) = 0`.
2. **Homological equation.** Let `b = B/|B|`, `K v = v × b`, `P = I − bbᵀ`, `a = Sb` and
   `S_⊥ = PSP`. Put
   `C = b(Ka)ᵀ + (Ka)bᵀ − ½ S_⊥ K` and `D = C/|B|`.
   Then `C = Cᵀ`, `[C,K] = S` and `‖C‖_F ≤ ‖S‖_F`.
   - The construction is tensorial: no gyroangle or frame is chosen.
   - Without `bᵀSb = 0` there is no solution, because `[C,K]` has zero `bb` block.
3. **Exact identity.** With `J = ψ − εu·v + ε²vᵀDv`,
   `J' = ε² Σ v_iv_jv_k ∂_kD_ij`.
4. **Certificate.** Let `U₀ = sup|u|`, `D₀ = sup‖D‖`, and let `D₁` be the sup of the cubic form
   of `∇D` over unit vectors. Put `A(V) = |ε|U₀V + ε²D₀V²` and `R(V) = ε²D₁V³`. Then
   `|ψ(x(t)) − ψ(x(s))| ≤ 2A(V) + |t − s|R(V)` while the orbit stays in `Ω̄` (`|v| ≤ V`).
   Suppose `ψ = ψ_b` on `∂Ω`, `ψ < ψ_b` inside, and `Δ > 2A + TR`. Then every orbit that starts
   in the core `{ψ ≤ ψ_b − Δ}` with speed `≤ V` stays in `Ω` on `[0, T]`, and in particular for
   `T_cert = (Δ − 2A)/R`.
   - Under `B ↦ ΛB`, `ψ ↦ Λψ` (with `u` fixed), the drift relative to the buffer is
     `O(T/Λ²)`.
5. **Hot core.** Take prescribed-field Vlasov with zero incoming data (the mild solution, with
   characteristics killed at the wall) and an initial Maxwellian `M`. Then `f = M` on the core
   for `|v| ≤ V = cσ` and `t ≤ T`, so
   - `n ≥ a(c)n₀`;
   - `Θ/Θ₀ ≥ b(c) − d(c)²/(3a(c)²)`;
   - a directional bound (H5), and the perturbed-data bound (H4).
   At `c = 2.8` the temperature ratio is above `0.8258`, so 12.5 keV gives more than 10.32 keV.

## Relation to compiled work

| Case | Generator | Field | Corrector | Lean |
| --- | --- | --- | --- | --- |
| exact symmetry | Killing `K` | `δ = 0` | none | `canonicalMomentum_conserved`, `noetherMomentum_conserved` |
| symmetry defect | Killing `K` | `δ ≠ 0` | linear `m⟪U, v⟫` | `gyroNoether_hasDerivAt`, `gyroNoether_band` |
| **exact weak QS** | non-Killing `u` | `u·∇|B| = 0` | quadratic `ε²vᵀDv` | none (Q-29) |
| weak QS with defect | non-Killing `u` | `δ ≠ 0`, `u·∇|B| ≠ 0` | both, plus a secular parallel term | open (Q-29 (c)) |

Sanity checks for any formalization:
- a Killing `u` gives `S = 0`, hence `C = D = 0`, and `J` is the canonical momentum;
- a uniform field with a linear shear `u` gives explicit `C` and `J'`.

Sign convention: `WeakQS` has `B × ξ = −∇ψ`, so take `u = −ξ` or flip `ψ`.

## Barriers

- **No exact weak-QS equilibrium is available.** On a toroidal volume with a non-Killing
  generator, exact weak QS is open (Q-16, Q-24). The source's own seed has an equilibrium
  obstruction, from the unassessed earlier handoff.
- **Projected fields need part (c) first.** For the project's fields (Dommaschk, rational), only
  approximate QS is available (N-34). A device claim therefore needs the defect version (c)
  before anything else.
- **No device constants yet.** `U₀`, `D₀`, `D₁` and the buffer `Δ` have not been bounded for any
  embedded geometry. The source makes no device claim either.
- **Prescribed-field model.** Self-consistent fields, collisions (P3)–(P5) and sources enter as
  explicit extra terms, not as hypotheses that hold for free.

## Outputs

- **Q-29:**
  - (a) the linear algebra (Q4) and the exact identity (Q7) along supplied orbits;
  - (b) the certificate (Q8)–(Q9) and the hot-core moment bounds (H3);
  - (c) research: combine with the gyro-Noether defect correction, so that the secular term is
    explicit in `|u·∇|B||` (feeding N-29 and N-34).
  - (a) and (b) are lean-ready and parallel `GyroNoether`.
- **N-40:** the moment bounds (H3)–(H5) are recorded as candidate kinetic fixtures for Q-28.

**Pointer (23 November 2026).** Step 1 is compiled in form language: `L_ξ ω_B = 0`
(`WeakQS.lieDerivForm_flux_eq_zero`, N-48), and so is the vector statement `[ξ, B] = 0`
(`WeakQS.lieBracket_eq_zero`).
