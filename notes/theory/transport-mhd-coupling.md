# Transport–MHD coupling: one plasma for the G1 and G2 chains

Lane A note, 20 October 2026, against `e647fdb`. Tracks: M2/M3 coupling (Phase 4, item 3 of the progress-4 "Next
boundary"). **Nothing here is a compiled Lean theorem.** Status tags as in [README](README.md).

## 0. The gap

The library currently has three results that talk about *different* plasmas:

| Result | Field | Pressure | Transport geometry |
| --- | --- | --- | --- |
| `SolovevAlpha.reactor_alpha_confined` (G1) | Solov'ev reactor, `L = 10 m`, `A = 7/4 T`, `F = 50 T m` | `p = p₀(1 − ψ̃/ψ̃_e)`, `p₀ ≈ 457 kPa` | none |
| `HelicalTransportBarrier.helical_core_barrier` (G2) | straight helical, 5 T | `0.398(1 − s)` MPa | `IsHelicalGeometry` |
| `TransportBarrier.m2_core_barrier_kernel` (G2) | idealized cylinder | none | constant `V'` |

The helical barrier is pressure-consistent only on the axis (`tsub_axis_pressure`). The reason, recorded in its module
doc, is that the equilibrium pressure vanishes on the transport edge while the edge temperature is at least 1 keV. The
goal here is one statement in which **the same field `B`** satisfies `ForceBalance` with pressure `p`, confines 3.5 MeV
alphas, and carries a transport solution whose pressure is consistent with `p`.

## 1. Consistency conditions (what "one plasma" means)

Let `ψ` be the equilibrium flux label, `s = ψ/ψ_b` the transport label, and `c = 1 + r_i` the particles per electron
(`c = 1 + 53/60` for `m2Plasma`). For a transport solution `T(s,t)` (keV) with density profile `n(s)`, define the
plasma pressure `p_tr(s,t) = n(s)·c·T(s,t)·keV`.

**(C-geom) Geometry from the same equilibrium.** `V'(s)`, `g(s) = ⟨|∇s|²⟩` and `h(s) = ⟨Δs⟩` are the flux-surface
quantities of the *same* `ψ` whose level sets carry `B`. In Lean this is a class `IsSolovevGeometry G` on a
`FluxGeometry` (as `IsHelicalGeometry` is for the helical field). For the Solov'ev family it can be almost fully
*proved*, not supplied (§3.1).

**(C-p) Pressure consistency.** Three strengths, in decreasing order:

1. **Equality** `p_tr(s,t) = p_eq(s)`. A static equilibrium can equal a time-dependent pressure only in steady state.
   So equality means "a steady transport state `T∞` with `n c T∞ keV = p_eq`". It needs either existence of steady
   states (not in the library) or "equilibrium from barrier" (§4, rung C3).
2. **Band (recommended target)**: `p_sub(s) ≤ p_tr(s,t) ≤ p_eq(s)` for all `t ≥ 0` and all `s ∈ [0,1]`.
   - The upper side is the physically required one: the plasma never exceeds the pressure the field can confine.
   - The lower side records how far below equilibrium the plasma is.
   - **The upper side needs an upper transport barrier (supersolution), not only the lower one.** This is the
     main structural finding of this note. The current barrier theorems are one-sided (lower), and no lower barrier
     alone can imply `p_tr ≤ p_eq`.
3. **Axis-only** (`tsub_axis_pressure`, what exists now).

**(C-edge) Edge pressure.** The transport edge `s = 1` must sit where `p_eq(1) ≥ n(1)·c·T_edge·keV > 0`. There are
three ways to get this.

- **(E1) Truncate inside the zero-pressure surface (recommended).** Choose `ψ_b < ψ_e`. For Solov'ev take
  `ψ_b = (11/12)ψ_e`, so that `p_eq ≥ p₀/12 ≈ 38 kPa` on the whole transport domain. This needs no sheet and no
  vacuum region. The layer `ψ_b < ψ < ψ_e` is unmodelled (it plays the role of the pedestal foot / SOL). It is
  *exactly* the region that `reactor_alpha_confined` already uses: alphas born in `ψ̃ ≤ ψ̃_e/4` stay in
  `ψ̃ ≤ (11/12)ψ̃_e`. So the G1 confinement region equals the G2 transport domain.
- **(E2) Constant pressure offset.** `ForceBalance` involves only `∇p`, so `p_eq + Δ` (any `Δ ≥ 0`) is an
  equilibrium of the *same* `B` and `J` on the region. Proof: `reactor_force_balance` uses `pressureGrad`, which is
  unchanged. The offset is a free fit parameter.
  - Its physical meaning is a pressure pedestal at the boundary. A sharp boundary with `p = Δ` inside and `p = 0`
    outside needs a current sheet with the jump condition `[[p + B²/2μ₀]] = 0`.
  - For `Δ = 40 kPa` at 5 T (`B²/2μ₀ ≈ 9.95 MPa`) this is `δB/B ≈ Δ μ₀/B² ≈ 0.2%`, a sheet current
    `K = δB/μ₀ ≈ 8 kA/m`.
  - The kernel `ForceBalance` is pointwise, so the sheet is outside the kernel. As with the existing
    "pressure continues to negative values outside the region" caveat, claims are restricted to the region and the
    exterior is not modelled.
- **(E3) Density → 0 at the edge.** Rejected as stated. The density-weighted operator (§2) has capacity `n V'`, and
  the kernel law `Vp_pos` requires `n(1) > 0`. With `n(1) = 0` the edge becomes a second degenerate boundary, which is
  a kernel change with no payoff, since (E1) gives a positive edge pressure anyway. A density that *decreases*
  toward the edge but stays positive is fine and is used below.

## 2. The kernel handles a density profile `n(s)` without change (proved informally)

With density `n(s) > 0`, the energy equation `(3/2)c n ∂ₜT = (1/V')∂ₛ(V' (3/2)c n χ g ∂ₛT) + p_α − p_br + p_aux`
divided by the local heat capacity `(3/2)c n(s) keV` is

    ∂ₜT = (1/(nV')) ∂ₛ(nV' χ g ∂ₛT) + R(s,T),
    R(s,T) = [(E_α/4) f² n(s)² ⟨σv⟩(T) − C_br Z_eff n(s)² √T + p_aux(s)] / ((3/2) c n(s) keV).

(As in the library, `χ` includes the 3/2 normalization.) This is the kernel operator for the **weighted flux
geometry**

    G.weight n n' := ⟨n V', n' V' + n V'', g, g', h + (n'/n) g⟩.

Its Gauss law `(nV'g)' = nV'(h + n'g/n)` follows from that of `G` by the product rule. So `FluxGeometry.Laws` is
preserved whenever `n > 0` on `[0,1]` and `n'` is its derivative. `FluxGeometry.coeffs`, `coeffs_transportLaws`,
`g_le`/`le_g` and all comparison theorems then apply verbatim. The only caveat is that the `Vp_le` enclosures now
involve `(n V')''/(nV')`. `IsHelicalGeometry`-style mean-value hypotheses are about `G`, not about the weight, so they
are unaffected. The source `R` scales like `n(s)`, so alpha heating per unit heat capacity drops toward the edge.

## 3. Solov'ev reactor as the common equilibrium

### 3.1 The flux geometry of the reactor Solov'ev is explicit (proved informally, numerically checked)

Write `X = R² − L²`, so `ψ̃ = (X + L²) z²/2 + X²/4`, and `dV = π dX dz` (axisymmetry, `R dR = dX/2`).

- **Volume derivative.** Substituting `X = 2√ψ̃ sin ϑ` gives

      V'_ψ̃(ψ̃) = 2√2 π ∫_{−π/2}^{π/2} (L² + 2√ψ̃ sin ϑ)^{−1/2} dϑ
               = (2√2 π²/L) Σ_k C(−1/2, 2k) · C(2k,k) · (ψ̃/L⁴)^k.

  The odd powers of `sin ϑ` integrate to zero. The series has ratio `≤ 4ψ̃/L⁴ ≤ 0.23` on `ψ̃ ≤ ψ̃_b`, so a
  geometric tail bound gives a rigorous enclosure with a handful of terms.
- **Laplacian.** The 3-D Laplacian is `Δψ̃ = 2z² + 5R² − 2L² = 2z² + 5X + 3L²`, a polynomial. Hence

      V'⟨|∇ψ̃|²⟩ = ∫_{ψ̃'≤ψ̃} Δψ̃ dV = π ∬ (2z² + 5X + 3L²) dX dz   (Gauss + coarea),

  again a 1-D integral of an algebraic function with an analytic series in `ψ̃`.
- **Axis values.** `V'(0) = 2√2π²/L` and `h(0) = 3L²/ψ_b` (per unit `s`).

Numerical values for `L = 10`, label `s = ψ̃/ψ̃_b`, `ψ̃_b = (11/12)·625 = 572.9 m⁴` (`/tmp/laneA5/geom.py`, adaptive
quadrature):

| s | V'(s) (m³) | g(s)/s (m⁻²) | h(s) (m⁻²) | V''/V' |
| --- | --- | --- | --- | --- |
| 0 | 1599.3 | 0.5236 | 0.5236 | 0.043 |
| 0.4 | 1628 | 0.5128 | 0.5113 | 0.047 |
| 1 | 1678.3 | 0.4953 | 0.4914 | 0.054 |

The plasma volume is 1637 m³ (1790 m³ to `ψ̃_e`). The enclosures `h ∈ [0.491, 0.524]` and `V''/V' ∈ [0.043, 0.055]`
are as tight as the helical ones.

**Important difference from the helical case.** Pointwise, `Δψ̃` varies by a factor ≈ 9 on the edge surface (60 to 540
m²). So the mean-value route of `IsHelicalGeometry` (pointwise bounds on each surface) is far too weak here. The
explicit series is the right route, and it makes the class *provable* except for the coarea/divergence link, which
stays the supplied step as in the helical case.

### 3.2 Candidate rungs and parameters (numerical observations; oracle `/tmp/laneA5/tr*.py`, untrusted)

Common data:
- Equilibrium: reactor Solov'ev, transport domain `ψ̃ ≤ (11/12)ψ̃_e`, so `p_eq(s) = Δ + p₀(1 − 11s/12)` with
  `p₀ = 456.95 kPa`.
- Density: `n(s) = n₀ (1 − 11s/12)/(1 − βs)`, which makes `T_eq := p_eq/(n c keV)` linear when `Δ = 0`.
- Plasma: `Z_eff = 1.7`, `f = 0.86`, `T_edge = 1 keV`, Bosch–Hale reactivity.
- Numerics: finite volumes (200 cells), BDF time-marching to steady state from a cold and a hot start. Both starts
  give the same state unless noted.

**Finding 1 (runaway with fixed χ).** With a temperature-independent `χ(s)` (the present semilinear kernel), every
ignited configuration tried runs away to 90–220 keV. The burning steady states near 13 keV are thermally unstable.
Stable hot states exist only in a driven regime `Q ≲ 2–3`. This is the 1-D counterpart of the Phase 1 finding
(runaway above 30 keV with constant τ_E).

**Finding 2 (0-D obstruction, proved informally).** Let `F(T) = P_α(T) + P_aux − P_loss(T)`, with
`T P_α' ≥ γ P_α` and `T P_loss' ≤ δ P_loss` on `[T₁, T₂]`. If `F(T₁) ≥ 0 > F(T₂)` (an ordered sub/supersolution pair),
let `T* = sup{T ∈ [T₁,T₂] : F ≥ 0}`. Then `T* < T₂`, `F(T*) = 0`, and `F'(T*) ≤ 0`, so
`(γ − δ) P_α(T*) ≤ δ P_aux`.
- For Bosch–Hale, `γ = T⟨σv⟩'/⟨σv⟩` is 2.52, 2.21, 1.83 and 1.53 at 10, 12, 15 and 18 keV.
- Fixed χ means `δ = 1`. On `[10, 15]` keV this gives `Q(T*) = 5P_α/P_aux ≤ 5/(γ − 1) ≤ 6.1`.
- An *ignited* two-sided band therefore needs a loss exponent `δ ≥ γ`, i.e. temperature-dependent transport. For
  example gyro-Bohm `χ ∝ T^{3/2}` gives `δ = 5/2`.

**Rung C1 (no kernel change; semilinear, driven).**
- Parameters: `Δ = 0`, `n₀ = 0.9×10²⁰ m⁻³`, `β = 0.7` (`n(1) = 2.5×10¹⁹`), flat `χ = χ₀ = 1.5 m²/s`,
  `p_aux = 3.5×10⁵ exp(−(s/0.45)²) W/m³` (225 MW).
- Steady state: `T(0) = 15.4`, `T(0.3) = 10.5`, `T(0.9) = 2.7` keV, `max p_tr/p_eq = 0.92`, `P_α = 104 MW` (Q ≈ 2.3).
- **Fragile.** `χ₀ = 2.0` gives `T(0) = 9.2` (fails), and `p_aux = 3.0×10⁵` gives `T(0.3) = 8.0` (fails). An
  ordered barrier pair would cover only `χ₀ ≈ 1.5 ± 0.05`.
- Useful only as a kernel-compatible demonstration.

**Rung C2 (recommended; needs kernel extension K2, quasilinear `D(s,T)`).**
- Transport: `χ = χ₀ (1/10 + (T/10 keV)^{3/2})` (gyro-Bohm-like, with a floor), `χ₀ ∈ [0.75, 0.80] m²/s`.
- Density and edge: `n₀ = 0.9×10²⁰`, `β = 0.7`, offset `Δ = 40 kPa`.
- Heating: `p_aux = 4×10⁴ exp(−(s/0.35)²) W/m³` (20 MW).

| χ₀ | T(0) | T(0.3) | T(0.9) | max p_tr/(p_eq+Δ) | P_α | Q |
| --- | --- | --- | --- | --- | --- | --- |
| 0.75 | 16.6 | 14.1 | 6.6 | 0.963 | 187 MW | ≈ 47 |
| 0.80 | 13.7 | 11.5 | 5.3 | 0.780 | 122 MW | ≈ 30 |

- Volume-averaged plasma β is 2.1–2.6% (equilibrium `β_axis = 4.6%`). Fusion power is 0.6–0.9 GW.
- The edge pressure `n(1) c T_edge keV ≈ 7.5 kPa` is far below `p_eq(1) + Δ ≈ 78 kPa`.
- At `χ₀ = 0.70` the plasma is hotter, `T(0) = 18.6`, and needs `Δ ≈ 66 kPa`. Near `χ₀ ≈ 0.85` the hot branch
  disappears (saddle-node), and below `χ₀ ≈ 0.75` the pressure exceeds `p_eq + 40 kPa`.
- **The admissible χ window is narrow (±3%) because the equilibrium fixes β.** That is the real content of the
  coupling.
- The window can be widened by a second fit parameter: the Solov'ev amplitude `A ∈ [7/4, 2]` T.
  - The ψ̃-geometry and the transport label do not depend on `A`. Only `B_pol ∝ A` and `p₀ ∝ A²` change.
  - Alpha confinement needs `A L/64 ≥ 0.2694` T·m, i.e. `A ≥ 1.724`, so a larger `A` only improves its margin.
  - `A = 2` gives `p₀ = 597 kPa`, `β_axis = 6%`, `q₀ = 1.77`.
- Barrier data for C2: take `T_sub` ≈ the χ₀ = 0.80 steady state minus a margin (≈ 0.5 keV in the core), and
  `T_sup` ≈ the χ₀ = 0.75 steady state plus a margin. Check `n c T_sup keV ≤ p_eq + Δ` (margin ≥ 3%) and the
  operator signs at both χ corners. For the quasilinear operator, `N[T]` is no longer affine in χ₀. It is monotone in
  χ₀ wherever `(D(s,T)T')' ` has a fixed sign, so check both corners **and** the sign condition piecewise.

**Alpha birth region lies in the hot core.** `ψ̃ ≤ ψ̃_e/4 ⇔ s ≤ (1/4)/(11/12) = 3/11 < 3/10`. So the alphas that
`reactor_alpha_confined` covers are born where the barrier gives `T ≥ 10 keV`, and they never leave the transport
domain.

## 4. Rungs, in order of cost

| Rung | Kernel change | Content | Cost |
| --- | --- | --- | --- |
| C0 | none | `IsSolovevGeometry` (series `V'`, `V'g`), `FluxGeometry.weight`, offset equilibrium, lower barrier + **pressure upper bound only at points where `T_sub` already exceeds `T_eq`** (a negative check) | low |
| C1 | none | two-sided band, semilinear, driven Q ≈ 2 | medium (narrow window, two 12-piece certificates) |
| **C2** | **K2: `D : ℝ → ℝ → ℝ` (quasilinear)** | two-sided band, ignited, Q ≈ 30–47, Δ = 40 kPa | medium–high |
| C3 | none beyond C2 | "equilibrium from barrier": a validated toroidal GS solve (radii polynomial, M3) with `p(ψ) = n c T∞` for a validated steady `T∞` | high (Phase 5+) |

**K2 justification.** The first-crossing argument evaluates the operator at a touching point where `u = S` and
`u' = S'`. Hence a quasilinear operator
`op c ψ u uψ uψψ = D(ψ,u) uψψ + (∂_ψD(ψ,u) + ∂_TD(ψ,u)·uψ + D(ψ,u) V''/V') uψ + R(ψ,u)`
with `D ≥ 0` satisfies the same comparison theorems. The existing proofs use only monotonicity in `uψψ` and equality
of the lower-order arguments at the touching point. A kernel change record is needed, as for the 2026-10-20 change.
Old models are recovered with `D(ψ,T) := D(ψ)`.

**C3 note (equality).** In inverse design one fixes `T*` and defines `n := p_eq/(c T* keV)`; the aux profile that
makes `T*` steady is then forced. This is exact only if `⟨σv⟩` is a fixed function. With the enclosure class
`BoschHaleDT` it is not, so equality is not achievable in the current framework. Only the band (C1/C2) is.

## 5. Exact Lean statements proposed

Namespace `PlasmaLean.Design.SolovevBurn` (new; imports `SolovevAlpha`, `Theory.Transport.FluxGeometry`).

```lean
/-- Transport boundary flux ψ̃_b = (11/12) ψ̃_e = 11·10⁴/192 (the alpha-confinement shell). -/
def psiB : ℝ := 11 * 10 ^ 4 / 192
/-- Transport label s = ψ̃/ψ̃_b. -/
def label (x : Space) : ℝ := psiT 10 x / psiB

/-- Equilibrium pressure on labels, with constant offset Δ. -/
def peqLabel (μ₀ Δ s : ℝ) : ℝ := Δ + 147 / (256 * μ₀) * (1 - 11 / 12 * s)

theorem reactorPressure_label (μ₀ : ℝ) (hμ : μ₀ ≠ 0) (x : Space) :
    reactorPressure μ₀ x = peqLabel μ₀ 0 (label x)

/-- Constant offsets preserve the pressure gradient (hence `ForceBalance`). -/
theorem offset_pressure_hasFDerivAt (μ₀ Δ : ℝ) (x : Space) :
    HasFDerivAt (fun y => reactorPressure μ₀ y + Δ)
      (innerSL ℝ (pressureGrad μ₀ (7 / 4) 10 x)) x

/-- Alpha birth region inside the barrier core. -/
theorem birth_in_core {x : Space} (h : psiT 10 x ≤ 10 ^ 4 / 64) : label x ≤ 3 / 11
```

Density weighting (`Theory/Transport/FluxGeometry.lean`, no kernel change):

```lean
def FluxGeometry.weight (G : FluxGeometry) (n dn : ℝ → ℝ) : FluxGeometry :=
  ⟨fun s => n s * G.Vp s, fun s => dn s * G.Vp s + n s * G.dVp s, G.g, G.dg,
   fun s => G.h s + dn s / n s * G.g s⟩

theorem FluxGeometry.weight_laws (G : FluxGeometry) [G.Laws] {n dn : ℝ → ℝ}
    (hn : ∀ s ∈ Icc (0:ℝ) 1, 0 < n s)
    (hdn : ∀ s ∈ Icc (0:ℝ) 1, HasDerivWithinAt n (dn s) (Icc 0 1) s) :
    (G.weight n dn).Laws
```

Solov'ev geometry (provable except the coarea link, which is part of the class):

```lean
/-- V'(s) as the even series; `solovevVp_bounds`: 1599 ≤ V' ≤ 1679 on [0,1]. -/
def solovevVp (s : ℝ) : ℝ := ...   -- tsum with explicit tail, or closed rational enclosure
class IsSolovevGeometry (G : FluxGeometry) : Prop extends G.Laws where
  Vp_eq : ∀ s ∈ Icc (0:ℝ) 1, G.Vp s = solovevVp s
  Vpg_eq : ∀ s ∈ Icc (0:ℝ) 1, G.Vp s * G.g s = solovevLapIntegral s
theorem solovev_h_bounds [IsSolovevGeometry G] : ∀ s ∈ Icc (0:ℝ) 1, 0.49 ≤ G.h s ∧ G.h s ≤ 0.525
theorem solovev_g_bounds [IsSolovevGeometry G] :
    ∀ s ∈ Icc (0:ℝ) 1, 0.49 * s ≤ G.g s ∧ G.g s ≤ 0.524 * s
```

0-D obstruction (Finding 2; `Theory/Transport/PowerBalance.lean`):

```lean
theorem ordered_pair_gain_bound {Pα Pα' Pl Pl' : ℝ → ℝ} {Paux T₁ T₂ γ δ : ℝ}
    (h12 : T₁ < T₂) (hT₁ : 0 < T₁)
    (hα : ∀ T ∈ Icc T₁ T₂, HasDerivAt Pα (Pα' T) T) (hl : ∀ T ∈ Icc T₁ T₂, HasDerivAt Pl (Pl' T) T)
    (hγ : ∀ T ∈ Icc T₁ T₂, γ * Pα T ≤ T * Pα' T) (hδ : ∀ T ∈ Icc T₁ T₂, T * Pl' T ≤ δ * Pl T)
    (h1 : 0 ≤ Pα T₁ + Paux - Pl T₁) (h2 : Pα T₂ + Paux - Pl T₂ < 0) :
    ∃ T ∈ Ico T₁ T₂, Pα T + Paux = Pl T ∧ (γ - δ) * Pα T ≤ δ * Paux
```

**Combined theorem (rung C2; C1 is the same with semilinear `χ₀ ∈ [29/20, 31/20]`, `Δ = 0`):**

```lean
/-- One plasma: the reactor Solov'ev field is an equilibrium with pressure `p_eq + Δ`; 3.5 MeV
alphas born in the hot core never leave the transport domain; every transport solution started
in the band stays hot in the core and never exceeds the equilibrium pressure. -/
theorem solovev_one_plasma {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6)
    (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleDT sv]
    {χ₀ : ℝ} (hχ : χ₀ ∈ Icc (3 / 4) (4 / 5))
    {Tedge : ℝ → ℝ} (hedge : ∀ t, 0 ≤ t → Tedge t ∈ Icc 1 (3 / 2))
    {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (burnCoeffs G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0:ℝ) 1, Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ Tsup s) :
    -- (G1a) equilibrium: same B, J; pressure reactorPressure + Δ (Δ = 40 kPa)
    (∀ x, R2 x ≠ 0 → ForceBalance (ofLp (reactorField x))
        (ofLp (current μ₀ (7 / 4) 10 50 x)) (ofLp (pressureGrad μ₀ (7 / 4) 10 x))) ∧
    (∀ x, HasFDerivAt (fun y => reactorPressure μ₀ y + 40000)
        (innerSL ℝ (pressureGrad μ₀ (7 / 4) 10 x)) x) ∧
    -- (consistency) on the whole transport domain, for all time
    (∀ x, psiT 10 x ≤ psiB → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤ reactorPressure μ₀ x + 40000) ∧
    -- (G2) hot core
    (∀ s ∈ Icc (0:ℝ) (3 / 10), ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
    -- (G1b) alphas born in s ≤ 3/11 stay in the transport domain for all t
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
        e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
        m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → psiT 10 (x 0) ≤ 10 ^ 4 / 64 →
        ∀ t, psiT 10 (x t) ≤ psiB)
```

Here `nProf s = 9e19 * (1 - 11/12*s)/(1 - 7/10*s)`. `burnCoeffs` is `(G.weight nProf dnProf)` with the quasilinear
coefficient `χ₀(1/10 + (T/10)^{3/2})·g` and the density-scaled source of §2. `Tsub`/`Tsup` are polynomial barriers
certified by `BarrierCheck`. The (G1b) clause is `reactor_alpha_confined` restated, so it is free. The (G1a) clause
is `reactor_force_balance` plus `offset_pressure_hasFDerivAt`. The new work is the band (two barrier certificates),
`IsSolovevGeometry`, `weight_laws` and K2.

Honest limitations to keep in the docstring:
- The transport model is single-temperature with a prescribed density and a prescribed (supplied) χ law.
- The equilibrium is static while `T` evolves, so consistency is the band, not equality.
- The layer `ψ̃_b < ψ̃ < ψ̃_e` and the exterior are unmodelled. The offset Δ implies an unmodelled boundary sheet.
- The coarea/divergence link of `IsSolovevGeometry` is supplied.
- Tokamak-like (axisymmetric), not a stellarator.
- There is no MHD stability claim (Mercier for Solov'ev is Phase 4 item 4).

## 6. Counterexample checks performed

- Constant `n`, `Δ = 0`, the helical-style `T_sub` (slope −7.6/13 relative at the axis): `p_tr > p_eq` already at
  `s = 0.1` (0.368 vs 0.358 MPa). This reproduces the module's own finding. A linear `p_eq` needs `n·T` to fall at
  least as fast as `1 − θs`, hence the decreasing `n(s)`.
- `n(1) = 0`: the kernel's `Vp_pos` fails, so E3 is rejected.
- Fixed χ, ignited: runaway (Finding 1). Gyro-Bohm χ with the edge drop `w = 1 − 0.95s⁴`: the edge becomes
  insulating (`χ_edge ≈ 0.0015 χ₀` at 1 keV), the profile flattens at ≈ 100 keV, and the edge-drop factor is
  unusable with `T^{3/2}` transport. C2 uses `w ≡ 1`.

## 7. Next dependency

K2 kernel record → `weight_laws` → `IsSolovevGeometry` series enclosures → two barrier certificates for C2 →
`solovev_one_plasma`. In parallel, C0 can be done in the current kernel as a warm-up.
