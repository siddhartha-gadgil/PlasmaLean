# Trapped (banana) alphas in near-quasi-axisymmetric fields: what can be proved

Lane A note, 20 October 2026, against `e647fdb`. Tracks: M4, T8. Companion to
[near-axis-quasisymmetry.md](near-axis-quasisymmetry.md) and [guiding-centre-averaging.md](guiding-centre-averaging.md).
**Nothing here is a compiled Lean theorem.**

## 0. Where the library stands

- `Kinetic.Boozer`: a vacuum Boozer guiding-centre model. It proves energy conservation, the exact helical-momentum
  identity `dP/dt = −(q²ρ²B/m + μ)·ξB`, the finite-time trapping `boozerGC_trapped_until` (time ∝ 1/ε) and the
  exact-QS all-time `boozerGC_trapped`.
  - **These hold for any pitch, trapped included.** The momentum band uses only `|Δρ|`, and for a trapped particle
    `|Δρ| ≤ 2ρ_max`.
  - So exact QA already confines bananas for all time in the model. The open problem is *near* QA for times
    ≈ slowing-down (0.4 s).
- `Design.NearAxisQA.reactorQA`: the field is `B = B₀(1 + ηr cos θ) + r²(b₀ + b₁ cos 2φ + B₂c cos 2θ)`, with
  `B₀ = 5.7 T`, `η = −0.07 m⁻¹`, `b₀ = −0.0137`, `b₁ = −4.3×10⁻⁴`, `B₂c = 0.0165 T m⁻²`, `ι = 0.422`,
  `G = 58.1 T m`, `a = 1.7 m`.
  - The defect is `ξB = ∂_φB = −2b₁r² sin 2φ`, so `ε_QS(a) = 2.49×10⁻³ T` (`4.4×10⁻⁴ B₀`).
  - Passing alphas (`|v_∥/v| ≥ 0.9`) are trapped for 0.8 ms.
- `Kinetic.AvailableEnergy.bounceActionRadialDeriv_neg`: the sign of the expression
  `−(λ/2)∫ ∂_ψB/√(1 − λB) dl`, i.e. min-B ⇒ max-J. Its identification with `∂J/∂ψ` is not proved.
- `Kinetic.osc_ibp_drift(_iter)`: oscillatory averaging with explicit constants. It needs a phase speed
  `Ω ≥ Ω₀ > 0`.

## 1. Standard theory (published)

- **Second adiabatic invariant.** `J = ∮ m v_∥ dl` over a bounce, at fixed `(E, μ)` and field line `α`.
- **Bounce-averaged radial drift.** `⟨ψ̇⟩_b = −(1/(q τ_b)) ∂J/∂α` and `⟨α̇⟩_b = (1/(q τ_b)) ∂J/∂ψ` (Helander,
  *Rep. Prog. Phys.* 77 (2014) 087001, §5; Hall & McNamara, *Phys. Fluids* 18 (1975) 552).
  - So the bounce-averaged motion is a 1-degree-of-freedom Hamiltonian flow in `(ψ, α)` with "Hamiltonian" `J`.
  - Trapped particles are confined iff the `J` contours close inside the plasma.
  - **Omnigeneity** is `∂J/∂α ≡ 0`. Exact omnigeneity forces QS or non-analytic `B` (Cary & Shasharina, *PRL* 78
    (1997) 674; see [toroidal-min-b-obstruction.md](toroidal-min-b-obstruction.md) F).
- **QS cannot be max-J** (Rodríguez, Helander & Goodman 2024; same note G). So trapped-particle confinement in
  near-QS cannot come from a sign of `∂J/∂ψ`. It must come from closed `J` contours, or equivalently from
  near-conservation of `P`.
- **Adiabatic invariance.** For one fast phase (here the bounce), averaging gives drift of the improved invariant
  `O(ε)` over times `O(1/ε)`. In the analytic case the non-averaged remainder is exponentially small
  (Neishtadt, *J. Appl. Math. Mech.* 48 (1984) 133; Arnold–Kozlov–Neishtadt, *Mathematical Aspects of Classical and
  Celestial Mechanics*, ch. 6).
  - **This fails at separatrices.** Crossing the trapped–passing boundary (bounce frequency → 0 logarithmically)
    changes `J` by `O(ε ln ε)` per crossing, with a quasi-random phase (Cary, Escande & Tennyson, *Phys. Rev. A* 34
    (1986) 4256; Neishtadt 1986).
  - Repeated crossings give diffusion.

## 2. Known loss mechanisms (published; these are the obstructions)

1. **Stochastic ripple diffusion of bananas** (Goldston, White & Boozer, *PRL* 47 (1981) 647).
   - In a tokamak with toroidal ripple δ, each bounce-tip passage gives a radial kick `∝ δ sin(Nφ_tip)`. The tip
     phase advances by an amount that depends on radius.
   - The kicks are stochastic (Chirikov overlap) once δ exceeds a low critical value `δ_GWB`. During this, `E`, `μ`
     and `B` at the tips are conserved.
   - The commonly quoted form `δ_GWB ~ (ε/(πNq))^{3/2}/(ρ_L q')` is from secondary sources; it is a **lead** to
     recheck against White et al., *Phys. Plasmas* 3 (1996) 3043.
   - This is a numerical/heuristic threshold, not a theorem. No rigorous proof of the stochastic regime exists, and
     proving positive-measure chaos is out of reach.
2. **Ripple trapping** in local wells along the field line: fast vertical/radial drift loss.
3. **Banana-drift convection** where the precession `⟨α̇⟩_b ∝ ∂J/∂ψ` vanishes: there `J` contours open
   (Velasco et al., *Nucl. Fusion* 61 (2021) 116059, as cited by Paul et al.).
4. **Non-conservation of `J` and class transitions** (trapped↔passing, well↔well), periodic or irregular.
   - Paul, Bhattacharjee, Landreman, Alex, Velasco & Nies, "Energetic particle loss mechanisms in reactor-scale
     equilibria close to quasisymmetry", *Nucl. Fusion* 62 (2022) 126054, arXiv:2208.02351.
   - That study used guiding-centre tracing in NCSX, ARIES-CS, Wistell-A, Ku5, HSX and a rippled ITER. It found that
     "substantial non-conservation of the parallel adiabatic invariant" causes diffusive banana-tip motion, and that
     quasihelical configurations are naturally protected against ripple trapping and banana-tip diffusion.
   - The rippled ITER case had the smallest QS error but large losses. **The size of `ε_QS` alone does not control
     trapped-particle losses**; how the defect is structured along the bananas matters.
   - Numerical, not rigorous.
5. **Recent (numerical)**: weighted-Birkhoff-average chaos diagnostics for alphas in near-omnigeneous fields
   (Lachmann, Knyazev & Paul, arXiv:2609.39376, Sept 2026). Not rigorous; relevant as an oracle technique.

The obstructions for any rigorous long-time statement follow. A theorem must **exclude**:
- (O1) a pitch layer around the trapped–passing separatrix, where the bounce frequency → 0 and averaging fails;
- (O2) a layer around precession reversal, `ω_prec = 0`, where the excursion bound below blows up as `1/ω_min`;
- (O3) multiple-well field lines, because transitions break `J`;
- (O4) large Chirikov parameter (GWB regime), where the averaging remainder is not small.

## 3. Facts about the reactorQA model (proved informally)

**Single-well property (no ripple wells, so no O3) for `r ≤ a`.** Along a field line `θ = α + ιφ`, as a function of
`θ`,

    dB/dθ|_line = −B₀ηr sin θ − 2B₂c r² sin 2θ − (2/ι) b₁ r² sin(2(θ − α)/ι).

With `η < 0`:
- The first two terms equal `sin θ · r(B₀|η| − 4B₂c r cos θ)`, and the bracket is `≥ r(0.399 − 0.112) = 0.287 r`.
- The ripple term is `≤ (2/ι)|b₁| r² ≤ 3.5×10⁻³ r`.
- Hence `sign(dB/dθ) = sign(sin θ)` except where `|sin θ| < 0.0122`.
- In those windows (near θ = 0 and θ = π) the second derivative is `≥ r(0.399 − 0.112 − 0.0164) > 0.27 r` near 0,
  and symmetrically `< 0` near π.

So on each poloidal turn `B|_line` has exactly one minimum and one maximum.
- Ripple wells would need `4|b₁|r² > B₀|η| r ι²`, i.e. `r > 41 m`.
- This is a polynomial-plus-trig inequality and is feasible in Lean (see T2 below).
- **Caveat:** this concerns the truncated model. The `O(r³)` remainder of the real precise-QA field is not bounded
  (formal asymptotics).

**Order of magnitude of the trapped excursion (estimate, not proved).**
- In the `J`-contour picture, `δψ ≲ 2 max|J₁| / min|∂_ψJ₀|`, with `J₁` from the `b₁` term and `∂_ψB ≈ η cos θ / r`.
  This gives `δr ≈ |b₁| r²/(B₀ |η| ⟨cos θ⟩_b) ≈ 3×10⁻³/⟨cos θ⟩_b` m at the edge. That is millimetres for deep
  bananas, and it blows up at precession reversal, where `⟨cos θ⟩_b → 0` (for large aspect ratio,
  `2E(κ)/K(κ) − 1 = 0` at `κ² ≈ 0.83`).
- **However**, 3.5 MeV alphas have finite orbit width: `ρ_L ≈ 0.047 m`, and the banana width is
  `≈ 2ρ_L/(ι√ε) ≈ 0.8 m` at mid-radius. So bounce-averaging at fixed ψ is not accurate. Finite-orbit-width
  corrections in near-omnigenous fields are a **lead** (d'Herbemont, Parra, Calvo & Velasco, *J. Plasma Phys.* 2022);
  check the statement before use.
- The robust formulation therefore averages over the **exact-QA banana**, not over a field line at fixed ψ (§4).

## 4. Recommended formulation: averaged first integral over exact-QA bananas

In exact QA (`b₁ = 0`), `φ` is cyclic and `P = q(Gρ − ψ_p(ψ))` is exact. The reduced motion in `(ψ, θ, ρ)` at fixed
`(H, μ, P)` is one degree of freedom, so the banana is closed. It has a bounce period `τ_b(P)` and a toroidal
precession per bounce `Δφ_b(P)`, i.e. `ω_φ = Δφ_b/τ_b`. Turning on `b₁` gives the following.

- **Per-bounce step (exact identity in the model).** Over a bounce interval `[t₀, t₁]` with `ρ(t₁) = ρ(t₀)`, the
  integral `∫ dP/dt dt` gives
  `q(ψ_p(ψ(t₁)) − ψ_p(ψ(t₀))) = ∫_{t₀}^{t₁} (q²ρ²B/m + μ) ∂_φB dt`.
  This is the finite-orbit-width version of `⟨ψ̇⟩_b ∝ ∂J/∂α`.
- **Averaged dynamics.** To leading order, the step is `ε·S(P) sin(2φ_c + χ(P))`, with `φ_c` the banana's toroidal
  centre. Then `φ_c` advances by `Δφ_b(P)` per bounce.
  - The averaged map has the approximate first integral `K = H₀(P) + ε h(P, φ_c)`.
  - The ψ excursion is bounded by `2ε max|h| / min|∂_P H₀|`, where `∂_P H₀ ↔ ω_φ`.
- **Discrete oscillatory sum.** At fixed `P`, `|Σ_{k<K} sin(2φ₀ + 2kΔ)| ≤ 1/|sin Δ|`. This is the discrete
  counterpart of `osc_ibp_drift`. It gives the `1/ε²` time scale, as for passing particles, provided
  `|sin Δφ_b| ≥ s₀ > 0`. That condition excludes precession resonances (O2) and is the discrete form of the
  "Ω ≥ Ω₀" hypothesis.
  - The `ψ`-dependence of `Δφ_b` (shear of the precession) enters the remainder, together with `ε` and the kick size.
  - The product is exactly the Chirikov/GWB parameter, so (O4) appears as a smallness hypothesis, not as a hidden
    assumption.

## 5. Proposed Lean targets (in order; T1–T3 feasible in one cycle)

**T1 (easy). Per-bounce momentum step**, in `Theory/Kinetic/BoozerGuidingCentre.lean`. This is the FTC applied to
`helicalMomentum_hasDerivAt_on`, plus continuity of the integrand along the orbit.

```lean
theorem bounce_psip_step (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t₀ t₁ : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hρ : ρ t₁ = ρ t₀) :
    q * (F.ψp (ψ t₁) - F.ψp (ψ t₀)) =
      ∫ t in t₀..t₁, (q ^ 2 * ρ t ^ 2 * F.B (ψ t) (θ t) (φ t) / m + μ) * F.Bφ (ψ t) (θ t) (φ t)
```

(QA helicity `(N, M) = (0, 1)`. The general-helicity version uses `symmetryDefect F N M`.)

**T2 (moderate). Single-well property of `reactorQA`**, in `Design/NearAxisQA.lean`.

```lean
/-- On every field line `θ = α + ι₀ φ` and every radius `0 < r ≤ 17/10`, `B` restricted to the line
is strictly increasing in `θ` on `(0, π)` and strictly decreasing on `(π, 2π)` (mod 2π): one well
per poloidal turn, hence no ripple-trapped orbits in the model. -/
theorem reactorQA_single_well {ψ α : ℝ} (hψ0 : 0 < ψ) (hψ : ψ ≤ psiEdge) :
    StrictMonoOn (fun θ => reactorQA.B ψ θ ((θ - α) / (211 / 500))) (Set.Icc 0 Real.pi) ∧
    StrictAntiOn (fun θ => reactorQA.B ψ θ ((θ - α) / (211 / 500))) (Set.Icc Real.pi (2 * Real.pi))
```

Proof: the derivative bound of §3, with `|sin| ≥ 0.0122` handled by the first-derivative sign. The windows near 0 and
π are handled by a second-derivative sign plus the derivative vanishing only at the endpoint, e.g. via
`strictMonoOn_of_deriv_pos` on `(0, π)` after showing `dB/dθ > 0` there through the convexity argument. Interval
arithmetic on `sin`/`cos` uses Mathlib bounds such as `Real.sin_le`, `Real.cos_bound`.

**T3 (easy, abstract). Band from an approximate first integral**, in `Theory/Kinetic/ApproximateInvariant.lean`.

```lean
/-- If K = H₀ ∘ P + ε·h with |h| ≤ 1, H₀' ≥ ω > 0 on [Pa, Pb], and |K(t) − K(0)| ≤ δ t, then
|H₀(P t) − H₀(P 0)| ≤ 2ε + δ t, hence P stays in [Pa, Pb] while 2ε + δ t < ω · gap. -/
theorem band_of_approx_first_integral {P K h : ℝ → ℝ} {H₀ : ℝ → ℝ} {ε δ ω Pa Pb T : ℝ}
    (hω : 0 < ω) (hH : ∀ x ∈ Set.Icc Pa Pb, ∀ y ∈ Set.Icc Pa Pb, x ≤ y → ω * (y - x) ≤ H₀ y - H₀ x)
    (hK : ∀ t ∈ Set.Icc 0 T, K t = H₀ (P t) + ε * h t) (hh : ∀ t ∈ Set.Icc 0 T, |h t| ≤ 1)
    (hdrift : ∀ t ∈ Set.Icc 0 T, |K t - K 0| ≤ δ * t) (hP : Continuous P)
    (hgap : 2 * ε + δ * T < ω * min (P 0 - Pa) (Pb - P 0)) :
    ∀ t ∈ Set.Icc 0 T, P t ∈ Set.Icc Pa Pb
```

This reuses the `trapped_until` first-crossing pattern.

**T4 (research, Phase 5+). Instance for 3.5 MeV bananas in `reactorQA`.** Construct `K` from the bounce-averaged
`b₁` term over exact-QA bananas, prove `hdrift` with `δ = O(ε·(ε + ρ*))` via the iterated averaging lemma along the
bounce phase (pitch set excluding O1 and O2), and give interval bounds for `S(P)`, `Δφ_b(P)` and `ω`. This needs
validated bounce integrals (elliptic-type) and is the trapped analogue of the passing-particle Phase 4 item 1.

**Discrete averaging lemma (easy, supports T4).**

```lean
theorem abs_sum_sin_arith_le (φ₀ Δ : ℝ) (hΔ : Real.sin Δ ≠ 0) (K : ℕ) :
    |∑ k in Finset.range K, Real.sin (2 * φ₀ + 2 * k * Δ)| ≤ 1 / |Real.sin Δ|
```

## 6. Verdict

- Exact QA: trapped alphas are already covered for all time by `boozerGC_trapped` (model).
- Near QA, uniformly in pitch: **not possible** (O1 and O2 are genuine; Paul et al. 2022 see these losses
  numerically).
- Feasible now: T1 and T3 (abstract), plus T2 (concrete; it removes O3 for the model). Together they reduce the
  trapped-alpha problem to one quantitative hypothesis, the averaged-drift bound `hdrift` on a stated pitch set.
  That is the honest next target.
