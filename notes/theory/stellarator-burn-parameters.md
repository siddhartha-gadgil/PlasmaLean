# Stellarator burn parameters for M1/M2 instances (ISS04, reactor studies, profile peaking)

Track: T4 (0-D burn window), M1/M2 stellarator instance, and the M4 confinement assumption. Lane A. **No Lean theorem
here.** All computed figures are **numerical observations** (floating point, `/tmp/laneA3/pb*.py`). They use the
same model as `PlasmaLean/Kernel/Fusion.lean`:
- Bosch–Hale D-T reactivity (NF 32 (1992) 611, standard coefficients);
- `P_α = (E_α/4)(f n)²⟨σv⟩V`, `P_br = 5.35×10⁻³⁷ n² Z_eff √T V`, `W = (3/2) n (1 + r_i) T V`;
- carbon impurity: `Z_eff = 1.7` gives `f = 0.86` and `r_i = 53/60`;
- steady-scaling convention: `P = P_α + P_aux`, `τ_E = f_ren · τ_ISS04(P)`.

The required renormalization is `f_ren = W/(P_α + P_aux − P_br) / τ_ISS04(P_α + P_aux)`.

## 1. ISS04 and f_ren (published)

- **ISS04** (H. Yamada et al., Nucl. Fusion **45** (2005) 1684):
  `τ_E = 0.134 a^2.28 R^0.64 P^−0.61 n̄_e19^0.54 B^0.84 ι_{2/3}^0.41` (s, m, MW, 10¹⁹ m⁻³ line-averaged, T).
  This is the form used in `ConfinementScaling.StellaratorParams.iss04`. In 10²⁰ m⁻³ units the prefactor is
  `0.134 × 10^0.54 = 0.465`.
  **Caution:** the UKAEA PROCESS documentation writes 0.134 together with n̄₂₀. That looks like a units slip and
  should not be copied.
- **f_ren** = τ_E/τ_ISS04 is configuration-dependent. In the 2004 database, f_ren ranges over about 0.25–1. The
  scaling is normalized so that the best-optimized configurations (W7-AS, inward-shifted LHD R = 3.6 m) are near 1.
  Yamada 2005 needed four f_ren values for LHD and three for W7-AS. f_ren correlates with the effective helical
  ripple. The exact per-configuration table values are a **lead** (not extracted here).
- **W7-X:** in OP1.1 limiter plasmas, τ_E was close to ISS04, i.e. f_ren ≈ 1 (Fuchert et al., NF 2018). After
  pellet injection τ_E transiently exceeded ISS04 by about 30% (Bozhenkov et al., NF 60 (2020) 066011; Baldzuhn et
  al., PPCF 2019), and by 30–40% in OP2 (Grulke et al., NF 2026 overview). So **f_ren ≈ 1.3–1.4 is the experimental
  ceiling, and it is transient.**
- **Reactor extrapolation:** Warmer et al. (Fusion Sci. Technol. 68 (2015), "Limits of confinement enhancement")
  use 1-D predictive transport and get f_ren ≈ 2 at W7-X size, falling to **1.1–1.3 at HELIAS-reactor size**. They
  treat 1.5 as a conservative upper limit.

## 2. Reactor studies (published parameters)

| Study | R (m) | a (m) | B (T) | V (m³) | other | confinement assumption |
| --- | --- | --- | --- | --- | --- | --- |
| **ARIES-CS** (Ku et al., Physics design, FST 54 (2008) 673; PPPL-4265) | 7.75 | 1.72 (A = 4.5) | 5.7 | 444 | ⟨n_i⟩ = 4.01×10²⁰, ⟨T⟩ = 6.55 keV (density-weighted), Z_eff = 1.13, β = 6.4%, P_fus = 2436 MW, alpha energy loss ≈ 5% | τ_E ≈ 1 s required, i.e. **H_ISS95 ≈ 2** ("ISS04 will give a more favorable confinement") |
| **HELIAS 5-B** (Warmer et al., IEEE TPS 44 (2016) 1576 / EUROfusion WPS2-PR(15)14259; Schauer et al.) | 22 | 1.80 (A = 12.2) | 5.5 (often quoted as 5.6–5.7) | ≈ 1400 | ⟨T⟩_V = 7 keV fixed, 10% He, P_fus ≈ 3 GW | **f_ren = 1.2** baseline (1.4 variant). Ignition reached with 55 MW start-up heating (20 MW at f_ren = 1.4) |
| **Stellaris** (Lion et al., Fusion Eng. Des. 214 (2025) 114868; parameters as quoted in arXiv:2507.12681) | 12.7 | 1.3 | 9 (axis average) | 425 | 4 periods, QI (SQuID), ⟨β⟩ ≈ 2.76%, P_fus ≈ 2.7 GW | ISS04 with P replaced by W/τ_E. The f_ren value was **not located** (lead: Table 2 / §3 of the paper) |

Not verified: the ι_{2/3} values used below (HELIAS 0.9, ARIES-CS 0.6, Stellaris 0.9) are **assumptions**. τ ∝ ι^0.41,
so a ±20% change in ι shifts f_ren by about ∓8%.

## 3. Results of the 0-D model

**Check against the repository:** for the HELIAS geometry (a = 1.8, R = 22, B = 5.5, ι = 0.9) at n = 10²⁰ and
10 keV the model gives f_ren = 1.87 with 50 MW of auxiliary power and 2.23 without it. This reproduces the "H ≈ 1.9"
note in `Design/BurnWindowScaling.lean`.

**Check against ARIES-CS's published point** (n_e ≈ 4.1×10²⁰, ⟨T⟩ = 6.55, Z_eff = 1.13):
- flat profiles: P_fus = 1692 MW (published 2436 MW), τ_need = 2.56 s, f_ren = 2.00, β = 6.6%;
- parabolic profiles with α_n = 0.5, α_T = 1: P_fus = 5357 MW.

The published point lies between these two. The model is therefore consistent once peaking is included.

**Design-point mode** (density chosen so that P_fus equals the study's value, Z_eff = 1.7, values of f_ren needed;
"peaked" means `n ∝ (1−ρ²)^0.5`, `T ∝ (1−ρ²)^1`, i.e. T₀/⟨T⟩ = 2):

| Device (P_fus target) | ⟨T⟩ keV | profile | n̄ (10²⁰) | β | f_ren (P_aux = 0) | f_ren (P_aux = 50 MW) |
| --- | --- | --- | --- | --- | --- | --- |
| HELIAS 5-B (3 GW) | 7 | flat | 3.13 | 5.5% | 2.72 | 2.41 |
| | 7 | peaked | 1.80 | 3.8% | 1.47 | 1.40 |
| | 10 | flat | 1.90 | 4.8% | 1.82 | 1.72 |
| | 10 | peaked | 1.26 | 3.8% | 1.58 | 1.51 |
| | 15 | flat | 1.22 | 4.6% | 1.92 | 1.84 |
| | 20 | flat | 0.97 | 4.9% | 2.22 | 2.14 |
| ARIES-CS (2.44 GW) | 10 | flat | 3.04 | 7.1% | 1.91 | 1.79 |
| | 10 | peaked | 2.02 | 5.6% | 1.66 | 1.57 |
| | 15 | flat | 1.96 | 6.9% | 2.02 | 1.92 |
| Stellaris (2.7 GW) | 7 | peaked | 3.11 | 2.5% | 1.18 | 1.11 |
| | 10 | flat | 3.28 | 3.1% | 1.45 | 1.36 |
| | 10 | peaked | 2.17 | 2.4% | 1.26 | 1.20 |
| | 15 | flat | 2.11 | 3.0% | 1.53 | 1.46 |
| | 20 | flat | 1.68 | 3.1% | 1.77 | 1.70 |

With Z_eff = 1.3 every entry falls by about 0.1–0.4 (for example, Stellaris at 10 keV flat goes to 1.29).

**Observations.**
1. At fixed fusion power, the f_ren needed is smallest near ⟨T⟩ ≈ 10–12 keV (flat) or 7–10 keV (peaked).
   **Holding 20 keV costs about 25% more confinement than 10 keV.**
2. The high field of Stellaris (B^0.84 in ISS04, B⁴ in fusion power at fixed β) is what brings f_ren into
   the 1.2–1.5 range. At 5.5–5.7 T a flat 0-D model needs f_ren ≈ 1.7–1.9. That is above the W7-X ceiling and
   above Warmer's 1.1–1.3.
3. **f_need(T) at fixed density is not monotone.** For example, for Stellaris geometry at n = 2.5×10²⁰ with
   50 MW: f_need = 1.58 (8 keV), 1.43 (10), 1.39 (12), 1.40 (15), 1.53 (20), 1.71 (25), 1.91 (30).
   - A lower barrier at T_lo needs f_ren > f_need(T_lo).
   - An upper barrier at T_hi needs f_ren < f_need(T_hi).
   - So a burn window [T_lo, T_hi] exists only if f_need(T_hi) > f_need(T_lo). With T_lo = 10 keV this forces
     T_hi ≳ 18–20 keV. At 2–2.5×10²⁰ the fusion power at T_hi is then 4–6 GW, above the design value.
     Lowering the density to 1.5×10²⁰ makes the window consistent with ≈ 2.4 GW at T_hi (§5).

## 4. Profile peaking (1-D versus 0-D)

The gain is `G = ⟨n²⟨σv⟩(T)⟩ / (n̄²⟨σv⟩(T̄))`, using parabolic profiles in `x = ρ²` (cylindrical volume measure).
`G_p` is the same ratio at fixed ⟨nT⟩ (fixed W, hence fixed β):

| T̄ (keV) | G (α_n=0, α_T=1; peaking 2) | G (α_n=0.5, α_T=1) | G_p (α_n=0.5, α_T=1) | G_p (α_n=1, α_T=1) |
| --- | --- | --- | --- | --- |
| 5 | 2.14 | 3.88 | 2.69 | 3.24 |
| 7 | 1.70 | 3.01 | 2.09 | 2.47 |
| 10 | 1.33 | 2.28 | 1.58 | 1.83 |
| 15 | 1.05 | 1.72 | 1.19 | 1.33 |
| 20 | 0.93 | 1.46 | 1.01 | 1.10 |

**Conclusion:** at the same ⟨p⟩, peaking with T₀/⟨T⟩ ≈ 2 raises the volume-averaged fusion power by about 1.6× at
10 keV, but by only about 1.0–1.1× at 20 keV. Peaking therefore justifies a lower f_ren at the *lower* barrier
(10 keV). It does not help the upper barrier. This is quantitative support for the Phase 2 finding that M2-type
(1-D) barriers beat 0-D ones. A 1-D lower barrier at T₀ = 20 keV on axis corresponds to ⟨T⟩ ≈ 10 keV.

## 5. Recommended Lean instance (M1-type, stellarator)

**"Stellaris-like" synthetic data** (labelled *synthetic, Stellaris-scale*; geometry from Lion et al. 2025 via
arXiv:2507.12681; ι assumed):

| parameter | value |
| --- | --- |
| a, R, B, ι_{2/3} | 1.3 m, 12.7 m, 9 T, 0.9 |
| V | 425 m³ |
| n_e (flat) | 1.5×10²⁰ m⁻³ (n₁₉ = 15) |
| Z_eff | 1.7 carbon (`f = 0.86`, `r_i = 53/60`, reusing `carbon_fixture`) |
| ISS04 coefficient | `C = 0.134·1.3^2.28·12.7^0.64·15^0.54·9^0.84·0.9^0.41 ≈ 32.45 s·MW^0.61` (enclose with rational brackets as in `iter_coeff_bounds`) |
| α | 0.61 |
| P_aux | ∈ [50, 70] MW |
| f_ren range | **[1.55, 1.75]** |
| window | **T(0) ∈ [10, 22] keV ⇒ T(t) ∈ [10, 22] keV** |

Certificate margins, with Bosch–Hale shifted −1% at the lower barrier and +1% at the upper (`pb5.py`):
- **10 keV**, P_aux = 50 MW, f = 1.55: P_α = 111.5 MW, P_br = 27.5, W = 288.5 MJ, τ_E = 2.26 s, so net
  **+6.5 MW**.
- **22 keV**, P_aux = 70 MW, f = 1.75: P_α = 490.4 MW, P_br = 40.8, W = 634.8 MJ, τ_E = 1.20 s, so net
  **−11.2 MW**.

P_fus at 22 keV ≈ 2.46 GW (below the 2.7 GW design) and β(22 keV) = 3.1%.

The window [10, 20] with f ≤ 1.70 has only −0.7 MW of margin, which is too thin. Use 22 keV.

**Honesty labels for the theorem docstring:**
- f_ren ∈ [1.55, 1.75] is **above** the measured W7-X range (≤ 1.4, transient) and above Warmer's reactor-size
  prediction (1.1–1.3). It is an *assumption on confinement improvement* (QI/high-field), not an extrapolation of
  data.
- The flat 0-D model understates the 10 keV fusion power by about 1.6× relative to peaked profiles, so the 1-D (M2)
  version should get by with f_ren ≈ 1.25–1.3.
- ISS04 uses line-averaged density. Here line average = volume average (flat).

**Alternative, more conservative** (HELIAS 5-B, Warmer's f_ren = 1.2): this is not reachable in this 0-D flat model
at 10 keV. It needs f_ren ≈ 1.7 (n = 1.9×10²⁰, 3 GW). It *is* consistent with Warmer's 1-D, 7 keV, peaked operation
(f ≈ 1.4–1.5 in the peaked column, with He dilution and synchrotron radiation not modelled). So HELIAS is the right
target for a 1-D M2 instance, not for 0-D M1.

## 6. Recommended confinement assumption for M4

- Use ISS04 with **f_ren as an interval hypothesis**, as `H ∈ [H_lo, H_hi]` is used in `ConfinementScaling`. The
  instance values are [1.55, 1.75] for 0-D at Stellaris scale, or about [1.25, 1.5] once the 1-D profile gain is
  proved (M2).
- State alpha heating as `P_α · (1 − f_loss)`. ARIES-CS reports f_loss ≈ 5% in *energy*. The M4 GC theorem
  (`near-axis-quasisymmetry.md`) does not yet certify any f_loss < 1, so a Lean instance should carry
  `f_loss ∈ [0, 0.05]` as an explicit hypothesis. With f_loss = 0.05 the 10 keV margin falls to
  +6.5 − 5.6 = +0.9 MW, so use f_lo = 1.6 if f_loss is included.

## 7. Sources

- Yamada et al., NF 45 (2005) 1684, doi:10.1088/0029-5515/45/12/024 (ISS04).
- Fuchert et al., NF 58 (2018) (W7-X OP1.1 confinement ≈ ISS04). Bozhenkov et al., NF 60 (2020) 066011
  (+30% post-pellet). Baldzuhn et al., PPCF (2019), doi:10.1088/1361-6587/ab3567.
- Warmer et al., FST 68 (2015) "Limits of confinement enhancement for stellarators". Warmer et al., IEEE TPS 44
  (2016) 1576 (HELIAS 5-B systems study: R = 22 m, B = 5.5 T, f_ren = 1.2/1.4, ⟨T⟩ = 7 keV, 10% He).
- Ku et al., FST 54 (2008) 673 / PPPL-4265 (ARIES-CS physics design: B = 5.7 T, ⟨n⟩ = 4.01×10²⁰, ⟨T⟩ = 6.55 keV,
  Z_eff = 1.13, β = 6.4%, V = 444 m³, P_fus = 2436 MW, H_ISS95 ≈ 2). Najmabadi et al., FST 54 (2008) 655.
- Lion et al., Fusion Eng. Des. 214 (2025) 114868 (Stellaris). Geometry figures as quoted in arXiv:2507.12681.
- Bosch & Hale, NF 32 (1992) 611. NRL Plasma Formulary (slowing-down time).
