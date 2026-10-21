# Coil-field KAM (target 1, option (a)): status

Goal: `PolygonCoilKam.coilStellarator_confined_forever`, i.e. all-time field-line confinement for
the coil field `tfField + polyCoilFieldC`, obtained by refitting a KAM torus to the coil field
(`after-kam.md` §2.2–2.4). The ι_A Diophantine certificate is reused.

Status tags follow `README.md`. Everything listed under "Stage 1: done" compiles with zero warnings
and uses only the standard axioms (`#print axioms` checked). None of the three modules is imported
by `PlasmaLean.lean` yet.

## Stage 1: analytic infrastructure (done, this session)

### `PlasmaLean/Theory/KAM/StripPaleyWiener.lean`

Namespace `PlasmaLean.Theory.KAM.PaleyWiener`.

- **Contour shifts.**
  - `integral_eq_integral_shift` (1-D, periodic, rectangle Cauchy).
  - `iterated_integral_shift` (2-D). The hypothesis is joint `DifferentiableOn ℂ` on
    `stripC ρ' ×ˢ stripC ρ'`, plus biperiodicity.
  - `integral_integral_swap_of_continuous` (Fubini on a rectangle).
- **Cauchy / Paley–Wiener bounds.**
  - `norm_fcoeff2_le`: `|f_{k,m}| ≤ M e^{-ρ(|k|+|m|)}` for `|f| ≤ M` on `|Im| ≤ ρ < ρ'`.
  - `norm_coeff_le_of_holo` (for `x : FA` with `eval x = f` on ℝ²).
  - `wnorm_le_of_decay` and `Bd_of_holo`: `‖x‖_r ≤ M·geoZ(q)²` with `q = e^{-(ρ-r)}`, where
    `geoZ q = (1+q)/(1-q)`.
- **Aliasing.**
  - `dft2` is the N₁×N₂ grid DFT.
  - `sum_roots_of_unity` and `sum_mode_samples` give discrete orthogonality.
  - `dft2_eval` is the aliasing identity `dft_n = ∑_{p≡n} x_p`.
  - `wnorm_le_dft`: `‖x‖_r ≤ ∑_{box} |dft_n| e^{r|n|} + 2·(mass outside box)`, assuming `N_i > 2K_i`.
  - `tsum_outMass_le`: the mass outside the box is at most `M·geoZ q·(tailZ q K₁ + tailZ q K₂)`,
    with `tailZ q K = 2q^{K+1}/(1-q)`.
- **`Bd_of_samples`**, the residual-certificate interface. Given an analyticity bound M on the strip
  ρ and the real samples of f, it returns an explicit `Bd r x B`.
- **Sanity:** `dft2_mode`; the rejected fixture `dft2_alias_fixture`; `geoZ_zero`, `tailZ_zero`,
  `tailZ_le_geoZ`.

### `PlasmaLean/Theory/Fields/BiotSavartComplex.lean`

Namespace `PlasmaLean.Fields.BiotSavartComplex`.

- **Definitions.** Complex points are `CVec = Fin 3 → ℂ`, with `dotC` (bilinear), `crossC`,
  `ofRealV`/`reV`/`imV` and the Hermitian norm `hnorm`. The segment quantities are:
  - `segQ p q y t = w·w`;
  - `segIntC = ∫₀¹ segQ^(-3/2)` (principal branch);
  - `segFieldC κ p q y = κ·segIntC • (a × b)`;
  - `segDomain = {y | ∀ t ∈ [0,1], Re segQ > 0}`, which is open (`isOpen_segDomain`).
- **Real points.** `segFieldC_ofReal`: at every real point `segFieldC = segClosed`, the existing
  closed form (`PolygonCoilSegment`).
- **Bound.** `segFieldC_bound`: assume `‖Im y‖ < d ≤ dist(Re y, segment)` and `‖Re y − p‖ ≤ D`. Then
  `hnorm ≤ |κ|·|q−p|·√(D²+η²)/(d²−η²)^{3/2}`. The sup-norm version is `segFieldC_bound_sup`. The
  supporting lemmas are `re_segQ`, `norm_segIntC_le` and `hnorm_crossC_le`.
- **Holomorphy.** `segFieldC_differentiableOn` on `segDomain`, and
  `segFieldC_differentiableOn_boundRegion`. The proof differentiates under the integral sign with an
  explicit derivative (`segDF`) and a uniform bound on balls (`segDomain_ball`).
- **Sanity:** `segFieldC_zero_kappa`, `segFieldC_bound_real`, `segDomain_ofReal` and the rejected
  fixture `not_mem_segDomain_endpoint`.

### `PlasmaLean/Theory/KAM/AnalyticComposition.lean`

Namespace `PlasmaLean.Theory.KAM.AnalyticComposition`. Mathlib has no Hartogs/Osgood and no
polydisc Cauchy formula, so this layer works with **two-variable power series with Banach-algebra
coefficients** that satisfy Cauchy majorants.

- **Definitions** (in any complete normed commutative ℂ-algebra):
  - `Majorized c C d` means `‖c_α‖ ≤ C/d^{|α|}`;
  - `comp c h = ∑ c_α h₁^{α₁} h₂^{α₂}`;
  - the partial-derivative series `d1`, `d2`, and `dcomp = d1·k₁ + d2·k₂`.
- **Bounds.** Write x = s/d, for ‖hᵢ‖ ≤ s < d or ‖hᵢ‖+‖kᵢ‖ ≤ s:
  - `comp_summable_and_le`: ‖comp‖ ≤ C/(1−x)²;
  - `d1_summable_and_le`, `d2_summable_and_le`: C/(d(1−x)³);
  - `norm_comp_sub_le`: Lipschitz constant C/(d(1−x)³);
  - `norm_d1_sub_le`, `norm_d2_sub_le`: Lipschitz constant 2C/(d²(1−x)⁴);
  - **`comp_taylor`**: ‖comp(h+k) − comp h − dcomp h k‖ ≤ C/(d²(1−x)⁴)·(‖k₁‖+‖k₂‖)². So ½M₂ is
    16C/d² at s = d/2, not the 8C/d² estimated in `after-kam.md`.
- **Strip-algebra (`Bd ρ`) versions:** `bd_comp`, `bd_d1`, `bd_d2`, `bd_comp_taylor`.
- **Interface `AnaFieldAt ρ C d X`.** It has:
  - coefficients `c : ℕ×ℕ → FA` with `Bd ρ (c α) (C/d^{|α|})`;
  - pointwise Taylor convergence `hasSum_eval` of `X θ ψ z₁ z₂`, the field written around the
    torus point K₀(θ,ψ).

  `AnaFieldAt.comp_eval` then gives `eval (compFA h) = X θ ψ (eval h₁) (eval h₂)` for `Bd ρ hᵢ b`
  with `b < d`.
- **Sanity:** `comp_zero_series`, `comp_zero`, `comp_const`, `comp_monomial` and the rejected fixture
  `not_summable_at_radius`.

## Gaps remaining inside stage 1

1. **Constructing `AnaFieldAt` from a holomorphic field.** This is the multivariable Cauchy formula on
   a bidisc: `X` holomorphic and bounded by `M` on the polydisc of radius `d` gives Taylor
   coefficients with `|∂^αX/α!| ≤ M/d^{|α|}` and `hasSum`. Mathlib only has the 1-D version.
   - Route: iterate the 1-D `cauchyPowerSeries` / `hasSum_taylorSeries_on_ball`. The coefficient
     `a_n(z₂) = (2πi)⁻¹∮X(ζ,z₂)(ζ−c)^{-n-1}dζ` is holomorphic in z₂, by a 1-parameter version of the
     `hasFDerivAt_integral_of_dominated_of_fderiv_le` argument already used in BiotSavartComplex.
   - Then put the coefficients c_α into FA, with Fourier decay, via `Bd_of_holo`. This loses the
     factor `geoZ(q)²`.
2. **Holomorphy of the complexified torus map.** `fourierSumC` (WeightedEll1Z2) is bounded on the
   strip, but its joint `DifferentiableOn ℂ` on `stripC ρ ×ˢ stripC ρ` is not proved. It is needed
   so that (θ,ψ) ↦ B_c(K(θ,ψ)) satisfies the hypothesis of `Bd_of_samples`.
3. **From one segment to the coil field.**
   - Sum `segFieldC_bound` over the 192 segments of `polyCoilFieldC` and the TF rectangle.
   - Holomorphic cylindrical coordinates (R, φ, Z) ↦ (R cos φ, R sin φ, Z), with complex φ = ψ.
   - Membership of the complexified torus in every `segDomain`. This needs a certified distance from
     the torus neighbourhood to the coils, with margin d > η: about 0.25 against 0.15
     (`after-kam.md` §2.4.5).
4. **`Bd`-form Lipschitz bounds** (`norm_comp_sub_le`, `norm_d*_sub_le` in the strip norm). The
   lifting used in `bd_comp_taylor` applies directly.

## Stage 2: oracle refit and sampled residual certificate (not started)

- High-precision Galerkin–Newton refit of the ι_A torus to B_c (`tfField + polyCoilFieldC`, not the
  ideal ∇φ). Expected size: N ≈ 40, M ≈ 64, about 10⁴ dyadic coefficients at ~100 bits. Run a pilot
  on one grid line first.
- Residual certificate via `Bd_of_samples`:
  - exact or interval evaluation of E = D·𝓛K₀ − n at N_θ × N_ψ ≈ 170 × 300 real points (about
    2.5×10⁴ after σ-symmetry, ~5×10⁶ segment evaluations, using `segClosed` and the `Bseg` checker
    with square-root brackets);
  - an analyticity bound M″ ≈ 10 on the strip (0.8, 0.5), from gaps 2–3 together with
    `segFieldC_bound`.
  - Target: e₀ ≈ 10⁻²¹ in ℓ¹_{0.1257}, against a tolerance of 5.7×10⁻¹⁹.
- The certificate must be an explicit proof term (SubsetSum pattern), one constructor per grid
  point or DFT block.
  - The DFT sums over ~5×10⁴ points need an exact or interval summation scheme with a checked
    rounding budget.
  - Keep memory ≤ 6 GB per process: split into chunked modules.

## Stage 3: frame and twist for the refitted torus (not started)

- Surrogate certificates as in `KamTorusASurrogate*`, recomputed for the refitted K₀: the frame
  (normal and torsion), the twist constant and the c_K, c_L bounds. The values should be close to
  torus A's (κ ≈ 5.7×10⁹).
- The divergence-free and flux identities for B_c hold at real points: div B_c = 0, and the segment
  vector potential A = κ v̂ ln((|b|+b·v̂)/(|a|+a·v̂)) gives the flux primitive. Transport them to FA
  by `ext_eval`; neither identity is formalized yet.

## Stage 4: generic analytic-FlowField KAM step and application (not started)

- **Generic step.** Generalize the `KamFlow*` FlowField interface, which today requires
  `PolyExpr`/`PolyExprS` field expressions. Replace the polynomial majorants (`maj`, `majD`,
  `majD2`, `C2`) by `AnaFieldAt` together with `bd_comp`, `bd_d1`/`bd_d2`, `bd_comp_taylor` and
  the Lipschitz bounds. The Taylor constant becomes 16C/d² (or C/(d²(1−s/d)⁴) for general s), and
  the radius condition ‖h‖ ≤ s < d has to be tracked through the iteration.
- **Application.** Then:
  - `coilTorus_exact` (exact invariant torus of B_c within 10⁻¹⁰ of the refit);
  - the trapping transfer via `ODEGlobal` (B_c is C¹ off the coils);
  - `PolygonCoilKam.coilStellarator_confined_forever`.
