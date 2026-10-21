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

## Stage 1, continued: gaps 1–4 closed (this session)

All modules below compile with zero warnings and only the standard axioms (`#print axioms`
checked on the main results). None is imported by `PlasmaLean.lean` yet.

### Gap 1: `PlasmaLean/Theory/KAM/CauchyTwoVar.lean` (namespace `…KAM.CauchyTwoVar`)

- `fc2 g k m` is the double Fourier coefficient on `[0,2π]²`, with characters `em k θ = e^{-ikθ}`.
  Supporting lemmas: `coeff_eq_fc2`, `fcoeff2_eq_fc2`, `norm_fc2_le`, `fc2_sub`, `fc2_const_mul`.
  **`fc2_fc2_swap`** is Fubini on `[0,2π]⁴` for jointly continuous integrands.
- **Uniqueness.**
  - `eq_zero_of_coeff_zero` (1-D) uses Mathlib `hasSum_fourier_series_of_summable` on `AddCircle`.
  - `eq_zero_of_fc2_zero` (2-D): a continuous biperiodic function with all `fc2 = 0` is zero.
- **Two-variable Cauchy formula.** `cauchyCoeff f R α = R^{-|α|} fc2 (f(Re^{is}, Re^{it})) α₁ α₂`.
  - `norm_cauchyCoeff_le`: `|c_α| ≤ M/R^{|α|}`.
  - **`hasSum_cauchyCoeff`**: if `f` is jointly holomorphic on the bidisc of radius `R' > R`, then
    `f(z) = ∑ c_α z^α` for `|zᵢ| < R`.
  - The proof chains `cauchy1` (the 1-D formula in parametrised form), `hasSum_ckern` (geometric
    kernel) and `integral_tsum_bdd`.
- **Constructor.** The hypotheses are bundled as `HoloData G ρ' ρ r d d' M`:
  - `G(θ,ψ,z₁,z₂)` is jointly holomorphic on `|Im θ|,|Im ψ| < ρ'`, `|zᵢ| < d'`;
  - `G` is biperiodic;
  - `|G| ≤ M` on `|Im| ≤ ρ`, `|zᵢ| ≤ d`;
  - `0 ≤ r < ρ < ρ'` and `0 < d < d'`.

  From these:
  - `taylorFA G h α ∈ 𝔸` is built from the Fourier coefficients of the Cauchy coefficients.
  - `HoloData.norm_fc2_coeffFun_le` bounds their decay by `M d^{-|α|} e^{-ρ|n|}`. The proof applies
    `norm_fcoeff2_le` inside the Cauchy integral, after `fc2_fc2_swap`.
  - `eval_taylorFA` follows by uniqueness.
  - **`AnaFieldAt.of_holomorphic : AnaFieldAt r (M·geoZ(e^{-(ρ-r)})²) d X`** holds for any `X` that
    equals `G` at real `θ,ψ` and `|zᵢ| < d`.
- **Sanity:** `fc2_const`, `cauchyCoeff_zero_fun`, `cauchyCoeff_const`, `hasSum_cauchyCoeff_const`,
  and the rejected fixture `not_cauchy_bound_half`.

### Gap 2: `PlasmaLean/Theory/KAM/FourierSumHolo.lean` and `TorusFieldAna.lean`

- **Holomorphy of Fourier sums.**
  - `differentiableOn_fourierSumC (hu : InWeighted r u)`: joint holomorphy on the open
    `stripC r ×ˢ stripC r`. The proof uses `hasFDerivAt_tsum_of_isPreconnected` on substrips.
  - `fourierSumC_add_two_pi_left/right`, `fourierSumC_coeff_ofReal`, `norm_fourierSumC_le_of_Bd`.
- **Cylindrical and torus maps.**
  - `cylC R φ Z = (R cos φ, R sin φ, Z)`, with `differentiable_cylC` and `cylC_ofReal`.
  - Exact identities: `norm_imV_cylC_sq` (`|Im|² = (Im R)² cosh²(Im φ) + (Re R)² sinh²(Im φ)
    + (Im Z)²`) and `norm_reV_cylC_sub_sq`.
  - `torusMapC u₁ u₂ θ ψ z₁ z₂ = cylC(K₁+z₁, ψ, K₂+z₂)`, with `differentiableOn_torusMapC` and
    periodicity.
- **`TorusFieldAna`.**
  - `holoData_torus` and **`anaFieldAt_torus`**: `F` holomorphic and bounded by `M` on `U`, with
    the torus neighbourhood mapped into `U`, gives `AnaFieldAt` for `F ∘ torusMapC`.
  - `norm_fourierSumC_sub_re_le`: `|K(θ,ψ) − K(Re θ, Re ψ)| ≤ ‖u‖_ρ − ‖u‖_0`. This is the tool for
    checking the mapping hypothesis.

### Gap 3: `PlasmaLean/Design/CoilFieldComplex.lean` (+ `CoilFieldComplexDist.lean`)

- **The field.** `coilFieldCC = tfFieldCC + polyFieldCC` is the four TF sides (κ = 1/2) plus the
  192 segments of `allSegs filsC`.
  - `coilFieldCC_ofReal`: on `realTube w` (`w < 7/20`) it equals `tfField + polyCoilFieldC`.
- **Distance certificate** (`CoilFieldComplexDist`).
  - `farAll_true` is checked by `decide +kernel` (about 7 s). It is an exact rational bisection
    checker per segment.
  - `filsC_far`: every coil point satisfies `Far (7/20)`, i.e. `|z| ≥ 7/20` or
    `|r − 1| ≥ 7/20`. The numerical minimum is 0.3653.
  - `dist_of_far`: points of `realTube w` are at distance `≥ δ` from the coil when `w+δ ≤ 7/20`.
  - Data bounds: `|κ| ≤ 90485364/2³²`, `‖p‖ ≤ 3`, segment length `≤ 23/10`.
  - `Ka_sub_realTube : Ka aF ⊆ realTube (3/20)`.
- **Neighbourhood.** `coilNbhdP w η = {|r(Re y)−1| < w, |(Re y)₂| < w, |Im y| < η}` is open, with
  the concrete instance `coilNbhd = coilNbhdP (3/20) (3/20)` (`ofRealV_mem_coilNbhd` for `Ka aF`).
- **Holomorphy and bound.**
  - `coilFieldCC_differentiableOn` holds for `η < δ`, `w + δ ≤ 7/20`.
  - Sup bound `norm_coilFieldCC_le ≤ Mcoil w δ η` (closed form), and concretely
    `norm_coilFieldCC_le_concrete ≤ 17400`.
  - The TF axis side (length 2·10⁶) needed the new length-uniform bound `segFieldC_bound_line`.
- **`AnaFieldAt` instances.** `coilAnaFieldP` (general `w, δ, η`) and `coilAnaField` (concrete,
  `M = 17400`) cover each Cartesian component of `coilFieldCC ∘ torusMapC`, given that the
  complexified torus neighbourhood lies in the coil neighbourhood.

### Gap 4: `PlasmaLean/Theory/KAM/AnalyticCompositionLip.lean`

`bd_comp_sub` (constant `C/(d(1−s/d)³)`), `bd_d1_sub` and `bd_d2_sub` (constant
`2C/(d²(1−s/d)⁴)`) are the `Bd ρ` forms of the Lipschitz bounds. Sanity: `bd_comp_sub_zero`.

### Findings that affect stages 2–4

- **The complex strip in ψ is limited by the coil distance.** At `Im ψ = β` the cylindrical map
  has imaginary part ≥ `R sinh β`, and membership in `coilNbhdP w η` needs `η < δ ≤ 7/20 − w`.
  Hence `|Im ψ| ≲ asinh(η/R) ≈ 0.13–0.15` at `R ≈ 1`.
  - The strip pair `(0.8, 0.5)` assumed in `after-kam.md` §2.4.5 is **not** attainable with this
    neighbourhood.
  - `HoloData` uses a common strip for θ and ψ. Stage 2 should either plan with ρ' ≈ 0.13, or
    generalize `HoloData`/`norm_fcoeff2_le` to anisotropic strips (ρ_θ, ρ_ψ). That would be a cheap
    change in `CauchyTwoVar`.
- **The bound M is crude.** `M = 17400` comes from the uniform per-segment bound with
  `(δ²−η²)^{-3/2} ≈ 433`. Per-segment distances, or smaller η, would reduce it by orders of
  magnitude. This matters, because `C = M·geoZ²` enters the KAM smallness condition.
- **What `AnaFieldAt` covers.** It currently handles scalar Cartesian components. The KAM flow
  field uses ratios such as `B^R/B^φ` in cylindrical components. For those, compose `F` with the
  (holomorphic) cylindrical projection and a division, bounded below on the neighbourhood. That
  needs a lower bound on `|B^φ|` on `coilNbhd`, which is not yet proved; it should come from the
  TF dominance, `|B_TF| ≈ 1/(2R)`.
- **Remaining stage-2–4 work.**
  - Stage 2: refit the torus; check the mapping hypothesis `hmap` for the refit (via
    `norm_fourierSumC_sub_re_le` plus `norm_imV_cylC_sq`); produce the sampled residual
    certificate (`Bd_of_samples`).
  - Stage 3: frame and twist.
  - Stage 4: generic `AnaFieldAt`-based KAM step.
