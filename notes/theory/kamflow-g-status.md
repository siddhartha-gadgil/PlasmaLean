# KamFlow*G: status of the generalised KAM interface (N-33 module plan item 3)

Last updated: 31 October 2026. Companion to `dommaschk-kam-certificate.md` (N-33), §2.2 (O1, O2)
and §6 item 3.

## Done (milestone 1): `Design/KamFlowFieldG`, `Design/KamFlowFrameG`

Both compile with zero warnings and standard axioms only (about 3 s and 4 s, under 0.2 GB). Both are
now imported by `PlasmaLean.lean`.

**Generalised (`FlowFieldG`).**
- **Radial centre.** `R = R₀ + u` (`Rof R₀ u`, field `R₀ : ℝ`).
- **Density exponent.** `w = D/R^p` (field `p : ℕ`). The divergence identity is
  `R ∂_φD − p n_R + R ∂_u n_R + R ∂_z n_z = 0`.
- **Flux primitive.** `α = (P_a/R^{k_a}) dR + (P_b/R^{k_b}) dz` (fields `ka kb : ℕ`).
  - `flux_a/b/c` are stated in solved form (`∂_R b − ∂_z a = w`, `∂_φ a = w X_z`,
    `∂_φ b = −w X_R`, with `Ring.inverse R` powers), at torus points where `R` is a unit.
  - Any polynomial clearing implies them: multiply by `R⁻ᵐ` (`FlowFieldG.eq_of_pow_mul`).
  - The Dommaschk data (`k_a = k_b = p = 7`) need no extra powers of `R`.
- **Moving frame centre.** `A(φ) = (R₀ + a_R, a_z)`.
  - `a_R`, `a_z` are polynomial expressions evaluated at `(0, 0, cos 2φ, sin 2φ)` (`cen`), so
    they are trigonometric polynomials in `ψ`, independent of the torus.
  - `Lt_cen`: `𝓛a = ∂_φa = cenD a`. `dTh_cen`: `∂_θa = 0`.
  - The frame vector is `V₀ = (u − a_R, z − a_z)` (`F.V0R`, `F.V0Z`), and `W₀ = ∂_θK × V₀`
    (`F.W0`).
  - The torsion identity is `P = (D²(X − A' − DX·V₀)) × V₀` (`torsion_poly`).
- **Unchanged.** The polynomial data `D, n_R, n_z, P_a, P_b, P` in `(u, z, c, s, w_R, w_z)`,
  `noW`, the real coefficients, and the field-independent layer of `KamFlowField` (reused).

**Frame (`KamFlowFrameG`).** Every identity of `KamFlowFrame` holds in this generality:
- `frame_decomp_R/Z`, `Eh_decomp` and `frame_det`;
- `torsion_coord`: the centre velocity enters only through `P`;
- `S_coord`: `S = −(∇D·Ê)/D + p Ê_R/R − (∂_θÊ × V₀)/W₀`. The centre velocity cancels, and the
  divergence identity enters with exponent `p` (`Ltw_trA`);
- `eta2_flux` and `avg_eta2` (`⟨η₂⟩ = 0`);
- `linear_residual_R/Z` and `newton_error_R/Z`.

**Reduction and sanity.**
- `FlowField.toG` embeds every `FlowField` (`R₀ = 1`, `p = 3`, `k_a = 1`, `k_b = 2`, centre `0`).
- These agree definitionally or by rewriting: `toG_Dof/Pof/resR/resZ`, `toG_R`, `toG_V0R/V0Z`,
  `toG_W0`, `toG_hN`, `toG_eta1/eta2`, `toG_Tor` and `toG_Scoef`.
- `toG_frameHyp_iff`, `toG_invariant_iff`, and for the rational field `field14G := field14.toG`
  with `field14G_data` and `field14G_invariant_iff`.
- Fixtures: `FlowFieldG.toroidal R₀`, with `toroidal_resR`. The moving-centre fixture is
  `toroidalShift` (`a_R = sin 2φ`), with `toroidalShift_Pof` (`P = −2 cos 2φ · z`) and the
  rejected fixture `toroidalShift_Pof_ne`.

## Done (milestone 2): `Design/KamFlowStepG`

Compiles with zero warnings and standard axioms only (about 6 s, 1.7 GB peak RSS; 1,303 lines).
Checked together with `import PlasmaLean`: no name clashes.

- **Constants `SCG extends SC`.** New fields: `avR`, `avZ` (bounds of `‖V₀_R‖`, `‖V₀_z‖`), `aR`
  (bound of `‖R‖`), `p : ℕ` (the exponent), `dlow`, `Klow` (split Diophantine data; `γ` is now
  the high-mode constant). `au`, `az` stay as bounds of `u, z` (used in `avec`, `C₂`). The
  derived constants (`SCG.kη1 … SCG.kap`) are all redefined in `SCG`:
  - `kη1 = sW (avZ + avR) kE`, `kη2 = bD sR^p (aRt + azt) kE`, `kh = aR^p sD sW`;
  - `kTc = aR^p sD sW² (avZ + avR) kE`, `kS = … + p sR kE δ₀ + sW (avZ + avR) kE/E1`;
  - `mV = max avR avZ`. The rest (`g = 2 E1 γ`, `k20`, `kc`, `k2`, `k1`, `cK`, `kRem`, `kA`,
    `cL`, `kap`, `avec`, `mvec`, `Tq`) have the old formulas.
- **Step hypothesis `FlowFieldG.StepH c ι u z e δ`.** As `FlowField.StepH`, with:
  - `hp : F.p = c.p`;
  - `dio : DiophantineSplit (ι/2) c.dlow c.γ 1 c.Klow`, `hK : 1 ≤ c.Klow`, `hd : 0 < c.dlow`,
    `hlow : exp 1 * c.γ * c.δ0 ≤ c.dlow` (passed to `δ` by `StepH.hlowδ`);
  - `hV0R : Bd ρ (F.V0R u) avR`, `hV0Z : Bd ρ (F.V0Z z) avZ`, `hR : Bd ρ (F.R u) aR`;
  - `hsR : Bd ρ (F.Ri u) sR`, `hsW : Bd ρ (F.Wi u z) sW`, field bounds via `FlowFieldG.Du` etc.;
  - **no `hδ2 : δ₀ ≤ 2/e`** (not needed by `Bd.coh_split`).
- **Main theorem `FlowFieldG.StepH.kam_step`**: analytic `ΔR, Δz`,
  `‖ΔK‖_{ρ−2δ} ≤ cK e/δ²`, `‖𝓛ΔK‖_{ρ−2δ} ≤ cL e/δ²`, `‖E(K+ΔK)‖_{ρ−2δ} ≤ κ e²/δ⁴` (same shape
  as `FlowField.StepH.kam_step`). Components: `bXi20`/`bXi1` (by `Bd.coh_split`), `bdR/bdZ`,
  `bLdR/bLdZ`, `bER'/bEZ'`, `bQR/bQZ`. Qualitative uses: `StepH.dioG` (`.toDiophantine`,
  constant `min dlow γ`), `dioG_pos`.
- **Reality**: `FlowFieldG.FrameHyp.isReal_dRs` (and `isReal_xi1/xi2/eta1/eta2/Tor/…`).
- **Correction**: `FlowFieldG.xi20/cbar/xi2/xi1/dRs/dZs`.
- **Reduction.** `SC.toSCG` (`p = 3`, `avR = au`, `avZ = az`, `aR = 1 + au`, `dlow = γ`,
  `Klow = 1`): `toSCG_cK`, `toSCG_cL`, `toSCG_kap` (and `kη1, kη2, kh, kTc, τ', mV, kS, kRem`,
  `toSCG_taylor`) are **equalities**. `FlowField.StepH.toG` (needs `exp 1 * δ₀ ≤ 1`; torus A has
  `δ₀ = r_A/7 ≈ 0.018`) and `field14_stepH_toG`. `FlowField.toG_dRs`: the correction is the
  same. Degenerate sanity: `SCG.kh_of_p_zero`.

## Remaining

### `KamFlowIterationG` (copy of `KamFlowIteration`, 832 lines)

What it needs from `KamFlowStepG` (all available):
- `FlowFieldG.StepH.kam_step` (the eight-part conclusion, same order as before) and
  `FlowFieldG.FrameHyp.isReal_dRs`; `FlowFieldG.dRs/dZs` for `stepK`.
- `SCG.withρ` (define as `{ c with ρ := ρ }`; with `extends` this updates `toSC.ρ`). All
  derived constants are independent of `ρ` (`rfl`), as before.
- `AdmBounds` (G): the `AdmBounds` fields, with `F.Ri u`, `F.Wi u z` (G versions), plus
  `hV0R`, `hV0Z`, `hR`. The admissibility hypothesis must supply them for every `μ`-close torus.
  `‖V₀‖`: `V₀ − V₀⁽⁰⁾ = u − u₀` (the centre does not depend on the torus), so `Close` already gives `avR = ‖V₀_R⁽⁰⁾‖ + μ`
  by `Bd.add`; similarly `aR = ‖R⁽⁰⁾‖ + μ`.
- `GlobalH` (G): `dio : DiophantineSplit (ι/2) c.dlow c.γ 1 c.Klow`, `hK`, `hd`, `hlow`, `γ_pos`,
  `hp : F.p = c.p`; drop `hδ2`. `hlow` is stated at `δ₀`, so it holds at every `δ_j ≤ δ₀`
  (`stepH_of_adm` passes `hδ0`).
- `stepH_of_adm` (G): field-by-field as in `KamFlowIteration`, plus `hp`, `hK`, `hd`, `hlow`,
  `hV0R/hV0Z/hR` from `AdmBounds`.
- `cauchy_conv` uses `hE1`, unchanged. The `kamExact` part is field-independent.
- The conclusion `kam_flow_torus` for `F : FlowFieldG` is unchanged in form.
- **Chain sanity**: with `field14_stepH_toG` and `SC.toSCG_*`, the torus-A `KamH` instantiates the
  G-hypotheses once `GlobalH.toG`/`KamH.toG` adapters are written (needs `exp 1 * δ₀ ≤ 1`;
  `AdmBounds` adds `hV0R = hu`, `hR = bR`).
- **Effort.** About 850 lines, one session.

### Sanity for the chain

At the end, re-derive `KamTorusAExact.torusA_exact` through `field14G`, or at least check that
`torusA`'s `SC`/`KamH` instantiate the G-hypotheses with `R₀ = 1`, `p = 3`, `av = a` and
`Diophantine.toSplit`. That adapter already exists in `Theory/KAM/CohomologicalLow`.

### Total

About 2,100 more lines (StepG + IterationG), each light (seconds, ≪ 1 GB). The interface choice
(solved-form flux identities and the polynomial centre) needs no change for the Dommaschk field
data of N-33 §2.4.

## Shared files (owner to add)

- `PlasmaLean.lean`, after line 250 (`KamFlowIterationS`):
  ```
  public import PlasmaLean.Design.KamFlowFieldG
  public import PlasmaLean.Design.KamFlowFrameG
  ```
  (both present). Add after line 252 (`KamFlowFrameG`):
  ```
  public import PlasmaLean.Design.KamFlowStepG
  ```
- `scripts/check_axioms.lean`:
  ```
  #print axioms PlasmaLean.Design.KamNewton.FlowField.toG
  #print axioms PlasmaLean.Design.KamNewton.field14G_invariant_iff
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.toroidalShift_Pof_ne
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.FrameHyp.torsion_coord
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.FrameHyp.S_coord
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.FrameHyp.eta2_flux
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.FrameHyp.newton_error_R
  #print axioms PlasmaLean.Design.KamNewton.FlowField.toG_Scoef
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.StepH.kam_step
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.FrameHyp.isReal_dRs
  #print axioms PlasmaLean.Design.KamNewton.FlowField.StepH.toG
  #print axioms PlasmaLean.Design.KamNewton.field14_stepH_toG
  #print axioms PlasmaLean.Design.KamNewton.SC.toSCG_kap
  #print axioms PlasmaLean.Design.KamNewton.FlowField.toG_dRs
  ```
