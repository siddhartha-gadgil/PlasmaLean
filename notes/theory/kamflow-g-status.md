# KamFlow*G: status of the generalised KAM interface (N-33 module plan item 3)

Last updated: 31 October 2026. Companion to `dommaschk-kam-certificate.md` (N-33), §2.2 (O1, O2)
and §6 item 3.

## Done (milestone 1): `Design/KamFlowFieldG`, `Design/KamFlowFrameG`

Both compile with zero warnings and standard axioms only (about 3 s and 4 s, under 0.2 GB). Neither
is imported by `PlasmaLean.lean` yet.

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

## Remaining

### `KamFlowStepG` (copy of `KamFlowStep`, 1,226 lines)

- **`SC` fields.**
  - Add `R₀` and `p`, or take them from `F`.
  - Replace the frame-vector bounds `au, az` by bounds `av_R, av_z` of `‖V₀_R‖, ‖V₀_z‖`.
  - Add a bound `aR` of `‖R‖` (today `1 + au`).
  - Keep `au, az` for `avec`/`C₂`.
- **Constants.**
  - `kη1 = sW (av_z + av_R) kE`.
  - `kη2 = bD sR^p (aRt + azt) kE`.
  - `kh = aR^p sD sW`.
  - `kTc = aR^p sD sW² (av_z + av_R) kE`.
  - In `kS`, replace `3 sR` by `p sR`.
  - `mV = max av_R av_z`.
- **Bounds.**
  - `bR` becomes `Bd ρ (F.R u) aR`.
  - `bwD`, `bhN`, `bTcorr` and `bS` change only in these constants.
  - `bdR/bdZ` use `NR = h V₀_R`.
- **Cohomological step.** Replace `dio : Diophantine (ι/2) γ 1` by `DiophantineSplit` (with
  `1 ≤ K`, `0 < d`, `e γ δ₀ ≤ d`). Use `Bd.coh_split` in `bXi20`/`bXi1`, and `.toDiophantine`
  for `ana_xi*`.
  - This is "the Rüssmann constant as a parameter": `g = 2 E1 γ` becomes the split constant.
  - Existing instances pass through `Diophantine.toSplit`.
- **Reality.**
  - `isReal_W` and `isReal_eta1` need `F.isReal_V0R/V0Z`, which exist.
  - `isReal_Ri` uses `isReal_Rof`.
- **Unchanged.** `real_resRp/real_resZp` already exist in `FieldG`, and `bQR/bQZ` (`C₂` via
  `majD2`) carry over verbatim.
- **Effort.** Mechanical. About 1,250 lines, 1–2 sessions. Expect `positivity`/`gcongr` fixes
  where `(1 + au)^3` becomes `aR^p`.

### `KamFlowIterationG` (copy of `KamFlowIteration`, 832 lines)

- `AdmBounds` takes the new `SC` bounds (`‖V₀‖`, `‖R‖`). The displacement budget must
  propagate `‖V₀‖ ≤ av` along the iteration; this is automatic, since `V₀ = K − A` moves with
  `K`.
- `GlobalH` uses the split Diophantine.
- The conclusion `kam_flow_torus` for `F : FlowFieldG` is unchanged in form.
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
  ```
