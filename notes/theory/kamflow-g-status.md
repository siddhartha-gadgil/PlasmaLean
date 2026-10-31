# KamFlow*G: status of the generalised KAM interface (N-33 module plan item 3)

Last updated: 31 October 2026 (milestone 3). Companion to `dommaschk-kam-certificate.md` (N-33), §2.2 (O1, O2)
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

## Done (milestone 3): `Design/KamFlowIterationG`, `Design/KamTorusAExactG`

Both compile with zero warnings and standard axioms only (`KamFlowIterationG`: 816 lines, about
4 s, 1.6 GB peak RSS; `KamTorusAExactG`: 70 lines, about 5 s, 1.6 GB, all its imports are in
the default build). Checked together with `import PlasmaLean`: no name clashes.

**Iteration (`KamFlowIterationG`).**
- Constants: `SCG.withρ` (`{ c with ρ := ρ }`; sanity `withρ_ρ`, `withρ_kap`), and the
  generalised scalar sequences `SCG.eN` (`kamExact c.kap c.δ0 e₀`), `SCG.SK/St/SL`. The strips
  and losses reuse `rhoN c.toSC`, `delN c.toSC`, `rInf c.toSC` (they depend only on `ρ`, `δ₀`).
- `FlowFieldG.AdmBoundsG c ι ρ u z`: the old fields (with `F.Ri`, `F.Wi`) plus `hV0R`, `hV0Z`,
  `hR`. Helpers for the admissibility proof: `AdmBoundsG.bV0R_of_close`, `bV0Z_of_close`,
  `bR_of_close` (`‖V₀(u)‖ ≤ ‖V₀(u₀)‖ + μ`, `‖R(u)‖ ≤ ‖R(u₀)‖ + μ` from `Close`).
- `FlowFieldG.GlobalHG c ι`: `hp : F.p = c.p`, `dio : DiophantineSplit (ι/2) c.dlow c.γ 1 c.Klow`,
  `hK`, `hd`, `γ_pos`, `hlow : exp 1 * γ * δ₀ ≤ dlow`, `hτ'`, `hC2R/Z`, `hac`, `hE1`, `hcb`
  (no `hδ2`).
- `FlowFieldG.stepH_of_admG`, `stepK`, `iterK` (`iterK_zero`), `KamHG` (same fields as
  `FlowField.KamH`), `InvG`.
- **Main theorem `FlowFieldG.KamHG.kam_flow_torus`**: `K : F.KamHG c ι u₀ z₀ e₀ μ →
  ∃ u z, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ F.resR ι u z = 0 ∧ F.resZ ι u z = 0 ∧
  Close (rInf c.toSC) ι u z u₀ z₀ μ` (same shape as `FlowField.KamH.kam_flow_torus`; reality of
  the limit included).
- Reduction: `FlowField.GlobalH.toG` (needs `exp 1 * δ₀ ≤ 1`), `FlowField.AdmBounds.toG`,
  `FlowField.KamH.toG` (needs `exp 1 * δ₀ ≤ 1`), `FlowField.toG_Talg`, `FlowField.toG_dZs`,
  `FlowField.toG_stepK`, `FlowField.toG_iterK` (the generalised iterates of `F.toG` **are** the
  old ones).

**Chain sanity (`KamTorusAExactG`).** `cA_exp_δ0 : exp 1 * cA.δ0 ≤ 1`;
`cA_kamHG : field14G.KamHG cA.toSCG iota u₀ z₀ e0A μA` (from `cA_kamH` by `KamH.toG`);
`torusA_exactG` (exact real analytic invariant torus of `field14G` on `r_A/7`, `μA`-close);
`torusA_exact_viaG`: **the statement of `torusA_exact`, re-derived** through the generalised
theorem and `field14G_invariant_iff`; `torusA_iterK_G` (same iterates, hence the same torus);
`cA_toSCG_consts` (same `cK`, `cL`, `κ`).

Plan item 3 is complete (about 4,000 lines over the four `G` modules).

## What the Dommaschk instantiation (N-33 items 5–10) needs from this interface

To call `FlowFieldG.KamHG.kam_flow_torus` for `dkField` and torus A of the Dommaschk target:
1. **Item 5, `dkField : FlowFieldG`**: `R₀`, `p = k_a = k_b = 7`, the polynomials
   `Dp, nRp, nZp, Pap, Pbp, Pp, aRp, aZp` (the centre polynomials in `c, s` only), and the fields
   `noW_*`, `real_*`, `divFree`, `flux_a/b/c` (solved form, at points where `R` is a unit),
   `torsion_poly`.
2. **Item 4 (done, `DiophantineSplit` for torus A)**: `GlobalHG.dio` with `Klow` low modes,
   `dlow = γ_low`, `γ` the high-mode constant (0.3645), `hK`, `hd`, and the loss threshold
   `hlow : e γ δ₀ ≤ dlow` (a closed numeric fact once `δ₀` is chosen; with `δ₀ = r/7` small it
   is far from tight).
3. **Item 9, constants `cDK : SCG`**: all `SC` fields plus `avR`, `avZ`, `aR`, `p = 7`, `dlow`,
   `Klow`; then `hτ' : 0 < cDK.τ'`, `hC2R/Z` (Taylor constant as `PolyExpr.majD2` at
   `avec + Tq • mvec`), `hac`, `hE1`, `hcb`, `hκ`, `hsmall`, `hcK`, `hcL`, `hμK/t/L` — closed
   numeric checks on the `SCG.*` derived constants (unfold set: `SCG.cK, k1, k2, kc, k20, g,
   kη1, kη2, kh, kE, tTot, τ', kTc, eM, mA, mV, cL, kA, XRb, XZb, kRem, kS, kap`).
4. **Item 8, `hadm`**: for every `ρ ∈ [ρ₀ − 6δ₀, ρ₀]` and every analytic `μ`-close torus, an
   `AdmBoundsG cDK ι ρ u z`: frame (units and analytic inverses of `D`, `R`, `W₀`), torus bounds,
   field bounds (`Dof, Du, Dz, nR, …` via majorants at `avec`-type bounds), inverse bounds
   `sD, sR, sW`, torsion `tT` and twist `τ`. The frame-vector and `R` bounds come for free from
   the initial torus by `bV0R_of_close`, `bV0Z_of_close`, `bR_of_close` (so set
   `avR = ‖V₀_R⁽⁰⁾‖ + μ`, etc.).
5. **Item 7, initial error**: `e0R/e0Z : Bd ρ₀ (dkField.resR/Z ι u₀ z₀) e₀`, plus `ana_*`,
   `real_*` of the data torus and `hθ : θ = e₀/δ₀⁴`, `hδ0`, `hρ6`.
6. **Item 10** consumes the conclusion unchanged: `resR = resZ = 0` (`D 𝓛K = n`), reality, and
   `Close (rInf cDK.toSC) …`, with `rInf cDK.toSC = ρ₀ − 6δ₀`.

## Shared files (owner to add)

- `PlasmaLean.lean`, after line 253 (`KamFlowStepG`):
  ```
  public import PlasmaLean.Design.KamFlowIterationG
  public import PlasmaLean.Design.KamTorusAExactG
  ```
  (`KamTorusAExactG` imports only `KamTorusAExact`, already in the default build through
  `RationalStellaratorConfinedForever`, and is light.)
- `scripts/check_axioms.lean` (milestones 1–2 lines, if not yet added):
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
  and for milestone 3:
  ```
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.KamHG.kam_flow_torus
  #print axioms PlasmaLean.Design.KamNewton.FlowFieldG.AdmBoundsG.bV0R_of_close
  #print axioms PlasmaLean.Design.KamNewton.FlowField.KamH.toG
  #print axioms PlasmaLean.Design.KamNewton.FlowField.toG_iterK
  #print axioms PlasmaLean.Design.KamNewton.torusA_exactG
  #print axioms PlasmaLean.Design.KamNewton.torusA_exact_viaG
  ```

## Item 5: the Dommaschk target in flow form (31 October 2026)

**Status:** the data, all identities and the identification with `field candidate` compile.
The instance `dkField : FlowFieldG` **cannot be built with the current interface**, because of
an obstruction proved in Lean (below). With a small interface extension it is a 30-line
definition, checked in a scratch worktree (not committed).

**Files** (new; all zero warnings, standard axioms). None is imported by `PlasmaLean.lean` yet.

| Module | Content | Time, peak RSS |
| --- | --- | --- |
| `Design/DommaschkKamPoly` | `DkPoly`: sparse rational polynomials in `(u, z, c, s)` with checker operations `merge`, `scale`, `mul`, `dU/dZ/dC/dS`, `phiS`, `atZero`, `AO`. Soundness (`ev_merge`, `ev_mul`, …) is unconditional. Bridges: `eval_toPE`, `pd_toPE_U/Z/C/S`, `phiD_toPE`; `ev_congr_AO`, `AO_phiS` | 5 s, 1.6 GB |
| `Design/DommaschkKamFieldData` | generated data: `dD, dnR, dnZ, dPa, dPb, dPc` (344/362/328/309/362/3 terms), `dQ`, `Kq`, the `R`-form data `dDR, dnRh, dnZR`, and the denominators `NDn, NRn, NZn, Lw` | 5 s, 1.6 GB |
| `Design/DommaschkKamFieldCheck` | kernel checks `divCombo_eq`, `faCombo_eq`, `fbCombo_eq`, `fcCombo_eq`, `obsCombo_eq`, `AO_dQ` (`kernel_fact`) | 8 s, 2.0 GB |
| `Design/DommaschkKamField` | the interface-shaped identities and the obstruction | 5 s, 1.6 GB |
| `Design/DommaschkKamIdentCheck`, `…CheckD`, `…CheckR` | kernel checks: the substitution `R = R₀ + u` (`subst_D/nR/nZ`), exact conversion (`convOK_*`, `LW_int`), the Cartesian identities `ident_nZ`, `ident_D`, `ident_nR` (`degCheck`: `CylAlgebra.sliceCheck` sliced by `R`-degree) | 12 s / 9 s / 10 s; 2.1 / 2.9 / 3.0 GB |
| `Design/DommaschkKamIdent` | the identification theorems | 5 s, 1.6 GB |

The generator is `scripts/dommaschk_kam/emit_flowfield.py`. It validates every identity and
every kernel combination by an exact Python mirror of the Lean checkers before it writes, and
checks `D = R⁷B_φ`, `n_R = R⁸B_R`, `n_z = R⁸B_z` exactly at rational points against the Cartesian
potentials parsed from `DommaschkQA2RData.lean`.

**Choices.**
- **Centre and exponents.** `R₀ = 29/32` (`dkR0`, the middle of torus A's `R`-range), `u = R − R₀`.
  The exponents are `p = k_a = k_b = 7`.
- **Polynomials.**
  - `D = R⁶(1 + ∂_φV) = R⁷B_φ`, `n_R = R⁸B_R`, `n_z = R⁸B_z`.
  - `P_a = R⁸∂_zW − zR⁶` and `P_b = −R⁸∂_RW`, where `W` is the `φ`-antiderivative of the
    oscillating part of `V`.
  - `P_c = −c₀R²/2`, with `c₀ = −0.0239…` the coefficient of the axisymmetric potential `z`.
- **`φ`-encoding.** `c = cos 2φ`, `s = sin 2φ`, with `φ` the cylindrical angle (the strip
  algebra's `cS`, `sS`).
  - The harmonics `m = 2, 4, 6` are the homogeneous harmonic polynomials `Re/Im (c + i s)^{m/2}`.
  - `phiD` acts on them exactly, so every identity holds as a polynomial identity in independent
    `(u, z, c, s)`. The relation `c² + s² = 1` is never used.
- **Torsion.** `Pp aR aZ` is *defined* by the torsion formula for any angle-only centre
  `(aR, aZ)`, so `torsion_poly` holds for every centre chosen later.

**Identities (`DommaschkKamField`), at every `xB u z`.**
- `divFree`, `flux_a` and `torsion_poly aR aZ hR hZ` are exactly the fields of `FlowFieldG`.
- `flux_b'` and `flux_c'` are the flux identities **with** the `dφ`-component:
  - `phiD Pap · R⁻⁷ − pd 0 Pcp = nZ · R⁻⁷`;
  - `phiD Pbp · R⁻⁷ − pd 1 Pcp = −(nR · R⁻⁷)`.
- Side conditions: `noW_Dp/nRp/nZp`, `real_Dp/nRp/nZp`, `real_Pp`, `realConsts_toPE`.
- Sanity: `Pp_zero_centre`, `R7l_ne`, and the `DkPoly` fixtures.

**Obstruction.** `no_primitive_without_dphi ka p Pa` states that
`phiD Pa R^{-ka} = nZ R^{-p}` holds at no family of torus points. `no_flowFieldG` deduces that no
`FlowFieldG` has `R₀ = 29/32` and this `n_z`.
- **Proof.** At `u = z = 0`, take the `φ`-mean (`avg`). The left side is a `dPh`, so its mean is
  0. The mean of `n_z` is `c₀R₀⁸ ≠ 0` (`avg_nZ`, via `obsCombo_eq`).
- **Physics.** `B_z` has `φ`-mean `c₀`. So the flux of `B` through a horizontal annulus swept
  around the axis is `πc₀(R₂² − R₁²) ≠ 0`.
- **Consequence.** The primitive needs a `dφ`-term. The N-33 §2.4 remark "no dφ-component" is
  wrong for this candidate: it overlooked `⟨B_z⟩ = c₀`.

**Interface extension needed (coordinator decision; edits to existing files).** This is the
`FlowFieldS` pattern.
1. **`KamFlowFieldG`.**
   - Add the field `Pcp : PolyExpr ℂ (Fin 6)` after `Pbp`.
   - `flux_b` becomes `phiD (xB u z) Pap * R⁻¹^ka - pd (xB u z) 0 Pcp = eval nZp * R⁻¹^p`.
   - `flux_c` becomes `phiD (xB u z) Pbp * R⁻¹^kb - pd (xB u z) 1 Pcp = -(eval nRp * R⁻¹^p)`.
   - `toroidal` and `toG` get `Pcp := const 0`. In `toG.flux_b/c`, first
     `rw [show pd (xB u z) i (const 0 : PolyExpr ℂ (Fin 6)) = 0 from rfl, sub_zero]`.
2. **`KamFlowFrameG`.**
   - Add `def Pc : FA := PolyExpr.eval (xB u z) F.Pcp`.
   - `BF := aF ∂_φu + bF ∂_φz + Pc`.
   - In `eta2_flux`, add
     `have hPc : dTh (F.Pc u z) = pd 0 Pcp * Rt u + pd 1 Pcp * zt z := H.dTh_evalB F.Pcp`.
     `hBF` gains `+ dTh (F.Pc u z)` (with `dS_add … (H.ana_evalB F.Pcp)`), and the final rewrite
     uses `hPc`. The `linear_combination` is unchanged.
3. **Nothing else.** `KamFlowStepG` uses only `avg_eta2`, and `KamFlowIterationG` and
   `KamTorusAExactG` are untouched.

Checked in a scratch worktree: with this 106-line diff, `KamFlowFieldG`, `KamFlowFrameG`,
`KamFlowStepG`, `KamFlowIterationG` and `KamTorusAExactG` all build. The instance below builds too:
```lean
def dkFieldC (aR aZ : SP) (hR : AO aR = true) (hZ : AO aZ = true) : FlowFieldG where
  R₀ := dkR0; p := 7; ka := 7; kb := 7
  Dp := Dp; nRp := nRp; nZp := nZp; Pap := Pap; Pbp := Pbp; Pcp := Pcp; Pp := Pp aR aZ
  aRp := toPE aR; aZp := toPE aZ
  noW_Dp := noW_Dp; noW_nRp := noW_nRp; noW_nZp := noW_nZp
  real_Dp := real_Dp; real_nRp := real_nRp; real_nZp := real_nZp; real_Pp := real_Pp aR aZ
  real_aRp := realConsts_toPE aR; real_aZp := realConsts_toPE aZ
  divFree := divFree; flux_a := flux_a; flux_b := flux_b'; flux_c := flux_c'
  torsion_poly := torsion_poly aR aZ hR hZ
def dkField : FlowFieldG := dkFieldC [] [] rfl rfl
```
After the extension, `no_flowFieldG` takes the extra hypothesis `F.Pcp = const 0`. The proof
gains `rwa [hc, show pd (xB u z) 0 (const 0 : PolyExpr ℂ (Fin 6)) = 0 from rfl, sub_zero] at h`.
That was also checked.

**Identification (`DommaschkKamIdent`).** Let `B = field candidate (cylPoint R φ z)` with
`R > 0`. Its cylindrical components are `cylBR = cos φ B_x + sin φ B_y`,
`cylBphi = −sin φ B_x + cos φ B_y` and `cylBz = B_z`. Evaluate the polynomials at
`ptC R φ z = (R − R₀, z, cos 2φ, sin 2φ, 0, 0) : Fin 6 → ℂ`.
- `Dp_ident`: `eval (ptC R φ z) Dp = ↑(R⁷ · cylBphi R φ z)`.
- `nRp_ident`: `n_R = ↑(R⁸ · cylBR R φ z)`.
- `nZp_ident`: `n_z = ↑(R⁸ · cylBz R φ z)`.
- `flow_ident`: if `cylBphi ≠ 0`, then `D ≠ 0`, `n_R/D = ↑(R·B_R/B_φ)` and `n_z/D = ↑(R·B_z/B_φ)`.
  These are the field-line equations `dR/dφ`, `dz/dφ` of `field candidate`.

For item 10:
- In the strip algebra, `eval (PolyExpr.eval (xB u z) e) θ ψ` is `e` at
  `(u(θ,ψ), z(θ,ψ), −sin ψ, cos ψ, 0, 0)` (`KamFlowField.eval_polyExpr`).
- With `ψ = 2φ − π/2`, this is `ptC (R₀ + u) φ z`, once `u` and `z` are real.

**Remaining for item 5:** only the interface decision above. Then add the instance (as
`Design/DommaschkKamInstance` or in `DommaschkKamField`) and adjust `no_flowFieldG`. The moving
centre is a parameter of `dkFieldC`; it is to be chosen with the torus data (items 6–8).

**Shared files (owner to add).**
- `PlasmaLean.lean`, after line 301 (`DommaschkKamDio`); light modules, about 60 CPU-s in total:
  ```
  public import PlasmaLean.Design.DommaschkKamPoly
  public import PlasmaLean.Design.DommaschkKamFieldData
  public import PlasmaLean.Design.DommaschkKamFieldCheck
  public import PlasmaLean.Design.DommaschkKamField
  public import PlasmaLean.Design.DommaschkKamIdentCheck
  public import PlasmaLean.Design.DommaschkKamIdentCheckD
  public import PlasmaLean.Design.DommaschkKamIdentCheckR
  public import PlasmaLean.Design.DommaschkKamIdent
  ```
- `scripts/check_axioms.lean`:
  ```
  #print axioms PlasmaLean.Design.DommaschkKam.divFree
  #print axioms PlasmaLean.Design.DommaschkKam.flux_a
  #print axioms PlasmaLean.Design.DommaschkKam.flux_b'
  #print axioms PlasmaLean.Design.DommaschkKam.flux_c'
  #print axioms PlasmaLean.Design.DommaschkKam.torsion_poly
  #print axioms PlasmaLean.Design.DommaschkKam.no_flowFieldG
  #print axioms PlasmaLean.Design.DommaschkKam.Dp_ident
  #print axioms PlasmaLean.Design.DommaschkKam.nRp_ident
  #print axioms PlasmaLean.Design.DommaschkKam.nZp_ident
  #print axioms PlasmaLean.Design.DommaschkKam.flow_ident
  #print axioms PlasmaLean.Design.DommaschkKam.DkPoly.merge_fixture_ne
  ```
