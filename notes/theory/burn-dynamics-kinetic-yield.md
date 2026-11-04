# Burn dynamics and kinetic yield for C5: thermal stability, fuel depletion, alpha deposition

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-38` |
| Title | Burn dynamics and kinetic yield bridges for C5 (method note for N-5 and N-6) |
| Kind | method (research approach; lean-ready parts) |
| Addresses | `G-2` (C5), `Q-26` (new); supports `Q-13`, `Q-15`, `G-8` |
| Depends on | N-5 (burn window, obstructions), N-6 (one-plasma coupling), N-36 (claims 10, 17, 21, 40, 41); Lean: `Kernel/Fusion` (`DTPlasma.alphaPower`, `netHeating`, `PowerBalance`, `BoschHaleDT`), `Design/BurnWindowStellarator`, `Theory/Transport/Comparison` |
| Dependency requirement | compiled: the `PowerBalance` trajectory interface and `netHeating`; none of the new items needs a new kernel law |
| Produces | Q-26 (a)–(d) statements, with Lean targets |
| Difficulty | routine (a)–(c); moderate (d, kernel change) |
| Status | stated; (a)–(c) lean-ready |
| Lean evidence | none yet |
| Audit evidence | AK-1, AK-2 (N-36) motivate (c) and (d) |
| Last updated | 4 November 2026: created from N-36 |
| Patched by / Alternatives | method for N-5, N-6 (their compiled results stand) |

## Purpose and scope

N-5 and N-6 certify burn windows and one-plasma bands with:
- **fixed densities;**
- **Maxwellian fuel** (thermal reactivity ⟨σv⟩ through `BoschHaleDT`);
- **full, prompt alpha deposition:** `alphaPower = (E_α/4)(f_fuel n)²⟨σv⟩V`, E_α = 3.5 MeV.

The kinetic/coil brief (N-36) points out three gaps between such results and a maintained burn:
- a heating balance at one temperature can be thermally unstable;
- all-time burn needs refuelling and ash removal;
- alpha energy is deposited through slowing down, not locally at birth.

It also points out a fourth: a temperature bound gives a reaction rate only for Maxwellians. This
note gives the method for closing each gap with elementary Lean theorems. It leaves the compiled
N-5 and N-6 results unchanged; they stay correct under their stated assumptions.

Model: the 0-D `Kernel/Fusion` power balance C dT/dt = G(T) with
G(T) = P_α(T) + P_aux(T) − P_br(T) − P_loss(T), and its 1-D radial analogue (`Theory/Transport`).
SI units with T in keV as in `Kernel/Fusion`.

## Theory development

**(a) Thermal stability of a burn point** (N-36, claim 40; brief §8.6).
- If G(T*) = 0 and G′(T*) > 0, then T* is unstable: every solution with T(0) ≠ T* close to T*
  leaves a neighbourhood of T*.
- If G′(T*) < 0, then T* is locally asymptotically stable.
- A practical certificate form avoids derivatives: on an interval [T*−δ, T*+δ], G ≥ 0 below T* and
  G ≤ 0 above it. That makes the interval forward-invariant for `PowerBalance` trajectories. It is
  the 0-D analogue of the existing barrier theorems.
- The existing window results give G > 0 or G < 0 on bands. Adding the sign change at a certified
  T* gives a *stable operating band*, and the opposite sign pattern gives a certified thermal
  runaway or collapse threshold.

Lean target: `stable_band_of_sign_change`. If `PowerBalance` holds, G(T) ≥ 0 on [T₁, T*] and G ≤ 0
on [T*, T₂], and T(0) ∈ [T₁, T₂], then T(t) ∈ [T₁, T₂] for all t ≥ 0. The proof is the same
comparison pattern as `riccati_le_initial`, using `image_le_of_deriv_right_le_deriv_boundary`.
The negative fixture is `unstable_of_deriv_pos`.

**(b) Finite fuel obstruction** (claim 41).
- In a closed particle balance with dN_D/dt = −R(t) ≤ 0, N_D ≥ 0 and no source, ∫₀^t R ≤ N_D(0) for
  all t.
- Hence there is no r > 0 with R(t) ≥ r for all t ≥ 0. The same holds for N_T.
- Lean target: `no_sustained_burn_without_fuelling`. Hypotheses: a nonnegative N with right
  derivative −R, and R ≥ r > 0 on [0, ∞). The conclusion is False.

This is the obstruction an "all-time burn" claim must respect. The fixed-density models avoid it
only by assuming refuelling (AK-2). G-2's "(or forever)" therefore requires a fuelling and ash model
(a source S_D, S_T ≥ R and ash removal), named in its scope.

**(c) Kinetic yield perturbation bound** (claim 21; brief (5.14)).
- For reaction kernels k(v, w) = g σ(g) ≤ K_max:

  |R(f_D, f_T) − R(F_D, F_T)| ≤ K_max (‖f_D − F_D‖₁ ‖f_T‖₁ + ‖F_D‖₁ ‖f_T − F_T‖₁).

- On a truncated velocity domain, add certified tail terms.
- This is the bridge from a Maxwellian reactivity (`BoschHaleDT`) to a non-Maxwellian state within
  a stated L¹_v distance. It replaces "T in the window ⇒ reaction rate" by "state within distance d
  of a Maxwellian with T in the window ⇒ reaction rate ≥ R_Maxw − K_max(…)d".
- Lean target: `reactionRate_sub_le`, for integrable functions on a measure space with a bounded
  measurable kernel. This is Bochner-integral algebra (`MeasureTheory.integral_mul_le`, Fubini). It
  can be stated abstractly in a new module `Theory/Kinetic/ReactionRate.lean`.

**(d) Alpha deposition fraction** (claim 10; AK-1).
- Replace the implicit deposition fraction 1 by an explicit f_dep ∈ [0, 1] in G-2 claims:
  P_α,dep = f_dep · P_α.
- Two options:
  - add the field to `DTPlasma` (a kernel change, needs the strict audit);
  - keep the kernel and state each design theorem for `f_dep · alphaPower` with f_dep a hypothesis.
    This is the cheaper option.
- The compiled windows are monotone in P_α, so the existing results become the f_dep = 1 case. The
  margin at f_dep < 1 is a computation per window.
- The certified alpha-confinement results (N-14, N-15) bound prompt losses only for passing alphas.
  They do not yet supply f_dep.

## Claims and evidence

- (a), (b), (c): complete mathematical proofs (elementary); not yet in Lean.
- (d): a modelling decision; the existing results are correct for f_dep = 1, which is stated by
  AK-1 as an assumption, not a defect in a proof.

## Difficulty, barriers and readiness

(a)–(c) are lean-ready and small (one module each, a few hundred lines, light builds). (d) needs a
choice between a kernel field and a hypothesis per theorem; the hypothesis form is recommended
first. Smallest next step: `no_sustained_burn_without_fuelling` and `stable_band_of_sign_change`
in `Theory/Transport/BurnDynamics.lean` (new, default build).

## Outputs and next dependencies

Q-26. Ready after (a): a stable-band certificate for the Stellaris window (N-5). After (c): a
kinetic yield statement for G-2 once a state-distance bound exists (Q-27, Q-28).
