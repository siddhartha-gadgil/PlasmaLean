# A 3.5-radian field comparison on two physical birth trajectories

At every launch angle satisfying $|φ_0|≤2^{-19}$, the phase-zero births at radial labels $0.470$ and $0.478$ have two true field lines on which, at every common azimuth $-7/2≤φ≤7/2$,

$$
 |B_o(φ)| ≤ |B_i(φ)| - 1/18000, \qquad
 ds_o/dφ ≥ (3999/4000)\,ds_i/dφ .
$$

Here the arclength densities use increasing azimuth and stay positive. The tori defining the original birth interpolation are the same for every launch and both labels. One existential witness supplies both lines before the observation angle is chosen. The full archive contains this comparison through $325/64$ radians in each direction on the original tubes. The physical interval above uses the 224 consecutive signed steps at the outer birth. [Full tube comparison](full-paired-physical-profiles.md) · [Proof on both signed trajectories](../../scripts/dommaschk_kam/verify_compared_trace_prefix.py)

## Eight original births on one embedded torus pair

Each entry counts consecutive original angular steps of width $1/64$ radian in **each** direction. Together the entries give 1,482 signed physical steps. The same pair of embedded tori also carries the pilot’s upper action and flight-time calibration. [Common-family construction](../../scripts/dommaschk_kam/verify_common_endpoint_traces.py) · [Pilot observables](../../scripts/dommaschk_kam/verify_common_pilot_observables.py)

| Birth section | Radial labels, in order | Steps each way |
| --- | --- | --- |
| $0$ | 0.470, 0.478, 0.523, 0.531 | 391, 224, 48, 12 |
| $π/2$ | 0.456, 0.464, 0.509, 0.517 | 48, 8, 5, 5 |

At $u=0.523$, the signed physical tubes of all 322 incoming pairs satisfy $|B|<h_L-1/100000$. At $u=0.531$, the analogous bound on all 323 incoming pairs is $|B|<h_L-1/50000$. Projecting the two estimates onto true paths through the original births gives these strict field margins on $|φ|≤48/64$ and $|φ|≤12/64$, respectively. The longer 322- and 323-pair statements apply to any path meeting the archived bounds. [Projection onto a true physical birth](../../scripts/dommaschk_kam/verify_submirror_prefix_projection.py)

## A physical lower action on 65 signed slab pairs

At the second phase-zero birth $u=239/500$, the actual QA2R trajectory on $[-96/64,96/64]$ satisfies a lower bound for its upper-height action between $-65/64$ and $65/64$. With physical Cartesian arclength density $w$ and field strength $f$ on this trajectory, Lean proves

$$
\frac{50225245810819}{140737488355328}
\le \int_{-65/64}^{65/64} w(t)\sqrt{\max(0,2(h_U-f(t)))}\,dt .
$$

The 6,240 chronological cells refer to this same line. The central 64 pairs reuse the previously checked physical 48-panel-per-slab cover. Lean checked the density and squared-speed digit comparisons for the entire center in 21.6 seconds. The two outer blocks use the actual signed row-64 tubes. The radius, section, height and chronological indices agree at both joins. This result concerns the indicated interior interval. The two first mirrors at this height occur later on the outward clocks.

The grounded declaration is `DommaschkQ0R478CoarseBirthCover065Of096.from_nested_tori`, key `05267b51e97115d2ff437a4ce81d548bb2d4719b7b4c3c8ced5c2954764d048e`; the underlying cover is `e9317bd76809f9e7c17744e7b9f13f3cfc38c2dbdf9753ce10373f4dc1906fb5`. Both use only the three standard axioms.

The block lemma concatenates lists in their original order and transfers pointwise lower action bounds under checked weakening of the stored density and speed digits. A single transfer handles both central signed lists and the two outer blocks add just one slab on each side. A project release can regenerate these computations from the committed witness packets. [Block lemmas](../../PlasmaLean/Certificates/WeakenLowerActionCover.lean) · [Center transfer](../../scripts/dommaschk_kam/verify_coarse_native_center.py) · [Signed cover composition](../../scripts/dommaschk_kam/verify_coarse_secondary_cover.py)

Independently, the physical action over the complete $[-7/2,7/2]$ interval exceeds $87/250$ at every height $h≥h_U-267/2^{27}$. Its exact lower bound is $367617635095984613/1055531162664960000$. This uses the incoming-height estimate, which applies across that interval of heights and before either first mirror. The proof key is `e8f2e817b9b65443ea723827333ce640f86c48433aacd169d5f8fc13122c24fa`. [Uniform-height action bounds](secondary-near-upper-first-wells.md)

## Evidence

| Claim | Physical proof key |
| --- | --- |
| Common signed family | `dfc34708f5ccc4ef89a5e59aec8907134d1fa383a370e2f02c9ff50adec9fc3c` |
| Same tori and calibrated pilot | `4441e10e7f4e9fa2f4a4b56bc7445a4e0645e423277003d1edaeed1352baca6e` |
| Two actual signed profiles through ±3.5 radians | `42bff600b7a3c4a7bb65d5e5b3656ab3fe57a9315c38950b2cfd10927dfa7d3a` |
| Actual opposite-section observations | `5a30569419ddc33b2940b64abb999289bca137b001a4f23653b6cc6aad568cfb` |
| Ordered sign on 322 pairs at 0.523 | `0e5878d6038e10a22a478a45f03a36b08e66e097a93ac546554d7925cfca6021` |
| Quantified margin on 322 pairs at 0.523 | `b1218efa39d5837caa6fda7c14790019ffb308f50b87e96339b25433ad261c84` |
| Physical margin through 48 pairs at 0.523 | `2b94e1097f0c74c8142dbb054b33ff59ce57115bbf6735d79f4fcd48b4c75c9d` |
| Ordered sign on 323 pairs at 0.531 | `210c78b36fc7f1d8eabe1ff29b20ca903c86d2d3458a2b12116e206193cb4c09` |
| Quantified margin on 323 pairs at 0.531 | `dae817183e57226d55e1118fbae7814a865e73441d2a84347fe464476594daca` |
| Physical margin through 12 pairs at 0.531 | `edd9984136649a2b0bcf8ec828aab6d97d40a6bab79303ce3912e7fcfe452c71` |

The 3.5-radian theorem is `DommaschkComparedBirths224On391_224_48_12_48_8_5_5.from_common_tori`. Its 224 rows are the initial segment of the ordered N-146 input manifest. The on-demand Lean checks report only `propext`, `Classical.choice` and `Quot.sound`. The original 325-pair comparison and the 328-pair outer trajectory are the inputs for a first-well secant through both mirrors. [First-well comparison](paired-first-well-actions.md)

For example, the complete ordered map can reproduce the physical comparison at any covered prefix, including a prefix ending inside a grouped estimate.

~~~bash
.venv-ws/bin/python scripts/dommaschk_kam/verify_compared_trace_prefix.py \
  --calibrated /tmp/plasma-calibrated-at-224.json \
  --launch-profile /tmp/plasma-paired-action-profile000.json \
  --row-map /tmp/plasma-all325-compared-row-map.json --length 224 \
  --output /tmp/plasma-compared224-replay.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-149 |
| Kind | Signed physical trajectory and integral certificates |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-130, N-131, N-135, N-138, N-145, N-146, N-148 |
| Dependency requirement | Archived signed ODE enclosures, matched field and arclength tubes, and a shared embedded torus pair |
| Produces | A pointwise 3.5-radian comparison on two physical trajectories, a 65-pair physical action lower bound and two further physical submirror margins |
| Status | Kernel verified, including on-demand applications to the actual launches |
| Lean evidence | `from_common_tori` above, `DommaschkQ0R478CoarseBirthCover065Of096.from_nested_tori` and the two signed `from_birth` projections |
| Last updated | 25 November 2026 |
