# An equal-height action gap throughout the closed mirror-height band

At phase zero, the radial endpoints $u_i=47/100$ and $u_o=239/500$ satisfy a uniform action separation throughout the closed interval $[h_L,h_U]$ of mirror heights. The two field lines issue from the original interpolated positions on the same pair of nested embedded QA2R tori. For every admitted $|\phi_0|\le2^{-19}$ they can be chosen before the height. Writing $J_i,J_o$ for one-way action integrated against Cartesian arclength between the first two enclosing mirrors, the conclusions are

$$
 J_o(h)-J_i(h)>2/625,\qquad
 \frac{J_o(h)-J_i(h)}{239/500-47/100}>2/5
 \quad (h_L\le h\le h_U).
$$

The inner first well is contained in the outer first well at the same height. The old shifted-height gain and the sharper upper-end secant above $1/2$ apply to the same pair of curves. The new estimate also applies in the interval $h_U-1/18000<h<h_U$. [Paired profiles](paired-first-well-actions.md) · [Upper-end secant](upper-height-radial-action-secant.md)

## An integrated lower bound from the field drop

On the inner first well the certified pointwise bounds are $B_o\le B_i-1/18000$ and $w_o\ge k w_i$, where $w$ denotes Cartesian arclength per unit toroidal angle and $k=3999/4000$. Thus the outer field remains below the selected height throughout the inner well. The component containing the birth contains this whole interval. On its interior write $v_i=\sqrt{2(h-B_i)}$ and $v_o=\sqrt{2(h-B_o)}$. Then $v_o^2\ge v_i^2+d$, with $d=1/9000$.

For any $a,b$ with $b^2\le d(1-a^2)$, one has $a v_i+b\le v_o$. The proof expands $(bv_i-ad)^2$ and uses the nonnegative remainder $(d-da^2-b^2)(v_i^2+d)$. Integrating on the inner well and then including it in the outer well gives

$$J_o\ge k(aJ_i+b\ell_i),$$

where $\ell_i$ is the inner well’s physical arclength. The proof requires only a pointwise field drop, a relative arclength bound and integrability on the closed wells. [Affine comparison theorem](../../PlasmaLean/Theory/Kinetic/MirrorActionAffineGain.lean)

## Certified arclength and constants

Every inner first well contains $[-316/64,316/64]$. On that interval the physical tangent obeys $w_i\ge R_i$. On each of the 316 paired positive and negative angle slabs, Lean bounds $R_i$ from below by subtracting the radius error and the absolute polynomial deviation from unit radius. It takes the smaller of the two signed bounds and integrates that constant on both intervals. Their exact sum is

$$
 \frac{180067881457796589806937503}{19342813113834066795298816}
 \simeq 9.309291280336636.
$$

In particular $\ell_i\ge9309/1000$. The calculation uses the original two signed radial coefficient lists and their outgoing tube errors. [Signed arclength proof](../../PlasmaLean/Design/DommaschkPilotArcLength.lean) · [Exact row sum](../../PlasmaLean/Design/DommaschkPilotArcLengthPacket.lean)

Choosing $a=99739881/10^8$ and $b=759795/10^9$ satisfies the supporting inequality. Since $ka<1$, the existing upper bound $J_i\le1146552112157123/844424930131968$ gives the worst case. The resulting gain before rounding down is $135138718097889868751123537/42221246506598400000000000000$, about $0.00320073$. The radial spacing is $1/125$. This is a finite radial secant at fixed height. An action level on an intermediate field line would require control of the whole radial interval. [Physical action on the closed band](../../PlasmaLean/Design/DommaschkClosedBandAction.lean)

## Reproduction

```bash
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
lake build PlasmaLean.Design.DommaschkClosedBandAction PlasmaLean.Design.DommaschkPilotArcLengthPacket
.venv-ws/bin/python scripts/dommaschk_kam/verify_closed_band_secant.py \
  --top /tmp/plasma-n162-upper-secants.json --family /tmp/plasma-n147-regular-arcs-328.json \
  --output /tmp/plasma-n165-closed-band.json
```

## Metadata

| Field | Value |
| --- | --- |
| ID | N-165 |
| Kind | Reusable action comparison and physical secant |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-116, N-144, N-146, N-147, N-156, N-161, N-162 |
| Dependency requirement | The 325 paired field and arclength comparisons, 316 central signed radius pairs, a uniform pilot action cap, and both signed first-well branches. |
| Produces | Equal-height action gap and radial secant uniformly on the complete closed mirror-height band, on the same original births as the upper-height result. |
| Status | Kernel-verified on the two actual field lines for every admitted birth angle. |
| Lean evidence | `DommaschkPilotArcLength.exact_sum`, `DommaschkClosedBandAction.on_paths`, and `DommaschkClosedBandSecant391_328_48_16_48_16_8_5.from_common_tori`. |
| Audit evidence | Both generated declarations use only propext, Classical.choice and Quot.sound. The proof key is `816f6b17095691e29d0540927705620b5c4fd464954b1e37578ae203d1741568`. |
| Last updated | 25 November 2026 |
