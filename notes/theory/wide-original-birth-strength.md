# The original QA2R births lie below both mirror heights on two wide sectors

On one pair of nested embedded invariant tori of the actual QA2R field, every original birth at interpolation radius \(u\in[0.44,0.54]\) has strength strictly below the lower mirror height whenever
\[
 |\phi|\le 1/32 \qquad\text{or}\qquad |\phi-\pi/2|\le 1/32 .
\]
The field is evaluated at the Cartesian point obtained from both torus profiles at the original launch angle and the fixed poloidal cut. These sectors have combined length \(1/8\) geometric radian, about 3.98% of the field-strength period \(\pi\). The exact upper height exceeds the lower height, so the same births are accessible at both. [Original birth statement and coordinate bounds](../../PlasmaLean/Design/DommaschkWideBirthBounds.lean)

## Coordinate and field proof

The certified Fourier moments on the two symmetry cuts bound the radius for all interpolating labels. The true torus profiles differ from their packed seeds by at most \(10^{-12}\) per coordinate. A seed derivative bound of \(1/6\) per radian controls the coordinate change away from the cut. Over each entire sector, the radius therefore lies in its original section range expanded by \(1/192+10^{-11}\) at both ends. The absolute vertical coordinate is at most \(1/192+10^{-11}\). These boxes include every radius from the wider common action bracket considered in N-190. [Fourier moments and launch displacement](../../PlasmaLean/Design/DommaschkMirrorLaunch.lean)

Write \(t\) for displacement from the symmetry phase. The double-angle sine varies by at most \(2|t|\le1/16\). The cosine differs from its central value \(+1\) or \(-1\) by at most \(2\sin^2t\le 1/512\). This quadratic cosine error permits one field certificate for a whole sector. The proof uses the physical radius as a common Taylor variable when evaluating the three exact QA2R field polynomials. The outward arithmetic bounds the sign of
\[
 (R D-hR^8)(R D+hR^8)+n_R^2+n_Z^2
   = R^{16}\bigl(\lVert B\rVert^2-h^2\bigr)
\]
at the original lower height \(h=5297961656084411/5000000000000000\). The checked radius is positive on both boxes. [Physical sparse-field replay](../../scripts/dommaschk_kam/verify_wide_birth_strength.py)

N-56's directed external checker still covers the entire original launch circle. Replaying all 32,768 cells gave the exact strength upper numerator 4719138642989737 over \(2^{52}\), below 1.048. The two new sectors have direct physical Lean proofs. Each result concerns the field evaluated at birth. The long ODE, its first selected mirror pair, and the action from one mirror to the other have their own obligations. In particular the opposite-sector wrong action sign on the entire narrow strip coexists with these low-field births. [Full-period external enclosure](dommaschk-launch-collar.md) · [Opposite-section action obstruction](opposite-section-excludes-pilot-action-strip.md)

## Replay

The accepted common-torus declaration is `DommaschkWideBirthFamily.original_births`, key `7777d8332b94d8ba4a82feda551f00dcddf4c9be421648630b0fdb1a8fc03032`. An independent invocation reproduced the receipt byte-for-byte. The two original branch proofs and the common-torus conclusion use only `propext`, `Classical.choice` and `Quot.sound`.

~~~sh
lake build PlasmaLean.Design.DommaschkWideBirthBounds PlasmaLean.Design.DommaschkGroupedMirrorModels \
  PlasmaLean.Design.DommaschkStoredPowers
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 .venv-ws/bin/python \
  scripts/dommaschk_kam/verify_wide_birth_strength.py --output /tmp/wide-birth-strength.json
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-196 |
| Kind | Candidate field certificate on continuous launch sectors |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-56, N-61, N-79, N-190 |
| Dependency requirement | The two Q-16 profile closeness bounds, their Fourier slice derivative bounds, and the original three field polynomials. |
| Produces | A width-\(1/16\) launch interval at each symmetry section for every deep-strip birth on common embedded tori. |
| Status | Coordinate bounds, physical polynomials and common-torus application replayed in Lean. |
| Lean evidence | `DommaschkWideBirthBounds.angle_bounds`, `.birth_in_box`, `.from_sectors` and generated `DommaschkWideBirthFamily.original_births`. |
| Audit evidence | The candidate certificate audits both branches and the common-torus conclusion. |
| Last updated | 25 November 2026 |
