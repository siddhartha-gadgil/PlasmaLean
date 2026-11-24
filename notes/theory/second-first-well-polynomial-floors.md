# Polynomial lower bounds for the second QA2R first-well action

At the phase-zero launch $u=239/500$, the one-way Cartesian action between the two physical first mirrors at the upper height is at least $1.3618404057884121$ to the digits shown. The exact lower bound exceeds the target $6799610938322487/5000000000000000$ by more than $0.0019182$. Lean proves this on the signed field line reached from every admitted birth angle on one pair of nested QA2R invariant tori. The proof integrates 37 degree-seven polynomial lower bounds on the two outer parts of the line and uses the original 110-pair physical quadrature in the center. [First-well and birth proofs](../../scripts/dommaschk_kam/verify_second_polynomial_first_well.py) · [Exact dyadic polynomials](../../scripts/dommaschk_kam/results/q0r478_action_polynomials.json)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-156 |
| Title | Polynomial lower bounds for the second QA2R first-well action |
| Kind | Method and physical certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-129, N-134, N-137, N-138, N-148 |
| Dependency requirement | Signed physical field models on the actual outer tubes, a centered squared-strength error on the grouped models, an independently checked central native action cover, and the first-mirror timing theorem. |
| Produces | A reusable integrand inequality, exact polynomial integrals on two signed clocks, and the above-target physical outer action between the actual upper-height first mirrors. |
| Status | Kernel-verified on the 328-row signed trajectory from the nested tori. |
| Lean evidence | `DommaschkQ0R478PolynomialFirstWellBirth328.from_entry`, `.from_nested_tori`, and `DommaschkQ0R478PolynomialFloor325.floor_on_enclosing_interval`. |
| Audit evidence | The local physical theorems, signed row and integral proofs and final birth theorem use propext, Classical.choice and Quot.sound. |
| Last updated | 25 November 2026 |

## A scalar inequality for action density

Write $h=h_U=5300546391395933/5000000000000000$, $B$ for physical field strength, and $w$ for Cartesian arclength per unit geometric angle. The field and arclength density are nonnegative. The toroidal denominator $D$ and reference radius power $P$ are strictly positive. The physical inputs give $U=D^2w^2$ and $G\le P(h^2-B^2)$. A polynomial $p$ in normalized angular time satisfies

$$
 p \le w\sqrt{2(h-B)}
 \qquad\text{if}\qquad
 2UG-p^2D^2\left(2hP-\frac{G}{2h}\right)\ge0,
$$

where the real square root is zero at negative arguments. Indeed, $G/(2h)\le P(h-B)$ follows from $(h-B)^2\ge0$. The factor multiplying $p^2D^2$ therefore bounds $P(h+B)$ from below. Dividing by the strictly positive $D^2P(h+B)$ proves the desired squared inequality, and nonnegativity of the physical integrand gives the stated lower bound. This criterion retains the dependence of the field and the proposed integrand on the same angle. [Lean proof](../../PlasmaLean/Certificates/PolynomialActionFloor.lean)

In a grouped model, $P$ is the sixteenth power of the reference radius. Existing field proofs supply $N=P B_{\rm ref}^2$ and a certified $e$ with $|B^2-B_{\rm ref}^2|\le e$. We take $G=P(h^2-e)-N$. Separate models on the physical tube enclose $R,D,N_R,N_Z$ and prove $U=(RD)^2+N_R^2+N_Z^2$. On a native row the stored upper-height numerator gives $G=R^{16}(h^2-B^2)$ directly. The lower bounds use the two actual physical signed rows in both cases. [Grouped field applications](../../scripts/dommaschk_kam/verify_grouped_action_polynomials.py) · [Native field applications](../../scripts/dommaschk_kam/verify_native_action_polynomials.py)

The stored polynomial coefficients are integers divided by $2^{80}$. Lean checks additions, multiplications, the final nonnegative remainder bound on $[-1,1]$, and a rational antiderivative. Fitting the coefficients can be requested separately with `--propose`. Replaying all 37 saved integer polynomials produced byte-identical accepted Lean sources. Increasing the last group's constant coefficient by $1/4$ was rejected by the exact margin check.

## Contributions on the two signed clocks

On a group of outward indices $[a,b)$, $s=(128t-a-b)/(b-a)$ for the increasing elapsed angle $t$. Both orientations integrate the same polynomial over $s\in[-1,1]$, using the actual physical field on their respective signed intervals. The contribution of a coefficient $c_j/2^{80}$ with even $j$ is $(b-a)c_j/[32(j+1)2^{80}]$ for the two intervals together. Odd powers cancel. On the group $[319,325)$, the resulting two-sided lower contribution is $2153258319243045786249449/676998458984192337835458560$. Its signed pointwise receipt is `4f7099a5a9a900c8befdad38a10136473ee6c72eae1729e20396b5d7f3f7a66e`. Its interval integration receipt is `fea5047a343aae121f5f481edcf2c8c6995056e559418bf568103210d8bb9bd0`. [Signed shell theorem](../../PlasmaLean/Certificates/ActionFloorShells.lean) · [Actual time intervals](../../scripts/dommaschk_kam/verify_action_polynomial_shells.py)

The native 110-pair center contributes $485523138005575/844424930131968$. Its original physical cover receipt is `324c8328aa5ac6faab40bd8a2832e5a182b0fc9780387e6d07425273b3d11187`. The grouped intervals are $[110,176)$ and $[192,325)$. Sixteen native-model polynomials cover $[176,192)$. Checking the 21 grouped polynomials in Lean took 185 seconds in total. The 16 smaller native polynomials took 65 seconds. Each local proof used less than 3.9 GiB peak resident memory.

The signed interior proof gives the exact lower bound $790254733800996141875465767/580284393415022003858964480$ on $[-325/64,325/64]$. Its receipt is `6fcc8e890bd019f22aea77b59cc4891d71a80d9f6c16c4fe5bebb76e5254079b`. The true first mirrors have elapsed angles in $(325/64,327/64)$ on both clocks. Nonnegativity of the physical integrand extends the bound to the whole well on that trajectory. The first-well theorem has receipt `82ba89a79857f54f2ee51fff4545c604b9fe9940e675e7d061966a0d042f03b6`. Binding it to the 328-row signed field line from the invariant tori gives `63d09b9eb282e91824ed50ae5b5d22fd968e2a1a404aaede06a5b60b30be72ab`. [Integral assembly](../../scripts/dommaschk_kam/verify_second_action_polynomial_floor.py) · [Binding to the original birth](../../scripts/dommaschk_kam/verify_second_polynomial_first_well.py)

## Reproduction

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
lake build PlasmaLean.Certificates.ActionFloorShells
.venv-ws/bin/python scripts/dommaschk_kam/verify_grouped_action_polynomials.py \
  --map /tmp/plasma-all325-compared-row-map.json --output /tmp/plasma-n156-groups.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_native_action_polynomials.py \
  --output /tmp/plasma-n156-native.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_secondary_action_cover.py \
  --band /tmp/plasma-q0r478-all-height-branches.json --pairs 110 --output /tmp/plasma-n156-native-center110.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_action_polynomial_shells.py \
  --band /tmp/plasma-q0r478-all-height-branches.json --models /tmp/plasma-n156-groups.json \
  /tmp/plasma-n156-native.json --output /tmp/plasma-n156-shells.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_second_action_polynomial_floor.py \
  --center /tmp/plasma-n156-native-center110.json --stop 325 --shells /tmp/plasma-n156-shells.json \
  --output /tmp/plasma-n156-floor325.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_second_polynomial_first_well.py \
  --floor /tmp/plasma-n156-floor325.json --band /tmp/plasma-q0r478-all-height-branches.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/328.json --output /tmp/plasma-n156-first-well.json
```
