# Cartesian action exceeds 0.2765 between the first upper mirrors of a pilot birth

For every admitted QA2R birth on the phase-zero sector at launch parameter $u=47/100$, Lean constructs a single signed physical field line whose action at the upper height exceeds **553/2000** between its first negative and first positive upper mirrors. The action is dimensionless and counts the journey between those mirrors once. The proof obtains all of this lower bound on the central interval of length $79/8$ radians. [Physical well action](../../PlasmaLean/Design/DommaschkFirstMirrorActionFloor.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-96 |
| Title | Cartesian action between the first upper mirrors of a pilot birth |
| Kind | Proof and certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-86, N-93, N-95 |
| Dependency requirement | The identified QA2R field, both signed tube chains for the same Q-16 birth, the lower-height signs on both 316-row prefixes, the first upper mirror contacts on both branches, and Euclidean cylindrical arclength. |
| Produces | A strict dimensionless lower bound of 553/2000 on the true complete upper-height well action for the phase-zero pilot. The physical arclength density is continuous and bounded below on every pilot tube. |
| Difficulty | The slope of the cylindrical coordinate curve must represent the true Cartesian density. The closed signed path provides one-sided endpoint derivatives. |
| Status | Verified |
| Lean evidence | `DommaschkFirstUpperActionFrom316Of325.from_birth` and `DommaschkSignedActionFloor316Of325.on_path` in the on-demand replay. The reusable supporting modules are linked below. |
| Audit evidence | Sixteen supporting declarations and the generated applications report only `propext`, `Classical.choice` and `Quot.sound`. The final two content keys appear under Reproduce. |
| Last updated | 25 November 2026 |

## Physical statement

The Q-16 nested tori, birth curves and section approach are those in the compiled signed birth theorem. For each initial phase $|\phi|\le 2^{-19}$, take its actual approach to section zero and its resulting field line $y(t)=(R(t),z(t))$, where $t$ is signed geometric toroidal angle. Let $b(t)=\lVert B(R(t),t,z(t))\rVert$. The two mirror heights at this launch are

$$
 h_L=\frac{5297961656084411}{5000000000000000},\qquad
 h_U=\frac{5300546391395933}{5000000000000000}.
$$

There are elapsed angles $c_-,c_+\in(324/64,325/64)$ with $b(-c_-)=b(c_+)=h_U$. From zero up to each contact its respective branch has strength strictly below $h_U$. The same trajectory has its two first lower-height contacts at elapsed angles in $(316/64,317/64)$. Set $X(t)=(R(t)\cos t,R(t)\sin t,z(t))$. The integrand is Lebesgue integrable, and the true action satisfies

$$
 J_U=\int_{-c_-}^{c_+}\lVert X'(t)\rVert\sqrt{2(h_U-b(t))}\,dt
 > \frac{553}{2000}=0.2765 .
$$

The endpoints are the first mirrors on each side of this actual launch. This theorem supplies one lower bound at one endpoint and one height. The N-60 radial root comparison needs tighter action enclosures across the other endpoints and heights. Physical time and thermal operating targets remain open. [Physical birth and first-contact definitions](../../PlasmaLean/Design/DommaschkSignedObservable.lean) · [Field-line action definition](../../PlasmaLean/Theory/Kinetic/CylindricalActionSensitivity.lean)

## Geometry and integrability

Each of the 391 forward and 391 backward archived slabs satisfies $7/8\le R\le1$ and $|z|\le5/64$, for every physical point in its closed outgoing tube and every time on the slab. The checker adds the $2^{-80}$-scaled physical output radius to the exact coefficient-sum range of each traced coordinate polynomial after subtracting $15/16$ or zero. The enclosure follows from $1/16$ and $5/64$ bounds on those two enlarged ranges. [Both full archive checks](../../PlasmaLean/Design/DommaschkSignedTraceDomain.lean)

On this rectangle the true polynomial $D=R^7 B_\phi$ satisfies $D>1/64$ for every physical angle. The proof divides $R-29/32\in[-2/64,6/64]$ into four equal intervals and $z\in[-5/64,5/64]$ into two. Each of the eight exact fixed-point interval certificates permits the full ranges of cosine and sine. Positive $D$ implies positive toroidal field and jointly continuous angular field-line velocity throughout the region. [All-angle denominator](../../PlasmaLean/Design/DommaschkSignedTraceDenominator.lean) · [Physical density continuity](../../PlasmaLean/Design/DommaschkSignedTraceDensity.lean)

At interior times the signed ODE gives both coordinate derivatives. The true Cartesian density is $\sqrt{R^2+(R')^2+(z')^2}\ge R\ge7/8$. The same density, evaluated using the physical velocity components, extends continuously to the closed interval. Strength is also continuous there. Changing the integrand at the two endpoints preserves integrability and the interval integral. This proves integrability independently of the numerical action columns. [Cartesian derivative and integral](../../PlasmaLean/Design/DommaschkSignedActionFloor.lean)

Throughout $[-316/64,316/64]$ the certified field strength is below $h_L$. Exact arithmetic gives $4/125<\sqrt{2(h_U-h_L)}$. Multiplying these two positive lower bounds gives a strict contribution greater than $7/250$ per radian over that core. The integrand is nonnegative on the full interval between the first upper mirrors. Inclusion of the core therefore yields the stated complete-well inequality. [Core-to-contact comparison](../../PlasmaLean/Design/DommaschkFirstMirrorActionFloor.lean)

| Closed signed core | Compiled strict lower bound on $J_U$ over this core |
| --- | --- |
| $[-5/2,5/2]$ | $7/50 = 0.14$ |
| $[-4,4]$ | $28/125 = 0.224$ |
| $[-9/2,9/2]$ | $63/250 = 0.252$ |
| $[-316/64,316/64]$ | $553/2000 = 0.2765$ |

## Reproduce

From the repository root, build the Lean modules and check that the exact polynomial generator reproduces the tracked source. The second and third Python commands consume the N-95 manifests for the pilot's paired 325-slab birth, its 316-row strict lower-height signs on that birth, and its first-contact theorem at both heights. The filenames below are the workstation outputs from that phase. On a fresh checkout, produce those three inputs by the N-95 replay, then pass their locations to the same commands. The producers validate the compiled upstream modules and their artifact SHA-256 hashes and perform a new axiom audit of the result. [Core proof producer](../../scripts/dommaschk_kam/verify_signed_action_floor.py) · [Complete well proof producer](../../scripts/dommaschk_kam/verify_first_mirror_action_floor.py)

```sh
LEAN_NUM_THREADS=1 lake build PlasmaLean.Design.DommaschkFirstMirrorActionFloor
.venv-ws/bin/python scripts/dommaschk_kam/emit_signed_trace_denominator.py --check
.venv-ws/bin/python scripts/dommaschk_kam/verify_signed_action_floor.py \
  --paired /tmp/plasma-signed-checkpoint-325.json \
  --submirror /tmp/plasma-birth-lower-first-prefix-325.json \
  --output /tmp/plasma-signed-action-floor-316of325.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_first_mirror_action_floor.py \
  --core /tmp/plasma-signed-action-floor-316of325.json \
  --contacts /tmp/plasma-first-contacts-325.json \
  --output /tmp/plasma-first-upper-action-floor-325.json
```

The signed trace archive has SHA-256 `203174bc83dc40b46bca175b2ac03a39e9631c1d9cf6f35209df9660ae213a3d`. The 316-row core replay key is `5907e8d0c5ba9649c946ce38bf014c9203315b375f2234dc062f7de97bb8e68f`. The first-contact theorem key is `639e3b9131390174891ca98d4d12759aac8475416b83f99b68cc35f7f807c59b`. The combined well-action theorem key is `10abdb8d0a36a11f45d3dad63f7ae1fec908853fa12d79ce45323facb0a50f55`.
