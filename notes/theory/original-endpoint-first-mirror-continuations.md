# N-207 · First mirror branches from the original phase-zero birth at 0.523

| Field | Value |
| --- | --- |
| ID | N-207 |
| Kind | Physical certificate and computation |
| Addresses | Q-16, Q-22 and the trapped-orbit geometry for G-10 |
| Depends on | The Q-16 nested physical tori, N-120 signed birth, N-131 incoming exclusion, endpoint mirror caps and outward slopes, N-189 signed spatial certificates |
| Dependency requirement | The signed ODE trajectory and both first-mirror branches must use the same original packet and section state |
| Produces | A through-birth signed trace and two continuous first-mirror time functions over the closed height band |
| Difficulty | The length-337 signed chain needs 674 physical slabs together with two independent signed mirror histories |
| Status | Verified for the original phase-zero radius 523/1000 |
| Lean evidence | On demand, `DommaschkQ0R523MirrorBandBirth337.from_birth` and `.from_entry_passage` |
| Audit evidence | Lean kernel checked both declarations, using `propext`, `Classical.choice` and `Quot.sound` |
| Last updated | 25 November 2026 |

## Physical statement

There is one pair of nested invariant Q-16 tori for which the following holds for every geometric birth phase $|φ|≤2^{-19}$ radians. Starting at their original radial interpolation coordinate $u=523/1000$, the solution of the physical field-line ODE reaches the zero section after angular duration $|φ|$. At that section state there is a single physical field line $y$, verified for signed angles from $-337/64$ to $337/64$. For each height $h$ in the closed interval below, this same $y$ has a unique first outward mirror in each direction. Mirror times are positive elapsed angles **from the section state reached by the approach**. The forward clock samples $y(t)$ and the backward clock samples $y(-t)$.

| Height | Exact value | First mirror in each outward clock |
| --- | --- | --- |
| Lower | $5297961656084411/5000000000000000$ | $(322/64,324/64)$ |
| Upper | $5300546391395933/5000000000000000$ | $(335/64,336/64)$ |

On each signed line the first-mirror time is continuous and strictly increasing throughout the band. For interior heights, $0<τ'(h)<800h$. The early field-strength exclusion, squared-strength outward slope strictly greater than $1/400$ on the crossing region, and final above-height cap justify the branch for every intermediate height. These are magnetic field-line statements in model units. Computing action integrals on these wells requires the corresponding physical quadrature.

## Proof and replay

The checked trajectory uses SHA-256 `60aa38c42b74fac7631fb29ef1bcad5dcb629b413d89eaa464c984235ee10e68` for the original frame archive. The producer authenticates both launch theorems, the central and spatial row receipts, the signed prefix and the mirror branch before accepting the birth theorem. All package names below have the namespace prefix `PlasmaLean.Design`.

| Declaration or package | Accepted key |
| --- | --- |
| `DommaschkSignedPrefixQ0R523337.from_birth` | `ae88495f08648736594c4ff76aa1d4832ba268618fd7c2cf42e709b71f5efa20` |
| `DommaschkQ0R523MirrorBranch336.of_signed_chain` | `0b7c478eef52b5120c6bc263f530025e5dcb9b8ad4f89d2d1ddc5aba2f65e976` |
| `DommaschkQ0R523MirrorTimeSeparation`, four signed localization and derivative theorems | `7e84cef02d2995aa3a98d86c5d35d47d7af54b121961294dca12c054c702fdff` |
| `DommaschkQ0R523MirrorBandBirth337.from_entry_passage` and `.from_birth` | `55708e88b4d6a9c60e446d3b567e8e5f001c5f1a6518449d1f61d9506bfb4580` |

Using the common launch receipts and the original 0.523 caps, slopes and exclusion, run this command from the repository root.

```sh
.venv-ws/bin/python scripts/dommaschk_kam/verify_endpoint_mirror_closure.py \
  --endpoint q0r523 --plan /tmp/plasma-six-endpoint-interior-plan.json \
  --forward-launches /tmp/plasma-all-eight-physical-launches.json \
  --backward-launches .lake/endpoint-backward/all-eight-physical-backward-launches.json \
  --caps /tmp/plasma-next-caps523.json --slopes /tmp/plasma-next-slopes523.json \
  --exclusion /tmp/plasma-n131-q0r523-exclusion.json --workers 2 \
  --output /tmp/plasma-n207-q0r523-first-mirrors.json
```

The final birth key is in `physical_birth.key`. The top-level key identifies the mirror branch. The same driver accepts `q0r531` with its own cap, signed slopes and exclusion. The ordinary six-endpoint supervisor offers `--cap-priority --wait-manager`. It allocates workers according to distinct outstanding proof groups and releases excess slots when only the serial terminal join remains. Workers use a common lock for long prefix joins and per-package locks for compiled results. Existing per-label signed proofs are reused. The 0.523 run processed the last 20 row pairs and joined the birth to both mirrors in 3 minutes 27 seconds wall time, with 5 minutes 23 seconds of charged CPU time and two workers. This measurement starts from the pre-existing central and spatial certificates.
