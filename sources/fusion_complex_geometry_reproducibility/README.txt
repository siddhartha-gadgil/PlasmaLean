FUSION: COMPLEX VACUUM GEOMETRY AND STABILITY ESTIMATES
Research continuation, 18 November 2026

This bundle accompanies fusion_complex_geometry_and_stability.pdf.
It contains full mathematical source text and reproducible exact checks.
It does not certify a complete hot, stable stellarator.

CONTENTS

continuation_main.tex and four included continuation_*.tex files:
  Complete proof-note source. In a normal LaTeX installation with amsmath,
  amssymb and hyperref, compile continuation_main.tex twice with pdflatex.
  The delivered PDF was rendered from these sources using a separate local
  conversion workflow; that workflow is not required to read or compile them.

candidate.json:
  Original rational Dommaschk candidate at the pinned project commit.
  Its optimisation metadata is labelled untrusted in the original data.

DommaschkQA2RData.lean:
  Pinned formal-project Cartesian field data, retained with its source header.

dommaschk_complex_laurent.json:
  Exact converted potential. Each record contributes
    (real + i*imag) u^(u exponent) v^(v exponent) z^(z exponent).
  The rational coefficients are strings, with 121 nonzero collected terms.
  The field one-form is
    B^flat = (du/u - dv/v)/(2i) + dF.
  Physical space is u=x+iy, v=x-iy, z real. The holomorphic bilinear metric
  is du dv + dz^2. This is distinct from a positive Hermitian metric.

complex_vacuum_exact_check.py:
  Checks Git blob identities, equality of the candidate and pinned Lean
  potential, harmonicity, reality, field-period symmetry, stellarator parity,
  and finite exact examples of the general null-polynomial/Laurent identities.
  It rewrites dommaschk_complex_laurent.json deterministically.
  Requires Python 3 and SymPy. Run from any directory:
    python3 complex_vacuum_exact_check.py
  Keep the candidate and Lean data beside the script.
  The arbitrary-degree basis theorems are proved in the note; checking finitely
  many examples is not presented as their proof.

verify_hot_core_constants.py:
  Standard-library-only rational certificates for the Maxwellian mass,
  centered scalar temperature and directional temperature lower bounds.
  It uses alternating-series enclosures, Machin's pi identity and integer
  square roots. Assertions use exact rationals; floats are display only.
  Run:
    python3 verify_hot_core_constants.py

lean_dependency_audit.json, source_commit.json, source_tree.json:
  Pinned provenance and identities of all 227 project modules transitively
  imported by PlasmaLean.Design.DommaschkKamNested.

audit_lean_dependencies.py:
  Re-fetches that project import closure and verifies Git blob identities.
  Requires network access to raw.githubusercontent.com and about 73 MB of
  output space. Run:
    python3 audit_lean_dependencies.py
  This is a source retrieval/identity audit, NOT a Lean build or theorem proof.
  The full downloaded closure is intentionally omitted from this small bundle.

MANIFEST.sha256:
  SHA-256 hashes of the other bundle files at creation time.

PROVENANCE

Project: https://github.com/siddhartha-gadgil/PlasmaLean
Commit: 6312f1cc9c30b32798ad7b7540766152ef03e76f
Commit timestamp: 17 November 2026, 13:14:46 UTC
Lean toolchain stated by project: v4.34.1
Mathlib commit stated by project:
  d13f23b723b8a846827a245b89c10fc7d3f11612

Original candidate path:
  scripts/dommaschk_qa/results/20261031T092522Z/candidate.json
Candidate Git blob SHA-1:
  1e70104e57660e4605439f12d6e06a9fea76d48a
Original Lean data path:
  PlasmaLean/Design/DommaschkQA2RData.lean
Lean data Git blob SHA-1:
  dbca1daa8ddbf4e1405c55395f4842ece396f2c8

The included original project data/code retain their upstream attribution.
DommaschkQA2RData.lean states Copyright (c) 2026 PlasmaLean contributors,
released under Apache 2.0. A copy of that license is included as
THIRD_PARTY_APACHE_2_0.txt. Consult the pinned upstream repository for the
full project's licensing and provenance.

PROOF STATUS AND SCOPE

1. The exact algebra computations and rational numerical certificates passed.
   They are separate from the mathematical proofs written in the note.
2. The seed-torus results are inputs taken from the pinned project source.
   All 227 project source modules were retrieved and blob-checked, and the
   proof-source audit found no project proof holes. Lean was NOT rebuilt here;
   no fresh kernel axiom printout was obtained, and external dependencies were
   not independently audited.
3. The vacuum-family KAM radius is existential; no positive numerical radius
   in coefficient space is certified by this bundle.
4. The complete ideal-MHD stability theorem concerns a periodic cylinder,
   fixed independent magnetic fluxes, and a passive close conducting wall.
   It is a linear energy theorem with an interface gap, not a proof of
   nonlinear regularity or a completed embedded toroidal equilibrium.
5. The hot-core theorem concerns prescribed-field Vlasov transport and an
   absorbing boundary. It requires the explicit geometric buffer inequality.
   That inequality has NOT been certified here for a physical device.
6. The exact weak-QS seed, the Dommaschk vacuum family, and the stable cylinder
   are different constructions. Their favorable properties have not been
   proved for one common toroidal, self-consistent collisional plasma.
7. Coil realization, electromagnetic feedback, collisions, heating, fueling,
   ash, wall power and a fusion power balance remain outside the completed
   results. Their required estimates are identified rather than assumed.
