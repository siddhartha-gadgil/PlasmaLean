# Design/

Placeholder. Concrete candidates of your domain go here: specification records, exact data
emitted by oracles, and the theorems that compose kernel laws, bridges, theory and certificates
into a verified claim about a specific candidate (see the `domain-design` skill).

Conventions: large generated data in their own modules (≤ 6 GB peak per module); main theorems
registered in `scripts/check_axioms.lean`; default-build modules imported by `LeanTheory.lean`,
heavier ones as on-demand top modules (`lake build LeanTheory.Design.<Top>`), documented here.
The template's end-to-end example is `Certificates/Example.amplitude_cert`.
