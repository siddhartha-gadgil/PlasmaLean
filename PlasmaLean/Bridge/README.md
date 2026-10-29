# Bridge/

Composition theorems that connect laws, theory and certificates to design claims.

- [`Contracts.lean`](Contracts.lean): common-witness certificate composition. `DesignContracts`
  keeps separate predicates (`equilibrium`, `stability`, `transport`, `components`) on a design,
  an uncertainty parameter and a witness; `RobustDesign` asks for one witness per parameter in the
  uncertainty set satisfying all of them; `compose_branch`, `robust_mono`.

Most certificate-to-semantics bridges live next to their certificates (soundness theorems in
`Certificates/`) or in the design families (`Design/…LowMem*`, `…Chain*` for the KAM families).
Keep a bridge here when it is reused across families.
