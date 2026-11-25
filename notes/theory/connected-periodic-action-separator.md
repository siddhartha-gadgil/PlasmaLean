# A connected periodic action level separating the two boundary circles

Let \(J:(\mathbb R/\mathbb Z)\times[0,1]\to\mathbb R\) be continuous. Suppose \(J(p,0)<H<J(p,1)\) for **every** phase \(p\). The level \(J=H\) contains a compact connected set \(K\) in the open radial interval. Every path from the inner boundary to the outer boundary meets \(K\), including paths which move in phase and reverse their radial direction. The phase projection of \(K\) covers the circle. Each inner boundary point and each outer boundary point belong to different connected components of the complement of \(K\). Lean accepts both an intrinsic action on the circle and a periodic action on its real cover. [Annulus and periodic separator theorems](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean)

The same \(K\) has a homotopy obstruction. Its angular coordinate has no continuous real lift, and its inclusion into the annulus cannot be continuously deformed to a constant. This is a statement about the inclusion of the entire continuum. A winding number for a parametrized loop would require exhibiting such a loop. A continuous single-valued radius requires further information about the radial roots. [Essential inclusion and angular lift](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean) · [Oriented crossings and graphs](../../PlasmaLean/Theory/Geometry/PeriodicOrientedCrossings.lean)

## Proof

The path-intersection argument works on \(X\times[0,1]\) for any compact Hausdorff path-connected \(X\). Take finitely many boundary-to-boundary paths. Their two endpoint phases are free. One can continuously deform each path \((x(t),r(t))\) to the vertical path at \(x(0)\) by replacing its phase by \(x(st)\) and its radius by \((1-s)t+sr(t)\). Vertical paths move continuously along any path in \(X\). Consequently a continuous one-parameter family of boundary passages visits all the finitely many paths. Pull the action back along this family. The parameter of the family and the time on the path give a rectangle with opposite face signs. Its connected crossing maps to a connected part of the original level meeting all the chosen paths. [Rectangle continuation](connected-rectangle-action-level.md) · [Cylinder proof](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean)

For each passage, the components of the compact level which meet that passage form a closed subset of the compact Hausdorff space of components. The finite construction proves the finite intersection property, so a single component meets every passage. Vertical passages give full phase projection. The complement is open and locally path-connected on the annulus. In this complement, membership in the same connected component would give a path joining the two boundary points. [Complement component theorem](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean)

Suppose the angular projection on this separator admitted a continuous real lift. Tietze extension would give a bounded continuous real extension \(G\) on the whole annulus. On an angular strip wider than its range, the equation
\[
 \theta-G(\theta\bmod 1,r)=\tfrac12
\]
has opposite signs relative to its right side at the two angular ends for every radius. The rectangle theorem, now with radius as parameter, gives a connected solution set meeting both radial boundaries. Its projection into the annulus avoids the separator, since on the separator \(\theta-G\) has integral values. This contradicts complement separation. Finally, lifting a hypothetical homotopy from a constant to the inclusion along the covering \(\mathbb R\to\mathbb R/\mathbb Z\) would produce the excluded real angle. [Winding obstruction in Lean](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean)

Pascoletti and Zanolin prove an annular path-cutting theorem for arbitrary closed sets and identify essential inclusion as a consequence in their Lemmas 14 and 15. The present formalization works directly with scalar levels and proves the action statement through the parameterized rectangle theorem. The current QA2R launch calculation covers a short phase sector. Applying the annulus theorem to that field requires continuity and the two oriented inequalities over a whole period. [Pascoletti and Zanolin, *A Crossing Lemma for Annular Regions and Invariant Sets*](https://doi.org/10.1155/2013/267393) · [QA2R sector](compact-sector-first-well-actions.md)

## Verification

~~~sh
lake build PlasmaLean.Theory.Geometry.AnnularLevelSeparator
printf '%s\n' 'import PlasmaLean.Theory.Geometry.AnnularLevelSeparator' \
  'open PlasmaLean.AnnularLevelSeparator' '#print axioms cylinder_separator' \
  '#print axioms different_complement_components' '#print axioms annulus_separator' \
  '#print axioms periodic_separator' '#print axioms no_angular_lift' \
  '#print axioms essential_inclusion' | lake env lean --stdin
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-185 |
| Kind | Candidate-independent annular separation and winding obstruction |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-180 and the circle covering, compactness and Tietze extension theorems. |
| Dependency requirement | A continuous scalar over the entire periodic annulus and strict oriented radial-face signs for every phase. |
| Produces | One compact connected exact-action set intersecting every boundary passage, separating the boundary circles, with essential inclusion and no continuous real angular lift. |
| Status | Six public declarations kernel-verified. Full-period physical inputs remain open. |
| Lean evidence | `AnnularLevelSeparator.cylinder_separator`, `.different_complement_components`, `.annulus_separator`, `.periodic_separator`, `.no_angular_lift`, `.essential_inclusion`. |
| Audit evidence | All six use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
