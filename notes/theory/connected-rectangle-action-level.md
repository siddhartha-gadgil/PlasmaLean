# A connected action level across a radial launch bracket

Let \(J\) be continuous on the closed rectangle \([a,b]\times[c,d]\), with \(a\le b\) and \(c\le d\). If \(J(p,c)\le H\le J(p,d)\) at every phase \(p\), then the level \(J=H\) contains a compact connected set \(K\) whose phase projection is exactly \([a,b]\). Thus one connected set meets both end faces and every intervening phase. Strict radial inequalities put all of \(K\) in \([a,b]\times(c,d)\). The Lean statements cover both a function on the ambient plane continuous on the rectangle and an action defined intrinsically on the product of the two interval subtypes. [Rectangle crossing proofs](../../PlasmaLean/Theory/Geometry/RectangleLevelCrossing.lean)

## Parametric fixed points

The underlying result is Browder continuation. If \(B\) is a nonempty compact convex subset of a finite-dimensional real normed space and \(F:[a,b]\times B\to B\) is continuous, a compact connected set of its fixed points projects onto \([a,b]\). Eilon Solan and Omri N. Solan give a proof from Brouwer's fixed-point theorem. The repository already supplies an independently verified Brouwer theorem through the TauCeti dependency. [Solan and Solan, *Browder’s Theorem through Brouwer’s Fixed Point Theorem*](https://doi.org/10.1080/00029890.2022.2160170)

In the Lean proof, take the compact fixed-point space. If no component meets both parameter faces, their images in its space of connected components are disjoint compact sets. This component space is compact Hausdorff and zero-dimensional, so a clopen set separates the images. Pulling it back partitions the fixed points into two compact pieces. Urysohn's lemma gives a continuous real function \(g\) on the ambient product which equals one on the piece containing the fixed points at \(a\) and zero on the piece containing those at \(b\). Brouwer applied to \((p,x)\mapsto(a+(b-a)g(p,x), F(p,x))\) gives a contradiction. Its second coordinate makes the point belong to one of the pieces, and its first coordinate sends it to the face excluded by that piece. The resulting spanning component is compact, and its connected phase projection contains every intermediate phase. [Fixed-point continuation and clopen separation](../../PlasmaLean/Theory/Geometry/RectangleLevelCrossing.lean)

For the scalar action, use \(F(p,r)=\min(d,\max(c,r+H-J(p,r)))\). If \(J<H\), its update moves outward unless \(r=d\), where the assumed sign excludes the inequality. The inward argument for \(J>H\) uses the opposite face. Every fixed point therefore has \(J=H\), including possible roots on the radial faces when the inequalities are weak. [Scalar specialization](../../PlasmaLean/Theory/Geometry/RectangleLevelCrossing.lean)

## Meaning for the physical application

The continuous action and its two oriented endpoint bounds are the inputs. Mere existence of an interior root at every phase would discard those bounds. For the QA2R birth sector the action is the physical first-well integral, the phase lies in \([-2^{-19},2^{-19}]\), and the interpolation radius lies in \([0.470,0.478]\). Applying this theorem requires identifying the same continuous action with the two original endpoint actions. The physical path and mirror hypotheses are documented in the sector criterion. [Physical sector and first-well continuity](compact-sector-first-well-actions.md)

A folded cubic illustrates how much regularity this conclusion provides. Take \(J(p,r)=r^3-r-p\), \(H=0\), \(|p|\le1\), \(|r|\le2\). The radial face signs are strict. The solution curve folds twice. A continuous choice of one radius for each phase would be injective, hence strictly monotone. Its image would join the unique endpoint roots below \(-1\) and above \(1\), and would therefore include \([-1,1]\), where \(r^3-r\) fails to be injective. A continuous single-valued radius already fails in this polynomial example. The rectangle theorem yields connectedness and full projection without differentiating the action.

## Verification

~~~sh
lake build PlasmaLean.Theory.Geometry.RectangleLevelCrossing
printf '%s\n' 'import PlasmaLean.Theory.Geometry.RectangleLevelCrossing' \
  'open PlasmaLean.RectangleLevelCrossing' '#print axioms clopen_separator' \
  '#print axioms parameter_fixed_points' '#print axioms level_crossing' \
  '#print axioms interior_level_crossing' '#print axioms interior_level_crossing_subtype' \
  | lake env lean --stdin
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-180 |
| Kind | Candidate-independent topology of a prescribed action level |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-178 supplies the physical application context. The topological proof depends only on Brouwer's theorem and compact Hausdorff separation. |
| Dependency requirement | Joint continuity on the closed rectangle and oriented radial face bounds at every phase. Strict bounds give interior radial clearance. |
| Produces | A compact connected exact-action set spanning every phase, plus finite-dimensional continuation for fixed points of a parameterized family. |
| Status | All five generic theorems kernel-verified. |
| Lean evidence | `RectangleLevelCrossing.clopen_separator`, `.parameter_fixed_points`, `.level_crossing`, `.interior_level_crossing` and `.interior_level_crossing_subtype`. |
| Audit evidence | Each declaration uses only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |
