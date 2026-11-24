# One transverse mirror well gives an open set of physical launch positions and heights

A particle born strictly inside a well with two transverse first mirrors remains a regular mirror birth after sufficiently small joint changes in its **Cartesian launch position and its mirror height**, provided a local field-line window brackets the two mirrors as specified below. The conclusion gives a nonempty open subset of the four-dimensional space of positions and heights. Every measure that charges nonempty open sets assigns these regular births positive mass. The theorem gives no numerical radius or fraction. [Local physical theorem](../../PlasmaLean/Theory/Kinetic/MirrorLocalFlowPersistence.lean)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-112 |
| Title | Persistence of a regular mirror birth under changes of position and height |
| Kind | Differential-geometric and measure-theoretic proof |
| Addresses | G-6, G-10, Q-1, Q-16, Q-19, Q-35 |
| Depends on | N-97, N-100 and Mathlib's Picard–Lindelöf and smooth cutoff theorems |
| Dependency requirement | Regular arclength birth from a transverse bracket. Openness of a jointly continuous family of strength profiles and their time derivatives. |
| Produces | An open neighborhood in physical launch position and height from one locally defined physical field-line witness, and positive measure for regular births. |
| Difficulty | The varied trajectories must stay in the physical chart on an entire compact time interval. The strength derivative at the two window endpoints has to refer to an actual differential equation. |
| Status | Verified in the default library |
| Lean evidence | MirrorWellPersistence.isOpen_flowBracketIn, regular_birth_open_of_model, regular_birth_open_of_local and regular_birth_mass_of_local. |
| Audit evidence | The full neighborhood and measure theorems and their auxiliary lemmas have the standard Lean axiom set. |
| Last updated | 25 November 2026 |

## Local statement

Let $U$ be open in Euclidean three-space. On $U$, let $V$ be a $C^1$ vector field and let $F$ be a $C^1$ scalar observable. Assume $F(x)=\lVert B(x)\rVert$, $B(x)\ne0$ and $V(x)=v(x) B(x)/\lVert B(x)\rVert$ for a continuous positive $v$. This allows an angular clock as well as arclength. For $a<c<b$, suppose a solution $X'=V(X)$ stays in $U$ throughout $[a,b]$, with $X(c)=x_0$. Write $f=F\circ X$. At the proposed height $h_0$ suppose

- $f(c)<h_0$, and both $f(a)$ and $f(b)$ exceed $h_0$.
- At every contact $f(t)=h_0$ on $[a,c]$, $f'(t)<0$. At every such contact on $[c,b]$, $f'(t)>0$.

Then some open neighborhood $W$ of $(x_0,h_0)$ consists entirely of pairs $(x,h)$ satisfying the physical arclength predicate `Contract.RegularMirrorBirth B x h`. Consequently the set of all regular births has positive measure for every measure on position and height that charges nonempty open sets, including Lebesgue measure. All smoothness, alignment and positivity hypotheses on the physical field are local to $U$. [Bracket and contract](../../PlasmaLean/Theory/Kinetic/MirrorWellPersistence.lean) · [Local theorem and measure corollary](../../PlasmaLean/Theory/Kinetic/MirrorLocalFlowPersistence.lean)

## Why one orbit suffices

The image of the observed closed time interval is compact. Choose nested neighborhoods of this image whose outer closure stays in $U$. A smooth scalar cutoff equals one throughout the inner neighborhood and has compact support in the outer closure. Multiplying $V$ and $F$ by the cutoff gives globally defined $C^1$ extensions. The extended velocity is bounded and Lipschitz, so Picard–Lindelöf produces a flow jointly continuous in initial position and time throughout the required window. Uniqueness identifies the original orbit in this flow. [Local cutoff construction](../../PlasmaLean/Theory/Kinetic/MirrorLocalFlowPersistence.lean) · [Flow and uniqueness proof](../../PlasmaLean/Theory/Kinetic/MirrorFlowPersistence.lean)

For the varied orbits, the time derivative of $F(X(t))$ equals $DF(X(t))[V(X(t))]$ and is jointly continuous. Staying in the inner open neighborhood throughout the compact window is itself an open condition on the launch. N-100's compact-projection argument therefore preserves the strict cap inequalities and both contact orientations. Positive speed converts each resulting well to the arclength contract. A positive mass follows even when the size of this neighborhood is unknown. The candidate application requires exhibiting the local field and one such bracket on the same known trajectory. [Earlier family theorem and pilot angle-height rectangle](open-mirror-wells-and-birth-area.md)

## Replay

~~~bash
lake --wfail build PlasmaLean.Theory.Kinetic.MirrorLocalFlowPersistence
lake env lean scripts/check_axioms.lean
~~~
