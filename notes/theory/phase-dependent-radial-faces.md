# Action levels between phase-dependent radial faces

Two continuous radial faces may bend around the phase circle. This allows a proposed inner and outer bracket to follow a physical family of wells whose target radius varies with launch angle. The directed quarter-turn screen suggests looking outside the original narrow strip there. [Quarter-turn calculation](opposite-section-excludes-pilot-action-strip.md)

Let \(l,h,j:S^1\to\mathbb R\) be continuous, with \(l<h\) everywhere. Suppose the actual first-well action \(J\) is continuous on the closed region \(l(\phi)\le r\le h(\phi)\). Assume \(J(\phi,l(\phi))<j(\phi)<J(\phi,h(\phi))\) at every phase. There is a compact connected subset of the strict interior on which \(J=j\). It projects onto the full circle, meets every continuous path across the two faces within the strip, and its phase map has no continuous real lift. These conclusions allow several target radii at the same phase. [Lean theorem](../../PlasmaLean/Theory/Geometry/MovingRadialFaces.lean)

The proof uses the normalized radius \(s=(r-l)/(h-l)\). Apply the annular separator to \(J(\phi,l+(h-l)s)-j(\phi)\) and take the image of its connected set in physical coordinates. Normalizing any physical face-to-face path shows that it meets that image. A real lift on the image would give one on the original separator. [Annular separation theorem](../../PlasmaLean/Theory/Geometry/AnnularLevelSeparator.lean)

There is also a dynamical first-exit test. Let a continuous radius start strictly between two continuous time-dependent faces. Suppose its observed action stays in a closed band as long as the radius lies between them, and at each lower or upper face the observed action is strictly below or above that band, respectively. The radius stays strictly between the faces through the given horizon. This version allows an action specified by independent boundary observations and requires no continuity of the action in time. The normalized radius must otherwise first reach zero or one. [First-exit theorem](../../PlasmaLean/Theory/Geometry/MovingRadialFaces.lean)

For QA2R the necessary full-period first wells and strict inequalities along a moving pair of faces remain open. The completed original sector supplies one local bracket. Selecting another phase-dependent label inside that same narrow strip cannot resolve its quarter-turn action obstruction when the physical floors there hold. [Local physical result](completed-original-radial-sector.md) · [Quarter-turn scope](opposite-section-excludes-pilot-action-strip.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-212 |
| Kind | Reusable geometric and dynamical theorems |
| Addresses | G-10, Q-35 |
| Depends on | N-185 annular separation, the radial first-exit lemma and N-190's moving-face question |
| Dependency requirement | Continuous ordered faces, a continuous action in the enclosed region, and strict signs on both faces for the separator. |
| Produces | An angularly essential connected level for moving physical faces and a separate pre-exit test. |
| Difficulty | The abstract geometry is proved. Finding a global family of physical wells with certified face signs is open. |
| Status | Lean-verified in the default library. |
| Lean evidence | `MovingRadialFaces.separator` and `MovingRadialFaces.stays_between`. |
| Audit evidence | Standard axioms for both public theorems. |
| Last updated | 25 November 2026 |
