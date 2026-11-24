# Comparing action when both the field and arclength density change

Two field lines written in the same angular coordinate generally have different arclength per radian. Lean now gives an explicit term for that change in the action and its label derivative. [Density perturbation theorem](../../PlasmaLean/Theory/Kinetic/MirrorActionDensity.lean)

Let $\mu$ be a common parameter measure and $w,v$ nonnegative, integrable, measurable arclength densities. For the strength profile $C$, assume $C\ge b_0$ almost everywhere and put $V=\sqrt{2(h-b_0)_+}$. Then

$$
|J(w\mu,C,h)-J(v\mu,C,h)|\le V\,\|w-v\|_{L^1(\mu)}.
$$

The estimate follows by integrating the density difference against the clipped speed, which is bounded by $V$. The constant is sharp: on a unit-mass parameter space, densities one and zero and the constant field $C=b_0$ attain equality. If a profile estimate gives $|J(w\mu,B,h)-J(w\mu,C,h)|\le E$, the full action change is at most $E+V\|w-v\|_1$. The profile term can come from the regular mirror collar, including for a well with a critical bottom. [Collar bound](mirror-action-collar.md)

For a label $\alpha$, suppose the action change under a nearby profile at **fixed reference density** is at most $P|\beta-\alpha|$ and $\|w_\alpha-w_\beta\|_1\le L|\beta-\alpha|$. Whenever the action derivative exists, its magnitude is at most $P+VL$. The application to Dommaschk now has two concrete inputs to certify, a profile estimate and an integrated change of the geometric density on a common interval. N-86 identifies that density with the norm of the physical Cartesian derivative. [Physical arclength](dommaschk-first-physical-action-cells.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-88 |
| Kind | Candidate-independent comparison of geometric actions |
| Addresses | G-6, G-10, Q-1, Q-35 |
| Depends on | N-72, N-85, N-87 |
| Dependency requirement | A common parameter measure, integrable nonnegative densities and a field floor; a fixed-density profile bound for the combined estimate. |
| Produces | Sharp L¹ arclength correction and a derivative bound for moving densities. |
| Difficulty | Measure or certify how quickly the physical density and profile vary across the proposed label band. |
| Status | Five Lean theorems compiled, including the sharpness example. |
| Lean evidence | `MirrorActionDensity.action_density`, `.density_difference`, `.profile_and_density`, `.label_derivative`, `.density_bound_attained`. |
| Audit evidence | Checked in the default library with only its standard axioms. |
| Last updated | 24 November 2026 |
