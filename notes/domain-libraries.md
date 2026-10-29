# Domain Library for PlasmaLean in Lean

These are instructions for modelling real-world domains in Lean to allow auditing cleanly, customized for PlasmaLean. The lean library has a *kernel*, *sanity checks* for the kernel and a *library* of functions with *verification theorems*.

When building such a library, add a `[[lean_lib]]` entry to `lakefile.toml`. You can use Mathlib and TauCeti as dependencies.

Add documentation strings for all definitions and theorems, and module documentation for each module. Use Lean's module system and ensure the correct functions and theorems are marked public or exposed.

## Agent Runs and Loops

When following these instructions for the first time (i.e., where there is no domain kernel), build the kernel as in the following section, then sanity checks. Loop through the library building steps accumulating theory as code until progress halts.

For subsequent runs, examine the kernel and fix errors if any, noting carefully changes as comments. Add to the kernel only if more empirical facts or real-world concepts need to be modelled. It is encouraged, but not essential, to add sanity steps. The main goal of subsequent runs is to assess what has been done and what remains for the core goals as well as the prompt, and to augment the library with verified code.

After each run, write a markdown report in the `progress/` directory with filename `{yyyy-mm-dd}-progress.md`, i.e., beginning with the date. In case of more than one report in a day, add appropriate suffix. Also update the progress in the website at `docs/` in the appropriate pages.

After **every run**, including a run that stagnates or is blocked, refresh the website's progress slideshow. Edit `progress/slideshow.json`, the source for `docs/slides.html`, which is linked from the original landing page. Keep its `updated` date and `report` filename aligned with `progress/status.json`. Update the latest results, progress so far, evidence links, assumptions, remaining gaps and next targets; if nothing new was proved, say so and record the blocker. Review any counts against the actual build/audit report. Distinguish compiled theorems from synthetic examples, supplied physical data and planned work; never imply practical confinement or construction readiness from a fixture alone. Keep the brief progress summary in `README.md` consistent too.

Regenerate the website and slideshow with `node scripts/generate_handbook.mjs`, then run `node scripts/check_site.mjs`. Fix stale output, broken evidence links or failed checks before finishing the run. Edit the source JSON and Markdown rather than generated HTML. Preserve the original landing-page motivations and graphics, and keep the slideshow reachable from it.

Finally, **commit and push** the completed stage: stage paths explicitly (never `git add -A` while other agents or runs may have files in progress), write a message that names the stage and its main result, end it with the attribution line, and `git push`. A stage is not finished until it is pushed. This applies after every completed work unit or phase stage, including a stage that ends in a recorded barrier or failure.

## Kernel

This is the layer that models the domain with definitions and empirically (or more generally externally) known facts. It should be kept as small as reasonable while being a complete model. By complete we mean all relevant facts should be consequences and all queries we wish to answer should be answerable in terms of functions that can be built from the kernel.

The following are ingredients of the kernel. NEVER introduce additional axioms.

* Definitions, Structures and Inductive Types correspond to the basic ingredients of the domain.
* Relevant properties of the domain are modelled by structures, typeclasses or inductive propositions.
* Facts and laws are modelled as *typeclasses* and results and definitions depending on these in the library should invoke them as implicit arguments.

The kernel should be a separate file. Explain the domain being modelled and the corresponding Lean code in the module documentation. Clearly indicate in the module documentation that this is the kernel file.

## Sanity checks for the kernel

To ensure correctness of the definitions in the kernel, state results that are true in the domain and prove that they hold in terms of the definitions (and typeclasses) in the kernel. These should include characterizing results, special cases including degenerate ones, bounds if applicable etc.

## Library with verification

The core goal of the library is to enable design of stellerators with proofs that plasmas will be stable in them. The conditions such as strengths of magnetic fields, temperatures etc should be realistic. We will incrementally work towards this.

The library builds on the kernel incrementally adding discoveries starting with those from the literature and subsequently by Autoformalizing AI discoveries. In PlasmaLean, we will use both theoretical advances and exact numerical calculations (using interval arithmetic etc). However, we prioritize theoretical advances. Use all mathematical skills to add to the theory as far as possible, using numerical experiments to help discovery. Use proofs based on exact computations to go beyond the theory where it is not clear how to extend it.

Whenever a definition or type is introduced, state and prove properties. This is meant to ensure the definitions are correct. If a definition has characterizing properties, state and prove them. In addition, state consequences, results for special cases (especially degenerate ones) etc and prove these. In case of failure check and correct definition. When a theorem is proved that is supposed to be useful, make similar sanity checks by proving corollaries, deducing special cases etc to ensure that the statements are correct.
