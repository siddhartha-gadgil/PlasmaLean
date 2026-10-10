# Domain Library for PlasmaLean in Lean

These are instructions for modelling real-world domains in Lean to allow auditing cleanly, customized for PlasmaLean. The lean library has a *kernel*, *sanity checks* for the kernel and a *library* of functions with *verification theorems*.

When building such a library, add a `[[lean_lib]]` entry to `lakefile.toml`. You can use Mathlib and TauCeti as dependencies.

Add documentation strings for all definitions and theorems, and module documentation for each module. Use Lean's module system and ensure the correct functions and theorems are marked public or exposed.

## Looping/Incremental building

When following these instructions for the first time, build the kernel as in the following section, then sanity checks. Loop through the library building steps accumulating theory as code until progress halts.

For subsequent runs, examine the kernel and fix errors if any, noting carefully changes as comments. Add to the kernel only if more empirical facts or real-world concepts need to be modelled. It is encouraged, but not essential, to add sanity steps. The main goal of subsequent runs is to assess what has been done and what remains for the core goals as well as the prompt, and to augment the library with verified code.

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
