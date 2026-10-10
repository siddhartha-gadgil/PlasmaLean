# Domain Libraries in Lean

These are instructions for modelling real-world domains in Lean to allow auditing cleanly. The lean library has a *kernel*, *sanity checks* for the kernel and a *library* of functions with *verification theorems*.

When building such a library, add a `[[lean_lib]]` entry to `lakefile.toml`. Before building, look up (non-standard) dependencies in `lakefile.toml` and read and use their code.

Add documentation strings for all definitions and theorems, and module documentation for each module. Use Lean's module system and ensure the correct functions and theorems are marked public or exposed.

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

List functions that answer various queries a user may have about the domain and which are helpful in some way or the other in working with the domain. Implement functions, definitions, types etc for these. In each case state and prove properties of the definitions. This is meant to ensure the definitions are correct. If a definition has characterizing properties, state and prove them. In addition, state consequences, results for special cases (especially degenerate ones) etc and prove these. In case of failure check and correct definition. Following the Mathlib idiom, immediately after a definition include enough characterizing properties so that subsequently we do not have to unfold (or `simp` or `rw` with) the definition but can use the properties instead.

The library should constitute a reasonably complete and verified API, so that function calls or small functions building on those in the library should suffice for most uses. Organize into files and if appropriate directories.
