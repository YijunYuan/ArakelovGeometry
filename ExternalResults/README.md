# Selected external results for the Bost foundation

This directory contains selected, locally verified transplants used by the `lite`
branch. It is not a checkout or dependency on an entire donor project. The existing
mathlib and HarderNarasimhan dependencies remain the first sources to consult.

No external Lean theorem has been transplanted into this directory yet. Survey
findings are candidates, not verification evidence.

## Layout and ownership

- `Stacks/`: selected AxiomMath Stacks modules; preserve the distinction between
  upstream `StacksCore` and `StacksFrontier` paths.
- `TauCeti/`: selected TauCeti modules, preserving upstream mathematical namespaces
  unless a documented compatibility change is necessary.
- Each donor subtree owns its own `provenance.json` and license notices, so parallel
  migration tasks do not edit a shared provenance file.
- `ExternalResults.lean` is deliberately a small entry point. Consumers import the
  particular verified module they need; it must not become an import of all donor code.

## Required record for every imported result

Record the upstream repository, exact commit and original path; retain copyright,
license and attribution notices. Record the local path, changed imports/API, and
whether the mathematical statement is unchanged, specialized or weakened.

The module docstring and the docstring of a specialized exported theorem must state:

1. The original result and its hypotheses.
2. The exact local statement and any omitted generality.
3. The Bost page/formula and downstream declaration that use it.
4. Why the local statement supplies that use, including any remaining bridge.

Mirror substantive scope changes in the project [README](../README.md). Do not label
a conditional interface as a proved producer for its missing hypothesis. Verification
records must identify the narrow build target, revision, transitive axiom audit and
semantic review. A source scan without `sorry` is not an axiom audit.

## Initial selection policy

Prefer the fixed, same-toolchain Stacks DVR closure over general algebraic-stack
machinery. For TauCeti, first assess its Lean 4.35.0 history and the smallest useful
SL/invariant interfaces. Its Mathlib pin differs from this project even in that
history, so compatibility must be proved by local builds. Do not upgrade the shared
toolchain or add a complete donor project as a shortcut.

Use the project's already proved PID matrix diagonalization before copying another
Smith-normal-form implementation. Bost needs the specific binary tensor/quotient
representation and one unstable direction; general GIT quotients and invariant-ring
finite generation are not independent goals.
