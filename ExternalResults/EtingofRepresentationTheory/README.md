# Selected Etingof representation theory results

Five proof modules (892 lines) selected from
[mathlib-initiative/EtingofRepresentationTheory](https://github.com/mathlib-initiative/EtingofRepresentationTheory/tree/752fe269b3233f08f0795aa4bcdc5b4c84be7a50),
commit 752fe269b3233f08f0795aa4bcdc5b4c84be7a50, Apache-2.0.
The original LICENSE and NOTICE are retained byte-for-byte.

The port proves the permutation centralizer formula, semisimplicity of the
actual tensor image algebra in characteristic zero, and the GL tensor-map
span formula over an infinite field. It omits alignment metadata, enveloping
algebras, and detailed Schur–Weyl decompositions. All imports are narrow;
no donor dependency or toolchain change is required.

The project consumer is
ArakelovGeometry.InvariantTheory.TensorPowerSemisimple. Over an algebraically
closed characteristic-zero field and a nonzero finite-dimensional space, it
proves semisimplicity of every actual SL tensor power, including degree zero,
and invariant lifting across equivariant quotients of invariant subspaces.
This is the fixed-degree representation input for Bost p31's binary instability
branch. Bounded polynomial quotients, two-factor assembly, and actual orbit
separation remain separate. The infinite group algebra is not asserted semisimple.

[provenance.json](provenance.json) records exact source/local hashes, retained
regions, alterations, imports, and kernel evidence. The evidence directory
retains the final build record, the twelve-root transitive axiom audit and its
degree-zero example. The donor source was fetched at the pin; kernel evidence
comes from local Lean 4.35/mathlib, not a build of the original donor package.

Import the concrete project consumer above. For the selected donor theorem alone,
use ExternalResults.EtingofRepresentationTheory.PiTensorProduct.MapSpanCentralizer.
