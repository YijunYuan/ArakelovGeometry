# Selected Stacks DVR specialization

This subtree contains only the recursive Stacks-source import closure of
`StacksFrontier/AlgebraicGeometry/Limits/NoetherianValuativeCriterion/DiscreteValuationSpecialization.lean`
from [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b),
commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`: 14 modules, 4,814 original lines.
Files were downloaded individually. There is no donor package dependency.
Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`
match the host. The Apache-2.0 license is retained in `LICENSE`; original headers
are preserved. `provenance.json` records each original hash, local path, edits,
and verification status. Mathematical namespaces remain upstream namespaces.
Only Stacks imports acquire the prefix `ExternalResults.Stacks.`.

The upstream scope is retained: for a locally finite type, quasi-compact morphism
`f : X ⟶ Y` with `Y` locally Noetherian and `y ∈ closure (range f.base)`,
`AlgebraicGeometry.nonempty_discreteValuationSpecialization` produces a DVR `R`,
its fraction field `L`, maps `Spec L → X` and `Spec R → Y`, their commutative
square, and the specified closed point. It also selects a generic point of an
irreducible component of `X`. When that point does not already map to `y`, the
fraction field is identified with the residue field of that source point.

It asserts **no** completeness, identification with a power-series ring, or
finiteness of the DVR residue field over any ground field. In the already-in-image
case the constructed DVR is a localization of a polynomial ring over the source
residue field; the fraction field is enlarged. Frontier is not human-reviewed
upstream; local independent review and kernel/axiom results are recorded in the
provenance file as they become available.

For Bost p31 (Theorem 1.1, via the binary instability input to CM Theorem 5.4.3),
apply the producer to the **actual group orbit parameter morphism**. Only then
is `Spec L → X` an actual group element whose action specializes to zero.
A source consisting merely of the orbit closure does not supply such an element.
This is the geometric input for the general-DVR matrix route. The orbit morphism
and its finite-type/quasi-compact hypotheses, invariant separation, compatible
ground-field structures, a primitive initial determinant vector, and descent from
the arbitrary DVR residue field are separate unmet consumers. The local
`ArakelovGeometry.InvariantTheory.DVRWeights` producer now proves the actual A2
tensor/exterior/dual coordinate-weight implication using general DVR Cartan. This port alone does not prove A8 or a
Hilbert–Mumford theorem.

Verification: the narrow target passed (96.1 s; 5.3 s after the documentation
correction); four transitive axiom probes passed (28.6 s), using only
`propext`, `Classical.choice`, and `Quot.sound`. Independent semantic review
found no defect in the target or its main algebraic route. It corrected the
informal proof of dimension-one domination: choose a generator of maximal
valuation in a dominating valuation ring. The original formal proof already
made this choice. Four upstream module-header placement warnings and one
optional tactic suggestion are retained to minimize changes; no proof warnings
or sorries occur. The API is at the level of `Scheme`; compatibility with the
ground-field structure and interpretation as a ground-field group functor point
are additional downstream obligations.
