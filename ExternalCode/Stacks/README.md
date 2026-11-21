# Discrete valuation specialization prerequisites

These modules supply the geometric specialization used in the binary instability
construction for Chen–Moriwaki's *Arakelov Geometry over Adelic Curves*.

For a locally finite-type, quasi-compact morphism `f : X ⟶ Y` with `Y` locally
Noetherian and `y ∈ closure (range f.base)`, the specialization theorem constructs
a discrete valuation ring `R`, its fraction field `L`, maps `Spec L → X` and
`Spec R → Y`, and a commutative square with prescribed closed point. The generic
point maps to the generic point of an irreducible component of `X`. When this
point does not already map to `y`, the fraction field is identified with the
residue field at that source point.

The original finite-type statement is retained. No completeness, power-series
presentation, or finite residue-field extension is asserted. In the tensor
instability application, `f` is the group orbit parameter morphism, so the
field-valued source point supplies a group element over the fraction field.
This specialization theorem alone is not a Hilbert–Mumford equivalence.

## Source attribution

Adapted from
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b),
commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, under Apache-2.0.
The original copyright and license notices are retained. The distinction between
upstream `StacksCore` and `StacksFrontier` modules is preserved; `StacksFrontier`
is not asserted to have upstream human review.
