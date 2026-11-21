# Arakelov Geometry over Adelic Curves

[![CI](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.35.0-5C2D91)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.35.0-5C2D91)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

This project is a partial Lean formalization of Huayi Chen and Atsushi Moriwaki's
[*Arakelov Geometry over Adelic Curves*](https://doi.org/10.1007/978-981-15-1728-0)
(Lecture Notes in Mathematics 2258, Springer, 2020). It builds on mathlib and the
[HarderNarasimhan library](https://github.com/YijunYuan/HarderNarasimhan).

The development covers adelic curves, substantial parts of the theory of adelic
vector bundles, selected local and geometric prerequisites, and parts of the
filtration and tensor-slope theory. It does not formalize the entire book.
Some results have stronger hypotheses or weaker conclusions than the corresponding
book statements. The scope descriptions below and the Lean docstrings record
these restrictions.

## Mathematical setting

An adelic curve consists of a field, a measure space of places, and absolute values
whose logarithmic evaluations on nonzero field elements are integrable. Properness
is the product formula. An adelic vector bundle equips a finite-dimensional vector
space with norms on its completed scalar extensions, subject to domination and
measurability of both the norm family and its dual.

The Lean statements retain properness, measurable-base conditions, Archimedean
normalization, finite-place ultrametricity, and purity wherever required. Ordinary
and Hermitian scalar extension are distinct constructions. Counterexamples and
corrected hypotheses are included where an unrestricted statement fails.
Section and theorem numbers follow the October 2019 version of the book; the
mathematical statements determine the correspondence with the published edition.

## Chapters 1 and 2: selected prerequisites

| Topic | Implemented material | Scope |
| --- | --- | --- |
| Local normed linear algebra | Coordinate bounds and near-orthogonal bases; dual, restriction, quotient, tensor, exterior, and determinant norms; local exact-sequence comparisons; ordinary and Hermitian scalar extension; real and complex norm comparison; John ellipsoid constructions. | Complete-field, ultrametric, and usual-Archimedean hypotheses remain explicit. Chapters 1 and 2 are not complete. |
| Analytic points and geometric fibres | Valued points of schemes, their topology, scalar-extension maps, completed residue fields, fibres of module sheaves and line bundles, and completed section values. | General analytic compactness and geometric section supremum norms remain incomplete. |
| Global sections | Flat tensor descent over finite covers, tensor comparison on section sheaves, and the relative affine section equivalence. | The full global base-change equivalence and the application in 2.1.19 remain incomplete. |

The main directories are [Analysis](ArakelovGeometry/Analysis/),
[LinearAlgebra](ArakelovGeometry/LinearAlgebra/), and
[AlgebraicGeometry](ArakelovGeometry/AlgebraicGeometry/).

## Chapter 3: adelic curves

| Section | Implemented material | Scope |
| --- | --- | --- |
| 3.1: definitions and basic properties | Adelic structures and proper curves; Archimedean locus and exponent; measurability, integrability, and finite Archimedean mass. | Finiteness of Archimedean mass retains the stated lower-bound hypothesis. |
| 3.2: examples and constructions | Number-field curves and their product formula; rational function fields; trivial absolute-value curves; amalgamation; restriction to a subfield or measurable subset. | General projective-curve and polarized-variety examples, polarized arithmetic varieties, and the separate product formula for the specific example in 3.2.5 remain incomplete. |
| 3.3: finite separable extensions | Extension parameter spaces, embeddings, fibres, fibre probabilities, integration, induced measures, logarithmic integrability, and preservation of properness. | The statements retain their field and measurability assumptions. |
| 3.4: algebraic extensions | Inseparable extensions, finite intermediate fields, projective fibre probabilities, algebraic-extension measures, disintegration, base change, and tower compatibility. | Signed tower formulas retain integrability and almost-everywhere equality. |
| 3.5: heights and Northcott | Heights and extension compatibility; polynomial and root estimates; bounded-height-and-degree finiteness; Northcott ascent under finite extension. | The Northcott hypotheses are explicit. |
| 3.6: automorphisms | Measurability of pullbacks, attained maxima on finite fibres, and measurable invariant majorants. | Algebraic-extension and measurability assumptions are retained. |
| 3.7: morphisms | Morphisms on real L1 spaces, identity and composition, algebraic extension and subfield restriction, and rational-function examples with circle averaging. | The separate product formula in 3.2.5 is not included. |

Entry points include [definitions](ArakelovGeometry/AdelicCurve/Defs.lean),
[extensions](ArakelovGeometry/AdelicCurve/Extension.lean),
[heights](ArakelovGeometry/AdelicCurve/Height.lean), and
[morphisms](ArakelovGeometry/AdelicCurve/Morphism.lean).

## Chapter 4: adelic vector bundles

| Topic | Implemented material | Scope |
| --- | --- | --- |
| 4.1: norm families and operations | Restriction and separated quotient norms, operator duals, bidual comparisons, profile direct sums, projective/injective/mixed tensors, Hermitian tensors, exterior powers, and determinants. | Operations use the original completed fibres and their induced norms. |
| 4.1: scalar extension and domination | Ordinary and Hermitian extensions, transitivity, dual and subquotient compatibility, finite-stage descent, degree transport, domination and strong domination, basis-distance criteria, and metric completion. | The mixed-basis identity in 4.1.5 includes arbitrary algebraic extensions and rank zero. Strong domination in 4.1.15 allows nonmeasurable choices of extending places. |
| 4.1: measurability | Countable evaluation formulas for duals, quotients, distances, tensors, exterior powers, and determinants; measurable scalar extension and Hermitian approximation. | Scalar extension uses common countable density or the countable discrete-base alternative. The unrestricted uncountable discrete-base statement is not asserted. |
| 4.1: examples | Counterexamples concerning domination, distance to a basis family, and quotient measurability; profile direct sums; number-field density and completion. | The result corresponding to 4.1.36 requires strong domination, and a counterexample to the weaker printed hypotheses is included. The full section-supremum-norm application in 4.1.18 remains incomplete. |
| 4.2: adelic divisors | Divisors as real L1 classes, continuous linear degree, effective and principal divisors, the closure of the principal subspace, the Banach quotient class space, pullback, and pushforward. | Degree descends to divisor classes on proper curves. |
| 4.3: degrees | Line and determinant degrees, isometry and extension transport, discrepancy bounds, flag comparisons, exact Hermitian additivity, positive degree, and dual Riemann–Roch comparisons. | General norm families retain discrepancy errors. The mixed-tensor result is an inequality, with a counterexample to unrestricted equality. |
| 4.3: slopes and Harder–Narasimhan theory | Heights of maps, extremal slopes, attainment, destabilizing subspaces, slope comparisons, finite flags, real-indexed filtrations, duality, functoriality, weighted degrees, and polygons. | The measurable-base and normalization hypotheses are explicit; positive-rank assumptions are retained where required. |
| 4.3: general and absolute invariants | General filtrations and comparisons, modified invariants, algebraic-closure and finite-stage descent, ordinary and geometric absolute invariants, and tower results. | These are not unrestricted statements over an arbitrary measurable base. |
| 4.3: minima and Minkowski properties | Successive-minimum filtrations, independent-vector descriptions, slope comparisons, tensor/minimum bounds, and consequences of ordinary, strong, and absolute Minkowski properties. | A result assuming a Minkowski property does not establish that property for every curve. Full all-index transference and the absolute bounds in 4.3.74 remain incomplete. |
| 4.3: section counts | The number-field section-count/positive-degree comparison in 4.3.24, trace-dual lattices, codifferents, trace-dual extremal slopes, and positive twists. | The geometric curve comparison in 4.3.23 remains incomplete. |
| 4.3: strong-to-ordinary comparison | The implication with an additional Archimedean correction, together with Hermitian and zero-Archimedean-mass cases. | The unrestricted positive-constant implication at the same constant in 4.3.81 remains open. |
| 4.4: number-field models | Local and global unit-ball modules, localization, completed lattice gauges, spanning and coherence criteria, finite generation, lattice-induced bundles, degree/covolume comparisons, purity, and impurity. | Dominated, coherent, pure, and lattice-induced families remain distinct. This is not a complete formalization of every statement in 4.4. |

The [HarderNarasimhan library](https://github.com/YijunYuan/HarderNarasimhan)
supplies existence and uniqueness of finite semistable flags and the largest
slope maximizers used in the Hermitian theory. The adelic game construction uses
the induced subquotient norms, identifies first-player values with minimal slopes,
and recovers the real-indexed filtration, including rank zero.

Selected entry points are [norm families](ArakelovGeometry/AdelicVectorBundle/NormFamily/Basic.lean),
[degrees](ArakelovGeometry/AdelicVectorBundle/Degree/Basic.lean),
[slopes](ArakelovGeometry/AdelicVectorBundle/Slope/Basic.lean),
[Hermitian filtrations](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Basic.lean),
[general filtrations](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/General/Basic.lean),
[minima](ArakelovGeometry/AdelicVectorBundle/Minima/Basic.lean), and
[Minkowski properties](ArakelovGeometry/AdelicVectorBundle/Minkowski/Basic.lean).
Arithmetic constructions are in [NumberTheory](ArakelovGeometry/NumberTheory/),
with lattice counting and polar-body arguments in
[GeometryOfNumbers](ArakelovGeometry/GeometryOfNumbers/).

## Chapter 5: filtrations and tensor slopes

| Topic | Implemented material | Scope relative to the book |
| --- | --- | --- |
| Real filtrations | Common adapted bases for two filtrations, intrinsic expectation and pairing, centering, fixed-basis variation, tensor convolution, and quotient filtrations. | Finite-family weighted-span formulas are included; the graded tensor constructions are binary. General finite-family graded refinement is not included. |
| Geometric instability | Plücker and quotient determinant constructions, polynomial invariant separation, degeneration over a discrete valuation ring, and negative filtrations over the original characteristic-zero field. | The instability implication is binary and one-way; the full finite-family Hilbert–Mumford equivalence is not asserted. |
| Optimal filtrations | Conditional finite-family existence and uniqueness of normalized optimizers, binary descent, and a binary optimizer from geometric nonsemistability. | The binary geometric existence statement is weaker than the full Theorem 5.4.3. The general variational inequality (5.13) is not formalized. |
| Graded norm and degree comparison | Contractions on completed binary grades, finite-image Harder–Narasimhan degree bounds, and an eventual affine upper bound for quotient expectation. | The construction restricts the refinement setting of Remark 5.5.6 and does not assert a contraction of the whole orthogonal direct sum. |
| Variation along Harder–Narasimhan lifts | Lifted grade filtrations, common adapted bases, quadratic energy identities, and binary quotient-slope comparisons. | Tensor compatibility of Harder–Narasimhan filtrations on all strictly smaller-rank grades remains an explicit hypothesis. The general variational inequality (5.13) is not included. |

The main directories are
[trivial-place filtrations](ArakelovGeometry/AdelicVectorBundle/Examples/Trivial/Filtration/),
[graded tensors](ArakelovGeometry/AdelicVectorBundle/Tensor/Graded/), and
[invariant theory](ArakelovGeometry/InvariantTheory/).
Chapters 5–7 are not claimed complete.

## Building

The project uses Lean **4.35.0**, mathlib **v4.35.0**, and the
[HarderNarasimhan dependency at commit `14b3090e1e16`](https://github.com/YijunYuan/HarderNarasimhan/tree/14b3090e1e169b77fe381102a1289f24c2b08a11).

```bash
lake exe cache get
lake build
```

To treat warnings as failures and recompute file hashes:

```bash
LEAN_NUM_THREADS=2 lake build --wfail --rehash ArakelovGeometry ExternalCode \
  ArakelovGeometry.AdelicVectorBundle.Tensor.HermitianInnerProduct
```

The root module [ArakelovGeometry](ArakelovGeometry.lean) publicly imports the
project's mathematical modules. Supporting algebraic results are included through
the modules that use them.

## Using the library

`NormFamily S E` keeps the vector space and the choice of norms explicit.
`NormFamily.IsAdelic` records primal measurability, dual measurability, and domination.
`AdelicVectorBundle S` packages a finite-dimensional vector space, its norm family,
and its adelicity certificate. A bundle `V` coerces to its carrier: write `x : V`,
`Submodule K V`, and `V →ₗ[K] W`.

For a bundled curve `C`, `C.AdelicVectorBundle` abbreviates `AdelicVectorBundle C.AS`.
Its base field is `C.K`. Properness and analytic base conditions remain separate
assumptions. `V.toNormFamily` exposes the norm family; `ξ.toAdelicVectorBundle`
packages a family when `[ξ.IsAdelic]` is available, preserving its carrier and norms.

Binary injective, mixed, and Hermitian tensors use the carrier `V ⊗[K] W`.
Restriction, quotient, and dual constructors retain the additional measurability
hypotheses required by their operations.

## References

- Huayi Chen and Atsushi Moriwaki,
  [*Arakelov Geometry over Adelic Curves*](https://doi.org/10.1007/978-981-15-1728-0),
  Lecture Notes in Mathematics 2258, Springer, 2020.
- Yijun Yuan, [HarderNarasimhan Lean library](https://github.com/YijunYuan/HarderNarasimhan).
