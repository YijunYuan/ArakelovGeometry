# Arakelov Geometry over Adelic Curves

[![CI](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/YijunYuan/ArakelovGeometry/actions/workflows/lean_action_ci.yml)
[![Lean](https://img.shields.io/badge/Lean-4.35.0-5C2D91)](https://lean-lang.org/)
[![mathlib](https://img.shields.io/badge/mathlib-v4.35.0-5C2D91)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

The `lite` branch develops the Chen–Moriwaki foundations needed by the main theorem
of [bost.pdf](bost.pdf), *Rectangular Specht lattices and tensor semistability —
A proposed proof over adelic curves of characteristic zero* (10 November 2026).
It builds on mathlib and the
[HarderNarasimhan library](https://github.com/YijunYuan/HarderNarasimhan), reusing
results from Huayi Chen and Atsushi Moriwaki, *Arakelov Geometry over Adelic Curves*
(Lecture Notes in Mathematics 2258, Springer, 2020).

## The lite branch's consumer contract

The deliverable is a complete, lightweight foundation for the Chen–Moriwaki
inputs actually used in Bost Theorem 1.1. Coverage of the entire book is not a
completion criterion. The theorem's proper adelic curve, countable characteristic-zero
field, positive-rank Hermitian factors, and actual completed norms remain part of
the contract. In particular, a number-field-only result does not discharge this goal.

Use [todo.md](todo.md) as the demand ledger. Each specialization or weaker replacement
must explain in its Lean module/declaration docstrings and here: the source result,
the retained statement, the omitted generality, the Bost page/formula that consumes
it, and the mathematical reason it suffices. A missing bridge is an open obligation,
not an implicit hypothesis. Already checked stronger results remain available.

The local paper is named `bost.pdf` (35 pages; SHA256
`2b8639841b17e421a9a62bf32d158e1bb5529dfe37d286a0dc830e35019a4c57`);
it is the paper referred to as `bost_conjecture.pdf` in the workspace instructions.

| Input | Retained scope and status | Why this suffices for Bost |
| --- | --- | --- |
| A1: tensor duality | Actual completed-fibre duality, tensor powers of arbitrary degree, and the required permutations/regroupings; final assembly remains in progress. | Section 6, (40)–(43), uses arbitrary vectors and unbounded auxiliary degree. No separate arbitrary-block grouping theory is required. |
| A2: geometric semistability | The finite-dimensional Plücker, quotient determinant and projective interfaces are checked. The stronger SL/GL comparison already proved is retained. | Pages 26–28 need actual positive-degree homogeneous invariants and the dual quotient point. The binary main proof uses SL(E) × SL(F), without a general scheme-theoretic GIT quotient. |
| A3: common adapted bases | The arbitrary two-filtration theorem is checked and retained. | Pages 28–32 need a basis shared by a primary filtration and the chosen HN lift. Simultaneous adaptation to an arbitrary family is unnecessary. |
| A4: numerical operations | Intrinsic expectation, pairing, centering and fixed-basis real variation are checked. | Page 32, (48), uses these linear/quadratic identities; no additional geometry of the full filtration space is needed. |
| A5: tensor and quotient filtrations | The binary canonical graded decomposition, quotient maps, actual norm correspondence and naturality are checked. Existing finite-family weight formulas are retained; additional finite-family graded refinement is deferred. | Pages 28–30, (44) and (46), use two factors, collisions of total weights, and the original quotient weights. The finite-family conclusion of Theorem 1.1 is obtained by binary iteration on page 32. |
| A6: graded norm comparison | The revised target is componentwise canonical graded contractions plus the finite-image HN degree estimate below; implementation is in progress. | This replaces the whole orthogonal-direct-sum norm argument in Lemmas 7.1 and 7.2 while preserving their numerical conclusions. Componentwise contraction is not asserted to imply l2-sum contraction. |
| A7: lifting filtrations | Actual prescribed quotient lifts and their HN specialization are checked, with expectation and weighted pairing formulas. | Pages 29 and 32 need a chosen lift of the subquotient HN filtrations. A canonical or unique lift is unnecessary; the ambient HN filtration cannot replace this construction. |
| A8: instability input | Only the binary, specific tensor/determinant representation and the direction from geometric instability to a K-defined negative centered candidate are required. Cartan is checked; the full bridge remains open. | The geometrically semistable case is handled by Section 6; page 31 needs the unstable direction. Integer/rational weights suffice for this initial candidate. A full two-way real-weight HM theorem is unnecessary. |
| A9: optimal filtration | Given an actual negative candidate, construct a negative normalized minimum across all actual bases/filtrations and the needed right variation. Work remains in progress. | Pages 31–32 use existence and the HN-lift variation, not the full CM inequality (5.13) or a public uniqueness theorem. If uniqueness is used internally for A8 descent, that lemma remains an explicit obligation. |

### The A6 replacement argument

For finitely many actual completed contractions `f_i : C_i → Q` whose images span
`Q`, let `S^λ Q = Σ_i f_i(HN(C_i)^λ)`. For each fixed `λ`, the nonzero source HN
grades are semistable of slope `λ`. Their induced maps to `gr_S^λ Q` contract and
their images span. Accumulating these images gives a finite flag whose nonzero
adjacent actual quotients are surjective contraction images of those source grades.
The existing surjective slope comparison and Hermitian flag degree additivity give
`deg(Q) ≥ Σ_λ λ dim(gr_S^λ Q)`, hence `μ(Q) ≥ e(S)` for nonzero `Q`.

This proves the degree bound needed in Lemma 7.2 after identifying `S` with its
secondary-weight image filtration, using the explicitly stated smaller-rank tensor
HN induction hypothesis. The same image-flag argument applied to arbitrary target
quotients supplies Lemma 7.1. The Lean work must still establish strict-right-limit
compatibility, actual subquotient contraction, zero-image cases and that filtration
identification. This is an independently reviewed proof plan, not a claim that its
new Lean consumers have already passed. See
[graded-tensor-contraction.tex](blueprint/src/graded-tensor-contraction.tex).

Real weights remain necessary for A4–A7 and A9: the secondary weights are actual
HN slopes, and page 32 varies by a real parameter. Restricting the compactness and
variation argument to rational weights would require additional proofs. Likewise,
a minimum in one fixed basis is insufficient; A9 must minimize over the finite
collection of support types realized by all actual bases.

## Selected external results

New external transplants belong in [ExternalResults/](ExternalResults/README.md),
not in a dependency on an entire donor project. Select only a needed theorem and
its unavoidable source dependencies, first checking whether mathlib or the existing
HarderNarasimhan dependency already supplies them. Record upstream URL and fixed
commit, license, exact original statement, local changes, the Bost consumer, and
build/axiom evidence in each donor's provenance record. The Lean docstrings must
also disclose any specialization or weakening and explain its sufficiency.

The initial candidates are the small Stacks DVR-specialization closure and selected
TauCeti SL/invariant tools. They have been surveyed, not yet certified as local
dependencies. In particular, a DVR specialization does not by itself prove
Hilbert–Mumford, and an invariant-lifting theorem with an abstract linear-reductivity
hypothesis does not establish that hypothesis for the concrete binary SL group.

## Current scope

Status updated: **2026-11-11**.

The retained development covers adelic curves in Chapter 3 and a substantial part of
adelic vector bundles, degrees, slopes and number-field models in Chapter 4.
Selected prerequisites from Chapters 1 and 2 are also implemented.
**Chapter 4 is not complete.** The historical library inventory below records broader
coverage and gaps; those gaps are lite-branch tasks only when a Bost consumer needs them. A
constructed interface or an auxiliary lemma is not counted as its consumer theorem.

An adelic curve consists of a field, a measure space of places, and absolute values
whose logarithmic evaluations on nonzero field elements are integrable. Properness
is the product formula. An adelic vector bundle equips a finite-dimensional vector
space with norms on its actual completed scalar extensions, subject to domination
and measurability of both the family and its dual.

The status descriptions below refer to the hypotheses in the Lean statements.
In particular, properness, the measurable-base alternatives, usual Archimedean
normalization, finite-place ultrametricity and purity are retained where required.
The implementation distinguishes ordinary scalar extension from Hermitian scalar
extension, and distinguishes corrected source statements from false unqualified
versions. Book numbering is compared with the registered 2019 draft by mathematical
statement; numbering alone is not evidence of coverage of another edition.

## Chapter 3 — Adelic curves

| Section | Implemented content | Remaining boundary |
| --- | --- | --- |
| **3.1 Definitions and basic properties** | Adelic structures and proper curves; Archimedean locus and exponent; measurability and integrability of the exponent; finite Archimedean mass under the stated lower-bound hypothesis. | The finiteness hypothesis is explicit; arbitrary normalizations are not identified with the usual real or complex norm. |
| **3.2 Examples and elementary constructions** | Number-field curves and their product formula; the rational function field over an arbitrary field; trivial absolute-value curves; amalgamation; restriction to a subfield or measurable subset. The concrete rational-function construction over the rationals used in 3.7 is also present. | General regular projective-curve examples, polarized varieties and polarized arithmetic varieties remain unfinished. The separate product formula for the specific 3.2.5 rational-function example remains open. |
| **3.3 Finite separable extensions** | Actual extension parameter spaces, embeddings and fibres; fibre probabilities and integration; measurable evaluation functions; induced measures; logarithmic integrability and preservation of properness. | The mathematical results are implemented with their stated assumptions. |
| **3.4 General algebraic extensions** | General finite extensions, including inseparable extensions; finite intermediate fields; projective fibre probabilities; arbitrary algebraic extension measures; disintegration, base change and tower compatibility. | Signed tower formulas retain integrability and almost-everywhere equality. They are not unrestricted pointwise identities for arbitrary functions. |
| **3.5 Heights and Northcott** | Heights and their algebraic-extension compatibility; polynomial and root estimates; bounded-height-and-degree finiteness; Northcott's theorem and ascent under finite extension. | These results are proved under the source Northcott assumptions, rather than asserting Northcott for every adelic curve. |
| **3.6 Automorphism actions** | Measurability of automorphism pullbacks, attained maxima on finite fibres and measurable invariant majorants. | The algebraic-extension and measurability assumptions remain visible. |
| **3.7 Morphisms** | Morphisms on actual real L1 spaces; identity and composition laws; algebraic-extension and subfield-restriction morphisms; the rational-function example with transcendental-circle averaging. | This does not supply the separate missing product formula in 3.2.5. |

The main entry points are [AdelicCurve/Defs.lean](ArakelovGeometry/AdelicCurve/Defs.lean),
[Extension.lean](ArakelovGeometry/AdelicCurve/Extension.lean),
[Height.lean](ArakelovGeometry/AdelicCurve/Height.lean) and
[Morphism.lean](ArakelovGeometry/AdelicCurve/Morphism.lean).
Sections **3.3–3.7 are implemented**; Chapter 3 as a whole retains the example gaps
in Section 3.2. Historical source-transcription gaps are separate from Lean proof
status and are not used to claim complete coverage of every source page.

## Chapter 4 — Adelic vector bundles

### 4.1 Norm families and adelic bundles

The implementation uses the actual completed fibres and canonical restriction,
quotient, dual, tensor and determinant maps. The following results are present:

- **Algebraic operations:** restriction and separated quotient norms, operator
  duals and bidual comparisons, profile direct sums, projective/injective/mixed
  tensor products, Hermitian orthogonal tensors, exterior powers and determinants.
  Empty products and zero-dimensional cases are included where meaningful.
- **Scalar extension:** ordinary and Hermitian extensions, transitivity, dual and
  subquotient compatibility, finite-stage descent and degree transport. The full
  **4.1.5 mixed-basis identity** holds on every extended completed vector, for
  every algebraic extension, including rank zero; it is not just an identity on
  vectors coming from the base field.
- **Domination:** upper and lower envelopes, domination and strong domination,
  basis-distance criteria, stability under the operations above, algebraic
  extension and descent. **4.1.15** allows arbitrary choices of extending places
  and proves strong domination without assuming those choices are measurable.
- **Metric completion:** the local-distance pseudometric, equality almost
  everywhere and the complete metric quotient in **4.1.20** are implemented.
- **Measurability:** countable evaluation formulas for duals, quotients, local
  distances, tensors, exterior powers and determinants. Ordinary and Hermitian
  scalar extension are measurable under the common-countable-density hypothesis
  and under the corrected **countable discrete base** alternative, for arbitrary
  algebraic extensions. Number-field place spaces have the required discreteness.
- **Hermitian approximation:** local John ellipsoids, measurable real/complex
  embeddings and the measurable Hermitian approximation machinery are constructed,
  with the stated normalization and countability hypotheses.
- **Actual counterexamples:** upper/lower domination does not imply domination;
  domination alone need not control the distance to a basis family; and the
  measurable family in **4.1.23** has a genuinely nonmeasurable quotient.
- **Bundle constructors and examples:** primal and dual measurability are supplied
  by the appropriate constructors; ordinary and strong profile direct sums in
  **4.1.35** are implemented. The corrected strong-domination version of classical
  density/completion over number fields in **4.1.36**, and a counterexample to its weaker printed
  formulation, are proved.

Useful entry points include [NormFamily/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Basic.lean),
[ScalarExtension/Basis/Basic.lean](ArakelovGeometry/AdelicVectorBundle/ScalarExtension/Basis/Basic.lean),
[NormFamily/Domination/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Domination/Basic.lean),
[Measurability/Countable.lean](ArakelovGeometry/AdelicVectorBundle/Measurability/Countable.lean),
[ScalarExtension/Hermitian/Discrete.lean](ArakelovGeometry/AdelicVectorBundle/ScalarExtension/Hermitian/Discrete.lean),
[Construction/DirectSum.lean](ArakelovGeometry/AdelicVectorBundle/Construction/DirectSum.lean) and
[NormFamily/Completion/Basic.lean](ArakelovGeometry/AdelicVectorBundle/NormFamily/Completion/Basic.lean).

**Still open:** the full geometric section-supremum-norm application **4.1.18**,
and actual Lean counterexamples to the unrestricted *uncountable* discrete-base
scalar-extension claim. The countable-discrete theorem does not prove that
unrestricted claim. Some compound source clauses still require final scope and
attachment reconciliation; this section is not advertised as complete.

### 4.2 Adelic divisors

[AdelicDivisor/](ArakelovGeometry/AdelicDivisor/) implements divisors as the actual
real L1 space modulo almost-everywhere equality, their continuous linear degree,
the effective cone, principal divisors, the closure of the principal subspace and
the Banach quotient class space. Pullback and pushforward use the adelic-curve
morphism machinery. For proper curves, degree descends to divisor classes.

### 4.3 Degrees, slopes, filtrations and minima

| Topic | Implemented results | Scope and remaining work |
| --- | --- | --- |
| **Line and determinant degrees** | Vector and line degrees; scalar invariance; dual and tensor identities for lines; determinant degree; rank-zero conventions; actual isometry and algebraic-extension transport. | Full bundle statements use the appropriate measurability hypotheses. |
| **Discrepancy and exact sequences** | Determinant and majorant discrepancy bounds; subspace/quotient and flag degree comparisons; exact Hermitian degree additivity. | General norm families retain discrepancy errors. |
| **Tensor degrees** | The corrected mixed-tensor degree inequality, an actual counterexample to the unqualified equality, and exact degree additivity for orthogonal Hermitian tensors. | The printed mixed-tensor equality is not asserted. Broad local-field auxiliary clauses still need final source-scope reconciliation. |
| **Positive degree and Riemann–Roch** | Positive degree over actual rational subspaces, finiteness, exact-map and rescaling inequalities, and the positive-degree/dual Riemann–Roch comparisons. | This is distinct from the unfinished geometric curve section-count comparison. |
| **Heights of linear maps and slopes** | Actual completed operator norms, measurable/integrable height producers, maximal and minimal slopes, finiteness and attainment results, destabilizing subspaces, and injective/surjective/nonzero-map comparisons. | Extended-real values and zero-map conventions are handled explicitly; positive rank is retained where division is used. |
| **Hermitian Harder–Narasimhan theory** | An actual HN flag and factors; semistable graded pieces with strictly decreasing slopes; uniqueness; real-indexed filtration; duality and reversed annihilator flags; height-shifted functoriality; extremal slopes; weighted degrees and positive degree. The HN polygon includes its convex-hull interpretation and break points. | These are constructed filtrations, not supplied HN certificates. |
| **General HN theory and absolute invariants** | General HN constructions and comparisons, modified invariants, algebraic-closure and finite-stage descent, ordinary/geometric absolute invariants and tower results. | The relevant common-density, countable-discrete, geometric-base and normalization assumptions are stated in the individual APIs; this is not a blanket theorem for an arbitrary measurable base. |
| **Logarithmic minima and Minkowski consequences** | Successive-minimum filtrations, independent-vector descriptions, comparison with slopes, tensor/minimum bounds and consequences of ordinary, strong and absolute Minkowski properties. | A theorem conditional on a Minkowski property does not establish that property for a given curve. |
| **Arithmetic section counts, 4.3.24** | The actual number-field section-count/positive-degree comparison, with the source arithmetic constant; trace-dual lattice and codifferent constructions, the actual trace-dual maximal/minimal-slope identity, positive twists and HN transport. | This closes the arithmetic comparison. It does not close the curve comparison 4.3.23. |
| **Classical minima and transference** | Pure number-field first-minimum estimates, impurity-dependent extensions, lattice/polar counting and trace-dual ingredients. The valued Vandermonde support isometry and its real-weighted support bound are also proved. | Full all-index transference and the global factorial-family/absolute-bound consumers remain open. |
| **Strong-to-ordinary implication** | The general implication with the additional Archimedean correction, and the established Hermitian or zero-Archimedean-mass cases. | The unrestricted positive-C implication at the **same C** remains open and is not assumed. |

The [HarderNarasimhan library](https://github.com/YijunYuan/HarderNarasimhan) supplies existence and uniqueness
of the general finite HN flag and the largest slope maximizers used in the
Hermitian theory. The [adelic game](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Game/Payoff.lean)
uses the actual normed subquotients. Its first-player values equal their minimal
slopes, and the [compatibility theorems](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/General/Game.lean)
recover the original real-indexed filtration, including rank zero. The existing
measurable-base and normalization hypotheses are retained. These proofs use
Chen–Jeannin’s [Harder–Narasimhan Games](https://chenhuayi.lab.westlake.edu.cn/Recherche/HNgame.pdf),
Remark 2.5 and Theorem 3.10.

Selected entry points are [Degree/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Basic.lean),
[Degree/Positive/RiemannRoch.lean](ArakelovGeometry/AdelicVectorBundle/Degree/Positive/RiemannRoch.lean),
[Slope/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Slope/Basic.lean),
[HarderNarasimhan/Hermitian/Basic.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/Hermitian/Basic.lean),
[HarderNarasimhan/General/Basic.lean](ArakelovGeometry/AdelicVectorBundle/HarderNarasimhan/General/Basic.lean),
[Minima/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Minima/Basic.lean),
[Minkowski/Basic.lean](ArakelovGeometry/AdelicVectorBundle/Minkowski/Basic.lean) and
[Ultrametric/VandermondeSupport.lean](ArakelovGeometry/Analysis/Ultrametric/VandermondeSupport.lean).
The arithmetic implementations are in [NumberTheory/](ArakelovGeometry/NumberTheory/),
with local counting and polar-body arguments in [GeometryOfNumbers/](ArakelovGeometry/GeometryOfNumbers/).

### 4.4 Number-field models

The number-field development constructs actual local and global unit-ball modules,
localization and completed lattice gauges, spanning/coherence criteria, finite
generation, lattice-induced adelic bundles and determinant degree/covolume
comparisons. It also develops purity, impurity, local gauge comparison, global
integrability and the field-dependent lattice/minimum comparison route.

The implementation preserves distinctions between a dominated family, a coherent
family, a pure family and a family induced by a full lattice. In particular,
finite generation under domination is not silently strengthened to an unproved
coherence assertion. Raw local-degree masses and degree-normalized masses are
also kept distinct. Most model-theoretic producers are implemented; the README
does not certify every compound source clause of 4.4 as independently complete.

## Implemented prerequisites from Chapters 1 and 2

These are selected prerequisites used by Chapters 3–4, **not complete
formalizations of Chapters 1 and 2**.

| Chapter | Implemented material | Entry points / boundary |
| --- | --- | --- |
| **1: local normed linear algebra** | Finite-dimensional coordinate bounds and near-orthogonal bases; operator duals, restrictions and separated quotients; projective/injective tensor norms and their maps; exterior/determinant norms and pairings; local exact-sequence comparisons; ordinary and Hermitian scalar extension; real/complex norm comparison and polarization; direct-sum profiles and polar duality; John ellipsoid and measurable-ellipsoid ingredients. | [Analysis/](ArakelovGeometry/Analysis/) and the local parts of [AdelicVectorBundle/](ArakelovGeometry/AdelicVectorBundle/). Statements retain their complete-field, ultrametric or usual-Archimedean hypotheses. A few broader local source clauses and assembled estimates still need reconciliation. |
| **2: analytic points and geometric fibres** | Intrinsic valued points of schemes, their topology, scalar-extension maps and surjectivity; completed residue fields; actual fibres of module sheaves and line bundles; affine tensor base change, completed section values and compatible pullback constructions. | [AlgebraicGeometry/](ArakelovGeometry/AlgebraicGeometry/). Full analytic compactness, geometric section supremum norms and the source 2.1.19 application remain unfinished. |
| **2: global-section prerequisites** | Flat tensor descent over finite covers, the canonical tensor comparison on section sheaves, and the relative affine section equivalence with its pure-tensor formula. | [BaseChange/GlobalSections.lean](ArakelovGeometry/AlgebraicGeometry/BaseChange/GlobalSections.lean). Transport to arbitrary scheme fibre products/affine opens and the final global base-change equivalence remain open. |

## TODO

1. **Geometric supremum norms (2.1.19 and 4.1.18).** Finish the actual completed-section
   norm identity, invariance of the section supremum under base change, global H0
   base change, projective finite-dimensionality, proper analytic compactness,
   boundedness of continuous metrics and reducedness-based detection of sections.
   Existing point/fibre or affine lemmas do not discharge this whole chain.
2. **Curve comparison 4.3.23.** Relate the actual dimension of global sections to
   positive degree with the stated genus error, including model/HN compatibility
   and the full constant-field scaling. The number-field proof of 4.3.24 is separate.
3. **Uncountable discrete scalar-extension counterexamples.** Implement the actual
   quadratic-extension witnesses for the specified evaluation-generated sigma
   algebra, including the proper probability and zero-measure variants. The
   4.1.23 quotient counterexample is already proved and is a different construction.
4. **Absolute classical bounds in 4.3.74.** Complete the all-rank Hermitian harmonic
   estimate, the corrected ordinary absolute number-field bound, and the
   characteristic-zero function-field absolute level-zero theorem. For the
   ordinary number-field route, construct the actual factorial norm family and
   prove its degree and all absolute minima; the new Vandermonde lemma is only
   its local input. Retain the corrected constants and purity/normalization scopes.
5. **All-index transference and last minima.** Complete the actual Euclidean and
   number-field transference consumers and their impurity corrections. First-minimum
   bounds and trace-dual slope identities alone do not prove these statements.
6. **General same-C problem in 4.3.81.** Leave the unrestricted positive-C
   strong-to-ordinary implication explicitly open. Do not substitute a theorem
   with a larger constant or a restricted Hermitian hypothesis for it.
7. **Finish source-clause reconciliation.** Match remaining broad local determinant,
   tensor and scalar-extension clauses and small assembled corollaries to their
   exact exports. Preserve counterexamples and corrected hypotheses instead of
   marking an incorrect printed assertion proved.
8. **Chapter 3 examples and broader coverage.** Finish the general projective-curve,
   polarized-variety and polarized-arithmetic-variety examples and the outstanding
   3.2.5 product formula. Extend the selected Chapter 1–2 prerequisites as needed.
   Chapters 5–7 are not claimed complete by this snapshot.

## Building and verification

The project is pinned to Lean **4.35.0** and mathlib **v4.35.0** by
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

The [HarderNarasimhan dependency](https://github.com/YijunYuan/HarderNarasimhan) is pinned to commit
[`14b3090e1e16`](https://github.com/YijunYuan/HarderNarasimhan/tree/14b3090e1e169b77fe381102a1289f24c2b08a11)
in the Lake configuration and manifest. It uses the same Lean and mathlib versions.

```bash
lake exe cache get
lake build
```

The stricter publication check treats every warning as a failure and recomputes
file hashes rather than trusting cached hash files:

```bash
LEAN_NUM_THREADS=2 lake build --wfail --rehash
```

[ArakelovGeometry.lean](ArakelovGeometry.lean) publicly imports every shipped Lean
module, so the default build checks all 749 source files. Its imports are kept
when the dependency graph is minimized. Unfinished geometric drafts remain
outside this snapshot; the implemented results retain the boundaries described
above.

## Repository layout

The modules are grouped by mathematical objects and constructions. Basic normed
linear algebra, measure theory and field theory sit below the adelic developments;
number-field models and arithmetic applications are grouped in `NumberTheory`.

| Directory | Content |
| --- | --- |
| [AdelicCurve/](ArakelovGeometry/AdelicCurve/) | Adelic structures, examples, extensions, heights and morphisms. |
| [AdelicStructure/](ArakelovGeometry/AdelicStructure/) | Rational normalization and comparison of rational place classes. |
| [AdelicVectorBundle/](ArakelovGeometry/AdelicVectorBundle/) | Norm families and bundles, their operations, degrees, slopes, filtrations and minima; see the groups below. |
| [AdelicDivisor/](ArakelovGeometry/AdelicDivisor/) | Integrable divisors and their class spaces. |
| [Analysis/](ArakelovGeometry/Analysis/) and [LinearAlgebra/](ArakelovGeometry/LinearAlgebra/) | Absolute values and completions, local norm comparisons, tensor and exterior constructions, and finite-dimensional algebra. |
| [MeasureTheory/](ArakelovGeometry/MeasureTheory/) and [FieldTheory/](ArakelovGeometry/FieldTheory/) | Measure and integration lemmas, monotone-class arguments, and algebraic-tower prerequisites. |
| [Order/HarderNarasimhan/](ArakelovGeometry/Order/HarderNarasimhan/) | Generic game adapters for slope maximizers and finite semistable flags. |
| [AlgebraicGeometry/](ArakelovGeometry/AlgebraicGeometry/) | Valued points, completed fibres, base change and locally free sheaves. |
| [NumberTheory/NumberField/](ArakelovGeometry/NumberTheory/NumberField/) | Normalized adelic curves, local arithmetic, lattice models, covolumes, trace duality, minima and arithmetic Riemann–Roch. |
| [GeometryOfNumbers/](ArakelovGeometry/GeometryOfNumbers/) | Convex bodies, lattice geometry, polar duality, normalized measures and counting. |

The main bundle hierarchy is:

```text
AdelicVectorBundle/
  Basic.lean                    adelic bundles and the IsAdelic certificate
  NormFamily/                   fibre norms, domination, Hermitian properties, completion
  Construction/                 bundle constructors and tensor constructions
  Measurability/                evaluation criteria and measurable operations
  Subquotient/                   restrictions, quotients and isometries
  Dual/, DirectSum/, Tensor/    operations on norm families
  Exterior/, Determinant/       exterior and determinant norms
  ScalarExtension/              ordinary and Hermitian extensions, descent and towers
  Degree/                       degrees, discrepancy, flags and positive degree
  Slope/                        slope bounds and semistability
  HarderNarasimhan/              general and Hermitian filtrations and descent
  Minima/, Minkowski/            logarithmic minima and Minkowski properties
  AbsoluteInvariants/           algebraic-extension invariants
  Examples/                     constructions and counterexamples
```

`NormFamily` keeps the choice of norms explicit, so comparison theorems can use
several metrics on the same completed vector space. `NormFamily.IsAdelic` records
primal measurability, dual measurability and domination. `AdelicVectorBundle`
bundles these proofs with the norm family. Restriction, quotient and dual
constructors retain their precise additional measurability hypotheses.

Supporting results are placed with their mathematical subject and use mathlib's
existing constructions wherever applicable. Specialized files import the modules
they use; [ArakelovGeometry.lean](ArakelovGeometry.lean) publicly imports every
project source for complete library exports and build coverage.

## References

- Huayi Chen and Atsushi Moriwaki,
  [*Arakelov Geometry over Adelic Curves*](https://chenhuayi.lab.westlake.edu.cn/Recherche/adelic_curve.pdf),
  Lecture Notes in Mathematics 2258, Springer, 2020.
- Huayi Chen and Marion Jeannin, [*Harder–Narasimhan Games*](https://chenhuayi.lab.westlake.edu.cn/Recherche/HNgame.pdf).
- Yijun Yuan, [HarderNarasimhan Lean library](https://github.com/YijunYuan/HarderNarasimhan), commit `14b3090e1e16`.
- Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999.
- Keith Conrad, *Ostrowski for number fields*.
