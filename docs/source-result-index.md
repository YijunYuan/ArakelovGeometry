# Source-result coverage: sections 3.3–3.7

Every numbered result and all five clauses of Theorem 3.3.7 are indexed below.
PDF page numbers are sixteen greater than printed page numbers. The JSON index
is the machine-readable source for this table; proof status is checked separately
by `scripts/blueprint_coverage.py`.

| Source result | PDF pages | Mathematical claim | Blueprint nodes |
| --- | --- | --- | --- |
| 3.3.setup | 194, 195 | Extension parameters, completed local factorization, local-degree probability weights and the finite fibre operator. | `def:extension-parameters`, `lem:local-factorization`, `lem:finite-extension-fibres`, `lem:fibre-normalization`, `def:weighted-fibre-integral`, `lem:fibre-one`, `lem:fibre-additivity`, `lem:fibre-homogeneity` |
| 3.3.1 | 195 | Multiplication by an arbitrary base function commutes with fibre integration. | `prop:fibre-base-multiplication` |
| 3.3.2 | 195, 196 | Restriction along a finite separable tower preserves the fibre integral of pullbacks. | `prop:fibre-restriction` |
| 3.3.3 | 196 | Integration retracts arbitrary real base pullback. | `cor:fibre-pullback` |
| 3.3.4 | 196, 198, 199, 200 | Measurability of finite separable real fibre integration, including the bounded-generator and functional closure proof steps. | `lem:measurable-evaluation-average`, `lem:bounded-evaluation-generators`, `lem:functional-monotone-class`, `lem:sequential-functional-monotone-class`, `thm:measurable-fibre-integral`, `lem:bounded-fibre-measurability`, `cor:measurable-fibre-integral-by-truncation` |
| 3.3.5 | 196, 197, 198 | Power sums recover the largest absolute value; separable orbit maxima are measurable. | `lem:power-sum-radius`, `lem:separable-orbit-cardinality`, `lem:orbit-power-sums`, `lem:orbit-maximum` |
| 3.3.6 | 200 | Induced measure defined by fibre probabilities. | `def:separable-induced-measure` |
| 3.3.7(1) | 201 | Countable additivity and nonnegative disintegration. | `def:separable-induced-measure`, `thm:separable-lintegral` |
| 3.3.7(2) | 201, 202 | Integrability criterion and signed disintegration. | `thm:separable-integrability`, `thm:separable-integral` |
| 3.3.7(3) | 201, 202 | Projection pushforward, pullback integrability and integral identities. | `prop:separable-pushforward`, `lem:separable-pullback-integrability`, `cor:separable-pullback-integral` |
| 3.3.7(4) | 201, 202, 203 | Logarithmic integrability makes the separable scalar extension an adelic curve. | `lem:algebraic-root-bound`, `lem:log-root-bound`, `thm:separable-log-integrable`, `def:separable-extension` |
| 3.3.7(5) | 201, 203, 204 | Norm-integral formula and preservation of properness. | `lem:fibre-log-norm`, `prop:separable-norm-integral`, `prop:separable-proper` |
| 3.4.setup | 204, 205 | Finite separable part and unique purely inseparable extension of absolute values. | `lem:finite-separable-part`, `lem:inseparable-power`, `lem:inseparable-absolute-value`, `lem:inseparable-extension-unique`, `lem:inseparable-log` |
| 3.4.1 | 205 | Arbitrary finite scalar extension, its inherited measure and fibre operator. | `def:finite-parameters`, `def:finite-measure`, `def:finite-extension`, `def:finite-fibre-integral`, `lem:finite-log-integrable`, `prop:finite-proper`, `lem:finite-parameter-identification`, `lem:finite-measurable-space` |
| 3.4.2 | 205, 206 | The completed separable part is the separable closure of the completed base. | `lem:completion-separable-closure` |
| 3.4.3 | 206 | Finite fibre weights expressed by local and global separable degrees. | `lem:finite-separable-weight`, `rem:completion-factorization-indices` |
| 3.4.4 | 206, 207 | Arbitrary finite tower equivalence, operator compatibility and measure transport. | `lem:finite-tower-parameters`, `lem:finite-tower-weights`, `lem:finite-fibre-tower`, `prop:finite-tower`, `rem:finite-tower-evaluation-domain` |
| 3.4.5 | 208 | Surjective finite-stage restriction, inverse-limit fibres and projective measurable spaces. | `prop:algebraic-restriction-surjective`, `lem:compact-algebraic-fibre`, `def:projective-measurable` |
| 3.4.6 | 208, 209 | Cylinder algebra, normalized positive linear functional and induced fibre probability with prescribed finite marginals. | `lem:cylinder-algebra`, `lem:cylinder-constants`, `lem:cylinder-integral-independent`, `lem:cylinder-functional`, `lem:cylinder-premeasure`, `lem:cylinder-outer-measure`, `def:algebraic-fibre-probability`, `prop:algebraic-fibre-marginals`, `rem:cylinder-borel-distinction` |
| 3.4.7 | 209 | Global cylinder linear operator and base retraction. | `lem:global-cylinder-functional`, `lem:algebraic-integral-pullback` |
| 3.4.8 | 210 | Measurable nonnegative fibre integration and the induced algebraic-extension measure. | `lem:algebraic-fibre-measurable`, `prop:algebraic-kernel-measurable`, `def:algebraic-measure`, `prop:algebraic-lintegral` |
| 3.4.9 | 210, 211 | Nonnegative integrability criterion, signed disintegration, continuous linear L1 operator and base pullback. | `prop:algebraic-integrability`, `prop:algebraic-signed-disintegration`, `cor:algebraic-L1-operator`, `prop:algebraic-base-pullback` |
| 3.4.10 | 211 | Measurable integrable logarithmic evaluations and preservation of properness. | `prop:algebraic-log-integrable`, `prop:algebraic-proper` |
| 3.4.11 | 212 | The algebraic scalar-extension adelic curve. | `def:algebraic-extension` |
| 3.4.12 | 212, 213, 214 | Canonical algebraic tower equivalence and nonnegative/signed-compatible integration, using faithful domain and finite-descent corrections. | `lem:finite-descent-separable`, `lem:descended-base-change`, `lem:algebraic-tower-cylinders`, `thm:algebraic-tower-lintegral`, `lem:algebraic-tower-equivalence`, `lem:algebraic-tower-signed`, `thm:algebraic-tower`, `rem:algebraic-tower-source-repair`, `rem:signed-tower-domain` |
| 3.4.13 | 214, 215 | The projective sigma algebra is generated by the base projection and all evaluations. | `prop:projective-measurable-equality` |
| 3.5.1 | 215, 216 | Height integral on the algebraic closure, integrability, invariance under nonzero scaling, and descent to projective space. | `def:local-height`, `lem:local-height-integrable`, `def:tuple-height`, `lem:height-scaling`, `prop:height-scalar-invariant`, `def:projective-height`, `def:absolute-projective-height` |
| 3.5.2 | 216 | Base-field Northcott property for every nonnegative real bound, with compatibility of base and algebraic-closure heights. | `def:northcott-property` |
| 3.5.3 | 216, 217, 218 | Finiteness of projective points of bounded height and field-of-definition degree, for every dimension and real bounds. | `lem:projective-normalized-representatives`, `def:projective-field-of-definition`, `lem:projective-chart-height-degree`, `lem:finite-projective-representatives`, `thm:northcott` |
| 3.5.4 | 216 | Conjugate-height equality for finite normal extensions; proved more generally via finite embedding measure marginals, including inseparable extensions. | `lem:height-finite-embedding`, `lem:height-conjugate` |
| 3.5.polynomial | 216 | Height of the coefficient vector of a nonzero polynomial. | `def:polynomial-height`, `lem:polynomial-height-linear`, `lem:polynomial-height-monic-coefficient` |
| 3.5.5 | 217 | Polynomial product height bound with archimedean mass; the unrestricted proof route uses the sharper finite integral of the archimedean exponent. | `def:height-archimedean-constant`, `lem:height-archimedean-extension`, `lem:height-finite-sum-bound`, `lem:polynomial-local-product-bound`, `lem:polynomial-height-product-sharp`, `lem:polynomial-height-product`, `rem:northcott-archimedean-error` |
| 3.5.6 | 217 | Finiteness of algebraic elements of bounded affine height and simple-extension degree; proved for every algebraic extension, including inseparable elements and arbitrary real bounds. | `lem:minimal-polynomial-root-conjugacy`, `lem:polynomial-height-split-bound`, `lem:polynomial-height-base-extension`, `lem:minimal-polynomial-height`, `lem:northcott-bounded-coefficient-roots`, `lem:northcott-algebraic-elements` |
| 3.5.7 | 218 | Preservation of the Northcott property by every finite field extension, for both the finite and algebraic extension constructions. | `cor:northcott-finite-extension` |
| 3.6.1 | 218 | Pullback by every base-field automorphism of an algebraic extension is measurable for the sigma algebra of the extended adelic structure, with the source evaluation convention. | `def:automorphism-pullback`, `prop:automorphism-measurable` |
| 3.6.2 | 218, 219 | For every finite extension and every measurable real function on its intrinsic parameter space, the attained maximum on each fibre is measurable on the base; the proof uses positive fibre probabilities instead of normal closure. | `lem:measurable-orbit-maximum`, `def:fibre-maximum`, `lem:finite-fibre-indicator-positive`, `lem:finite-projection-measurable-image`, `prop:fibre-maximum-measurable` |
| 3.7.1 | 219 | The source triple of a field map, a measurable measure-preserving base map compatible with absolute values, and a real-linear L1 disintegration preserving integrals and retracting pullback. | `def:adelic-morphism` |
| 3.7.composition | 219 | Identity and composition with contravariant field maps, covariant base maps and fibre operators, including every category law. | `lem:adelic-morphism-id`, `lem:adelic-morphism-comp`, `thm:adelic-curve-category` |
| 3.7.2(1) | 220 | The canonical morphism from every algebraic extension, using the existing quotient L1 fibre-integration operator. | `ex:algebraic-extension-morphism` |
| 3.7.2(2) | 220 | The morphism from an adelic curve to its restriction to a subfield, with identity base map and L1 operator. | `ex:subfield-restriction-morphism` |
| 3.7.2(3) | 188, 189, 220 | The concrete rational-function morphism: inclusion of Q, collapse of transcendental-circle parameters to the infinite place, and identity on finite places plus circle averaging on L1; horizontal places follow the cited affine-line construction. | `lem:probability-collapse`, `ex:adelic-morphism-rational-function` |

Section 3.5 uses finite embedding compatibility from Section 3.4; it does not
require Sections 3.6 or 3.7. Its polynomial proof retains the finite integrated
archimedean exponent, as explained in [source-corrections.md](source-corrections.md).

The examples mentioned after Definition 3.5.2 refer to Section 3.2 and remain
outside this task. Remark 3.5.8 points forward to Chapter 6 and adds no
prerequisite to these results. Earlier missing source transcriptions are tracked
in Horizon issue I-0001; Sections 3.5–3.6 pages 215–219 are registered.

Section 3.6 retains algebraicity in Proposition 3.6.1 and finiteness alone in
Proposition 3.6.2. The latter uses positive fibre probabilities and measurable
projection images in place of the source normal-closure argument. Both statements
use the projective sigma algebra of the existing extension adelic structure.

Section 3.7 includes all clauses of Definition 3.7.1, its category statement,
and all three examples. Example 3.7.2(3) uses the concrete Section 3.2.5
adelic structure; the separate product formula for that structure is not
part of this coverage claim. Its horizontal-place correction is documented
in [source-corrections.md](source-corrections.md).
