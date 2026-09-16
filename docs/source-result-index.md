# Source-result coverage: sections 3.3–3.4

Every numbered result and all five clauses of Theorem 3.3.7 are indexed below.
The opening constructions and proof dependencies are included explicitly.
PDF pages refer to the registered 2019 manuscript; printed pages are 16 lower.
Each blueprint node contains the mathematical statement, proof, source anchors,
dependency edges and exact project attachments or an audited imported boundary.
The index is a coverage map; proof status is checked separately by
`scripts/blueprint_coverage.py --require-closed`.

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

The source corrections are documented in [source-corrections.md](source-corrections.md):
the signed algebraic tower domain, the infinite-fibre ENNReal integrability test,
finite descent in the tower proof, and the distinction between cylinder and Borel
sigma algebras for uncountable inverse systems. Every correction preserves the
intended construction and is justified against the cited source pages.
