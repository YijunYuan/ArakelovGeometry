# Source adjudications for extension statements

The registered Chen–Moriwaki manuscript is version 1.2, 5 October 2019.
PDF page numbers are printed page numbers plus 16.

## Algebraic tower integration (I-0008)

`exists_equiv_algebraicExtension_algebraicExtension` formerly asserted equality
of iterated real fibre integrals for every real function. PDF 210 defines the
signed operator only where the nonnegative integral of the absolute value is
finite. Proposition 3.4.9 on PDF 211 extends the operator to integrable
functions, modulo almost everywhere equality. The proof of Theorem 3.4.12 on
PDF 213–214 explicitly proves the tower formula for nonnegative measurable
functions.

The corrected declaration retains the adelic equivalence and projection
compatibility, asserts pointwise tower equality for measurable ENNReal-valued
functions, and asserts almost everywhere equality for globally integrable real
functions. Its existing proof obligation remains open. It introduces no axiom,
and the ENNReal integrability criterion of `Algebraic.integrable_measure_iff`
is unchanged.

Evidence: the complete page transcriptions are registered under
`references/chen-moriwaki-adelic/tex/page-0210.tex` through `page-0214.tex`.
The configured `horizon check --json` passed on 2026-09-16 at 03:43:26 UTC
(3392 jobs), with the existing sorry warnings. An independent honesty review
confirmed the correction's source domain. This verifies the declaration's
elaboration, not its still-unproved mathematical result.
