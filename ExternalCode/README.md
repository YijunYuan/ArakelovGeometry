# Supporting algebraic results

This directory contains selected algebraic results used in the partial
formalization of Chen–Moriwaki's *Arakelov Geometry over Adelic Curves*.
The project also uses mathlib and the HarderNarasimhan library.

- `Stacks/` supplies specialization over a discrete valuation ring for the
  binary instability construction.
- `EtingofRepresentationTheory/` supplies centralizer, semisimplicity, and
  general-linear tensor-map span results for fixed tensor degrees.

Modules import the individual results they use. The specialization theorem
retains its finite-type scheme hypotheses. The representation results concern
fixed tensor degrees and their subquotients; they do not assert general linear
reductivity or semisimplicity of an infinite group's group algebra.

Upstream copyright, license, and attribution notices are retained. The subtree
readmes identify the original repositories and revisions. Documentation of a
specialized result states its hypotheses and any omitted generality.
