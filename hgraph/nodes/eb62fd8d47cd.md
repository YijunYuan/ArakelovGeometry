---
author: sync
content_type: definition
created: '2026-10-02T11:55:13'
generated: blueprint
label: def:algebraic-tower-probability
lean_status: lean_ok
order: 279
ref: chen-moriwaki-adelic:page-0213,chen-moriwaki-adelic:page-0214
title: The iterated fibre probability
type: tex
updated: '2026-10-02T11:55:13'
---
For $K\subseteq B\subseteq N$ algebraic, let $e$ identify the iterated
parameter space with $\Omega_N$. For each $\omega\in\Omega_K$ the formula
\[
 Q_\omega(A)=\int_{\Omega_B}
       (e_*\mu_{N,x})(A)\,d\mu_{B,\omega}(x)
       \qquad(A\in\mathcal A_N)
\]
defines a probability measure. The family $x\mapsto e_*\mu_{N,x}$ is
measurable, and every measurable $f:\Omega_N\to[0,\infty]$ satisfies
\[
 \int f\,dQ_\omega
 =I^+_{B/K}\bigl(I^+_{N/B}(f\circ e)\bigr)(\omega).
\]