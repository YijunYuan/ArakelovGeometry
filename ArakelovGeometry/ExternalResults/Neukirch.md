# Theorem 4.2 

Let \(K\) be a field which is complete with respect to an archimedean valuation \(|\cdot|\). Then there is an isomorphism \(\sigma\) from \(K\) onto \(\mathbb{R}\) or \(\mathbb{C}\) satisfying

\[
|a|=|\sigma a|^s
\qquad\text{for all }a\in K,
\]

for some fixed \(s\in(0,1]\).

## Proof

We may assume without loss of generality that \(\mathbb{R}\subseteq K\) and that the valuation \(|\cdot|\) of \(K\) is an extension of the usual absolute value of \(\mathbb{R}\). In fact, replacing \(|\cdot|\) by \(|\cdot|^{s^{-1}}\) for a suitable \(s>0\), we may assume by (3.7) that the restriction of \(|\cdot|\) to \(\mathbb{Q}\) is equal to the usual absolute value. Then, taking the closure \(\widehat{\mathbb{Q}}\) in \(K\), we find that \(\widehat{\mathbb{Q}}\) is complete with respect to the restriction of \(|\cdot|\) to \(\mathbb{Q}\); in other words, it is a completion of \((\mathbb{Q},|\cdot|)\). In view of the uniqueness of completions, there is an isomorphism

\[
\sigma:\mathbb{R}\longrightarrow\widehat{\mathbb{Q}}
\]

such that

\[
|a|=|\sigma a|,
\]

as required.

In order to prove that \(K=\mathbb{R}\) or \(K=\mathbb{C}\), we show that each \(\xi\in K\) satisfies a quadratic equation over \(\mathbb{R}\). For this, consider the continuous function

\[
f:\mathbb{C}\longrightarrow\mathbb{R}
\]

defined by

\[
f(z)=\left|\xi^2-(z+\overline z)\xi+z\overline z\right|.
\]

Note here that

\[
z+\overline z,\;z\overline z\in\mathbb{R}\subseteq K.
\]

Since

\[
\lim_{z\to\infty}f(z)=\infty,
\]

\(f(z)\) has a minimum \(m\). The set

\[
S=\{z\in\mathbb{C}\mid f(z)=m\}
\]

is therefore nonempty, bounded, and closed, and there is a \(z_0\in S\) such that

\[
|z_0|\geq |z|
\qquad\text{for all }z\in S.
\]

It suffices to show that \(m=0\), because then one has the equation

\[
\xi^2-(z_0+\overline{z_0})\xi+z_0\overline{z_0}=0.
\]

Assume \(m>0\). Consider the real polynomial

\[
g(x)=x^2-(z_0+\overline{z_0})x+z_0\overline{z_0}+\varepsilon,
\]

where \(0<\varepsilon<m\), with the roots \(z_1,\overline{z_1}\in\mathbb{C}\). We have

\[
z_1\overline{z_1}=z_0\overline{z_0}+\varepsilon,
\]

hence

\[
|z_1|>|z_0|
\]

and thus

\[
f(z_1)>m.
\]

For fixed \(n\in\mathbb{N}\), consider on the other hand the real polynomial

\[
G(x)
=
[g(x)-\varepsilon]^n-(-\varepsilon)^n
=
\prod_{i=1}^{2n}(x-\alpha_i)
=
\prod_{i=1}^{2n}(x-\overline{\alpha_i}),
\]

with roots \(\alpha_1,\ldots,\alpha_{2n}\in\mathbb{C}\). It follows that \(G(z_1)=0\); say, \(z_1=\alpha_1\). We may substitute \(\xi\in K\) into the polynomial

\[
G(x)^2
=
\prod_{i=1}^{2n}
\left(
x^2-(\alpha_i+\overline{\alpha_i})x
+\alpha_i\overline{\alpha_i}
\right)
\]

and get

\[
|G(\xi)|^2
=
\prod_{i=1}^{2n}f(\alpha_i)
\geq
f(\alpha_1)m^{2n-1}.
\]

From this and the inequality

\[
\begin{aligned}
|G(\xi)|
&\leq
\left|
\xi^2-(z_0+\overline{z_0})\xi+z_0\overline{z_0}
\right|^n
+
|-\varepsilon|^n \\
&=
f(z_0)^n+\varepsilon^n \\
&=
m^n+\varepsilon^n,
\end{aligned}
\]

it follows that

\[
f(\alpha_1)m^{2n-1}
\leq
(m^n+\varepsilon^n)^2,
\]

and hence

\[
\frac{f(\alpha_1)}{m}
\leq
\left(
1+\left(\frac{\varepsilon}{m}\right)^n
\right)^2.
\]

For \(n\to\infty\), we have

\[
f(\alpha_1)\leq m,
\]

which contradicts the inequality \(f(\alpha_1)>m\) proved before. Therefore \(m=0\), completing the proof. \(\square\)
