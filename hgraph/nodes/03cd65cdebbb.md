---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
generated: blueprint
label: def:completion-tensor-map
lean_status: lean_ok
order: 39
ref: chen-moriwaki-adelic:page-0194,chen-moriwaki-adelic:page-0205
title: Canonical maps to completed extensions
type: tex
updated: '2026-10-02T11:55:12'
---
Let $L/K$ be a field extension and $w$ an absolute value on $L$
extending $v$ on $K$. The canonical maps $K\to K_v\to L_w$ and
$K\to L\to L_w$ agree. Thus $L_w$ is a $K_v$-algebra and there is a
canonical $K_v$-algebra homomorphism
\[
 q_w:K_v\otimes_KL\longrightarrow L_w,\qquad
 q_w(a\otimes b)=a\,b.
\]
In particular $q_w(1\otimes b)$ is the image of $b$ in $L_w$.
The maps $q_w$ together define
$q:K_v\otimes_KL\to\prod_{w|_K=v}L_w$.