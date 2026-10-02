---
author: sync
content_type: theorem
created: '2026-10-02T12:11:38'
decl: ArakelovGeometry.AdelicStructure.localHeight_pair
file: ArakelovGeometry/AdelicCurve/Height/Affine.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.localHeight_pair
type: lean
updated: '2026-10-02T12:11:38'
---
theorem localHeight_pair (a b : K) (ω : AS.Ω) :
    AS.localHeight ![a, b] ω = max (AS.ϕ ω a) (AS.ϕ ω b) := by
  simp [localHeight, Finset.univ_fin2, Finset.sup'_insert, Finset.sup'_singleton]