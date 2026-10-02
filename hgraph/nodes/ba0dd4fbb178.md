---
author: sync
content_type: theorem
created: '2026-10-02T12:19:19'
decl: ArakelovGeometry.AdelicStructure.polynomialLocalHeight_X_sub_C
file: ArakelovGeometry/AdelicCurve/Height/Polynomial.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.polynomialLocalHeight_X_sub_C
type: lean
updated: '2026-10-02T12:19:19'
---
theorem polynomialLocalHeight_X_sub_C (a : K) (ω : AS.Ω) :
    AS.polynomialLocalHeight (X - C a) ω = max 1 (AS.ϕ ω a) := by
  rw [AS.polynomialLocalHeight_eq_localHeight (X - C a) (n := 1) (by simp)]
  have he : (fun i : Fin 2 ↦ (X - C a).coeff i) = ![-a, 1] := by
    ext i
    fin_cases i <;> simp
  rw [he, AS.localHeight_pair]
  simp [max_comm]