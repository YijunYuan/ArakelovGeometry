---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AlgHom.natCard_comp_eq_finSepDegree
docstring: Extensions of an embedding are counted by the relative separable degree.
file: ArakelovGeometry/ExternalResults/AbsoluteValueLocal.lean
generated: lean
lean_status: lean_ok
title: AlgHom.natCard_comp_eq_finSepDegree
type: lean
updated: '2026-10-02T11:55:12'
---
theorem _root_.AlgHom.natCard_comp_eq_finSepDegree {K F L C : Type*}
    [Field K] [Field F] [Field L] [Field C]
    [Algebra K F] [Algebra K L] [Algebra K C] [Algebra F L]
    [IsScalarTower K F L] [FiniteDimensional F L] [IsAlgClosed C]
    (τ : F →ₐ[K] C) :
    Nat.card {σ : L →ₐ[K] C // σ.comp (IsScalarTower.toAlgHom K F L) = τ} =
      Field.finSepDegree F L := by
  let : Algebra F C := τ.toRingHom.toAlgebra
  have : IsScalarTower K F C := IsScalarTower.of_algebraMap_eq (fun a ↦ (τ.commutes a).symm)
  let e : {σ : L →ₐ[K] C // σ.comp (IsScalarTower.toAlgHom K F L) = τ} ≃
      (L →ₐ[F] C) := {
    toFun σ := {
      σ.val.toRingHom with
      commutes' a := congrArg (fun z : F →ₐ[K] C ↦ z a) σ.property }
    invFun σ := ⟨σ.restrictScalars K, by ext a; exact σ.commutes a⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (Field.finSepDegree_eq_of_isAlgClosed F L C).symm