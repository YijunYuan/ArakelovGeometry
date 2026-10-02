---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.card_embeddings_eq_localDegree
docstring: The number of embeddings inducing a fixed absolute value is its local degree.
file: ArakelovGeometry/ExternalResults/AbsoluteValueLocal.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.card_embeddings_eq_localDegree
type: lean
updated: '2026-10-02T11:55:12'
---
theorem card_embeddings_eq_localDegree {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion) :
    Nat.card {σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion //
      u.pullback σ.toRingHom = w} = w.localDegree K := by
  have : Algebra.IsSeparable (w.restriction K).Completion w.Completion := isSeparable_completion w
  simpa only [Field.finSepDegree_eq_finrank_of_isSeparable, localDegree] using
    card_embeddings_eq_localFinSepDegree w u hu