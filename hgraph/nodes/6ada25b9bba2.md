---
author: sync
content_type: theorem
created: '2026-10-02T11:55:12'
decl: AbsoluteValue.card_embeddings_eq_localDegree_of_isAlgClosed
docstring: 'The number of embeddings inducing a fixed place is independent of the

  algebraically closed ambient field.'
file: ArakelovGeometry/ExternalResults/AbsoluteValueLocal.lean
generated: lean
lean_status: lean_ok
title: AbsoluteValue.card_embeddings_eq_localDegree_of_isAlgClosed
type: lean
updated: '2026-10-02T11:55:12'
---
theorem card_embeddings_eq_localDegree_of_isAlgClosed {K L C₀ : Type*}
    [Field K] [Field L] [Field C₀] [Algebra K L] [Algebra K C₀]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed C₀]
    (w : AbsoluteValue L ℝ) (u₀ : AbsoluteValue C₀ ℝ)
    (hu₀ : u₀.restriction K = w.restriction K) :
    Nat.card {σ : L →ₐ[K] C₀ // u₀.pullback σ.toRingHom = w} = w.localDegree K := by
  have : Algebra.IsSeparable (w.restriction K).Completion w.Completion := isSeparable_completion w
  simpa only [Field.finSepDegree_eq_finrank_of_isSeparable, localDegree] using
    card_embeddings_eq_localFinSepDegree_of_isAlgClosed w u₀ hu₀