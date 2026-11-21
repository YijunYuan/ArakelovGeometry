/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree
public import ArakelovGeometry.AdelicVectorBundle.Tensor.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Descent.InfiniteGalois

/-!
# Scalar extension of finite real filtrations

Subspace layers and their quotient images commute with scalar extension.
The intrinsic expectation and pairing retain the real weights and reciprocal-rank
normalizations. No finite-degree assumption on the extension is required.
The trivial-norm constructions identify these filtrations with the corresponding
norms on completed fibres.
-/

@[expose] public section

open Module ArakelovGeometry
open scoped TensorProduct

namespace Submodule

variable {K L E Q : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] [AddCommGroup Q] [Module K Q]

/-- Actual subspace images commute with scalar extension, for every linear map. -/
theorem baseChange_map_eq (U : Submodule K E) (q : E →ₗ[K] Q) :
    (U.map q).baseChange L = (U.baseChange L).map (q.baseChange L) := by
  rw [baseChange_eq_span, baseChange_eq_span, map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- The extended basis describes the actual extended weighted layer. -/
theorem baseChange_span_basis_weights {ι : Type*} (b : Basis ι K E)
    (w : ι → ℝ) (t : ℝ) :
    (span K (b '' {i | t ≤ w i})).baseChange L =
      span L (b.baseChange L '' {i | t ≤ w i}) := by
  rw [baseChange_span, Set.image_image]
  congr 2
  funext i
  exact (Basis.baseChange_apply L b i).symm

/-- The four genuine finite-filtration conditions are preserved by scalar extension. -/
theorem finite_filtration_baseChange (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    Antitone (fun t ↦ (F t).baseChange L) ∧
      (∃ t, (F t).baseChange L = ⊥) ∧ (∃ t, (F t).baseChange L = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
        (F s).baseChange L = (F t).baseChange L) := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨u, ht⟩ := ht
  refine ⟨fun _ _ h ↦ baseChange_mono L (hF h),
    ⟨b, by rw [hb, baseChange_bot]⟩, ⟨u, by rw [ht, baseChange_top]⟩, ?_⟩
  intro t
  obtain ⟨ε, hε, he⟩ := hl t
  exact ⟨ε, hε, fun s hs hst ↦ congrArg (baseChange L) (he s hs hst)⟩

variable [FiniteDimensional K E]

/-- Actual finite real-filtration expectation is unchanged by arbitrary field extension. -/
theorem filtrationExpectation_baseChange (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    filtrationExpectation (fun t ↦ (F t).baseChange L) = filtrationExpectation F := by
  obtain ⟨b, w, _, hw, _⟩ := exists_common_weighted_basis hF hb ht hl hF hb ht hl
  have hwL t : (F t).baseChange L = span L (b.baseChange L '' {i | t ≤ w i}) := by
    rw [hw, baseChange_span_basis_weights]
  rw [filtrationExpectation_eq_sum_weights (b.baseChange L) w hwL,
    filtrationExpectation_eq_sum_weights b w hw, Module.finrank_baseChange]

/-- Actual pairings retain the common real weights and the reciprocal-rank factor. -/
theorem filtrationPairing_baseChange (F G : ℝ → Submodule K E)
    (hF : Antitone F) (hFb : ∃ t, F t = ⊥) (hFt : ∃ t, F t = ⊤)
    (hFl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hG : Antitone G) (hGb : ∃ t, G t = ⊥) (hGt : ∃ t, G t = ⊤)
    (hGl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → G s = G t) :
    filtrationPairing (fun t ↦ (F t).baseChange L) (fun t ↦ (G t).baseChange L) =
      filtrationPairing F G := by
  obtain ⟨b, w, v, hw, hv, _⟩ := exists_common_weighted_basis hF hFb hFt hFl hG hGb hGt hGl
  have hwL t : (F t).baseChange L = span L (b.baseChange L '' {i | t ≤ w i}) := by
    rw [hw, baseChange_span_basis_weights]
  have hvL t : (G t).baseChange L = span L (b.baseChange L '' {i | t ≤ v i}) := by
    rw [hv, baseChange_span_basis_weights]
  rw [filtrationPairing_eq_sum_weights (b.baseChange L) w v hwL hvL,
    filtrationPairing_eq_sum_weights b w v hw hv, Module.finrank_baseChange]

/-- The actual quotient expectation is preserved by extending its adapted image basis.
This compares the same quotient layers, without comparing determinant-support index types. -/
theorem filtrationExpectation_image_baseChange [FiniteDimensional K Q]
    (F : ℝ → Submodule K E)
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦ ((F t).baseChange L).map (q.baseChange L)) =
      filtrationExpectation (fun t ↦ (F t).map q) := by
  obtain ⟨b, w, _, hw, _⟩ := exists_common_weighted_basis hF hb ht hl hF hb ht hl
  obtain ⟨c, d, hd⟩ := exists_weighted_basis_image b w q hq
  have hqF t : (F t).map q = span K (c '' {i | t ≤ d i}) := by rw [hw]; exact hd t
  have hqL t : ((F t).baseChange L).map (q.baseChange L) =
      span L (c.baseChange L '' {i | t ≤ d i}) := by
    rw [← baseChange_map_eq, hqF, baseChange_span_basis_weights]
  rw [filtrationExpectation_eq_sum_weights (c.baseChange L) d hqL,
    filtrationExpectation_eq_sum_weights c d hqF, Module.finrank_baseChange]

end Submodule

namespace Submodule

section TensorBaseChange

variable {K L J Q : Type*} [Field K] [Field L] [Algebra K L] [Fintype J]
  {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [AddCommGroup Q] [Module K Q]

/-- The finite-family scalar-extended quotient is the actual base change of the given map. -/
noncomputable def piTensorQuotientBaseChange (q : (⨂[K] j, E j) →ₗ[K] Q) :
    (⨂[L] j, L ⊗[K] E j) →ₗ[L] L ⊗[K] Q :=
  (q.baseChange L).comp (tensorBaseChangeEquiv K L E).symm.toLinearMap

/-- Surjectivity is retained by the actual tensor quotient base change. -/
theorem piTensorQuotientBaseChange_surjective (q : (⨂[K] j, E j) →ₗ[K] Q)
    (hq : Function.Surjective q) : Function.Surjective (piTensorQuotientBaseChange (L := L) q) :=
  (LinearMap.baseChange_surjective L hq).comp (tensorBaseChangeEquiv K L E).symm.surjective

/-- Scalar extension identifies the actual tensor-filtration layers. -/
theorem piTensorFiltration_baseChange {ι : J → Type*}
    (b : ∀ j, Basis (ι j) K (E j)) (w : ∀ j, ι j → ℝ)
    {F : ∀ j, ℝ → Submodule K (E j)}
    (hw : ∀ j t, F j t = span K (b j '' {i | t ≤ w j i})) (t : ℝ) :
    ((piTensorFiltration F t).baseChange L).map (tensorBaseChangeEquiv K L E).toLinearMap =
      piTensorFiltration (fun j u ↦ (F j u).baseChange L) t := by
  have hL j u : (F j u).baseChange L =
      span L ((b j).baseChange L '' {i | u ≤ w j i}) := by
    rw [hw, baseChange_span_basis_weights]
  rw [piTensorFiltration_eq_span b w hw, baseChange_span_basis_weights,
    map_span, Set.image_image, piTensorFiltration_eq_span (fun j ↦ (b j).baseChange L) w hL]
  congr 2
  funext p
  simp [Basis.baseChange_apply, Basis.piTensorProduct_apply]

/-- Actual quotient layers, not merely their numerical expectations, commute with base change. -/
theorem piTensorFiltration_image_baseChange {ι : J → Type*}
    (b : ∀ j, Basis (ι j) K (E j)) (w : ∀ j, ι j → ℝ)
    {F : ∀ j, ℝ → Submodule K (E j)}
    (hw : ∀ j t, F j t = span K (b j '' {i | t ≤ w j i}))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (t : ℝ) :
    ((piTensorFiltration F t).map q).baseChange L =
      (piTensorFiltration (fun j u ↦ (F j u).baseChange L) t).map
        (piTensorQuotientBaseChange q) := by
  rw [← piTensorFiltration_baseChange b w hw, ← map_comp, baseChange_map_eq]
  congr 1
  ext z
  simp [piTensorQuotientBaseChange]

variable [∀ j, FiniteDimensional K (E j)] [FiniteDimensional K Q]

/-- The actual tensor quotient expectation is unchanged under an arbitrary field extension. -/
theorem filtrationExpectation_piTensor_image_baseChange
    (F : ∀ j, ℝ → Submodule K (E j))
    (hF : ∀ j, Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t))
    (q : (⨂[K] j, E j) →ₗ[K] Q) (hq : Function.Surjective q) :
    filtrationExpectation (fun t ↦
      (piTensorFiltration (fun j u ↦ (F j u).baseChange L) t).map
        (piTensorQuotientBaseChange q)) =
      filtrationExpectation (fun t ↦ (piTensorFiltration F t).map q) := by
  have hex j := exists_common_weighted_basis (hF j).1 (hF j).2.1 (hF j).2.2.1
    (hF j).2.2.2 (hF j).1 (hF j).2.1 (hF j).2.2.1 (hF j).2.2.2
  choose b w v hw hv _ using hex
  obtain ⟨c, d, hd⟩ := exists_weighted_basis_image (Basis.piTensorProduct b)
    (fun p ↦ ∑ j, w j (p j)) q hq
  have hqF t : (piTensorFiltration F t).map q = span K (c '' {i | t ≤ d i}) := by
    rw [piTensorFiltration_eq_span b w hw]
    exact hd t
  have hqL t : (piTensorFiltration (fun j u ↦ (F j u).baseChange L) t).map
      (piTensorQuotientBaseChange q) = span L (c.baseChange L '' {i | t ≤ d i}) := by
    rw [← piTensorFiltration_image_baseChange b w hw, hqF, baseChange_span_basis_weights]
  rw [filtrationExpectation_eq_sum_weights (c.baseChange L) d hqL,
    filtrationExpectation_eq_sum_weights c d hqF, Module.finrank_baseChange]

end TensorBaseChange

end Submodule

namespace ArakelovGeometry

section GaloisFiltration

variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E]

/-- Inverse Galois transport on actual vectors, valid for an infinite extension. -/
@[simp]
theorem scalarExtensionSemilinearEquiv_symm_apply_apply (σ : L ≃ₐ[K] L)
    (x : L ⊗[K] E) :
    scalarExtensionSemilinearEquiv σ.symm (scalarExtensionSemilinearEquiv σ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp only [scalarExtensionSemilinearEquiv_tmul, AlgEquiv.symm_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Inverse transport recovers the actual subspace. -/
@[simp]
theorem scalarExtensionSubspaceOrderIso_symm_apply_apply (σ : L ≃ₐ[K] L)
    (U : Submodule L (L ⊗[K] E)) :
    scalarExtensionSubspaceOrderIso σ.symm (scalarExtensionSubspaceOrderIso σ U) = U := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    change scalarExtensionSemilinearEquiv σ.symm (scalarExtensionSemilinearEquiv σ y) ∈ U
    rw [scalarExtensionSemilinearEquiv_symm_apply_apply]
    exact hy
  · intro hx
    exact ⟨scalarExtensionSemilinearEquiv σ x, ⟨x, hx, rfl⟩,
      scalarExtensionSemilinearEquiv_symm_apply_apply σ x⟩

/-- The Galois action preserves all four conditions on actual real filtrations. -/
theorem finite_filtration_scalarExtensionSubspaceOrderIso (σ : L ≃ₐ[K] L)
    (F : ℝ → Submodule L (L ⊗[K] E))
    (hF : Antitone F) (hb : ∃ t, F t = ⊥) (ht : ∃ t, F t = ⊤)
    (hl : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) :
    Antitone (fun t ↦ scalarExtensionSubspaceOrderIso σ (F t)) ∧
      (∃ t, scalarExtensionSubspaceOrderIso σ (F t) = ⊥) ∧
      (∃ t, scalarExtensionSubspaceOrderIso σ (F t) = ⊤) ∧
      (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
        scalarExtensionSubspaceOrderIso σ (F s) = scalarExtensionSubspaceOrderIso σ (F t)) := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨u, ht⟩ := ht
  refine ⟨fun _ _ h ↦ (scalarExtensionSubspaceOrderIso σ).monotone (hF h),
    ⟨b, by rw [hb, OrderIso.map_bot]⟩, ⟨u, by rw [ht, OrderIso.map_top]⟩, ?_⟩
  intro t
  obtain ⟨ε, hε, he⟩ := hl t
  exact ⟨ε, hε, fun s hs hst ↦ congrArg (scalarExtensionSubspaceOrderIso σ) (he s hs hst)⟩

/-- Galois transport preserves strict right limits as actual subspaces. -/
theorem filtrationRightLimit_scalarExtensionSubspaceOrderIso (σ : L ≃ₐ[K] L)
    (F : ℝ → Submodule L (L ⊗[K] E)) (t : ℝ) :
    Submodule.filtrationRightLimit (fun s ↦ scalarExtensionSubspaceOrderIso σ (F s)) t =
      scalarExtensionSubspaceOrderIso σ (Submodule.filtrationRightLimit F t) :=
  ((scalarExtensionSubspaceOrderIso σ).map_iSup _).symm

variable [FiniteDimensional K E]

/-- Galois transport preserves the intrinsic expectation of actual layers. -/
theorem filtrationExpectation_scalarExtensionSubspaceOrderIso (σ : L ≃ₐ[K] L)
    (F : ℝ → Submodule L (L ⊗[K] E)) :
    Submodule.filtrationExpectation (fun t ↦ scalarExtensionSubspaceOrderIso σ (F t)) =
      Submodule.filtrationExpectation F := by
  unfold Submodule.filtrationExpectation Submodule.FiltrationGraded
  congr 1
  apply finsum_congr
  intro t
  rw [filtrationRightLimit_scalarExtensionSubspaceOrderIso σ F t,
    scalarExtensionSubquotientSemilinearEquiv_finrank]

/-- Galois transport preserves intrinsic pairings, via intersections, joins and dimensions. -/
theorem filtrationPairing_scalarExtensionSubspaceOrderIso (σ : L ≃ₐ[K] L)
    (F G : ℝ → Submodule L (L ⊗[K] E)) :
    Submodule.filtrationPairing (fun t ↦ scalarExtensionSubspaceOrderIso σ (F t))
      (fun t ↦ scalarExtensionSubspaceOrderIso σ (G t)) = Submodule.filtrationPairing F G := by
  unfold Submodule.filtrationPairing Submodule.filtrationJointMultiplicity
  congr 1
  apply finsum_congr
  intro p
  rw [filtrationRightLimit_scalarExtensionSubspaceOrderIso σ F p.1,
    filtrationRightLimit_scalarExtensionSubspaceOrderIso σ G p.2,
    ← (scalarExtensionSubspaceOrderIso σ).map_inf,
    ← (scalarExtensionSubspaceOrderIso σ).map_inf,
    ← (scalarExtensionSubspaceOrderIso σ).map_inf,
    ← (scalarExtensionSubspaceOrderIso σ).map_sup,
    scalarExtensionSubspaceOrderIso_finrank, scalarExtensionSubspaceOrderIso_finrank]

end GaloisFiltration

end ArakelovGeometry

namespace Submodule

section GaloisQuotient

variable {K L J Q : Type*} [Field K] [Field L] [Algebra K L] [Fintype J]
  {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [∀ j, FiniteDimensional K (E j)]
  [AddCommGroup Q] [Module K Q]

/-- The actual scalar-extended quotient intertwines the semilinear Galois actions
on pure tensors. The proof expands in extended original bases, retaining the given quotient. -/
theorem piTensorQuotientBaseChange_galois_tprod (σ : L ≃ₐ[K] L)
    (q : (⨂[K] j, E j) →ₗ[K] Q) (x : ∀ j, L ⊗[K] E j) :
    scalarExtensionSemilinearEquiv σ (piTensorQuotientBaseChange q (⨂ₜ[L] j, x j)) =
      piTensorQuotientBaseChange q (⨂ₜ[L] j, scalarExtensionSemilinearEquiv σ (x j)) := by
  classical
  let b := fun j ↦ Module.finBasis K (E j)
  let c := fun j ↦ ((b j).baseChange L).repr (x j)
  have hx : x = fun j ↦ ∑ i, c j i ⊗ₜ[K] b j i := by
    funext j
    simpa only [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using (((b j).baseChange L).sum_repr (x j)).symm
  rw [hx]
  simp only [MultilinearMap.map_sum, map_sum, scalarExtensionSemilinearEquiv_tmul,
    piTensorQuotientBaseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorBaseChangeEquiv_symm_tprod_tmul, LinearMap.baseChange_tmul, map_prod]

/-- Galois transport sends every actual tensor quotient layer into the transported layer. -/
theorem scalarExtensionSubspaceOrderIso_piTensor_image_le (σ : L ≃ₐ[K] L)
    (q : (⨂[K] j, E j) →ₗ[K] Q)
    (F : ∀ j, ℝ → Submodule L (L ⊗[K] E j)) (t : ℝ) :
    scalarExtensionSubspaceOrderIso σ
      ((piTensorFiltration F t).map (piTensorQuotientBaseChange q)) ≤
      (piTensorFiltration (fun j u ↦ scalarExtensionSubspaceOrderIso σ (F j u)) t).map
        (piTensorQuotientBaseChange q) := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  change ((piTensorFiltration F t).map (piTensorQuotientBaseChange q)).map
    (scalarExtensionSemilinearEquiv σ).toLinearMap ≤ _
  simp only [piTensorFiltration, map_iSup]
  refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
  rw [PiTensorProduct.mapIncl, PiTensorProduct.map_range_eq_span_tprod, map_span, map_span]
  apply span_le.mpr
  rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
  change scalarExtensionSemilinearEquiv σ
    (piTensorQuotientBaseChange q (⨂ₜ[L] j, (x j : L ⊗[K] E j))) ∈ _
  rw [piTensorQuotientBaseChange_galois_tprod]
  apply mem_iSup_of_mem a
  apply mem_iSup_of_mem ha
  apply mem_map_of_mem
  exact ⟨⨂ₜ[L] j, (⟨scalarExtensionSemilinearEquiv σ (x j : L ⊗[K] E j),
    ⟨x j, (x j).property, rfl⟩⟩ : scalarExtensionSubspaceOrderIso σ (F j (a j))), by
      simp only [PiTensorProduct.mapIncl, PiTensorProduct.map_tprod, subtype_apply]⟩

/-- Galois transport commutes with the actual tensor quotient layer, for arbitrary input layers. -/
theorem scalarExtensionSubspaceOrderIso_piTensor_image (σ : L ≃ₐ[K] L)
    (q : (⨂[K] j, E j) →ₗ[K] Q)
    (F : ∀ j, ℝ → Submodule L (L ⊗[K] E j)) (t : ℝ) :
    scalarExtensionSubspaceOrderIso σ
      ((piTensorFiltration F t).map (piTensorQuotientBaseChange q)) =
      (piTensorFiltration (fun j u ↦ scalarExtensionSubspaceOrderIso σ (F j u)) t).map
        (piTensorQuotientBaseChange q) := by
  apply le_antisymm (scalarExtensionSubspaceOrderIso_piTensor_image_le σ q F t)
  have h := scalarExtensionSubspaceOrderIso_piTensor_image_le σ.symm q
    (fun j u ↦ scalarExtensionSubspaceOrderIso σ (F j u)) t
  simp only [scalarExtensionSubspaceOrderIso_symm_apply_apply] at h
  have h' := (scalarExtensionSubspaceOrderIso σ).monotone h
  have hinv (U : Submodule L (L ⊗[K] Q)) :
      scalarExtensionSubspaceOrderIso σ (scalarExtensionSubspaceOrderIso σ.symm U) = U := by
    simpa only [AlgEquiv.symm_symm] using
      scalarExtensionSubspaceOrderIso_symm_apply_apply σ.symm U
  simpa only [hinv] using h'

/-- The Galois action preserves the actual quotient objective; no invariance of the
input filtrations is assumed. -/
theorem filtrationExpectation_piTensor_image_galois [FiniteDimensional K Q]
    (σ : L ≃ₐ[K] L) (q : (⨂[K] j, E j) →ₗ[K] Q)
    (F : ∀ j, ℝ → Submodule L (L ⊗[K] E j)) :
    filtrationExpectation (fun t ↦
      (piTensorFiltration (fun j u ↦ scalarExtensionSubspaceOrderIso σ (F j u)) t).map
        (piTensorQuotientBaseChange q)) =
      filtrationExpectation (fun t ↦ (piTensorFiltration F t).map
        (piTensorQuotientBaseChange q)) := by
  simp_rw [← scalarExtensionSubspaceOrderIso_piTensor_image σ q F]
  exact filtrationExpectation_scalarExtensionSubspaceOrderIso σ _

end GaloisQuotient

end Submodule
