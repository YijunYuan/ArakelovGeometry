/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.TensorOperator
import ArakelovGeometry.AdelicVectorBundle.TensorDomination
import ArakelovGeometry.AdelicVectorBundle.OperatorComparison

/-!
# Integrable heights between strongly adelic bundles

Actual injective tensors first control the map between bidual norms. Strong
domination controls the two local distances back to the original norms.
-/

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- Tensor domination supplies both integrable bounds for maps from the first
dual to the second bidual, through the genuine tensor-to-Hom equivalence. -/
theorem localHeight_dual_bidual_bounds {E : Unit ⊕ Unit → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (ξ : ∀ i, NormFamily S (E i))
    (hξ : ∀ i, (ξ i).IsDominated) (hfin : S.v S.Ωinf < ⊤)
    (f : {f : Module.Dual K (E (.inl ())) →ₗ[K] E (.inr ()) // f ≠ 0}) :
    HasIntegrableBounds ((ξ (.inl ())).dual.localHeight
      ((ξ (.inr ())).dual.dual.pullback (Module.Dual.eval K (E (.inr ())))
        (Module.eval_apply_injective K)) f) S.v := by
  let z := (binaryTensorToHomEquiv K E).symm f.val
  have hz : z ≠ 0 := by
    intro h
    have he := (binaryTensorToHomEquiv K E).apply_symm_apply f.val
    change binaryTensorToHomEquiv K E z = f.val at he
    rw [h, map_zero] at he
    exact f.property he.symm
  have he : binaryTensorToHom K E z = f.val := by
    exact (binaryTensorToHomEquiv K E).apply_symm_apply f.val
  apply ((IsDominated.strong_injectiveTensor ξ hξ hfin).1.logNorm_bounds hz).congr
  apply Eventually.of_forall
  intro ω
  change Real.log ((injectiveTensor ξ).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] z)) = _
  rw [injectiveTensor_norm_eq_operatorNorm, he]
  rfl

variable {E F : Type (max u w)} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Every map between canonical bidual norm families has integrable logarithmic
bounds. The tensor representing it is supplied by a proved linear equivalence. -/
theorem localHeight_bidual_bounds (ξ : NormFamily S E) (η : NormFamily S F)
    (hξ : ξ.IsDominated) (hη : η.IsDominated) (hfin : S.v S.Ωinf < ⊤)
    (f : {f : E →ₗ[K] F // f ≠ 0}) :
    HasIntegrableBounds
      ((ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)).localHeight
        (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K)) f) S.v := by
  let M : Unit ⊕ Unit → Type (max u w)
    | .inl _ => Module.Dual K E
    | .inr _ => F
  let : ∀ i, AddCommGroup (M i) := by
    rintro (i | i) <;> dsimp [M] <;> infer_instance
  let : ∀ i, Module K (M i) := by
    rintro (i | i) <;> dsimp [M] <;> infer_instance
  let : ∀ i, FiniteDimensional K (M i) := by
    rintro (i | i) <;> dsimp [M] <;> infer_instance
  let Ξ : ∀ i, NormFamily S (M i) := by
    rintro (i | i)
    · exact ξ.dual
    · exact η
  have hΞ : ∀ i, (Ξ i).IsDominated := by
    rintro (i | i)
    · exact hξ.dual
    · exact hη
  let e := Module.evalEquiv K E
  let g := f.val.comp e.symm.toLinearMap
  have hge : g.comp e.toLinearMap = f.val := by
    ext x
    simp [g]
  have hg : g ≠ 0 := by
    intro h
    apply f.property
    rw [← hge, h, LinearMap.zero_comp]
  have hb := localHeight_dual_bidual_bounds Ξ hΞ hfin ⟨g, hg⟩
  apply hb.congr
  apply Eventually.of_forall
  intro ω
  have he := ξ.dual.dual.operatorNorm_comp_equiv
    (η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K)) e g ω
  rw [hge] at he
  exact congrArg Real.log he.symm

/-- The bidual tensor bound and the two actual local distances prove domination
of local heights for strongly dominated source and target families. -/
theorem IsStronglyDominated.localHeight_bounds {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) (f : {f : E →ₗ[K] F // f ≠ 0}) :
    HasIntegrableBounds (ξ.localHeight η f) S.v := by
  let ξbb := ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  let ηbb := η.dual.dual.pullback (Module.Dual.eval K F) (Module.eval_apply_injective K)
  have hb := localHeight_bidual_bounds ξ η hξ.1 hη.1 hfin f
  apply ((hb.abs.add hξ.2).add hη.2).of_abs_le
  apply Eventually.of_forall
  intro ω
  have hd := ξ.abs_localHeight_sub_le_localDist ξbb η ηbb ω f
  change |ξ.localHeight η f ω| ≤ |ξbb.localHeight ηbb f ω| +
    ξ.localDist ξbb ω + η.localDist ηbb ω
  calc
    |ξ.localHeight η f ω| =
        |(ξ.localHeight η f ω - ξbb.localHeight ηbb f ω) + ξbb.localHeight ηbb f ω| := by
      congr 1
      ring
    _ ≤ |ξ.localHeight η f ω - ξbb.localHeight ηbb f ω| + |ξbb.localHeight ηbb f ω| :=
      abs_add_le _ _
    _ ≤ _ := by linarith

/-- Under either source measurability alternative, the two proved bounds
give an integrable local map height. -/
theorem IsStronglyDominated.integrable_localHeight {ξ : NormFamily S E} {η : NormFamily S F}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hmξ : ξ.IsMeasurable) (hmη : η.IsMeasurable)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hfin : S.v S.Ωinf < ⊤) (f : {f : E →ₗ[K] F // f ≠ 0}) :
    Integrable (ξ.localHeight η f) S.v :=
  (hξ.localHeight_bounds hη hfin f).integrable
    (hmξ.localHeight_of_discrete_or_countable hmη hS f).aestronglyMeasurable

end

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type (max u w)} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Source Proposition4.3.16: local map height is integrable for strongly
adelic bundles. Normalization proves the required finite Archimedean measure. -/
theorem integrable_localHeight_of_isStronglyAdelic (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (hV : V.IsStronglyAdelic) (hW : W.IsStronglyAdelic)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (f : {f : E →ₗ[K] F // f ≠ 0}) :
    Integrable (V.toNormFamily.localHeight W.toNormFamily f) S.v :=
  hV.integrable_localHeight hW V.isMeasurable W.isMeasurable hS
    (S.v_Ωinf_lt_top_of_isRCLike hN) f

/-- The actual lower-integral map height is a finite real integral for a
nonzero map between strongly adelic bundles. -/
theorem mapHeight_eq_integral_of_isStronglyAdelic (V : AdelicVectorBundle S E)
    (W : AdelicVectorBundle S F) (hV : V.IsStronglyAdelic) (hW : W.IsStronglyAdelic)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {f : E →ₗ[K] F} (hf : f ≠ 0) :
    V.mapHeight W f = ((∫ ω, V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω ∂S.v) : ℝ) :=
  V.mapHeight_eq_integral W hf
    (V.integrable_localHeight_of_isStronglyAdelic W hV hW hS hN ⟨f, hf⟩)

end ArakelovGeometry.AdelicVectorBundle
