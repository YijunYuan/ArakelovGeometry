/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor decomposition into completed fields

The canonical homomorphisms to completed extensions have distinct maximal kernels.
The Chinese remainder theorem and the local-degree sum identify their product with
the tensor product over the ground field.
-/

@[expose] public section

open scoped TensorProduct

namespace AbsoluteValue
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (w : AbsoluteValue L ℝ)
/-- The base field maps compatibly through its completion into an extending completion. -/
instance isScalarTower_base_completion :
    IsScalarTower K (w.restriction K).Completion w.Completion := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change (WithAbs.toAbs w (algebraMap K L a) : w.Completion) =
    algebraMap (w.restriction K).Completion w.Completion
      (WithAbs.toAbs (w.restriction K) a : (w.restriction K).Completion)
  rw [algebraMap_completion_def, UniformSpace.Completion.mapRingHom_coe]
  rfl
/-- The tensor-product map onto the completion of an extending absolute value. -/
noncomputable def completionTensorMap :
    (w.restriction K).Completion ⊗[K] L →ₐ[(w.restriction K).Completion] w.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (IsScalarTower.toAlgHom K L w.Completion) (fun _ _ ↦ Commute.all _ _)
/-- Images of a finite basis make the canonical tensor map surjective. -/
theorem completionTensorMap_surjective [FiniteDimensional K L] :
    Function.Surjective (completionTensorMap (K := K) w) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← w.span_coe_basis_eq_top K (Module.finBasis K L)]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨1 ⊗ₜ[K] (Module.finBasis K L i), ?_⟩
  change completionTensorMap (K := K) w (1 ⊗ₜ[K] (Module.finBasis K L i)) = _
  simp only [completionTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- Transport the canonical completed-base algebra across an equality of restrictions. -/
@[instance_reducible]
noncomputable def algebraCompletionOfEq (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.restriction K = v) :
    Algebra v.Completion w.Completion := h ▸ algebraCompletion w K

/-- The tensor-product map with an explicitly specified base absolute value. -/
noncomputable def completionTensorMapOfEq (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.restriction K = v) :
    let _ := algebraCompletionOfEq v w h
    v.Completion ⊗[K] L →ₐ[v.Completion] w.Completion := by
  subst v
  exact completionTensorMap (K := K) w

/-- The specified-base tensor map is surjective for a finite field extension. -/
theorem completionTensorMapOfEq_surjective [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.restriction K = v) :
    Function.Surjective (completionTensorMapOfEq v w h) := by
  subst v
  exact completionTensorMap_surjective w
/-- The tensor map extends the canonical inclusion of the field into its completion. -/
theorem completionTensorMapOfEq_one_tmul (v : AbsoluteValue K ℝ)
    (w : AbsoluteValue L ℝ) (h : w.restriction K = v) (a : L) :
    completionTensorMapOfEq v w h (1 ⊗ₜ[K] a) = algebraMap L w.Completion a := by
  subst v
  change completionTensorMap (K := K) w (1 ⊗ₜ[K] a) = _
  simp only [completionTensorMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl


/-- Different extending absolute values give different kernels of their tensor maps. -/
theorem completionTensorMapOfEq_ker_injective [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) :
    Function.Injective (fun w : {w : AbsoluteValue L ℝ // w.restriction K = v} ↦
      let _ := algebraCompletionOfEq v w.val w.property
      RingHom.ker (completionTensorMapOfEq v w.val w.property).toRingHom) := by
  intro w₁ w₂ h
  let B := v.Completion
  let : Algebra B w₁.val.Completion := algebraCompletionOfEq v w₁.val w₁.property
  let : Algebra B w₂.val.Completion := algebraCompletionOfEq v w₂.val w₂.property
  let f₁ := completionTensorMapOfEq v w₁.val w₁.property
  let f₂ := completionTensorMapOfEq v w₂.val w₂.property
  let e : w₁.val.Completion →ₐ[B] w₂.val.Completion :=
    AlgHom.liftOfSurjective f₁ (completionTensorMapOfEq_surjective v w₁.val w₁.property)
      f₂ h.le
  have he (a : B ⊗[K] L) : e (f₁ a) = f₂ a :=
    AlgHom.liftOfSurjective_apply _ _ _ _ a
  have hn (w : {w : AbsoluteValue L ℝ // w.restriction K = v}) :
      let _ := algebraCompletionOfEq v w.val w.property
      ∀ a : B, ‖algebraMap B w.val.Completion a‖ = ‖a‖ := by
    rcases w with ⟨w, hw⟩
    dsimp only at hw ⊢
    subst v
    exact norm_algebraMap_completion w K
  have hfinite : FiniteDimensional B w₁.val.Completion := by
    rcases w₁ with ⟨w, hw⟩
    dsimp only at hw ⊢
    subst v
    exact finiteDimensional_completion w K
  let n := NormedField.toAbsoluteValue B
  let en : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  let : CompleteSpace (WithAbs n) := en.completeSpace
  have hu₁ : (NormedField.toAbsoluteValue w₁.val.Completion).restriction B = n := by
    ext a
    exact hn w₁ a
  have hu₂ : ((NormedField.toAbsoluteValue w₂.val.Completion).pullback e.toRingHom).restriction B
      = n := by
    ext a
    change ‖e (algebraMap B w₁.val.Completion a)‖ = ‖a‖
    rw [e.commutes]
    exact hn w₂ a
  obtain ⟨u, hu, hunique⟩ := existsUnique_extension_of_complete (L := w₁.val.Completion) n
  have he_norm (a : w₁.val.Completion) : ‖e a‖ = ‖a‖ :=
    congrArg (fun v : AbsoluteValue w₁.val.Completion ℝ ↦ v a)
      ((hunique _ hu₂).trans (hunique _ hu₁).symm)
  apply Subtype.ext
  ext a
  have hea := he (1 ⊗ₜ[K] a)
  change e (completionTensorMapOfEq v w₁.val w₁.property (1 ⊗ₜ[K] a)) =
    completionTensorMapOfEq v w₂.val w₂.property (1 ⊗ₜ[K] a) at hea
  rw [completionTensorMapOfEq_one_tmul, completionTensorMapOfEq_one_tmul] at hea
  have hz := he_norm (algebraMap L w₁.val.Completion a)
  rw [hea] at hz
  change ‖(WithAbs.toAbs w₂.val a : w₂.val.Completion)‖ =
    ‖(WithAbs.toAbs w₁.val a : w₁.val.Completion)‖ at hz
  simpa only [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.ofAbs_toAbs] using hz.symm


section Product
variable (v : AbsoluteValue K ℝ)
/-- Every extending completion carries the same specified completed-base scalar field. -/
@[instance_reducible]
noncomputable def algebraCompletionExtension
    (w : {w : AbsoluteValue L ℝ // w.restriction K = v}) :
    Algebra v.Completion w.val.Completion := algebraCompletionOfEq v w.val w.property

attribute [local instance] algebraCompletionExtension

/-- The simultaneous canonical map to all completions above a fixed absolute value. -/
noncomputable def completionTensorProductMap :
    v.Completion ⊗[K] L →ₐ[v.Completion]
      (∀ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, w.val.Completion) :=
  AlgHom.pi (fun w ↦ completionTensorMapOfEq v w.val w.property)

/-- The Chinese remainder theorem makes the simultaneous completion map surjective. -/
theorem completionTensorProductMap_surjective [FiniteDimensional K L] :
    Function.Surjective (completionTensorProductMap (L := L) v) := by
  classical
  let : Finite {w : AbsoluteValue L ℝ // w.restriction K = v} :=
    (finite_extensions (L := L) v).to_subtype
  let f (w : {w : AbsoluteValue L ℝ // w.restriction K = v}) :=
    completionTensorMapOfEq v w.val w.property
  have hf (w) : Function.Surjective (f w) :=
    completionTensorMapOfEq_surjective v w.val w.property
  have hm (w) : (RingHom.ker (f w).toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (f w).toRingHom (hf w)
  let : ∀ w, (RingHom.ker (f w).toRingHom).IsMaximal := hm
  have hp : Pairwise (Function.onFun IsCoprime (fun w ↦ RingHom.ker (f w).toRingHom)) := by
    intro w₁ w₂ hne
    apply Ideal.isCoprime_of_isMaximal
    exact fun h ↦ hne (completionTensorMapOfEq_ker_injective v h)
  let e (w) := Ideal.quotientKerAlgEquivOfSurjective (hf w)
  intro y
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hp (fun w ↦ (e w).symm (y w))
  refine ⟨a, funext fun w ↦ ?_⟩
  have h := congrArg (e w) (ha w)
  change f w a = y w
  change e w ((Ideal.Quotient.mk (RingHom.ker (f w).toRingHom)) a) =
    e w ((e w).symm (y w)) at h
  rw [(e w).apply_symm_apply] at h
  exact (Ideal.quotientKerAlgEquivOfSurjective_mk (hf w) a).symm.trans h

/-- A finite separable extension decomposes after completion into its completed fields. -/
noncomputable def completionTensorEquiv [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    v.Completion ⊗[K] L ≃ₐ[v.Completion]
      (∀ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, w.val.Completion) := by
  classical
  let : Fintype {w : AbsoluteValue L ℝ // w.restriction K = v} :=
    (finite_extensions (L := L) v).fintype
  let : ∀ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
      FiniteDimensional v.Completion w.val.Completion := by
    rintro ⟨w, hw⟩
    dsimp only at hw ⊢
    subst v
    exact finiteDimensional_completion w K
  have hdim (w : {w : AbsoluteValue L ℝ // w.restriction K = v}) :
      Module.finrank v.Completion w.val.Completion = w.val.localDegree K := by
    rcases w with ⟨w, hw⟩
    dsimp only at hw ⊢
    subst v
    rfl
  let : ∀ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
      Module.Free v.Completion w.val.Completion := fun w ↦ Module.Free.of_divisionRing _ _
  have hd : Module.finrank v.Completion (v.Completion ⊗[K] L) =
      Module.finrank v.Completion
        (∀ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, w.val.Completion) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
      Module.finrank_pi_fintype]
    simp_rw [hdim]
    exact (sum_localDegree v).symm
  let f := completionTensorProductMap (L := L) v
  exact AlgEquiv.ofBijective f
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd (f := f.toLinearMap)).mpr
      (completionTensorProductMap_surjective v), completionTensorProductMap_surjective v⟩

/-- The local factorization carries a field element to its image in every completion. -/
theorem completionTensorEquiv_one_tmul [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (a : L) (w : {w : AbsoluteValue L ℝ // w.restriction K = v}) :
    completionTensorEquiv (L := L) v (1 ⊗ₜ[K] a) w = algebraMap L w.val.Completion a := by
  change completionTensorMapOfEq v w.val w.property (1 ⊗ₜ[K] a) = _
  exact completionTensorMapOfEq_one_tmul v w.val w.property a

end Product

end AbsoluteValue
