/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.EquivMeasure
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianDegree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismDeterminantRational

/-!
# Actual Hermitian completed-fibre transport under coefficient automorphisms

The extending Archimedean normalization is produced from the original one.
Coefficient transport preserves the exact Hermitian extension, including
arbitrary completed vectors, actual restrictions and their determinants.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry


private theorem hermitianTensor_norm_algEquiv
    {k A B V ι : Type*} [RCLike k] [RCLike A] [RCLike B]
    [NormedAlgebra k A] [NormedAlgebra k B] [NormedAddCommGroup V]
    [InnerProductSpace k V] [Fintype ι] (b : OrthonormalBasis ι k V)
    (e : A ≃ₐ[k] B) (he : ∀ a, ‖e a‖ = ‖a‖) (z : A ⊗[k] V) :
    ‖hermitianScalarExtensionCoordinates (L := B) b
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k V) z)‖ =
      ‖hermitianScalarExtensionCoordinates (L := A) b z‖ := by
  have hc (i : ι) : hermitianScalarExtensionCoordinates (L := B) b
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl k V) z) i =
      e (hermitianScalarExtensionCoordinates (L := A) b z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        hermitianScalarExtensionCoordinates_tmul, map_mul, e.commutes]
      rfl
    | add x y hx hy => simp only [map_add, PiLp.add_apply, hx, hy]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun r : ℝ => r ^ 2) ((congrArg norm (hc i)).trans (he _))


namespace NormFamily
open AdelicStructure.ParameterSpaceExtension
variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {S : AdelicStructure K}

/-- The actual Hermitian extension is isometric under every coefficient automorphism,
with target Archimedean normalization produced from the original normalization. -/
theorem hermitianScalarExtension_norm_algEquiv (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ξ.IsHermitian hN) (σ : L ≃ₐ[K] L) (x : S.ParameterSpaceExtension L) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (L ⊗[K] E),
      (ξ.hermitianScalarExtension hN
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).norm x
          (completedScalarExtensionAlgEquiv (E := E) σ x z) =
        (ξ.hermitianScalarExtension hN
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).norm
            (pullbackAlgEquiv S σ x) z := by
  intro aL aM z
  let := aL
  let := aM
  let hNL := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · have hy : pullbackAlgEquiv S σ x ∈ (S.algebraicExtension L).Ωfin :=
      (pullbackAlgEquiv_mem_Ωfin_iff S σ x).mpr hx
    rw [hermitianScalarExtension_norm_of_finite ξ hN hNL hH x hx,
      hermitianScalarExtension_norm_of_finite ξ hN hNL hH _ hy]
    exact ξ.injectiveScalarExtensionSeminorm_algEquiv σ x z
  · have hxinf : x ∈ (S.algebraicExtension L).Ωinf := hx
    have hyinf : pullbackAlgEquiv S σ x ∈ (S.algebraicExtension L).Ωinf :=
      fun hy => hx ((pullbackAlgEquiv_mem_Ωfin_iff S σ x).mp hy)
    let := hN x.base ((scalarExtension_mem_Ωinf_iff x).mp hxinf)
    let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    let : IsRCLikeNormedField (pullbackAlgEquiv S σ x).abv.Completion := hNL _ hyinf
    let := IsRCLikeNormedField.rclike (pullbackAlgEquiv S σ x).abv.Completion
    let : IsRCLikeNormedField x.abv.Completion := hNL x hxinf
    let := IsRCLikeNormedField.rclike x.abv.Completion
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    let := hH.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hxinf)
    let b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
        ((S.ϕ x.base).Completion ⊗[K] E) :=
      (stdOrthonormalBasis (S.ϕ x.base).Completion
        ((S.ϕ x.base).Completion ⊗[K] E)).reindex (finCongr Module.finrank_baseChange)
    rw [hermitianScalarExtension_norm_coordinates ξ hN hNL hH x hxinf b,
      hermitianScalarExtension_norm_coordinates ξ hN hNL hH _ hyinf b]
    have hflat : completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
        (completedScalarExtensionAlgEquiv (E := E) σ x z) =
        TensorProduct.congr (algEquivCompletedFields S σ x).toLinearEquiv
          (LinearEquiv.refl (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E))
          (completedScalarExtensionEquiv E (S.ϕ x.base)
            (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq z) := by
      change (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq)
        ((completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq).symm _) = _
      exact LinearEquiv.apply_symm_apply _ _
    rw [hflat]
    exact hermitianTensor_norm_algEquiv b (algEquivCompletedFields S σ x)
      ((isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
        (map_zero (algEquivCompletedFields S σ x))) _

/-- Coefficient transport preserves the genuine restriction of the Hermitian
scalar-extension norm, without an invariant-subspace hypothesis. -/
theorem hermitianScalarExtension_restrict_norm_algEquiv (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ξ.IsHermitian hN) (σ : L ≃ₐ[K] L) (x : S.ParameterSpaceExtension L)
    (B : Submodule L (L ⊗[K] E))
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L] B) :
    ((ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
        (scalarExtensionSubspaceOrderIso (E := E) σ B)).norm x
          (completedScalarExtensionRestrictionEquiv σ x B z) =
      ((ξ.hermitianScalarExtension hN
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
          B).norm (pullbackAlgEquiv S σ x) z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  change (ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).norm x
    ((scalarExtensionSubspaceOrderIso (E := E) σ B).subtype.baseChange x.abv.Completion
      (completedScalarExtensionRestrictionEquiv σ x B z)) =
    (ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).norm
        (pullbackAlgEquiv S σ x)
        (B.subtype.baseChange (pullbackAlgEquiv S σ x).abv.Completion z)
  rw [completedScalarExtensionRestrictionEquiv_inclusion]
  exact ξ.hermitianScalarExtension_norm_algEquiv hN hH σ x _

/-- The actual completed determinant of every genuine Hermitian restriction is
isometric under coefficient transport, including the empty top wedge. -/
theorem hermitianScalarExtension_restrict_determinant_norm_algEquiv (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ξ.IsHermitian hN) (σ : L ≃ₐ[K] L) (x : S.ParameterSpaceExtension L)
    (B : Submodule L (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    ∀ z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L B) B),
      ((ξ.hermitianScalarExtension hN
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
          (scalarExtensionSubspaceOrderIso (E := E) σ B)).determinant.norm x
            (completedDeterminantSemilinearEquiv (algEquivCompletedFields S σ x).toRingEquiv
              (completedScalarExtensionRestrictionEquiv σ x B)
              (scalarExtensionSubspaceOrderIso_finrank σ B).symm z) =
        ((ξ.hermitianScalarExtension hN
          (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
            B).determinant.norm (pullbackAlgEquiv S σ x) z := by
  intro aL aM z
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let η := (ξ.hermitianScalarExtension hN
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict B
  let θ := (ξ.hermitianScalarExtension hN
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)
  exact completedDeterminantSeminorm_norm_eq (algEquivCompletedFields S σ x).toRingEquiv
    (η.norm (pullbackAlgEquiv S σ x)) (η.determinant.norm (pullbackAlgEquiv S σ x))
    (θ.norm x) (θ.determinant.norm x)
    (completedScalarExtensionRestrictionEquiv σ x B)
    (scalarExtensionSubspaceOrderIso_finrank σ B).symm
    ((isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
      (map_zero (algEquivCompletedFields S σ x)))
    (ξ.hermitianScalarExtension_restrict_norm_algEquiv hN hH σ x B)
    (fun w ε hε => η.exists_smul_determinant_ιMulti_norm_lt (pullbackAlgEquiv S σ x) w hε)
    (fun w ε hε => θ.exists_smul_determinant_ιMulti_norm_lt x w hε)
    (η.determinant_norm_ιMulti_le (pullbackAlgEquiv S σ x))
    (θ.determinant_norm_ιMulti_le x) z

/-- On every scalar tensor, completed determinant transport is the prescribed
rational determinant transport and preserves its genuine Hermitian norm. -/
theorem hermitianScalarExtension_restrict_determinant_norm_tmul_algEquiv (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ξ.IsHermitian hN) (σ : L ≃ₐ[K] L) (x : S.ParameterSpaceExtension L)
    (B : Submodule L (L ⊗[K] E))
    (a : (pullbackAlgEquiv S σ x).abv.Completion)
    (z : ⋀[L]^(Module.finrank L B) B) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    ((ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
        (scalarExtensionSubspaceOrderIso (E := E) σ B)).determinant.norm x
          (algEquivCompletedFields S σ x a ⊗ₜ[L]
            determinantSemilinearEquiv σ.toRingEquiv
              (scalarExtensionSubspaceSemilinearEquiv σ B)
              (scalarExtensionSubspaceOrderIso_finrank σ B).symm z) =
      ((ξ.hermitianScalarExtension hN
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
          B).determinant.norm (pullbackAlgEquiv S σ x) (a ⊗ₜ[L] z) := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let C := scalarExtensionSubspaceOrderIso (E := E) σ B
  let p : (x.abv.Completion ⊗[L] (⋀[L]^(Module.finrank L C) C)) → ℝ :=
    ((ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
        C).determinant.norm x
  have ht := completedDeterminantSemilinearEquiv_tmul σ.toRingEquiv
    (algEquivCompletedFields S σ x).toRingEquiv
    (scalarExtensionSubspaceSemilinearEquiv σ B)
    (completedScalarExtensionRestrictionEquiv σ x B)
    (scalarExtensionSubspaceOrderIso_finrank σ B).symm
    (algEquivCompletedFields_algebraMap S σ x)
    (completedScalarExtensionRestrictionEquiv_tmul σ x B) a z
  exact (congrArg p ht).symm.trans
    (ξ.hermitianScalarExtension_restrict_determinant_norm_algEquiv hN hH σ x B (a ⊗ₜ[L] z))

local instance hermitianGaloisScalarNormMeasurableSpace :
    MeasurableSpace (S.ParameterSpaceExtension L) :=
  (S.algebraicExtension L).instMeasurableSpaceΩ

/-- Genuine place-measure transport preserves the actual rational determinant
logarithm integral of every Hermitian restriction, in every rank. -/
theorem hermitianScalarExtension_restrict_determinant_integral_logNorm_algEquiv
    (ξ : NormFamily S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hH : ξ.IsHermitian hN) (σ : L ≃ₐ[K] L)
    (B : Submodule L (L ⊗[K] E)) (z : ⋀[L]^(Module.finrank L B) B) :
    letI := RingHomInvPair.of_ringEquiv σ.toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
    (∫ x, ((ξ.hermitianScalarExtension hN
      (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
        (scalarExtensionSubspaceOrderIso (E := E) σ B)).determinant.logNorm
          (determinantSemilinearEquiv σ.toRingEquiv
            (scalarExtensionSubspaceSemilinearEquiv σ B)
            (scalarExtensionSubspaceOrderIso_finrank σ B).symm z) x
              ∂(S.algebraicExtension L).v) =
      ∫ y, ((ξ.hermitianScalarExtension hN
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
          B).determinant.logNorm z y ∂(S.algebraicExtension L).v := by
  let := RingHomInvPair.of_ringEquiv σ.toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv
  let η := (ξ.hermitianScalarExtension hN
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict B
  let θ := (ξ.hermitianScalarExtension hN
    (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) hH).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)
  let d := determinantSemilinearEquiv σ.toRingEquiv
    (scalarExtensionSubspaceSemilinearEquiv σ B)
    (scalarExtensionSubspaceOrderIso_finrank σ B).symm
  change (∫ x, θ.determinant.logNorm (d z) x ∂(S.algebraicExtension L).v) =
    ∫ y, η.determinant.logNorm z y ∂(S.algebraicExtension L).v
  have hn (x : S.ParameterSpaceExtension L) :
      θ.determinant.logNorm (d z) x = η.determinant.logNorm z (pullbackAlgEquiv S σ x) := by
    change Real.log (θ.determinant.norm x (1 ⊗ₜ[L] d z)) =
      Real.log (η.determinant.norm (pullbackAlgEquiv S σ x) (1 ⊗ₜ[L] z))
    have h := ξ.hermitianScalarExtension_restrict_determinant_norm_tmul_algEquiv
      hN hH σ x B 1 z
    simp only [map_one] at h
    exact congrArg Real.log h
  calc
    (∫ x, θ.determinant.logNorm (d z) x ∂(S.algebraicExtension L).v) =
        ∫ x, η.determinant.logNorm z (pullbackAlgEquiv S σ x)
          ∂(S.algebraicExtension L).v := integral_congr_ae (Filter.Eventually.of_forall hn)
    _ = ∫ y, η.determinant.logNorm z y ∂(S.algebraicExtension L).v :=
      (AdelicStructure.Algebraic.measurePreserving_algEquivMeasurableEquiv S σ).integral_comp
        (algEquivMeasurableEquiv S σ).measurableEmbedding _

end NormFamily

end ArakelovGeometry
