/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction

/-!
# The actual coherent rational generic fibre

The actual integer ring localized at nonzero integers is the number field.
Its genuine localization pushout cancels the base change from the integers
to the rationals. Under finite-exception coherence the resulting canonical
rational generic map is an equivalence in every rank.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- The actual integer-ring embedding respects the canonical integer action. -/
instance integerRing_field_intScalarTower : IsScalarTower ℤ (𝓞 K) K :=
  IsScalarTower.of_algebraMap_eq fun a => by simp

/-- Localizing actual integers at the images of nonzero integers gives `K`. -/
theorem integerRing_nonzeroInt_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) (nonZeroDivisors ℤ)) K :=
  inferInstance

/-- The actual integer localization square is a genuine pushout. -/
theorem integerRing_rationalIsPushout : Algebra.IsPushout ℤ ℚ (𝓞 K) K := by
  let := integerRing_nonzeroInt_isLocalization (K := K)
  exact (Algebra.IsPushout.comm ℤ ℚ (𝓞 K) K).mpr
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors ℤ) ℚ (𝓞 K) K)

/-- The actual rational scalar extension of the integer ring is the field. -/
def integerRingRationalTensorEquiv : ℚ ⊗[ℤ] (𝓞 K) ≃ₐ[ℚ] K :=
  letI := integerRing_rationalIsPushout (K := K)
  Algebra.IsPushout.equiv ℤ ℚ (𝓞 K) K

@[simp]
theorem integerRingRationalTensorEquiv_tmul (q : ℚ) (a : 𝓞 K) :
    integerRingRationalTensorEquiv (q ⊗ₜ[ℤ] a) =
      algebraMap ℚ K q * algebraMap (𝓞 K) K a := by
  let := integerRing_rationalIsPushout (K := K)
  exact Algebra.IsPushout.equiv_tmul ℤ ℚ (𝓞 K) K q a

local notation "N" => normalizedNumberFieldAdelicStructure K

attribute [local instance] RestrictScalars.moduleOrig

local instance : Module ℤ (RestrictScalars ℚ K E) :=
  inferInstanceAs (Module ℤ E)

local instance : IsScalarTower ℤ ℚ (RestrictScalars ℚ K E) :=
  @AddCommGroup.intIsScalarTower ℚ (RestrictScalars ℚ K E) _ _
    (RestrictScalars.module ℚ K E)

/-- The literal global inclusion, with the canonical rational restricted target. -/
def normalizedGlobalRationalInclusion (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) :
    ξ.globalUnitBallModule hξ →ₗ[ℤ] RestrictScalars ℚ K E :=
  (ξ.globalUnitBallModule hξ).subtype.restrictScalars ℤ

@[simp]
theorem normalizedGlobalRationalInclusion_coe (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (x : ξ.globalUnitBallModule hξ) :
    RestrictScalars.addEquiv ℚ K E (ξ.normalizedGlobalRationalInclusion hξ x) =
      (x : E) := rfl

/-- The original canonical rational tensor map, without a coherence input. -/
def normalizedGlobalRationalGenericFibreMap (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) :
    ℚ ⊗[ℤ] (ξ.globalUnitBallModule hξ) →ₗ[ℚ] RestrictScalars ℚ K E :=
  (ξ.normalizedGlobalRationalInclusion hξ).liftBaseChange ℚ

@[simp]
theorem normalizedGlobalRationalGenericFibreMap_tmul (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) (q : ℚ) (x : ξ.globalUnitBallModule hξ) :
    RestrictScalars.addEquiv ℚ K E
      (ξ.normalizedGlobalRationalGenericFibreMap hξ (q ⊗ₜ[ℤ] x)) =
      algebraMap ℚ K q • (x : E) := by
  rw [normalizedGlobalRationalGenericFibreMap, LinearMap.liftBaseChange_tmul,
    RestrictScalars.addEquiv_map_smul, normalizedGlobalRationalInclusion_coe]

/-- Genuine coherence identifies the actual rational scalar extension with `E`. -/
def HasFiniteNormExceptions.normalizedGlobalRationalGenericFibreEquiv
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    ℚ ⊗[ℤ] (ξ.globalUnitBallModule hξ) ≃ₗ[ℚ] RestrictScalars ℚ K E := by
  letI := integerRing_rationalIsPushout (K := K)
  let e : K ⊗[𝓞 K] (ξ.globalUnitBallModule hξ) ≃ₗ[K] RestrictScalars ℚ K E :=
    hfinite.normalizedGlobalGenericFibreEquiv hξ
  exact (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 K) K
    (ξ.globalUnitBallModule hξ)).symm.trans (e.restrictScalars ℚ)

@[simp]
theorem HasFiniteNormExceptions.normalizedGlobalRationalGenericFibreEquiv_tmul
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (q : ℚ) (x : ξ.globalUnitBallModule hξ) :
    RestrictScalars.addEquiv ℚ K E
      (hfinite.normalizedGlobalRationalGenericFibreEquiv hξ (q ⊗ₜ[ℤ] x)) =
      algebraMap ℚ K q • (x : E) := by
  let := integerRing_rationalIsPushout (K := K)
  change (hfinite.normalizedGlobalGenericFibreEquiv hξ)
    ((Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 K) K
      (ξ.globalUnitBallModule hξ)).symm (q ⊗ₜ[ℤ] x)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  exact hfinite.normalizedGlobalGenericFibreEquiv_tmul hξ (algebraMap ℚ K q) x

/-- The genuine coherent equivalence is the original canonical rational map. -/
theorem HasFiniteNormExceptions.normalizedGlobalRationalGenericFibreEquiv_coe
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    (hfinite.normalizedGlobalRationalGenericFibreEquiv hξ).toLinearMap =
      ξ.normalizedGlobalRationalGenericFibreMap hξ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  apply (RestrictScalars.addEquiv ℚ K E).injective
  exact (hfinite.normalizedGlobalRationalGenericFibreEquiv_tmul hξ q x).trans
    (ξ.normalizedGlobalRationalGenericFibreMap_tmul hξ q x).symm

/-- Under genuine coherence the original rational generic map is bijective. -/
theorem HasFiniteNormExceptions.normalizedGlobalRationalGenericFibreMap_bijective
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    Function.Bijective (ξ.normalizedGlobalRationalGenericFibreMap hξ) := by
  rw [← hfinite.normalizedGlobalRationalGenericFibreEquiv_coe hξ]
  exact (hfinite.normalizedGlobalRationalGenericFibreEquiv hξ).bijective

/-- The original canonical map in the source's right-tensor convention. -/
def normalizedGlobalRightRationalGenericFibreMap (ξ : NormFamily (N) E)
    (hξ : ξ.IsUltrametric) :
    (ξ.globalUnitBallModule hξ) ⊗[ℤ] ℚ →ₗ[ℤ] RestrictScalars ℚ K E :=
  ((ξ.normalizedGlobalRationalGenericFibreMap hξ).restrictScalars ℤ).comp
    (TensorProduct.comm ℤ (ξ.globalUnitBallModule hξ) ℚ).toLinearMap

@[simp]
theorem normalizedGlobalRightRationalGenericFibreMap_tmul
    (ξ : NormFamily (N) E) (hξ : ξ.IsUltrametric)
    (x : ξ.globalUnitBallModule hξ) (q : ℚ) :
    RestrictScalars.addEquiv ℚ K E
      (ξ.normalizedGlobalRightRationalGenericFibreMap hξ (x ⊗ₜ[ℤ] q)) =
      algebraMap ℚ K q • (x : E) :=
  ξ.normalizedGlobalRationalGenericFibreMap_tmul hξ q x

/-- The source's right-tensor generic fibre, through canonical commutation. -/
def HasFiniteNormExceptions.normalizedGlobalRightRationalGenericFibreEquiv
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    (ξ.globalUnitBallModule hξ) ⊗[ℤ] ℚ ≃ₗ[ℤ] RestrictScalars ℚ K E :=
  (TensorProduct.comm ℤ (ξ.globalUnitBallModule hξ) ℚ).trans
    ((hfinite.normalizedGlobalRationalGenericFibreEquiv hξ).restrictScalars ℤ)

@[simp]
theorem HasFiniteNormExceptions.normalizedGlobalRightRationalGenericFibreEquiv_tmul
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) (x : ξ.globalUnitBallModule hξ) (q : ℚ) :
    RestrictScalars.addEquiv ℚ K E
      (hfinite.normalizedGlobalRightRationalGenericFibreEquiv hξ (x ⊗ₜ[ℤ] q)) =
      algebraMap ℚ K q • (x : E) :=
  hfinite.normalizedGlobalRationalGenericFibreEquiv_tmul hξ q x

/-- The coherent right-tensor equivalence is the original canonical map. -/
theorem HasFiniteNormExceptions.normalizedGlobalRightRationalGenericFibreEquiv_coe
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    (hfinite.normalizedGlobalRightRationalGenericFibreEquiv hξ).toLinearMap =
      ξ.normalizedGlobalRightRationalGenericFibreMap hξ := by
  apply LinearMap.ext
  intro t
  exact congrArg (fun f : ℚ ⊗[ℤ] (ξ.globalUnitBallModule hξ) →ₗ[ℚ]
    RestrictScalars ℚ K E => f (TensorProduct.comm ℤ (ξ.globalUnitBallModule hξ) ℚ t))
      (hfinite.normalizedGlobalRationalGenericFibreEquiv_coe hξ)

/-- The literal source-order canonical rational tensor map is bijective. -/
theorem HasFiniteNormExceptions.normalizedGlobalRightRationalGenericFibreMap_bijective
    {ξ : NormFamily (N) E} (hfinite : ξ.HasFiniteNormExceptions)
    (hξ : ξ.IsUltrametric) :
    Function.Bijective (ξ.normalizedGlobalRightRationalGenericFibreMap hξ) := by
  rw [← hfinite.normalizedGlobalRightRationalGenericFibreEquiv_coe hξ]
  exact (hfinite.normalizedGlobalRightRationalGenericFibreEquiv hξ).bijective

end ArakelovGeometry.NormFamily
