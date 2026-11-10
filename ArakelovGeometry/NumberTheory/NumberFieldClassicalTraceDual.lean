/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldProjectiveTraceDualGeneric

/-! # Original classical trace tensors and integer biduality

The original codifferent tensor is finite projective, has the original generic
rank, and its second trace tensor is the original integer bidual. The metric
involution is a separate assertion.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.NumberFieldClassicalTraceDual

open NumberField AdelicStructure
open NumberFieldCodifferentDual NumberFieldProjectiveTraceDual
  NumberFieldProjectiveTraceDualGeneric NumberFieldProjectiveGeneric
open NumberFieldInvertibleGeneric (genericImage)
open scoped TensorProduct

universe u
variable {K : Type u} [Field K] [NumberField K]
  (M : Type u) [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

attribute [local instance] genericFiniteDimensional
attribute [local instance 2000] integralVectorModule

/-- The original codifferent tensor is finite over the original integer ring,
by its actual integer trace-dual equivalence. -/
theorem traceTensor_finite :
    Module.Finite (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  let : Module.Finite ℤ T := Module.Finite.equiv (integerTensorEquiv (K := K) M).symm
  exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) T

attribute [local instance] traceTensor_finite

/-- The original trace tensor is projective via its literal finite trace-integral
submodule of the original generic dual. -/
theorem traceTensor_projective :
    Module.Projective (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) := by
  let D := NumberFieldIntegralTraceDual.integralTraceDual (genericImage (K := K) M)
  let e : (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) ≃ₗ[𝓞 K] D :=
    traceTensorEquiv (K := K) M
  let : Module.Finite (𝓞 K) D := Module.Finite.equiv e
  let : Module.Projective (𝓞 K) D :=
    NumberFieldFullLattice.projective D (Submodule.FG.of_finite (N := D))
  exact Module.Projective.of_equiv e.symm

attribute [local instance] traceTensor_projective

/-- Scalar multiplication is adjoint in the original integer trace pairing. -/
theorem integerTensorEquiv_smul_pairing (a : 𝓞 K)
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) (m : M) :
    integerTensorEquiv (K := K) M (a • z) m = integerTensorEquiv (K := K) M z (a • m) := by
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [smul_add, map_add, LinearMap.add_apply, hz, ht]
  | tmul b f =>
      apply (Int.cast_injective (α := ℚ))
      rw [TensorProduct.smul_tmul', integerTensorEquiv_tmul_apply,
        integerTensorEquiv_tmul_apply]
      congr 1
      simp only [map_smul, smul_eq_mul, map_mul, Submodule.coe_smul]
      change (algebraMap (𝓞 K) K (f m)) * (algebraMap (𝓞 K) K a * (b : K)) = _
      ring

/-- The actual generic trace tensor has exactly the original generic rank. -/
theorem traceTensor_generic_finrank :
    Module.finrank K (K ⊗[𝓞 K] (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) =
      Module.finrank K (K ⊗[𝓞 K] M) := by
  erw [(traceTensorGenericPairEquiv (K := K) M).finrank_eq,
    Module.finrank_tensorProduct, Module.finrank_self, mul_one]
  exact Subspace.dual_finrank_eq

include K in
/-- The original module is integer free via its literal generic full-lattice image. -/
theorem originalModule_free_integer : Module.Free ℤ M := by
  let := NumberFieldFullLattice.free_integer (genericImage (K := K) M)
    (genericImage_fg (K := K) M)
  exact Module.Free.of_equiv ((genericImageEquiv (K := K) M).symm.restrictScalars ℤ)

/-- Actual integer trace biduality, on the original double codifferent tensor.
This map carries no assertion about the infinite-place metrics. -/
def integerTraceBidualEquiv :
    (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗ[ℤ] M := by
  let T := codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M
  let : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  let : Module.Free ℤ M := originalModule_free_integer (K := K) M
  exact ((integerTensorEquiv (K := K) T).trans
    (integerTensorEquiv (K := K) M).symm.dualMap).trans (Module.evalEquiv ℤ M).symm

/-- The constructed integer bidual identification is characterized by the actual
trace-evaluation pairing, not an arbitrary abstract module isomorphism. -/
theorem integerTraceBidualEquiv_pairing
    (t : codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M))
    (z : codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) :
    integerTensorEquiv (K := K) M z (integerTraceBidualEquiv M t) =
      integerTensorEquiv (K := K)
        (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M) t z := by
  let : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  let : Module.Free ℤ M := originalModule_free_integer (K := K) M
  simp only [integerTraceBidualEquiv, LinearEquiv.trans_apply,
    Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply,
    LinearEquiv.symm_apply_apply]

/-- Actual integer trace biduality respects the original integer-ring scalar action. -/
theorem integerTraceBidualEquiv_smul (a : 𝓞 K)
    (t : codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) :
    integerTraceBidualEquiv M (a • t) = a • integerTraceBidualEquiv M t := by
  let : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  let : Module.Free ℤ M := originalModule_free_integer (K := K) M
  apply (Module.evalEquiv ℤ M).injective
  apply LinearMap.ext
  intro f
  obtain ⟨z, rfl⟩ := (integerTensorEquiv (K := K) M).surjective f
  change integerTensorEquiv (K := K) M z (integerTraceBidualEquiv M (a • t)) =
    integerTensorEquiv (K := K) M z (a • integerTraceBidualEquiv M t)
  rw [integerTraceBidualEquiv_pairing,
    integerTensorEquiv_smul_pairing, ← integerTraceBidualEquiv_pairing,
    integerTensorEquiv_smul_pairing]

/-- The actual double codifferent tensor is canonically the original module over
the original integer ring, with its actual trace-evaluation characterization. -/
def traceBidualEquiv :
    (codifferentModule K ⊗[𝓞 K]
      Module.Dual (𝓞 K) (codifferentModule K ⊗[𝓞 K] Module.Dual (𝓞 K) M)) ≃ₗ[𝓞 K] M :=
  { (integerTraceBidualEquiv M).toAddEquiv with
    map_smul' := integerTraceBidualEquiv_smul M }

end ArakelovGeometry.NumberFieldClassicalTraceDual
