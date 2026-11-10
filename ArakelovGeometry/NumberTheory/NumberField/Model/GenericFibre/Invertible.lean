/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.PrincipalFrame
public import Mathlib.RingTheory.PicardGroup
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Index.BoundedElement
import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.FullLatticeIndex
import Mathlib.Topology.Sheaves.Init

/-!
# Original invertible modules in their actual generic and completed fibres

The canonical original module tensor inclusion is injective, and its literal
integral image is a full line. Actual completed tensor images coincide in both
orientations with the canonical completed image lattice. Its gauges read the
original cyclic quotient, with positive finite cardinality proved separately.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct nonZeroDivisors
noncomputable section

namespace ArakelovGeometry.NumberFieldInvertibleGeneric

open AdelicStructure ActualPrimeIndexing
attribute [local instance 2000] integralVectorModule

variable {K : Type*} [Field K] [NumberField K]
  (M : Type*) [AddCommGroup M] [Module (𝓞 K) M] [Module.Invertible (𝓞 K) M]

/-- The actual original integral-module inclusion in its canonical generic tensor fibre. -/
def genericInclusion : M →ₗ[𝓞 K] K ⊗[𝓞 K] M := TensorProduct.mk (𝓞 K) K M 1

omit [NumberField K] [Module.Invertible (𝓞 K) M] in
@[simp]
theorem genericInclusion_apply (m : M) : genericInclusion (K := K) M m = (1 : K) ⊗ₜ[𝓞 K] m := rfl

/-- The source's original right-tensor inclusion, with the original integral action. -/
def genericRightInclusion : M →ₗ[𝓞 K] M ⊗[𝓞 K] K :=
  (TensorProduct.comm (𝓞 K) K M).toLinearMap.comp (genericInclusion (K := K) M)

omit [NumberField K] [Module.Invertible (𝓞 K) M] in
/-- The source right inclusion is the literal original tensor. -/
@[simp]
theorem genericRightInclusion_apply (m : M) :
    genericRightInclusion (K := K) M m = m ⊗ₜ[𝓞 K] (1 : K) := rfl

omit [NumberField K] [Module.Invertible (𝓞 K) M] in
/-- Literal commutation identifies the two original inclusions. -/
theorem genericRightInclusion_comm (m : M) :
    TensorProduct.comm (𝓞 K) M K (genericRightInclusion (K := K) M m) =
      genericInclusion (K := K) M m :=
  rfl

/-- The original integral image is a literal submodule of the actual generic tensor fibre. -/
def genericImage : Submodule (𝓞 K) (K ⊗[𝓞 K] M) := (genericInclusion (K := K) M).range

/-- Tensoring the original coefficient inclusion by an invertible module stays injective. -/
theorem genericInclusion_injective : Function.Injective (genericInclusion (K := K) M) := by
  have hf : Function.Injective (Algebra.linearMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have ht := (Module.Invertible.rTensor_injective_iff M).mpr hf
  have he : genericInclusion (K := K) M = ((Algebra.linearMap (𝓞 K) K).rTensor M).comp
      (TensorProduct.lid (𝓞 K) M).symm.toLinearMap := by
    ext m
    rfl
  rw [he]
  exact ht.comp (TensorProduct.lid (𝓞 K) M).symm.injective

/-- Injectivity in the source's original right-tensor orientation is also derived. -/
theorem genericRightInclusion_injective : Function.Injective (genericRightInclusion (K := K) M) :=
  (TensorProduct.comm (𝓞 K) K M).injective.comp (genericInclusion_injective (K := K) M)

/-- The canonical inclusion gives an actual equivalence with its literal original image. -/
def genericImageEquiv : M ≃ₗ[𝓞 K] genericImage (K := K) M :=
  LinearEquiv.ofInjective (genericInclusion (K := K) M) (genericInclusion_injective (K := K) M)

@[simp]
theorem genericImageEquiv_coe (m : M) :
    (genericImageEquiv (K := K) M m : K ⊗[𝓞 K] M) = genericInclusion (K := K) M m := rfl

omit [NumberField K] in
/-- The actual generic tensor fibre has dimension one, rather than an assumed rank certificate. -/
theorem generic_finrank : Module.finrank K (K ⊗[𝓞 K] M) = 1 :=
  Module.Invertible.finrank_eq_one K (K ⊗[𝓞 K] M)

omit [NumberField K] in
/-- The original image is finitely generated because the original invertible module is finite. -/
theorem genericImage_fg : (genericImage (K := K) M).FG := by
  rw [genericImage, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

omit [NumberField K] [Module.Invertible (𝓞 K) M] in
/-- The actual original image spans its generic fibre, by literal tensor induction. -/
theorem genericImage_fullSpan :
    Submodule.span K (genericImage (K := K) M : Set (K ⊗[𝓞 K] M)) = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    have h := (Submodule.span K (genericImage (K := K) M : Set (K ⊗[𝓞 K] M))).smul_mem a
      (Submodule.subset_span
        (show genericInclusion (K := K) M m ∈ genericImage (K := K) M from ⟨m, rfl⟩))
    simpa only [genericInclusion_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

local notation "Kᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AbsoluteValue.Completion
    (AdelicStructure.ϕ (normalizedNumberFieldAdelicStructure K) (normalizedPrimeParameter p)))
local notation "𝓞ᵥ" => (fun p : HeightOneSpectrum (𝓞 K) ↦
  AdelicStructure.completedLocalRing (normalizedNumberFieldAdelicStructure K)
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p))

/-- Scalar extension of the original inclusion into the actual completed generic tensor fibre. -/
def completedTensorMap (p : HeightOneSpectrum (𝓞 K)) :
    (𝓞ᵥ p) ⊗[𝓞 K] M →ₗ[𝓞ᵥ p] Kᵥ p ⊗[K] (K ⊗[𝓞 K] M) :=
  (NumberFieldModel.completedLatticeTensorMap (genericImage (K := K) M) p).comp
    (LinearEquiv.baseChange (𝓞 K) (𝓞ᵥ p) M (genericImage (K := K) M)
      (genericImageEquiv (K := K) M)).toLinearMap

/-- The completed map has the literal original scalar tensor formula. -/
theorem completedTensorMap_tmul (p : HeightOneSpectrum (𝓞 K)) (a : 𝓞ᵥ p) (m : M) :
    completedTensorMap (K := K) M p (a ⊗ₜ[𝓞 K] m) =
      (a : Kᵥ p) ⊗ₜ[K] (genericInclusion (K := K) M m) := by
  simp only [completedTensorMap, LinearMap.comp_apply, LinearEquiv.coe_baseChange,
    LinearMap.baseChange_tmul,
    NumberFieldModel.completedLatticeTensorMap_tmul]
  rfl

/-- The original completed tensor range is the canonical completed image lattice, literally. -/
theorem completedTensorMap_range (p : HeightOneSpectrum (𝓞 K)) :
    (completedTensorMap (K := K) M p).range =
      NumberFieldModel.completedLatticeSpan (genericImage (K := K) M) p := by
  rw [completedTensorMap, LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.baseChange (𝓞 K) (𝓞ᵥ p) M (genericImage (K := K) M)
      (genericImageEquiv (K := K) M)).range]
  exact NumberFieldModel.range_completedLatticeTensorMap (genericImage (K := K) M) p

/-- The source's original completed right-tensor map, through literal commutation. -/
def completedRightTensorMap (p : HeightOneSpectrum (𝓞 K)) :
    M ⊗[𝓞 K] (𝓞ᵥ p) →ₗ[𝓞 K] Kᵥ p ⊗[K] (K ⊗[𝓞 K] M) :=
  -- Explicit compatibility reconciles the definitionally equal integral scalar actions.
  let h : LinearMap.CompatibleSMul ((𝓞ᵥ p) ⊗[𝓞 K] M)
      (Kᵥ p ⊗[K] (K ⊗[𝓞 K] M)) (𝓞 K) (𝓞ᵥ p) := by
    have : IsScalarTower (𝓞 K) (𝓞ᵥ p) (Kᵥ p ⊗[K] (K ⊗[𝓞 K] M)) :=
      NumberFieldModel.completedVector_integralScalarTower (E := K ⊗[𝓞 K] M) p
    infer_instance
  (@LinearMap.restrictScalars (𝓞 K) (𝓞ᵥ p) _ _ _ _ _ _ _ _ _ _ h
    (completedTensorMap (K := K) M p)).comp
    (TensorProduct.comm (𝓞 K) M (𝓞ᵥ p)).toLinearMap

/-- The right completed map sends the original tensor to the same completed vector. -/
theorem completedRightTensorMap_tmul (p : HeightOneSpectrum (𝓞 K)) (m : M) (a : 𝓞ᵥ p) :
    completedRightTensorMap (K := K) M p (m ⊗ₜ[𝓞 K] a) =
      (a : Kᵥ p) ⊗ₜ[K] (genericInclusion (K := K) M m) :=
  completedTensorMap_tmul (K := K) M p a m

/-- Both original completed tensor orientations have exactly the same image set. -/
theorem completedRightTensorMap_range (p : HeightOneSpectrum (𝓞 K)) :
    Set.range (completedRightTensorMap (K := K) M p) =
      ((completedTensorMap (K := K) M p).range : Set _) := by
  change Set.range ((completedTensorMap (K := K) M p) ∘ (TensorProduct.comm (𝓞 K) M (𝓞ᵥ p))) = _
  rw [Set.range_comp, (TensorProduct.comm (𝓞 K) M (𝓞ᵥ p)).surjective.range_eq]
  simp only [Set.image_univ, LinearMap.coe_range]

/-- Every original nonzero element has a positive actual cyclic quotient cardinality. -/
theorem cyclicQuotient_card_pos (m : M) (hm : m ≠ 0) :
    0 < Nat.card (M ⧸ Submodule.span (𝓞 K) {m}) := by
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq (genericImageEquiv (K := K) M) m]
  exact NumberFieldFullLattice.line_cyclicQuotient_card_pos (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (generic_finrank (K := K) M) (genericImageEquiv (K := K) M m)
    (fun h => hm ((genericImageEquiv (K := K) M).injective (h.trans (map_zero _).symm)))

/-- Finiteness is derived for every actual original invertible-module cyclic quotient. -/
theorem cyclicQuotient_finite (m : M) (hm : m ≠ 0) :
    Finite (M ⧸ Submodule.span (𝓞 K) {m}) :=
  Nat.finite_of_card_ne_zero (cyclicQuotient_card_pos (K := K) M m hm).ne'

/-- The original completed tensor gauges recover the original invertible-module index. -/
theorem completedGauge_finite_log_index (m : M) (hm : m ≠ 0) :
    (∑' p : HeightOneSpectrum (𝓞 K),
      (normalizedNumberFieldAdelicStructure K).v.real {normalizedPrimeParameter p} *
        (-Real.log (scalarLatticeGauge (F := Kᵥ p) ((completedTensorMap (K := K) M p).range : Set _)
          ((1 : Kᵥ p) ⊗ₜ[K] (genericInclusion (K := K) M m))))) =
      Real.log (Nat.card (M ⧸ Submodule.span (𝓞 K) {m})) := by
  have hm' : genericImageEquiv (K := K) M m ≠ 0 :=
    fun h => hm ((genericImageEquiv (K := K) M).injective (h.trans (map_zero _).symm))
  rw [NumberFieldBoundedIndex.cyclicQuotient_card_eq (genericImageEquiv (K := K) M) m]
  convert NumberFieldFullLattice.line_completedGauge_finite_log_index (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) (generic_finrank (K := K) M)
    (genericImageEquiv (K := K) M m) hm' using 1
  apply tsum_congr
  intro p
  rw [completedTensorMap_range, genericImageEquiv_coe]

/-- Nonzero original vectors have finite support of their actual completed logarithmic gauges. -/
theorem completedGauge_log_support_finite (m : M) (hm : m ≠ 0) :
    (Function.support fun p : HeightOneSpectrum (𝓞 K) =>
      Real.log (scalarLatticeGauge (F := Kᵥ p) ((completedTensorMap (K := K) M p).range : Set _)
        ((1 : Kᵥ p) ⊗ₜ[K] (genericInclusion (K := K) M m)))).Finite := by
  have hm' : genericImageEquiv (K := K) M m ≠ 0 :=
    fun h => hm ((genericImageEquiv (K := K) M).injective (h.trans (map_zero _).symm))
  have h := NumberFieldFullLattice.line_completedGauge_log_support_finite (genericImage (K := K) M)
    (genericImage_fg (K := K) M) (genericImage_fullSpan (K := K) M) (generic_finrank (K := K) M)
    (genericImageEquiv (K := K) M m) hm'
  simpa only [completedTensorMap_range, genericImageEquiv_coe] using h

end ArakelovGeometry.NumberFieldInvertibleGeneric
