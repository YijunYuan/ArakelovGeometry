/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.Analysis.Tensor.CountableTensorFormula
import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Countable projective tensor and determinant measurability

One countable dense rational subfield supplies countable exact tensor
decompositions. Their cost infimum proves projective tensor measurability;
the actual projective top tensor quotient then gives determinant measurability.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u v w wι wκ

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- Enlarging the rational subfield retains its actual density in a completion. -/
theorem AdelicStructure.IsDenseSubfieldAt.mono {K₀ K₁ : Subfield K} {ω : S.Ω}
    (h : S.IsDenseSubfieldAt K₀ ω) (hle : K₀ ≤ K₁) : S.IsDenseSubfieldAt K₁ ω := by
  apply Dense.mono (hd := h)
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨a.val, hle a.property⟩, rfl⟩

/-- One enlarged countable subfield contains every coordinate of a fixed
rational tensor and remains dense at every place. -/
theorem exists_countable_dense_subfield_tensor_coordinates
    {ι : Type wι} [Finite ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    {κ : ι → Type wκ} [∀ i, Finite (κ i)]
    (b : ∀ i, Module.Basis (κ i) K (E i)) (z : ⨂[K] i, E i)
    (hS : S.HasCommonCountableDenseSubfield) :
    ∃ K₁ : Subfield K, Countable K₁ ∧ (∀ ω, S.IsDenseSubfieldAt K₁ ω) ∧
      ∀ j, (Basis.piTensorProduct b).equivFun z j ∈ K₁ := by
  obtain ⟨K₀, hcount, hK₀⟩ := hS
  let : Countable K₀ := hcount
  obtain ⟨K₁, hcount₁, hle, hcoord⟩ :=
    exists_countable_subfield_ge_range K₀ ((Basis.piTensorProduct b).equivFun z)
  exact ⟨K₁, hcount₁, fun ω => (hK₀ ω).mono hle, hcoord⟩

noncomputable section

namespace NormFamily

variable {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  {κ : ι → Type wκ} [∀ i, Fintype (κ i)]
  (b : ∀ i, Module.Basis (κ i) K (E i))

/-- Completed scalar extension carries rational tensor coordinates to their
actual images in the completed ground field. -/
theorem tensorBaseChange_tensorFromCoordinates (K₀ : Subfield K)
    (c : (∀ i, κ i) → K₀) (ω : S.Ω) :
    tensorBaseChangeEquiv K (S.ϕ ω).Completion E
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] tensorFromCoordinates b K₀.subtype c) =
      tensorFromCoordinates (fun i => (b i).baseChange (S.ϕ ω).Completion)
        ((algebraMap K (S.ϕ ω).Completion).comp K₀.subtype) c := by
  apply (Basis.piTensorProduct (fun i => (b i).baseChange (S.ϕ ω).Completion)).equivFun.injective
  ext j
  rw [tensorBaseChange_equivFun]
  simp only [tensorFromCoordinates, Module.Basis.equivFun_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  change algebraMap K (S.ϕ ω).Completion
    ((Basis.piTensorProduct b).equivFun ((Basis.piTensorProduct b).equivFun.symm
      (fun j => K₀.subtype (c j))) j) =
      (Basis.piTensorProduct (fun i => (b i).baseChange (S.ϕ ω).Completion)).equivFun
        ((Basis.piTensorProduct (fun i => (b i).baseChange (S.ϕ ω).Completion)).equivFun.symm
          (fun j => ((algebraMap K (S.ϕ ω).Completion).comp K₀.subtype) (c j))) j
  simp only [LinearEquiv.apply_symm_apply, RingHom.comp_apply]

variable [∀ i, FiniteDimensional K (E i)] (ξ : ∀ i, NormFamily S (E i))

/-- The completed projective norm has an exact subfield decomposition formula
whose indexing type and rational vectors are independent of the place. -/
theorem projectiveTensor_norm_tensorFromCoordinates_eq_iInf (K₀ : Subfield K)
    (c : (∀ i, κ i) → K₀) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω) :
    (projectiveTensor ξ).norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] tensorFromCoordinates b K₀.subtype c) =
      ⨅ p : {p : List (K₀ × (∀ i, κ i → K₀)) // tensorCoordinateCoefficients p = c},
        (p.val.map fun q => (S.ϕ ω) (q.1 : K) *
          ∏ i, (ξ i).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
            basisSubfieldMap (b i) K₀ (q.2 i))).sum := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let B := fun i => (b i).baseChange (S.ϕ ω).Completion
  let σ := (algebraMap K (S.ϕ ω).Completion).comp K₀.subtype
  change PiTensorProduct.projectiveSeminorm (tensorBaseChangeEquiv K (S.ϕ ω).Completion E
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] tensorFromCoordinates b K₀.subtype c)) = _
  rw [tensorBaseChange_tensorFromCoordinates,
    projectiveSeminorm_eq_iInf_tensorCoordinateCost B σ hK₀]
  congr 1
  funext p
  have hv (x : ∀ i, κ i → K₀) (i : ι) :
      tensorCoordinateVector B σ x i =
        (1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap (b i) K₀ (x i) :=
    (basisSubfieldMap_tmul (b i) K₀ ω (x i)).symm
  simp only [tensorCoordinateCost, hv, σ, RingHom.comp_apply,
    S.norm_algebraMap_eq_absValue]
  rfl

/-- Measurable factors have a measurable actual projective tensor norm whenever
one countable rational subfield is dense in every completed ground field. -/
theorem IsMeasurable.projectiveTensor_of_common_countable_dense_subfield
    (hξ : ∀ i, (ξ i).IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    (projectiveTensor ξ).IsMeasurable := by
  classical
  intro z
  let b := fun i => Module.finBasis K (E i)
  obtain ⟨K₁, hcount, hdense, hcoord⟩ :=
    exists_countable_dense_subfield_tensor_coordinates b z hS
  let : Countable K₁ := hcount
  let c : (∀ i, Fin (Module.finrank K (E i))) → K₁ :=
    fun j => ⟨(Basis.piTensorProduct b).equivFun z j, hcoord j⟩
  have hz : tensorFromCoordinates b K₁.subtype c = z := by
    apply (Basis.piTensorProduct b).equivFun.injective
    simp only [tensorFromCoordinates, LinearEquiv.apply_symm_apply]
    rfl
  rw [← hz]
  simp_rw [projectiveTensor_norm_tensorFromCoordinates_eq_iInf b ξ K₁ c _ (hdense _)]
  apply Measurable.iInf
  intro p
  induction p.val with
  | nil => exact measurable_const
  | cons q p hp =>
    simp only [List.map_cons, List.sum_cons]
    apply Measurable.add _ hp
    exact (S.measurable_absValue (q.1 : K)).mul
      (Finset.measurable_prod _ (fun i _ => hξ i (basisSubfieldMap (b i) K₁ (q.2 i))))

end NormFamily

namespace NormFamily

variable {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The actual determinant family is measurable as the quotient of the
projective top tensor power, including in dimension zero. -/
theorem IsMeasurable.determinant_of_common_countable_dense_subfield
    {η : NormFamily S F} (hη : η.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    η.determinant.IsMeasurable := by
  have hπ := IsMeasurable.projectiveTensor_of_common_countable_dense_subfield
    (fun _ : Fin (Module.finrank K F) => η) (fun _ => hη) hS
  exact hπ.pushforward_of_common_countable_dense_subfield
      (tensorToExterior K F (Module.finrank K F))
      (tensorToExterior_surjective K F (Module.finrank K F)) hS

end NormFamily

end

end ArakelovGeometry
