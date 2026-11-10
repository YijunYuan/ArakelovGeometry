/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic
public import ArakelovGeometry.Analysis.Hermitian.Norm
public import ArakelovGeometry.Analysis.Tensor.HermitianTensor
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
import ArakelovGeometry.AdelicVectorBundle.Tensor.Domination
import ArakelovGeometry.Analysis.Tensor.InjectiveTensorPure
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Orthogonal tensor products of Hermitian norm families

The finite-place norm is injective. At infinite places the actual completed
tensor product carries the product inner product of the prescribed factor
norms. Its injective/projective comparisons supply strong domination.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- A Hermitian family gives an inner-product structure with precisely its
existing completed norm and scalar action. -/
@[instance_reducible]
def IsHermitian.fibreInnerProductSpace {V : Type w} [AddCommGroup V] [Module K V]
    {ξ : NormFamily S V}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hS) (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V) := by
  letI := hS ω hω
  letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  letI := ξ.fibreNormedAddCommGroup ω
  letI := ξ.fibreNormedSpace ω
  exact innerProductSpaceOfCoreNorm (hξ.2 ω hω).choose (hξ.2 ω hω).choose_spec

variable {ι : Type wι} [Fintype ι]
  {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  (ξ : ∀ i, NormFamily S (E i))
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hξ : ∀ i, (ξ i).IsHermitian hS)

/-- At an infinite place, transport the actual finite orthogonal tensor norm
through the canonical completed scalar-extension equivalence. -/
def orthogonalTensorArchSeminorm (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) := by
  letI := hS ω hω
  letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  letI : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  letI : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  letI : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (hξ i).fibreInnerProductSpace ω hω
  exact (ArakelovGeometry.orthogonalTensorSeminorm
    (fun i => stdOrthonormalBasis (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i))).comp
      (tensorBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap

/-- The Archimedean orthogonal tensor norm separates points in the actual completed fibre. -/
theorem orthogonalTensorArchSeminorm_eq_zero_iff (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    orthogonalTensorArchSeminorm ξ hS hξ ω hω z = 0 ↔ z = 0 := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (hξ i).fibreInnerProductSpace ω hω
  change ArakelovGeometry.orthogonalTensorSeminorm _ (tensorBaseChangeEquiv K _ E z) = 0 ↔ _
  rw [ArakelovGeometry.orthogonalTensorSeminorm_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The orthogonal tensor family from Section 4.1.1: the injective norm at
finite places and the product inner-product norm at infinite places. -/
def orthogonalTensor : NormFamily S (⨂[K] i, E i) := by
  classical
  exact
    { norm := fun ω => if hω : ω ∈ S.Ωinf then orthogonalTensorArchSeminorm ξ hS hξ ω hω
        else (injectiveTensor ξ).norm ω
      norm_eq_zero_iff := fun ω z => by
        split_ifs with hω
        · exact orthogonalTensorArchSeminorm_eq_zero_iff ξ hS hξ ω hω z
        · exact (injectiveTensor ξ).norm_eq_zero_iff ω z }

/-- At a finite place the actual orthogonal tensor norm is injective. -/
theorem orthogonalTensor_norm_of_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (orthogonalTensor ξ hS hξ).norm ω z = (injectiveTensor ξ).norm ω z := by
  have hn : ω ∉ S.Ωinf := fun h => h hω
  simp only [orthogonalTensor, dite_eq_right hn]

/-- At an infinite place the actual orthogonal tensor norm is the transported
product inner-product norm. -/
theorem orthogonalTensor_norm_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (orthogonalTensor ξ hS hξ).norm ω z = orthogonalTensorArchSeminorm ξ hS hξ ω hω z := by
  simp only [orthogonalTensor, dite_eq_left hω]

/-- The orthogonal tensor family is ultrametric at all finite places. -/
theorem orthogonalTensor_isUltrametric : (orthogonalTensor ξ hS hξ).IsUltrametric := by
  intro ω hω z t
  simp only [orthogonalTensor_norm_of_finite ξ hS hξ ω hω]
  exact injectiveTensor_isUltrametric ξ ω hω z t

/-- The actual completed orthogonal tensor norm lies between the injective
and projective norms at every place. -/
theorem orthogonalTensor_norm_bounds (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (injectiveTensor ξ).norm ω z ≤ (orthogonalTensor ξ hS hξ).norm ω z ∧
      (orthogonalTensor ξ hS hξ).norm ω z ≤ (projectiveTensor ξ).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · let := hS ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
      fun i => (ξ i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
      fun i => (ξ i).fibreNormedSpace ω
    let : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
      fun i => (hξ i).fibreInnerProductSpace ω hω
    rw [orthogonalTensor_norm_of_infinite ξ hS hξ ω hω]
    exact ⟨ArakelovGeometry.injectiveTensorSeminorm_le_orthogonal _ _,
      ArakelovGeometry.orthogonalTensorSeminorm_le_projective _ _⟩
  · rw [orthogonalTensor_norm_of_finite ξ hS hξ ω (not_not.mp hω)]
    exact ⟨le_rfl, injectiveTensor_norm_le_projectiveTensor_norm ξ ω z⟩

/-- The completed orthogonal tensor family is Hermitian for its actual norm. -/
theorem orthogonalTensor_isHermitian : (orthogonalTensor ξ hS hξ).IsHermitian hS := by
  classical
  refine ⟨orthogonalTensor_isUltrametric ξ hS hξ, fun ω hω => ?_⟩
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (hξ i).fibreInnerProductSpace ω hω
  let : NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :=
    (orthogonalTensor ξ hS hξ).fibreNormedAddCommGroup ω
  let : NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :=
    (orthogonalTensor ξ hS hξ).fibreNormedSpace ω
  let b := fun i => stdOrthonormalBasis (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i)
  let f := (tensorBaseChangeEquiv K (S.ϕ ω).Completion E).trans
    (ArakelovGeometry.orthogonalTensorCoordinates b)
  have : InnerProductSpaceable
      (EuclideanSpace (S.ϕ ω).Completion (∀ i, Fin (Module.finrank (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E i)))) :=
    InnerProductSpace.toInnerProductSpaceable (S.ϕ ω).Completion
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  apply innerProductSpaceable_of_norm_preserving_addMonoidHom f.toAddMonoidHom
  intro z
  change ‖f z‖ = (orthogonalTensor ξ hS hξ).norm ω z
  rw [orthogonalTensor_norm_of_infinite ξ hS hξ ω hω]
  rfl

/-- The Archimedean pure-tensor norm is exactly the product of the original
completed factor norms. -/
theorem orthogonalTensor_norm_tprod_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : ∀ i, (S.ϕ ω).Completion ⊗[K] E i) :
    (orthogonalTensor ξ hS hξ).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm (⨂ₜ[(S.ϕ ω).Completion] i, x i)) =
      ∏ i, (ξ i).norm ω (x i) := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (hξ i).fibreInnerProductSpace ω hω
  rw [orthogonalTensor_norm_of_infinite ξ hS hξ ω hω]
  let b := fun i => stdOrthonormalBasis (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i)
  change ArakelovGeometry.orthogonalTensorSeminorm b
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, x i))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ArakelovGeometry.orthogonalTensorSeminorm_tprod _ x

/-- The empty orthogonal tensor family has the completed unit-field norm. -/
theorem orthogonalTensor_norm_isEmpty [IsEmpty ι] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (orthogonalTensor ξ hS hξ).norm ω z =
      ‖PiTensorProduct.isEmptyEquiv ι (tensorBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ := by
  obtain ⟨hlo, hhi⟩ := orthogonalTensor_norm_bounds ξ hS hξ ω z
  exact le_antisymm (hhi.trans_eq (projectiveTensor_norm_isEmpty ξ ω z))
    ((injectiveTensor_norm_isEmpty ξ ω z).symm.le.trans hlo)

/-- At a finite place the exact pure-tensor product follows from approximate
ultrametric norming functionals on the actual completed factors. -/
theorem orthogonalTensor_norm_tprod_of_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : ∀ i, (S.ϕ ω).Completion ⊗[K] E i) :
    (orthogonalTensor ξ hS hξ).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm (⨂ₜ[(S.ϕ ω).Completion] i, x i)) =
      ∏ i, (ξ i).norm ω (x i) := by
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω
  let : ∀ i, IsUltrametricDist ((S.ϕ ω).Completion ⊗[K] E i) := fun i =>
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm ((hξ i).1 ω hω)
  rw [orthogonalTensor_norm_of_finite ξ hS hξ ω hω]
  change ArakelovGeometry.injectiveTensorSeminorm
    (tensorBaseChangeEquiv K (S.ϕ ω).Completion E
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm
        (⨂ₜ[(S.ϕ ω).Completion] i, x i))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact ArakelovGeometry.injectiveTensorSeminorm_tprod_eq_of_ultrametric x

/-- The orthogonal tensor norm has the exact pure-tensor product formula at
every place, without any nonzero-vector or positive-rank restriction. -/
theorem orthogonalTensor_norm_tprod (ω : S.Ω)
    (x : ∀ i, (S.ϕ ω).Completion ⊗[K] E i) :
    (orthogonalTensor ξ hS hξ).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion E).symm (⨂ₜ[(S.ϕ ω).Completion] i, x i)) =
      ∏ i, (ξ i).norm ω (x i) := by
  by_cases hω : ω ∈ S.Ωinf
  · exact orthogonalTensor_norm_tprod_of_infinite ξ hS hξ ω hω x
  · exact orthogonalTensor_norm_tprod_of_finite ξ hS hξ ω (not_not.mp hω) x

/-- Proposition 4.1.19(5) for finite orthogonal tensor products: actual
injective/projective bounds feed the checked tensor-domination argument. -/
theorem IsDominated.strong_orthogonalTensor (hd : ∀ i, (ξ i).IsDominated) :
    (orthogonalTensor ξ hS hξ).IsStronglyDominated :=
  isStronglyDominated_tensor_of_bounds ξ (orthogonalTensor ξ hS hξ)
    (orthogonalTensor_isUltrametric ξ hS hξ)
    (fun ω z => (orthogonalTensor_norm_bounds ξ hS hξ ω z).1)
    (fun ω z => (orthogonalTensor_norm_bounds ξ hS hξ ω z).2)
    hd (S.v_Ωinf_lt_top_of_isRCLike hS)

end ArakelovGeometry.NormFamily
