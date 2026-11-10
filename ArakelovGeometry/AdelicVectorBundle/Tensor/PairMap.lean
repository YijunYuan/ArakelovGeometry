/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian
import ArakelovGeometry.Analysis.Determinant.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Contraction of actual completed tensor maps

The projective bound uses every finite pure-tensor decomposition. The injective
bound restricts each dual functional and compares its actual operator norm.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

section LocalTensorMaps

variable {ι L : Type*} [Fintype ι] [NormedField L]
  {X Y : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace L (X i)]
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace L (Y i)]
  (f : ∀ i, X i →ₗ[L] Y i)

/-- The projective tensor of contractions contracts every vector. -/
theorem projectiveSeminorm_map_le_of_norm_le (hf : ∀ i x, ‖f i x‖ ≤ ‖x‖)
    (z : ⨂[L] i, X i) :
    PiTensorProduct.projectiveSeminorm (PiTensorProduct.map f z) ≤
      PiTensorProduct.projectiveSeminorm z := by
  change ‖PiTensorProduct.map f z‖ ≤ PiTensorProduct.projectiveSeminorm z
  have h := norm_linearMap_le_projective_of_tprod_le (PiTensorProduct.map f)
    (C := 1) zero_le_one (fun x ↦ ?_) z
  · simpa only [one_mul] using h
  · rw [PiTensorProduct.map_tprod, one_mul]
    exact (PiTensorProduct.projectiveSeminorm_tprod_le _).trans
      (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hf i (x i)))

/-- Pulling back a tuple of dual functionals commutes with its tensor evaluation. -/
theorem tensorDualEval_comp_map (φ : ∀ i, Y i →ₗ[L] L) :
    (tensorDualEval φ).comp (PiTensorProduct.map f) =
      tensorDualEval (fun i ↦ (φ i).comp (f i)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    PiTensorProduct.map_tprod, tensorDualEval_tprod]

variable [CompleteSpace L] [∀ i, FiniteDimensional L (X i)]
  [∀ i, FiniteDimensional L (Y i)]

/-- The injective tensor of contractions contracts every vector, by restriction
of all dual tuples rather than a test on pure tensors alone. -/
theorem injectiveSeminorm_map_le_of_norm_le (hf : ∀ i x, ‖f i x‖ ≤ ‖x‖)
    (z : ⨂[L] i, X i) :
    injectiveTensorSeminorm (PiTensorProduct.map f z) ≤ injectiveTensorSeminorm z := by
  classical
  apply (injectiveTensorSeminorm_le_iff _ _).mpr
  intro φ
  have hd : ∏ i, linearMapOperatorSeminorm ((φ i).comp (f i)) ≤
      ∏ i, linearMapOperatorSeminorm (φ i) := by
    apply Finset.prod_le_prod₀ (fun _ _ ↦ apply_nonneg _ _)
    intro i _
    apply linearMapOperatorSeminorm_le _ (apply_nonneg _ _)
    intro x
    exact (norm_linearMap_apply_le (φ i) (f i x)).trans
      (mul_le_mul_of_nonneg_left (hf i x) (apply_nonneg _ _))
  by_cases hz : (∏ i, linearMapOperatorSeminorm (φ i)) = 0
  · rw [hz, div_zero]
    exact apply_nonneg _ _
  · have hp : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
      lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have he := DFunLike.congr_fun (tensorDualEval_comp_map f φ) z
    calc
      ‖tensorDualEval φ (PiTensorProduct.map f z)‖ =
          ‖tensorDualEval (fun i ↦ (φ i).comp (f i)) z‖ := congrArg norm he
      _ ≤ (∏ i, linearMapOperatorSeminorm ((φ i).comp (f i))) *
          injectiveTensorSeminorm z := by
        simpa only [mul_comm] using norm_tensorDualEval_le_injective (fun i ↦ (φ i).comp (f i)) z
      _ ≤ (∏ i, linearMapOperatorSeminorm (φ i)) * injectiveTensorSeminorm z :=
        mul_le_mul_of_nonneg_right hd (apply_nonneg _ _)
      _ = _ := mul_comm _ _

end LocalTensorMaps

section OrthogonalTensorMaps

variable {ι L : Type*} [Fintype ι] [RCLike L]
  {X Y : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, InnerProductSpace L (X i)]
  [∀ i, NormedAddCommGroup (Y i)] [∀ i, InnerProductSpace L (Y i)]
  {κ τ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Fintype (τ i)]
  (b : ∀ i, OrthonormalBasis (κ i) L (X i))
  (c : ∀ i, OrthonormalBasis (τ i) L (Y i))
  (f : ∀ i, X i →ₗᵢ[L] Y i)

/-- Tensoring factor isometries preserves the actual product inner form. -/
theorem orthogonalTensorCore_map_inner (z t : ⨂[L] i, X i) :
    (orthogonalTensorCore c).inner (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) z)
        (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) t) =
      (orthogonalTensorCore b).inner z t := by
  classical
  change inner L (orthogonalTensorCoordinates c _)
      (orthogonalTensorCoordinates c _) =
    inner L (orthogonalTensorCoordinates b z) (orthogonalTensorCoordinates b t)
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod d y =>
      simp only [map_smul, inner_smul_left, inner_smul_right]
      change d * ((starRingEnd L) a * (orthogonalTensorCore c).inner
          (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) (⨂ₜ[L] i, x i))
          (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) (⨂ₜ[L] i, y i))) =
        d * ((starRingEnd L) a * (orthogonalTensorCore b).inner _ _)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        orthogonalTensorCore_tprod, orthogonalTensorCore_tprod]
      simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.inner_map_map]
    | add t s ht hs => simp only [map_add, inner_add_right, ht, hs]
  | add z s hz hs => simp only [map_add, inner_add_left, hz, hs]

/-- Tensoring factor isometries preserves the orthogonal norm on every vector. -/
theorem orthogonalTensorSeminorm_map_eq (z : ⨂[L] i, X i) :
    orthogonalTensorSeminorm c (PiTensorProduct.map (fun i ↦ (f i).toLinearMap) z) =
      orthogonalTensorSeminorm b z := by
  apply (sq_eq_sq₀ (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [orthogonalTensorSeminorm_sq, orthogonalTensorSeminorm_sq,
    orthogonalTensorCore_map_inner b c f z z]

end OrthogonalTensorMaps

section TensorMapBaseChange

variable {ι : Type*} [Finite ι]
  (K L : Type*) [Field K] [Field L] [Algebra K L]
  {X Y : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]

/-- The canonical tensor scalar extension commutes with every tensor map. -/
theorem tensorBaseChangeEquiv_map (f : ∀ i, X i →ₗ[K] Y i)
    (z : L ⊗[K] (⨂[K] i, X i)) :
    tensorBaseChangeEquiv K L Y ((PiTensorProduct.map f).baseChange L z) =
      PiTensorProduct.map (fun i ↦ (f i).baseChange L) (tensorBaseChangeEquiv K L X z) := by
  let : Fintype ι := Fintype.ofFinite ι
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod b x =>
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      simp only [PiTensorProduct.map_tprod, LinearMap.baseChange_tmul, map_smul,
        tensorBaseChangeEquiv_tmul_tprod]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end TensorMapBaseChange

section BinaryTensorMap

universe wB

variable (K : Type*) [Field K]
  {E F G H : Type wB} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H]

/-- The ordinary binary tensor map agrees with the canonical finite tensor map. -/
theorem binaryTensorEquiv_map (f : E →ₗ[K] G) (g : F →ₗ[K] H) :
    (binaryTensorEquiv K (BinaryTensorFactors G H)).toLinearMap.comp
      (PiTensorProduct.map (fun i ↦ match i with | .inl _ => f | .inr _ => g)) =
      (TensorProduct.map f g).comp (binaryTensorEquiv K (BinaryTensorFactors E F)).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    PiTensorProduct.map_tprod, binaryTensorEquiv_tprod, LinearEquiv.coe_coe,
    TensorProduct.map_tmul]

end BinaryTensorMap

universe u v w wι

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {X Y : ι → Type w}
  [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, FiniteDimensional K (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)] [∀ i, FiniteDimensional K (Y i)]
  (ξ : ∀ i, NormFamily S (X i)) (η : ∀ i, NormFamily S (Y i))
  (f : ∀ i, X i →ₗ[K] Y i) (ω : S.Ω)
  (hf : ∀ i x, (η i).norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤ (ξ i).norm ω x)

include hf

/-- The actual completed projective tensor map contracts every vector. -/
theorem projectiveTensor_map_norm_le (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, X i)) :
    (projectiveTensor η).norm ω ((PiTensorProduct.map f).baseChange (S.ϕ ω).Completion z) ≤
      (projectiveTensor ξ).norm ω z := by
  let L := (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedSpace ω
  change PiTensorProduct.projectiveSeminorm (tensorBaseChangeEquiv K L Y
      ((PiTensorProduct.map f).baseChange L z)) ≤
    PiTensorProduct.projectiveSeminorm (tensorBaseChangeEquiv K L X z)
  rw [tensorBaseChangeEquiv_map]
  exact projectiveSeminorm_map_le_of_norm_le (fun i ↦ (f i).baseChange L) hf _

/-- The actual completed injective tensor map contracts every vector. -/
theorem injectiveTensor_map_norm_le (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, X i)) :
    (injectiveTensor η).norm ω ((PiTensorProduct.map f).baseChange (S.ϕ ω).Completion z) ≤
      (injectiveTensor ξ).norm ω z := by
  let L := (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedSpace ω
  change ArakelovGeometry.injectiveTensorSeminorm (tensorBaseChangeEquiv K L Y
      ((PiTensorProduct.map f).baseChange L z)) ≤
    ArakelovGeometry.injectiveTensorSeminorm (tensorBaseChangeEquiv K L X z)
  rw [tensorBaseChangeEquiv_map]
  exact injectiveSeminorm_map_le_of_norm_le (fun i ↦ (f i).baseChange L) hf _

/-- The actual mixed tensor map contracts at finite and infinite places. -/
theorem mixedTensor_map_norm_le (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, X i)) :
    (mixedTensor η).norm ω ((PiTensorProduct.map f).baseChange (S.ϕ ω).Completion z) ≤
      (mixedTensor ξ).norm ω z := by
  by_cases hω : ω ∈ S.Ωfin
  · rw [mixedTensor_norm_of_mem_Ωfin η ω hω, mixedTensor_norm_of_mem_Ωfin ξ ω hω]
    exact injectiveTensor_map_norm_le ξ η f ω hf z
  · rw [mixedTensor_norm_of_not_mem_Ωfin η ω hω,
      mixedTensor_norm_of_not_mem_Ωfin ξ ω hω]
    exact projectiveTensor_map_norm_le ξ η f ω hf z

end NormFamily

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {X Y : ι → Type w}
  [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, FiniteDimensional K (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)] [∀ i, FiniteDimensional K (Y i)]

/-- The actual Hermitian tensor of completed factor isometries contracts at
every place, preserving the full orthogonal norm at infinite places. -/
theorem orthogonalTensor_map_norm_le_of_norm_eq
    (ξ : ∀ i, NormFamily S (X i)) (η : ∀ i, NormFamily S (Y i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (hη : ∀ i, (η i).IsHermitian hN)
    (f : ∀ i, X i →ₗ[K] Y i) (ω : S.Ω)
    (hf : ∀ i x, (η i).norm ω ((f i).baseChange (S.ϕ ω).Completion x) = (ξ i).norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, X i)) :
    (orthogonalTensor η hN hη).norm ω
        ((PiTensorProduct.map f).baseChange (S.ϕ ω).Completion z) ≤
      (orthogonalTensor ξ hN hξ).norm ω z := by
  by_cases hω : ω ∈ S.Ωinf
  · let L := (S.ϕ ω).Completion
    let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let : ∀ i, NormedAddCommGroup (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace L (L ⊗[K] X i) := fun i ↦ (ξ i).fibreNormedSpace ω
    let : ∀ i, NormedAddCommGroup (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedAddCommGroup ω
    let : ∀ i, NormedSpace L (L ⊗[K] Y i) := fun i ↦ (η i).fibreNormedSpace ω
    let : ∀ i, InnerProductSpace L (L ⊗[K] X i) := fun i ↦ (hξ i).fibreInnerProductSpace ω hω
    let : ∀ i, InnerProductSpace L (L ⊗[K] Y i) := fun i ↦ (hη i).fibreInnerProductSpace ω hω
    let g : ∀ i, (L ⊗[K] X i) →ₗᵢ[L] (L ⊗[K] Y i) :=
      fun i ↦ { toLinearMap := (f i).baseChange L, norm_map' := hf i }
    rw [orthogonalTensor_norm_of_infinite, orthogonalTensor_norm_of_infinite]
    change orthogonalTensorSeminorm (fun i ↦ stdOrthonormalBasis L (L ⊗[K] Y i))
        (tensorBaseChangeEquiv K L Y ((PiTensorProduct.map f).baseChange L z)) ≤
      orthogonalTensorSeminorm (fun i ↦ stdOrthonormalBasis L (L ⊗[K] X i))
        (tensorBaseChangeEquiv K L X z)
    rw [tensorBaseChangeEquiv_map]
    exact (orthogonalTensorSeminorm_map_eq
      (fun i ↦ stdOrthonormalBasis L (L ⊗[K] X i))
      (fun i ↦ stdOrthonormalBasis L (L ⊗[K] Y i)) g _).le
  · rw [orthogonalTensor_norm_of_finite _ _ _ ω (not_not.mp hω),
      orthogonalTensor_norm_of_finite _ _ _ ω (not_not.mp hω)]
    exact injectiveTensor_map_norm_le ξ η f ω (fun i x ↦ (hf i x).le) z

end NormFamily

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F G H : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K G]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- The canonical ordinary binary mixed tensor map contracts every completed
vector when both given factor maps do. -/
theorem mixedTensorPair_map_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G) (θ : NormFamily S H)
    (f : E →ₗ[K] G) (g : F →ₗ[K] H) (ω : S.Ω)
    (hf : ∀ x, ζ.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (hg : ∀ y, θ.norm ω (g.baseChange (S.ϕ ω).Completion y) ≤ η.norm ω y)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ζ.mixedTensorPair θ).norm ω
      ((TensorProduct.map f g).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.mixedTensorPair η).norm ω z := by
  let L := (S.ϕ ω).Completion
  let ff : ∀ i, BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors G H i :=
    fun i ↦ match i with | .inl _ => f | .inr _ => g
  let B₁ := binaryTensorEquiv K (BinaryTensorFactors E F)
  let B₂ := binaryTensorEquiv K (BinaryTensorFactors G H)
  have hc : B₂.symm.toLinearMap.comp (TensorProduct.map f g) =
      (PiTensorProduct.map ff).comp B₁.symm.toLinearMap := by
    apply LinearMap.ext
    intro y
    apply B₂.injective
    have h := DFunLike.congr_fun (binaryTensorEquiv_map K f g) (B₁.symm y)
    simpa only [B₁, B₂, ff, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h.symm
  have hz := DFunLike.congr_fun (congrArg (fun h ↦ h.baseChange L) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  change (mixedTensor (tensorPairFactors ζ θ)).norm ω
      (B₂.symm.toLinearMap.baseChange L ((TensorProduct.map f g).baseChange L z)) ≤
    (mixedTensor (tensorPairFactors ξ η)).norm ω (B₁.symm.toLinearMap.baseChange L z)
  rw [hz]
  apply mixedTensor_map_norm_le (tensorPairFactors ξ η) (tensorPairFactors ζ θ) ff ω
  rintro (i | i) x
  · exact hf x
  · exact hg x

/-- The actual rational tensor inclusion of two subspaces contracts every
completed vector for their mixed restricted tensor norm. -/
theorem mixedTensorPair_restrict_map_norm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (U : Submodule K E) (T : Submodule K F) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (U ⊗[K] T)) :
    (ξ.mixedTensorPair η).norm ω
      ((TensorProduct.map U.subtype T.subtype).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.restrict U).mixedTensorPair (η.restrict T)).norm ω z := by
  apply mixedTensorPair_map_norm_le (ξ.restrict U) (η.restrict T) ξ η
    U.subtype T.subtype ω _ _ z
  · intro x
    exact le_rfl
  · intro y
    exact le_rfl

/-- The actual binary Hermitian tensor map contracts whenever the factor maps
are isometries on their completed fibres. -/
theorem orthogonalTensorPair_map_norm_le_of_norm_eq
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G) (θ : NormFamily S H)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (hζ : ζ.IsHermitian hN) (hθ : θ.IsHermitian hN)
    (f : E →ₗ[K] G) (g : F →ₗ[K] H) (ω : S.Ω)
    (hf : ∀ x, ζ.norm ω (f.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (hg : ∀ y, θ.norm ω (g.baseChange (S.ϕ ω).Completion y) = η.norm ω y)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ζ.orthogonalTensorPair θ hN hζ hθ).norm ω
        ((TensorProduct.map f g).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.orthogonalTensorPair η hN hξ hη).norm ω z := by
  let L := (S.ϕ ω).Completion
  let ff : ∀ i, BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors G H i :=
    fun i ↦ match i with | .inl _ => f | .inr _ => g
  let B₁ := binaryTensorEquiv K (BinaryTensorFactors E F)
  let B₂ := binaryTensorEquiv K (BinaryTensorFactors G H)
  have hc : B₂.symm.toLinearMap.comp (TensorProduct.map f g) =
      (PiTensorProduct.map ff).comp B₁.symm.toLinearMap := by
    apply LinearMap.ext
    intro y
    apply B₂.injective
    have h := DFunLike.congr_fun (binaryTensorEquiv_map K f g) (B₁.symm y)
    simpa only [B₁, B₂, ff, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h.symm
  have hz := DFunLike.congr_fun (congrArg (fun h ↦ h.baseChange L) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  change (orthogonalTensor (tensorPairFactors ζ θ) hN (hζ.tensorPairFactors hθ)).norm ω
      (B₂.symm.toLinearMap.baseChange L ((TensorProduct.map f g).baseChange L z)) ≤
    (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).norm ω
      (B₁.symm.toLinearMap.baseChange L z)
  rw [hz]
  apply orthogonalTensor_map_norm_le_of_norm_eq (tensorPairFactors ξ η)
    (tensorPairFactors ζ θ) hN (hξ.tensorPairFactors hη) (hζ.tensorPairFactors hθ) ff ω
  rintro (i | i) x
  · exact hf x
  · exact hg x

/-- The actual rational tensor inclusion of Hermitian restricted factors
contracts their full completed orthogonal tensor norm. -/
theorem orthogonalTensorPair_restrict_map_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (U : Submodule K E) (T : Submodule K F) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (U ⊗[K] T)) :
    (ξ.orthogonalTensorPair η hN hξ hη).norm ω
        ((TensorProduct.map U.subtype T.subtype).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.restrict U).orthogonalTensorPair (η.restrict T) hN (hξ.restrict U)
        (hη.restrict T)).norm ω z := by
  apply orthogonalTensorPair_map_norm_le_of_norm_eq (ξ.restrict U) (η.restrict T) ξ η
    hN (hξ.restrict U) (hη.restrict T) hξ hη U.subtype T.subtype ω _ _ z
  · intro x
    rfl
  · intro y
    rfl

end NormFamily

end

end ArakelovGeometry
