/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberFieldArchimedeanDiagonal
public import Mathlib.LinearAlgebra.TensorProduct.Pi
/-! # Archimedean vector diagonals in the actual completed fibres

The scalar decomposition induces the canonical real tensor decomposition of the
original vector space into its literal normalized completed fibres. An actual
norm family supplies the product norm, and a full integral submodule supplies
the integer basis of its literal diagonal image. No covolume assertion is made.
-/

@[expose] public section

open NumberField
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NumberFieldArchimedeanVectorDiagonal
open NumberFieldArchimedeanDiagonal AdelicStructure
variable {K : Type*} [Field K] [NumberField K]
abbrev CompletedCoefficient (w : InfinitePlace K) :=
  ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion
abbrev CompletedScalarProduct (K : Type*) [Field K] [NumberField K] :=
  (w : InfinitePlace K) → CompletedCoefficient w
open scoped Classical in
def completedRealScalarMap (w : InfinitePlace K) : ℝ →+* CompletedCoefficient w :=
  if hw : w.IsReal then (normalizedRealCompletionEquiv hw).symm.toRingHom
  else (normalizedComplexCompletionEquiv
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toRingHom.comp Complex.ofRealHom
instance completedRealAlgebra (w : InfinitePlace K) : Algebra ℝ (CompletedCoefficient w) :=
  (completedRealScalarMap w).toAlgebra
theorem norm_completedRealScalarMap (w : InfinitePlace K) (r : ℝ) :
    ‖completedRealScalarMap w r‖ = |r| := by
  classical
  by_cases hw : w.IsReal
  · have hn := norm_normalizedRealCompletionEquiv hw
      ((normalizedRealCompletionEquiv hw).symm r)
    simpa [completedRealScalarMap, hw] using hn.symm
  · have hn := norm_normalizedComplexCompletionEquiv
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      ((normalizedComplexCompletionEquiv
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm (r : ℂ))
    simpa [completedRealScalarMap, hw] using hn.symm
instance completedRealNormedAlgebra (w : InfinitePlace K) :
    NormedAlgebra ℝ (CompletedCoefficient w) where
  norm_smul_le r z := by
    change ‖completedRealScalarMap w r * z‖ ≤ ‖r‖ * ‖z‖
    rw [norm_mul, norm_completedRealScalarMap, Real.norm_eq_abs]
open scoped Classical in
def coefficientMixedRingEquiv :
    CompletedScalarProduct K ≃+* mixedEmbedding.mixedSpace K :=
  (RingEquiv.piEquivPiSubtypeProd (fun w : InfinitePlace K => w.IsReal)
    (fun w => CompletedCoefficient w)).trans
  (RingEquiv.prodCongr
    (RingEquiv.piCongrRight (fun w => normalizedRealCompletionEquiv w.property))
    ((RingEquiv.piCongrRight (fun w => normalizedComplexCompletionEquiv
      (InfinitePlace.not_isReal_iff_isComplex.mp w.property))).trans
      (RingEquiv.piCongrLeft (fun _ => ℂ)
        (Equiv.subtypeEquivRight
          (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))
open scoped Classical in
def coefficientMixedAlgEquiv :
    CompletedScalarProduct K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  { coefficientMixedRingEquiv with
    commutes' := by
      intro r
      ext w
      · change normalizedRealCompletionEquiv w.property
          (completedRealScalarMap w.val r) = r
        simp [completedRealScalarMap, w.property]
      · change normalizedComplexCompletionEquiv w.property
          (completedRealScalarMap w.val r) = (r : ℂ)
        simp [completedRealScalarMap,
          InfinitePlace.not_isReal_iff_isComplex.mpr w.property] }
theorem coefficientMixedAlgEquiv_algebraMap (a : K) :
    coefficientMixedAlgEquiv (algebraMap K (CompletedScalarProduct K) a) =
      mixedEmbedding K a := by
  classical
  change coefficientMixedRingEquiv _ = _
  ext w <;> simp [coefficientMixedRingEquiv]
def completedScalarTensorEquiv : ℝ ⊗[ℚ] K ≃ₐ[ℝ] CompletedScalarProduct K :=
  scalarDiagonalEquiv.trans coefficientMixedAlgEquiv.symm
theorem completedScalarTensorEquiv_one_tmul (a : K) :
    completedScalarTensorEquiv (1 ⊗ₜ[ℚ] a) =
      algebraMap K (CompletedScalarProduct K) a := by
  apply coefficientMixedAlgEquiv.injective
  change coefficientMixedAlgEquiv
    (coefficientMixedAlgEquiv.symm (scalarDiagonalEquiv (1 ⊗ₜ[ℚ] a))) = _
  rw [AlgEquiv.apply_symm_apply, scalarDiagonalEquiv_one_tmul,
    coefficientMixedAlgEquiv_algebraMap]
theorem completedScalarTensorEquiv_tmul (r : ℝ) (a : K) :
    completedScalarTensorEquiv (r ⊗ₜ[ℚ] a) =
      algebraMap ℝ (CompletedScalarProduct K) r * algebraMap K (CompletedScalarProduct K) a := by
  apply coefficientMixedAlgEquiv.injective
  change coefficientMixedAlgEquiv
    (coefficientMixedAlgEquiv.symm (scalarDiagonalEquiv (r ⊗ₜ[ℚ] a))) = _
  rw [AlgEquiv.apply_symm_apply, scalarDiagonalEquiv_tmul, map_mul,
    AlgEquiv.commutes, coefficientMixedAlgEquiv_algebraMap]
  exact Algebra.smul_def r (mixedEmbedding K a)

theorem completedScalar_isPushout :
    Algebra.IsPushout ℚ ℝ K (CompletedScalarProduct K) := by
  apply Algebra.IsPushout.mk
  apply IsBaseChange.of_equiv (completedScalarTensorEquiv (K := K)).toLinearEquiv
  intro a
  exact completedScalarTensorEquiv_one_tmul a

variable {E : Type*} [AddCommGroup E] [Module K E]
variable [Module ℚ E] [IsScalarTower ℚ K E]
abbrev CompletedVectorProduct (K E : Type*) [Field K] [NumberField K]
    [AddCommGroup E] [Module K E] :=
  (w : InfinitePlace K) → CompletedCoefficient w ⊗[K] E
def vectorCoefficientTensorEquiv :
    ℝ ⊗[ℚ] E ≃ₗ[ℝ] CompletedScalarProduct K ⊗[K] E := by
  let := completedScalar_isPushout (K := K)
  exact (Algebra.IsPushout.cancelBaseChange ℚ ℝ K (CompletedScalarProduct K) E).symm
theorem vectorCoefficientTensorEquiv_tmul (r : ℝ) (x : E) :
    vectorCoefficientTensorEquiv (K := K) (r ⊗ₜ[ℚ] x) =
      algebraMap ℝ (CompletedScalarProduct K) r ⊗ₜ[K] x := by
  let := completedScalar_isPushout (K := K)
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul ℚ ℝ K (CompletedScalarProduct K) E r x
open scoped Classical in
def coefficientTensorPiEquiv :
    CompletedScalarProduct K ⊗[K] E ≃ₗ[ℝ] CompletedVectorProduct K E :=
  { (TensorProduct.piLeft K E (fun w => CompletedCoefficient w)).toAddEquiv with
    map_smul' := by
      intro r z
      induction z using TensorProduct.inductionOn with
      | tmul c x =>
        ext w
        simp [TensorProduct.piLeft, TensorProduct.piRight_apply,
          TensorProduct.piRightHom_tmul, TensorProduct.smul_tmul']
      | add z z' hz hz' =>
        let f := TensorProduct.piLeft K E (fun w : InfinitePlace K => CompletedCoefficient w)
        calc
          f (r • (z + z')) = f (r • z + r • z') :=
            congrArg f (smul_add r z z')
          _ = f (r • z) + f (r • z') := f.map_add _ _
          _ = r • f z + r • f z' := congrArg₂ (· + ·) hz hz'
          _ = r • (f z + f z') := (smul_add r (f z) (f z')).symm
          _ = r • f (z + z') := congrArg (r • ·) (f.map_add z z').symm }
omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem coefficientTensorPiEquiv_tmul (c : CompletedScalarProduct K) (x : E)
    (w : InfinitePlace K) :
    coefficientTensorPiEquiv (K := K) (E := E) (c ⊗ₜ[K] x) w = c w ⊗ₜ[K] x := by
  simp [coefficientTensorPiEquiv, TensorProduct.piLeft, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]
def vectorDiagonalEquiv : ℝ ⊗[ℚ] E ≃ₗ[ℝ] CompletedVectorProduct K E :=
  vectorCoefficientTensorEquiv.trans coefficientTensorPiEquiv
theorem vectorDiagonalEquiv_tmul (r : ℝ) (x : E) (w : InfinitePlace K) :
    vectorDiagonalEquiv (K := K) (r ⊗ₜ[ℚ] x) w =
      algebraMap ℝ (CompletedCoefficient w) r ⊗ₜ[K] x := by
  rw [vectorDiagonalEquiv, LinearEquiv.trans_apply, vectorCoefficientTensorEquiv_tmul,
    coefficientTensorPiEquiv_tmul]
  rfl
def vectorDiagonalMap : E →ₗ[K] CompletedVectorProduct K E :=
  LinearMap.pi (fun _ => TensorProduct.mk K (CompletedCoefficient _) E 1)
omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem vectorDiagonalMap_apply (x : E) (w : InfinitePlace K) :
    vectorDiagonalMap (K := K) x w = 1 ⊗ₜ[K] x := rfl
theorem vectorDiagonalEquiv_one_tmul (x : E) :
    vectorDiagonalEquiv (K := K) (1 ⊗ₜ[ℚ] x) = vectorDiagonalMap (K := K) x := by
  ext w
  rw [vectorDiagonalEquiv_tmul, map_one, vectorDiagonalMap_apply]


omit [Module ℚ E] [IsScalarTower ℚ K E] in
instance finite_completedVectorProduct [FiniteDimensional K E] :
    FiniteDimensional ℝ (CompletedVectorProduct K E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let : Module.Finite ℚ E := Module.Finite.trans K E
  exact (vectorDiagonalEquiv (K := K) (E := E)).finiteDimensional

theorem vectorDiagonal_dimension [FiniteDimensional K E] :
    Module.finrank ℝ (CompletedVectorProduct K E) =
      Module.finrank ℚ K * Module.finrank K E := by
  rw [← (vectorDiagonalEquiv (K := K) (E := E)).finrank_eq,
    Module.finrank_tensorProduct]
  simp only [Module.finrank_self, one_mul]
  exact (Module.finrank_mul_finrank ℚ K E).symm

omit [Module ℚ E] [IsScalarTower ℚ K E] in
abbrev completedProductNormedAddCommGroup
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    NormedAddCommGroup (CompletedVectorProduct K E) := by
  letI : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  infer_instance

omit [Module ℚ E] [IsScalarTower ℚ K E] in
abbrev completedProductNormedSpace
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E) :
    letI := completedProductNormedAddCommGroup ξ
    NormedSpace ℝ (CompletedVectorProduct K E) := by
  letI : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  letI : ∀ w : InfinitePlace K, NormedSpace ℝ (CompletedCoefficient w ⊗[K] E) :=
    fun w =>
      { norm_smul_le := by
          intro r z
          change ξ.norm (normalizedInfinitePlacePoint w) (r • z) ≤
            ‖r‖ * ξ.norm (normalizedInfinitePlacePoint w) z
          rw [← IsScalarTower.algebraMap_smul (CompletedCoefficient w) r z,
            ξ.norm_smul]
          change ‖completedRealScalarMap w r‖ * _ ≤ ‖r‖ * _
          rw [norm_completedRealScalarMap, Real.norm_eq_abs] }
  infer_instance

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem completedProduct_norm
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (z : CompletedVectorProduct K E) :
    letI := completedProductNormedAddCommGroup ξ
    ‖z‖ = ↑(Finset.univ.sup (fun w : InfinitePlace K =>
      ⟨ξ.norm (normalizedInfinitePlacePoint w) (z w),
        ξ.norm_nonneg (normalizedInfinitePlacePoint w) (z w)⟩ : _ → NNReal)) := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  exact Pi.norm_def z

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem completedProduct_norm_smul
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (r : ℝ) (z : CompletedVectorProduct K E) :
    letI := completedProductNormedAddCommGroup ξ
    ‖r • z‖ = |r| * ‖z‖ := by
  let := completedProductNormedAddCommGroup ξ
  let := completedProductNormedSpace ξ
  exact norm_smul r z

def latticeDiagonalMap (M : Submodule (𝓞 K) E) :
    M →ₗ[ℤ] CompletedVectorProduct K E :=
  (vectorDiagonalMap (K := K) (E := E)).restrictScalars ℤ |>.comp
    (M.subtype.restrictScalars ℤ)

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem latticeDiagonalMap_apply (M : Submodule (𝓞 K) E) (m : M) (w : InfinitePlace K) :
    latticeDiagonalMap M m w = 1 ⊗ₜ[K] (m : E) := rfl

def diagonalLattice (M : Submodule (𝓞 K) E) : Submodule ℤ (CompletedVectorProduct K E) :=
  (latticeDiagonalMap M).range

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem mem_diagonalLattice_iff (M : Submodule (𝓞 K) E) (z : CompletedVectorProduct K E) :
    z ∈ diagonalLattice M ↔ ∃ m : M, vectorDiagonalMap (K := K) (m : E) = z := Iff.rfl

omit [Module ℚ E] [IsScalarTower ℚ K E] in
def diagonalLatticeBasis (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Module.Basis (Fin (Module.finrank ℤ M)) ℝ (CompletedVectorProduct K E) := by
  letI : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  letI : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  exact ((NumberFieldFullLattice.integerRationalBasis M hfg hspan).baseChange ℝ).map
    (vectorDiagonalEquiv (K := K))

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem diagonalLatticeBasis_apply (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) (i : Fin (Module.finrank ℤ M)) :
    diagonalLatticeBasis M hfg hspan i =
      vectorDiagonalMap (K := K) (NumberFieldFullLattice.integerBasis M hfg i : E) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  let b := NumberFieldFullLattice.integerRationalBasis M hfg hspan
  calc
    diagonalLatticeBasis M hfg hspan i =
        vectorDiagonalEquiv (K := K) (b.baseChange ℝ i) :=
      Module.Basis.map_apply _ _ i
    _ = vectorDiagonalEquiv (K := K) (1 ⊗ₜ[ℚ] b i) :=
      congrArg (vectorDiagonalEquiv (K := K)) (Module.Basis.baseChange_apply ℝ b i)
    _ = vectorDiagonalMap (K := K) (b i) := vectorDiagonalEquiv_one_tmul (b i)
    _ = _ := congrArg (vectorDiagonalMap (K := K))
      (NumberFieldFullLattice.integerRationalBasis_coe M hfg hspan i)

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem diagonalLattice_eq_integerSpan (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    diagonalLattice M = Submodule.span ℤ (Set.range (diagonalLatticeBasis M hfg hspan)) := by
  apply le_antisymm
  · rintro x ⟨m, rfl⟩
    have hm := congrArg (latticeDiagonalMap M)
      ((NumberFieldFullLattice.integerBasis M hfg).sum_repr m)
    rw [map_sum] at hm
    rw [← hm]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨i, diagonalLatticeBasis_apply M hfg hspan i⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact ⟨NumberFieldFullLattice.integerBasis M hfg i,
      (diagonalLatticeBasis_apply M hfg hspan i).symm⟩

omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem discrete_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := completedProductNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice M) := by
  classical
  let := completedProductNormedAddCommGroup ξ
  let := completedProductNormedSpace ξ
  rw [diagonalLattice_eq_integerSpan M hfg hspan]
  infer_instance

open scoped Classical in
omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem isZLattice_diagonalLattice [FiniteDimensional K E]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (M : Submodule (𝓞 K) E) (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    letI := completedProductNormedAddCommGroup ξ
    letI := completedProductNormedSpace ξ
    letI := discrete_diagonalLattice ξ M hfg hspan
    IsZLattice ℝ (diagonalLattice M) := by
  let := completedProductNormedAddCommGroup ξ
  let := completedProductNormedSpace ξ
  let := discrete_diagonalLattice ξ M hfg hspan
  simpa only [diagonalLattice_eq_integerSpan M hfg hspan] using
    (inferInstance : IsZLattice ℝ
      (Submodule.span ℤ (Set.range (diagonalLatticeBasis M hfg hspan))))


omit [Module ℚ E] [IsScalarTower ℚ K E] in
theorem completedProduct_continuous_iff {X : Type*} [TopologicalSpace X]
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (f : X → CompletedVectorProduct K E) :
    letI : ∀ w : InfinitePlace K,
        NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
      fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := completedProductNormedAddCommGroup ξ
    Continuous f ↔ ∀ w, Continuous (fun x => f x w) := by
  let : ∀ w : InfinitePlace K,
      NormedAddCommGroup (CompletedCoefficient w ⊗[K] E) :=
    fun w => ξ.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  exact continuous_pi_iff

theorem vectorDiagonalEquiv_tmul_norm
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (r : ℝ) (x : E) (w : InfinitePlace K) :
    ξ.norm (normalizedInfinitePlacePoint w) (vectorDiagonalEquiv (K := K) (r ⊗ₜ[ℚ] x) w) =
      |r| * ξ.norm (normalizedInfinitePlacePoint w) (1 ⊗ₜ[K] x) := by
  rw [vectorDiagonalEquiv_tmul]
  have he : algebraMap ℝ (CompletedCoefficient w) r ⊗ₜ[K] x =
      algebraMap ℝ (CompletedCoefficient w) r • (1 ⊗ₜ[K] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, ξ.norm_smul]
  change ‖completedRealScalarMap w r‖ * _ = _
  rw [norm_completedRealScalarMap]

end ArakelovGeometry.NumberFieldArchimedeanVectorDiagonal

namespace ArakelovGeometry.NormFamily
open AdelicStructure NumberFieldArchimedeanVectorDiagonal
variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

def IsDominated.pure_globalBall_diagonalBasis (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    Module.Basis (Fin (Module.finrank ℤ (ξ.globalUnitBallModule hξ))) ℝ
      (CompletedVectorProduct K E) := by
  have hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  have hspan : Submodule.span K ((ξ.globalUnitBallModule hξ) : Set E) = ⊤ := hm.2.2
  exact diagonalLatticeBasis (ξ.globalUnitBallModule hξ) hm.1 hspan

theorem IsDominated.pure_globalBall_diagonal_discrete (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := completedProductNormedAddCommGroup ξ
    DiscreteTopology (diagonalLattice (ξ.globalUnitBallModule hξ)) := by
  have hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  exact discrete_diagonalLattice ξ (ξ.globalUnitBallModule hξ) hm.1 hm.2.2

open scoped Classical in
theorem IsDominated.pure_globalBall_diagonal_isZLattice (hdom : ξ.IsDominated)
    (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    letI := completedProductNormedAddCommGroup ξ
    letI := completedProductNormedSpace ξ
    letI := hdom.pure_globalBall_diagonal_discrete hξ hpure
    IsZLattice ℝ (diagonalLattice (ξ.globalUnitBallModule hξ)) := by
  have hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  exact isZLattice_diagonalLattice ξ (ξ.globalUnitBallModule hξ) hm.1 hm.2.2

end ArakelovGeometry.NormFamily
