/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.EquivalentCompletion
public import ArakelovGeometry.NumberTheory.NormalizedNumberFieldInfiniteMass
public import ArakelovGeometry.NumberTheory.NumberFieldFullLatticeIntegerBasis
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-! # Actual Archimedean scalar decomposition and diagonal lattices

The canonical real tensor map is an algebra equivalence onto the usual mixed
space. Actual normalized infinite completions map isometrically to their usual
real or complex factors. A literal full integral submodule of the scalar field
maps to an actual discrete full integer lattice.
-/

@[expose] public section

open NumberField
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldArchimedeanDiagonal

open AdelicStructure

variable {K : Type*} [Field K] [NumberField K]

theorem normalizedInfiniteValue (w : InfinitePlace K) :
    (normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w) = w.val :=
  normalizedPlaceValue_eq_infinitePlace w

/-- The canonical completion map fixes original scalars. -/
def normalizedInfiniteCompletionEquiv (w : InfinitePlace K) :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion ≃ₐ[K]
      w.val.Completion :=
  AbsoluteValue.completionAlgEquivOfIsEquiv _ _
    (by rw [normalizedInfiniteValue]; exact AbsoluteValue.IsEquiv.refl _)

@[simp]
theorem normalizedInfiniteCompletionEquiv_coe (w : InfinitePlace K) (a : K) :
    normalizedInfiniteCompletionEquiv w
      (algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedInfinitePlacePoint w)).Completion a) = algebraMap K w.val.Completion a :=
  (normalizedInfiniteCompletionEquiv w).commutes a

theorem norm_normalizedInfiniteCompletionEquiv (w : InfinitePlace K) (z :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion) :
    ‖normalizedInfiniteCompletionEquiv w z‖ = ‖z‖ := by
  have h := AbsoluteValue.norm_completionAlgEquivOfIsEquiv _ _
    (by rw [normalizedInfiniteValue]; exact AbsoluteValue.IsEquiv.refl _) 1 zero_lt_one
    (fun a => by rw [normalizedInfiniteValue, Real.rpow_one]) z
  simpa only [normalizedInfiniteCompletionEquiv, Real.rpow_one] using h

/-- The actual real factor of a normalized infinite completion. -/
def normalizedRealCompletionEquiv {w : InfinitePlace K} (hw : w.IsReal) :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion ≃+*
      ℝ :=
  (normalizedInfiniteCompletionEquiv w).toRingEquiv.trans
    ((InfinitePlace.Completion.equiv w).symm.trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw))

/-- The actual complex factor of a normalized infinite completion. -/
def normalizedComplexCompletionEquiv {w : InfinitePlace K} (hw : w.IsComplex) :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion ≃+*
      ℂ :=
  (normalizedInfiniteCompletionEquiv w).toRingEquiv.trans
    ((InfinitePlace.Completion.equiv w).symm.trans
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw))

@[simp]
theorem normalizedRealCompletionEquiv_coe {w : InfinitePlace K} (hw : w.IsReal) (a : K) :
    normalizedRealCompletionEquiv hw
      (algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedInfinitePlacePoint w)).Completion a) = w.embedding_of_isReal hw a := by
  simp only [normalizedRealCompletionEquiv, RingEquiv.trans_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    ((InfinitePlace.Completion.equiv w).symm (normalizedInfiniteCompletionEquiv w
      (algebraMap K _ a))) = _
  rw [normalizedInfiniteCompletionEquiv_coe]
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion) = _
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw (WithAbs.toAbs w.val a)

@[simp]
theorem normalizedComplexCompletionEquiv_coe {w : InfinitePlace K} (hw : w.IsComplex) (a : K) :
    normalizedComplexCompletionEquiv hw
      (algebraMap K ((normalizedNumberFieldAdelicStructure K).ϕ
        (normalizedInfinitePlacePoint w)).Completion a) = w.embedding a := by
  simp only [normalizedComplexCompletionEquiv, RingEquiv.trans_apply,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  change InfinitePlace.Completion.extensionEmbedding w
    ((InfinitePlace.Completion.equiv w).symm (normalizedInfiniteCompletionEquiv w
      (algebraMap K _ a))) = _
  rw [normalizedInfiniteCompletionEquiv_coe]
  change InfinitePlace.Completion.extensionEmbedding w (a : w.Completion) = _
  exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs w.val a)

theorem norm_normalizedRealCompletionEquiv {w : InfinitePlace K} (hw : w.IsReal) (z :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion) :
    ‖normalizedRealCompletionEquiv hw z‖ = ‖z‖ := by
  rw [normalizedRealCompletionEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
    (map_zero _) _, InfinitePlace.Completion.norm_ofCompletion]
  exact norm_normalizedInfiniteCompletionEquiv w z

theorem norm_normalizedComplexCompletionEquiv {w : InfinitePlace K} (hw : w.IsComplex) (z :
    ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion) :
    ‖normalizedComplexCompletionEquiv hw z‖ = ‖z‖ := by
  rw [normalizedComplexCompletionEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) _, InfinitePlace.Completion.norm_ofCompletion]
  exact norm_normalizedInfiniteCompletionEquiv w z

/-- The actual canonical tensor map, defined from the embeddings. -/
def scalarDiagonalMap : ℝ ⊗[ℚ] K →ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (mixedEmbedding K).toRatAlgHom
    (fun _ _ => Commute.all _ _)

@[simp]
theorem scalarDiagonalMap_tmul (t : ℝ) (a : K) :
    scalarDiagonalMap (t ⊗ₜ[ℚ] a) = t • mixedEmbedding K a := by
  simp [scalarDiagonalMap, Algebra.smul_def]

theorem scalarDiagonalMap_bijective : Function.Bijective (scalarDiagonalMap (K := K)) := by
  let b := (integralBasis K).baseChange ℝ
  let e := b.equiv (mixedEmbedding.latticeBasis K) (Equiv.refl _)
  have he : scalarDiagonalMap.toLinearMap = e.toLinearMap := by
    apply b.ext
    intro i
    change _ = (b.equiv (mixedEmbedding.latticeBasis K) (Equiv.refl _)) (b i)
    rw [Module.Basis.equiv_apply]
    rw [show b i = 1 ⊗ₜ[ℚ] integralBasis K i from Module.Basis.baseChange_apply ℝ _ i]
    change scalarDiagonalMap (1 ⊗ₜ[ℚ] integralBasis K i) = mixedEmbedding.latticeBasis K i
    rw [scalarDiagonalMap_tmul, one_smul, mixedEmbedding.latticeBasis_apply]
  change Function.Bijective scalarDiagonalMap.toLinearMap
  rw [he]
  exact e.bijective

/-- The canonical actual scalar decomposition; a basis only proves bijectivity. -/
def scalarDiagonalEquiv : ℝ ⊗[ℚ] K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  AlgEquiv.ofBijective scalarDiagonalMap scalarDiagonalMap_bijective

@[simp]
theorem scalarDiagonalEquiv_tmul (t : ℝ) (a : K) :
    scalarDiagonalEquiv (t ⊗ₜ[ℚ] a) = t • mixedEmbedding K a :=
  scalarDiagonalMap_tmul t a

@[simp]
theorem scalarDiagonalEquiv_one_tmul (a : K) :
    scalarDiagonalEquiv (1 ⊗ₜ[ℚ] a) = mixedEmbedding K a := by
  rw [scalarDiagonalEquiv_tmul, one_smul]

theorem scalarDiagonalEquiv_tmul_real (t : ℝ) (a : K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (scalarDiagonalEquiv (t ⊗ₜ[ℚ] a)).1 w = t * w.val.embedding_of_isReal w.property a := by
  rw [scalarDiagonalEquiv_tmul]
  simp

theorem scalarDiagonalEquiv_tmul_complex (t : ℝ) (a : K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (scalarDiagonalEquiv (t ⊗ₜ[ℚ] a)).2 w = (t : ℂ) * w.val.embedding a := by
  rw [scalarDiagonalEquiv_tmul]
  simp [Complex.real_smul]

theorem normAtPlace_scalarDiagonalEquiv_tmul (w : InfinitePlace K) (t : ℝ) (a : K) :
    mixedEmbedding.normAtPlace w (scalarDiagonalEquiv (t ⊗ₜ[ℚ] a)) = |t| * w a := by
  rw [scalarDiagonalEquiv_tmul, mixedEmbedding.normAtPlace_smul,
    mixedEmbedding.normAtPlace_apply]

theorem scalarDiagonal_dimension :
    Module.finrank ℝ (mixedEmbedding.mixedSpace K) = Module.finrank ℚ K :=
  mixedEmbedding.finrank K

theorem degree_eq_real_add_two_complex :
    Module.finrank ℚ K = InfinitePlace.nrRealPlaces K + 2 * InfinitePlace.nrComplexPlaces K :=
  (InfinitePlace.card_add_two_mul_card_eq_rank K).symm

theorem scalarDiagonal_dimension_eq_infinite_mass :
    (Module.finrank ℝ (mixedEmbedding.mixedSpace K) : ENNReal) =
      (normalizedNumberFieldAdelicStructure K).v
        (normalizedNumberFieldAdelicStructure K).Ωinf := by
  rw [scalarDiagonal_dimension, normalizedNumberFieldAdelicStructure_v_Ωinf]

/-- The literal map on an integral submodule, without a basis choice. -/
def latticeDiagonalMap (M : Submodule (𝓞 K) K) : M →ₗ[ℤ] mixedEmbedding.mixedSpace K :=
  (mixedEmbedding K).toIntAlgHom.toLinearMap.comp (M.subtype.restrictScalars ℤ)

omit [NumberField K] in
@[simp]
theorem latticeDiagonalMap_apply (M : Submodule (𝓞 K) K) (m : M) :
    latticeDiagonalMap M m = mixedEmbedding K (m : K) := rfl

/-- The actual image of the original integral submodule. -/
def diagonalLattice (M : Submodule (𝓞 K) K) : Submodule ℤ (mixedEmbedding.mixedSpace K) :=
  (latticeDiagonalMap M).range

omit [NumberField K] in
theorem mem_diagonalLattice_iff (M : Submodule (𝓞 K) K) (x : mixedEmbedding.mixedSpace K) :
    x ∈ diagonalLattice M ↔ ∃ m : M, mixedEmbedding K (m : K) = x := Iff.rfl

/-- The actual integer-basis vectors with the standard rational scalar action. -/
def scalarIntegerRationalBasis (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) :
    Module.Basis (Fin (Module.finrank ℤ M)) ℚ K := by
  let v : Fin (Module.finrank ℤ M) → K := fun i => NumberFieldFullLattice.integerBasis M hfg i
  have hv : v = NumberFieldFullLattice.integerRationalBasis M hfg hspan := by
    funext i
    exact (NumberFieldFullLattice.integerRationalBasis_coe M hfg hspan i).symm
  let hli_c := letI : Module ℚ K := Module.compHom K (algebraMap ℚ K)
    (NumberFieldFullLattice.integerRationalBasis M hfg hspan).linearIndependent
  have hli : LinearIndependent ℚ v := by
    convert! hli_c using 1
    apply Module.ext
    funext q a
    exact Algebra.smul_def q a
  have hcard : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℚ K := by
    simpa using NumberFieldFullLattice.finrank_integer M hfg hspan
  letI : Nonempty (Fin (Module.finrank ℤ M)) := Fin.pos_iff_nonempty.mp (by
    rw [show Module.finrank ℤ M = Module.finrank ℚ K from
      (Fintype.card_fin _).symm.trans hcard]
    exact Module.finrank_pos)
  exact Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank hcard).ge

@[simp]
theorem scalarIntegerRationalBasis_apply (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) (i : Fin (Module.finrank ℤ M)) :
    scalarIntegerRationalBasis M hfg hspan i =
      (NumberFieldFullLattice.integerBasis M hfg i : K) := by
  rw [scalarIntegerRationalBasis, Module.Basis.coe_mk]

/-- The produced real basis consists of actual embedded integer-basis vectors. -/
def diagonalLatticeBasis (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) :
    Module.Basis (Fin (Module.finrank ℤ M)) ℝ (mixedEmbedding.mixedSpace K) :=
  ((scalarIntegerRationalBasis M hfg hspan).baseChange ℝ).map
    scalarDiagonalEquiv.toLinearEquiv

@[simp]
theorem diagonalLatticeBasis_apply (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) (i : Fin (Module.finrank ℤ M)) :
    diagonalLatticeBasis M hfg hspan i =
      mixedEmbedding K (NumberFieldFullLattice.integerBasis M hfg i : K) := by
  rw [diagonalLatticeBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  change scalarDiagonalEquiv (1 ⊗ₜ[ℚ] scalarIntegerRationalBasis M hfg hspan i) = _
  rw [scalarDiagonalEquiv_one_tmul, scalarIntegerRationalBasis_apply]

theorem diagonalLattice_eq_integerSpan (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) :
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

theorem discrete_diagonalLattice (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) : DiscreteTopology (diagonalLattice M) := by
  classical
  rw [diagonalLattice_eq_integerSpan M hfg hspan]
  infer_instance

open scoped Classical in
theorem isZLattice_diagonalLattice (M : Submodule (𝓞 K) K) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set K) = ⊤) :
    letI := discrete_diagonalLattice M hfg hspan
    IsZLattice ℝ (diagonalLattice M) := by
  let := discrete_diagonalLattice M hfg hspan
  simpa only [diagonalLattice_eq_integerSpan M hfg hspan] using
    (inferInstance : IsZLattice ℝ
      (Submodule.span ℤ (Set.range (diagonalLatticeBasis M hfg hspan))))

end ArakelovGeometry.NumberFieldArchimedeanDiagonal
