/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Descent
public import ArakelovGeometry.AdelicVectorBundle.Tensor.HermitianDual

/-!
# Bool-indexed tensors and the ordinary binary quotient

The binary instability argument for Bost page 31 uses Bool-indexed factors,
whereas the real-filtration descent and A9 consumer use ordinary binary tensors.
This module transports the existing tensor product, convolution filtration and
quotient base change through their canonical equivalences. No new filtration
or notion of geometric instability is introduced.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u

/-- The binary indexing convention: false is the left factor and true the right. -/
def boolEquivUnitSumUnit : Bool ≃ Unit ⊕ Unit :=
  Equiv.boolEquivPUnitSumPUnit.{0, 0}.trans
    (Equiv.sumCongr (Equiv.ofUnique PUnit Unit) (Equiv.ofUnique PUnit Unit))

/-- The existing binary factor family, reindexed by false/true. -/
abbrev BoolTensorFactors (E F : Type u) : Bool → Type u :=
  fun j ↦ BinaryTensorFactors E F (boolEquivUnitSumUnit j)

instance boolTensorFactorsNontrivial {E F : Type u} [Nontrivial E] [Nontrivial F]
    (j : Bool) : Nontrivial (BoolTensorFactors E F j) := by
  cases j <;> assumption

variable (K : Type*) [Field K] (E : Bool → Type*)
  [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]

/-- Canonical Bool-to-binary tensor transport for the binary Bost application.
It is reindexing followed by the existing singleton-grouping equivalence. -/
def boolTensorEquiv : (⨂[K] j, E j) ≃ₗ[K] E false ⊗[K] E true :=
  (PiTensorProduct.reindex K E boolEquivUnitSumUnit).trans
    (binaryTensorEquiv K (fun j ↦ E (boolEquivUnitSumUnit.symm j)))

@[simp]
theorem boolTensorEquiv_tprod (x : ∀ j, E j) :
    boolTensorEquiv K E (⨂ₜ[K] j, x j) = x false ⊗ₜ[K] x true := by
  change binaryTensorEquiv K (fun j ↦ E (boolEquivUnitSumUnit.symm j))
    (PiTensorProduct.reindex K E boolEquivUnitSumUnit (⨂ₜ[K] j, x j)) = _
  rw [PiTensorProduct.reindex_tprod, binaryTensorEquiv_tprod]
  rfl

/-- Bool tensor transport commutes with actual tensor scalar extension on all
vectors, for the binary Bost quotient. -/
theorem tensorBaseChangeEquiv_bool (L : Type*) [Field L] [Algebra K L] :
    (boolTensorEquiv L (fun j ↦ L ⊗[K] E j)).toLinearMap ∘ₗ
      (tensorBaseChangeEquiv K L E).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L (E false) (E true)).toLinearMap ∘ₗ
      (boolTensorEquiv K E).toLinearMap.baseChange L := by
  apply LinearMap.restrictScalars_injective K
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change boolTensorEquiv L (fun j ↦ L ⊗[K] E j)
      (tensorBaseChangeEquiv K L E (a ⊗ₜ[K] (⨂ₜ[K] j, x j))) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L (E false) (E true)
      ((boolTensorEquiv K E).toLinearMap.baseChange L (a ⊗ₜ[K] (⨂ₜ[K] j, x j)))
  simp only [tensorBaseChangeEquiv_tmul_tprod, map_smul, boolTensorEquiv_tprod,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

section IndependentPair

universe wE wF

variable (R : Type*) [Field R] (V : Type wE) (W : Type wF)
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Independently sized factors in the common universe required by a Bool family. -/
abbrev LiftedBoolTensorFactors := BoolTensorFactors (ULift.{wF} V) (ULift.{wE} W)

/-- The Bool tensor of lifted factors is the original ordinary binary tensor. -/
def boolTensorPairEquiv : (⨂[R] j, LiftedBoolTensorFactors V W j) ≃ₗ[R] V ⊗[R] W :=
  (boolTensorEquiv R (LiftedBoolTensorFactors V W)).trans
    (TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv)

end IndependentPair

end ArakelovGeometry

namespace Submodule

open ArakelovGeometry

variable {K : Type*} [Field K] {E : Bool → Type*}
  [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]

/-- The Bool convolution has exactly the ordinary binary convolution layers,
under the canonical equivalence used in the Bost p31 assembly. -/
theorem piTensorFiltration_map_boolTensorEquiv
    (F : ∀ j, ℝ → Submodule K (E j)) (γ : ℝ) :
    (piTensorFiltration F γ).map (boolTensorEquiv K E).toLinearMap =
      tensorFiltration (F false) (F true) γ := by
  classical
  apply le_antisymm
  · rw [piTensorFiltration, map_iSup]
    apply iSup_le
    intro t
    rw [map_iSup]
    apply iSup_le
    intro ht
    rw [PiTensorProduct.mapIncl, PiTensorProduct.map_range_eq_span_tprod, map_span]
    apply span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp only [LinearEquiv.coe_coe, boolTensorEquiv_tprod]
    apply tmul_mem_tensorFiltration _ (x false).property (x true).property
    simpa only [Fintype.sum_bool, add_comm] using ht
  · apply iSup_le
    intro t
    apply iSup_le
    intro u
    apply iSup_le
    intro htu
    rintro _ ⟨z, rfl⟩
    induction z with
    | tmul x y =>
      let s : Bool → ℝ := fun j ↦ if j then u else t
      let v : ∀ j, E j := fun j ↦ match j with
        | false => x.val
        | true => y.val
      refine ⟨⨂ₜ[K] j, v j, ?_, ?_⟩
      · apply tprod_mem_piTensorFiltration (t := s)
        · simpa [s, Fintype.sum_bool, add_comm] using htu
        · intro j
          cases j
          · exact x.property
          · exact y.property
      · simp [v]
    | add x y hx hy => simpa only [map_add] using add_mem hx hy

variable {L Q : Type*} [Field L] [Algebra K L] [AddCommGroup Q] [Module K Q]

/-- The same quotient over the extension field, expressed in Bool and ordinary
binary tensor coordinates. This is an equality of the prescribed maps. -/
theorem piTensorQuotientBaseChange_bool (q : E false ⊗[K] E true →ₗ[K] Q) :
    piTensorQuotientBaseChange (L := L)
      (q.comp (boolTensorEquiv K E).toLinearMap) =
    (tensorQuotientBaseChange q).comp
      (boolTensorEquiv L (fun j ↦ L ⊗[K] E j)).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (tensorBaseChangeEquiv K L E).surjective z
  simp only [piTensorQuotientBaseChange, tensorQuotientBaseChange, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have he := DFunLike.congr_fun (tensorBaseChangeEquiv_bool K E L) y
  change boolTensorEquiv L (fun j ↦ L ⊗[K] E j) (tensorBaseChangeEquiv K L E y) =
    TensorProduct.AlgebraTensorModule.distribBaseChange K L (E false) (E true)
      ((boolTensorEquiv K E).toLinearMap.baseChange L y) at he
  rw [he, LinearEquiv.symm_apply_apply, LinearMap.baseChange_comp]
  rfl

/-- The Bool and binary scalar-extended quotient filtrations have identical
actual layers, so their expectations agree without extra invariance assumptions. -/
theorem piTensor_image_bool_baseChange
    (q : E false ⊗[K] E true →ₗ[K] Q)
    (F : ∀ j, ℝ → Submodule L (L ⊗[K] E j)) (t : ℝ) :
    (piTensorFiltration F t).map (piTensorQuotientBaseChange (L := L)
      (q.comp (boolTensorEquiv K E).toLinearMap)) =
    (tensorFiltration (F false) (F true) t).map (tensorQuotientBaseChange q) := by
  rw [piTensorQuotientBaseChange_bool, map_comp, piTensorFiltration_map_boolTensorEquiv]

end Submodule

namespace Submodule

open Module

variable {k : Type*} [Field k] {ι : Bool → Type*}
  {E V : Bool → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
  {Q : Type*} [AddCommGroup Q] [Module k Q]

/-- Transporting weighted bases along factor equivalences preserves the actual
quotient convolution layers. This returns coordinate negative filtrations to
the original factors in Bost's binary instability argument. -/
theorem piTensorFiltration_image_map_basis
    (e : ∀ j, E j ≃ₗ[k] V j) (b : ∀ j, Basis (ι j) k (E j))
    (w : ∀ j, ι j → ℝ) (q : (⨂[k] j, V j) →ₗ[k] Q) (t : ℝ) :
    (piTensorFiltration (fun j s ↦ span k ((b j).map (e j) '' {i | s ≤ w j i})) t).map q =
    (piTensorFiltration (fun j s ↦ span k (b j '' {i | s ≤ w j i})) t).map
      (q.comp (PiTensorProduct.congr e).toLinearMap) := by
  rw [piTensorFiltration_eq_span (fun j ↦ (b j).map (e j)) w (fun _ _ ↦ rfl),
    piTensorFiltration_eq_span b w (fun _ _ ↦ rfl), map_span, map_span,
    Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro p _
  simp [Basis.piTensorProduct_apply]

end Submodule
