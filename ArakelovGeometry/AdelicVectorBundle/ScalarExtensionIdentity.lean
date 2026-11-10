/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Bidual
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionTower
public import ArakelovGeometry.Analysis.ScalarExtensionIdentity

/-!
# Identity scalar extension of norm families

The actual completed identity extension agrees with the bidual family under
canonical evaluation. Archimedean bidual equality uses the usual normalized
real or complex norm explicitly.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- The explicitly specified completed-field embedding is isometric. -/
theorem isometry_normedAlgebraCompletionOfEq {L : Type*} [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) (h : w.restriction K = v) :
    Isometry (normedAlgebraCompletionOfEq v w h).toAlgebra.algebraMap := by
  subst v
  exact isometry_algebraMap_completion w K

/-- The completed embedding attached to the identity field extension is
the identity on the completed field. -/
theorem algebraMap_normedAlgebraCompletionOfEq_self (v : AbsoluteValue K ℝ)
    (h : v.restriction K = v) (a : v.Completion) :
    (normedAlgebraCompletionOfEq v v h).toAlgebra.algebraMap a = a := by
  let := normedAlgebraCompletionOfEq v v h
  let : Algebra v.Completion v.Completion :=
    (normedAlgebraCompletionOfEq v v h).toAlgebra
  change algebraMap v.Completion v.Completion a = a
  refine UniformSpace.Completion.induction_on a ?_ ?_
  · exact isClosed_eq (isometry_normedAlgebraCompletionOfEq v v h).continuous continuous_id
  · intro b
    change algebraMap v.Completion v.Completion (algebraMap K v.Completion b.ofAbs) =
      algebraMap K v.Completion b.ofAbs
    rw [algebraMap_normedAlgebraCompletionOfEq_coe]
    rfl

/-- The canonical normed-algebra structure for the completed identity
extension agrees with the standard self-algebra structure. -/
theorem normedAlgebraCompletionOfEq_self (v : AbsoluteValue K ℝ)
    (h : v.restriction K = v) :
    normedAlgebraCompletionOfEq v v h = NormedAlgebra.id v.Completion := by
  have hinj : Function.Injective
      (fun a : NormedAlgebra v.Completion v.Completion ↦ a.toAlgebra) := by
    intro a b hab
    cases a
    cases b
    cases hab
    rfl
  apply hinj
  apply Algebra.algebra_ext
  intro a
  exact algebraMap_normedAlgebraCompletionOfEq_self v h a

end AbsoluteValue

namespace ArakelovGeometry

universe u v w

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- The unique extending place above a base place for the identity extension. -/
def scalarExtensionIdentityPlace (ω : S.Ω) : S.ParameterSpaceExtension K where
  base := ω
  abv := S.ϕ ω
  restrict_eq := by ext a; rfl

/-- Every place of the identity extension is its canonical base-place lift. -/
theorem scalarExtensionIdentityPlace_base (x : S.ParameterSpaceExtension K) :
    scalarExtensionIdentityPlace S x.base = x := by
  refine AdelicStructure.ParameterSpaceExtension.ext S K
    (x := scalarExtensionIdentityPlace S x.base) (y := x) rfl ?_
  have hx : x.abv = S.ϕ x.base := by
    ext a
    exact congrArg (fun v : AbsoluteValue K ℝ ↦ v a) x.restrict_eq
  exact hx.symm

variable {E : Type w} [AddCommGroup E] [Module K E]

/-- Under the identity extension, the completed scalar-extension
equivalence is the rational inclusion after the canonical tensor left unit. -/
theorem completedScalarExtensionEquiv_self (v : AbsoluteValue K ℝ)
    (h : v.restriction K = v) (z : v.Completion ⊗[K] (K ⊗[K] E)) :
    let mV : Module v.Completion (v.Completion ⊗[K] E) := inferInstance
    let a := AbsoluteValue.normedAlgebraCompletionOfEq v v h
    let : NormedAlgebra v.Completion v.Completion := a
    let : Algebra v.Completion v.Completion := a.toAlgebra
    let : Module v.Completion v.Completion := a.toAlgebra.toModule
    let : Module v.Completion (v.Completion ⊗[K] E) := mV
    completedScalarExtensionEquiv E v v h z =
      (1 : v.Completion) ⊗ₜ[v.Completion]
        ((TensorProduct.lid K E).toLinearMap.baseChange v.Completion z) := by
  intro mV a na aa ma mv
  let : NormedAlgebra v.Completion v.Completion := na
  let : Algebra v.Completion v.Completion := aa
  let : Module v.Completion v.Completion := ma
  let : Module v.Completion (v.Completion ⊗[K] E) := mv
  let : DistribMulAction v.Completion v.Completion := ma.toDistribMulAction
  let : DistribMulAction v.Completion (v.Completion ⊗[K] E) := mv.toDistribMulAction
  let : SMul v.Completion v.Completion := ma.toDistribMulAction.toSMul
  let : SMul v.Completion (v.Completion ⊗[K] E) := mv.toDistribMulAction.toSMul
  let : TensorProduct.CompatibleSMul v.Completion v.Completion v.Completion
      (v.Completion ⊗[K] E) :=
    ⟨fun r b x ↦ Quotient.sound' (AddConGen.Rel.of _ _ (TensorProduct.Eqv.of_smul r b x))⟩
  have hscalar (r : v.Completion) : r • (1 : v.Completion) = r := by
    change a.toAlgebra.algebraMap r * 1 = r
    rw [mul_one]
    exact AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_self v h r
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, TensorProduct.tmul_add, hz, ht]
  | tmul b y =>
    induction y using TensorProduct.inductionOn with
    | add y t hy ht => simp only [TensorProduct.tmul_add, map_add, hy, ht]
    | tmul c x =>
      rw [completedScalarExtensionEquiv_tmul]
      simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul]
      calc
        _ = (1 : v.Completion) ⊗ₜ[v.Completion]
            ((algebraMap K v.Completion c * b) • ((1 : v.Completion) ⊗ₜ[K] x)) := by
          rw [← TensorProduct.smul_tmul, hscalar]
        _ = _ := by
          congr 1
          change (algebraMap K v.Completion c * b * 1) ⊗ₜ[K] x = b ⊗ₜ[K] (c • x)
          rw [mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul]

namespace NormFamily

variable {S} [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- The projective identity extension agrees with the original completed
fibre norm under the canonical tensor left unit. -/
theorem projectiveScalarExtension_self (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (K ⊗[K] E)) :
    (ξ.projectiveScalarExtension (L := K)).norm (scalarExtensionIdentityPlace S ω) z =
      ξ.norm ω ((TensorProduct.lid K E).toLinearMap.baseChange (S.ϕ ω).Completion z) := by
  let aVV := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) (S.ϕ ω)
    (scalarExtensionIdentityPlace S ω).restrict_eq
  let : NormedAlgebra (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV
  let : Algebra (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV.toAlgebra
  let : Module (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV.toAlgebra.toModule
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  change scalarExtensionProjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ ω) (S.ϕ ω)
      (scalarExtensionIdentityPlace S ω).restrict_eq z) = _
  rw [completedScalarExtensionEquiv_self (E := E) (S.ϕ ω)
    (scalarExtensionIdentityPlace S ω).restrict_eq z]
  exact scalarExtensionProjectiveSeminorm_one_tmul_self aVV
    (AbsoluteValue.normedAlgebraCompletionOfEq_self _ _) _

/-- The completed bidual norm is the supremum over all actual completed
linear functionals, expressed in the original fibre norm. -/
theorem dual_dual_norm_eval_eq_sSup (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion x) =
      sSup (Set.range fun f : ((S.ϕ ω).Completion ⊗[K] E) →ₗ[(S.ϕ ω).Completion]
          (S.ϕ ω).Completion ↦ ‖f x‖ / linearMapOperatorSeminorm f) := by
  intro nV nsV
  let := nV
  let := nsV
  rw [ξ.dual.dual_norm_eq_sSup]
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dualBaseChangeEquiv K (S.ϕ ω).Completion E z, ?_⟩
    simp only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
    rfl
  · rintro ⟨f, rfl⟩
    refine ⟨(dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm f, ?_⟩
    simp only [dualBaseChangeEquiv_eval, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
    change ‖dualBaseChangeEquiv K (S.ϕ ω).Completion E
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm f) x‖ /
      linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm f)) = _
    rw [LinearEquiv.apply_symm_apply]

/-- Injective identity extension is the actual completed bidual norm, with
no ultrametricity assumption on the original norm family. -/
theorem injectiveScalarExtension_self (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (K ⊗[K] E)) :
    (ξ.injectiveScalarExtension (L := K)).norm (scalarExtensionIdentityPlace S ω) z =
      ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion
        ((TensorProduct.lid K E).toLinearMap.baseChange (S.ϕ ω).Completion z)) := by
  let aVV := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) (S.ϕ ω)
    (scalarExtensionIdentityPlace S ω).restrict_eq
  let : NormedAlgebra (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV
  let : Algebra (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV.toAlgebra
  let : Module (S.ϕ ω).Completion (S.ϕ ω).Completion := aVV.toAlgebra.toModule
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  change scalarExtensionInjectiveSeminorm
    (completedScalarExtensionEquiv E (S.ϕ ω) (S.ϕ ω)
      (scalarExtensionIdentityPlace S ω).restrict_eq z) = _
  rw [completedScalarExtensionEquiv_self (E := E) (S.ϕ ω)
    (scalarExtensionIdentityPlace S ω).restrict_eq z]
  rw [scalarExtensionInjectiveSeminorm_one_tmul]
  exact (ξ.dual_dual_norm_eval_eq_sSup ω _).symm

/-- Under the source's usual Archimedean normalization, identity scalar
extension equals the bidual norm at every actual completed fibre. -/
theorem scalarExtension_self
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (K ⊗[K] E)) :
    (ξ.scalarExtension (L := K)).norm (scalarExtensionIdentityPlace S ω) z =
      ξ.dual.dual.norm ω ((Module.Dual.eval K E).baseChange (S.ϕ ω).Completion
        ((TensorProduct.lid K E).toLinearMap.baseChange (S.ϕ ω).Completion z)) := by
  by_cases hω : ω ∈ S.Ωfin
  · exact (ξ.scalarExtension_norm_of_mem_Ωfin (scalarExtensionIdentityPlace S ω) hω z).trans
      (ξ.injectiveScalarExtension_self ω z)
  · exact (ξ.scalarExtension_norm_of_not_mem_Ωfin
      (scalarExtensionIdentityPlace S ω) hω z).trans
      ((ξ.projectiveScalarExtension_self ω z).trans
        (ξ.dual_dual_norm_eval_eq_of_isRCLike ω (hS ω hω) _).symm)

/-- An ultrametric norm family is unchanged by the identity scalar
extension, with the actual usual Archimedean normalization explicit. -/
theorem scalarExtension_self_of_isUltrametric (hξ : ξ.IsUltrametric)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (K ⊗[K] E)) :
    (ξ.scalarExtension (L := K)).norm (scalarExtensionIdentityPlace S ω) z =
      ξ.norm ω ((TensorProduct.lid K E).toLinearMap.baseChange (S.ϕ ω).Completion z) := by
  rw [ξ.scalarExtension_self hS ω z]
  by_cases hω : ω ∈ S.Ωfin
  · exact hξ.dual_dual_norm_eval ω hω _
  · exact ξ.dual_dual_norm_eval_eq_of_isRCLike ω (hS ω hω) _

end NormFamily

end ArakelovGeometry

end
