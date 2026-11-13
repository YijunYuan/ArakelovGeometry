/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Isomorphism.Subspace
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.EquivMeasure
import Mathlib.CategoryTheory.Category.Init

/-!
# Compatible common algebraic-closure realizations

For arbitrary algebraic L/K, the canonical closure of L is also a closure of
K. A chosen K-equivalence between the two existing closures produces an actual
embedding of L into the closure of K and a compatible local L-algebra there.
The same field equivalence is L-linear for this algebra, and the existing
actual place and scalar-norm transport APIs apply to it. The choices are
coherent, with no uniqueness or absolute-invariance premise.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct
noncomputable section

namespace ArakelovGeometry
universe u w wE
variable (K : Type u) [Field K] (L : Type w) [Field L]
  [Algebra K L] [Algebra.IsAlgebraic K L]

/-- A chosen actual K-equivalence of the two existing canonical closures. -/
def commonAlgebraicClosureEquiv : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure L :=
  IsAlgClosure.equiv K (AlgebraicClosure K) (AlgebraicClosure L)

/-- The compatible actual embedding of L into the existing closure of K. -/
def commonAlgebraicClosureEmbedding : L →ₐ[K] AlgebraicClosure K :=
  (commonAlgebraicClosureEquiv K L).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom K L (AlgebraicClosure L))

/-- The actual L-algebra on the existing closure of K, induced by the embedding. -/
@[instance_reducible]
def commonAlgebraicClosureAlgebra : Algebra L (AlgebraicClosure K) :=
  (commonAlgebraicClosureEmbedding K L).toRingHom.toAlgebra

/-- Its coefficient map is exactly the produced compatible embedding. -/
theorem commonAlgebraicClosureAlgebraMap (a : L) :
    letI := commonAlgebraicClosureAlgebra K L
    algebraMap L (AlgebraicClosure K) a = commonAlgebraicClosureEmbedding K L a := rfl

/-- The induced L-algebra fixes the original K-algebra and gives a true tower. -/
theorem commonAlgebraicClosure_isScalarTower :
    letI := commonAlgebraicClosureAlgebra K L
    IsScalarTower K L (AlgebraicClosure K) := by
  let := commonAlgebraicClosureAlgebra K L
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (commonAlgebraicClosureEmbedding K L).commutes a |>.symm

/-- Algebraicity over L is produced from the compatible tower over K. -/
theorem commonAlgebraicClosure_isAlgebraic :
    letI := commonAlgebraicClosureAlgebra K L
    Algebra.IsAlgebraic L (AlgebraicClosure K) := by
  let := commonAlgebraicClosureAlgebra K L
  let := commonAlgebraicClosure_isScalarTower K L
  exact Algebra.IsAlgebraic.tower_top L (K := K)

/-- The existing closure of K is an actual closure of L for the induced algebra. -/
theorem commonAlgebraicClosure_isAlgClosure :
    letI := commonAlgebraicClosureAlgebra K L
    IsAlgClosure L (AlgebraicClosure K) := by
  let := commonAlgebraicClosureAlgebra K L
  exact ⟨inferInstance, commonAlgebraicClosure_isAlgebraic K L⟩

/-- The same chosen K-field map is an L-equivalence for the produced L-algebra. -/
def commonAlgebraicClosureLEquiv :
    letI := commonAlgebraicClosureAlgebra K L
    AlgebraicClosure K ≃ₐ[L] AlgebraicClosure L := by
  letI := commonAlgebraicClosureAlgebra K L
  refine { (commonAlgebraicClosureEquiv K L).toRingEquiv with commutes' := ?_ }
  intro a
  change commonAlgebraicClosureEquiv K L
    ((commonAlgebraicClosureEquiv K L).symm (algebraMap L (AlgebraicClosure L) a)) = _
  exact (commonAlgebraicClosureEquiv K L).apply_symm_apply _

/-- Restriction of this L-equivalence recovers the same original K-equivalence. -/
theorem commonAlgebraicClosureLEquiv_restrictScalars :
    letI := commonAlgebraicClosureAlgebra K L
    letI := commonAlgebraicClosure_isScalarTower K L
    (commonAlgebraicClosureLEquiv K L).restrictScalars K = commonAlgebraicClosureEquiv K L := rfl

/-- The produced embedding's actual image is a genuine intermediate field. -/
def commonAlgebraicClosureIntermediateField : IntermediateField K (AlgebraicClosure K) :=
  (commonAlgebraicClosureEmbedding K L).fieldRange

/-- The actual image-field equivalence identifies an arbitrary algebraic
extension with this genuine intermediate field, without changing coefficients. -/
def commonAlgebraicClosureRangeEquiv :
    L ≃ₐ[K] commonAlgebraicClosureIntermediateField K L :=
  (commonAlgebraicClosureEmbedding K L).equivFieldRange

/-- The image-field inclusion is exactly the original produced embedding. -/
theorem commonAlgebraicClosureRangeEquiv_val (a : L) :
    (commonAlgebraicClosureRangeEquiv K L a).val = commonAlgebraicClosureEmbedding K L a :=
  (commonAlgebraicClosureEmbedding K L).equivFieldRange_apply_coe a

namespace AdelicStructure

/-- The actual common-closure K-place map preserves the extension measures. -/
theorem measurePreserving_commonAlgebraicClosure (S : AdelicStructure K) :
    MeasurePreserving (ParameterSpaceExtension.algEquivMeasurableEquiv S
      (commonAlgebraicClosureEquiv K L))
      (S.algebraicExtension (AlgebraicClosure L)).v
      (S.algebraicExtension (AlgebraicClosure K)).v :=
  Algebraic.measurePreserving_algEquivMeasurableEquiv S (commonAlgebraicClosureEquiv K L)

/-- The same true transport over the actual extended curve uses the produced
L-algebra and algebraicity, without regularity on that place space. -/
theorem measurePreserving_commonAlgebraicClosureOverExtension
    (S : AdelicStructure K) :
    letI := commonAlgebraicClosureAlgebra K L
    letI := commonAlgebraicClosure_isAlgebraic K L
    MeasurePreserving (ParameterSpaceExtension.algEquivMeasurableEquiv
      (S.algebraicExtension L) (commonAlgebraicClosureLEquiv K L))
      ((S.algebraicExtension L).algebraicExtension (AlgebraicClosure L)).v
      ((S.algebraicExtension L).algebraicExtension (AlgebraicClosure K)).v := by
  let := commonAlgebraicClosureAlgebra K L
  let := commonAlgebraicClosure_isAlgebraic K L
  exact Algebraic.measurePreserving_algEquivMeasurableEquiv (S.algebraicExtension L)
    (commonAlgebraicClosureLEquiv K L)

end AdelicStructure
namespace NormFamily
open AdelicStructure.ParameterSpaceExtension
variable {S : AdelicStructure K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Actual direct rational scalar norm profiles pass through the produced
common-closure field equivalence and the genuine place map. -/
theorem scalarExtension_commonAlgebraicClosure_norm (ξ : NormFamily S E)
    (x : AdelicStructure.ParameterSpaceExtension S (AlgebraicClosure L))
    (z : AlgebraicClosure K ⊗[K] E) :
    (ξ.scalarExtension (L := AlgebraicClosure L)).norm x
      ((1 : x.abv.Completion) ⊗ₜ[AlgebraicClosure L]
        scalarExtensionSemilinearEquiv (E := E) (commonAlgebraicClosureEquiv K L) z) =
      (ξ.scalarExtension (L := AlgebraicClosure K)).norm
        (pullbackAlgEquiv S (commonAlgebraicClosureEquiv K L) x)
        ((1 : (pullbackAlgEquiv S (commonAlgebraicClosureEquiv K L) x).abv.Completion)
          ⊗ₜ[AlgebraicClosure K] z) :=
  ξ.scalarExtension_norm_rational_algEquiv (commonAlgebraicClosureEquiv K L) x z

/-- The actual same field map acts over L on rational sections of every norm
family on S_L, using its compatible produced L-algebra on the closure of K. -/
theorem scalarExtension_commonAlgebraicClosureOverExtension_norm
    {X : Type*} [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    (η : NormFamily (S.algebraicExtension L) X)
    (x : AdelicStructure.ParameterSpaceExtension (S.algebraicExtension L) (AlgebraicClosure L)) :
    letI := commonAlgebraicClosureAlgebra K L
    letI := commonAlgebraicClosure_isAlgebraic K L
    ∀ z : AlgebraicClosure K ⊗[L] X,
      (η.scalarExtension (L := AlgebraicClosure L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[AlgebraicClosure L]
          scalarExtensionSemilinearEquiv (E := X) (commonAlgebraicClosureLEquiv K L) z) =
        (η.scalarExtension (L := AlgebraicClosure K)).norm
          (pullbackAlgEquiv (S.algebraicExtension L) (commonAlgebraicClosureLEquiv K L) x)
          ((1 : (pullbackAlgEquiv (S.algebraicExtension L)
            (commonAlgebraicClosureLEquiv K L) x).abv.Completion) ⊗ₜ[AlgebraicClosure K] z) := by
  let := commonAlgebraicClosureAlgebra K L
  let := commonAlgebraicClosure_isAlgebraic K L
  intro z
  exact η.scalarExtension_norm_rational_algEquiv (commonAlgebraicClosureLEquiv K L) x z

end NormFamily
end ArakelovGeometry
