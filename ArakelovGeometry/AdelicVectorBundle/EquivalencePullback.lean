/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
public import ArakelovGeometry.AdelicVectorBundle.DegreeIsometryDual

/-!
# Pullback of ordinary adelic bundles along linear equivalences

An equivalence produces the dual measurability required by the canonical
injective pullback. Completed inverse isometries transport genuine determinant
measurability and canonical degree without hypotheses on the place space.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'
variable {M : Type u} [Field M] {T : AdelicStructure.{u, v} M}
  {X : Type w} [AddCommGroup X] [Module M X] [FiniteDimensional M X]
  {Y : Type w'} [AddCommGroup Y] [Module M Y] [FiniteDimensional M Y]

/-- The canonical injective pullback along an equivalence, with actual dual
measurability produced by the completed transpose isometry. -/
def pullbackEquiv (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y) :
    AdelicVectorBundle T X := by
  apply V.pullback e.toLinearMap e.injective
  apply NormFamily.IsMeasurable.of_completed_isometry V.toNormFamily.dual
    (V.toNormFamily.pullback e.toLinearMap e.injective).dual e.dualMap
  · intro ω z
    let η := V.toNormFamily.pullback e.toLinearMap e.injective
    exact η.dualEquiv_norm_eq_of_completed_isometry V.toNormFamily ω e (fun _ => rfl) z
  · exact V.dual_isMeasurable

@[simp]
theorem pullbackEquiv_toNormFamily (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y) :
    (V.pullbackEquiv e).toNormFamily = V.toNormFamily.pullback e.toLinearMap e.injective := rfl

/-- The completed inverse is an actual isometry at every place. -/
theorem pullbackEquiv_inverse_norm (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y)
    (ω : T.Ω) (z : (T.ϕ ω).Completion ⊗[M] Y) :
    (V.pullbackEquiv e).toNormFamily.norm ω
      (e.symm.toLinearMap.baseChange (T.ϕ ω).Completion z) = V.toNormFamily.norm ω z := by
  let eω := e.baseChange M (T.ϕ ω).Completion X Y
  change V.toNormFamily.norm ω (eω (eω.symm z)) = V.toNormFamily.norm ω z
  rw [eω.apply_symm_apply]

/-- Actual determinant measurability transports from the original bundle. -/
theorem pullbackEquiv_determinant_isMeasurable (V : AdelicVectorBundle T Y)
    (e : X ≃ₗ[M] Y) (hdet : V.toNormFamily.determinant.IsMeasurable) :
    (V.pullbackEquiv e).toNormFamily.determinant.IsMeasurable :=
  V.toNormFamily.determinant_isMeasurable_of_completed_isometry
    (V.pullbackEquiv e).toNormFamily e.symm (V.pullbackEquiv_inverse_norm e) hdet

/-- The genuine equivalence pullback preserves the canonical determinant
degree; its determinant measurability is produced, without base regularity. -/
theorem degreeOfMeasurableDeterminant_pullbackEquiv [T.IsProper]
    (V : AdelicVectorBundle T Y) (e : X ≃ₗ[M] Y)
    (hdet : V.toNormFamily.determinant.IsMeasurable)
    (hN : ∀ ω ∈ T.Ωinf, IsRCLikeNormedField (T.ϕ ω).Completion) :
    (V.pullbackEquiv e).degreeOfMeasurableDeterminant
      (V.pullbackEquiv_determinant_isMeasurable e hdet) hN =
        V.degreeOfMeasurableDeterminant hdet hN :=
  (V.degreeOfMeasurableDeterminant_eq_of_completed_isometry
    (V.pullbackEquiv e) e.symm hdet hN (V.pullbackEquiv_inverse_norm e)).symm

end ArakelovGeometry.AdelicVectorBundle
