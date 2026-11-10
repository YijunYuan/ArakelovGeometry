/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.DirectSumDualArchimedean

/-!
# Adelic profile direct sums

Chen–Moriwaki Proposition 4.1.35, including the strongly adelic clause.
The norm family is the existing actual completed direct sum. Both primal and
actual dual measurability are proved; no measurability certificate is assumed.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

variable (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
  (ψ : S.Ω → NormShape) (hψ : NormShape.IsMeasurableFamily ψ)
  (U : Set S.Ω) (hU : MeasurableSet U) (hfinU : S.v U < ⊤)
  (hmax : ∀ ω ∉ U,
    Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The adelic bundle on the actual profile direct sum, for source-measurable
profiles equal to maximum outside a measurable set of finite measure. -/
noncomputable def directSum : AdelicVectorBundle S (E × F) where
  toNormFamily := V.toNormFamily.directSum W.toNormFamily ψ
  isMeasurable := V.isMeasurable.directSum W.isMeasurable hψ
  dual_isMeasurable := V.toNormFamily.directSum_dual_isMeasurable W.toNormFamily ψ hS
    V.dual_isMeasurable W.dual_isMeasurable hψ
  isDominated := V.isDominated.directSum W.isDominated ψ U hU hfinU hmax hS

@[simp]
theorem directSum_toNormFamily :
    (V.directSum W ψ hψ U hU hfinU hmax hS).toNormFamily =
      V.toNormFamily.directSum W.toNormFamily ψ := rfl

/-- Source Proposition 4.1.35, strongly adelic clause, including rank zero. -/
theorem directSum_isStronglyAdelic (hV : V.IsStronglyAdelic) (hW : W.IsStronglyAdelic) :
    (V.directSum W ψ hψ U hU hfinU hmax hS).IsStronglyAdelic :=
  hV.directSum hW ψ U hU hfinU hmax hS

end ArakelovGeometry.AdelicVectorBundle
