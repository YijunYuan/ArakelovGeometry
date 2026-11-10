/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianDegree
import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtensionMeasurable
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionHermitianDomination

/-!
# Degree of the actual Hermitian extended determinant line

The proved actual determinant norm identity constructs the Hermitian extended
determinant as an adelic line for every algebraic field extension. Its line
degree equals the original vector degree under the original degree context.
Under original common countable density, primal and dual measurability and
domination construct the actual Hermitian extended vector bundle. For finite
extensions the proved target common density gives equality of vector degrees.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Common countable density gives measurability of the actual Hermitian
extended dual through the canonical completed dual transport. -/
theorem IsMeasurable.hermitianScalarExtension_dual_of_common_countable_dense_subfield
    (ξ : NormFamily S E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hH : ξ.IsHermitian hS) (hm : ξ.IsMeasurable)
    (hcount : S.HasCommonCountableDenseSubfield) :
    (hermitianScalarExtension ξ hS hL hH).dual.IsMeasurable := by
  let d := dualBaseChangeEquiv K L E
  let θ := hermitianScalarExtension ξ.dual hS hL hH.dual
  have hθ : θ.IsMeasurable :=
    IsMeasurable.hermitianScalarExtension_of_common_countable_dense_subfield
      ξ.dual hS hH.dual (hm.dual_of_common_countable_dense_subfield hcount) hcount
  have he : (hermitianScalarExtension ξ hS hL hH).dual =
      θ.pullback d.symm.toLinearMap d.symm.injective := by
    apply NormFamily.ext
    intro x z
    change S.ParameterSpaceExtension L at x
    change x.abv.Completion ⊗[L] Module.Dual L (L ⊗[K] E) at z
    change (hermitianScalarExtension ξ hS hL hH).dual.norm x z =
      θ.norm x (d.symm.toLinearMap.baseChange x.abv.Completion z)
    have hc : d.toLinearMap.baseChange x.abv.Completion
        (d.symm.toLinearMap.baseChange x.abv.Completion z) = z :=
      (LinearEquiv.baseChange L x.abv.Completion _ _ d).apply_symm_apply z
    have h := hermitianScalarExtension_dual ξ hS hL hH x
      (d.symm.toLinearMap.baseChange x.abv.Completion z)
    rw [hc] at h
    exact h.symm
  rw [he]
  exact hθ.pullback d.symm.toLinearMap d.symm.injective

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wL

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The actual determinant of the Hermitian scalar extension is an adelic
line. Original determinant measurability and domination suffice; whole-vector
extension measurability is not a hypothesis. -/
def hermitianScalarExtensionDeterminant (V : AdelicVectorBundle S E)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    AdelicVectorBundle (S.algebraicExtension L)
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)) :=
  ofLine (NormFamily.hermitianScalarExtension V.toNormFamily hS hL hV).determinant
    NormFamily.determinant_finrank
    (NormFamily.IsMeasurable.determinant_hermitianScalarExtension V.toNormFamily hS hL hV
      (V.isMeasurable.determinant_of_discrete_or_countable hbase))
    (NormFamily.IsDominated.determinant_hermitianScalarExtension V.toNormFamily hS hL hV
      (V.determinantOfMeasurableBase hbase hS).isDominated
      (V.isMeasurable.determinant_of_discrete_or_countable hbase))

@[simp]
theorem hermitianScalarExtensionDeterminant_toNormFamily (V : AdelicVectorBundle S E)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtensionDeterminant (L := L) hbase hS hL hV).toNormFamily =
      (NormFamily.hermitianScalarExtension V.toNormFamily hS hL hV).determinant := rfl

/-- The actual Hermitian extended determinant has rank one in every
original rank, including zero. -/
theorem hermitianScalarExtensionDeterminant_isLine (V : AdelicVectorBundle S E)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtensionDeterminant (L := L) hbase hS hL hV).IsLine :=
  NormFamily.determinant_finrank

/-- The actual Hermitian and ordinary extended determinant adelic lines
are equal through their proved norm-family identity. -/
theorem hermitianScalarExtensionDeterminant_eq_scalarExtensionDeterminant
    (V : AdelicVectorBundle S E)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    V.hermitianScalarExtensionDeterminant (L := L) hbase hS hL hV =
      V.scalarExtensionDeterminant (L := L) hbase hS := by
  apply AdelicVectorBundle.ext
  exact NormFamily.hermitianScalarExtension_determinant_eq_scalarExtension V.toNormFamily hS hL hV

/-- The actual Hermitian extended determinant-line degree equals the
original vector-bundle degree for every algebraic extension. -/
theorem lineDegree_hermitianScalarExtensionDeterminant [S.IsProper]
    (V : AdelicVectorBundle S E)
    (hbase : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtensionDeterminant (L := L) hbase hS hL hV).lineDegree
      (V.hermitianScalarExtensionDeterminant_isLine hbase hS hL hV) = V.degree hbase hS := by
  intro hp
  let := hp
  have hdegree :
      (V.hermitianScalarExtensionDeterminant (L := L) hbase hS hL hV).lineDegree
        (V.hermitianScalarExtensionDeterminant_isLine hbase hS hL hV) =
      (V.scalarExtensionDeterminant (L := L) hbase hS).lineDegree
        (V.scalarExtensionDeterminant_isLine hbase hS) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x s
    change S.ParameterSpaceExtension L at x
    change (NormFamily.hermitianScalarExtension V.toNormFamily hS hL hV).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s) =
      (V.toNormFamily.scalarExtension (L := L)).determinant.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] s)
    exact NormFamily.hermitianScalarExtension_determinant_norm_eq_scalarExtension
      V.toNormFamily hS hL hV x _
  exact hdegree.trans (V.lineDegree_scalarExtensionDeterminant (L := L) hbase hS)

/-- The actual Hermitian scalar extension is an adelic vector bundle under
original common countable density. Both measurability clauses and domination
are proved for the specified actual Hermitian norm. -/
def hermitianScalarExtension (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    AdelicVectorBundle (S.algebraicExtension L) (L ⊗[K] E) where
  toNormFamily := NormFamily.hermitianScalarExtension V.toNormFamily hS hL hV
  isMeasurable :=
    NormFamily.IsMeasurable.hermitianScalarExtension_of_common_countable_dense_subfield
      V.toNormFamily hS hV V.isMeasurable hcount
  dual_isMeasurable :=
    NormFamily.IsMeasurable.hermitianScalarExtension_dual_of_common_countable_dense_subfield
      V.toNormFamily hS hL hV V.isMeasurable hcount
  isDominated := NormFamily.IsDominated.hermitianScalarExtension
    V.toNormFamily hS hL hV V.isDominated

@[simp]
theorem hermitianScalarExtension_toNormFamily (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).toNormFamily =
      NormFamily.hermitianScalarExtension V.toNormFamily hS hL hV := rfl

/-- The produced Hermitian extended bundle is Hermitian for the specified
usual Archimedean norms on the extending completed fields. -/
theorem hermitianScalarExtension_isHermitian (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).IsHermitian hL :=
  NormFamily.hermitianScalarExtension_isHermitian V.toNormFamily hS hL hV

/-- Strong domination is produced for the actual extended Hermitian bundle. -/
theorem hermitianScalarExtension_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).IsStronglyAdelic :=
  NormFamily.IsDominated.hermitianScalarExtension_isStronglyDominated
    V.toNormFamily hS hL hV V.isDominated

/-- The actual finite Hermitian scalar-extended vector bundle has the
original vector degree. Target common countable density is proved from the
finite extension, while the determinant-line producer works algebraically. -/
theorem degree_hermitianScalarExtension_of_finiteDimensional [S.IsProper]
    [FiniteDimensional K L] (V : AdelicVectorBundle S E)
    (hcount : S.HasCommonCountableDenseSubfield)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
    (hV : V.toNormFamily.IsHermitian hS) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    (V.hermitianScalarExtension (L := L) hcount hS hL hV).degree
      (Or.inr (hcount.algebraicExtension_of_finiteDimensional (L := L))) hL =
        V.degree (Or.inr hcount) hS := by
  intro hp
  let := hp
  let hLS := hcount.algebraicExtension_of_finiteDimensional (L := L)
  let W := V.hermitianScalarExtension (L := L) hcount hS hL hV
  have hdegree : (W.determinantOfMeasurableBase (Or.inr hLS) hL).lineDegree
        (W.determinantOfMeasurableBase_isLine (Or.inr hLS) hL) =
      (V.hermitianScalarExtensionDeterminant (L := L) (Or.inr hcount) hS hL hV).lineDegree
        (V.hermitianScalarExtensionDeterminant_isLine (Or.inr hcount) hS hL hV) := by
    apply lineDegree_eq_of_norm_rational_eq _ _ _ _ (LinearEquiv.refl L _)
    intro x s
    rfl
  exact hdegree.trans
    (V.lineDegree_hermitianScalarExtensionDeterminant (L := L) (Or.inr hcount) hS hL hV)

end ArakelovGeometry.AdelicVectorBundle

end
