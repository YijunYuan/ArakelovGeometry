/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianBasis

/-!
# Strong domination of subspaces and quotients

The source's strong-domination clauses in Proposition 4.1.19 follow by
comparison with an actual dominated Hermitian basis family. Completed
restriction and quotient distances contract, and their Hermitian reference
families are strongly dominated by the checked bidual isometry.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- Two strongly dominated families have integrably bounded distance, by
their actual comparison with one common mixed basis family. -/
theorem IsStronglyDominated.localDist {ξ η : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (hη : η.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) : HasIntegrableBounds (ξ.localDist η) S.v := by
  let b := Module.finBasis K E
  have h₁ := IsStronglyDominated.localDist_ofBasisMixed b ξ hξ hfin
  have h₂ := IsStronglyDominated.localDist_ofBasisMixed b η hη hfin
  refine ⟨(h₁.1.add h₂.1).mono ?_,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg η)⟩⟩
  apply Eventually.of_forall
  intro ω
  have ht := ξ.localDist_triangle (ofBasisMixed S E b) η ω
  rwa [(ofBasisMixed S E b).localDist_comm] at ht

/-- Strong domination survives restriction along any injective rational map.
The Hermitian reference family is constructed from an actual completed basis. -/
theorem IsStronglyDominated.pullback {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (f : F →ₗ[K] E) (hf : Function.Injective f)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.pullback f hf).IsStronglyDominated := by
  let b := Module.finBasis K E
  let η := ofBasisHermitian S E b
  have hηd : η.IsDominated := ofBasisHermitian_isDominated b hS
  have hηh : η.IsHermitian hS := ofBasisHermitian_isHermitian b hS
  have hηs : η.IsStronglyDominated :=
    ofBasisHermitian_isStronglyDominated_of_measure_lt_top b (S.v_Ωinf_lt_top_of_isRCLike hS)
  have hd := hηs.localDist hξ (S.v_Ωinf_lt_top_of_isRCLike hS)
  have hr : (η.pullback f hf).IsStronglyDominated :=
    ((η.pullback f hf).isStronglyDominated_iff_isDominated_of_ultrametric
      (hηh.pullback f hf).1 hS).mpr (hηd.pullback f hf)
  apply hr.of_localDist
  exact hd.1.mono (Eventually.of_forall fun ω => η.localDist_pullback_le ξ f hf ω)

/-- The strong-domination restriction clause of Proposition 4.1.19(1),
including the zero subspace. -/
theorem IsStronglyDominated.restrict {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (F : Submodule K E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.restrict F).IsStronglyDominated :=
  hξ.pullback F.subtype F.subtype_injective hS

/-- Strong domination survives the actual quotient norm along any surjective
rational map. Hermitian quotient preservation supplies the reference norm. -/
theorem IsStronglyDominated.pushforward {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.pushforward π hπ).IsStronglyDominated := by
  let b := Module.finBasis K E
  let η := ofBasisHermitian S E b
  have hηd : η.IsDominated := ofBasisHermitian_isDominated b hS
  have hηh : η.IsHermitian hS := ofBasisHermitian_isHermitian b hS
  have hηs : η.IsStronglyDominated :=
    ofBasisHermitian_isStronglyDominated_of_measure_lt_top b (S.v_Ωinf_lt_top_of_isRCLike hS)
  have hd := hηs.localDist hξ (S.v_Ωinf_lt_top_of_isRCLike hS)
  have hq : (η.pushforward π hπ).IsStronglyDominated :=
    ((η.pushforward π hπ).isStronglyDominated_iff_isDominated_of_ultrametric
      (hηh.pushforward π hπ).1 hS).mpr (hηd.pushforward π hπ)
  apply hq.of_localDist
  exact hd.1.mono (Eventually.of_forall fun ω => η.localDist_pushforward_le ξ π hπ ω)

/-- The strong-domination quotient clause of Proposition 4.1.19(2),
including quotient by the full subspace. -/
theorem IsStronglyDominated.quotient {ξ : NormFamily S E}
    (hξ : ξ.IsStronglyDominated) (F : Submodule K E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ξ.quotient F).IsStronglyDominated :=
  hξ.pushforward F.mkQ F.mkQ_surjective hS

end ArakelovGeometry.NormFamily
