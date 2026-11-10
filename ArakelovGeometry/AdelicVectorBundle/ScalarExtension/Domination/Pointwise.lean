/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import Mathlib.CategoryTheory.Category.Init

/-!
# Pointwise representatives for algebraic basis-distance envelopes

A finite sum of positive rational basis and dual-basis logarithmic norms
bounds every algebraic extension at every place. Modifying the integrable
base envelope on its single measurable null set gives a pointwise bound
which is integrable in the almost-everywhere sense.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E) {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K E)
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- A finite expression in the original rational basis and dual-basis norms
bounds local distance at every extending place, with no domination hypothesis. -/
theorem scalarExtension_localDist_ofBasisMixed_le_basisLogNorms
    (x : S.ParameterSpaceExtension L) :
    (ξ.scalarExtension (L := L)).localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤
        (∑ i, max 0 (ξ.logNorm (b i) x.base)) +
          (∑ i, max 0 (ξ.dual.logNorm (b.dualBasis i) x.base)) +
            S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x.base := by
  let A := ∑ i, max 0 (ξ.logNorm (b i) x.base)
  let B := ∑ i, max 0 (ξ.dual.logNorm (b.dualBasis i) x.base)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have ha : ∀ i, ξ.norm x.base
      ((b.baseChange (S.ϕ x.base).Completion) i) ≤ Real.exp A := by
    intro i
    rw [Module.Basis.baseChange_apply]
    apply (Real.log_le_iff_le_exp (ξ.norm_rational_pos x.base (b.ne_zero i))).mp
    exact (le_max_right _ _).trans (Finset.single_le_sum
      (fun j _ => le_max_left 0 (ξ.logNorm (b j) x.base)) (Finset.mem_univ i))
  have hb : ∀ i, ξ.dual.norm x.base
      ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp B := by
    intro i
    apply (Real.log_le_iff_le_exp
      (ξ.dual.norm_rational_pos x.base (b.dualBasis.ne_zero i))).mp
    exact (le_max_right _ _).trans (Finset.single_le_sum
      (fun j _ => le_max_left 0 (ξ.dual.logNorm (b.dualBasis j) x.base))
      (Finset.mem_univ i))
  exact ξ.scalarExtension_localDist_ofBasisMixed_le b x hA0 hB0 ha hb

omit [DecidableEq ι] in
/-- A dominated family admits one finite nonnegative integrable base function
bounding the basis distance at every place of every algebraic extension.
The representative is obtained by a proved modification on the single base
null set; strict measurability of the representative is not asserted. -/
theorem IsDominated.exists_scalarExtension_localDist_ofBasisMixed_pointwise_bound
    (hd : ξ.IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    ∃ H : S.Ω → ℝ, Integrable H S.v ∧ (∀ ω, 0 ≤ H ω) ∧
      ∀ (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
        (x : S.ParameterSpaceExtension L),
        (ξ.scalarExtension (L := L)).localDist
          (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤ H x.base := by
  classical
  obtain ⟨C, N, hC, hC0, _, hzero, hbound⟩ :=
    IsDominated.exists_scalarExtension_localDist_ofBasisMixed_bound ξ b hd hfin
  let D : S.Ω → ℝ := fun ω =>
    (∑ i, max 0 (ξ.logNorm (b i) ω)) +
      (∑ i, max 0 (ξ.dual.logNorm (b.dualBasis i) ω)) +
        S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) ω
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω =>
    add_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
      (Finset.sum_nonneg (fun _ _ => le_max_left _ _)))
      (Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _) ω)
  let H : S.Ω → ℝ := fun ω => if ω ∈ N then D ω else C ω
  have hnot : ∀ᵐ ω ∂S.v, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hzero
  have he : C =ᵐ[S.v] H := by
    filter_upwards [hnot] with ω hω
    simp only [H, ite_eq_right hω]
  refine ⟨H, hC.congr he, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · exact (show H ω = D ω from ite_eq_left hω).symm ▸ hD0 ω
    · exact (show H ω = C ω from ite_eq_right hω).symm ▸ hC0 ω
  · intro L _ _ _ x
    by_cases hx : x.base ∈ N
    · simp only [H, ite_eq_left hx]
      exact ξ.scalarExtension_localDist_ofBasisMixed_le_basisLogNorms b x
    · simp only [H, ite_eq_right hx]
      exact hbound L x hx

end ArakelovGeometry.NormFamily

end
