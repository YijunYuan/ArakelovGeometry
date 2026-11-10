/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ArchimedeanDual
public import ArakelovGeometry.Analysis.UltrametricDual

/-!
# The minimal-extension formula for a restricted dual norm

The actual operator norm of a subspace functional is the infimum of the
operator norms of its extensions. At usual Archimedean places an extension
attains the infimum. For an ultrametric original norm, arbitrary losses
greater than one suffice, including over a trivially valued field.
-/

@[expose] public section

namespace ArakelovGeometry

variable {L V : Type*}

section Normed

variable [NormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]

/-- Restriction of a functional to an actual normed subspace contracts its
algebraic operator norm. -/
theorem linearMapOperatorSeminorm_comp_subtype_le (W : Submodule L V)
    (g : V →ₗ[L] L) :
    linearMapOperatorSeminorm (g.comp W.subtype) ≤ linearMapOperatorSeminorm g := by
  apply linearMapOperatorSeminorm_le _ (apply_nonneg _ g)
  intro w
  exact norm_linearMap_apply_le g (w : V)

private theorem extension_operatorNorms_bddBelow (W : Submodule L V) (f : W →ₗ[L] L) :
    BddBelow (linearMapOperatorSeminorm '' {g : V →ₗ[L] L | g.comp W.subtype = f}) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨g, _, rfl⟩
  exact apply_nonneg _ g

/-- Approximate ultrametric Hahn–Banach gives the exact infimum of all
extension norms, without assuming that this infimum is attained. -/
theorem linearMapOperatorSeminorm_eq_sInf_extensions_ultrametric [IsUltrametricDist V]
    (W : Submodule L V) (f : W →ₗ[L] L) :
    linearMapOperatorSeminorm f =
      sInf (linearMapOperatorSeminorm '' {g : V →ₗ[L] L | g.comp W.subtype = f}) := by
  obtain ⟨g, hg, _⟩ := exists_ultrametric_extension_norm_le W f (A := 2) (by norm_num)
  have hne : (linearMapOperatorSeminorm ''
      {g : V →ₗ[L] L | g.comp W.subtype = f}).Nonempty := ⟨_, g, hg, rfl⟩
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨g, hg, rfl⟩
    rw [← hg]
    exact linearMapOperatorSeminorm_comp_subtype_le W g
  · apply (le_iff_forall_one_lt_le_mul₀ (apply_nonneg _ f)).mpr
    intro A hA
    obtain ⟨g, hg, hgn⟩ := exists_ultrametric_extension_norm_le W f hA
    simpa only [mul_comm] using
      (csInf_le (extension_operatorNorms_bddBelow W f) ⟨g, hg, rfl⟩).trans hgn

end Normed

section Archimedean

variable [NontriviallyNormedField L] [CompleteSpace L] [IsRCLikeNormedField L]
  [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V]

/-- Exact Archimedean Hahn–Banach identifies the restricted dual norm with
the infimum over genuine full-space functional extensions. -/
theorem linearMapOperatorSeminorm_eq_sInf_extensions_archimedean
    (W : Submodule L V) (f : W →ₗ[L] L) :
    linearMapOperatorSeminorm f =
      sInf (linearMapOperatorSeminorm '' {g : V →ₗ[L] L | g.comp W.subtype = f}) := by
  obtain ⟨g, hg, hn⟩ := exists_archimedean_extension_norm_eq W f
  have hne : (linearMapOperatorSeminorm ''
      {g : V →ₗ[L] L | g.comp W.subtype = f}).Nonempty := ⟨_, g, hg, rfl⟩
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨g, hg, rfl⟩
    rw [← hg]
    exact linearMapOperatorSeminorm_comp_subtype_le W g
  · exact (csInf_le (extension_operatorNorms_bddBelow W f) ⟨g, hg, rfl⟩).trans hn.le

end Archimedean

end ArakelovGeometry
