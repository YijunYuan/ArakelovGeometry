/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.ScalarExtension.Basic
import ArakelovGeometry.Analysis.Dual.UltrametricDual
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NormNum.GCD
/-!
# Injective scalar extension of actual subspace norms

Approximate ultrametric functional extension proves that genuine subspace
inclusions become isometries for the injective scalar-extension norm. Trivial
valuations and zero subspaces are retained.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
variable {k L V : Type*} [NormedField k] [NormedField L] [NormedAlgebra k L]
  [NormedAddCommGroup V] [NormedSpace k V]

/-- Canonical extended functional evaluation commutes with the genuine
base-changed subspace inclusion. -/
theorem scalarExtensionDualEval_subtype (W : Submodule k V)
    (f : W →ₗ[k] k) (g : V →ₗ[k] k) (hg : g.comp W.subtype = f) :
    (scalarExtensionDualEval (L := L) g).comp (W.subtype.baseChange L) =
      scalarExtensionDualEval f := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a w
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, scalarExtensionDualEval_tmul]
  rw [← LinearMap.congr_fun hg w]
  rfl

variable [CompleteSpace k] [FiniteDimensional k V] [IsUltrametricDist L]
  [IsUltrametricDist V]

/-- Injective scalar extension preserves the actual induced subspace norm
over every isometric non-Archimedean extension field. -/
theorem scalarExtensionInjectiveSeminorm_subtype (W : Submodule k V)
    (z : L ⊗[k] W) :
    scalarExtensionInjectiveSeminorm (W.subtype.baseChange L z) =
      scalarExtensionInjectiveSeminorm z := by
  apply le_antisymm
  · exact scalarExtensionInjectiveSeminorm_baseChange_le W.subtype (fun _ => le_rfl) z
  · apply (le_iff_forall_one_lt_le_mul₀
      (apply_nonneg scalarExtensionInjectiveSeminorm (W.subtype.baseChange L z))).mpr
    intro A hA
    apply (scalarExtensionInjectiveSeminorm_le_iff z _).mpr
    intro f
    by_cases hf : f = 0
    · simp only [hf, scalarExtensionDualEval_zero, LinearMap.zero_apply, norm_zero, zero_div]
      exact mul_nonneg (apply_nonneg _ _) (zero_lt_one.trans hA).le
    have hfn : 0 < linearMapOperatorSeminorm f := lt_of_le_of_ne'
      (apply_nonneg _ _) (fun h => hf ((linearMapOperatorSeminorm_eq_zero_iff f).mp h))
    apply (div_le_iff₀ hfn).mpr
    obtain ⟨g, hg, hgn⟩ := exists_ultrametric_extension_norm_le W f hA
    have he := LinearMap.congr_fun (scalarExtensionDualEval_subtype W f g hg) z
    calc
      ‖scalarExtensionDualEval f z‖ =
          ‖scalarExtensionDualEval g (W.subtype.baseChange L z)‖ := congrArg norm he.symm
      _ ≤ scalarExtensionInjectiveSeminorm (W.subtype.baseChange L z) *
          linearMapOperatorSeminorm g := norm_scalarExtensionDualEval_le_injective _ _
      _ ≤ scalarExtensionInjectiveSeminorm (W.subtype.baseChange L z) *
          (A * linearMapOperatorSeminorm f) :=
        mul_le_mul_of_nonneg_left hgn (apply_nonneg _ _)
      _ = _ := by ring
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace k U] [FiniteDimensional k U]

/-- Injective scalar extension preserves every genuine linear isometric
embedding into a finite-dimensional ultrametric space. -/
theorem scalarExtensionInjectiveSeminorm_baseChange_embedding
    (f : U →ₗᵢ[k] V) (z : L ⊗[k] U) :
    scalarExtensionInjectiveSeminorm (f.toLinearMap.baseChange L z) =
      scalarExtensionInjectiveSeminorm z := by
  let e := f.equivRange
  have he : f.toLinearMap = f.range.subtype.comp e.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [he, LinearMap.baseChange_comp, LinearMap.comp_apply,
    scalarExtensionInjectiveSeminorm_subtype]
  exact scalarExtensionInjectiveSeminorm_baseChange_isometry e z
end ArakelovGeometry
