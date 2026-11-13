/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Basis
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
import ArakelovGeometry.AdelicVectorBundle.NormFamily.BasisComparison
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Domination under algebraic scalar extension

Extended rational functional evaluations are controlled by their original
completed dual norms. These bounds are the local input for a base-curve
envelope uniform over algebraic extensions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

namespace Module.Basis

/-- Dual basis formation commutes with algebraic base change. -/
theorem dualBasis_baseChange {K L E ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup E] [Module K E] [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι K E) (i : ι) :
    (b.baseChange L).dualBasis i = Module.Dual.baseChange L (b.dualBasis i) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a e
  simp [Module.Dual.baseChange, Algebra.smul_def, mul_comm]

end Module.Basis

namespace ArakelovGeometry.NormFamily

universe u w wE

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- The injective extension is bounded by the source mixed extension at
every actual extending place. -/
theorem injectiveScalarExtension_norm_le_scalarExtension_norm
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.injectiveScalarExtension (L := L)).norm x z ≤
      (ξ.scalarExtension (L := L)).norm x z := by
  by_cases hx : x.base ∈ S.Ωfin
  · exact (ξ.scalarExtension_norm_of_mem_Ωfin x hx z).symm.le
  · exact (ξ.injectiveScalarExtension_norm_le_projectiveScalarExtension_norm x z).trans_eq
      (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx z).symm

omit [Algebra.IsAlgebraic K L] in
/-- Extension of a rational functional commutes with the canonical
completed-fibre identification on every completed vector. -/
theorem completedScalarExtensionEquiv_baseChange_dual_apply
    (x : S.ParameterSpaceExtension L) (f : Module.Dual K E)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    Module.Dual.baseChange x.abv.Completion
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E
        ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f))
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) =
      dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
        ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L f) z := by
  intro aVW
  let := aVW
  have h := completedScalarExtensionEquiv_dual_apply (S.ϕ x.base) x.abv x.restrict_eq
    ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] f)) z
  simpa only [completedScalarExtensionEquiv_tmul, map_one, one_mul,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe, dualBaseChangeEquiv_tmul,
    one_smul] using h

/-- Every extended rational functional is bounded by its original
completed dual norm times the mixed scalar-extension norm. -/
theorem norm_scalarExtension_rational_dual_apply_le
    (x : S.ParameterSpaceExtension L) (f : Module.Dual K E)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
      ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L f) z‖ ≤
      ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f) *
        (ξ.scalarExtension (L := L)).norm x z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let F := dualBaseChangeEquiv K (S.ϕ x.base).Completion E
    ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f)
  have he : scalarExtensionDualEval (L := x.abv.Completion) F =
      Module.Dual.baseChange x.abv.Completion F := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    simp [scalarExtensionDualEval, Algebra.smul_def, mul_comm]
  have hb := norm_scalarExtensionDualEval_le_injective F
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z)
  rw [he, completedScalarExtensionEquiv_baseChange_dual_apply] at hb
  change _ ≤ (ξ.injectiveScalarExtension (L := L)).norm x z *
    ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f) at hb
  have hb' : ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
      ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L f) z‖ ≤
      ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f) *
        (ξ.injectiveScalarExtension (L := L)).norm x z := by
    simpa only [mul_comm] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (ξ.injectiveScalarExtension_norm_le_scalarExtension_norm x z)
    (ξ.dual.norm_nonneg _ _))

variable {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι K E)

/-- Every completed coordinate of an extended vector is controlled by the
original rational dual-basis norm. -/
theorem norm_scalarExtension_coordinate_le (x : S.ParameterSpaceExtension L)
    (i : ι) (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    ‖((b.baseChange L).baseChange x.abv.Completion).equivFun z i‖ ≤
      ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) *
        (ξ.scalarExtension (L := L)).norm x z := by
  have he := dualBaseChange_one_dualBasis_apply
    (S := S.algebraicExtension L) (b.baseChange L) x i z
  change dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
    ((1 : x.abv.Completion) ⊗ₜ[L] (b.baseChange L).dualBasis i) z =
    ((b.baseChange L).baseChange x.abv.Completion).equivFun z i at he
  rw [← he, Module.Basis.dualBasis_baseChange]
  exact ξ.norm_scalarExtension_rational_dual_apply_le x (b.dualBasis i) z

variable [Fintype ι]

/-- A common bound on the original dual-basis norms controls the maximum
coordinate norm on every actual completed extended fibre. -/
theorem ofBasis_norm_le_mul_scalarExtension_of_dual_basis_norm_le
    (x : S.ParameterSpaceExtension L) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.dual.norm x.base
      ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ C)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ofBasis (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z ≤
      C * (ξ.scalarExtension (L := L)).norm x z := by
  change ‖((b.baseChange L).baseChange x.abv.Completion).equivFun z‖ ≤
    C * (ξ.scalarExtension (L := L)).norm x z
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg hC ((ξ.scalarExtension (L := L)).norm_nonneg x z))).mpr
  intro i
  exact (ξ.norm_scalarExtension_coordinate_le b x i z).trans
    (mul_le_mul_of_nonneg_right (hb i) ((ξ.scalarExtension (L := L)).norm_nonneg x z))

/-- Original dual-basis bounds control the mixed extended coordinate norm,
with the rank factor supported on the base infinite locus. -/
theorem ofBasisMixed_norm_le_mul_scalarExtension_of_dual_basis_norm_le
    (x : S.ParameterSpaceExtension L) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.dual.norm x.base
      ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ C)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z ≤
      Real.exp (S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x.base) *
        C * (ξ.scalarExtension (L := L)).norm x z := by
  classical
  by_cases hx : x.base ∈ S.Ωinf
  · rw [Set.indicator_of_mem hx, mul_assoc]
    exact (ofBasisMixed_norm_le_exp_log_card_mul (S := S.algebraicExtension L)
      (b.baseChange L) x z).trans
      (mul_le_mul_of_nonneg_left
        (ξ.ofBasis_norm_le_mul_scalarExtension_of_dual_basis_norm_le b x hC hb z)
        (Real.exp_pos _).le)
  · have hf : x ∈ (S.algebraicExtension L).Ωfin :=
      (AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr (not_not.mp hx)
    have he := ofBasisMixed_norm_of_finite (S := S.algebraicExtension L)
      (b.baseChange L) x hf z
    rw [he, Set.indicator_of_notMem hx, Real.exp_zero, one_mul]
    exact ξ.ofBasis_norm_le_mul_scalarExtension_of_dual_basis_norm_le b x hC hb z

omit [Finite ι] [DecidableEq ι] in
/-- Original primal-basis bounds control the actual mixed scalar extension
by the mixed norm of the extended rational basis. -/
theorem scalarExtension_norm_le_mul_of_basis_norm_le
    (x : S.ParameterSpaceExtension L) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.norm x.base ((b.baseChange (S.ϕ x.base).Completion) i) ≤ C)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).norm x z ≤
      C * (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z := by
  classical
  apply norm_le_mul_of_basis_norm_le (b.baseChange L) (ξ.scalarExtension (L := L))
    (hξ := ξ.scalarExtension_isUltrametric) x hC _ z
  intro i
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
  exact (ξ.scalarExtension_norm_one_tmul_le x (b i)).trans
    (by simpa only [Module.Basis.baseChange_apply] using hb i)

/-- Two base rational-basis bounds give a pointwise local-distance bound
simultaneously on the full completed fibre over every extending place. -/
theorem scalarExtension_localDist_ofBasisMixed_le
    (x : S.ParameterSpaceExtension L) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, ξ.norm x.base ((b.baseChange (S.ϕ x.base).Completion) i) ≤ Real.exp A)
    (hb : ∀ i, ξ.dual.norm x.base
      ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp B) :
    (ξ.scalarExtension (L := L)).localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤
        A + B + S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x.base := by
  let R := S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ))
  have hR : 0 ≤ R x.base :=
    Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _) _
  apply ((ξ.scalarExtension (L := L)).localDist_le_iff_norm_le
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x
    (add_nonneg (add_nonneg hA hB) hR)).mpr
  intro z
  constructor
  · exact (ξ.scalarExtension_norm_le_mul_of_basis_norm_le b x (Real.exp_pos _).le ha z).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        ((ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E)
          (b.baseChange L)).norm_nonneg x z))
  · calc
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z ≤
          Real.exp (R x.base) * Real.exp B * (ξ.scalarExtension (L := L)).norm x z :=
        ξ.ofBasisMixed_norm_le_mul_scalarExtension_of_dual_basis_norm_le b x
          (Real.exp_pos _).le hb z
      _ = Real.exp (B + R x.base) * (ξ.scalarExtension (L := L)).norm x z := by
        rw [← Real.exp_add, add_comm (R x.base)]
      _ ≤ Real.exp (A + B + R x.base) * (ξ.scalarExtension (L := L)).norm x z :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
          ((ξ.scalarExtension (L := L)).norm_nonneg x z)

omit [Finite ι] [DecidableEq ι] in
/-- Domination supplies one integrable base-curve envelope and one measurable
base null set that bound the distance to the extended mixed basis family
uniformly over all algebraic extensions. The empty basis is included. -/
theorem IsDominated.exists_scalarExtension_localDist_ofBasisMixed_bound
    (hd : ξ.IsDominated) (hfin : S.v S.Ωinf < ⊤) :
    ∃ C : S.Ω → ℝ, ∃ N : Set S.Ω,
      Integrable C S.v ∧ (∀ ω, 0 ≤ C ω) ∧ MeasurableSet N ∧ S.v N = 0 ∧
        ∀ (L : Type w) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
          (x : S.ParameterSpaceExtension L), x.base ∉ N →
          (ξ.scalarExtension (L := L)).localDist
            (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤
              C x.base := by
  classical
  obtain ⟨A, hA, hA0, ha⟩ := IsUpperDominated.exists_basis_norm_bound (ξ := ξ) b hd.1
  obtain ⟨B, hB, hB0, hb⟩ :=
    IsUpperDominated.exists_basis_norm_bound (ξ := ξ.dual) b.dualBasis hd.2
  have hb' : ∀ᵐ ω ∂S.v, ∀ i,
      ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp (B ω) := by
    simpa only [Module.Basis.baseChange_apply] using hb
  obtain ⟨N, hsub, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp (ha.and hb'))
  let R := S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  have hR0 : ∀ ω, 0 ≤ R ω := Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _)
  refine ⟨fun ω => A ω + B ω + R ω, N, (hA.add hB).add hR,
    fun ω => add_nonneg (add_nonneg (hA0 ω) (hB0 ω)) (hR0 ω), hN, hzero, ?_⟩
  intro L _ _ _ x hx
  have hgood : (∀ i, ξ.norm x.base
      ((b.baseChange (S.ϕ x.base).Completion) i) ≤ Real.exp (A x.base)) ∧
      ∀ i, ξ.dual.norm x.base
        ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp (B x.base) := by
    by_contra h
    exact hx (hsub h)
  exact ξ.scalarExtension_localDist_ofBasisMixed_le b x (hA0 x.base) (hB0 x.base)
    hgood.1 hgood.2

/-- Algebraic extension preserves the measure of the infinite locus. -/
theorem scalarExtension_measure_Ωinf :
    (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf = S.v S.Ωinf := by
  have hproj : MeasurePreserving (fun x : (S.algebraicExtension L).Ω => x.base)
      (S.algebraicExtension L).v S.v :=
    ⟨AdelicStructure.Algebraic.measurable_proj_projective S L,
      AdelicStructure.Algebraic.map_measure_proj S L⟩
  have he : (S.algebraicExtension L).Ωinf =
      (fun x : (S.algebraicExtension L).Ω => x.base) ⁻¹' S.Ωinf := by
    ext x
    exact not_congr (AdelicStructure.mem_Ωfin_algebraicExtension_iff x)
  rw [he]
  exact hproj.measure_preimage S.measurableSet_Ωinf.nullMeasurableSet

omit [Finite ι] [DecidableEq ι] in
/-- Pullback of the single base envelope bounds the distance of every
algebraic scalar extension from its extended mixed rational-basis family. -/
theorem IsDominated.scalarExtension_localDist_ofBasisMixed (hd : ξ.IsDominated)
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds ((ξ.scalarExtension (L := L)).localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)))
        (S.algebraicExtension L).v := by
  obtain ⟨C, N, hC, _, _, hzero, hb⟩ :=
    IsDominated.exists_scalarExtension_localDist_ofBasisMixed_bound ξ b hd hfin
  have hproj : MeasurePreserving (fun x : (S.algebraicExtension L).Ω => x.base)
      (S.algebraicExtension L).v S.v :=
    ⟨AdelicStructure.Algebraic.measurable_proj_projective S L,
      AdelicStructure.Algebraic.map_measure_proj S L⟩
  have hnot : ∀ᵐ ω ∂S.v, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hzero
  have hi : Integrable (fun x : (S.algebraicExtension L).Ω => C x.base)
      (S.algebraicExtension L).v :=
    AdelicStructure.Algebraic.integrable_comp_proj_measure S L hC
  refine ⟨⟨_, hi, ?_⟩,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall
      ((ξ.scalarExtension (L := L)).localDist_nonneg _)⟩⟩
  filter_upwards [hproj.quasiMeasurePreserving.ae hnot] with x hx
  exact hb L x hx

/-- The forward implication of Corollary 4.1.13: every algebraic scalar
extension of a dominated family is strongly dominated. Finite measure of
the base infinite locus suffices, without an assumption on the original
family's ultrametricity. -/
theorem IsDominated.scalarExtension_isStronglyDominated (hd : ξ.IsDominated)
    (hfin : S.v S.Ωinf < ⊤) : (ξ.scalarExtension (L := L)).IsStronglyDominated := by
  let b := Module.finBasis K E
  have hfinL : (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf < ⊤ := by
    rw [scalarExtension_measure_Ωinf]
    exact hfin
  exact (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    (b.baseChange L) (ξ.scalarExtension (L := L)) hfinL).mpr
      (IsDominated.scalarExtension_localDist_ofBasisMixed ξ b hd hfin)

end ArakelovGeometry.NormFamily

end
