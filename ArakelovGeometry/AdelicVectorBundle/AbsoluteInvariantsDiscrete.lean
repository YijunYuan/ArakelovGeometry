/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.AbsoluteInvariants
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDiscreteNativeFiniteStageDegree

/-!
# Absolute invariants over a countable discrete original base

The suprema use every actual native algebraic-closure restriction and its
produced measurable determinant. Target discreteness and common density are
unnecessary. On the overlap, these are the existing absolute invariants.
-/

open MeasureTheory Filter
open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.AdelicVectorBundle
universe u v w wL
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Countable S.Ω] [DiscreteMeasurableSpace S.Ω]

/-- Degree of an actual native target restriction, with its determinant
measurability produced from the original countable discrete base. -/
def nativeRestrictionDegreeOfCountableDiscreteBase
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) : ℝ :=
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  (V.scalarExtensionRestrictionOfCountableDiscreteBase hN A).degreeOfMeasurableDeterminant
    (V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
      hN A) (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN)

/-- Absolute positive degree is the supremum of ALL actual native closure
restriction degrees, with no regularity premise on the closure place space. -/
def absolutePositiveDegreeOfCountableDiscreteBase (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  ⨆ A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E),
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN A : EReal)

/-- Absolute maximal slope uses the actual positive-rank closure subspaces.
The zero bundle retains the existing empty supremum convention. -/
def absoluteMaximalSlopeOfCountableDiscreteBase (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : EReal :=
  ⨆ A : {A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) A},
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN A.val /
      (Module.finrank (AlgebraicClosure K) A.val : ℝ) : EReal)

/-- On the common-density overlap, every native determinant degree is the
existing usual degree of the SAME actual closure subspace. -/
theorem nativeRestrictionDegreeOfCountableDiscreteBase_eq_degree
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) :
    let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
    V.nativeRestrictionDegreeOfCountableDiscreteBase hN A =
      ((V.scalarExtension hcount hN).restrictOfMeasurableBase A
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))).degree
        (Or.inr (hcount.algebraicExtension_of_isAlgClosed (L := L)))
        (AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN) := rfl

/-- The entire positive-degree supremum is coherent with the existing
absolute invariant, rather than merely bounded by it. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_eq_absolutePositiveDegree
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absolutePositiveDegreeOfCountableDiscreteBase hN =
      V.absolutePositiveDegree hcount hN := rfl

/-- The maximal-slope supremum has identical terms, ranks and index set
on the common-density overlap, including the rank-zero empty convention. -/
theorem absoluteMaximalSlopeOfCountableDiscreteBase_eq_absoluteMaximalSlope
    (V : AdelicVectorBundle S E) (hcount : S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalSlopeOfCountableDiscreteBase hN =
      V.absoluteMaximalSlope hcount hN := rfl

/-- The actual empty determinant generator has norm one in rank zero. -/
theorem nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule L (L ⊗[K] E)) (hr : Module.finrank L A = 0) :
    V.nativeRestrictionDegreeOfCountableDiscreteBase hN A = 0 := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let W := V.scalarExtensionRestrictionOfCountableDiscreteBase hN A
  let hdet := V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    hN A
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  change (W.determinant hdet hLN).lineDegree (W.determinant_isLine hdet hLN) = 0
  apply lineDegree_eq_zero_of_norm_eq_one _ _ ⟨_, determinant_empty_ne_zero hr⟩
  intro ω
  change W.toNormFamily.determinant.norm ω _ = 1
  simpa only [norm_one] using W.toNormFamily.determinant_norm_empty_tmul hr ω 1 (fun _ ↦ 0)

/-- Every actual native restriction contributes a term to the absolute
positive degree, with no finite-stage-only restriction on the index set. -/
theorem nativeRestrictionDegree_le_absolutePositiveDegreeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) :
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN A : EReal) ≤
      V.absolutePositiveDegreeOfCountableDiscreteBase hN :=
  le_iSup (fun B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) ↦
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN B : EReal)) A

/-- The actual zero subspace supplies nonnegativity in every rank. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_nonneg
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    0 ≤ V.absolutePositiveDegreeOfCountableDiscreteBase hN := by
  have h := V.nativeRestrictionDegree_le_absolutePositiveDegreeOfCountableDiscreteBase hN ⊥
  rw [V.nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero hN ⊥
    (finrank_bot _ _), EReal.coe_zero] at h
  exact h

/-- Every actual closure subspace is zero in rank zero, so the supremum
of its genuine determinant degrees is zero. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_eq_zero_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) :
    V.absolutePositiveDegreeOfCountableDiscreteBase hN = 0 := by
  apply le_antisymm _ (V.absolutePositiveDegreeOfCountableDiscreteBase_nonneg hN)
  apply iSup_le
  intro A
  have hA : Module.finrank (AlgebraicClosure K) A = 0 := by
    have h := A.finrank_le
    rw [Module.finrank_baseChange, hr] at h
    omega
  rw [V.nativeRestrictionDegreeOfCountableDiscreteBase_eq_zero hN A hA, EReal.coe_zero]

/-- No positive-rank actual closure subspace exists in rank zero. -/
theorem absoluteMaximalSlopeOfCountableDiscreteBase_eq_bot_of_finrank_eq_zero
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : Module.finrank K E = 0) :
    V.absoluteMaximalSlopeOfCountableDiscreteBase hN = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro A
  have h := A.val.finrank_le
  have hA := A.property
  rw [Module.finrank_baseChange, hr] at h
  omega

private theorem nativeDiscrete_degree_le_of_dual_basis_norm_bound
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (b : Module.Basis (Fin (Module.finrank L (L ⊗[K] E))) L (L ⊗[K] E))
    (H : (S.algebraicExtension L).Ω → ℝ)
    (hH : Integrable H (S.algebraicExtension L).v)
    (hb : ∀ᵐ ω ∂(S.algebraicExtension L).v,
      ∀ (A : Submodule L (L ⊗[K] E)) (i : Fin (Module.finrank L (L ⊗[K] E))),
        ((V.toNormFamily.scalarExtension (L := L)).restrict A).dual.norm ω
          ((1 : ((S.algebraicExtension L).ϕ ω).Completion) ⊗ₜ[L]
            A.subtype.dualMap (b.coord i)) ≤ Real.exp (H ω))
    (A : Submodule L (L ⊗[K] E)) :
    V.nativeRestrictionDegreeOfCountableDiscreteBase hN A ≤
      (Module.finrank L A : ℝ) * (∫ ω, H ω ∂(S.algebraicExtension L).v) +
        (Module.finrank L A : ℝ) / 2 * Real.log (Module.finrank L A) *
          ((S.algebraicExtension L).v (S.algebraicExtension L).Ωinf).toReal := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let W := V.scalarExtensionRestrictionOfCountableDiscreteBase hN A
  let hdet := V.toNormFamily.scalarExtension_restrict_determinant_isMeasurable_of_countable_discrete
    hN A
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  let t := determinantGenerator (K := L) (E := A)
  have ht : t ≠ 0 := determinantGenerator_ne_zero
  obtain ⟨s, hs⟩ := exists_restrictedCoordinateDualWedge_pairing_ne_zero b A t ht
  let α := determinantDualEquiv L A (restrictedCoordinateDualWedge b A s) t
  have hα : α ≠ 0 := hs
  let R := (S.algebraicExtension L).Ωinf.indicator (fun _ ↦
    (Module.finrank L A : ℝ) / 2 * Real.log (Module.finrank L A))
  have hR : Integrable R (S.algebraicExtension L).v :=
    (integrable_indicator_iff (S.algebraicExtension L).measurableSet_Ωinf).mpr
      (integrableOn_const ((S.algebraicExtension L).v_Ωinf_lt_top_of_isRCLike hLN).ne)
  have hf : Integrable (W.toNormFamily.determinant.logNorm t) (S.algebraicExtension L).v :=
    (W.determinant hdet hLN).integrable_logNorm t
  have hlocal : ∀ᵐ ω ∂(S.algebraicExtension L).v,
      Real.log ((S.algebraicExtension L).ϕ ω α) ≤
        W.toNormFamily.determinant.logNorm t ω + (Module.finrank L A : ℝ) * H ω + R ω := by
    filter_upwards [hb] with ω hω
    exact NormFamily.log_absValue_coordinate_le_logNorm_restrict_determinant
      (V.toNormFamily.scalarExtension (L := L)) b A s t ht hs hLN ω (H ω) (hω A)
  have hi := integral_mono_ae ((S.algebraicExtension L).integrable_log α hα)
    ((hf.add (hH.const_mul (Module.finrank L A : ℝ))).add hR) hlocal
  simp only [Pi.add_apply] at hi
  have hsum := integral_add (hf.add (hH.const_mul (Module.finrank L A : ℝ))) hR
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add hf (hH.const_mul (Module.finrank L A : ℝ)), integral_const_mul,
    AdelicStructure.IsProper.product_formula α hα] at hi
  change W.degreeOfMeasurableDeterminant hdet hLN ≤ _
  rw [W.degreeOfMeasurableDeterminant_eq_neg_integral hdet hLN ⟨t, ht⟩]
  dsimp only [R] at hi
  rw [integral_indicator_const _ (S.algebraicExtension L).measurableSet_Ωinf] at hi
  change 0 ≤ (∫ ω, W.toNormFamily.determinant.logNorm t ω ∂(S.algebraicExtension L).v) +
    (Module.finrank L A : ℝ) * (∫ ω, H ω ∂(S.algebraicExtension L).v) +
      ((S.algebraicExtension L).v (S.algebraicExtension L).Ωinf).toReal *
        ((Module.finrank L A : ℝ) / 2 * Real.log (Module.finrank L A)) at hi
  linarith

/-- Actual ambient domination and properness produce one real rank-degree
bound for ALL native restrictions, without target place-space regularity. -/
theorem exists_nativeRestrictionDegreeOfCountableDiscreteBase_le_rank_mul
    {L : Type wL} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L]
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ C : ℝ, ∀ A : Submodule L (L ⊗[K] E),
      V.nativeRestrictionDegreeOfCountableDiscreteBase hN A ≤ (Module.finrank L A : ℝ) * C := by
  let := AdelicStructure.Algebraic.isProper_algebraicExtension S L
  let W := V.scalarExtensionOfCountableDiscreteBase (L := L) hN
  let b := Module.finBasis L (L ⊗[K] E)
  let hLN := AdelicStructure.isRCLikeNormedField_algebraicExtension (L := L) hN
  obtain ⟨H, hH, _, hb⟩ :=
    NormFamily.IsDominated.exists_restricted_dual_basis_norm_bound W.toNormFamily b W.isDominated
  let C := (∫ ω, H ω ∂(S.algebraicExtension L).v) +
    (1 / 2 : ℝ) * Real.log (Module.finrank L (L ⊗[K] E)) *
      ((S.algebraicExtension L).v (S.algebraicExtension L).Ωinf).toReal
  refine ⟨C, fun A ↦ ?_⟩
  have hdeg := nativeDiscrete_degree_le_of_dual_basis_norm_bound V hN b H hH hb A
  by_cases hn : Module.finrank L A = 0
  · simpa only [hn, Nat.cast_zero, zero_mul, zero_div, add_zero] using hdeg
  · have hlog : Real.log (Module.finrank L A : ℝ) ≤
        Real.log (Module.finrank L (L ⊗[K] E)) :=
      Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
        (Nat.cast_le.mpr A.finrank_le)
    have hl := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (div_nonneg (Nat.cast_nonneg (Module.finrank L A))
        (by norm_num : (0 : ℝ) ≤ 2)))
      (ENNReal.toReal_nonneg :
        0 ≤ ((S.algebraicExtension L).v (S.algebraicExtension L).Ωinf).toReal)
    refine hdeg.trans ?_
    dsimp only [C]
    nlinarith

/-- Produced uniform rank-degree control excludes positive infinity. -/
theorem absolutePositiveDegreeOfCountableDiscreteBase_lt_top
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absolutePositiveDegreeOfCountableDiscreteBase hN < ⊤ := by
  obtain ⟨C, hC⟩ :=
    V.exists_nativeRestrictionDegreeOfCountableDiscreteBase_le_rank_mul
      (L := AlgebraicClosure K) hN
  have hb : V.absolutePositiveDegreeOfCountableDiscreteBase hN ≤
      ((Module.finrank K E : ℝ) * max C 0 : ℝ) := by
    apply iSup_le
    intro A
    apply EReal.coe_le_coe_iff.mpr
    have hr : Module.finrank (AlgebraicClosure K) A ≤ Module.finrank K E := by
      simpa only [Module.finrank_baseChange] using A.finrank_le
    exact (hC A).trans ((mul_le_mul_of_nonneg_left (le_max_left C 0)
      (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hr) (le_max_right C 0)))
  exact hb.trans_lt (EReal.coe_lt_top _)

/-- Every positive-rank native mean contributes its actual value to the
maximal-slope supremum. -/
theorem nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (A : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E))
    (hr : 0 < Module.finrank (AlgebraicClosure K) A) :
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN A /
      (Module.finrank (AlgebraicClosure K) A : ℝ) : EReal) ≤
      V.absoluteMaximalSlopeOfCountableDiscreteBase hN :=
  le_iSup (fun B : {B : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E) //
      0 < Module.finrank (AlgebraicClosure K) B} ↦
    (V.nativeRestrictionDegreeOfCountableDiscreteBase hN B.val /
      (Module.finrank (AlgebraicClosure K) B.val : ℝ) : EReal)) ⟨A, hr⟩

/-- All actual positive-rank closure means have a produced finite upper bound. -/
theorem absoluteMaximalSlopeOfCountableDiscreteBase_lt_top
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    V.absoluteMaximalSlopeOfCountableDiscreteBase hN < ⊤ := by
  obtain ⟨C, hC⟩ :=
    V.exists_nativeRestrictionDegreeOfCountableDiscreteBase_le_rank_mul
      (L := AlgebraicClosure K) hN
  have hb : V.absoluteMaximalSlopeOfCountableDiscreteBase hN ≤ (C : EReal) := by
    apply iSup_le
    intro A
    apply EReal.coe_le_coe_iff.mpr
    exact (div_le_iff₀ (Nat.cast_pos.mpr A.property)).mpr (by
      simpa only [mul_comm] using hC A.val)
  exact hb.trans_lt (EReal.coe_lt_top C)

/-- Both extended endpoints are excluded, including in rank zero. -/
theorem exists_absolutePositiveDegreeOfCountableDiscreteBase_eq_coe
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ∃ c : ℝ, V.absolutePositiveDegreeOfCountableDiscreteBase hN = (c : EReal) := by
  lift V.absolutePositiveDegreeOfCountableDiscreteBase hN to ℝ using
    ⟨(V.absolutePositiveDegreeOfCountableDiscreteBase_lt_top hN).ne,
      ((EReal.bot_lt_coe 0).trans_le
        (V.absolutePositiveDegreeOfCountableDiscreteBase_nonneg hN)).ne'⟩ with c
  exact ⟨c, rfl⟩

/-- Positive original rank makes the true closure maximal slope a finite real. -/
theorem exists_absoluteMaximalSlopeOfCountableDiscreteBase_eq_coe
    (V : AdelicVectorBundle S E)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hr : 0 < Module.finrank K E) :
    ∃ c : ℝ, V.absoluteMaximalSlopeOfCountableDiscreteBase hN = (c : EReal) := by
  have hA : 0 < Module.finrank (AlgebraicClosure K)
      (⊤ : Submodule (AlgebraicClosure K) ((AlgebraicClosure K) ⊗[K] E)) := by
    simpa only [finrank_top, Module.finrank_baseChange] using hr
  have hbot : ⊥ < V.absoluteMaximalSlopeOfCountableDiscreteBase hN :=
    (EReal.bot_lt_coe _).trans_le
      (V.nativeMean_le_absoluteMaximalSlopeOfCountableDiscreteBase hN ⊤ hA)
  lift V.absoluteMaximalSlopeOfCountableDiscreteBase hN to ℝ using
    ⟨(V.absoluteMaximalSlopeOfCountableDiscreteBase_lt_top hN).ne, hbot.ne'⟩ with c
  exact ⟨c, rfl⟩

end ArakelovGeometry.AdelicVectorBundle
