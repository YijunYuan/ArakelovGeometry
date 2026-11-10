/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamilyAlgebraicBasis

/-!
# Strong domination of arbitrary-choice algebraic coordinate maxima

Both actual transition matrices have uniform coefficient envelopes. Their
completed coordinate estimates control distance from a mixed rational basis.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE
variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L]
  {E : Type wE} [AddCommGroup E] [Module K E]
  {ι : Type*} [Finite ι] (f : Module.Basis ι K E)

/-- Rational basis coordinates commute with the actual injection into a
chosen extended completed fibre. -/
theorem chosenExtensionMap_coordinates (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.restriction K = S.ϕ ω)
    (z : (S.ϕ ω).Completion ⊗[K] E) (i : ι) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
    ((f.baseChange L).baseChange w.Completion).equivFun (chosenExtensionMap ω w hw z) i =
      algebraMap (S.ϕ ω).Completion w.Completion
        ((f.baseChange (S.ϕ ω).Completion).equivFun z i) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  let := AbsoluteValue.isScalarTower_completionOfEq (S.ϕ ω) w hw
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp only [map_add, Pi.add_apply, hz, ht]
  | tmul a x =>
    rw [chosenExtensionMap_tmul]
    simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, mul_one, map_mul]
    rw [← IsScalarTower.algebraMap_apply K (S.ϕ ω).Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K L w.Completion]

variable [Algebra.IsAlgebraic K L] [Fintype ι]

/-- The original rational coordinate maximum is preserved under the chosen
completion injection, on every completed vector. -/
theorem ofBasis_norm_chosenExtensionMap (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.restriction K = S.ϕ ω) (z : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasis (S.algebraicExtension L) (L ⊗[K] E) (f.baseChange L)).norm
      ⟨ω, w, hw⟩ (chosenExtensionMap ω w hw z) = (ofBasis S E f).norm ω z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  simp only [ofBasis_norm]
  have h (i : ι) :
      ‖((f.baseChange L).baseChange w.Completion).equivFun
        (chosenExtensionMap ω w hw z) i‖ =
      ‖(f.baseChange (S.ϕ ω).Completion).equivFun z i‖ := by
    erw [chosenExtensionMap_coordinates, norm_algebraMap']
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i =>
      (h i).trans_le (norm_le_pi_norm _ i)
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i =>
      (h i).symm.trans_le (norm_le_pi_norm _ i)

/-- The mixed rational reference norm is preserved by the actual injection. -/
theorem ofBasisMixed_norm_chosenExtensionMap (ω : S.Ω) (w : AbsoluteValue L ℝ)
    (hw : w.restriction K = S.ϕ ω) (z : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (f.baseChange L)).norm
      ⟨ω, w, hw⟩ (chosenExtensionMap ω w hw z) = (ofBasisMixed S E f).norm ω z := by
  classical
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ ω) w hw
  have hi : (⟨ω, w, hw⟩ : S.ParameterSpaceExtension L) ∈
      (S.algebraicExtension L).Ωinf ↔ ω ∈ S.Ωinf := by
    change ¬IsNonarchimedean w ↔ ¬IsNonarchimedean (S.ϕ ω)
    rw [← hw, AbsoluteValue.isNonarchimedean_restriction_iff]
  by_cases hω : ω ∈ S.Ωinf
  · erw [ofBasisMixed_norm_of_infinite (S := S.algebraicExtension L) (f.baseChange L) _ (hi.mpr hω),
      ofBasisMixed_norm_of_infinite (S := S) f _ hω]
    apply Finset.sum_congr rfl
    intro i _
    erw [chosenExtensionMap_coordinates, norm_algebraMap']
  · erw [ofBasisMixed_norm_of_finite (S := S.algebraicExtension L) (f.baseChange L) _
      (not_not.mp (hi.not.mpr hω)),
      ofBasisMixed_norm_of_finite (S := S) f _ (not_not.mp hω)]
    exact ofBasis_norm_chosenExtensionMap f ω w hw z

omit [Algebra.IsAlgebraic K L] [Finite ι] in
/-- Bounds on an actual transition matrix control one coordinate maximum
by the other mixed coordinate norm, on all completed vectors. -/
theorem ofBasis_norm_le_mul_of_transition_coefficients_le
    {κ : Type*} [Fintype κ] (T : AdelicStructure L)
    (b : Module.Basis κ L (L ⊗[K] E)) (c : Module.Basis ι L (L ⊗[K] E))
    (ω : T.Ω) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, T.ϕ ω (b.equivFun (c i) j) ≤ C)
    (z : (T.ϕ ω).Completion ⊗[L] (L ⊗[K] E)) :
    (ofBasis T (L ⊗[K] E) b).norm ω z ≤ C * (ofBasisMixed T (L ⊗[K] E) c).norm ω z := by
  apply norm_le_mul_of_basis_norm_le c (ofBasis T (L ⊗[K] E) b) ?_ ω hC ?_ z
  · intro t ht x y
    simpa only [ofBasisMixed_norm_of_finite b t ht] using
      ofBasisMixed_isUltrametric b t ht x y
  · intro i
    rw [Module.Basis.baseChange_apply, ofBasis_norm_rational]
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro j
    simpa only [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)] using h i j

omit [Algebra.IsAlgebraic K L] [Finite ι] in
/-- The maximum-to-mixed rank correction is supported on the infinite locus. -/
theorem ofBasisMixed_norm_le_exp_indicator_mul (T : AdelicStructure L)
    (b : Module.Basis ι L (L ⊗[K] E)) (ω : T.Ω)
    (z : (T.ϕ ω).Completion ⊗[L] (L ⊗[K] E)) :
    (ofBasisMixed T (L ⊗[K] E) b).norm ω z ≤
      Real.exp (T.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) ω) *
        (ofBasis T (L ⊗[K] E) b).norm ω z := by
  classical
  by_cases hω : ω ∈ T.Ωinf
  · rw [Set.indicator_of_mem hω]
    exact ofBasisMixed_norm_le_exp_log_card_mul b ω z
  · rw [Set.indicator_of_notMem hω, Real.exp_zero, one_mul,
      ofBasisMixed_norm_of_finite b ω (not_not.mp hω)]

variable [FiniteDimensional K E]

/-- The two actual algebraic transition matrices give an integrable
local-distance envelope for every arbitrary choice of extending places. -/
theorem ofChosenAlgebraicBasis_localDist_hasIntegrableBounds
    {κ : Type*} [Fintype κ] (b : Module.Basis κ L (L ⊗[K] E))
    (w : S.Ω → AbsoluteValue L ℝ) (hw : ∀ ω, (w ω).restriction K = S.ϕ ω)
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds ((ofChosenAlgebraicBasis b w hw).localDist (ofBasisMixed S E f)) S.v := by
  classical
  let c := f.baseChange L
  obtain ⟨A, hA, hA0, ha⟩ := S.exists_algebraic_coefficients_exp_bound
    (fun ij : ι × κ => b.equivFun (c ij.1) ij.2)
  obtain ⟨B, hB, hB0, hb⟩ := S.exists_algebraic_coefficients_exp_bound
    (fun ij : κ × ι => c.equivFun (b ij.1) ij.2)
  let R : S.Ω → ℝ := S.Ωinf.indicator
    (fun _ => Real.log (Fintype.card ι : ℝ) + Real.log (Fintype.card κ : ℝ))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  have hR0 (ω : S.Ω) : 0 ≤ R ω := Set.indicator_nonneg
    (fun _ _ => add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)) ω
  let H : S.Ω → ℝ := A + B + R
  have hH0 (ω : S.Ω) : 0 ≤ H ω := add_nonneg (add_nonneg (hA0 ω) (hB0 ω)) (hR0 ω)
  refine ⟨⟨H, (hA.add hB).add hR, Filter.Eventually.of_forall ?_⟩,
    ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall
      (fun ω => (ofChosenAlgebraicBasis b w hw).localDist_nonneg _ ω)⟩⟩
  intro ω
  apply ((ofChosenAlgebraicBasis b w hw).localDist_le_iff_norm_le (ofBasisMixed S E f)
    ω (hH0 ω)).mpr
  intro z
  let T := S.algebraicExtension L
  let x : T.Ω := ⟨ω, w ω, hw ω⟩
  let y := chosenExtensionMap ω (w ω) (hw ω) z
  have hi : x ∈ T.Ωinf ↔ ω ∈ S.Ωinf := by
    change ¬IsNonarchimedean (w ω) ↔ ¬IsNonarchimedean (S.ϕ ω)
    rw [← hw ω, AbsoluteValue.isNonarchimedean_restriction_iff]
  have hq : (ofBasisMixed T (L ⊗[K] E) c).norm x y = (ofBasisMixed S E f).norm ω z :=
    ofBasisMixed_norm_chosenExtensionMap f ω (w ω) (hw ω) z
  have hp : (ofBasis T (L ⊗[K] E) b).norm x y =
      (ofChosenAlgebraicBasis b w hw).norm ω z := rfl
  have hforward := ofBasis_norm_le_mul_of_transition_coefficients_le T b c x
    (Real.exp_pos (A ω)).le (fun i j => ha ω (w ω) (hw ω) (i, j)) y
  rw [hq, hp] at hforward
  have hback := ofBasis_norm_le_mul_of_transition_coefficients_le T c b x
    (Real.exp_pos (B ω)).le (fun i j => hb ω (w ω) (hw ω) (i, j)) y
  have hrc := ofBasisMixed_norm_le_exp_indicator_mul T c x y
  have hrb := ofBasisMixed_norm_le_exp_indicator_mul T b x y
  have hrank : (T.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x) +
      (T.Ωinf.indicator (fun _ => Real.log (Fintype.card κ : ℝ)) x) = R ω := by
    by_cases hω : ω ∈ S.Ωinf
    · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hi.mpr hω), R]
    · simp only [Set.indicator_of_notMem hω,
        Set.indicator_of_notMem (hi.not.mpr hω), R, add_zero]
  have hreverse : (ofBasisMixed S E f).norm ω z ≤
      Real.exp (B ω + R ω) * (ofChosenAlgebraicBasis b w hw).norm ω z := by
    rw [← hq]
    calc
      _ ≤ Real.exp (T.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x) *
          (Real.exp (B ω) *
            (Real.exp (T.Ωinf.indicator (fun _ => Real.log (Fintype.card κ : ℝ)) x) *
              (ofBasis T (L ⊗[K] E) b).norm x y)) :=
        hrc.trans (mul_le_mul_of_nonneg_left
          (hback.trans (mul_le_mul_of_nonneg_left hrb (Real.exp_pos _).le)) (Real.exp_pos _).le)
      _ = _ := by rw [hp, Real.exp_add, ← hrank, Real.exp_add]; ring
  constructor
  · exact hforward.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by dsimp [H]; linarith [hB0 ω, hR0 ω]))
      ((ofBasisMixed S E f).norm_nonneg ω z))
  · exact hreverse.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by dsimp [H]; linarith [hA0 ω]))
      ((ofChosenAlgebraicBasis b w hw).norm_nonneg ω z))

/-- Proposition 4.1.15: the literal restricted coordinate maxima from any
algebraic basis and arbitrary extending-place choices are strongly dominated. -/
theorem ofChosenAlgebraicBasis_isStronglyDominated
    {κ : Type*} [Fintype κ] (b : Module.Basis κ L (L ⊗[K] E))
    (w : S.Ω → AbsoluteValue L ℝ) (hw : ∀ ω, (w ω).restriction K = S.ϕ ω)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofChosenAlgebraicBasis b w hw).IsStronglyDominated := by
  let f := Module.finBasis K E
  exact (isStronglyDominated_iff_localDist_ofBasisMixed f _ hS).mpr
    (ofChosenAlgebraicBasis_localDist_hasIntegrableBounds f b w hw
      (S.v_Ωinf_lt_top_of_isRCLike hS))

end ArakelovGeometry.NormFamily
