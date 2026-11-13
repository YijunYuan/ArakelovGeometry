/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import Mathlib.Analysis.Normed.Lp.PiLp

import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.Analysis.NormedSpace.CoordinateNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The mixed coordinate norm family

Chen–Moriwaki, Example 4.1.5 (PDF pages 226–227), uses the coordinate
maximum at finite places and the coordinate sum at infinite places.  Both
norms here are transported through the actual completed basis.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] (S : AdelicStructure K)

/-- The usual real or complex norm on the actual completion forces the
Archimedean exponent to be one. -/
theorem κ_eq_one_of_isRCLike (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (hL : IsRCLikeNormedField (S.ϕ ω).Completion) : S.κ ω = 1 := by
  let := hL
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  have htwo : (S.ϕ ω) (2 : K) = 2 := by
    rw [← S.norm_algebraMap_eq_absValue ω 2, map_ofNat]
    norm_num
  have hk : (2 : ℝ) = (2 : ℝ) ^ S.κ ω := by
    simpa [Rat.AbsoluteValue.real_eq_abs, htwo] using S.κ_def hω 2
  have he := congrArg Real.log hk
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at he
  nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-- With usual Archimedean norms, the infinite locus has finite measure.
This uses the accepted integrability theorem for the exponent `κ`. -/
theorem v_Ωinf_lt_top_of_isRCLike
    [hS : S.IsArchimedeanNormalized] : S.v S.Ωinf < ⊤ := by
  apply S.v_Ωinf_lt_top_of_κ_bddBelow
  refine ⟨1, zero_lt_one, ?_⟩
  rintro t ⟨ω, hω, rfl⟩
  rw [S.κ_eq_one_of_isRCLike ω hω (hS ω hω)]

/-- The actual completed-field norm is ultrametric at every finite place. -/
theorem norm_add_le_max_of_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (a b : (S.ϕ ω).Completion) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  refine UniformSpace.Completion.induction_on₂ a b ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro x y
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe]
      using (show ‖x + y‖ ≤ max ‖x‖ ‖y‖ from hω x.ofAbs y.ofAbs)

/-- Finitely many rational coefficients have a common integrable logarithmic
bound, including zero coefficients. -/
theorem integrable_sum_abs_log {ι : Type*} [Fintype ι] (c : ι → K) :
    Integrable (fun ω => ∑ i, |Real.log ((S.ϕ ω) (c i))|) S.v := by
  apply integrable_finsetSum
  intro i _
  by_cases hi : c i = 0
  · simp only [hi, map_zero, Real.log_zero, abs_zero]
    exact integrable_zero _ _ _
  · exact (S.integrable_log (c i) hi).abs

/-- The logarithmic bound controls each coefficient at every place. -/
theorem absValue_le_exp_sum_abs_log {ι : Type*} [Fintype ι] (c : ι → K)
    (ω : S.Ω) (i : ι) :
    (S.ϕ ω) (c i) ≤ Real.exp (∑ j, |Real.log ((S.ϕ ω) (c j))|) := by
  by_cases hi : c i = 0
  · simpa only [hi, map_zero] using (Real.exp_pos _).le
  · apply (Real.log_le_iff_le_exp ((S.ϕ ω).pos hi)).mp
    exact (le_abs_self _).trans (Finset.single_le_sum
      (f := fun j => |Real.log ((S.ϕ ω) (c j))|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

universe u w

variable {K : Type u} [Field K] (S : AdelicStructure K)
  (E : Type w) [AddCommGroup E] [Module K E]

/-- The coordinate sum norm, transported through the completed basis. -/
def ofBasisSum {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) : NormFamily S E where
  norm ω := (normSeminorm (S.ϕ ω).Completion (PiLp 1 (fun _ : ι => (S.ϕ ω).Completion))).comp
    (((b.baseChange (S.ϕ ω).Completion).equivFun.trans
      (WithLp.linearEquiv 1 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm).toLinearMap)
  norm_eq_zero_iff ω x := by
    change ‖(WithLp.linearEquiv 1 (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).symm
      ((b.baseChange (S.ϕ ω).Completion).equivFun x)‖ = 0 ↔ x = 0
    rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- The mixed coordinate family of Example 4.1.5. -/
def ofBasisMixed {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) : NormFamily S E := by
  classical
  exact
    { norm := fun ω => if ω ∈ S.Ωinf then (ofBasisSum S E b).norm ω
        else (ofBasis S E b).norm ω
      norm_eq_zero_iff := fun ω x => by
        split_ifs <;> exact norm_eq_zero_iff _ ω x }

variable {S E} {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)

/-- The coordinate sum formula holds also for the empty basis. -/
theorem ofBasisSum_norm (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisSum S E b).norm ω x =
      ∑ i, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖ :=
  PiLp.norm_eq_of_L1 _

/-- At finite places the mixed family is the existing coordinate supremum family. -/
theorem ofBasisMixed_norm_of_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed S E b).norm ω x = (ofBasis S E b).norm ω x := by
  have hn : ω ∉ S.Ωinf := fun h => h hω
  simp only [ofBasisMixed, ite_eq_right hn]

/-- At infinite places the mixed family is the coordinate sum norm. -/
theorem ofBasisMixed_norm_of_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed S E b).norm ω x =
      ∑ i, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖ := by
  simp only [ofBasisMixed, ite_eq_left hω, ofBasisSum_norm]

/-- Every completed basis vector has norm one for the sum norm. -/
@[simp]
theorem ofBasisSum_norm_basis (ω : S.Ω) (i : ι) :
    (ofBasisSum S E b).norm ω ((b.baseChange (S.ϕ ω).Completion) i) = 1 := by
  classical
  rw [ofBasisSum_norm]
  simp only [Module.Basis.equivFun_self]
  simp [apply_ite]

/-- Both branches normalize scalar multiples of basis vectors in the same way. -/
@[simp]
theorem ofBasisMixed_norm_tmul_basis (ω : S.Ω) (a : (S.ϕ ω).Completion) (i : ι) :
    (ofBasisMixed S E b).norm ω (a ⊗ₜ[K] b i) = ‖a‖ := by
  by_cases hω : ω ∈ S.Ωinf
  · have ht : a ⊗ₜ[K] b i = a • (b.baseChange (S.ϕ ω).Completion) i := by
      simp [Module.Basis.baseChange_apply, TensorProduct.smul_tmul']
    simp only [ofBasisMixed, ite_eq_left hω, ht, norm_smul, ofBasisSum_norm_basis, mul_one]
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    rw [ofBasisMixed_norm_of_finite b ω hf, ofBasis_norm_tmul_basis]

/-- In rank zero the mixed family is the unique zero family. -/
theorem ofBasisMixed_norm_eq_zero_of_subsingleton [Subsingleton E] (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) : (ofBasisMixed S E b).norm ω x = 0 :=
  norm_eq_zero_of_subsingleton _ _ _

/-- Completed coordinates of a rational vector are the images of its rational
coordinates under the actual completed-field algebra map. -/
theorem basis_equivFun_one_tmul {ι' : Type*} [Finite ι'] (b : Module.Basis ι' K E)
    (ω : S.Ω) (x : E) (i : ι') :
    (b.baseChange (S.ϕ ω).Completion).equivFun
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) i =
      algebraMap K (S.ϕ ω).Completion (b.equivFun x i) := by
  simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]

/-- The rational evaluation of the coordinate sum norm. -/
theorem ofBasisSum_norm_rational (ω : S.Ω) (x : E) :
    (ofBasisSum S E b).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      ∑ i, (S.ϕ ω) (b.equivFun x i) := by
  simp only [ofBasisSum_norm, basis_equivFun_one_tmul, S.norm_algebraMap_eq_absValue]

/-- The rational evaluation of the coordinate supremum norm, expressed in a
fixed real coordinate space so that measurability is directly visible. -/
theorem ofBasis_norm_rational (ω : S.Ω) (x : E) :
    (ofBasis S E b).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      ‖fun i => (S.ϕ ω) (b.equivFun x i)‖ := by
  rw [ofBasis_norm]
  have hn (i : ι) :
      ‖(b.baseChange (S.ϕ ω).Completion).equivFun
          ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) i‖ =
        ‖(S.ϕ ω) (b.equivFun x i)‖ := by
    rw [basis_equivFun_one_tmul, S.norm_algebraMap_eq_absValue,
      Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i =>
      (hn i).trans_le (norm_le_pi_norm (fun i => (S.ϕ ω) (b.equivFun x i)) i)
  · exact (pi_norm_le_iff_of_nonneg (_root_.norm_nonneg _)).mpr fun i =>
      (hn i).symm.trans_le (norm_le_pi_norm
        ((b.baseChange (S.ϕ ω).Completion).equivFun ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)) i)

open Classical in
/-- Both branches of the mixed rational norm are explicit functions of the
absolute values of finitely many rational coordinates. -/
theorem ofBasisMixed_norm_rational (ω : S.Ω) (x : E) :
    (ofBasisMixed S E b).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) =
      if ω ∈ S.Ωinf then ∑ i, (S.ϕ ω) (b.equivFun x i)
      else ‖fun i => (S.ϕ ω) (b.equivFun x i)‖ := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · simp only [ofBasisMixed, ite_eq_left hω, ofBasisSum_norm_rational]
  · simp only [ofBasisMixed, ite_eq_right hω, ofBasis_norm_rational]

/-- The coordinate supremum family is measurable for every adelic structure. -/
theorem ofBasis_isMeasurable : (ofBasis S E b).IsMeasurable := by
  constructor
  intro x
  simp only [ofBasis_norm_rational]
  exact (Measurable.of_eval fun i => S.measurable_absValue (b.equivFun x i)).norm

/-- The mixed basis family is measurable; the Archimedean partition is the
measurable partition supplied by the adelic structure. -/
theorem ofBasisMixed_isMeasurable : (ofBasisMixed S E b).IsMeasurable := by
  constructor
  classical
  intro x
  simp only [ofBasisMixed_norm_rational]
  apply Measurable.ite (S.measurableSet_Ωinf)
  · exact Finset.measurable_sum _ fun i _ => S.measurable_absValue (b.equivFun x i)
  · exact (Measurable.of_eval fun i => S.measurable_absValue (b.equivFun x i)).norm

/-- The coordinate maximum has an integrable upper logarithmic bound for
every adelic structure. -/
theorem ofBasis_isUpperDominated : (ofBasis S E b).IsUpperDominated := by
  constructor
  intro x hx
  refine ⟨fun ω => ∑ i, |Real.log ((S.ϕ ω) (b.equivFun x i))|,
    S.integrable_sum_abs_log (b.equivFun x), Filter.Eventually.of_forall ?_⟩
  intro ω
  apply (Real.log_le_iff_le_exp ((ofBasis S E b).norm_rational_pos ω hx)).mpr
  rw [ofBasis_norm_rational]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
  exact S.absValue_le_exp_sum_abs_log (b.equivFun x) ω i

/-- The only extra envelope for the coordinate sum is a constant supported
on the infinite locus. Thus finite measure of that locus suffices. -/
theorem ofBasisMixed_isUpperDominated_of_measure_lt_top (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisMixed S E b).IsUpperDominated := by
  constructor
  classical
  intro x hx
  let N : ℝ := max 1 (Fintype.card ι : ℝ)
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  have hI : Integrable (S.Ωinf.indicator (fun _ => Real.log N)) S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  refine ⟨fun ω => (∑ i, |Real.log ((S.ϕ ω) (b.equivFun x i))|) +
    S.Ωinf.indicator (fun _ => Real.log N) ω,
    (S.integrable_sum_abs_log (b.equivFun x)).add hI, Filter.Eventually.of_forall ?_⟩
  intro ω
  apply (Real.log_le_iff_le_exp ((ofBasisMixed S E b).norm_rational_pos ω hx)).mpr
  rw [ofBasisMixed_norm_rational]
  by_cases hω : ω ∈ S.Ωinf
  · simp only [ite_eq_left hω, Set.indicator_of_mem hω, Real.exp_add, Real.exp_log hN]
    calc
      ∑ i, (S.ϕ ω) (b.equivFun x i) ≤
          ∑ _ : ι, Real.exp (∑ i, |Real.log ((S.ϕ ω) (b.equivFun x i))|) :=
        Finset.sum_le_sum fun i _ => S.absValue_le_exp_sum_abs_log (b.equivFun x) ω i
      _ = (Fintype.card ι : ℝ) * Real.exp
          (∑ i, |Real.log ((S.ϕ ω) (b.equivFun x i))|) := by simp
      _ ≤ N * Real.exp (∑ i, |Real.log ((S.ϕ ω) (b.equivFun x i))|) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · simp only [ite_eq_right hω, Set.indicator_of_notMem hω, add_zero]
    apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
    exact S.absValue_le_exp_sum_abs_log (b.equivFun x) ω i

/-- The coordinate maximum is bounded by the mixed coordinate norm. -/
theorem ofBasis_le_ofBasisMixed : ofBasis S E b ≤ ofBasisMixed S E b := by
  intro ω x
  by_cases hω : ω ∈ S.Ωinf
  · rw [ofBasis_norm, ofBasisMixed_norm_of_infinite b ω hω]
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => _root_.norm_nonneg _)).mpr
    intro i
    exact Finset.single_le_sum (fun j _ => _root_.norm_nonneg _) (Finset.mem_univ i)
  · rw [ofBasisMixed_norm_of_finite b ω (not_not.mp hω)]

/-- The coordinate sum loses at most the rank relative to the coordinate
maximum. Writing the factor as `exp (log rank)` covers rank zero too. -/
theorem ofBasisMixed_norm_le_exp_log_card_mul (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed S E b).norm ω x ≤
      Real.exp (Real.log (Fintype.card ι : ℝ)) * (ofBasis S E b).norm ω x := by
  have hone : 1 ≤ Real.exp (Real.log (Fintype.card ι : ℝ)) :=
    Real.one_le_exp_iff.mpr (Real.log_natCast_nonneg _)
  by_cases hω : ω ∈ S.Ωinf
  · rw [ofBasisMixed_norm_of_infinite b ω hω, ofBasis_norm]
    have hcard : (Fintype.card ι : ℝ) ≤ Real.exp (Real.log (Fintype.card ι : ℝ)) := by
      by_cases hc : Fintype.card ι = 0
      · simp [hc]
      · rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hc)]
    calc
      ∑ i, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x i‖ ≤
          ∑ _ : ι, ‖(b.baseChange (S.ϕ ω).Completion).equivFun x‖ :=
        Finset.sum_le_sum fun i _ => norm_le_pi_norm _ i
      _ = (Fintype.card ι : ℝ) * ‖(b.baseChange (S.ϕ ω).Completion).equivFun x‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (_root_.norm_nonneg _)
  · rw [ofBasisMixed_norm_of_finite b ω (not_not.mp hω)]
    exact le_mul_of_one_le_left ((ofBasis S E b).norm_nonneg ω x) hone

/-- Quantitative maximum-versus-sum comparison, with the source's exact
`log rank` correction supported only on the infinite locus. -/
theorem ofBasis_localDist_ofBasisMixed_le [FiniteDimensional K E] (ω : S.Ω) :
    (ofBasis S E b).localDist (ofBasisMixed S E b) ω ≤
      S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) ω := by
  classical
  apply ((ofBasis S E b).localDist_le_iff_norm_le (ofBasisMixed S E b) ω
    (Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _) ω)).mpr
  intro x
  by_cases hω : ω ∈ S.Ωinf
  · rw [Set.indicator_of_mem hω]
    refine ⟨(ofBasis_le_ofBasisMixed b ω x).trans ?_,
      ofBasisMixed_norm_le_exp_log_card_mul b ω x⟩
    exact le_mul_of_one_le_left ((ofBasisMixed S E b).norm_nonneg ω x)
      (Real.one_le_exp_iff.mpr (Real.log_natCast_nonneg _))
  · simp only [Set.indicator_of_notMem hω, Real.exp_zero, one_mul,
      ofBasisMixed_norm_of_finite b ω (not_not.mp hω), le_refl, and_self]

variable [FiniteDimensional K E]

/-- The actual completed dual norm is the maximum of the functional's values
on the completed basis, at every place. -/
theorem ofBasisMixed_dual_norm (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) :
    (ofBasisMixed S E b).dual.norm ω z =
      ‖fun i => dualBaseChangeEquiv K (S.ϕ ω).Completion E z
        ((b.baseChange (S.ϕ ω).Completion) i)‖ := by
  apply le_antisymm
  · apply (ofBasisMixed S E b).dual_norm_le ω z (_root_.norm_nonneg _)
    intro x
    by_cases hω : ω ∈ S.Ωinf
    · rw [ofBasisMixed_norm_of_infinite b ω hω]
      exact norm_linearMap_apply_le_basis_sum _ _ _
    · have hf : ω ∈ S.Ωfin := not_not.mp hω
      have : IsUltrametricDist (S.ϕ ω).Completion :=
        IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
          (S.norm_add_le_max_of_finite ω hf)
      rw [ofBasisMixed_norm_of_finite b ω hf, ofBasis_norm]
      exact norm_linearMap_apply_le_basis_max _ _ _
  · apply (pi_norm_le_iff_of_nonneg ((ofBasisMixed S E b).dual.norm_nonneg ω z)).mpr
    intro i
    have h := (ofBasisMixed S E b).norm_dual_apply_le ω z
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b i)
    simpa only [Module.Basis.baseChange_apply, ofBasisMixed_norm_tmul_basis,
      norm_one, mul_one] using h

/-- Base change of the rational dual basis has precisely the evaluation
coordinates on the completed original basis. -/
theorem dualBaseChange_apply_basis_eq {ι' : Type*} [Finite ι'] [DecidableEq ι']
    (b : Module.Basis ι' K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K E) (i : ι') :
    dualBaseChangeEquiv K (S.ϕ ω).Completion E z
        ((b.baseChange (S.ϕ ω).Completion) i) =
      (b.dualBasis.baseChange (S.ϕ ω).Completion).equivFun z i := by
  induction z using TensorProduct.inductionOn with
  | tmul a ℓ =>
      simp only [Module.Basis.baseChange_apply, dualBaseChangeEquiv_tmul_apply_tmul,
        Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
        Module.Basis.dualBasis_repr, Algebra.smul_def, mul_one, mul_comm]
  | add z t hz ht =>
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, hz, ht]

/-- The dual of the mixed basis family is the coordinate supremum family
of the rational dual basis, as asserted in Example 4.1.5. -/
theorem ofBasisMixed_dual [DecidableEq ι] :
    (ofBasisMixed S E b).dual = ofBasis S (Module.Dual K E) b.dualBasis := by
  ext ω z
  rw [ofBasisMixed_dual_norm, ofBasis_norm]
  congr 1
  funext i
  exact dualBaseChange_apply_basis_eq b ω z i

/-- The dual comparison (4.2) in Example 4.1.5, on the actual completed
dual fibre and with the exact logarithm of the rank. -/
theorem ofBasisMixed_dual_localDist_le [DecidableEq ι] (ω : S.Ω) :
    (ofBasisMixed S E b).dual.localDist
        (ofBasisMixed S (Module.Dual K E) b.dualBasis) ω ≤
      S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) ω := by
  rw [ofBasisMixed_dual]
  exact ofBasis_localDist_ofBasisMixed_le b.dualBasis ω

/-- The quantitative dual comparison has actual integrable envelopes. -/
theorem ofBasisMixed_dual_localDist_hasIntegrableBounds [DecidableEq ι]
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds ((ofBasisMixed S E b).dual.localDist
      (ofBasisMixed S (Module.Dual K E) b.dualBasis)) S.v := by
  refine ⟨⟨S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)), ?_,
    Filter.Eventually.of_forall (ofBasisMixed_dual_localDist_le b)⟩,
    ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩⟩
  · exact (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  · intro ω
    exact (ofBasisMixed S E b).dual.localDist_nonneg _ ω

/-- The actual dual mixed-basis family has measurable rational evaluations. -/
theorem ofBasisMixed_dual_isMeasurable : (ofBasisMixed S E b).dual.IsMeasurable := by
  classical
  rw [ofBasisMixed_dual]
  exact ofBasis_isMeasurable b.dualBasis

/-- The rational dual formula is the maximum of the absolute values of the
dual coordinates `ℓ (b i)`. -/
theorem ofBasisMixed_dual_norm_rational (ω : S.Ω) (ℓ : Module.Dual K E) :
    (ofBasisMixed S E b).dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ℓ) =
      ‖fun i => (S.ϕ ω) (ℓ (b i))‖ := by
  classical
  rw [ofBasisMixed_dual, ofBasis_norm_rational]
  simp only [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]

/-- The mixed family and its actual dual have integrable upper envelopes.
Only finite measure of the Archimedean locus is needed here. -/
theorem ofBasisMixed_isDominated_of_measure_lt_top (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisMixed S E b).IsDominated := by
  classical
  refine ⟨ofBasisMixed_isUpperDominated_of_measure_lt_top b hfin, ?_⟩
  rw [ofBasisMixed_dual]
  exact ofBasis_isUpperDominated b.dualBasis

/-- Domination of the mixed basis family under the usual Archimedean
normalization of Example 4.1.5. -/
theorem ofBasisMixed_isDominated
    [hS : S.IsArchimedeanNormalized] :
    (ofBasisMixed S E b).IsDominated :=
  ofBasisMixed_isDominated_of_measure_lt_top b (S.v_Ωinf_lt_top_of_isRCLike)

/-- Rational logarithmic norms of the mixed family are integrable, including
the convention `log 0 = 0` for the zero vector. -/
theorem ofBasisMixed_integrable_logNorm
    [hS : S.IsArchimedeanNormalized] (x : E) :
    Integrable ((ofBasisMixed S E b).logNorm x) S.v :=
  (ofBasisMixed_isDominated b).integrable_logNorm (ofBasisMixed_isMeasurable b) x

/-- Rational logarithmic norms of the actual dual mixed family are integrable. -/
theorem ofBasisMixed_dual_integrable_logNorm
    [hS : S.IsArchimedeanNormalized]
    (ℓ : Module.Dual K E) : Integrable ((ofBasisMixed S E b).dual.logNorm ℓ) S.v :=
  (ofBasisMixed_isDominated b).dual.integrable_logNorm
    (ofBasisMixed_dual_isMeasurable b) ℓ

omit [FiniteDimensional K E] in
/-- The mixed coordinate family is ultrametric at every finite place. -/
theorem ofBasisMixed_isUltrametric : (ofBasisMixed S E b).IsUltrametric := by
  constructor
  intro ω hω x y
  simp only [ofBasisMixed_norm_of_finite b ω hω, ofBasis_norm]
  apply (pi_norm_le_iff_of_nonneg
    ((_root_.norm_nonneg _).trans (le_max_left _ _))).mpr
  intro i
  simp only [map_add, Pi.add_apply]
  exact (S.norm_add_le_max_of_finite ω hω _ _).trans
    (max_le_max (norm_le_pi_norm _ i) (norm_le_pi_norm _ i))

/-- The mixed basis family is strongly dominated under the source's usual
Archimedean normalization, using actual completed bidual isometry. -/
theorem ofBasisMixed_isStronglyDominated
    [hS : S.IsArchimedeanNormalized] :
    (ofBasisMixed S E b).IsStronglyDominated :=
  ((ofBasisMixed S E b).isStronglyDominated_iff_isDominated_of_ultrametric
    (hξ := (ofBasisMixed_isUltrametric b))).mpr (ofBasisMixed_isDominated b)

end ArakelovGeometry.NormFamily
