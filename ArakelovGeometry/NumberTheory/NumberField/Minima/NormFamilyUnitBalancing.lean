/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.AdelicCurve.InfiniteMass
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Lambda
public import ArakelovGeometry.NumberTheory.NumberField.Minima.UnitBalancing
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational

/-!
# Actual unit balancing of a number-field norm family

Dirichlet's actual units act on the original vector space. Their completed
finite norms are one, so this action preserves the literal integral ball.
The weighted mean uses the original completed norm evaluations at infinity.
-/

@[expose] public section

open MeasureTheory Function
open scoped NumberField TensorProduct BigOperators

noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
variable (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)

/-- Actual integral units have value one at every finite normalized place. -/
theorem normalized_unit_absValue_eq_one
    (u : (𝓞 K)ˣ) (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    (normalizedNumberFieldAdelicStructure K).ϕ ω (algebraMap (𝓞 K) K u) = 1 := by
  let v := (normalizedNumberFieldAdelicStructure K).ϕ ω
  have hu := NumberField.abs_le_one_of_isIntegral hω
    (NumberField.RingOfIntegers.isIntegral_coe (u : 𝓞 K))
  have hi := NumberField.abs_le_one_of_isIntegral hω
    (NumberField.RingOfIntegers.isIntegral_coe (u⁻¹ : (𝓞 K)ˣ))
  have hmul : v (algebraMap (𝓞 K) K u) *
      v (algebraMap (𝓞 K) K (u⁻¹ : (𝓞 K)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hle : v (algebraMap (𝓞 K) K u) *
      v (algebraMap (𝓞 K) K (u⁻¹ : (𝓞 K)ˣ)) ≤ v (algebraMap (𝓞 K) K u) :=
    (mul_le_mul_of_nonneg_left hi (v.nonneg _)).trans_eq (mul_one _)
  exact le_antisymm hu (by rwa [hmul] at hle)

/-- The unit action preserves literal finite completed norm evaluations. -/
theorem norm_rational_unit_smul_finite
    (u : (𝓞 K)ˣ) (x : E) (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin) :
    ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K u • x)) =
      ξ.norm ω (1 ⊗ₜ[K] x) := by
  rw [ξ.norm_rational_smul, normalized_unit_absValue_eq_one u ω hω, one_mul]

/-- No ultrametric hypothesis is needed for preservation of the literal ball. -/
theorem unit_smul_mem_globalUnitBall_iff (u : (𝓞 K)ˣ) (x : E) :
    algebraMap (𝓞 K) K u • x ∈ ξ.globalUnitBall ↔ x ∈ ξ.globalUnitBall := by
  constructor <;> intro h ω hω
  · change ξ.norm ω (1 ⊗ₜ[K] x) ≤ 1
    have hn := h ω hω
    change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K u • x)) ≤ 1 at hn
    rwa [ξ.norm_rational_unit_smul_finite u x ω hω] at hn
  · change ξ.norm ω (1 ⊗ₜ[K] (algebraMap (𝓞 K) K u • x)) ≤ 1
    rw [ξ.norm_rational_unit_smul_finite u x ω hω]
    exact h ω hω

/-- The genuine infinite-place weighted mean of the original completed logs. -/
def archimedeanMeanLogNorm (x : E) : ℝ :=
  NumberFieldUnitBalancing.weightedMean K
    (fun w => ξ.logNorm x (normalizedInfinitePlacePoint w))

/-- The mean is the actual infinite-locus integral divided by the field degree. -/
theorem degree_mul_archimedeanMeanLogNorm_eq_integral (x : E) :
    (Module.finrank ℚ K : ℝ) * ξ.archimedeanMeanLogNorm x =
      ∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf, ξ.logNorm x ω
        ∂(normalizedNumberFieldAdelicStructure K).v := by
  classical
  let S := normalizedNumberFieldAdelicStructure K
  have : MeasurableSingletonClass S.Ω := by
    change MeasurableSingletonClass
      {ω : AbsoluteValue.Place K // ω ≠ AbsoluteValue.trivialPlace K}
    infer_instance
  have hset : S.Ωinf = ⋃ w : NumberField.InfinitePlace K,
      {normalizedInfinitePlacePoint w} := by
    rw [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.range_eq_iUnion]
  have hdisjoint : Pairwise (Disjoint on
      (fun w : NumberField.InfinitePlace K => ({normalizedInfinitePlacePoint w} : Set S.Ω))) := by
    intro w v h
    exact Set.disjoint_singleton.mpr (normalizedInfinitePlacePoint_injective.ne h)
  have hmass (w : NumberField.InfinitePlace K) :
      S.v {normalizedInfinitePlacePoint w} = (w.mult : ENNReal) :=
    normalizedNumberFieldAdelicStructure_v_infinitePlace w
  have hint : ∀ w : NumberField.InfinitePlace K,
      IntegrableOn (ξ.logNorm x) {normalizedInfinitePlacePoint w} S.v := by
    intro w
    exact integrableOn_singleton (by finiteness) (by rw [hmass]; simp)
  rw [hset, integral_iUnion_fintype (fun _ => measurableSet_singleton _) hdisjoint hint]
  simp only [integral_singleton, Measure.real, hmass,
    ENNReal.toReal_natCast, smul_eq_mul]
  unfold archimedeanMeanLogNorm NumberFieldUnitBalancing.weightedMean
  exact mul_div_cancel₀ _ (show (Module.finrank ℚ K : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne')

theorem logNorm_unit_smul_infinite (u : (𝓞 K)ˣ) {x : E} (hx : x ≠ 0)
    (w : NumberField.InfinitePlace K) :
    ξ.logNorm (algebraMap (𝓞 K) K u • x) (normalizedInfinitePlacePoint w) =
      ξ.logNorm x (normalizedInfinitePlacePoint w) + Real.log (w u) := by
  have hu : algebraMap (𝓞 K) K u ≠ 0 :=
    (IsFractionRing.injective (𝓞 K) K).ne (Units.ne_zero u)
  rw [ξ.logNorm_smul hu hx]
  rw [show (normalizedNumberFieldAdelicStructure K).ϕ
    (normalizedInfinitePlacePoint w) = w.val from normalizedPlaceValue_eq_infinitePlace w]
  exact add_comm _ _

/-- Actual units uniformly balance the original norm-family evaluations. -/
theorem exists_unit_archimedeanMaxNorm_le {x : E} (hx : x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, ξ.archimedeanMaxNorm (algebraMap (𝓞 K) K u • x) ≤
      Real.exp (ξ.archimedeanMeanLogNorm x + NumberFieldUnitBalancing.balancingConstant K) := by
  classical
  obtain ⟨u, hu⟩ := NumberFieldUnitBalancing.exists_weighted_unit_balancing K
    (fun w => ξ.logNorm x (normalizedInfinitePlacePoint w))
  refine ⟨u, (ξ.archimedeanMaxNorm_le_iff _ (Real.exp_pos _).le).mpr ?_⟩
  intro ω hω
  obtain ⟨w, rfl⟩ := normalizedNumberFieldAdelicStructure_Ωinf_eq_range.le hω
  have hn : algebraMap (𝓞 K) K u • x ≠ 0 :=
    smul_ne_zero ((IsFractionRing.injective (𝓞 K) K).ne (Units.ne_zero u)) hx
  have hlog := hu w
  rw [← ξ.logNorm_unit_smul_infinite u hx w] at hlog
  exact (Real.log_le_iff_le_exp (ξ.norm_rational_pos _ hn)).mp hlog

/-- The balanced vector remains in the same actual finite integral ball. -/
theorem exists_unit_smul_globalUnitBall_archimedeanMaxNorm_le
    {x : E} (hx : x ≠ 0) (hint : x ∈ ξ.globalUnitBall) :
    ∃ u : (𝓞 K)ˣ, algebraMap (𝓞 K) K u • x ∈ ξ.globalUnitBall ∧
      ξ.archimedeanMaxNorm (algebraMap (𝓞 K) K u • x) ≤
        Real.exp (ξ.archimedeanMeanLogNorm x + NumberFieldUnitBalancing.balancingConstant K) := by
  obtain ⟨u, hu⟩ := ξ.exists_unit_archimedeanMaxNorm_le hx
  exact ⟨u, (ξ.unit_smul_mem_globalUnitBall_iff u x).mpr hint, hu⟩

/-- Units rescale every actual integral basis while preserving its independent
rational directions and producing the balanced Archimedean bounds. -/
theorem exists_unit_rescaled_integral_basis
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (hb : ∀ i, b i ∈ ξ.globalUnitBall) :
    ∃ u : Fin (Module.finrank K E) → (𝓞 K)ˣ,
      ∃ c : Module.Basis (Fin (Module.finrank K E)) K E,
        (∀ i, c i = algebraMap (𝓞 K) K (u i) • b i) ∧
        ∀ i, c i ∈ ξ.globalUnitBall ∧ ξ.archimedeanMaxNorm (c i) ≤
          Real.exp (ξ.archimedeanMeanLogNorm (b i) +
            NumberFieldUnitBalancing.balancingConstant K) := by
  classical
  choose u hu hbound using fun i =>
    ξ.exists_unit_smul_globalUnitBall_archimedeanMaxNorm_le (b.ne_zero i) (hb i)
  let c := b.unitsSMul (fun i => Units.map (algebraMap (𝓞 K) K).toMonoidHom (u i))
  have hc (i) : c i = algebraMap (𝓞 K) K (u i) • b i := by
    simp only [c, Module.Basis.unitsSMul_apply, Units.smul_def, Units.coe_map]
    rfl
  exact ⟨u, c, hc, fun i => by rw [hc]; exact ⟨hu i, hbound i⟩⟩

/-- A common bound for the actual infinite mean produces a genuine integral
basis threshold through actual unit rescaling. -/
theorem mem_integralBasisThresholds_of_archimedeanMeanLogNorm_le
    (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (hb : ∀ i, b i ∈ ξ.globalUnitBall) {a : ℝ}
    (hm : ∀ i, ξ.archimedeanMeanLogNorm (b i) +
      NumberFieldUnitBalancing.balancingConstant K ≤ -a) :
    a ∈ ξ.integralBasisThresholds := by
  obtain ⟨u, c, hc, hbound⟩ := ξ.exists_unit_rescaled_integral_basis b hb
  refine ⟨c, fun i => ⟨(hbound i).1, (hbound i).2.trans ?_⟩⟩
  exact Real.exp_le_exp.mpr (hm i)

end ArakelovGeometry.NormFamily
