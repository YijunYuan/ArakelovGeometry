/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.CountableHermitianMeasurable
public import ArakelovGeometry.AdelicVectorBundle.CountableInjectiveMeasurable

/-!
# Measurability of actual orthogonal tensor norms

The Archimedean argument expands the actual tensor pairing into products of
the factor pairings. At finite places the orthogonal norm is the already
constructed injective norm.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- Rational factor pairings are measurable in the compatible completed embeddings. -/
theorem IsMeasurable.archimedeanInner_rational {V : Type w} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {ξ : NormFamily S V} (hξ : ξ.IsMeasurable)
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS)
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) (x y : V) :
    Measurable (fun ω : S.Ωinf => σ ω (hH.archimedeanInner ω
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x)
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] y))) := by
  apply hξ.archimedeanInner_of_measurable_coordinates hH (Module.finBasis K V)
    id measurable_id σ hσ hm K₀ (fun ω => hK₀ ω.val ω.property)
  all_goals
    intro i
    simpa only [id_eq, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, mul_one] using hm _

variable {ι : Type wι} [Fintype ι]
  {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  (ξ : ∀ i, NormFamily S (E i))
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hH : ∀ i, (ξ i).IsHermitian hS)

/-- The defining product pairing of the actual completed orthogonal tensor norm. -/
def orthogonalTensorArchInner (ω : S.Ωinf)
    (x y : (S.ϕ ω.val).Completion ⊗[K] (⨂[K] i, E i)) : (S.ϕ ω.val).Completion := by
  classical
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω.val
  let : ∀ i, NormedSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω.val
  let : ∀ i, InnerProductSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (hH i).fibreInnerProductSpace ω.val ω.property
  let b := fun i =>
    stdOrthonormalBasis (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i)
  exact inner (S.ϕ ω.val).Completion
    (ArakelovGeometry.orthogonalTensorCoordinates b
      (tensorBaseChangeEquiv K (S.ϕ ω.val).Completion E x))
    (ArakelovGeometry.orthogonalTensorCoordinates b
      (tensorBaseChangeEquiv K (S.ϕ ω.val).Completion E y))

/-- Additivity of the defining tensor pairing in its first variable. -/
theorem orthogonalTensorArchInner_add_left (ω : S.Ωinf)
    (x y z : (S.ϕ ω.val).Completion ⊗[K] (⨂[K] i, E i)) :
    orthogonalTensorArchInner ξ hS hH ω (x + y) z =
      orthogonalTensorArchInner ξ hS hH ω x z + orthogonalTensorArchInner ξ hS hH ω y z := by
  classical
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  simp only [orthogonalTensorArchInner, map_add, inner_add_left]

/-- Additivity of the defining tensor pairing in its second variable. -/
theorem orthogonalTensorArchInner_add_right (ω : S.Ωinf)
    (x y z : (S.ϕ ω.val).Completion ⊗[K] (⨂[K] i, E i)) :
    orthogonalTensorArchInner ξ hS hH ω x (y + z) =
      orthogonalTensorArchInner ξ hS hH ω x y + orthogonalTensorArchInner ξ hS hH ω x z := by
  classical
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  simp only [orthogonalTensorArchInner, map_add, inner_add_right]

/-- The embedded pairing of rational pure tensors is the product of the
embedded factor pairings, with the exact conjugate-first scalar factors. -/
theorem orthogonalTensorArchInner_rational_tprod (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (r s : K) (x y : ∀ i, E i) :
    σ (orthogonalTensorArchInner ξ hS hH ω
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] (r • (⨂ₜ[K] i, x i)))
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] (s • (⨂ₜ[K] i, y i)))) =
      σ (algebraMap K (S.ϕ ω.val).Completion s) *
        (starRingEnd ℂ (σ (algebraMap K (S.ϕ ω.val).Completion r)) *
          ∏ i, σ ((hH i).archimedeanInner ω
            ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x i)
            ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] y i))) := by
  classical
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω.val
  let : ∀ i, NormedSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω.val
  let : ∀ i, InnerProductSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (hH i).fibreInnerProductSpace ω.val ω.property
  have ht (a : K) (z : ⨂[K] i, E i) :
      (1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] (a • z) =
        algebraMap K (S.ϕ ω.val).Completion a •
          ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] z) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [ht, ht]
  simp only [orthogonalTensorArchInner,
    map_smul, tensorBaseChangeEquiv_tmul_tprod, one_smul, inner_smul_left,
    inner_smul_right, map_mul, complexEmbedding_map_conj σ hσ]
  congr 2
  rw [← map_prod]
  congr 1
  exact ArakelovGeometry.orthogonalTensorCore_tprod _ _ _

/-- The diagonal of the defining tensor pairing is precisely the actual
orthogonal norm squared, independent of the complex orientation. -/
theorem orthogonalTensor_norm_sq_eq_re_archInner (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (z : (S.ϕ ω.val).Completion ⊗[K] (⨂[K] i, E i)) :
    (orthogonalTensor ξ hS hH).norm ω.val z ^ 2 =
      (σ (orthogonalTensorArchInner ξ hS hH ω z z)).re := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let : ∀ i, NormedAddCommGroup ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedAddCommGroup ω.val
  let : ∀ i, NormedSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (ξ i).fibreNormedSpace ω.val
  let : ∀ i, InnerProductSpace (S.ϕ ω.val).Completion ((S.ϕ ω.val).Completion ⊗[K] E i) :=
    fun i => (hH i).fibreInnerProductSpace ω.val ω.property
  rw [orthogonalTensor_norm_of_infinite ξ hS hH ω.val ω.property,
    complexEmbedding_re σ hσ]
  exact ArakelovGeometry.orthogonalTensorSeminorm_sq _ _

/-- Finite expansion of the actual tensor pairing gives measurable rational
evaluations from the measurable factor pairings. -/
theorem measurable_orthogonalTensorArchInner
    (hξ : ∀ i, (ξ i).IsMeasurable)
    (σ : ∀ ω : S.Ωinf, (S.ϕ ω.val).Completion →+* ℂ)
    (hσ : ∀ ω x, ‖σ ω x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun ω : S.Ωinf =>
      σ ω (algebraMap K (S.ϕ ω.val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) (x y : ⨂[K] i, E i) :
    Measurable (fun ω : S.Ωinf => σ ω (orthogonalTensorArchInner ξ hS hH ω
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x)
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] y))) := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s y =>
          have hp : Measurable (fun ω : S.Ωinf => ∏ i, σ ω ((hH i).archimedeanInner ω
              ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] x i)
              ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] y i))) :=
            Finset.measurable_prod _ (fun i _ =>
              (hξ i).archimedeanInner_rational (hH i) σ hσ hm K₀ hK₀ (x i) (y i))
          convert (hm s).mul (((Complex.continuous_conj.measurable).comp (hm r)).mul hp) using 1
          funext ω
          exact orthogonalTensorArchInner_rational_tprod ξ hS hH ω (σ ω) (hσ ω) r s x y
      | add y z hy hz =>
          convert hy.add hz using 1
          funext ω
          simp only [TensorProduct.tmul_add, orthogonalTensorArchInner_add_right, map_add,
            Pi.add_apply]
  | add x z hx hz =>
      convert hx.add hz using 1
      funext ω
      simp only [TensorProduct.tmul_add, orthogonalTensorArchInner_add_left, map_add,
        Pi.add_apply]

/-- At infinite places the norm is the square root of the real diagonal of
the actual measurable product pairing. -/
theorem measurable_orthogonalTensor_norm_infinite
    (hξ : ∀ i, (ξ i).IsMeasurable)
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω ∈ S.Ωinf, S.IsDenseSubfieldAt K₀ ω) (z : ⨂[K] i, E i) :
    Measurable (fun ω : S.Ωinf => (orthogonalTensor ξ hS hH).norm ω.val
      ((1 : (S.ϕ ω.val).Completion) ⊗ₜ[K] z)) := by
  obtain ⟨σ, hσ, hm⟩ := S.exists_measurable_archimedeanComplexEmbedding hS K₀ hK₀
  have hi := (Complex.measurable_re.comp
    (measurable_orthogonalTensorArchInner ξ hS hH hξ σ hσ hm K₀ hK₀ z z)).sqrt
  convert hi using 1
  funext ω
  dsimp only [Function.comp_def]
  rw [← orthogonalTensor_norm_sq_eq_re_archInner ξ hS hH ω (σ ω) (hσ ω),
    Real.sqrt_sq ((orthogonalTensor ξ hS hH).norm_nonneg _ _)]

/-- The actual orthogonal tensor family is measurable under the source common
countable-density hypothesis. Empty tensor products and zero factors are included. -/
theorem IsMeasurable.orthogonalTensor_of_common_countable_dense_subfield
    (hξ : ∀ i, (ξ i).IsMeasurable) (hcount : S.HasCommonCountableDenseSubfield) :
    (orthogonalTensor ξ hS hH).IsMeasurable := by
  intro z
  apply measurable_of_restrict_of_restrict_compl S.measurableSet_Ωinf
  · obtain ⟨K₀, hcard, hdense⟩ := hcount
    let : Countable K₀ := hcard
    exact measurable_orthogonalTensor_norm_infinite ξ hS hH hξ K₀
      (fun ω _ => hdense ω) z
  · have hε := IsMeasurable.injectiveTensor_of_common_countable_dense_subfield ξ hξ hcount
    convert (hε z).comp measurable_subtype_coe using 1
    funext ω
    exact orthogonalTensor_norm_of_finite ξ hS hH ω.val (not_not.mp ω.property) _

end ArakelovGeometry.NormFamily
