/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Dual
import ArakelovGeometry.AdelicVectorBundle.DirectSum
import ArakelovGeometry.Analysis.ArchimedeanDual
import ArakelovGeometry.Analysis.EuclideanNormShape
import ArakelovGeometry.Analysis.HermitianNorm
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Hermitian norm families

The source's Hermitian condition is imposed on the actual completed fibres:
ultrametricity at finite places and a positive definite inner product inducing
the prescribed norm at infinite places.  The usual Archimedean normalization
of each completed field is supplied explicitly.  Inner-product cores fix the
existing completed scalar action.
-/

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {F : Type w'} [AddCommGroup F] [Module K F]

/-- Chen–Moriwaki's Hermitian condition, with the usual Archimedean normalization
explicit.  The inner-product core is positive definite and uses the canonical
module structure of the completed fibre. -/
def IsHermitian (ξ : NormFamily S E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : Prop :=
  ξ.IsUltrametric ∧ ∀ ω (hω : ω ∈ S.Ωinf),
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
      ∀ x, (ξ.norm ω x) ^ 2 = RCLike.re (c.inner x x)

variable {ξ : NormFamily S E}
  {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}

/-- The diagonal identity in `IsHermitian` gives exactly the source's
square-root formula for the norm. -/
theorem IsHermitian.exists_innerProduct_norm_eq_sqrt (hξ : ξ.IsHermitian hS)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    ∃ c : InnerProductSpace.Core (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E),
      ∀ x, ξ.norm ω x = Real.sqrt (RCLike.re (c.inner x x)) := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  obtain ⟨c, hc⟩ := hξ.2 ω hω
  refine ⟨c, fun x => ?_⟩
  rw [← hc, Real.sqrt_sq (ξ.norm_nonneg ω x)]

/-- An equivalent condition expressed entirely in the original fibre norms.
The reverse implication constructs positive definite inner products by
polarization, without changing the scalar action. -/
theorem isHermitian_iff_parallelogram : ξ.IsHermitian hS ↔
    ξ.IsUltrametric ∧ ∀ ω ∈ S.Ωinf, ∀ x y,
      ξ.norm ω (x + y) * ξ.norm ω (x + y) +
        ξ.norm ω (x - y) * ξ.norm ω (x - y) =
      2 * (ξ.norm ω x * ξ.norm ω x + ξ.norm ω y * ξ.norm ω y) := by
  constructor
  · rintro ⟨hu, hi⟩
    refine ⟨hu, fun ω hω => ?_⟩
    let := hS ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    have h := exists_innerProductCore_iff_innerProductSpaceable.mp (hi ω hω)
    exact h.parallelogram_identity
  · rintro ⟨hu, hp⟩
    refine ⟨hu, fun ω hω => ?_⟩
    let := hS ω hω
    let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    exact exists_innerProductCore_iff_innerProductSpaceable.mpr ⟨hp ω hω⟩

/-- Pullback along an injective map preserves the source Hermitian condition. -/
theorem IsHermitian.pullback (hξ : ξ.IsHermitian hS)
    (f : F →ₗ[K] E) (hf : Function.Injective f) :
    (ξ.pullback f hf).IsHermitian hS := by
  obtain ⟨hu, hp⟩ := isHermitian_iff_parallelogram.mp hξ
  apply isHermitian_iff_parallelogram.mpr
  refine ⟨hu.pullback f hf, fun ω hω x y => ?_⟩
  simpa only [pullback_norm, map_add, map_sub] using
    hp ω hω (f.baseChange (S.ϕ ω).Completion x) (f.baseChange (S.ϕ ω).Completion y)

/-- Restriction to a subspace preserves Hermitianity, including the zero subspace. -/
theorem IsHermitian.restrict (hξ : ξ.IsHermitian hS) (F : Submodule K E) :
    (ξ.restrict F).IsHermitian hS :=
  hξ.pullback F.subtype F.subtype_injective

/-- Multiplying each fibre norm by a positive real number preserves Hermitianity. -/
theorem IsHermitian.scale (hξ : ξ.IsHermitian hS)
    (a : S.Ω → ℝ) (ha : ∀ ω, 0 < a ω) : (ξ.scale a ha).IsHermitian hS := by
  obtain ⟨hu, hp⟩ := isHermitian_iff_parallelogram.mp hξ
  apply isHermitian_iff_parallelogram.mpr
  refine ⟨hu.scale a ha, fun ω hω x y => ?_⟩
  simp only [scale_norm]
  linear_combination (a ω) ^ 2 * hp ω hω x y

/-- A zero-dimensional norm family is Hermitian; no nonzero vector or
nonempty basis is required. -/
theorem isHermitian_of_subsingleton [Subsingleton E] : ξ.IsHermitian hS := by
  apply isHermitian_iff_parallelogram.mpr
  constructor
  · intro ω hω x y
    simp only [ξ.norm_eq_zero_of_subsingleton, max_self, le_refl]
  · intro ω hω x y
    simp only [ξ.norm_eq_zero_of_subsingleton, mul_zero, add_zero]

/-- The actual completed dual norm family of a Hermitian family is Hermitian.
At infinite places, the operator norm is transported from the continuous dual,
whose parallelogram law follows from the Riesz isometry. -/
theorem IsHermitian.dual [FiniteDimensional K E] (hξ : ξ.IsHermitian hS) :
    ξ.dual.IsHermitian hS := by
  refine ⟨ξ.dual_isUltrametric, fun ω hω => ?_⟩
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.dual.fibreNormedAddCommGroup ω
  let := ξ.dual.fibreNormedSpace ω
  have : InnerProductSpaceable ((S.ϕ ω).Completion ⊗[K] E) :=
    exists_innerProductCore_iff_innerProductSpaceable.mp (hξ.2 ω hω)
  have : CompleteSpace ((S.ϕ ω).Completion ⊗[K] E) :=
    FiniteDimensional.complete (S.ϕ ω).Completion _
  have : InnerProductSpaceable
      (StrongDual (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)) :=
    innerProductSpaceable_strongDual (L := (S.ϕ ω).Completion)
  let f := (LinearMap.toContinuousLinearMap (𝕜 := (S.ϕ ω).Completion)
    (E := (S.ϕ ω).Completion ⊗[K] E) (F' := (S.ϕ ω).Completion)).toLinearMap.comp
      (dualBaseChangeEquiv K (S.ϕ ω).Completion E).toLinearMap
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  apply innerProductSpaceable_of_norm_preserving_addMonoidHom f.toAddMonoidHom
  intro z
  change ‖LinearMap.toContinuousLinearMap
    (dualBaseChangeEquiv K (S.ϕ ω).Completion E z)‖ =
      linearMapOperatorSeminorm (dualBaseChangeEquiv K (S.ϕ ω).Completion E z)
  exact (linearMapOperatorSeminorm_coe_continuousLinearMap _).symm

/-- The quotient norm along a surjective map preserves Hermitianity.  At an
infinite place the canonical quotient norm is the norm on the orthogonal
complement of the completed kernel, by Mathlib's quotient inner product. -/
theorem IsHermitian.pushforward [FiniteDimensional K E] (hξ : ξ.IsHermitian hS)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).IsHermitian hS := by
  refine ⟨hξ.1.pushforward π hπ, fun ω hω => ?_⟩
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := (ξ.pushforward π hπ).fibreNormedAddCommGroup ω
  let := (ξ.pushforward π hπ).fibreNormedSpace ω
  obtain ⟨c, hc⟩ := hξ.2 ω hω
  let := innerProductSpaceOfCoreNorm c hc
  let W := (π.baseChange (S.ϕ ω).Completion).ker
  have : IsClosed (W : Set ((S.ϕ ω).Completion ⊗[K] E)) :=
    finiteDimensional_submodule_isClosed W
  have : InnerProductSpaceable (((S.ϕ ω).Completion ⊗[K] E) ⧸ W) :=
    InnerProductSpace.toInnerProductSpaceable (S.ϕ ω).Completion
  let e := (π.baseChange (S.ϕ ω).Completion).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective _ hπ)
  apply exists_innerProductCore_iff_innerProductSpaceable.mpr
  exact innerProductSpaceable_of_norm_preserving_addMonoidHom
    e.symm.toLinearMap.toAddMonoidHom (fun _ => rfl)

/-- Quotient by any subspace preserves Hermitianity, including the full
subspace and the zero subspace. -/
theorem IsHermitian.quotient [FiniteDimensional K E] (hξ : ξ.IsHermitian hS)
    (F : Submodule K E) : (ξ.quotient F).IsHermitian hS :=
  hξ.pushforward F.mkQ F.mkQ_surjective

/-- An infinite-place Euclidean profile gives the sum-of-squares identity on
the actual completed direct-sum fibre. -/
theorem directSum_norm_sq_of_profile_eq_euclidean (ξ : NormFamily S E)
    (η : NormFamily S F) (ψ : S.Ω → NormShape) (ω : S.Ω)
    (hψ : Set.EqOn (ψ ω).toFun NormShape.euclideanShape.toFun (Set.Icc (0 : ℝ) 1))
    (z : (S.ϕ ω).Completion ⊗[K] (E × F)) :
    ((ξ.directSum η ψ).norm ω z) ^ 2 =
      (ξ.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).1)) ^ 2 +
      (η.norm ω ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F z).2)) ^ 2 := by
  rw [directSum_norm,
    (ψ ω).perspective_congr NormShape.euclideanShape hψ (apply_nonneg _ _) (apply_nonneg _ _)]
  exact NormShape.euclideanShape_perspective_sq (apply_nonneg _ _) (apply_nonneg _ _)

/-- Source profiles agreeing with the max profile at finite places and the
Euclidean profile at infinite places preserve Hermitian norm families. -/
theorem IsHermitian.directSum_of_profile_eq {η : NormFamily S F}
    (hξ : ξ.IsHermitian hS) (hη : η.IsHermitian hS) (ψ : S.Ω → NormShape)
    (hfin : ∀ ω ∈ S.Ωfin,
      Set.EqOn (ψ ω).toFun NormShape.maxShape.toFun (Set.Icc (0 : ℝ) 1))
    (hinf : ∀ ω ∈ S.Ωinf,
      Set.EqOn (ψ ω).toFun NormShape.euclideanShape.toFun (Set.Icc (0 : ℝ) 1)) :
    (ξ.directSum η ψ).IsHermitian hS := by
  apply isHermitian_iff_parallelogram.mpr
  refine ⟨hξ.1.directSum_of_profile_eq_max hη.1 ψ hfin, fun ω hω x y => ?_⟩
  let e := TensorProduct.prodRight K (S.ϕ ω).Completion (S.ϕ ω).Completion E F
  have hp := (isHermitian_iff_parallelogram.mp hξ).2 ω hω (e x).1 (e y).1
  have hq := (isHermitian_iff_parallelogram.mp hη).2 ω hω (e x).2 (e y).2
  simp only [← pow_two] at hp hq ⊢
  simp only [directSum_norm_sq_of_profile_eq_euclidean ξ η ψ ω (hinf ω hω),
    map_add, map_sub, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  change _ + _ + (_ + _) = 2 * ((_ + _) + (_ + _))
  dsimp only [e] at hp hq
  linear_combination hp + hq

/-- The source orthogonal direct sum: max norm at finite places and Euclidean
norm at infinite places. -/
noncomputable def orthogonalSum (ξ : NormFamily S E) (η : NormFamily S F) :
    NormFamily S (E × F) := by
  classical
  exact ξ.directSum η (fun ω =>
    if ω ∈ S.Ωinf then NormShape.euclideanShape else NormShape.maxShape)

/-- The orthogonal direct-sum norm is the max norm at finite places. -/
theorem orthogonalSum_norm_pair_of_finite (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.orthogonalSum η).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) = max (ξ.norm ω x) (η.norm ω y) := by
  have hn : ω ∉ S.Ωinf := fun h => h hω
  simp only [orthogonalSum, directSum_norm_pair, if_neg hn]
  exact NormShape.maxShape_perspective (ξ.norm_nonneg ω x) (η.norm_nonneg ω y)

/-- The orthogonal direct-sum norm is the Euclidean norm at infinite places. -/
theorem orthogonalSum_norm_pair_of_infinite (ξ : NormFamily S E) (η : NormFamily S F)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] E) (y : (S.ϕ ω).Completion ⊗[K] F) :
    (ξ.orthogonalSum η).norm ω
      ((TensorProduct.prodRight K (S.ϕ ω).Completion
        (S.ϕ ω).Completion E F).symm (x, y)) =
      Real.sqrt ((ξ.norm ω x) ^ 2 + (η.norm ω y) ^ 2) := by
  simp only [orthogonalSum, directSum_norm_pair, if_pos hω]
  exact NormShape.euclideanShape_perspective (ξ.norm_nonneg ω x) (η.norm_nonneg ω y)

/-- Orthogonal direct sums of Hermitian families are Hermitian. -/
theorem IsHermitian.orthogonalSum {η : NormFamily S F}
    (hξ : ξ.IsHermitian hS) (hη : η.IsHermitian hS) :
    (ξ.orthogonalSum η).IsHermitian hS := by
  apply hξ.directSum_of_profile_eq hη
  · intro ω hω t ht
    have hn : ω ∉ S.Ωinf := fun h => h hω
    simp only [if_neg hn]
  · intro ω hω t ht
    simp only [if_pos hω]

end ArakelovGeometry.NormFamily
