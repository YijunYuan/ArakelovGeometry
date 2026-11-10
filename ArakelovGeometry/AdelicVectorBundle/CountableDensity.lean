/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Rational
public import ArakelovGeometry.Analysis.CountableNormEvaluation

/-!
# Countable rational sets dense in completed fibres

A single countable subfield dense in the completed ground fields supplies a
single countable set of rational vectors dense for every completed norm.
All constructions use the prescribed fibre and its actual scalar action.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}

/-- A rational subfield is dense at a place when its actual image in the
completed ground field is dense. -/
def AdelicStructure.IsDenseSubfieldAt (S : AdelicStructure.{u, v} K)
    (K₀ : Subfield K) (ω : S.Ω) : Prop :=
  DenseRange (fun a : K₀ => algebraMap K (S.ϕ ω).Completion (a : K))

/-- The common countability hypothesis of Section 4.1.3 uses one subfield
simultaneously at all places. -/
def AdelicStructure.HasCommonCountableDenseSubfield (S : AdelicStructure.{u, v} K) : Prop :=
  ∃ K₀ : Subfield K, Countable K₀ ∧ ∀ ω, S.IsDenseSubfieldAt K₀ ω

variable {E : Type w} [AddCommGroup E] [Module K E]
  {ι : Type wι} [Fintype ι]

/-- The rational vectors obtained from subfield coefficients in a fixed basis. -/
def basisSubfieldMap (b : Module.Basis ι K E) (K₀ : Subfield K) (c : ι → K₀) : E :=
  ∑ i, (c i : K) • b i

@[simp]
theorem basisSubfieldMap_zero (b : Module.Basis ι K E) (K₀ : Subfield K) :
    basisSubfieldMap b K₀ 0 = 0 := by
  simp [basisSubfieldMap]

/-- The same rational set is countable independently of a place or a norm. -/
theorem countable_range_basisSubfieldMap (b : Module.Basis ι K E) (K₀ : Subfield K)
    [Countable K₀] : (Set.range (basisSubfieldMap b K₀)).Countable :=
  Set.countable_range _

namespace NormFamily

/-- Explicit scalar-extension compatibility of the subfield combinations. -/
theorem basisSubfieldMap_tmul (b : Module.Basis ι K E) (K₀ : Subfield K)
    (ω : S.Ω) (c : ι → K₀) :
    (1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c =
      (b.baseChange (S.ϕ ω).Completion).equivFun.symm
        (fun i => algebraMap K (S.ϕ ω).Completion (c i : K)) := by
  simp only [basisSubfieldMap, Module.Basis.equivFun_symm_apply,
    Module.Basis.baseChange_apply, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Subfield combinations in a rational basis are dense for the actual
completed norm, including over trivially normed fields and in rank zero. -/
theorem denseRange_basisSubfieldMap (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    DenseRange (fun c : ι → K₀ =>
      (1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let f := (b.baseChange (S.ϕ ω).Completion).equivFun.symm
  have hc : Continuous f := (linearMapToNormedAddGroupHom f.toLinearMap).continuous
  have hd : DenseRange (fun c : ι → K₀ =>
      fun i => algebraMap K (S.ϕ ω).Completion (c i : K)) :=
    DenseRange.piMap (fun _ => hK₀)
  have h := f.surjective.denseRange.comp hd hc
  simpa only [Function.comp_def, basisSubfieldMap_tmul] using h

/-- The rational nonzero condition is exactly the nonzero condition in every
completed fibre. This keeps the punctured countable index independent of place. -/
theorem basisSubfieldMap_tmul_ne_zero_iff (b : Module.Basis ι K E) (K₀ : Subfield K)
    (ω : S.Ω) (c : ι → K₀) :
    (1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c ≠ 0 ↔
      basisSubfieldMap b K₀ c ≠ 0 := by
  have hi := rational_tmul_injective (E := E) ω
  constructor
  · intro h hz
    apply h
    simp [hz]
  · intro h hz
    apply h
    apply hi
    simpa using hz

/-- The nonzero rational combinations are dense in the nonzero completed
fibre. The assertion includes the empty punctured fibre in dimension zero. -/
theorem denseRange_basisSubfieldMap_nonzero (ξ : NormFamily S E) (b : Module.Basis ι K E)
    (K₀ : Subfield K) (ω : S.Ω) (hK₀ : S.IsDenseSubfieldAt K₀ ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    DenseRange (fun c : {c : ι → K₀ // basisSubfieldMap b K₀ c ≠ 0} =>
      (⟨(1 : (S.ϕ ω).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c,
        (basisSubfieldMap_tmul_ne_zero_iff b K₀ ω c).mpr c.property⟩ :
          {x : (S.ϕ ω).Completion ⊗[K] E // x ≠ 0})) := by
  let := ξ.fibreNormedAddCommGroup ω
  have hd := denseRange_subtype_ne_zero _ (ξ.denseRange_basisSubfieldMap b K₀ ω hK₀)
  apply Dense.mono (hd := hd)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨c.val, (basisSubfieldMap_tmul_ne_zero_iff b K₀ ω c.val).mp c.property⟩, rfl⟩

/-- Every norm and completed linear coordinate is continuous in the actual
fibre topology, including for trivially valued completed ground fields. -/
theorem continuous_completed_linearMap [FiniteDimensional K E] (ξ : NormFamily S E)
    (ω : S.Ω) (f : ((S.ϕ ω).Completion ⊗[K] E) →ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion) :
    letI := ξ.fibreNormedAddCommGroup ω
    Continuous f := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  exact (linearMapToNormedAddGroupHom f).continuous

/-- A completed dual-evaluation ratio is continuous away from zero. -/
theorem continuousOn_completed_dualRatio [FiniteDimensional K E] (ξ : NormFamily S E)
    (ω : S.Ω) (f : ((S.ϕ ω).Completion ⊗[K] E) →ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion) :
    letI := ξ.fibreNormedAddCommGroup ω
    ContinuousOn (fun x => ‖f x‖ / ξ.norm ω x) {x | x ≠ 0} := by
  let := ξ.fibreNormedAddCommGroup ω
  exact (ξ.continuous_completed_linearMap ω f).norm.continuousOn.div
    continuous_norm.continuousOn (fun x hx => (ξ.norm_pos ω hx).ne')

/-- One countable rational set works for every place and every norm family.
The basis and rational coefficients are chosen before either parameter. -/
theorem exists_countable_dense_rational_set [FiniteDimensional K E]
    (hS : S.HasCommonCountableDenseSubfield) :
    ∃ D : Set E, D.Countable ∧ ∀ (ξ : NormFamily S E) (ω : S.Ω),
      letI := ξ.fibreNormedAddCommGroup ω
      Dense ((fun x : E => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) '' D) := by
  obtain ⟨K₀, hcount, hK₀⟩ := hS
  let : Countable K₀ := hcount
  let b := Module.finBasis K E
  refine ⟨Set.range (basisSubfieldMap b K₀), countable_range_basisSubfieldMap b K₀, ?_⟩
  intro ξ ω
  let := ξ.fibreNormedAddCommGroup ω
  rw [← Set.range_comp]
  exact ξ.denseRange_basisSubfieldMap b K₀ ω (hK₀ ω)

end NormFamily

end ArakelovGeometry
