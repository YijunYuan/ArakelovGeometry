/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Spanning

import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.Analysis.AbsoluteValue.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.CategoryTheory.Category.Init

/-!
# Actual completed local unit balls and rational density

The completed unit ball is the literal ball of the given completed fibre norm.
Rational scalar completion density produces its rational unit-ball density;
no density, local lattice or global coherence certificate is assumed.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.AdelicStructure

universe u v

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- The whole rational field is genuinely dense in every actual scalar completion. -/
theorem isDenseSubfieldAt_top (ω : S.Ω) : S.IsDenseSubfieldAt (⊤ : Subfield K) ω := by
  apply Dense.mono (hd := UniformSpace.Completion.denseRange_coe (α := WithAbs (S.ϕ ω)))
  rintro z ⟨a, rfl⟩
  exact ⟨⟨a.ofAbs, Subfield.mem_top _⟩, rfl⟩

/-- The actual completed nonarchimedean scalar norm is an NNReal-valued valuation. -/
def completedValuation (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Valuation (S.ϕ ω).Completion NNReal where
  toFun a := ‖a‖₊
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul
  map_add_le_max' a b := by
    let := AbsoluteValue.isUltrametricDist_completion (S.ϕ ω) hω
    exact_mod_cast IsUltrametricDist.norm_add_le_max a b

@[simp]
theorem completedValuation_coe (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : (S.ϕ ω).Completion) :
    (S.completedValuation ω hω a : ℝ) = ‖a‖ := rfl

/-- The actual completed valuation ring consists exactly of completed scalars
with their actual absolute value at most one. -/
def completedLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin) : Subring (S.ϕ ω).Completion :=
  (S.completedValuation ω hω).integer

@[simp]
theorem mem_completedLocalRing (ω : S.Ω) (hω : ω ∈ S.Ωfin) (a : (S.ϕ ω).Completion) :
    a ∈ S.completedLocalRing ω hω ↔ ‖a‖ ≤ 1 := by
  change ‖a‖₊ ≤ 1 ↔ ‖a‖ ≤ 1
  exact_mod_cast Iff.rfl

/-- The actual scalar completion embedding restricts canonically to the actual
rational and completed local coefficient rings. -/
def completedLocalCoefficientMap (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    S.rationalLocalRing ω hω →+* S.completedLocalRing ω hω where
  toFun a := ⟨algebraMap K (S.ϕ ω).Completion (a : K), by
    rw [S.mem_completedLocalRing, S.norm_algebraMap_eq_absValue]
    exact a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem completedLocalCoefficientMap_coe (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (a : S.rationalLocalRing ω hω) :
    (S.completedLocalCoefficientMap ω hω a : (S.ϕ ω).Completion) =
      algebraMap K (S.ϕ ω).Completion (a : K) := rfl

/-- Canonical rational local coefficients act through the actual completion embedding. -/
instance completedLocalRing_algebra (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Algebra (S.rationalLocalRing ω hω) (S.completedLocalRing ω hω) :=
  (S.completedLocalCoefficientMap ω hω).toAlgebra

/-- The local coefficient actions agree with the actual completed field action. -/
instance completedLocalRing_scalarTower (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    IsScalarTower (S.rationalLocalRing ω hω) (S.completedLocalRing ω hω)
      (S.ϕ ω).Completion :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end ArakelovGeometry.AdelicStructure

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- The literal completed local unit ball of the actual fibre norm. -/
def completedUnitBall (ξ : NormFamily S E) (ω : S.Ω) : Set ((S.ϕ ω).Completion ⊗[K] E) :=
  {z | ξ.norm ω z ≤ 1}

@[simp]
theorem mem_completedUnitBall (ξ : NormFamily S E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] E) :
    z ∈ ξ.completedUnitBall ω ↔ ξ.norm ω z ≤ 1 := Iff.rfl

/-- The actual completed unit ball is closed in its own given norm topology. -/
theorem isClosed_completedUnitBall (ξ : NormFamily S E) (ω : S.Ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    IsClosed (ξ.completedUnitBall ω) := by
  let := ξ.fibreNormedAddCommGroup ω
  exact isClosed_le continuous_norm continuous_const

/-- The literal completed unit ball is an actual module over the actual
completed local coefficient ring. -/
def completedUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    [hξ : ξ.IsUltrametric] :
    Submodule (S.completedLocalRing ω hω) ((S.ϕ ω).Completion ⊗[K] E) where
  carrier := ξ.completedUnitBall ω
  zero_mem' := by simp
  add_mem' {x y} hx hy := (hξ ω hω x y).trans (max_le hx hy)
  smul_mem' r {x} hx := by
    change ξ.norm ω ((r : (S.ϕ ω).Completion) • x) ≤ 1
    rw [ξ.norm_smul]
    have hr : ‖(r : (S.ϕ ω).Completion)‖ ≤ 1 :=
      (S.mem_completedLocalRing ω hω _).mp r.property
    exact (mul_le_mul hr hx (ξ.norm_nonneg _ _) zero_le_one).trans_eq (mul_one 1)

@[simp]
theorem coe_completedUnitBallModule (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    [hξ : ξ.IsUltrametric] :
    (ξ.completedUnitBallModule ω hω : Set ((S.ϕ ω).Completion ⊗[K] E)) =
      ξ.completedUnitBall ω := rfl

/-- Restricting actual completed coefficients gives the canonical rational action. -/
instance completedUnitBall_rationalModule (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    Module (S.rationalLocalRing ω hω) (ξ.completedUnitBallModule ω hω) :=
  (ξ.completedUnitBallModule ω hω).module'

/-- The rational and completed actions on the literal unit ball form the actual tower. -/
instance completedUnitBall_rationalScalarTower (ξ : NormFamily S E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    IsScalarTower (S.rationalLocalRing ω hω) (S.completedLocalRing ω hω)
      (ξ.completedUnitBallModule ω hω) :=
  (ξ.completedUnitBallModule ω hω).isScalarTower

/-- The canonical actual local-ball inclusion into its completed unit-ball module. -/
def rationalUnitBallCompletionMap (ξ : NormFamily S E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    [hξ : ξ.IsUltrametric] :
    ξ.rationalUnitBallModule ω hω →ₗ[S.rationalLocalRing ω hω]
      ξ.completedUnitBallModule ω hω where
  toFun x := ⟨1 ⊗ₜ[K] (x : E), x.property⟩
  map_add' _ _ := Subtype.ext (TensorProduct.tmul_add _ _ _)
  map_smul' r x := by
    apply Subtype.ext
    change (1 : (S.ϕ ω).Completion) ⊗ₜ[K] (↑(r • x) : E) =
      ↑(r • (⟨1 ⊗ₜ[K] (x : E), x.property⟩ : ξ.completedUnitBallModule ω hω))
    rw [Submodule.coe_smul r x,
      Submodule.coe_smul_of_tower r
        (⟨1 ⊗ₜ[K] (x : E), x.property⟩ : ξ.completedUnitBallModule ω hω),
      Subring.smul_def r (x : E)]
    have ht : (algebraMap (S.rationalLocalRing ω hω) K r) •
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (x : E)) =
        r • ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] (x : E)) :=
      IsScalarTower.algebraMap_smul K r _
    exact (TensorProduct.tmul_smul (r : K) (1 : (S.ϕ ω).Completion) (x : E)).trans ht

@[simp]
theorem rationalUnitBallCompletionMap_coe (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] (x : ξ.rationalUnitBallModule ω hω) :
    (ξ.rationalUnitBallCompletionMap ω hω x : (S.ϕ ω).Completion ⊗[K] E) =
      1 ⊗ₜ[K] (x : E) := rfl

/-- The actual rational-ball completion map is injective on original vectors. -/
theorem rationalUnitBallCompletionMap_injective (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    Function.Injective (ξ.rationalUnitBallCompletionMap ω hω) := by
  intro x y h
  apply Subtype.ext
  apply rational_tmul_injective ω
  exact congrArg (fun z : ξ.completedUnitBallModule ω hω =>
    (z : (S.ϕ ω).Completion ⊗[K] E)) h

/-- The canonical completed-coefficient tensor map into the literal completed
unit ball; its surjectivity is not built into the definition. -/
def rationalUnitBallCompletedTensorMap (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    (S.completedLocalRing ω hω) ⊗[S.rationalLocalRing ω hω]
      (ξ.rationalUnitBallModule ω hω) →ₗ[S.completedLocalRing ω hω]
      ξ.completedUnitBallModule ω hω := by
  letI := ξ.completedUnitBall_rationalScalarTower ω hω
  exact (ξ.rationalUnitBallCompletionMap ω hω).liftBaseChange (S.completedLocalRing ω hω)

@[simp]
theorem rationalUnitBallCompletedTensorMap_tmul (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] (a : S.completedLocalRing ω hω)
    (x : ξ.rationalUnitBallModule ω hω) :
    ξ.rationalUnitBallCompletedTensorMap ω hω (a ⊗ₜ[S.rationalLocalRing ω hω] x) =
      a • ξ.rationalUnitBallCompletionMap ω hω x := by
  let := ξ.completedUnitBall_rationalScalarTower ω hω
  exact LinearMap.liftBaseChange_tmul _ _ _ _

variable [FiniteDimensional K E]

/-- Actual rational scalar completion density gives rational vector density in
the canonical completed tensor fibre for its actual norm. -/
theorem denseRange_rational_tmul (ξ : NormFamily S E) (ω : S.Ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    DenseRange (fun x : E => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  let := ξ.fibreNormedAddCommGroup ω
  let b := Module.finBasis K E
  have hd := ξ.denseRange_basisSubfieldMap b (⊤ : Subfield K) ω (S.isDenseSubfieldAt_top ω)
  apply Dense.mono (hd := hd)
  rintro z ⟨c, rfl⟩
  exact ⟨basisSubfieldMap b (⊤ : Subfield K) c, rfl⟩

/-- Every actual completed unit-ball vector admits arbitrarily accurate
rational approximants that remain in the literal rational unit ball. -/
theorem exists_rationalUnitBall_approx (ξ : NormFamily S E) [hξ : ξ.IsUltrametric]
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) {z : (S.ϕ ω).Completion ⊗[K] E}
    (hz : z ∈ ξ.completedUnitBall ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ ξ.rationalUnitBall ω,
      ξ.norm ω (z - (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) < ε := by
  let := ξ.fibreNormedAddCommGroup ω
  obtain ⟨x, hx⟩ := (ξ.denseRange_rational_tmul ω).exists_dist_lt z (lt_min hε zero_lt_one)
  have herr : ξ.norm ω (z - (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) < min ε 1 := by
    rw [dist_eq_norm] at hx
    exact hx
  refine ⟨x, ?_, herr.trans_le (min_le_left _ _)⟩
  have herr' : ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x - z) ≤ 1 := by
    change ‖(1 : (S.ϕ ω).Completion) ⊗ₜ[K] x - z‖ ≤ 1
    rw [norm_sub_rev]
    exact (herr.trans_le (min_le_right _ _)).le
  have h := (hξ ω hω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x - z) z).trans
    (max_le herr' hz)
  change ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) ≤ 1
  simpa only [sub_add_cancel] using h

/-- The closure in the actual norm topology of the literal rational local
unit-ball image is exactly the literal completed local unit ball. -/
theorem closure_rationalUnitBall_image_eq_completedUnitBall
    (ξ : NormFamily S E) [hξ : ξ.IsUltrametric] (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    letI := ξ.fibreNormedAddCommGroup ω
    closure ((fun x : E => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) '' ξ.rationalUnitBall ω) =
      ξ.completedUnitBall ω := by
  let := ξ.fibreNormedAddCommGroup ω
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (ξ.isClosed_completedUnitBall ω)
    rintro z ⟨x, hx, rfl⟩
    exact hx
  · intro z hz
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨x, hx, herr⟩ := ξ.exists_rationalUnitBall_approx ω hω hz hε
    exact ⟨1 ⊗ₜ[K] x, ⟨x, hx, rfl⟩, by rw [dist_eq_norm]; exact herr⟩

/-- The genuine rational local-ball completion map has dense range in the
literal completed local-ball module for the given fibre norm topology. -/
theorem denseRange_rationalUnitBallCompletionMap (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    letI := ξ.fibreNormedAddCommGroup ω
    DenseRange (ξ.rationalUnitBallCompletionMap ω hω) := by
  let := ξ.fibreNormedAddCommGroup ω
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨x, hx, herr⟩ := ξ.exists_rationalUnitBall_approx ω hω z.property hε
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [Subtype.dist_eq, dist_eq_norm]
  exact herr

/-- Completed-coefficient extension of the actual rational local unit ball
has dense image in the literal completed unit-ball module. -/
theorem denseRange_rationalUnitBallCompletedTensorMap (ξ : NormFamily S E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) [hξ : ξ.IsUltrametric] :
    letI := ξ.fibreNormedAddCommGroup ω
    DenseRange (ξ.rationalUnitBallCompletedTensorMap ω hω) := by
  let := ξ.fibreNormedAddCommGroup ω
  apply Dense.mono (hd := ξ.denseRange_rationalUnitBallCompletionMap ω hω)
  rintro z ⟨x, rfl⟩
  exact ⟨1 ⊗ₜ[S.rationalLocalRing ω hω] x, by
    rw [ξ.rationalUnitBallCompletedTensorMap_tmul, one_smul]⟩

end ArakelovGeometry.NormFamily

end
