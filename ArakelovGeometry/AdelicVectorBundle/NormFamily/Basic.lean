/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion

import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Norm families on completed scalar extensions

The norm-family datum of Chen–Moriwaki, §4.1.1 and §4.1.1.1
(PDF pages 221–222, printed pages 205–206), assigns a scalar-compatible norm to each
completed fibre `K_ω ⊗[K] E`. Tensor commutation identifies this orientation with
`E ⊗[K] K_ω` in the source.

The family is explicit data. Its fibre normed-group and normed-space structures
are installed locally, allowing several norms on the same underlying tensor
space in comparison theorems. Positive rescaling preserves this norm-family datum.

Measurability, domination, Hermitian properties and Archimedean normalization are
separate hypotheses. The definition itself applies to arbitrary vector spaces.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

universe u w

variable {K : Type u} [Field K]

/-- A family of norms on the completed scalar extensions of a vector space.
This is the norm-family datum of §4.1.1, without measurability or domination. -/
structure NormFamily (S : AdelicStructure K) (E : Type w)
    [AddCommGroup E] [Module K E] where
  /-- The norm on each completed fibre, using Mathlib's scalar-compatible seminorm. -/
  norm : (ω : S.Ω) → Seminorm (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E)
  /-- Each fibre seminorm separates zero. -/
  norm_eq_zero_iff : ∀ ω x, norm ω x = 0 ↔ x = 0

namespace NormFamily

variable {S : AdelicStructure K} {E : Type w} [AddCommGroup E] [Module K E]

/-- Interchanging tensor factors respects multiplication on the completed-field factor.
The right-factor action is expressed by `TensorProduct.map`, so no competing scalar
action on the source orientation is installed. -/
theorem comm_map_mul (ω : S.Ω) (a : (S.ϕ ω).Completion)
    (z : E ⊗[K] (S.ϕ ω).Completion) :
    TensorProduct.comm K E (S.ϕ ω).Completion
        (TensorProduct.map LinearMap.id (LinearMap.mulLeft K a) z) =
      a • TensorProduct.comm K E (S.ϕ ω).Completion z := by
  induction z using TensorProduct.inductionOn with
  | tmul x b => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [hx, hy, smul_add]

@[ext]
theorem ext {ξ η : NormFamily S E}
    (h : ∀ ω x, ξ.norm ω x = η.norm ω x) : ξ = η := by
  rcases ξ with ⟨p, hp⟩
  rcases η with ⟨q, hq⟩
  have hpq : p = q := funext fun ω ↦ Seminorm.ext (h ω)
  cases hpq
  rfl

variable (ξ : NormFamily S E)

@[simp]
theorem norm_zero (ω : S.Ω) : ξ.norm ω 0 = 0 := map_zero _

theorem norm_nonneg (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    0 ≤ ξ.norm ω x := apply_nonneg _ _

theorem norm_pos (ω : S.Ω) {x : (S.ϕ ω).Completion ⊗[K] E} (hx : x ≠ 0) :
    0 < ξ.norm ω x :=
  lt_of_le_of_ne' (ξ.norm_nonneg ω x) (fun h ↦ hx ((ξ.norm_eq_zero_iff ω x).mp h))

theorem norm_add_le (ω : S.Ω) (x y : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω (x + y) ≤ ξ.norm ω x + ξ.norm ω y := map_add_le_add _ _ _

@[simp]
theorem norm_neg (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω (-x) = ξ.norm ω x := map_neg_eq_map _ _

theorem norm_smul (ω : S.Ω) (a : (S.ϕ ω).Completion)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω (a • x) = ‖a‖ * ξ.norm ω x := map_smul_eq_mul _ _ _

/-- The normed additive group supplied by the separated seminorm of a fibre.
It is deliberately not a global instance: a fibre can carry many norm families. -/
noncomputable abbrev fibreNormedAddCommGroup (ω : S.Ω) :
    NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] E) :=
  (⟨(ξ.norm ω).toAddGroupSeminorm, fun x ↦ (ξ.norm_eq_zero_iff ω x).mp⟩ :
    AddGroupNorm ((S.ϕ ω).Completion ⊗[K] E)).toNormedAddCommGroup

/-- Scalar compatibility of the local normed additive group. -/
noncomputable abbrev fibreNormedSpace (ω : S.Ω) :
    letI := ξ.fibreNormedAddCommGroup ω
    NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] E) := by
  letI := ξ.fibreNormedAddCommGroup ω
  exact ⟨fun a x ↦ (ξ.norm_smul ω a x).le⟩

/-- The norm transported to the source's tensor orientation is homogeneous for
all completed scalars, acting on the right tensor factor. -/
theorem norm_comm_map_mul (ω : S.Ω) (a : (S.ϕ ω).Completion)
    (z : E ⊗[K] (S.ϕ ω).Completion) :
    ξ.norm ω (TensorProduct.comm K E (S.ϕ ω).Completion
        (TensorProduct.map LinearMap.id (LinearMap.mulLeft K a) z)) =
      ‖a‖ * ξ.norm ω (TensorProduct.comm K E (S.ϕ ω).Completion z) := by
  rw [comm_map_mul, norm_smul]

/-- In dimension zero every fibre norm vanishes identically. -/
theorem norm_eq_zero_of_subsingleton [Subsingleton E] (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) : ξ.norm ω x = 0 := by
  rw [Subsingleton.elim x 0, norm_zero]

instance instSubsingleton [Subsingleton E] : Subsingleton (NormFamily S E) where
  allEq ξ η := by
    ext ω x
    rw [norm_eq_zero_of_subsingleton, norm_eq_zero_of_subsingleton]

/-- Ultrametricity is imposed at every non-Archimedean place, as in §4.1.1. -/
class IsUltrametricAtFinitePlaces : Prop where
  /-- The defining property. -/
  norm_add_le_max :
    ∀ ω ∈ S.Ωfin, ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)

instance : CoeFun (ξ.IsUltrametricAtFinitePlaces)
    (fun _ ↦
      ∀ ω ∈ S.Ωfin, ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :=
  ⟨fun h ↦ h.norm_add_le_max⟩

/-- The defining proposition of `IsUltrametricAtFinitePlaces`. -/
theorem IsUltrametricAtFinitePlaces.iff :
    ξ.IsUltrametricAtFinitePlaces ↔
    ∀ ω ∈ S.Ωfin, ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y) :=
  ⟨fun h ↦ h.norm_add_le_max, fun h ↦ ⟨h⟩⟩

noncomputable section

/-- Multiplication by an arbitrary positive numerical function (§4.1.1.1). -/
def scale (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) : NormFamily S E where
  norm ω := NNReal.mk (f ω) (hf ω).le • ξ.norm ω
  norm_eq_zero_iff ω x := by
    change f ω * ξ.norm ω x = 0 ↔ x = 0
    rw [mul_eq_zero, or_iff_right (hf ω).ne', ξ.norm_eq_zero_iff]

@[simp]
theorem scale_norm (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ξ.scale f hf).norm ω x = f ω * ξ.norm ω x := rfl

@[simp]
theorem scale_one : ξ.scale (fun _ ↦ 1) (fun _ ↦ zero_lt_one) = ξ := by
  ext ω x
  simp

/-- Every rescaling fixes the unique norm family on a zero-dimensional space. -/
theorem scale_eq_self_of_subsingleton [Subsingleton E]
    (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) : ξ.scale f hf = ξ :=
  Subsingleton.elim _ _

/-- Successive rescalings multiply their numerical functions. -/
theorem scale_scale (f g : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (hg : ∀ ω, 0 < g ω) :
    (ξ.scale f hf).scale g hg =
      ξ.scale (fun ω ↦ g ω * f ω) (fun ω ↦ mul_pos (hg ω) (hf ω)) := by
  ext ω x
  simp only [scale_norm, mul_assoc]

@[simp]
theorem scale_inv_scale (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale f hf).scale (fun ω ↦ (f ω)⁻¹) (fun ω ↦ inv_pos.mpr (hf ω)) = ξ := by
  ext ω x
  simp only [scale_norm, ← mul_assoc, inv_mul_cancel₀ (hf ω).ne', one_mul]

@[simp]
theorem scale_scale_inv (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale (fun ω ↦ (f ω)⁻¹) (fun ω ↦ inv_pos.mpr (hf ω))).scale f hf = ξ := by
  ext ω x
  simp only [scale_norm, ← mul_assoc, mul_inv_cancel₀ (hf ω).ne', one_mul]

/-- Positive rescaling acts bijectively on all norm families. -/
def scaleEquiv (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) : NormFamily S E ≃ NormFamily S E where
  toFun η := η.scale f hf
  invFun η := η.scale (fun ω ↦ (f ω)⁻¹) (fun ω ↦ inv_pos.mpr (hf ω))
  left_inv η := η.scale_inv_scale f hf
  right_inv η := η.scale_scale_inv f hf

theorem scale_injective (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    Function.Injective (fun η : NormFamily S E ↦ η.scale f hf) :=
  (scaleEquiv f hf).injective

/-- Scaling by a positive function preserves the non-Archimedean triangle inequality. -/
theorem IsUltrametricAtFinitePlaces.scale {ξ : NormFamily S E} (hξ : ξ.IsUltrametricAtFinitePlaces)
    (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) : (ξ.scale f hf).IsUltrametricAtFinitePlaces := by
  constructor
  intro ω hω x y
  simp only [scale_norm, ← mul_max_of_nonneg _ _ (hf ω).le]
  exact mul_le_mul_of_nonneg_left (hξ ω hω x y) (hf ω).le

/-- Positive rescaling preserves and reflects ultrametricity. -/
@[simp]
theorem scale_isUltrametricAtFinitePlaces_iff (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) :
    (ξ.scale f hf).IsUltrametricAtFinitePlaces ↔ ξ.IsUltrametricAtFinitePlaces := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.scale f hf⟩
  simpa only [scale_inv_scale] using h.scale (fun ω ↦ (f ω)⁻¹)
    (fun ω ↦ inv_pos.mpr (hf ω))

/-- For a nonzero vector, positive rescaling adds the logarithm of the scale factor. -/
theorem log_scale_norm (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (ω : S.Ω)
    {x : (S.ϕ ω).Completion ⊗[K] E} (hx : x ≠ 0) :
    Real.log ((ξ.scale f hf).norm ω x) = Real.log (f ω) + Real.log (ξ.norm ω x) := by
  rw [scale_norm, Real.log_mul (hf ω).ne' (ξ.norm_pos ω hx).ne']

variable (S E)

/-- The coordinate supremum norm in each scalar extension of a finite basis. -/
def ofBasis {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) : NormFamily S E where
  norm ω := (normSeminorm (S.ϕ ω).Completion (ι → (S.ϕ ω).Completion)).comp
    (b.baseChange (S.ϕ ω).Completion).equivFun.toLinearMap
  norm_eq_zero_iff ω x := by
    change ‖(b.baseChange (S.ϕ ω).Completion).equivFun x‖ = 0 ↔ x = 0
    rw [norm_eq_zero, LinearEquiv.map_eq_zero_iff]

@[simp]
theorem ofBasis_norm {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasis S E b).norm ω x = ‖(b.baseChange (S.ϕ ω).Completion).equivFun x‖ := rfl

/-- A scalar multiple of a basis vector has its scalar's absolute value as norm. -/
@[simp]
theorem ofBasis_norm_tmul_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)
    (ω : S.Ω) (a : (S.ϕ ω).Completion) (i : ι) :
    (ofBasis S E b).norm ω (a ⊗ₜ[K] b i) = ‖a‖ := by
  classical
  have ht : a ⊗ₜ[K] b i = a • (b.baseChange (S.ϕ ω).Completion) i := by
    simp [Module.Basis.baseChange_apply, TensorProduct.smul_tmul']
  have hc : (b.baseChange (S.ϕ ω).Completion).equivFun
      ((b.baseChange (S.ϕ ω).Completion) i) = Pi.single i 1 := by
    ext j
    simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [ht, norm_smul, ofBasis_norm, hc, Pi.norm_single, norm_one, mul_one]

/-- Rescaling the constructed coordinate norm evaluates to the prescribed positive
factor on each scalar-extended basis vector. -/
theorem scale_ofBasis_norm_tmul_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι K E)
    (f : S.Ω → ℝ) (hf : ∀ ω, 0 < f ω) (ω : S.Ω)
    (a : (S.ϕ ω).Completion) (i : ι) :
    ((ofBasis S E b).scale f hf).norm ω (a ⊗ₜ[K] b i) = f ω * ‖a‖ := by
  rw [scale_norm, ofBasis_norm_tmul_basis]

/-- The empty-basis construction produces the unique zero-dimensional norm family. -/
@[simp]
theorem ofBasis_empty_norm [Subsingleton E] (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasis S E (Module.Basis.empty (ι := Fin 0) (R := K) E)).norm ω x = 0 :=
  norm_eq_zero_of_subsingleton _ _ _

/-- Finite-dimensional vector spaces admit norm families, including in dimension zero. -/
theorem nonempty [FiniteDimensional K E] : Nonempty (NormFamily S E) :=
  ⟨ofBasis S E (Module.finBasis K E)⟩

noncomputable instance instInhabitedOfFiniteDimensional [FiniteDimensional K E] :
    Inhabited (NormFamily S E) :=
  ⟨ofBasis S E (Module.finBasis K E)⟩

end

end NormFamily

end ArakelovGeometry
