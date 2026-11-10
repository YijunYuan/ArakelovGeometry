/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.ScalarExtensionLine
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar extension of explicit separated fibre seminorms

The existing scalar-extension norm is applied to a given separated seminorm,
preserving the original additive and scalar structures. On a line, the
scalar-extension unit preserves that norm exactly.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {k E : Type*} [NormedField k] [CompleteSpace k]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]

/-- The given separated seminorm changes only the metric structure. -/
abbrev geometricFibreNormedGroup (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0) :
    NormedAddCommGroup E :=
  (⟨p.toAddGroupSeminorm, fun x ↦ (hp x).mp⟩ : AddGroupNorm E).toNormedAddCommGroup

/-- Homogeneity supplies the compatible normed-space structure. -/
abbrev geometricFibreNormedSpace (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0) :
    letI := geometricFibreNormedGroup p hp
    NormedSpace k E := by
  letI := geometricFibreNormedGroup p hp
  exact ⟨fun a x ↦ (map_smul_eq_mul p a x).le⟩

variable {L : Type*} [NormedField L] [NormedAlgebra k L]

/-- Projective scalar extension of the original explicit fibre norm. -/
def geometricScalarExtensionSeminorm (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0) :
    Seminorm L (L ⊗[k] E) := by
  letI := geometricFibreNormedGroup p hp
  letI := geometricFibreNormedSpace p hp
  exact scalarExtensionProjectiveSeminorm

theorem geometricScalarExtensionSeminorm_eq_zero_iff
    (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0) (z : L ⊗[k] E) :
    geometricScalarExtensionSeminorm p hp z = 0 ↔ z = 0 := by
  let := geometricFibreNormedGroup p hp
  let := geometricFibreNormedSpace p hp
  exact scalarExtensionProjectiveSeminorm_eq_zero_iff z

/-- The scalar-extension unit preserves every norm on a line. -/
theorem geometricScalarExtensionSeminorm_one_tmul
    (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0)
    (hr : Module.finrank k E = 1) (x : E) :
    geometricScalarExtensionSeminorm p hp ((1 : L) ⊗ₜ[k] x) = p x := by
  let := geometricFibreNormedGroup p hp
  let := geometricFibreNormedSpace p hp
  let b := Module.finBasisOfFinrankEq k E hr
  have hx : (b.repr x) 0 • b 0 = x := by
    simpa only [Fin.sum_univ_one] using b.sum_repr x
  change scalarExtensionProjectiveSeminorm ((1 : L) ⊗ₜ[k] x) = ‖x‖
  rw [← hx, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rw [(scalarExtensionSeminorms_tmul_of_basis b _).1, norm_algebraMap, norm_smul]
  simp only [norm_one, mul_one]

end ArakelovGeometry

namespace ArakelovGeometry

universe u

variable {k L : Type u} [NormedField k] [CompleteSpace k] [NormedField L]

/-- An actual isometric field map supplies its normed algebra structure. -/
abbrev geometricIsometricNormedAlgebra (φ : k →+* L) (hφ : Isometry φ) : NormedAlgebra k L where
  toAlgebra := φ.toAlgebra
  norm_smul_le a z := by
    change ‖φ a * z‖ ≤ ‖a‖ * ‖z‖
    rw [norm_mul, hφ.norm_map_of_map_zero φ.map_zero]

/-- The explicit norm on the categorical scalar extension used by sheaf fibres. -/
def geometricModuleScalarExtensionSeminorm (φ : k →+* L) (hφ : Isometry φ)
    (E : ModuleCat.{u} k) [FiniteDimensional k E]
    (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0) :
    Seminorm L ((ModuleCat.extendScalars φ).obj E) := by
  letI := geometricIsometricNormedAlgebra φ hφ
  exact geometricScalarExtensionSeminorm p hp

theorem geometricModuleScalarExtensionSeminorm_eq_zero_iff
    (φ : k →+* L) (hφ : Isometry φ) (E : ModuleCat.{u} k) [FiniteDimensional k E]
    (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0)
    (z : (ModuleCat.extendScalars φ).obj E) :
    geometricModuleScalarExtensionSeminorm φ hφ E p hp z = 0 ↔ z = 0 := by
  let := geometricIsometricNormedAlgebra φ hφ
  exact geometricScalarExtensionSeminorm_eq_zero_iff (L := L) p hp z

/-- The actual categorical unit is isometric for every separated norm on a line. -/
theorem geometricModuleScalarExtensionSeminorm_unit
    (φ : k →+* L) (hφ : Isometry φ) (E : ModuleCat.{u} k) [FiniteDimensional k E]
    (p : Seminorm k E) (hp : ∀ x, p x = 0 ↔ x = 0)
    (hr : Module.finrank k E = 1) (x : E) :
    geometricModuleScalarExtensionSeminorm φ hφ E p hp
      ((ModuleCat.extendRestrictScalarsAdj φ).unit.app E x) = p x := by
  let := geometricIsometricNormedAlgebra φ hφ
  exact geometricScalarExtensionSeminorm_one_tmul p hp hr x

end ArakelovGeometry
