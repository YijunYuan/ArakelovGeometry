/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.IntervalTensorDeterminant

/-!
# Actual determinant input norms for the interval tensor example

The actual factor exterior quotient lengths are identified on every vector
with their canonical determinant coordinates and packaged as separating norms.
Their genuine projective tensor powers and ordinary binary tensor then give
input norm one on the powered standard factor wedges. The canonical determinant
representation has actual output exterior quotient length at most one half,
so it fails to preserve these lengths. This is a local real counterexample;
the global same-constant strong-Minkowski implication remains open.
-/

@[expose] public section

open scoped TensorProduct
open Module

namespace ArakelovGeometry

noncomputable section

/-- Every vector of the actual plane determinant line has its proved
projective exterior quotient length equal to its scalar determinant coordinate norm. -/
theorem intervalProjectiveExteriorLength₂_eq_coordinate
    (η : ⋀[ℝ]^2 (Fin 2 → ℝ)) :
    intervalProjectiveExteriorLength₂ η =
      ‖determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 2)) η‖ := by
  let e := determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 2))
  have hη : η = e η • exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2)) := by
    rw [← determinantCoordinateEquiv_symm]
    exact (e.symm_apply_apply η).symm
  calc
    _ = intervalProjectiveExteriorLength₂
        (e η • exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2))) := congrArg _ hη
    _ = |e η| := intervalProjectiveExteriorLength₂_smul_basis _
    _ = ‖e η‖ := (Real.norm_eq_abs _).symm

/-- Every vector of the actual three-space determinant line has its proved
projective exterior quotient length equal to its scalar determinant coordinate norm. -/
theorem intervalProjectiveExteriorLength₃_eq_coordinate
    (η : ⋀[ℝ]^3 (Fin 3 → ℝ)) :
    intervalProjectiveExteriorLength₃ η =
      ‖determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 3)) η‖ := by
  let e := determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 3))
  have hη : η = e η • exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3)) := by
    rw [← determinantCoordinateEquiv_symm]
    exact (e.symm_apply_apply η).symm
  calc
    _ = intervalProjectiveExteriorLength₃
        (e η • exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3))) := congrArg _ hη
    _ = |e η| := intervalProjectiveExteriorLength₃_smul_basis _
    _ = ‖e η‖ := (Real.norm_eq_abs _).symm

/-- The actual plane exterior quotient function, now bundled as a seminorm. -/
def intervalExteriorQuotientSeminorm₂ : Seminorm ℝ (⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  Seminorm.of intervalProjectiveExteriorLength₂
    (by
      intro x y
      simp only [intervalProjectiveExteriorLength₂_eq_coordinate, map_add]
      exact norm_add_le _ _)
    (by
      intro a x
      simp only [intervalProjectiveExteriorLength₂_eq_coordinate, map_smul, norm_smul])

/-- The actual three-space exterior quotient function, now bundled as a seminorm. -/
def intervalExteriorQuotientSeminorm₃ : Seminorm ℝ (⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  Seminorm.of intervalProjectiveExteriorLength₃
    (by
      intro x y
      simp only [intervalProjectiveExteriorLength₃_eq_coordinate, map_add]
      exact norm_add_le _ _)
    (by
      intro a x
      simp only [intervalProjectiveExteriorLength₃_eq_coordinate, map_smul, norm_smul])

/-- The bundled plane exterior seminorm is the actual quotient length on all vectors. -/
theorem intervalExteriorQuotientSeminorm₂_apply (η : ⋀[ℝ]^2 (Fin 2 → ℝ)) :
    intervalExteriorQuotientSeminorm₂ η = intervalProjectiveExteriorLength₂ η := rfl

/-- The bundled three-space exterior seminorm is the actual quotient length on all vectors. -/
theorem intervalExteriorQuotientSeminorm₃_apply (η : ⋀[ℝ]^3 (Fin 3 → ℝ)) :
    intervalExteriorQuotientSeminorm₃ η = intervalProjectiveExteriorLength₃ η := rfl

/-- The actual plane exterior quotient length separates zero. -/
theorem intervalExteriorQuotientSeminorm₂_eq_zero_iff (η : ⋀[ℝ]^2 (Fin 2 → ℝ)) :
    intervalExteriorQuotientSeminorm₂ η = 0 ↔ η = 0 := by
  rw [intervalExteriorQuotientSeminorm₂_apply, intervalProjectiveExteriorLength₂_eq_coordinate,
    norm_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The actual three-space exterior quotient length separates zero. -/
theorem intervalExteriorQuotientSeminorm₃_eq_zero_iff (η : ⋀[ℝ]^3 (Fin 3 → ℝ)) :
    intervalExteriorQuotientSeminorm₃ η = 0 ↔ η = 0 := by
  rw [intervalExteriorQuotientSeminorm₃_apply, intervalProjectiveExteriorLength₃_eq_coordinate,
    norm_eq_zero, LinearEquiv.map_eq_zero_iff]

/-- The actual plane exterior quotient norm. -/
def intervalExteriorQuotientNorm₂ : AddGroupNorm (⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  ⟨intervalExteriorQuotientSeminorm₂.toAddGroupSeminorm,
    fun x hx => (intervalExteriorQuotientSeminorm₂_eq_zero_iff x).mp hx⟩

/-- The actual three-space exterior quotient norm. -/
def intervalExteriorQuotientNorm₃ : AddGroupNorm (⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  ⟨intervalExteriorQuotientSeminorm₃.toAddGroupSeminorm,
    fun x hx => (intervalExteriorQuotientSeminorm₃_eq_zero_iff x).mp hx⟩

/-- The plane norm package evaluates to the actual exterior quotient length on every vector. -/
theorem intervalExteriorQuotientNorm₂_apply (η : ⋀[ℝ]^2 (Fin 2 → ℝ)) :
    intervalExteriorQuotientNorm₂ η = intervalProjectiveExteriorLength₂ η := rfl

/-- The three-space norm package evaluates to the actual exterior quotient
length on every vector. -/
theorem intervalExteriorQuotientNorm₃_apply (η : ⋀[ℝ]^3 (Fin 3 → ℝ)) :
    intervalExteriorQuotientNorm₃ η = intervalProjectiveExteriorLength₃ η := rfl

local instance intervalInputExteriorPlaneNormed : NormedAddCommGroup (⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  intervalExteriorQuotientNorm₂.toNormedAddCommGroup

local instance intervalInputExteriorPlaneSeminormed :
    SeminormedAddCommGroup (⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  intervalExteriorQuotientNorm₂.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalInputExteriorPlaneSpace : NormedSpace ℝ (⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  ⟨fun a x => by
    change intervalExteriorQuotientSeminorm₂ (a • x) ≤ ‖a‖ * intervalExteriorQuotientSeminorm₂ x
    exact (map_smul_eq_mul intervalExteriorQuotientSeminorm₂ a x).le⟩

local instance intervalInputExteriorThreeNormed : NormedAddCommGroup (⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  intervalExteriorQuotientNorm₃.toNormedAddCommGroup

local instance intervalInputExteriorThreeSeminormed :
    SeminormedAddCommGroup (⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  intervalExteriorQuotientNorm₃.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalInputExteriorThreeSpace : NormedSpace ℝ (⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  ⟨fun a x => by
    change intervalExteriorQuotientSeminorm₃ (a • x) ≤ ‖a‖ * intervalExteriorQuotientSeminorm₃ x
    exact (map_smul_eq_mul intervalExteriorQuotientSeminorm₃ a x).le⟩

/-- Scalar-coordinate isometries of real lines give the exact genuine finite
projective tensor seminorm, proved using all presentation costs. -/
theorem projectiveSeminorm_eq_norm_scalarCoordinate
    {ι : Type*} [Fintype ι] {D : ι → Type*}
    [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
    (e : ∀ i, D i ≃ₗ[ℝ] ℝ) (he : ∀ i x, ‖e i x‖ = ‖x‖)
    (z : ⨂[ℝ] i, D i) :
    PiTensorProduct.projectiveSeminorm z =
      ‖(PiTensorProduct.constantBaseRingEquiv ι ℝ)
        (PiTensorProduct.congr e z)‖ := by
  let f := (PiTensorProduct.congr e).trans
    (PiTensorProduct.constantBaseRingEquiv ι ℝ).toLinearEquiv
  have hf (x : ∀ i, D i) : f (PiTensorProduct.tprod ℝ x) = ∏ i, e i (x i) := by
    simp only [f, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      PiTensorProduct.constantBaseRingEquiv_tprod, AlgEquiv.toLinearEquiv_apply]
  have hlo : ‖f z‖ ≤ PiTensorProduct.projectiveSeminorm z := by
    have h := norm_linearMap_le_projective_of_tprod_le f.toLinearMap
      (C := 1) (by norm_num) (fun x => by
        rw [LinearEquiv.coe_coe, hf, norm_prod, one_mul]
        simp only [he, le_refl]) z
    simpa only [one_mul, LinearEquiv.coe_coe] using h
  let g : ∀ i, D i := fun i => (e i).symm 1
  have hgcoord : f (PiTensorProduct.tprod ℝ g) = 1 := by
    rw [hf]
    simp only [g, LinearEquiv.apply_symm_apply, Finset.prod_const_one]
  have hgnorm (i : ι) : ‖g i‖ = 1 := by
    calc
      _ = ‖e i (g i)‖ := (he i (g i)).symm
      _ = 1 := by simp only [g, LinearEquiv.apply_symm_apply, norm_one]
  have hg : PiTensorProduct.projectiveSeminorm (PiTensorProduct.tprod ℝ g) ≤ 1 := by
    have h := PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := ℝ) g
    change PiTensorProduct.projectiveSeminorm (PiTensorProduct.tprod ℝ g) ≤
      ∏ i, ‖g i‖ at h
    simpa only [hgnorm, Finset.prod_const_one] using h
  have hz : z = f z • PiTensorProduct.tprod ℝ g := by
    apply f.injective
    rw [map_smul, hgcoord, smul_eq_mul, mul_one]
  apply le_antisymm _ hlo
  calc
    _ = PiTensorProduct.projectiveSeminorm (f z • PiTensorProduct.tprod ℝ g) :=
      congrArg _ hz
    _ = ‖f z‖ * PiTensorProduct.projectiveSeminorm (PiTensorProduct.tprod ℝ g) :=
      map_smul_eq_mul _ _ _
    _ ≤ ‖f z‖ * 1 := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = ‖f z‖ := mul_one _

/-- Exact genuine projective seminorm on every vector of the actual triple
plane determinant tensor. -/
theorem intervalExteriorPlaneTriple_projective_eq_coordinate
    (z : ⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) :
    PiTensorProduct.projectiveSeminorm z =
      ‖determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 2)) 3 z‖ := by
  apply projectiveSeminorm_eq_norm_scalarCoordinate
    (fun _ => determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 2)))
  intro _ x
  exact (intervalProjectiveExteriorLength₂_eq_coordinate x).symm

/-- Exact genuine projective seminorm on every vector of the actual double
three-space determinant tensor. -/
theorem intervalExteriorThreeDouble_projective_eq_coordinate
    (z : ⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :
    PiTensorProduct.projectiveSeminorm z =
      ‖determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 3)) 2 z‖ := by
  apply projectiveSeminorm_eq_norm_scalarCoordinate
    (fun _ => determinantCoordinateEquiv (Pi.basisFun ℝ (Fin 3)))
  intro _ x
  exact (intervalProjectiveExteriorLength₃_eq_coordinate x).symm

/-- The actual triple plane determinant projective norm, separated by its scalar coordinate. -/
def intervalExteriorPlaneTripleProjectiveNorm :
    AddGroupNorm (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  ⟨PiTensorProduct.projectiveSeminorm.toAddGroupSeminorm,
    fun z hz => (projectiveSeminorm_eq_zero_iff z).mp hz⟩

/-- The actual double three-space determinant projective norm, separated by
its scalar coordinate. -/
def intervalExteriorThreeDoubleProjectiveNorm :
    AddGroupNorm (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  ⟨PiTensorProduct.projectiveSeminorm.toAddGroupSeminorm,
    fun z hz => (projectiveSeminorm_eq_zero_iff z).mp hz⟩

local instance intervalInputPlaneTripleNormed :
    NormedAddCommGroup (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  intervalExteriorPlaneTripleProjectiveNorm.toNormedAddCommGroup

local instance intervalInputPlaneTripleSeminormed :
    SeminormedAddCommGroup (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  intervalExteriorPlaneTripleProjectiveNorm.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalInputPlaneTripleSpace :
    NormedSpace ℝ (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) :=
  ⟨fun a z => by
    change PiTensorProduct.projectiveSeminorm (a • z) ≤
      ‖a‖ * PiTensorProduct.projectiveSeminorm z
    exact (map_smul_eq_mul PiTensorProduct.projectiveSeminorm a z).le⟩

local instance intervalInputThreeDoubleNormed :
    NormedAddCommGroup (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  intervalExteriorThreeDoubleProjectiveNorm.toNormedAddCommGroup

local instance intervalInputThreeDoubleSeminormed :
    SeminormedAddCommGroup (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  intervalExteriorThreeDoubleProjectiveNorm.toNormedAddCommGroup.toSeminormedAddCommGroup

local instance intervalInputThreeDoubleSpace :
    NormedSpace ℝ (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  ⟨fun a z => by
    change PiTensorProduct.projectiveSeminorm (a • z) ≤
      ‖a‖ * PiTensorProduct.projectiveSeminorm z
    exact (map_smul_eq_mul PiTensorProduct.projectiveSeminorm a z).le⟩

/-- The powered determinant lines forming the two factors of the interval tensor input. -/
abbrev IntervalDeterminantInputFactors : Unit ⊕ Unit → Type
  | .inl _ => ⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)
  | .inr _ => ⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)

local instance intervalDeterminantInputFactorsNormed (i : Unit ⊕ Unit) :
    NormedAddCommGroup (IntervalDeterminantInputFactors i) := by
  cases i <;> exact inferInstance

local instance intervalDeterminantInputFactorsSpace (i : Unit ⊕ Unit) :
    NormedSpace ℝ (IntervalDeterminantInputFactors i) := by
  cases i <;> exact inferInstance

private def intervalDeterminantInputFactorCoordinate :
    ∀ i, IntervalDeterminantInputFactors i ≃ₗ[ℝ] ℝ
  | .inl _ => determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 2)) 3
  | .inr _ => determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 3)) 2

/-- The canonical scalar coordinate on the ordinary powered determinant tensor domain. -/
def intervalDeterminantTensorInputCoordinate :
    ((⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) ≃ₗ[ℝ] ℝ :=
  (TensorProduct.congr (determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 2)) 3)
    (determinantPowerCoordinateEquiv (Pi.basisFun ℝ (Fin 3)) 2)).trans
    (TensorProduct.lid ℝ ℝ)

/-- The genuine ordinary binary projective seminorm of the actual determinant
tensor powers, whose factors carry their actual projective norms. -/
def intervalDeterminantTensorInputSeminorm :
    Seminorm ℝ ((⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) :=
  (PiTensorProduct.projectiveSeminorm (𝕜 := ℝ) (E := IntervalDeterminantInputFactors)).comp
    (binaryTensorEquiv ℝ IntervalDeterminantInputFactors).symm.toLinearMap

/-- The genuine input projective seminorm equals its canonical scalar-coordinate
norm on every actual vector; it is not a coordinate-defined replacement. -/
theorem intervalDeterminantTensorInputSeminorm_eq_coordinate
    (z : (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) :
    intervalDeterminantTensorInputSeminorm z = ‖intervalDeterminantTensorInputCoordinate z‖ := by
  let f := (PiTensorProduct.congr intervalDeterminantInputFactorCoordinate).trans
    (PiTensorProduct.constantBaseRingEquiv (Unit ⊕ Unit) ℝ).toLinearEquiv
  have hf : f.toLinearMap = intervalDeterminantTensorInputCoordinate.toLinearMap.comp
      (binaryTensorEquiv ℝ IntervalDeterminantInputFactors).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, f, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      AlgEquiv.toLinearEquiv_apply, PiTensorProduct.constantBaseRingEquiv_tprod,
      Fintype.prod_sum_type, Fintype.prod_unique, binaryTensorEquiv_tprod,
      intervalDeterminantTensorInputCoordinate, TensorProduct.congr_tmul,
      TensorProduct.lid_tmul, intervalDeterminantInputFactorCoordinate, smul_eq_mul]
  have h := projectiveSeminorm_eq_norm_scalarCoordinate
    intervalDeterminantInputFactorCoordinate (fun i => by
      cases i with
      | inl _ =>
        intro x
        exact (intervalExteriorPlaneTriple_projective_eq_coordinate x).symm
      | inr _ =>
        intro x
        exact (intervalExteriorThreeDouble_projective_eq_coordinate x).symm)
    ((binaryTensorEquiv ℝ IntervalDeterminantInputFactors).symm z)
  change PiTensorProduct.projectiveSeminorm
    ((binaryTensorEquiv ℝ IntervalDeterminantInputFactors).symm z) = ‖f
      ((binaryTensorEquiv ℝ IntervalDeterminantInputFactors).symm z)‖ at h
  have hc := DFunLike.congr_fun hf
    ((binaryTensorEquiv ℝ IntervalDeterminantInputFactors).symm z)
  simp only [LinearEquiv.coe_coe, LinearMap.comp_apply, LinearEquiv.apply_symm_apply] at hc
  rw [hc] at h
  exact h

/-- The genuine binary determinant input seminorm separates zero. -/
theorem intervalDeterminantTensorInputSeminorm_eq_zero_iff
    (z : (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) :
    intervalDeterminantTensorInputSeminorm z = 0 ↔ z = 0 := by
  rw [intervalDeterminantTensorInputSeminorm_eq_coordinate, norm_eq_zero,
    LinearEquiv.map_eq_zero_iff]

/-- The genuine ordinary projective norm on the actual powered determinant tensor. -/
def intervalDeterminantTensorInputNorm :
    AddGroupNorm ((⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) :=
  ⟨intervalDeterminantTensorInputSeminorm.toAddGroupSeminorm,
    fun z hz => (intervalDeterminantTensorInputSeminorm_eq_zero_iff z).mp hz⟩

/-- The separating input norm is the genuine binary projective seminorm on every vector. -/
theorem intervalDeterminantTensorInputNorm_apply
    (z : (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ))) :
    intervalDeterminantTensorInputNorm z = intervalDeterminantTensorInputSeminorm z := rfl

/-- The standard generator in the actual canonical determinant tensor domain. -/
def intervalDeterminantTensorInputGenerator :
    (⨂[ℝ] (_ : Fin 3), ⋀[ℝ]^2 (Fin 2 → ℝ)) ⊗[ℝ]
      (⨂[ℝ] (_ : Fin 2), ⋀[ℝ]^3 (Fin 3 → ℝ)) :=
  (⨂ₜ[ℝ] (_ : Fin 3), exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2))) ⊗ₜ[ℝ]
    (⨂ₜ[ℝ] (_ : Fin 2), exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3)))

/-- Its genuine projective input norm is exactly one. -/
theorem intervalDeterminantTensorInputNorm_generator :
    intervalDeterminantTensorInputNorm intervalDeterminantTensorInputGenerator = 1 := by
  change intervalDeterminantTensorInputSeminorm intervalDeterminantTensorInputGenerator = 1
  rw [intervalDeterminantTensorInputSeminorm_eq_coordinate]
  simp only [intervalDeterminantTensorInputCoordinate, intervalDeterminantTensorInputGenerator,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    determinantPowerCoordinateEquiv_tprod, determinantCoordinateEquiv_ιMulti,
    Basis.det_self, Finset.prod_const_one, smul_eq_mul, mul_one, norm_one]

/-- Its actual canonical representation image has exterior quotient cost at most one half. -/
theorem intervalDeterminantTensorInputGenerator_image_le_half :
    intervalTensorProjectiveExteriorLength
      (determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3))
        intervalDeterminantTensorInputGenerator) ≤ 1 / 2 :=
  intervalTensorProjectiveExteriorLength_determinantTensorEquiv_le_half

/-- The actual canonical determinant representation strictly decreases the
genuine input norm of this standard generator. -/
theorem intervalDeterminantTensorInputGenerator_image_lt_norm :
    intervalTensorProjectiveExteriorLength
      (determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3))
        intervalDeterminantTensorInputGenerator) <
      intervalDeterminantTensorInputNorm intervalDeterminantTensorInputGenerator := by
  rw [intervalDeterminantTensorInputNorm_generator]
  exact lt_of_le_of_lt intervalDeterminantTensorInputGenerator_image_le_half (by norm_num)

/-- The source local determinant representation cannot preserve the genuine
projective input norm and actual projective exterior quotient length on every vector. -/
theorem intervalDeterminantTensor_not_preserves_projective_length :
    ¬ ∀ z, intervalTensorProjectiveExteriorLength
      (determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3)) z) =
        intervalDeterminantTensorInputNorm z := by
  intro h
  exact (ne_of_lt intervalDeterminantTensorInputGenerator_image_lt_norm)
    (h intervalDeterminantTensorInputGenerator)

/-- In the source orientation, the inverse canonical determinant
representation also fails to preserve the two actual projective lengths. -/
theorem intervalDeterminantTensor_inverse_not_preserves_projective_length :
    ¬ ∀ η, intervalDeterminantTensorInputNorm
      ((determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3))).symm η) =
        intervalTensorProjectiveExteriorLength η := by
  intro h
  apply intervalDeterminantTensor_not_preserves_projective_length
  intro z
  have hz := h
    (determinantTensorEquivOfBases (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 3)) z)
  rw [LinearEquiv.symm_apply_apply] at hz
  exact hz.symm

end

end ArakelovGeometry
