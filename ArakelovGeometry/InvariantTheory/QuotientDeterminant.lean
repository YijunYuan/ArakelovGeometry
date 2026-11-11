/-
Copyright (c) 2026 ArakelovGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArakelovGeometry contributors
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Exterior.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.Determinant.DualBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Dual.Map
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# The determinant quotient and its dual Plücker vector

The maps here use the canonical exterior-power pairing and tensor-to-exterior
surjection already present in the project.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open scoped TensorProduct

variable {k W Q : Type*} [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup Q] [Module k Q]

/-- The canonical tensor quotient inducing the determinant projective point when
`r = finrank k Q`. -/
def quotientExterior (r : ℕ) (q : W →ₗ[k] Q) :
    (⨂[k]^r W) →ₗ[k] (⋀[k]^r Q) :=
  (exteriorPower.map r q).comp (tensorToExterior k W r)

@[simp]
theorem quotientExterior_tprod (r : ℕ) (q : W →ₗ[k] Q) (x : Fin r → W) :
    quotientExterior r q (⨂ₜ[k] i, x i) = exteriorPower.ιMulti k r (fun i ↦ q (x i)) := by
  simp [quotientExterior, Function.comp_def]

/-- A surjection induces the actual surjective tensor-to-exterior quotient. -/
theorem quotientExterior_surjective (r : ℕ) (q : W →ₗ[k] Q)
    (hq : Function.Surjective q) : Function.Surjective (quotientExterior r q) :=
  (exteriorPower.map_surjective hq).comp (tensorToExterior_surjective k W r)

/-- The actual tensor-to-determinant quotient commutes with scalar extension. -/
theorem quotientExterior_baseChange (L : Type*) [Field L] [Algebra k L]
    (r : ℕ) (q : W →ₗ[k] Q) (z : L ⊗[k] (⨂[k]^r W)) :
    exteriorBaseChangeEquiv k L Q r ((quotientExterior r q).baseChange L z) =
      quotientExterior r (q.baseChange L)
        (tensorBaseChangeEquiv k L (fun _ : Fin r ↦ W) z) := by
  simp only [quotientExterior, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [exteriorBaseChangeEquiv_map, exteriorBaseChangeEquiv_tensorToExterior]

/-- The canonical map of dual exterior vectors into tensor covectors. -/
def exteriorCovector (r : ℕ) :
    (⋀[k]^r (Module.Dual k W)) →ₗ[k] Module.Dual k (⨂[k]^r W) :=
  (tensorToExterior k W r).dualMap.comp (exteriorPower.pairingDual k W r)

@[simp]
theorem exteriorCovector_ιMulti_tprod (r : ℕ) (f : Fin r → Module.Dual k W)
    (x : Fin r → W) :
    exteriorCovector r (exteriorPower.ιMulti k r f) (⨂ₜ[k] i, x i) =
      Matrix.det (Matrix.of fun i j ↦ f j (x i)) := by
  simp [exteriorCovector]

/-- Exterior duality is natural for every linear map, including quotient maps. -/
theorem pairingDual_map_dualMap (r : ℕ) (q : W →ₗ[k] Q) :
    (exteriorPower.pairingDual k W r).comp (exteriorPower.map r q.dualMap) =
      (exteriorPower.map r q).dualMap.comp (exteriorPower.pairingDual k Q r) := by
  apply exteriorPower.linearMap_ext
  ext f x
  simp

/-- The Plücker covector of the dual quotient is exactly the dual of the
tensor-to-determinant quotient, with no sign or factorial factor. -/
theorem exteriorCovector_map_dualMap (r : ℕ) (q : W →ₗ[k] Q)
    (z : ⋀[k]^r (Module.Dual k Q)) :
    exteriorCovector r (exteriorPower.map r q.dualMap z) =
      (quotientExterior r q).dualMap (exteriorPower.pairingDual k Q r z) := by
  have h := congrArg (fun f : (⋀[k]^r (Module.Dual k Q)) →ₗ[k]
      Module.Dual k (⋀[k]^r W) ↦ f z) (pairingDual_map_dualMap r q)
  change (tensorToExterior k W r).dualMap
      (exteriorPower.pairingDual k W r (exteriorPower.map r q.dualMap z)) = _
  rw [show exteriorPower.pairingDual k W r (exteriorPower.map r q.dualMap z) =
      (exteriorPower.map r q).dualMap (exteriorPower.pairingDual k Q r z) from h]
  rfl

/-- Exterior-to-tensor covectors commute with the canonical scalar-extension
maps on exterior powers, tensors and duals, on all vectors. -/
theorem exteriorCovector_baseChange [FiniteDimensional k W]
    (L : Type*) [Field L] [Algebra k L] (r : ℕ)
    (z : L ⊗[k] (⋀[k]^r (Module.Dual k W))) (x : L ⊗[k] (⨂[k]^r W)) :
    dualBaseChangeEquiv k L (⨂[k]^r W) ((exteriorCovector r).baseChange L z) x =
      exteriorCovector r
        (exteriorPower.map r (dualBaseChangeEquiv k L W).toLinearMap
          (exteriorBaseChangeEquiv k L (Module.Dual k W) r z))
        (tensorBaseChangeEquiv k L (fun _ : Fin r ↦ W) x) := by
  simp only [exteriorCovector, LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [dualBaseChangeEquiv_dualMap]
  change dualBaseChangeEquiv k L (⋀[k]^r W)
      ((exteriorPower.pairingDual k W r).baseChange L z)
      ((tensorToExterior k W r).baseChange L x) = _
  rw [exteriorPairingDual_baseChange, exteriorBaseChangeEquiv_tensorToExterior]
  rfl

/-- In top degree the target of the quotient has dimension one. -/
theorem finrank_topExterior [FiniteDimensional k Q] :
    Module.finrank k (⋀[k]^(Module.finrank k Q) Q) = 1 := by
  simp

/-- Alternating a tensor and projecting to the exterior power multiplies by `r!`. -/
theorem tensorToExterior_toTensorPower (r : ℕ) :
    (tensorToExterior k W r).comp (exteriorPower.toTensorPower k W r) =
      (r.factorial : k) • LinearMap.id := by
  apply exteriorPower.linearMap_ext
  have h : (tensorToExterior k W r).compMultilinearMap (PiTensorProduct.tprod k) =
      (exteriorPower.ιMulti k r).toMultilinearMap := by
    apply MultilinearMap.ext
    intro x
    exact tensorToExterior_tprod k W r x
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.toTensorPower, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [← LinearMap.compAlternatingMap_apply,
    ← LinearMap.compMultilinearMap_alternatization, h, AlternatingMap.coe_alternatization]
  simp [Nat.cast_smul_eq_nsmul]

/-- The alternating tensor inclusion is natural for all linear maps. -/
theorem toTensorPower_map (r : ℕ) (f : W →ₗ[k] Q) :
    (exteriorPower.toTensorPower k Q r).comp (exteriorPower.map r f) =
      (PiTensorProduct.map fun _ : Fin r ↦ f).comp (exteriorPower.toTensorPower k W r) := by
  apply exteriorPower.linearMap_ext
  ext x
  simp [Function.comp_def]

/-- Exterior covectors embed into tensor covectors in finite dimension. -/
theorem exteriorCovector_injective [FiniteDimensional k W] (r : ℕ) :
    Function.Injective (exteriorCovector (k := k) (W := W) r) := by
  intro z w h
  apply (exteriorPower.bijective_pairingDual k W r).injective
  apply LinearMap.ext
  intro t
  obtain ⟨x, rfl⟩ := tensorToExterior_surjective k W r t
  exact congrArg (fun f : Module.Dual k (⨂[k]^r W) ↦ f x) h

/-- A nonzero dual determinant vector gives a nonzero tensor covector for a quotient. -/
theorem exteriorCovector_map_dualMap_ne_zero [FiniteDimensional k Q] (r : ℕ)
    (q : W →ₗ[k] Q) (hq : Function.Surjective q)
    {z : ⋀[k]^r (Module.Dual k Q)} (hz : z ≠ 0) :
    exteriorCovector r (exteriorPower.map r q.dualMap z) ≠ 0 := by
  intro h
  apply hz
  apply (exteriorPower.bijective_pairingDual k Q r).injective
  simp only [map_zero]
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := quotientExterior_surjective r q hq x
  have ht := congrArg (fun f : Module.Dual k (⨂[k]^r W) ↦ f t)
    (exteriorCovector_map_dualMap r q z)
  rw [h] at ht
  exact ht.symm

/-- The canonical alternating section of the tensor-to-exterior quotient. -/
def exteriorTensorSection [CharZero k] (r : ℕ) :
    (⋀[k]^r W) →ₗ[k] (⨂[k]^r W) :=
  (r.factorial : k)⁻¹ • exteriorPower.toTensorPower k W r

/-- In characteristic zero the normalized alternating sum is a section. -/
theorem tensorToExterior_section [CharZero k] (r : ℕ) (x : ⋀[k]^r W) :
    tensorToExterior k W r (exteriorTensorSection r x) = x := by
  have h := congrArg (fun f : (⋀[k]^r W) →ₗ[k] (⋀[k]^r W) ↦ f x)
    (tensorToExterior_toTensorPower (k := k) (W := W) r)
  change tensorToExterior k W r (exteriorPower.toTensorPower k W r x) =
    (r.factorial : k) • x at h
  simp only [exteriorTensorSection, LinearMap.smul_apply, map_smul, h, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)), one_smul]

/-- The normalized section commutes with every linear map. -/
theorem exteriorTensorSection_map [CharZero k] (r : ℕ) (f : W →ₗ[k] Q)
    (x : ⋀[k]^r W) :
    exteriorTensorSection r (exteriorPower.map r f x) =
      PiTensorProduct.map (fun _ : Fin r ↦ f) (exteriorTensorSection r x) := by
  have h := congrArg (fun g : (⋀[k]^r W) →ₗ[k] (⨂[k]^r Q) ↦ g x)
    (toTensorPower_map r f)
  simpa only [exteriorTensorSection, LinearMap.smul_apply, map_smul, LinearMap.comp_apply] using
    congrArg (fun z : ⨂[k]^r Q ↦ (r.factorial : k)⁻¹ • z) h

end ArakelovGeometry.InvariantTheory
