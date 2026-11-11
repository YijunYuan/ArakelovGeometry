module

public import ArakelovGeometry.AdelicVectorBundle.Exterior.BaseChange

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

/-- In top degree the target of the quotient has dimension one. -/
theorem finrank_topExterior [FiniteDimensional k Q] :
    Module.finrank k (⋀[k]^(Module.finrank k Q) Q) = 1 := by
  simp

end ArakelovGeometry.InvariantTheory
