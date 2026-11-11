module

public import ArakelovGeometry.InvariantTheory.Plucker
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# The determinant quotient as an actual projective point

Polynomial semistability descends to mathlib's projectivization. The quotient
point is represented by the dual of the canonical tensor-to-determinant map.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open scoped TensorProduct

variable {k G M W Q : Type*} [Field k] [Group G]
  [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]
  [AddCommGroup Q] [Module k Q] {ι : Type*}

/-- The homogeneous invariant condition on an actual projective point. -/
def IsProjectivelySemistable (b : Module.Basis ι k M) (ρ : Representation k G M) :
    Projectivization k M → Prop :=
  Projectivization.lift (fun v ↦ IsPolynomialSemistable b ρ v.val) (by
    intro v w c h
    have hc : c ≠ 0 := by
      intro hc
      exact v.prop (by simpa [hc] using h)
    apply propext
    rw [h]
    exact isPolynomialSemistable_smul_iff b ρ w.val hc)

@[simp]
theorem isProjectivelySemistable_mk (b : Module.Basis ι k M)
    (ρ : Representation k G M) (v : M) (hv : v ≠ 0) :
    IsProjectivelySemistable b ρ (Projectivization.mk k v hv) ↔
      IsPolynomialSemistable b ρ v := Iff.rfl

/-- A surjective quotient determines a projective tensor covector from any
nonzero dual determinant generator. -/
def quotientDeterminantPoint [FiniteDimensional k Q] (q : W →ₗ[k] Q)
    (hq : Function.Surjective q)
    (η : ⋀[k]^(Module.finrank k Q) (Module.Dual k Q)) (hη : η ≠ 0) :
    Projectivization k (Module.Dual k (⨂[k]^(Module.finrank k Q) W)) :=
  Projectivization.mk k
    ((quotientExterior (Module.finrank k Q) q).dualMap
      (exteriorPower.pairingDual k Q (Module.finrank k Q) η)) (by
        rw [← exteriorCovector_map_dualMap]
        exact exteriorCovector_map_dualMap_ne_zero _ q hq hη)

/-- The determinant quotient point is independent of its nonzero generator. -/
theorem quotientDeterminantPoint_eq [FiniteDimensional k Q] (q : W →ₗ[k] Q)
    (hq : Function.Surjective q)
    (η θ : ⋀[k]^(Module.finrank k Q) (Module.Dual k Q)) (hη : η ≠ 0) (hθ : θ ≠ 0) :
    quotientDeterminantPoint q hq η hη = quotientDeterminantPoint q hq θ hθ := by
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  have hr : Module.finrank k (⋀[k]^(Module.finrank k Q) (Module.Dual k Q)) = 1 := by
    simp
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hr hθ η
  exact ⟨c, by rw [← hc, map_smul, map_smul]⟩

/-- The source quotient condition is precisely projective semistability of its
tensor-to-determinant point, for every choice of generator. -/
theorem isQuotientSemistable_iff_projective [FiniteDimensional k Q]
    [FiniteDimensional k W] [CharZero k] (ρ : Representation k G W)
    (q : W →ₗ[k] Q) (hq : Function.Surjective q)
    (η : ⋀[k]^(Module.finrank k Q) (Module.Dual k Q)) (hη : η ≠ 0) :
    IsQuotientSemistable ρ q ↔
      IsProjectivelySemistable (Module.Free.chooseBasis k _)
        ((tensorPowerRepresentation (Module.finrank k Q) ρ).dual)
        (quotientDeterminantPoint q hq η hη) := by
  rw [isQuotientSemistable_iff_tensor]
  constructor
  · rintro ⟨θ, hθ, hs⟩
    change IsProjectivelySemistable _ _ (quotientDeterminantPoint q hq θ hθ) at hs
    rwa [quotientDeterminantPoint_eq q hq θ η hθ hη] at hs
  · exact fun hs ↦ ⟨η, hη, hs⟩

end ArakelovGeometry.InvariantTheory
