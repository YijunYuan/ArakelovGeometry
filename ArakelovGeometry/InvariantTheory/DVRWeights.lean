/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Valuation.CartanDecomposition
public import ArakelovGeometry.InvariantTheory.Plucker
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue weights for the actual tensor covector action

This is the coordinate step in the binary instability direction used by Bost p31.
The general CM Hilbert–Mumford equivalence is not asserted. We retain actual
A2 tensor-power and dual actions: the dual uses the inverse group element, so a
nonzero residue coordinate has a negative original tensor weight sum.
The remaining bridges are the actual orbit parameter map over the ground field,
transport of the integral lattice through the two Cartan outer factors in A2,
and descent from the arbitrary DVR residue field. No coefficient field or
completion is assumed.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

namespace ArakelovGeometry.DVRCartan

variable {R L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- General-DVR replacement for the Laurent constant-coefficient argument:
a nonpositive transformed weight forces zero residue. This is the exact scalar
input for Bost p31; the A2 integral lattice, orbit and residue-descent bridges remain. -/
theorem residue_eq_zero_of_nonpositive_weight {π : R} (hπ : Irreducible π)
    (a : ℤ) (ha : a ≤ 0) (c h : R)
    (heq : (algebraMap R L π) ^ a * algebraMap R L c =
      algebraMap R L (π * h)) : IsLocalRing.residue R c = 0 := by
  let φ := algebraMap R L
  have hx : φ π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr ha)
  have he : a = -(m : ℤ) := by omega
  have hc : c = π * (π ^ m * h) := by
    apply IsFractionRing.injective R L
    have hh := congrArg (fun z : L ↦ (φ π) ^ m * z) heq
    rw [he] at hh
    simpa [φ, zpow_neg, zpow_natCast, ← mul_assoc, hx, mul_comm, mul_left_comm] using hh
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  exact ⟨π ^ m * h, hc⟩

end ArakelovGeometry.DVRCartan

namespace ArakelovGeometry.InvariantTheory

variable {L G W : Type*} [Field L] [Group G] [AddCommGroup W] [Module L W]

/-- In the actual A2 tensor-power representation, eigenvectors tensor with the
sum of their integer weights. This retains the elementary representation identity
needed for binary Bost p31; integral Cartan transport and geometric/descent bridges remain. -/
theorem tensorPowerRepresentation_tprod_eigenvectors (ρ : Representation L G W)
    (r : ℕ) (g : G) (t : L) (ht : t ≠ 0) (a : Fin r → ℤ) (x : Fin r → W)
    (hx : ∀ i, ρ g (x i) = t ^ a i • x i) :
    tensorPowerRepresentation r ρ g (⨂ₜ[L] i, x i) =
      t ^ (∑ i, a i) • (⨂ₜ[L] i, x i) := by
  change PiTensorProduct.map (fun _ : Fin r ↦ ρ g) _ = _
  rw [PiTensorProduct.map_tprod]
  simp_rw [hx]
  rw [(PiTensorProduct.tprod L).map_smul_univ]
  congr 1
  have hs (s : Finset (Fin r)) : (∏ i ∈ s, t ^ a i) = t ^ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add₀ ht]
  exact hs Finset.univ

/-- Actual contragredient evaluation has the negative eigenweight. This is the
inverse-parameter convention required by the quotient formula in CM Example 5.2.6
and Bost p31. It proves evaluation on vectors; integral and geometric bridges remain. -/
theorem dual_apply_of_eigenvector (ρ : Representation L G W) (g : G)
    (t : L) (ht : t ≠ 0) (a : ℤ) (x : W) (hx : ρ g x = t ^ a • x)
    (f : Module.Dual L W) : ρ.dual g f x = t ^ (-a) * f x := by
  have hinv : ρ g⁻¹ x = t ^ (-a) • x := by
    have h := congrArg (ρ g⁻¹) hx
    have hleft : ρ g⁻¹ (ρ g x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hleft, map_smul] at h
    calc
      ρ g⁻¹ x = t ^ (-a) • (t ^ a • ρ g⁻¹ x) := by
        rw [smul_smul, ← zpow_add₀ ht]
        simp
      _ = t ^ (-a) • x := congrArg (fun z ↦ t ^ (-a) • z) h.symm
  change f (ρ g⁻¹ x) = _
  rw [hinv, map_smul, smul_eq_mul]

section Binary

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (E : Bool → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module L (E j)]

/-- The actual binary A2 SL action has the sum of the two factor eigenweights.
This is the tensor part of Bost p31; no geometric instability equivalence or
residue-field descent is asserted. The integral Cartan transport remains downstream. -/
theorem tensorSLRepresentation_binary_eigenvectors
    (g : ∀ j, SpecialLinearGroup L (E j)) (t : L) (ht : t ≠ 0)
    (a : Bool → ℤ) (x : ∀ j, E j) (hx : ∀ j, (g j).val (x j) = t ^ a j • x j) :
    tensorSLRepresentation E g (⨂ₜ[L] j, x j) =
      t ^ (∑ j, a j) • (⨂ₜ[L] j, x j) := by
  change PiTensorProduct.map (fun j ↦ (g j).val.toLinearMap) _ = _
  rw [PiTensorProduct.map_tprod]
  simp_rw [LinearEquiv.coe_coe, hx]
  rw [(PiTensorProduct.tprod L).map_smul_univ]
  congr 1
  simp [zpow_add₀ ht]

/-- For actual A2 binary tensor-power covectors, a coordinate with nonzero DVR
residue has a strictly negative original tensor weight sum when its transformed
coordinate is in the maximal-ideal lattice. This retains only the diagonal
coordinate step needed by Bost p31, with the inverse-parameter sign of CM 5.2.6.
The hypothesis concerns evaluation of the actual contragredient action, not a
numerical certificate. Transport through the Cartan outer factors, the orbit map
and descent to the ground field are still required. -/
theorem binary_tensorPower_dual_negative_weight_of_residue_ne_zero
    {π : R} (hπ : Irreducible π) (r : ℕ)
    (g : ∀ j, SpecialLinearGroup L (E j))
    (a : Fin r → Bool → ℤ) (x : Fin r → ∀ j, E j)
    (hx : ∀ i j, (g j).val (x i j) = (algebraMap R L π) ^ a i j • x i j)
    (f : Module.Dual L (⨂[L]^r (⨂[L] j, E j))) (c : R)
    (hc : f (⨂ₜ[L] i, (⨂ₜ[L] j, x i j)) = algebraMap R L c)
    (hres : IsLocalRing.residue R c ≠ 0)
    (hvan : ∃ h : R,
      (tensorPowerRepresentation r (tensorSLRepresentation E)).dual g f
        (⨂ₜ[L] i, (⨂ₜ[L] j, x i j)) = algebraMap R L (π * h)) :
    (∑ i, ∑ j, a i j) < 0 := by
  have hπL : algebraMap R L π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  have heigen := tensorPowerRepresentation_tprod_eigenvectors
    (tensorSLRepresentation E) r g (algebraMap R L π) hπL
    (fun i ↦ ∑ j, a i j) (fun i ↦ ⨂ₜ[L] j, x i j)
    (fun i ↦ tensorSLRepresentation_binary_eigenvectors E g
      (algebraMap R L π) hπL (a i) (x i) (hx i))
  have heval := dual_apply_of_eigenvector
    (tensorPowerRepresentation r (tensorSLRepresentation E)) g
    (algebraMap R L π) hπL (∑ i, ∑ j, a i j)
    (⨂ₜ[L] i, (⨂ₜ[L] j, x i j)) heigen f
  obtain ⟨h, hh⟩ := hvan
  rw [heval, hc] at hh
  by_contra hn
  exact hres (DVRCartan.residue_eq_zero_of_nonpositive_weight hπ
    (-(∑ i, ∑ j, a i j)) (by omega) c h hh)

/-- The preceding residue criterion applied to the actual dual determinant vector
of a binary tensor quotient: its coordinate is the determinant of the displayed
quotient images, with no factorial factor. This is the diagonal specialization
of the CM quotient criterion needed in Bost p31. The actual exterior action is
used through A2 equivariance; arbitrary Cartan transport, orbit and ground-field
descent are still unmet and are not assumed as numerical certificates. -/
theorem binary_quotientDeterminant_negative_weight_of_residue_ne_zero
    {π : R} (hπ : Irreducible π) (r : ℕ)
    (g : ∀ j, SpecialLinearGroup L (E j))
    (a : Fin r → Bool → ℤ) (x : Fin r → ∀ j, E j)
    (hx : ∀ i j, (g j).val (x i j) = (algebraMap R L π) ^ a i j • x i j)
    {Q : Type*} [AddCommGroup Q] [Module L Q]
    (q : (⨂[L] j, E j) →ₗ[L] Q) (b : Module.Basis (Fin r) L Q) (c : R)
    (hc : Matrix.det (Matrix.of fun i j ↦ b.coord j (q (⨂ₜ[L] k, x i k))) =
      algebraMap R L c)
    (hres : IsLocalRing.residue R c ≠ 0)
    (hvan : ∃ h : R,
      exteriorCovector r
        (exteriorRepresentation r (tensorSLRepresentation E).dual g
          (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord)))
        (⨂ₜ[L] i, (⨂ₜ[L] j, x i j)) = algebraMap R L (π * h)) :
    (∑ i, ∑ j, a i j) < 0 := by
  apply binary_tensorPower_dual_negative_weight_of_residue_ne_zero E hπ r g a x hx
    (exteriorCovector r
      (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord))) c
  · simpa using hc
  · exact hres
  · simpa only [exteriorCovector_equivariant] using hvan

end Binary

end ArakelovGeometry.InvariantTheory
