/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Plucker
public import ArakelovGeometry.LinearAlgebra.Valuation.CartanDecomposition
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue weights for the tensor covector action

The contragredient action uses the inverse group element, so a nonzero residue
coordinate has negative original tensor weight when its transformed coordinate
lies in the maximal-ideal lattice. Integral evaluations are transported through
both outer factors of a Cartan decomposition.

The resulting statements concern binary tensor covectors and quotient
determinants. They do not assert the general Hilbert–Mumford equivalence in
[ChenMoriwaki2020]. Neither a coefficient field nor completeness of the discrete
valuation ring is assumed.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

namespace ArakelovGeometry.DVRCartan

variable {R L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- A nonpositive transformed weight forces zero residue over a
discrete valuation ring. -/
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

/-- Tensor products of eigenvectors have eigenweight equal to the sum
of their integer weights. -/
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

/-- Contragredient evaluation negates the eigenweight, following the
inverse-parameter convention of [ChenMoriwaki2020], Example 5.2.6. -/
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

/-- Evaluation of a transformed quotient determinant equals the
determinant of the quotient images transformed by the inverse group element. -/
theorem tensorPower_dual_quotientDeterminant_eval (ρ : Representation L G W)
    (r : ℕ) (g : G) {Q : Type*} [AddCommGroup Q] [Module L Q]
    (q : W →ₗ[L] Q) (b : Module.Basis (Fin r) L Q) (x : Fin r → W) :
    (tensorPowerRepresentation r ρ).dual g
      (exteriorCovector r (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord)))
      (⨂ₜ[L] i, x i) =
    Matrix.det (Matrix.of fun i j ↦ b.coord j (q (ρ g⁻¹ (x i)))) := by
  change exteriorCovector r
    (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord))
      (PiTensorProduct.map (fun _ : Fin r ↦ ρ g⁻¹) (⨂ₜ[L] i, x i)) = _
  simp

section Binary

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (E : Bool → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module L (E j)]

/-- The binary special-linear tensor action has eigenweight equal
to the sum of the two factor eigenweights. -/
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

/-- A binary tensor-power covector coordinate with nonzero residue has
strictly negative original weight if its transformed coordinate lies in the
maximal-ideal lattice. The sign follows the contragredient convention of
[ChenMoriwaki2020], Example 5.2.6. -/
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

/-- The residue weight criterion for the dual determinant vector of
a binary tensor quotient. Its coordinate is the determinant of the displayed
quotient images, with no factorial factor. -/
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

section IntegralTransport

open Matrix

variable {R : Type*} [CommRing R] [Algebra R L]
variable {ι : Bool → Type*} [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]

/-- The canonical identification of matrix and module special-linear
actions commutes with inclusion of integral vectors. -/
theorem integralSL_apply {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix.SpecialLinearGroup n R) (x : n → R) :
    (Matrix.SpecialLinearGroup.toLin'_equiv
      (Matrix.SpecialLinearGroup.map (algebraMap R L) P)).val
        (fun i ↦ algebraMap R L (x i)) =
      fun i ↦ algebraMap R L (((P : Matrix n n R) *ᵥ x) i) := by
  ext i
  exact ((algebraMap R L).map_mulVec (P : Matrix n n R) x i).symm

/-- Integral special-linear changes preserve tensor-power covector
evaluations in any ideal lattice. The hypothesis concerns evaluations on all
integral pure tensors. -/
theorem binary_tensorPower_dual_preserves_integral_evaluations
    (r : ℕ) (P : ∀ j, Matrix.SpecialLinearGroup (ι j) R) (I : Ideal R)
    (f : Module.Dual L (⨂[L]^r (⨂[L] j, (ι j → L))))
    (hf : ∀ x : Fin r → ∀ j, ι j → R, ∃ c ∈ I,
      f (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ algebraMap R L (x i j k))) = algebraMap R L c)
    (x : Fin r → ∀ j, ι j → R) :
    ∃ c ∈ I,
      (tensorPowerRepresentation r (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
          (Matrix.SpecialLinearGroup.map (algebraMap R L) (P j))) f
        (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ algebraMap R L (x i j k))) = algebraMap R L c := by
  obtain ⟨c, hc, heq⟩ := hf (fun i j ↦ ((P j)⁻¹ : Matrix.SpecialLinearGroup (ι j) R) *ᵥ x i j)
  refine ⟨c, hc, ?_⟩
  change f (PiTensorProduct.map (fun _ : Fin r ↦
    (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))
      ((fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
        (Matrix.SpecialLinearGroup.map (algebraMap R L) (P j)))⁻¹)) _) = _
  rw [PiTensorProduct.map_tprod]
  change f (⨂ₜ[L] i, PiTensorProduct.map
    (fun j ↦ ((Matrix.SpecialLinearGroup.toLin'_equiv
      (Matrix.SpecialLinearGroup.map (algebraMap R L) (P j)))⁻¹).val.toLinearMap)
      (⨂ₜ[L] j, fun k ↦ algebraMap R L (x i j k))) = _
  simp_rw [PiTensorProduct.map_tprod, LinearEquiv.coe_coe, ← map_inv,
    integralSL_apply]
  exact heq

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R L]

/-- A binary special-linear degeneration over the fraction field gives
integral special-linear changes whose reduced tensor-covector support has
negative original weights. Integrality is expressed by evaluation on every
integral pure tensor. Nonemptiness of the residue support is not asserted. -/
theorem exists_binary_cartan_negative_support {π : R} (hπ : Irreducible π)
    (r : ℕ) (g : ∀ j, Matrix.SpecialLinearGroup (ι j) L)
    (f : Module.Dual L (⨂[L]^r (⨂[L] j, (ι j → L))))
    (hf : ∀ x : Fin r → ∀ j, ι j → R, ∃ c : R,
      f (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ algebraMap R L (x i j k))) = algebraMap R L c)
    (hvan : ∀ x : Fin r → ∀ j, ι j → R, ∃ c ∈ IsLocalRing.maximalIdeal R,
      (tensorPowerRepresentation r (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv (g j)) f
        (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ algebraMap R L (x i j k))) = algebraMap R L c) :
    ∃ (Q : ∀ j, Matrix.SpecialLinearGroup (ι j) R) (a : ∀ j, ι j → ℤ),
      (∀ j, ∑ k, a j k = 0) ∧
      ∀ p : Fin r → ∀ j, ι j, ∃ c : R,
        (tensorPowerRepresentation r (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
          (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
            (Matrix.SpecialLinearGroup.map (algebraMap R L) (Q j))) f
          (⨂ₜ[L] i, (⨂ₜ[L] j, Pi.single (p i j) 1)) = algebraMap R L c ∧
        (IsLocalRing.residue R c ≠ 0 → (∑ i, ∑ j, a j (p i j)) < 0) := by
  classical
  choose P Q a ha hfact using fun j ↦
    DVRCartan.exists_specialLinear_cartan hπ (g j).toGL (g j).prop
  let φ := algebraMap R L
  have hπL : φ π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R L).ne hπ.ne_zero
  let t : Lˣ := Units.mk0 (φ π) hπL
  let D j := LaurentCartan.diagonalOneParameterSL L (a j) (ha j) t
  let pL j := Matrix.SpecialLinearGroup.toLin'_equiv (Matrix.SpecialLinearGroup.map φ (P j))
  let qL j := Matrix.SpecialLinearGroup.toLin'_equiv (Matrix.SpecialLinearGroup.map φ (Q j))
  let dL j := Matrix.SpecialLinearGroup.toLin'_equiv (D j)
  let gL j := Matrix.SpecialLinearGroup.toLin'_equiv (g j)
  let ρ := (tensorPowerRepresentation r
    (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
  have hmatrix (j) : g j = Matrix.SpecialLinearGroup.map φ (P j) * D j *
      Matrix.SpecialLinearGroup.map φ (Q j) := by
    apply Subtype.ext
    change (g j : Matrix (ι j) (ι j) L) =
      (P j : Matrix (ι j) (ι j) R).map φ *
        diagonal (fun k ↦ ((t ^ a j k : Lˣ) : L)) *
        (Q j : Matrix (ι j) (ι j) R).map φ
    simpa [t] using hfact j
  have hgroup : gL = pL * dL * qL := by
    funext j
    dsimp only [gL, pL, dL, qL, Pi.mul_apply]
    rw [hmatrix, map_mul, map_mul]
  have hcancel : ρ dL (ρ qL f) = ρ pL⁻¹ (ρ gL f) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 1
    rw [hgroup]
    group
  have hdiag (x : Fin r → ∀ j, ι j → R) : ∃ c ∈ IsLocalRing.maximalIdeal R,
      ρ dL (ρ qL f)
        (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ φ (x i j k))) = φ c := by
    rw [hcancel]
    have hinv : (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv
        (Matrix.SpecialLinearGroup.map φ ((P j)⁻¹))) = pL⁻¹ := by
      funext j
      simp [pL]
    rw [← hinv]
    exact binary_tensorPower_dual_preserves_integral_evaluations r (fun j ↦ (P j)⁻¹)
      (IsLocalRing.maximalIdeal R) (ρ gL f) hvan x
  refine ⟨Q, a, ha, ?_⟩
  intro p
  let xR : Fin r → ∀ j, ι j → R := fun i j ↦ Pi.single (p i j) 1
  have hxmap (i j) : (fun k ↦ φ (xR i j k)) = Pi.single (p i j) (1 : L) := by
    ext k
    simp [xR, Pi.single_apply, apply_ite]
  have hxt : (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ φ (xR i j k))) =
      (⨂ₜ[L] i, (⨂ₜ[L] j, Pi.single (p i j) (1 : L))) := by
    congr 1
    funext i
    congr 1
    funext j
    exact hxmap i j
  obtain ⟨c, -, hc⟩ := binary_tensorPower_dual_preserves_integral_evaluations
    r Q ⊤ f (fun x ↦ by obtain ⟨c, hc⟩ := hf x; exact ⟨c, trivial, hc⟩) xR
  change ρ qL f (⨂ₜ[L] i, (⨂ₜ[L] j, fun k ↦ φ (xR i j k))) = φ c at hc
  rw [hxt] at hc
  refine ⟨c, hc, ?_⟩
  intro hres
  refine binary_tensorPower_dual_negative_weight_of_residue_ne_zero
    (fun j ↦ ι j → L) hπ r dL (fun i j ↦ a j (p i j))
    (fun i j ↦ Pi.single (p i j) 1) ?_ (ρ qL f) c hc hres ?_
  · intro i j
    change (diagonal (fun k ↦ ((t ^ a j k : Lˣ) : L))) *ᵥ
      Pi.single (p i j) 1 = _
    ext k
    by_cases hk : k = p i j
    · subst k; simp [mulVec_diagonal, t, φ]
    · simp [mulVec_diagonal, hk]
  · obtain ⟨z, hz, hh⟩ := hdiag xR
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
    obtain ⟨h, rfl⟩ := hz
    rw [hxt] at hh
    exact ⟨h, hh⟩

/-- An exterior-dual special-linear degeneration of a binary tensor
quotient yields integral special-linear basis changes and zero-sum weights,
with negative weight sums for nonzero reduced quotient determinants.
Integrality and maximal-ideal membership are hypotheses on determinant
evaluations. This is a coordinate implication, without the full numerical
equivalence of [ChenMoriwaki2020]. -/
theorem exists_binary_quotientDeterminant_negative_support
    {π : R} (hπ : Irreducible π) (r : ℕ)
    (g : ∀ j, Matrix.SpecialLinearGroup (ι j) L)
    {V : Type*} [AddCommGroup V] [Module L V]
    (q : (⨂[L] j, (ι j → L)) →ₗ[L] V) (b : Module.Basis (Fin r) L V)
    (hq : ∀ x : Fin r → ∀ j, ι j → R, ∃ c : R,
      Matrix.det (Matrix.of fun i k ↦ b.coord k
        (q (⨂ₜ[L] j, fun l ↦ algebraMap R L (x i j l)))) = algebraMap R L c)
    (hvan : ∀ x : Fin r → ∀ j, ι j → R, ∃ c ∈ IsLocalRing.maximalIdeal R,
      exteriorCovector r
        (exteriorRepresentation r (tensorSLRepresentation (k := L) (fun j ↦ ι j → L)).dual
          (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv (g j))
          (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord)))
        (⨂ₜ[L] i, (⨂ₜ[L] j, fun l ↦ algebraMap R L (x i j l))) = algebraMap R L c) :
    ∃ (Q : ∀ j, Matrix.SpecialLinearGroup (ι j) R) (a : ∀ j, ι j → ℤ),
      (∀ j, ∑ k, a j k = 0) ∧
      ∀ p : Fin r → ∀ j, ι j, ∃ c : R,
        Matrix.det (Matrix.of fun i k ↦ b.coord k (q
          (tensorSLRepresentation (k := L) (fun j ↦ ι j → L)
            (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv
              (Matrix.SpecialLinearGroup.map (algebraMap R L) (Q j)))⁻¹)
            (⨂ₜ[L] j, Pi.single (p i j) 1)))) = algebraMap R L c ∧
        (IsLocalRing.residue R c ≠ 0 → (∑ i, ∑ j, a j (p i j)) < 0) := by
  let f := exteriorCovector r
    (exteriorPower.map r q.dualMap (exteriorPower.ιMulti L r b.coord))
  have hf : ∀ x : Fin r → ∀ j, ι j → R, ∃ c : R,
      f (⨂ₜ[L] i, (⨂ₜ[L] j, fun l ↦ algebraMap R L (x i j l))) = algebraMap R L c := by
    intro x
    simpa [f] using hq x
  have hg : ∀ x : Fin r → ∀ j, ι j → R, ∃ c ∈ IsLocalRing.maximalIdeal R,
      (tensorPowerRepresentation r (tensorSLRepresentation (k := L) (fun j ↦ ι j → L))).dual
        (fun j ↦ Matrix.SpecialLinearGroup.toLin'_equiv (g j)) f
        (⨂ₜ[L] i, (⨂ₜ[L] j, fun l ↦ algebraMap R L (x i j l))) = algebraMap R L c := by
    intro x
    simpa only [exteriorCovector_equivariant] using hvan x
  obtain ⟨Q, a, ha, hs⟩ := exists_binary_cartan_negative_support hπ r g f hf hg
  refine ⟨Q, a, ha, ?_⟩
  intro p
  obtain ⟨c, hc, hcneg⟩ := hs p
  refine ⟨c, ?_, hcneg⟩
  simpa only [f, tensorPower_dual_quotientDeterminant_eval, Pi.inv_def] using hc

end IntegralTransport

end ArakelovGeometry.InvariantTheory
