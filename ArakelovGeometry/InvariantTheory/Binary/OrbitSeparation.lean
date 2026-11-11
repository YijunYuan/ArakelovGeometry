/-
Copyright (c) 2026 ArakelovGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArakelovGeometry contributors
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.Orbit.Coordinates
public import ArakelovGeometry.InvariantTheory.Binary.PolynomialSemisimple
public import ArakelovGeometry.InvariantTheory.Plucker

/-!
# Actual binary tensor invariant separation

For the actual A2 dual tensor-power representation of two special-linear groups,
nonsemistability implies that every polynomial vanishing on its actual orbit
vanishes at zero. The proof uses only the concrete bounded polynomial modules,
fixed-degree tensor semisimplicity and successive lifting for commuting factors.
This is the one-way closure input for Bost p31, proof of Theorem 1.1; actual DVR
specialization, negative weights and descent are separate consumers.

The public statement accepts every finite coordinate basis. The standard tensor
basis corollary is exactly the input of `BinaryOrbitCoordinates`, and the quotient
corollary uses the actual A2 exterior determinant covector.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open MvPolynomial
open scoped TensorProduct

section HomogeneousSeparation

variable {k G M : Type*} [Field k] [Infinite k] [Group G]
  [AddCommGroup M] [Module k M] {ι : Type*} [Fintype ι]

/-- An invariant with zero constant component and nonzero value contains a
positive-degree homogeneous invariant with nonzero value. No claim of orbit
vanishing is made for the extracted component. -/
theorem isPolynomialSemistable_of_invariant_zero_constant
    (b : Module.Basis ι k M) (ρ : Representation k G M) (v : M)
    (p : MvPolynomial ι k) (hi : ∀ g, polynomialRepresentation b ρ g p = p)
    (h0 : eval 0 p = 0) (hv : eval (b.repr v) p ≠ 0) :
    IsPolynomialSemistable b ρ v := by
  classical
  have hsum := congrArg (fun q ↦ eval (b.repr v) q) (sum_homogeneousComponent p)
  simp only [map_sum] at hsum
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne hv)
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    apply hne
    simpa [homogeneousComponent_zero, ← constantCoeff_eq] using h0
  refine ⟨d, homogeneousComponent d p, Nat.pos_of_ne_zero hd0,
    homogeneousComponent_isHomogeneous d p, ?_, hne⟩
  apply (polynomialRepresentation_fixed_iff b ρ _).mp
  intro g
  rw [polynomialRepresentation_homogeneousComponent, hi]

end HomogeneousSeparation

section Binary

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
  (E : Bool → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
  {ι : Type*} [Finite ι]

omit [IsAlgClosed k] [CharZero k] [∀ j, FiniteDimensional k (E j)]
  [∀ j, Nontrivial (E j)] in
private theorem binaryFactorHom_commute
    (g : SpecialLinearGroup k (E false)) (h : SpecialLinearGroup k (E true)) :
    binaryFactorHom k E false g * binaryFactorHom k E true h =
      binaryFactorHom k E true h * binaryFactorHom k E false g := by
  funext j
  cases j <;> simp [binaryFactorHom]

omit [IsAlgClosed k] [CharZero k] [∀ j, FiniteDimensional k (E j)]
  [∀ j, Nontrivial (E j)] in
private theorem binaryFactorHom_decompose (g : ∀ j, SpecialLinearGroup k (E j)) :
    g = binaryFactorHom k E false (g false) * binaryFactorHom k E true (g true) := by
  funext j
  cases j <;> simp [binaryFactorHom]

/-- Actual one-way null-cone input for Bost p31. Absence of a positive-degree
homogeneous A2 invariant nonzero at `f` implies vanishing at zero of EVERY
polynomial vanishing on the actual binary SL orbit. Coordinates are arbitrary;
no orbit certificate, reductivity assumption or numerical instability is an input. -/
theorem binary_orbit_zero_of_not_isPolynomialSemistable (r : ℕ)
    (b : Module.Basis ι k (Module.Dual k (⨂[k]^r (⨂[k] j, E j))))
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, E j)))
    (hns : ¬ IsPolynomialSemistable b
      (tensorPowerRepresentation r (tensorSLRepresentation E)).dual f)
    (P : MvPolynomial ι k)
    (hP : ∀ g, eval (b.repr
      ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual g f)) P = 0) :
    eval 0 P = 0 := by
  classical
  let := Fintype.ofFinite ι
  by_contra h0
  let ρ := (tensorPowerRepresentation r (tensorSLRepresentation (k := k) E)).dual
  let D := P.totalDegree
  let B := restrictTotalDegree ι k D
  let τ := boundedPolynomialRepresentation b ρ D
  let τ₀ : Representation k (SpecialLinearGroup k (E false)) B :=
    τ.comp (binaryFactorHom k E false)
  let τ₁ : Representation k (SpecialLinearGroup k (E true)) B :=
    τ.comp (binaryFactorHom k E true)
  have : IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E false))) τ₀.asModule :=
    binaryBounded_factor_semisimple k E r D b false
  have : IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E true))) τ₁.asModule :=
    binaryBounded_factor_semisimple k E r D b true
  let S : Submodule k B :=
    { carrier := {p | ∀ g, eval (b.repr (ρ g f)) p.val = 0}
      zero_mem' := by simp
      add_mem' := by intro p q hp hq g; simp [hp g, hq g]
      smul_mem' := by
        intro a p hp g
        change eval (b.repr (ρ g f)) (a • p.val) = 0
        simp [smul_eq_C_mul, hp g] }
  have hstable (g) (p : B) (hp : p ∈ S) : τ g p ∈ S := by
    intro h
    change eval (b.repr (ρ h f)) (polynomialRepresentation b ρ g p.val) = 0
    rw [eval_polynomialRepresentation]
    simpa only [map_mul, Module.End.mul_apply] using hp (g⁻¹ * h)
  let e : B →ₗ[k] k := (aeval (0 : ι → k)).toLinearMap.comp B.subtype
  have he (g) (p : B) : e (τ g p) = e p := by
    change eval 0 (polynomialRepresentation b ρ g p.val) = eval 0 p.val
    simpa using eval_polynomialRepresentation b ρ g p.val 0
  have hone : ∃ p ∈ S, e p = 1 := by
    let p : B := ⟨P, (mem_restrictTotalDegree ι D P).mpr le_rfl⟩
    refine ⟨(eval 0 P)⁻¹ • p, S.smul_mem _ hP, ?_⟩
    rw [map_smul]
    exact inv_mul_cancel₀ h0
  have hc (g) (h) (p : B) : τ₀ g (τ₁ h p) = τ₁ h (τ₀ g p) := by
    change τ _ (τ _ p) = τ _ (τ _ p)
    rw [← Module.End.mul_apply, ← map_mul, binaryFactorHom_commute,
      map_mul, Module.End.mul_apply]
  obtain ⟨u, hu, hue, hu₀, hu₁⟩ := exists_joint_fixed_lift_one τ₀ τ₁ hc S
    (fun g p hp ↦ hstable _ p hp) (fun h p hp ↦ hstable _ p hp)
    e (fun g p ↦ he _ p) (fun h p ↦ he _ p) hone
  have hufix (g) : τ g u = u := by
    rw [binaryFactorHom_decompose E g, map_mul, Module.End.mul_apply]
    exact (congrArg (τ₀ (g false)) (hu₁ (g true))).trans (hu₀ (g false))
  have hufix' (g) : polynomialRepresentation b ρ g u.val = u.val :=
    congrArg Subtype.val (hufix g)
  have hV (g) : polynomialRepresentation b ρ g (1 - u.val) = 1 - u.val := by
    change polynomialPullback b b (ρ g⁻¹) (1 - u.val) = _
    rw [map_sub, map_one, ← polynomialRepresentation_apply, hufix']
  apply hns
  apply isPolynomialSemistable_of_invariant_zero_constant b ρ f (1 - u.val) hV
  · change eval 0 (1 - u.val) = 0
    change eval 0 u.val = 1 at hue
    rw [map_sub, map_one, hue, sub_self]
  · have hf : eval (b.repr f) u.val = 0 := by
      simpa only [map_one, Module.End.one_apply] using hu 1
    simp [hf]

/-- The actual nonzero quotient determinant covector satisfies orbit closure
when the A2 quotient Plücker predicate fails. Positive factor and quotient ranks
are retained for Bost p31; DVR specialization and negative weights remain separate. -/
theorem binary_quotient_determinant_orbit_closure
    {Q : Type*} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q] [Nontrivial Q]
    (q : (⨂[k] j, E j) →ₗ[k] Q) (hq : Function.Surjective q)
    (hns : ¬ IsQuotientSemistable (tensorSLRepresentation E) q)
    (η : ⋀[k]^(Module.finrank k Q) (Module.Dual k Q)) (hη : η ≠ 0)
    (b : Module.Basis ι k (Module.Dual k (⨂[k]^(Module.finrank k Q) (⨂[k] j, E j)))) :
    let f := (quotientExterior (Module.finrank k Q) q).dualMap
      (exteriorPower.pairingDual k Q (Module.finrank k Q) η)
    0 < Module.finrank k Q ∧ f ≠ 0 ∧
      ∀ P : MvPolynomial ι k,
        (∀ g, eval (b.repr ((tensorPowerRepresentation (Module.finrank k Q)
          (tensorSLRepresentation E)).dual g f)) P = 0) → eval 0 P = 0 := by
  dsimp only
  refine ⟨Module.finrank_pos, ?_, ?_⟩
  · rw [← exteriorCovector_map_dualMap]
    exact exteriorCovector_map_dualMap_ne_zero _ q hq hη
  · apply binary_orbit_zero_of_not_isPolynomialSemistable E _ b
    intro h
    apply hns
    apply (isQuotientSemistable_iff_tensor (tensorSLRepresentation E) q).mpr
    exact ⟨η, hη, (isPolynomialSemistable_basis_iff b (Module.Free.chooseBasis k _) _ _).mp h⟩

end Binary

section FinTwoTransport

variable {k : Type*} [Field k] (E : Fin 2 → Type*)
  [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]

/-- Explicit transport of the two SL factors from `Fin 2` to `Bool`. -/
def finTwoSLReindex :
    (∀ i, SpecialLinearGroup k (E i)) →*
      (∀ j : Bool, SpecialLinearGroup k (E (finTwoEquiv.symm j))) where
  toFun g j := g (finTwoEquiv.symm j)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Reindexing the binary factors is onto the actual `Bool`-indexed group. -/
theorem finTwoSLReindex_surjective : Function.Surjective (finTwoSLReindex (k := k) E) :=
  (Equiv.piCongrLeft' (fun i ↦ SpecialLinearGroup k (E i)) finTwoEquiv).surjective

/-- The explicit positive tensor-power equivalence retains the `Fin 2`/`Bool`
index bijection rather than identifying the two tensor models definitionally. -/
def finTwoTensorPowerEquiv (r : ℕ) :
    (⨂[k]^r (⨂[k] i, E i)) ≃ₗ[k]
      (⨂[k]^r (⨂[k] j : Bool, E (finTwoEquiv.symm j))) :=
  PiTensorProduct.congr fun _ : Fin r ↦ PiTensorProduct.reindex k E finTwoEquiv

/-- Reindexing commutes with the actual positive tensor-power actions. -/
theorem finTwoTensorPowerEquiv_equivariant (r : ℕ)
    (g : ∀ i, SpecialLinearGroup k (E i)) (x : ⨂[k]^r (⨂[k] i, E i)) :
    finTwoTensorPowerEquiv (k := k) E r
        (tensorPowerRepresentation r (tensorSLRepresentation E) g x) =
      tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ E (finTwoEquiv.symm j)))
        (finTwoSLReindex E g) (finTwoTensorPowerEquiv E r x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul]
    congr 1
    change PiTensorProduct.congr _ (PiTensorProduct.map _ _) =
      PiTensorProduct.map _ (PiTensorProduct.congr _ _)
    rw [PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod,
      PiTensorProduct.congr_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    exact (PiTensorProduct.map_reindex (fun j ↦ (g j).val.toLinearMap)
      finTwoEquiv (x i)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The corresponding actual covector equivalence, with the inverse only in
linear dual transport. It is separate from the polynomial inverse-pullback action. -/
def finTwoCovectorEquiv (r : ℕ) :
    Module.Dual k (⨂[k]^r (⨂[k] i, E i)) ≃ₗ[k]
      Module.Dual k (⨂[k]^r (⨂[k] j : Bool, E (finTwoEquiv.symm j))) :=
  (finTwoTensorPowerEquiv (k := k) E r).symm.dualMap

/-- The explicit covector equivalence intertwines the actual A2 dual actions. -/
theorem finTwoCovectorEquiv_equivariant (r : ℕ)
    (g : ∀ i, SpecialLinearGroup k (E i))
    (f : Module.Dual k (⨂[k]^r (⨂[k] i, E i))) :
    finTwoCovectorEquiv E r ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual g f) =
      (tensorPowerRepresentation r
        (tensorSLRepresentation (fun j ↦ E (finTwoEquiv.symm j)))).dual
        (finTwoSLReindex E g) (finTwoCovectorEquiv E r f) := by
  apply LinearMap.ext
  intro x
  change f ((tensorPowerRepresentation r (tensorSLRepresentation E)) g⁻¹
      ((finTwoTensorPowerEquiv E r).symm x)) =
    f ((finTwoTensorPowerEquiv E r).symm
      ((tensorPowerRepresentation r
        (tensorSLRepresentation (fun j ↦ E (finTwoEquiv.symm j))))
        (finTwoSLReindex E g)⁻¹ x))
  congr 1
  apply (finTwoTensorPowerEquiv E r).injective
  rw [finTwoTensorPowerEquiv_equivariant, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, map_inv]

variable [IsAlgClosed k] [CharZero k]
  [∀ i, FiniteDimensional k (E i)] [∀ i, Nontrivial (E i)]
  {ι : Type*} [Finite ι]

/-- The same actual orbit-closure implication for `Fin 2` factors, proved through
explicit tensor/covector reindexing and a surjection of the actual SL groups. -/
theorem finTwo_orbit_zero_of_not_isPolynomialSemistable (r : ℕ)
    (b : Module.Basis ι k (Module.Dual k (⨂[k]^r (⨂[k] i, E i))))
    (f : Module.Dual k (⨂[k]^r (⨂[k] i, E i)))
    (hns : ¬ IsPolynomialSemistable b
      (tensorPowerRepresentation r (tensorSLRepresentation E)).dual f)
    (P : MvPolynomial ι k)
    (hP : ∀ g, eval (b.repr
      ((tensorPowerRepresentation r (tensorSLRepresentation E)).dual g f)) P = 0) :
    eval 0 P = 0 := by
  let e := finTwoCovectorEquiv (k := k) E r
  let ρ := (tensorPowerRepresentation r (tensorSLRepresentation (k := k) E)).dual
  let τ := (tensorPowerRepresentation r
    (tensorSLRepresentation (k := k) (fun j ↦ E (finTwoEquiv.symm j)))).dual
  have he : ∀ g x, e (ρ g x) = τ (finTwoSLReindex E g) (e x) :=
    finTwoCovectorEquiv_equivariant E r
  apply binary_orbit_zero_of_not_isPolynomialSemistable
    (fun j ↦ E (finTwoEquiv.symm j)) r (b.map e) (e f)
  · intro h
    have hres : IsPolynomialSemistable (b.map e) (τ.comp (finTwoSLReindex E)) (e f) := by
      obtain ⟨d, p, hd, hp, hi, hv⟩ := h
      exact ⟨d, p, hd, hp, fun g x ↦ hi (finTwoSLReindex E g) x, hv⟩
    exact hns (hres.of_map (b.map e) b (τ.comp (finTwoSLReindex E)) ρ
      e.toLinearMap he f)
  · intro g
    obtain ⟨h, rfl⟩ := finTwoSLReindex_surjective E g
    rw [← he]
    simpa [ρ] using hP h

end FinTwoTransport

section StandardCoordinates

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
  {κ : Bool → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
  [∀ j, Nonempty (κ j)] {r : ℕ}

omit [∀ j, DecidableEq (κ j)] in
/-- The public orbit-coordinate input in the actual standard tensor basis.
The hypothesis uses A2 chooseBasis coordinates; all test polynomials in the
conclusion use the standard coordinates `f(e_p)`, not chooseBasis coordinates. -/
theorem binary_standard_orbit_zero_of_not_isPolynomialSemistable
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (κ j → k))))
    (hns : ¬ IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ κ j → k))).dual f)
    (P : MvPolynomial (BinaryTensorIndex κ r) k)
    (hP : ∀ g : ∀ j, SpecialLinearGroup k (κ j → k),
      eval (fun p ↦ (tensorPowerRepresentation r
        (tensorSLRepresentation (fun j ↦ κ j → k))).dual g f
          (binaryTensorBasis k κ r p)) P = 0) : eval 0 P = 0 := by
  classical
  apply binary_orbit_zero_of_not_isPolynomialSemistable (fun j ↦ κ j → k) r
    (binaryTensorBasis k κ r).dualBasis f
  · intro h
    exact hns ((isPolynomialSemistable_basis_iff
      (binaryTensorBasis k κ r).dualBasis (Module.Free.chooseBasis k _) _ _).mp h)
  · intro g
    have hc : ⇑((binaryTensorBasis k κ r).dualBasis.repr
        ((tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ κ j → k))).dual g f)) =
        (fun p ↦ (tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ κ j → k))).dual
          g f (binaryTensorBasis k κ r p)) :=
      funext fun p ↦ Module.Basis.dualBasis_repr _ _ p
    rw [hc]
    exact hP g

/-- Actual scheme-image closure supplied to the explicit binary orbit/DVR route.
This consumes invariant separation and the actual coordinate morphism; no
polynomial orbit-closure assumption remains. -/
theorem origin_mem_closure_specOrbit_of_not_isPolynomialSemistable
    (f : Module.Dual k (⨂[k]^r (⨂[k] j, (κ j → k))))
    (hns : ¬ IsPolynomialSemistable (Module.Free.chooseBasis k _)
      (tensorPowerRepresentation r (tensorSLRepresentation (fun j ↦ κ j → k))).dual f) :
    binaryOrbitOrigin (k := k) (ι := κ) (r := r) ∈
      closure (Set.range (PrimeSpectrum.comap (binaryCovectorOrbitPullback f).toRingHom)) :=
  origin_mem_closure_specOrbit_of_actual_orbit_closure f
    (binary_standard_orbit_zero_of_not_isPolynomialSemistable f hns)

end StandardCoordinates

end ArakelovGeometry.InvariantTheory
