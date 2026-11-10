/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DeterminantHermitianBasis
public import ArakelovGeometry.AdelicVectorBundle.LineVectorDegree
public import ArakelovGeometry.Analysis.DeterminantExactSequence
public import ArakelovGeometry.NumberTheory.NonpureNumberFieldMinkowskiObstruction

/-! # Actual local determinants of the nonpure rational plane -/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
open AdelicStructure NormFamily
open MeasureTheory

/-- The actual shearing coordinate isomorphism has determinant one. -/
def shearEquiv (a : ℤ) : Plane ≃ₗ[ℚ] Plane where
  toFun x := ![x 0, x 1 - (a : ℚ) * x 0]
  invFun x := ![x 0, x 1 + (a : ℚ) * x 0]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp; ring

def shearBasis (a : ℤ) : Module.Basis (Fin 2) ℚ Plane :=
  standardBasis.map (shearEquiv a).symm

theorem shearBasis_zero (a : ℤ) : shearBasis a 0 = ![1, (a : ℚ)] := by
  ext i
  fin_cases i <;> simp [shearBasis, standardBasis, shearEquiv, Pi.basisFun_apply]

theorem shearBasis_one (a : ℤ) : shearBasis a 1 = ![0, 1] := by
  ext i
  fin_cases i <;> simp [shearBasis, standardBasis, shearEquiv, Pi.basisFun_apply]

theorem standardBasis_det_shearBasis (a : ℤ) : standardBasis.det (shearBasis a) = 1 := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, standardBasis, shearBasis_zero, shearBasis_one]

/-- Exact determinant volume from a genuine completed basis and computed
coordinate dual bounds. No determinant equality is supplied as a hypothesis. -/
theorem determinant_norm_completedBasis_eq_prod
    {K E : Type*} [Field K] {T : AdelicStructure K} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (ξ : NormFamily T E)
    {hT : ∀ ω ∈ T.Ωinf, IsRCLikeNormedField (T.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hT) (ω : T.Ω)
    (b : Module.Basis (Fin (Module.finrank K E)) (T.ϕ ω).Completion
      ((T.ϕ ω).Completion ⊗[K] E))
    (hb : ∀ i, ξ.dual.norm ω
      ((dualBaseChangeEquiv K (T.ϕ ω).Completion E).symm (b.coord i)) ≤
        (ξ.norm ω (b i))⁻¹) :
    ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (T.ϕ ω).Completion E _).symm
        (_root_.exteriorPower.ιMulti (T.ϕ ω).Completion _ b)) =
      ∏ i, ξ.norm ω (b i) := by
  classical
  let e := finCongr (Subspace.dual_finrank_eq (K := K) (V := E))
  let f (i : Fin (Module.finrank K (Module.Dual K E))) :=
    (dualBaseChangeEquiv K (T.ϕ ω).Completion E).symm (b.coord (e i))
  let w := (exteriorBaseChangeEquiv K (T.ϕ ω).Completion E _).symm
    (_root_.exteriorPower.ιMulti (T.ϕ ω).Completion _ b)
  let z := (exteriorBaseChangeEquiv K (T.ϕ ω).Completion (Module.Dual K E) _).symm
    (_root_.exteriorPower.ιMulti (T.ϕ ω).Completion _ f)
  have hp : completedDeterminantPairing K (T.ϕ ω).Completion E z w = 1 := by
    rw [completedDeterminantPairing_ιMulti]
    have hm : (Matrix.of fun i j => b.coord j (b i)) =
        (1 : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E))
          (T.ϕ ω).Completion) := by
      ext i j
      simp [Module.Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply]
    simp only [f, e, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      hm, Matrix.det_one]
  have hP : 0 < ∏ i, ξ.norm ω (b i) :=
    Finset.prod_pos (fun i _ => ξ.norm_pos ω (b.ne_zero i))
  have hz : ξ.dual.determinant.norm ω z ≤ (∏ i, ξ.norm ω (b i))⁻¹ := by
    refine (ξ.dual.determinant_norm_ιMulti_le ω f).trans ?_
    calc
      _ ≤ ∏ i, (ξ.norm ω (b (e i)))⁻¹ :=
        Finset.prod_le_prod₀ (fun i _ => ξ.dual.norm_nonneg ω (f i)) (fun i _ => hb (e i))
      _ = _ := by
        rw [Fintype.prod_equiv e
          (fun i => (ξ.norm ω (b (e i)))⁻¹)
          (fun i => (ξ.norm ω (b i))⁻¹) (fun _ => rfl)]
        rw [Finset.prod_inv_distrib]
  have h := hξ.norm_completedDeterminantPairing_le ξ ω z w
  rw [hp, norm_one] at h
  have hmul : 1 ≤ ξ.determinant.norm ω w * (∏ i, ξ.norm ω (b i))⁻¹ :=
    h.trans (mul_le_mul_of_nonneg_left hz (ξ.determinant.norm_nonneg ω w))
  apply le_antisymm (ξ.determinant_norm_ιMulti_le ω b)
  calc
    _ = 1 * ∏ i, ξ.norm ω (b i) := (one_mul _).symm
    _ ≤ (ξ.determinant.norm ω w * (∏ i, ξ.norm ω (b i))⁻¹) *
        ∏ i, ξ.norm ω (b i) := mul_le_mul_of_nonneg_right hmul hP.le
    _ = _ := by rw [mul_assoc, inv_mul_cancel₀ hP.ne', mul_one]

theorem shearBasis_completed_coord_zero (a : ℤ) (ω : S.Ω) :
    ((shearBasis a).baseChange (S.ϕ ω).Completion).coord 0 = firstCoordinate ω := by
  apply ((shearBasis a).baseChange (S.ϕ ω).Completion).ext
  intro i
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  fin_cases i <;>
    simp [firstCoordinate, completedCoordinates, Module.Basis.baseChange_apply,
      shearBasis_zero, shearBasis_one, standardBasis]

theorem shearBasis_completed_coord_one (a : ℤ) (ω : S.Ω) :
    ((shearBasis a).baseChange (S.ϕ ω).Completion).coord 1 = shearedCoordinate a ω := by
  apply ((shearBasis a).baseChange (S.ϕ ω).Completion).ext
  intro i
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  fin_cases i <;>
    simp [shearedCoordinate, completedCoordinates, Module.Basis.baseChange_apply,
      shearBasis_zero, shearBasis_one, standardBasis, Algebra.smul_def]

theorem family_norm_shearBasis_zero (p : Nat.Primes) (a : ℤ) :
    (family p a).norm (primePoint p)
      (((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion) 0) = 1 := by
  rw [Module.Basis.baseChange_apply, shearBasis_zero, family_norm_prime_rational]
  simp

theorem family_norm_shearBasis_one (p : Nat.Primes) (a : ℤ) :
    (family p a).norm (primePoint p)
      (((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion) 1) = Real.sqrt (p : ℝ) := by
  rw [Module.Basis.baseChange_apply, shearBasis_one, family_norm_prime_rational]
  simp [Real.sqrt_nonneg]

theorem family_dual_shearBasis_coord_bound (p : Nat.Primes) (a : ℤ) (i : Fin 2) :
    (family p a).dual.norm (primePoint p)
      ((dualBaseChangeEquiv ℚ (S.ϕ (primePoint p)).Completion Plane).symm
        (((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion).coord i)) ≤
      ((family p a).norm (primePoint p)
        (((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion) i))⁻¹ := by
  have hp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast p.property.pos)
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [family_norm_shearBasis_zero, inv_one]
    apply (family p a).dual_norm_le _ _ zero_le_one
    intro z
    rw [LinearEquiv.apply_symm_apply, shearBasis_completed_coord_zero,
      family_norm_prime, exceptionalSeminorm_apply, one_mul]
    exact le_max_left _ _
  · simp only [Fin.mk_one]
    rw [family_norm_shearBasis_one]
    apply (family p a).dual_norm_le _ _ (inv_nonneg.mpr hp.le)
    intro z
    rw [LinearEquiv.apply_symm_apply, shearBasis_completed_coord_one,
      family_norm_prime, exceptionalSeminorm_apply]
    change ‖completedCoordinates (primePoint p) z 1 -
      algebraMap ℚ (S.ϕ (primePoint p)).Completion (a : ℚ) *
        completedCoordinates (primePoint p) z 0‖ ≤ _
    calc
      _ = (Real.sqrt (p : ℝ))⁻¹ * (Real.sqrt (p : ℝ) *
          ‖completedCoordinates (primePoint p) z 1 -
            algebraMap ℚ (S.ϕ (primePoint p)).Completion (a : ℚ) *
              completedCoordinates (primePoint p) z 0‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hp.le)

theorem finrank_plane : Module.finrank ℚ Plane = 2 := by
  simp [Plane]

def rankBasis : Module.Basis (Fin (Module.finrank ℚ Plane)) ℚ Plane :=
  standardBasis.reindex (finCongr finrank_plane.symm)

def determinantVector : ⋀[ℚ]^(Module.finrank ℚ Plane) Plane :=
  _root_.exteriorPower.ιMulti ℚ _ rankBasis

theorem determinantVector_ne_zero : determinantVector ≠ 0 := by
  intro h
  have hc := congrArg (determinantCoordinateEquiv rankBasis) h
  simp only [determinantVector, determinantCoordinateEquiv_ιMulti,
    Module.Basis.det_self, map_zero] at hc
  exact one_ne_zero hc

theorem rankBasis_det_shearBasis (a : ℤ) :
    rankBasis.det ((shearBasis a).reindex (finCongr finrank_plane.symm)) = 1 := by
  rw [rankBasis, Module.Basis.det_reindex]
  have he : ((shearBasis a).reindex (finCongr finrank_plane.symm)) ∘
      finCongr finrank_plane.symm = shearBasis a := by
    funext i
    simp only [Function.comp_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rw [he, standardBasis_det_shearBasis]

theorem shearBasis_wedge_eq_determinantVector (a : ℤ) :
    _root_.exteriorPower.ιMulti ℚ (Module.finrank ℚ Plane)
      ((shearBasis a).reindex (finCongr finrank_plane.symm)) = determinantVector := by
  apply (determinantCoordinateEquiv rankBasis).injective
  rw [determinantCoordinateEquiv_ιMulti, rankBasis_det_shearBasis, determinantVector,
    determinantCoordinateEquiv_ιMulti, Module.Basis.det_self]

/-- The canonical determinant norm on the original rational generator has the
exact exceptional volume, derived from the actual primal and dual norms. -/
theorem family_determinant_norm_prime (p : Nat.Primes) (a : ℤ) :
    (family p a).determinant.norm (primePoint p)
      (1 ⊗ₜ[ℚ] determinantVector) = Real.sqrt (p : ℝ) := by
  classical
  let e : Fin 2 ≃ Fin (Module.finrank ℚ Plane) := finCongr finrank_plane.symm
  let b := ((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion).reindex e
  have hb : ∀ i, (family p a).dual.norm (primePoint p)
      ((dualBaseChangeEquiv ℚ (S.ϕ (primePoint p)).Completion Plane).symm (b.coord i)) ≤
        ((family p a).norm (primePoint p) (b i))⁻¹ := by
    intro i
    have hc : b.coord i =
        ((shearBasis a).baseChange (S.ϕ (primePoint p)).Completion).coord (e.symm i) := by
      apply LinearMap.ext
      intro z
      simp only [b, Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    rw [hc]
    simpa only [b, Module.Basis.reindex_apply] using
      family_dual_shearBasis_coord_bound p a (e.symm i)
  have hw : (exteriorBaseChangeEquiv ℚ (S.ϕ (primePoint p)).Completion Plane _).symm
      (_root_.exteriorPower.ιMulti (S.ϕ (primePoint p)).Completion _ b) =
        1 ⊗ₜ[ℚ] determinantVector := by
    have he : (b : Fin (Module.finrank ℚ Plane) → _) =
        fun i => 1 ⊗ₜ[ℚ] ((shearBasis a).reindex e) i := by
      funext i
      simp only [b, Module.Basis.reindex_apply, Module.Basis.baseChange_apply]
    rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
    exact congrArg (fun z => (1 : (S.ϕ (primePoint p)).Completion) ⊗ₜ[ℚ] z)
      (shearBasis_wedge_eq_determinantVector a)
  rw [← hw, determinant_norm_completedBasis_eq_prod (family p a)
    (family_isHermitian p a) _ b hb, ← e.prod_comp]
  simp only [b, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Fin.prod_univ_two,
    family_norm_shearBasis_zero, family_norm_shearBasis_one, one_mul]

theorem family_norm_standardBasis_off_prime (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ≠ primePoint p) (i : Fin 2) :
    (family p a).norm ω ((standardBasis.baseChange (S.ϕ ω).Completion) i) = 1 := by
  classical
  rw [family_norm_off_prime p a ω hω]
  by_cases hinf : ω ∈ S.Ωinf
  · rw [ofBasisHermitian_norm_of_infinite standardBasis ω hinf]
    fin_cases i <;> simp [Finsupp.single_apply]
  · rw [ofBasisHermitian_norm_of_finite standardBasis ω (not_not.mp hinf),
      Module.Basis.baseChange_apply, ofBasis_norm_tmul_basis]
    exact norm_one

theorem family_dual_standardBasis_coord_off_prime (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ≠ primePoint p) (i : Fin 2) :
    (family p a).dual.norm ω
      ((dualBaseChangeEquiv ℚ (S.ϕ ω).Completion Plane).symm
        ((standardBasis.baseChange (S.ϕ ω).Completion).coord i)) ≤ 1 := by
  apply (family p a).dual_norm_le _ _ zero_le_one
  intro z
  rw [LinearEquiv.apply_symm_apply, family_norm_off_prime p a ω hω, one_mul]
  change ‖(standardBasis.baseChange (S.ϕ ω).Completion).equivFun z i‖ ≤ _
  by_cases hinf : ω ∈ S.Ωinf
  · rw [ofBasisHermitian_norm_of_infinite standardBasis ω hinf]
    apply (Real.le_sqrt (_root_.norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mpr
    exact Finset.single_le_sum
      (f := fun j : Fin 2 => ‖(standardBasis.baseChange (S.ϕ ω).Completion).equivFun z j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  · rw [ofBasisHermitian_norm_of_finite standardBasis ω (not_not.mp hinf), ofBasis_norm]
    exact norm_le_pi_norm ((standardBasis.baseChange (S.ϕ ω).Completion).equivFun z) i

/-- Both ordinary finite places and infinity have determinant length one. -/
theorem family_determinant_norm_off_prime (p : Nat.Primes) (a : ℤ)
    (ω : S.Ω) (hω : ω ≠ primePoint p) :
    (family p a).determinant.norm ω (1 ⊗ₜ[ℚ] determinantVector) = 1 := by
  classical
  let e : Fin 2 ≃ Fin (Module.finrank ℚ Plane) := finCongr finrank_plane.symm
  let b := (standardBasis.baseChange (S.ϕ ω).Completion).reindex e
  have hb : ∀ i, (family p a).dual.norm ω
      ((dualBaseChangeEquiv ℚ (S.ϕ ω).Completion Plane).symm (b.coord i)) ≤
        ((family p a).norm ω (b i))⁻¹ := by
    intro i
    have hc : b.coord i =
        (standardBasis.baseChange (S.ϕ ω).Completion).coord (e.symm i) := by
      apply LinearMap.ext
      intro z
      simp only [b, Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    rw [hc]
    simpa only [b, Module.Basis.reindex_apply,
      family_norm_standardBasis_off_prime p a ω hω, inv_one] using
      family_dual_standardBasis_coord_off_prime p a ω hω (e.symm i)
  have hw : (exteriorBaseChangeEquiv ℚ (S.ϕ ω).Completion Plane _).symm
      (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b) =
        1 ⊗ₜ[ℚ] determinantVector := by
    have he : (b : Fin (Module.finrank ℚ Plane) → _) = fun i => 1 ⊗ₜ[ℚ] rankBasis i := by
      funext i
      simp only [b, rankBasis, e, Module.Basis.reindex_apply, Module.Basis.baseChange_apply]
    rw [he, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
    rfl
  rw [← hw, determinant_norm_completedBasis_eq_prod (family p a)
    (family_isHermitian p a) _ b hb]
  simp only [b, Module.Basis.reindex_apply, family_norm_standardBasis_off_prime p a ω hω,
    Finset.prod_const_one]

open Classical in
theorem family_determinant_norm_profile (p : Nat.Primes) (a : ℤ) (ω : S.Ω) :
    (family p a).determinant.norm ω (1 ⊗ₜ[ℚ] determinantVector) =
      if ω = primePoint p then Real.sqrt (p : ℝ) else 1 := by
  classical
  split_ifs with h
  · subst ω
    exact family_determinant_norm_prime p a
  · exact family_determinant_norm_off_prime p a ω h

/-- A rational completion has local degree one over its own completed base.
This is derived from the accepted sum of genuine local extension degrees. -/
theorem rational_localDegree_one (v : AbsoluteValue ℚ ℝ) [A : Algebra ℚ ℚ]
    [FiniteDimensional ℚ ℚ] : v.localDegree ℚ = 1 := by
  have hA : A = Algebra.id ℚ := Subsingleton.elim _ _
  subst A
  let : Unique {w : AbsoluteValue ℚ ℝ // w.under ℚ = v} :=
    { default := ⟨v, by ext q; rfl⟩
      uniq := fun w => by
        apply Subtype.ext
        ext q
        exact congrArg (fun u : AbsoluteValue ℚ ℝ => u q) w.property }
  have hd : (default : {w : AbsoluteValue ℚ ℝ // w.under ℚ = v}).val = v := by
    exact congrArg Subtype.val (Subsingleton.elim _
      (⟨v, by ext q; rfl⟩ : {w : AbsoluteValue ℚ ℝ // w.under ℚ = v}))
  have h := AbsoluteValue.sum_localDegree (K := ℚ) (L := ℚ) v
  simpa only [Fintype.sum_unique, hd, Module.finrank_self] using h

theorem rational_singleton_mass (ω : S.Ω) : S.v {ω} = 1 := by
  exact (normalizedNumberFieldAdelicStructure_v_singleton (K := ℚ) ω).trans
    (by
      simpa only [Nat.cast_one] using (congrArg (fun n : ℕ => (n : ENNReal))
        (rational_localDegree_one (A := DivisionRing.toRatAlgebra)
          (normalizedPlaceValue (K := ℚ) ω))))

theorem rational_singleton_real_mass (ω : S.Ω) : S.v.real {ω} = 1 := by
  rw [measureReal_def, rational_singleton_mass, ENNReal.toReal_one]

theorem rationalCurveRegularity :
    DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield := by
  left
  exact inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})

local instance rationalCurveProper : S.IsProper :=
  normalizedNumberFieldAdelicStructure_isProper

/-- The actual degree is negative one half of the prime logarithm. No
primitive-vector or slope estimate is needed for this determinant calculation. -/
theorem bundle_degree (p : Nat.Primes) (a : ℤ) :
    (bundle p a).degree rationalCurveRegularity
      (normalizedNumberFieldArchimedeanCompletions (K := ℚ)) = -Real.log (p : ℝ) / 2 := by
  classical
  let : DiscreteMeasurableSpace S.Ω := inferInstanceAs
    (DiscreteMeasurableSpace {ω : AbsoluteValue.Place ℚ // ω ≠ AbsoluteValue.trivialPlace ℚ})
  rw [(bundle p a).degree_eq_neg_integral rationalCurveRegularity
    (normalizedNumberFieldArchimedeanCompletions (K := ℚ))
      ⟨determinantVector, determinantVector_ne_zero⟩]
  have he : (bundle p a).toNormFamily.determinant.logNorm determinantVector =
      ({primePoint p} : Set S.Ω).indicator (fun _ => Real.log (Real.sqrt (p : ℝ))) := by
    funext ω
    change Real.log ((family p a).determinant.norm ω _) = _
    rw [family_determinant_norm_profile]
    by_cases hω : ω = primePoint p <;> simp [hω]
  rw [he, integral_indicator (measurableSet_singleton _), integral_singleton,
    rational_singleton_real_mass, one_smul, Real.log_sqrt (by positivity)]
  ring

end ArakelovGeometry.NonpureNumberFieldMinkowskiObstruction
