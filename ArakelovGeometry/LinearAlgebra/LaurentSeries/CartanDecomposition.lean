import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integer

/-!
# Elementary divisors over formal Laurent series

The route uses Smith normal form over the power-series discrete valuation ring.
All coefficient fields are arbitrary; this algebraic input alone does not prove
Hilbert–Mumford or rational descent.
-/

noncomputable section

open Module Matrix

namespace ArakelovGeometry.LaurentCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

omit [Fintype ι] [DecidableEq ι] in
/-- Smith normal form for an injective endomorphism, with bases of its actual domain
and codomain and nonzero diagonal entries. -/
theorem exists_bases_diagonal [Finite ι] (f : (ι → R) →ₗ[R] (ι → R))
    (hf : Function.Injective f) :
    ∃ (b c : Basis ι R (ι → R)) (d : ι → R),
      (∀ i, d i ≠ 0) ∧ ∀ i, f (c i) = d i • b i := by
  classical
  let := Fintype.ofFinite ι
  let e := LinearEquiv.ofInjective f hf
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    e.finrank_eq.symm
  let b := Submodule.smithNormalFormTopBasis (Pi.basisFun R ι) hr
  let c := Submodule.smithNormalFormBotBasis (Pi.basisFun R ι) hr
  let d := Submodule.smithNormalFormCoeffs (Pi.basisFun R ι) hr
  refine ⟨b, c.map e.symm, d, ?_, ?_⟩
  · exact Submodule.smithNormalFormCoeffs_ne_zero (Pi.basisFun R ι) hr
  · intro i
    simpa only [Basis.map_apply, e, LinearEquiv.ofInjective_symm_apply] using
      (Submodule.smithNormalFormBotBasis_def (Pi.basisFun R ι) hr i)

/-- An injective square matrix over a PID is a product of two integral invertible
matrices and a diagonal matrix with nonzero entries. -/
theorem exists_matrix_diagonal (A : Matrix ι ι R) (hA : Function.Injective A.mulVec) :
    ∃ (P Q : GL ι R) (d : ι → R),
      (∀ i, d i ≠ 0) ∧ A = (P : Matrix ι ι R) * diagonal d * (Q : Matrix ι ι R) := by
  obtain ⟨b, c, d, hd, hdiag⟩ := exists_bases_diagonal A.toLin' hA
  let e := Pi.basisFun R ι
  let P : GL ι R := ⟨e.toMatrix b, b.toMatrix e,
    e.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip e⟩
  let Q : GL ι R := ⟨c.toMatrix e, e.toMatrix c,
    c.toMatrix_mul_toMatrix_flip e, e.toMatrix_mul_toMatrix_flip c⟩
  refine ⟨P, Q, d, hd, ?_⟩
  have hD : LinearMap.toMatrix c b A.toLin' = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [LinearMap.toMatrix_apply, hdiag]
    · simp [LinearMap.toMatrix_apply, hdiag, hij]
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e c e b A.toLin'
  simpa only [hD, e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] using
    h.symm

end PID

section Laurent

variable {K : Type*} [Field K]

open scoped PowerSeries LaurentSeries

omit [Fintype ι] [DecidableEq ι] in
/-- A single power of `X` clears all entries of a finite Laurent-series matrix. -/
theorem exists_powerSeries_matrix [Finite ι] (g : Matrix ι ι K⸨X⸩) :
    ∃ (m : ℕ) (A : Matrix ι ι K⟦X⟧),
      A.map (algebraMap K⟦X⟧ K⸨X⸩) =
        (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ m • g := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (PowerSeries.X : K⟦X⟧)) (fun p : ι × ι ↦ g p.1 p.2)
  obtain ⟨m, hm⟩ := b.property
  choose A hA using hb
  refine ⟨m, fun i j ↦ A (i, j), ?_⟩
  apply Matrix.ext
  intro i j
  change algebraMap K⟦X⟧ K⸨X⸩ (A (i, j)) =
    (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ m * g i j
  simpa only [← hm, Algebra.smul_def, map_pow] using hA (i, j)

/-- A nonzero power series is a unit times a nonnegative power of `X`. -/
theorem exists_unit_mul_X_pow (f : K⟦X⟧) (hf : f ≠ 0) :
    ∃ (u : K⟦X⟧ˣ) (m : ℕ), f = (u : K⟦X⟧) * PowerSeries.X ^ m := by
  refine ⟨PowerSeries.Unit_of_divided_by_X_pow_order f, f.order.toNat, ?_⟩
  rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hf, mul_comm]
  exact PowerSeries.X_pow_order_mul_divXPowOrder.symm

/-- Laurent-series factorization with integral elementary divisors before absorbing
their units and shifting the exponents. -/
theorem exists_integral_diagonal (g : GL ι K⸨X⸩) :
    ∃ (m : ℕ) (P Q : GL ι K⟦X⟧) (d : ι → K⟦X⟧),
      (∀ i, d i ≠ 0) ∧
      (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ m • (g : Matrix ι ι K⸨X⸩) =
        (P : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) *
          diagonal (fun i ↦ algebraMap K⟦X⟧ K⸨X⸩ (d i)) *
          (Q : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) := by
  obtain ⟨m, A, hA⟩ := exists_powerSeries_matrix (g : Matrix ι ι K⸨X⸩)
  have hX : algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := K)
    apply IsFractionRing.injective K⟦X⟧ K⸨X⸩
    simp at h
  have hdet : A.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hA
    change ((algebraMap K⟦X⟧ K⸨X⸩).mapMatrix A).det = _ at h'
    rw [← RingHom.map_det, h, map_zero, Matrix.det_smul] at h'
    exact (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hX))
      (GeneralLinearGroup.det g).ne_zero) h'.symm
  obtain ⟨P, Q, d, hd, h⟩ := exists_matrix_diagonal A
    (Matrix.mulVec_injective_of_det_ne_zero hdet)
  refine ⟨m, P, Q, d, hd, ?_⟩
  simpa only [Matrix.map_mul, ← diagonal_map (map_zero (algebraMap K⟦X⟧ K⸨X⸩))] using
    hA.symm.trans (congrArg
      (fun B : Matrix ι ι K⟦X⟧ ↦ B.map (algebraMap K⟦X⟧ K⸨X⸩)) h)

/-- Cartan factorization over Laurent series, with both outer matrices invertible
over the power-series ring. The index type may be empty. -/
theorem exists_cartan (g : GL ι K⸨X⸩) :
    ∃ (P Q : GL ι K⟦X⟧) (a : ι → ℤ),
      (g : Matrix ι ι K⸨X⸩) =
        (P : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) *
          diagonal (fun i ↦ (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a i) *
          (Q : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) := by
  obtain ⟨m, P, Q, d, hd, h⟩ := exists_integral_diagonal g
  choose u k hk using fun i ↦ exists_unit_mul_X_pow (d i) (hd i)
  let U : GL ι K⟦X⟧ :=
    ⟨diagonal (fun i ↦ (u i : K⟦X⟧)), diagonal (fun i ↦ ((u i)⁻¹ : K⟦X⟧ˣ)),
      by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  let φ := algebraMap K⟦X⟧ K⸨X⸩
  let x : K⸨X⸩ := φ PowerSeries.X
  have hx : x ≠ 0 := by simp [x, φ]
  refine ⟨P * U, Q, fun i ↦ (k i : ℤ) - m, ?_⟩
  apply smul_right_injective (M := Matrix ι ι K⸨X⸩) (pow_ne_zero m hx)
  change x ^ m • (g : Matrix ι ι K⸨X⸩) = x ^ m •
    (((P * U : GL ι K⟦X⟧) : Matrix ι ι K⟦X⟧).map φ *
      diagonal (fun i ↦ x ^ ((k i : ℤ) - m)) * (Q : Matrix ι ι K⟦X⟧).map φ)
  rw [h, Units.val_mul, Matrix.map_mul]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  apply congrArg (fun B : Matrix ι ι K⸨X⸩ ↦ B * (Q : Matrix ι ι K⟦X⟧).map φ)
  rw [Matrix.mul_assoc]
  apply congrArg (fun B : Matrix ι ι K⸨X⸩ ↦ (P : Matrix ι ι K⟦X⟧).map φ * B)
  change diagonal (fun i ↦ φ (d i)) =
    (diagonal (fun i ↦ (u i : K⟦X⟧))).map φ *
      (x ^ m • diagonal (fun i ↦ x ^ ((k i : ℤ) - m)))
  rw [diagonal_map (map_zero φ), ← diagonal_smul, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hk i, map_mul, map_pow]
  dsimp only [x]
  rw [Pi.smul_apply, smul_eq_mul, ← zpow_natCast (φ PowerSeries.X) m, ← zpow_add₀ hx]
  simp [x]

/-- The only integral unit which is a pure Laurent monomial has exponent zero. -/
theorem exponent_eq_zero_of_eq_unit (a : ℤ) (u : K⟦X⟧ˣ)
    (h : (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a =
      algebraMap K⟦X⟧ K⸨X⸩ (u : K⟦X⟧)) : a = 0 := by
  by_contra ha
  have hc := congrArg (fun f : K⸨X⸩ ↦ f.coeff 0) h
  have hu := (PowerSeries.isUnit_constantCoeff (u : K⟦X⟧) u.isUnit).ne_zero
  apply hu
  simpa [LaurentSeries.coe_algebraMap, ← RatFunc.single_zpow,
    HahnSeries.coeff_single, PowerSeries.coeff_coe, ha, Ne.symm ha] using hc.symm

/-- Every Cartan factorization of a determinant-one matrix has zero total exponent. -/
theorem sum_exponents_eq_zero (P Q : GL ι K⟦X⟧) (a : ι → ℤ)
    (h : ((P : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) *
      diagonal (fun i ↦ (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a i) *
      (Q : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩)).det = 1) :
    ∑ i, a i = 0 := by
  let φ := algebraMap K⟦X⟧ K⸨X⸩
  let x : K⸨X⸩ := φ PowerSeries.X
  let u := GeneralLinearGroup.det P * GeneralLinearGroup.det Q
  have hx : x ≠ 0 := by simp [x, φ]
  have hprod : φ (u : K⟦X⟧) * x ^ (∑ i, a i) = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
    change (φ.mapMatrix (P : Matrix ι ι K⟦X⟧)).det * (∏ i, x ^ a i) *
      (φ.mapMatrix (Q : Matrix ι ι K⟦X⟧)).det = 1 at h
    rw [← φ.map_det, ← φ.map_det] at h
    rw [← zpow_sum₀ hx] at h
    simpa [u, map_mul, mul_assoc, mul_left_comm, mul_comm] using h
  apply exponent_eq_zero_of_eq_unit (∑ i, a i) u⁻¹
  apply mul_left_cancel₀ (u.isUnit.map φ).ne_zero
  rw [hprod, ← map_mul]
  simp

end Laurent

end ArakelovGeometry.LaurentCartan
