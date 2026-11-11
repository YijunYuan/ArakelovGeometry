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

/-- Smith normal form for an injective endomorphism, with bases of its actual domain
and codomain and nonzero diagonal entries. -/
theorem exists_bases_diagonal (f : (ι → R) →ₗ[R] (ι → R))
    (hf : Function.Injective f) :
    ∃ (b c : Basis ι R (ι → R)) (d : ι → R),
      (∀ i, d i ≠ 0) ∧ ∀ i, f (c i) = d i • b i := by
  let e := LinearEquiv.ofInjective f hf
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R (ι → R) :=
    e.finrank_eq.symm
  let b := Submodule.smithNormalFormTopBasis (Pi.basisFun R ι) hr
  let c := Submodule.smithNormalFormBotBasis (Pi.basisFun R ι) hr
  let d := Submodule.smithNormalFormCoeffs (Pi.basisFun R ι) hr
  refine ⟨b, c.map e.symm, d, ?_, ?_⟩
  · exact Submodule.smithNormalFormCoeffs_ne_zero (Pi.basisFun R ι) hr
  · intro i
    simpa only [Basis.map_apply, LinearEquiv.ofInjective_symm_apply] using
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
    simp [LinearMap.toMatrix_apply, hdiag, diagonal_apply, eq_comm]
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e c e b A.toLin'
  simpa only [hD, e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] using
    h.symm

end PID

section Laurent

variable {K : Type*} [Field K]

open scoped PowerSeries LaurentSeries

/-- A single power of `X` clears all entries of a finite Laurent-series matrix. -/
theorem exists_powerSeries_matrix (g : Matrix ι ι K⸨X⸩) :
    ∃ (m : ℕ) (A : Matrix ι ι K⟦X⟧),
      A.map (algebraMap K⟦X⟧ K⸨X⸩) =
        (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ m • g := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (PowerSeries.X : K⟦X⟧)) (fun p : ι × ι ↦ g p.1 p.2)
  obtain ⟨m, hm⟩ := b.property
  choose A hA using hb
  refine ⟨m, fun i j ↦ A (i, j), ?_⟩
  ext i j
  simpa only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, Algebra.smul_def,
    ← hm, map_pow, smul_eq_mul] using hA (i, j)

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
  have hX : algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X ≠ 0 :=
    map_ne_zero (IsFractionRing.injective K⟦X⟧ K⸨X⸩) PowerSeries.X_ne_zero
  have hdet : A.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hA
    rw [← RingHom.map_det, h, map_zero, Matrix.det_smul] at h'
    exact (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hX))
      (GeneralLinearGroup.det g).ne_zero) h'.symm
  obtain ⟨P, Q, d, hd, h⟩ := exists_matrix_diagonal A
    (Matrix.mulVec_injective_of_det_ne_zero hdet)
  refine ⟨m, P, Q, d, hd, ?_⟩
  rw [← hA, h, Matrix.map_mul, Matrix.map_mul, Matrix.map_diagonal]

end Laurent

end ArakelovGeometry.LaurentCartan
