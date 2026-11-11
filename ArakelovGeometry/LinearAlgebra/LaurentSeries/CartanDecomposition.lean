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

The imported elementary-divisor input is `Submodule.smithNormalFormOfRankEq`,
through its full-rank basis and coefficient API in `FreeModule.PID`.
`PowerSeries.Inverse` supplies the discrete valuation ring instance;
`LaurentSeries` supplies localization at powers of `X` and the fraction-field
instance. No field closure or descent hypothesis enters these producers.
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

section OneParameter

variable (R : Type*) [CommRing R]

/-- The diagonal one-parameter subgroup on units of any coefficient ring. -/
def diagonalOneParameter (a : ι → ℤ) : Rˣ →* GL ι R where
  toFun t := ⟨diagonal (fun i ↦ ((t ^ a i : Rˣ) : R)),
    diagonal (fun i ↦ ((t ^ (-a i) : Rˣ) : R)),
    by simp [diagonal_mul_diagonal, ← Units.val_mul],
    by simp [diagonal_mul_diagonal, ← Units.val_mul]⟩
  map_one' := by ext i j : 2; simp
  map_mul' t u := by
    apply Units.ext
    simp [diagonal_mul_diagonal, mul_zpow]

@[simp]
theorem diagonalOneParameter_val (a : ι → ℤ) (t : Rˣ) :
    (diagonalOneParameter R a t : Matrix ι ι R) =
      diagonal (fun i ↦ ((t ^ a i : Rˣ) : R)) := rfl

theorem diagonalOneParameter_det (a : ι → ℤ) (t : Rˣ) :
    GeneralLinearGroup.det (diagonalOneParameter R a t) = t ^ (∑ i, a i) := by
  apply Units.ext
  change (diagonal (fun i ↦ ((t ^ a i : Rˣ) : R))).det = _
  rw [det_diagonal]
  have hs (s : Finset ι) : (∏ i ∈ s, ((t ^ a i : Rˣ) : R)) =
      ((t ^ (∑ i ∈ s, a i) : Rˣ) : R) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  exact hs Finset.univ

/-- Zero total weight gives a special-linear one-parameter subgroup. -/
def diagonalOneParameterSL (a : ι → ℤ) (ha : ∑ i, a i = 0) :
    Rˣ →* SpecialLinearGroup ι R where
  toFun t := ⟨diagonalOneParameter R a t, by
    have h := congrArg Units.val (diagonalOneParameter_det R a t)
    simpa [ha] using h⟩
  map_one' := by apply Subtype.ext; exact congrArg Units.val (map_one _)
  map_mul' t u := by apply Subtype.ext; exact congrArg Units.val (map_mul _ t u)

/-- Diagonal one-parameter subgroups commute with every change of coefficient ring. -/
theorem map_diagonalOneParameter {S : Type*} [CommRing S] (f : R →+* S)
    (a : ι → ℤ) (t : Rˣ) :
    GeneralLinearGroup.map f (diagonalOneParameter R a t) =
      diagonalOneParameter S a (Units.map f t) := by
  apply Units.ext
  change (diagonal (fun i ↦ ((t ^ a i : Rˣ) : R))).map f =
    diagonal (fun i ↦ (((Units.map f t) ^ a i : Sˣ) : S))
  rw [diagonal_map (map_zero f)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) t (a i))

end OneParameter

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
    have hs (s : Finset ι) : (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, zpow_add₀ hx]
    rw [hs] at h
    simpa [u, map_mul, mul_assoc, mul_left_comm, mul_comm] using h
  apply exponent_eq_zero_of_eq_unit (∑ i, a i) u⁻¹
  apply mul_left_cancel₀ (u.isUnit.map φ).ne_zero
  rw [hprod, ← map_mul]
  simp

/-- Determinant-one Laurent matrices admit integral special-linear outer factors. -/
theorem exists_specialLinear_cartan (g : GL ι K⸨X⸩)
    (hg : (g : Matrix ι ι K⸨X⸩).det = 1) :
    ∃ (P Q : SpecialLinearGroup ι K⟦X⟧) (a : ι → ℤ),
      (∑ i, a i = 0) ∧ (g : Matrix ι ι K⸨X⸩) =
        (P : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) *
          diagonal (fun i ↦ (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a i) *
          (Q : Matrix ι ι K⟦X⟧).map (algebraMap K⟦X⟧ K⸨X⸩) := by
  obtain ⟨P, Q, a, h⟩ := exists_cartan g
  have ha : ∑ i, a i = 0 := sum_exponents_eq_zero P Q a (h ▸ hg)
  let φ := algebraMap K⟦X⟧ K⸨X⸩
  let x : K⸨X⸩ := φ PowerSeries.X
  have hx : x ≠ 0 := by simp [x, φ]
  have hD : (diagonal (fun i ↦ x ^ a i)).det = 1 := by
    rw [det_diagonal]
    have hs (s : Finset ι) : (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, zpow_add₀ hx]
    rw [hs, ha, zpow_zero]
  have hpq : (P : Matrix ι ι K⟦X⟧).det * (Q : Matrix ι ι K⟦X⟧).det = 1 := by
    apply IsFractionRing.injective K⟦X⟧ K⸨X⸩
    have hh := congrArg Matrix.det h
    rw [hg, det_mul, det_mul, hD, mul_one] at hh
    simpa only [map_mul, map_one, RingHom.map_det, RingHom.mapMatrix_apply] using hh.symm
  cases isEmpty_or_nonempty ι with
  | inl he =>
    exact ⟨1, 1, a, ha, Subsingleton.elim _ _⟩
  | inr he =>
    obtain ⟨i₀⟩ := he
    let u := GeneralLinearGroup.det P
    let s : ι → K⟦X⟧ˣ := fun i ↦ if i = i₀ then u⁻¹ else 1
    let S : Matrix ι ι K⟦X⟧ := diagonal (fun i ↦ (s i : K⟦X⟧))
    let T : Matrix ι ι K⟦X⟧ := diagonal (fun i ↦ ((s i)⁻¹ : K⟦X⟧ˣ))
    have hS : S.det = (u⁻¹ : K⟦X⟧ˣ) := by simp [S, s, apply_ite]
    have hT : T.det = (u : K⟦X⟧) := by simp [T, s, apply_ite]
    have hp : ((P : Matrix ι ι K⟦X⟧) * S).det = 1 := by
      rw [det_mul, hS]
      exact u.val_inv
    have hq : (T * (Q : Matrix ι ι K⟦X⟧)).det = 1 := by
      rw [det_mul, hT]
      exact hpq
    refine ⟨⟨(P : Matrix ι ι K⟦X⟧) * S, hp⟩,
      ⟨T * (Q : Matrix ι ι K⟦X⟧), hq⟩, a, ha, ?_⟩
    change (g : Matrix ι ι K⸨X⸩) =
      ((P : Matrix ι ι K⟦X⟧) * S).map φ * diagonal (fun i ↦ x ^ a i) *
        (T * (Q : Matrix ι ι K⟦X⟧)).map φ
    rw [h, Matrix.map_mul, Matrix.map_mul]
    have hmid : S.map φ * diagonal (fun i ↦ x ^ a i) * T.map φ =
        diagonal (fun i ↦ x ^ a i) := by
      dsimp only [S, T]
      rw [diagonal_map (map_zero φ), diagonal_map (map_zero φ),
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      rw [mul_right_comm, ← map_mul]
      simp
    calc
      _ = (P : Matrix ι ι K⟦X⟧).map φ *
          (S.map φ * diagonal (fun i ↦ x ^ a i) * T.map φ) *
          (Q : Matrix ι ι K⟦X⟧).map φ := by rw [hmid]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- A nonpositive weight can occur in a vector vanishing at `X = 0` only when
the corresponding integral coordinate has zero constant term. -/
theorem constantCoeff_eq_zero_of_nonpositive_weight (a : ℤ) (ha : a ≤ 0)
    (f h : K⟦X⟧)
    (heq : (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a *
      algebraMap K⟦X⟧ K⸨X⸩ f = algebraMap K⟦X⟧ K⸨X⸩ (PowerSeries.X * h)) :
    PowerSeries.constantCoeff f = 0 := by
  have hc := congrArg (fun z : K⸨X⸩ ↦ z.coeff a) heq
  by_cases hneg : a < 0
  · simpa [LaurentSeries.coe_algebraMap, ← RatFunc.single_zpow,
      HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, show a < 1 by omega] using hc
  · have he : a = 0 := le_antisymm ha (le_of_not_gt hneg)
    subst a
    simpa [LaurentSeries.coe_algebraMap, HahnSeries.coeff_single_mul,
      PowerSeries.coeff_coe] using hc

/-- A Laurent special-linear degeneration gives a constant special-linear change
of coordinates supported entirely in strictly positive weights. -/
theorem exists_constant_degeneration (g : GL ι K⸨X⸩)
    (hg : (g : Matrix ι ι K⸨X⸩).det = 1) (v : ι → K)
    (hv : ∃ w : ι → K⟦X⟧,
      (g : Matrix ι ι K⸨X⸩) *ᵥ (fun i ↦ algebraMap K K⸨X⸩ (v i)) =
        fun i ↦ algebraMap K⟦X⟧ K⸨X⸩ (PowerSeries.X * w i)) :
    ∃ (q : SpecialLinearGroup ι K) (a : ι → ℤ),
      (∑ i, a i = 0) ∧ ∀ i, a i ≤ 0 → ((q : Matrix ι ι K) *ᵥ v) i = 0 := by
  obtain ⟨P, Q, a, ha, h⟩ := exists_specialLinear_cartan g hg
  obtain ⟨w, hw⟩ := hv
  let φ := algebraMap K⟦X⟧ K⸨X⸩
  let vR : ι → K⟦X⟧ := fun i ↦ PowerSeries.C (v i)
  let f : ι → K⟦X⟧ := (Q : Matrix ι ι K⟦X⟧) *ᵥ vR
  let z : ι → K⟦X⟧ := ((P⁻¹ : SpecialLinearGroup ι K⟦X⟧) : Matrix ι ι K⟦X⟧) *ᵥ w
  let q := SpecialLinearGroup.map (PowerSeries.constantCoeff : K⟦X⟧ →+* K) Q
  have hmap (B : Matrix ι ι K⟦X⟧) (b : ι → K⟦X⟧) :
      (fun i ↦ φ ((B *ᵥ b) i)) = B.map φ *ᵥ (fun i ↦ φ (b i)) := by
    funext i
    exact φ.map_mulVec B b i
  have hvR : (fun i ↦ φ (vR i)) = fun i ↦ algebraMap K K⸨X⸩ (v i) := by
    funext i
    simp [φ, vR, LaurentSeries.algebraMap_apply]
  have hPi : (((P⁻¹ : SpecialLinearGroup ι K⟦X⟧) : Matrix ι ι K⟦X⟧).map φ) *
      (P : Matrix ι ι K⟦X⟧).map φ = 1 := by
    rw [← Matrix.map_mul, ← SpecialLinearGroup.coe_mul]
    simp
  have hdiag : diagonal (fun i ↦ (φ PowerSeries.X) ^ a i) *ᵥ (fun i ↦ φ (f i)) =
      fun i ↦ φ (PowerSeries.X * z i) := by
    rw [hmap]
    have hh := congrArg
      (fun b ↦ (((P⁻¹ : SpecialLinearGroup ι K⟦X⟧) : Matrix ι ι K⟦X⟧).map φ) *ᵥ b) hw
    rw [h] at hh
    have hr : (fun i ↦ φ (PowerSeries.X * w i)) =
        φ PowerSeries.X • (fun i ↦ φ (w i)) := by
      funext i
      simp
    rw [hr, mulVec_smul] at hh
    change (((P⁻¹ : SpecialLinearGroup ι K⟦X⟧) : Matrix ι ι K⟦X⟧).map φ) *ᵥ
      (((P : Matrix ι ι K⟦X⟧).map φ * diagonal (fun i ↦ (φ PowerSeries.X) ^ a i) *
        (Q : Matrix ι ι K⟦X⟧).map φ) *ᵥ _) = _ at hh
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hPi, Matrix.one_mul] at hh
    rw [hvR]
    convert hh using 1
    · exact mulVec_mulVec _ _ _
    · funext i
      simp only [map_mul, Pi.smul_apply, smul_eq_mul]
      congr 1
      exact φ.map_mulVec _ w i
  refine ⟨q, a, ha, ?_⟩
  intro i hi
  have hi' := congrFun hdiag i
  simp only [mulVec_diagonal] at hi'
  have hf := constantCoeff_eq_zero_of_nonpositive_weight (K := K) (a i) hi (f i) (z i) hi'
  have hc := (PowerSeries.constantCoeff : K⟦X⟧ →+* K).map_mulVec
    (Q : Matrix ι ι K⟦X⟧) vR i
  change (((Q : Matrix ι ι K⟦X⟧).map PowerSeries.constantCoeff) *ᵥ v) i = 0
  simpa [f, vR, Function.comp_def] using hc.symm.trans hf

/-- A diagonal Laurent action tends to zero exactly when every nonzero coordinate
has strictly positive weight. The witness is an actual integral power-series vector. -/
theorem diagonal_degeneration_iff (a : ι → ℤ) (v : ι → K) :
    (∃ w : ι → K⟦X⟧,
      diagonal (fun i ↦ (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a i) *ᵥ
        (fun i ↦ algebraMap K K⸨X⸩ (v i)) =
          fun i ↦ algebraMap K⟦X⟧ K⸨X⸩ (PowerSeries.X * w i)) ↔
      ∀ i, a i ≤ 0 → v i = 0 := by
  constructor
  · rintro ⟨w, hw⟩ i hi
    have h := congrFun hw i
    simp only [mulVec_diagonal] at h
    have hf := constantCoeff_eq_zero_of_nonpositive_weight (K := K) (a i) hi
      (PowerSeries.C (v i)) (w i) (by simpa [LaurentSeries.algebraMap_apply] using h)
    simpa using hf
  · intro hv
    refine ⟨fun i ↦ if 0 < a i then
      PowerSeries.X ^ ((a i).toNat - 1) * PowerSeries.C (v i) else 0, ?_⟩
    funext i
    rw [mulVec_diagonal]
    by_cases hp : 0 < a i
    · dsimp only
      simp only [hp, ↓reduceIte]
      have hn : (a i).toNat - 1 + 1 = (a i).toNat := by omega
      have hz : (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ a i =
          (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) ^ (a i).toNat := by
        simpa only [Int.toNat_of_nonneg (le_of_lt hp)] using
          zpow_natCast (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) (a i).toNat
      simp only [hz, map_mul, map_pow, ← mul_assoc, ← pow_succ', hn]
      congr 1
    · simp [hp, hv i (le_of_not_gt hp)]

/-- The concrete one-parameter degeneration extracted from a Laurent special-linear
degeneration, using the canonical linear equivalence of the constant SL matrix. -/
theorem exists_oneParameter_degeneration (g : GL ι K⸨X⸩)
    (hg : (g : Matrix ι ι K⸨X⸩).det = 1) (v : ι → K)
    (hv : ∃ w : ι → K⟦X⟧,
      (g : Matrix ι ι K⸨X⸩) *ᵥ (fun i ↦ algebraMap K K⸨X⸩ (v i)) =
        fun i ↦ algebraMap K⟦X⟧ K⸨X⸩ (PowerSeries.X * w i)) :
    ∃ (q : SpecialLinearGroup ι K) (a : ι → ℤ) (ha : ∑ i, a i = 0)
      (w : ι → K⟦X⟧),
      (diagonalOneParameterSL K⸨X⸩ a ha
        (Units.mk0 (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) (by simp)) : Matrix ι ι K⸨X⸩) *ᵥ
          (fun i ↦ algebraMap K K⸨X⸩ (q.toLin' v i)) =
            fun i ↦ algebraMap K⟦X⟧ K⸨X⸩ (PowerSeries.X * w i) := by
  obtain ⟨q, a, ha, hv'⟩ := exists_constant_degeneration g hg v hv
  obtain ⟨w, hw⟩ := (diagonal_degeneration_iff a ((q : Matrix ι ι K) *ᵥ v)).2 hv'
  refine ⟨q, a, ha, w, ?_⟩
  change diagonal (fun i ↦ ((Units.mk0
    (algebraMap K⟦X⟧ K⸨X⸩ PowerSeries.X) (by simp) ^ a i : K⸨X⸩ˣ) : K⸨X⸩)) *ᵥ
      (fun i ↦ algebraMap K K⸨X⸩ (((q : Matrix ι ι K) *ᵥ v) i)) = _
  simpa using hw

end Laurent

end ArakelovGeometry.LaurentCartan
