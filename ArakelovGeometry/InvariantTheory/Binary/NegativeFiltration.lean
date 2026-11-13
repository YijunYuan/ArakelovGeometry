/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree
public import ArakelovGeometry.InvariantTheory.Binary.Orbit.Coordinates
public import ArakelovGeometry.InvariantTheory.Binary.Orbit.DVR
public import ArakelovGeometry.InvariantTheory.Polynomial.SolutionDescent
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Residue matrix descent and actual negative binary filtrations

This is the binary finite-matrix implication required on Bost p31. The quotient
and its coefficient array are fixed over the original algebraically closed field.
Only matrix entries descend; the residue extension need not be algebraic.
Original weights are used: coordinates of weight at least zero vanish.
Optimizer rationality and further-extension semistability are separate results.
-/

@[expose] public section
noncomputable section

open Module MvPolynomial Matrix
open scoped TensorProduct

namespace ArakelovGeometry.InvariantTheory

section Polynomials

variable {k : Type*} [Field k] {ι : Bool → Type*}
  [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)] {r : ℕ}

/-- The determinant polynomial for a fixed original coefficient array. For two
factors its entries are the double sums `∑ i,j, c t (i,j) * U i p₁ * V j p₂`.
The row is a selected tensor and the column is a target coordinate. -/
def binaryDeterminantPolynomial (c : Fin r → (∀ j, ι j) → k)
    (p : BinaryTensorIndex ι r) : MvPolynomial (BinarySLVariables ι) k :=
  Matrix.det (Matrix.of fun l t ↦ ∑ s, C (c t s) * ∏ j, X ⟨j, s j, p l j⟩)

/-- Evaluation of the fixed determinant polynomial commutes with every scalar
extension, including an arbitrary residue field. -/
theorem binaryDeterminantPolynomial_eval {A : Type*} [CommRing A] [Algebra k A]
    (c : Fin r → (∀ j, ι j) → k) (h : ∀ j, Matrix.SpecialLinearGroup (ι j) A)
    (p : BinaryTensorIndex ι r) :
    evalBinarySLPolynomial h (binaryDeterminantPolynomial c p) =
      Matrix.det (fun l t ↦ ∑ s, algebraMap k A (c t s) * ∏ j, h j (s j) (p l j)) := by
  rw [binaryDeterminantPolynomial, (evalBinarySLPolynomial (k := k) h).map_det]
  congr 1
  ext l t
  simp [evalBinarySLPolynomial]

/-- Descent returns actual determinant-one matrices and vanishing of the same
original coefficient polynomials. Only the fixed integer weights select the
equations; no order on either field is used. -/
theorem exists_binarySL_vanishing_of_extension [IsAlgClosed k]
    {κ : Type*} [Field κ] [Algebra k κ]
    (c : Fin r → (∀ j, ι j) → k) (a : ∀ j, ι j → ℤ)
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) κ)
    (hz : ∀ p : BinaryTensorIndex ι r, 0 ≤ ∑ l, ∑ j, a j (p l j) →
      evalBinarySLPolynomial h (binaryDeterminantPolynomial c p) = 0) :
    ∃ h₀ : ∀ j, Matrix.SpecialLinearGroup (ι j) k,
      ∀ p : BinaryTensorIndex ι r, 0 ≤ ∑ l, ∑ j, a j (p l j) →
        evalBinarySLPolynomial h₀ (binaryDeterminantPolynomial c p) = 0 := by
  let S : Set (MvPolynomial (BinarySLVariables ι) k) :=
    Set.range (fun j ↦ (binarySLUniversalMatrix k ι j).det - 1) ∪
      {P | ∃ p, 0 ≤ ∑ l, ∑ j, a j (p l j) ∧ P = binaryDeterminantPolynomial c p}
  obtain ⟨x, hx⟩ := exists_polynomial_solution_of_extension S
    ⟨(fun v ↦ h v.1 v.2.1 v.2.2), by
      rintro P (⟨j, rfl⟩ | ⟨p, hp, rfl⟩)
      · change evalBinarySLPolynomial h ((binarySLUniversalMatrix k ι j).det - 1) = 0
        rw [map_sub, map_one, evalBinarySLPolynomial_det, sub_self]
      · exact hz p hp⟩
  have hdet (j : Bool) : Matrix.det (fun u v ↦ x ⟨j, u, v⟩) = 1 := by
    have hh := hx _ (Or.inl ⟨j, rfl⟩)
    rw [map_sub, map_one, sub_eq_zero, AlgHom.map_det] at hh
    convert hh using 1
    congr 1
    ext u v
    exact (aeval_X x ⟨j, u, v⟩).symm
  refine ⟨fun j ↦ ⟨fun u v ↦ x ⟨j, u, v⟩, hdet j⟩, ?_⟩
  intro p hp
  exact hx _ (Or.inr ⟨p, hp, rfl⟩)

/-- Evaluation of matrix-coordinate polynomials commutes with algebra maps.
This transports integral evaluations separately to the fraction and residue fields. -/
theorem evalBinarySLPolynomial_map
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (h : ∀ j, Matrix.SpecialLinearGroup (ι j) A)
    (P : MvPolynomial (BinarySLVariables ι) k) :
    evalBinarySLPolynomial (fun j ↦ Matrix.SpecialLinearGroup.map φ.toRingHom (h j)) P =
      φ (evalBinarySLPolynomial h P) := by
  have he : evalBinarySLPolynomial
      (fun j ↦ Matrix.SpecialLinearGroup.map φ.toRingHom (h j)) =
      φ.comp (evalBinarySLPolynomial h) := by
    ext v
    simp [evalBinarySLPolynomial]
  exact congrArg (fun f : MvPolynomial (BinarySLVariables ι) k →ₐ[k] B ↦ f P) he

/-- A fraction-field equality recovers the integral polynomial value by
injectivity and then reduces it. The scalar graph is `k → R → L` and
`k → R → ResidueField R`; no map from `L` to the residue field is used. -/
theorem evalBinarySLPolynomial_residue_of_fraction
    {R L : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L]
    [IsScalarTower k R L] [IsFractionRing R L]
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) R)
    (P : MvPolynomial (BinarySLVariables ι) k) (c : R)
    (hc : evalBinarySLPolynomial
      (fun j ↦ Matrix.SpecialLinearGroup.map (algebraMap R L) (h j)) P =
      algebraMap R L c) :
    evalBinarySLPolynomial
      (fun j ↦ Matrix.SpecialLinearGroup.map (IsLocalRing.residue R) (h j)) P =
      IsLocalRing.residue R c := by
  have he : evalBinarySLPolynomial h P = c := by
    apply IsFractionRing.injective R L
    exact (evalBinarySLPolynomial_map (IsScalarTower.toAlgHom k R L) h P).symm.trans hc
  exact (evalBinarySLPolynomial_map
    (IsScalarTower.toAlgHom k R (IsLocalRing.ResidueField R)) h P).trans
      (congrArg (IsLocalRing.residue R) he)

end Polynomials

section OriginalQuotient

variable {k : Type*} [Field k] {ι : Bool → Type*}
  [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
  {E : Bool → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]
  {Q : Type*} [AddCommGroup Q] [Module k Q] {r : ℕ}

/-- Coefficients of the original quotient in the originally chosen bases.
This array stays over `k` throughout residue descent. -/
def binaryQuotientCoefficients (b : ∀ j, Basis (ι j) k (E j))
    (d : Basis (Fin r) k Q) (q : (⨂[k] j, E j) →ₗ[k] Q) :
    Fin r → (∀ j, ι j) → k := fun t s ↦ d.repr (q (⨂ₜ[k] j, b j (s j))) t

/-- The original quotient expressed in factor coordinates. The map is the actual
quotient precomposed with the tensor of the chosen basis equivalences. -/
def binaryQuotientInCoordinates (b : ∀ j, Basis (ι j) k (E j))
    (q : (⨂[k] j, E j) →ₗ[k] Q) : (⨂[k] j, (ι j → k)) →ₗ[k] Q :=
  q.comp (PiTensorProduct.congr (fun j ↦ (b j).equivFun.symm)).toLinearMap

@[simp]
theorem binaryQuotientInCoordinates_basis (b : ∀ j, Basis (ι j) k (E j))
    (q : (⨂[k] j, E j) →ₗ[k] Q) (s : ∀ j, ι j) :
    binaryQuotientInCoordinates b q (⨂ₜ[k] j, Pi.single (s j) 1) =
      q (⨂ₜ[k] j, b j (s j)) := by
  simp [binaryQuotientInCoordinates, Basis.equivFun_symm_apply]

omit [∀ j, DecidableEq (ι j)] in
/-- Basis transport preserves surjectivity of the original quotient. -/
theorem binaryQuotientInCoordinates_surjective (b : ∀ j, Basis (ι j) k (E j))
    (q : (⨂[k] j, E j) →ₗ[k] Q) (hq : Function.Surjective q) :
    Function.Surjective (binaryQuotientInCoordinates b q) :=
  hq.comp (PiTensorProduct.congr (fun j ↦ (b j).equivFun.symm)).surjective

omit [∀ j, DecidableEq (ι j)] in
/-- Coefficient transport preserves precisely the original array. -/
theorem binaryQuotientInCoordinates_coefficients (b : ∀ j, Basis (ι j) k (E j))
    (d : Basis (Fin r) k Q) (q : (⨂[k] j, E j) →ₗ[k] Q) :
    binaryQuotientCoefficients (fun j ↦ Pi.basisFun k (ι j)) d
      (binaryQuotientInCoordinates b q) = binaryQuotientCoefficients b d q := by
  classical
  funext t s
  simp [binaryQuotientCoefficients]

/-- An actual basis transported by a determinant-one matrix. -/
def binaryChangedBasis (b : ∀ j, Basis (ι j) k (E j))
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) k) (j : Bool) : Basis (ι j) k (E j) :=
  (b j).map (Matrix.SpecialLinearGroup.toLin_equiv (b j) (h j)).val

@[simp]
theorem binaryChangedBasis_repr (b : ∀ j, Basis (ι j) k (E j))
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) k) (j : Bool) (u v : ι j) :
    (b j).repr (binaryChangedBasis b h j v) u = h j u v := by
  change (b j).repr (Matrix.toLin (b j) (b j) (h j).val (b j v)) u = _
  rw [Matrix.repr_toLin]
  simp [Matrix.mulVec, dotProduct, Finsupp.single_apply]

omit [∀ j, DecidableEq (ι j)] in
/-- Expansion of the same actual quotient in its fixed tensor basis. -/
theorem binaryQuotient_coordinate_tprod (b : ∀ j, Basis (ι j) k (E j))
    (d : Basis (Fin r) k Q) (q : (⨂[k] j, E j) →ₗ[k] Q)
    (x : ∀ j, E j) (t : Fin r) :
    d.repr (q (⨂ₜ[k] j, x j)) t =
      ∑ s, binaryQuotientCoefficients b d q t s * ∏ j, (b j).repr (x j) (s j) := by
  have hh := congrArg (fun z ↦ d.repr (q z) t)
    ((Basis.piTensorProduct b).sum_repr (⨂ₜ[k] j, x j))
  simpa [binaryQuotientCoefficients, map_sum, map_smul, mul_comm] using hh.symm

/-- The polynomial evaluates to the original actual quotient determinant after
an actual basis change. In particular no surrogate quotient or support is used. -/
theorem binaryDeterminantPolynomial_eq_quotient_det
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q)
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) k) (p : BinaryTensorIndex ι r) :
    evalBinarySLPolynomial h (binaryDeterminantPolynomial (binaryQuotientCoefficients b d q) p) =
      Matrix.det (fun l t ↦ d.repr (q (⨂ₜ[k] j, binaryChangedBasis b h j (p l j))) t) := by
  rw [binaryDeterminantPolynomial_eval]
  congr 1
  ext l t
  rw [binaryQuotient_coordinate_tprod b d q]
  simp

omit [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)] in
/-- The canonical tensor/base-change isomorphism identifies the extended actual
quotient coefficient array with the image of the original array. This checks the
original-field model without assuming it of a generic fraction-field quotient. -/
theorem binaryQuotientCoefficients_baseChange
    (L : Type*) [Field L] [Algebra k L]
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q) (t : Fin r) (s : ∀ j, ι j) :
    binaryQuotientCoefficients (fun j ↦ (b j).baseChange L) (d.baseChange L)
      ((q.baseChange L).comp (tensorBaseChangeEquiv k L E).symm.toLinearMap) t s =
      algebraMap k L (binaryQuotientCoefficients b d q t s) := by
  simp [binaryQuotientCoefficients, tensorBaseChangeEquiv_symm_tprod_tmul,
    Algebra.smul_def]

/-- Over every extension field the original-k polynomial is exactly the
actual base-changed quotient determinant after the same matrix basis changes.
This is the canonical tensor/base-change identity required by Bost p31. -/
theorem binaryDeterminantPolynomial_eq_baseChange_det
    (L : Type*) [Field L] [Algebra k L]
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q)
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) L) (p : BinaryTensorIndex ι r) :
    evalBinarySLPolynomial h (binaryDeterminantPolynomial (binaryQuotientCoefficients b d q) p) =
      Matrix.det (fun l t ↦ (d.baseChange L).repr
        (((q.baseChange L).comp (tensorBaseChangeEquiv k L E).symm.toLinearMap)
          (⨂ₜ[L] j, binaryChangedBasis (fun j ↦ (b j).baseChange L) h j (p l j))) t) := by
  rw [binaryDeterminantPolynomial_eval]
  congr 1
  ext l t
  rw [binaryQuotient_coordinate_tprod (fun j ↦ (b j).baseChange L) (d.baseChange L)]
  simp only [binaryQuotientCoefficients_baseChange]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact (binaryChangedBasis_repr (fun j ↦ (b j).baseChange L) h j (s j) (p l j)).symm

/-- The actual original quotient, canonically extended to the fraction field,
has exactly the original polynomial value after residue. The matrices are the
inverse Cartan factors; inverse polynomial variables are unnecessary. -/
theorem binaryDeterminantPolynomial_residue_of_actual
    {R L : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L]
    [IsScalarTower k R L] [IsFractionRing R L]
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q)
    (H : ∀ j, Matrix.SpecialLinearGroup (ι j) R) (p : BinaryTensorIndex ι r) (c : R)
    (hc : Matrix.det (fun l t ↦ (d.baseChange L).repr
      (((q.baseChange L).comp (tensorBaseChangeEquiv k L E).symm.toLinearMap)
        (⨂ₜ[L] j, binaryChangedBasis (fun j ↦ (b j).baseChange L)
          (fun j ↦ Matrix.SpecialLinearGroup.map (algebraMap R L) ((H j)⁻¹)) j (p l j))) t) =
      algebraMap R L c) :
    evalBinarySLPolynomial
      (fun j ↦ Matrix.SpecialLinearGroup.map (IsLocalRing.residue R) ((H j)⁻¹))
      (binaryDeterminantPolynomial (binaryQuotientCoefficients b d q) p) =
      IsLocalRing.residue R c := by
  apply evalBinarySLPolynomial_residue_of_fraction (L := L) (fun j ↦ (H j)⁻¹)
  exact (binaryDeterminantPolynomial_eq_baseChange_det L b d q _ p).trans hc

/-- Under the descended equations, every nonzero actual quotient determinant
has strictly negative original total weight. The conclusion concerns the original
quotient and actual changed bases, not just polynomial solutions. -/
theorem binary_quotient_weight_negative
    (b : ∀ j, Basis (ι j) k (E j)) (d : Basis (Fin r) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q) (h : ∀ j, Matrix.SpecialLinearGroup (ι j) k)
    (a : ∀ j, ι j → ℤ)
    (hz : ∀ p : BinaryTensorIndex ι r, 0 ≤ ∑ l, ∑ j, a j (p l j) →
      evalBinarySLPolynomial h
        (binaryDeterminantPolynomial (binaryQuotientCoefficients b d q) p) = 0)
    (p : BinaryTensorIndex ι r)
    (hp : d.det (fun l ↦ q (Basis.piTensorProduct (binaryChangedBasis b h) (p l))) ≠ 0) :
    (∑ l, ∑ j, a j (p l j)) < 0 := by
  by_contra hn
  have he := hz p (le_of_not_gt hn)
  rw [binaryDeterminantPolynomial_eq_quotient_det] at he
  apply hp
  rw [Basis.det_apply, ← Matrix.det_transpose]
  convert he using 1
  congr 1
  ext l t
  simp [Matrix.transpose_apply, Basis.toMatrix_apply]

variable [FiniteDimensional k Q]

/-- This binary Bost p31 producer returns genuine centered real filtrations on
the original factors, with integer weighted bases and strictly negative actual
quotient expectation. It consumes extension-field matrix equations, not an
assumed negative candidate. Surjectivity supplies nonempty determinant support. -/
theorem exists_binary_negative_filtrations_of_extension [IsAlgClosed k]
    {κ : Type*} [Field κ] [Algebra k κ]
    (b : ∀ j, Basis (ι j) k (E j))
    (d : Basis (Fin (finrank k Q)) k Q)
    (q : (⨂[k] j, E j) →ₗ[k] Q) (hq : Function.Surjective q)
    (hr : 0 < finrank k Q)
    (a : ∀ j, ι j → ℤ) (ha : ∀ j, ∑ i, a j i = 0)
    (h : ∀ j, Matrix.SpecialLinearGroup (ι j) κ)
    (hz : ∀ p : BinaryTensorIndex ι (finrank k Q), 0 ≤ ∑ l, ∑ j, a j (p l j) →
      evalBinarySLPolynomial h
        (binaryDeterminantPolynomial (binaryQuotientCoefficients b d q) p) = 0) :
    ∃ F : ∀ j, ℝ → Submodule k (E j),
      (∀ j, Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
        Submodule.filtrationExpectation (F j) = 0) ∧
      Submodule.filtrationExpectation
        (fun t ↦ (Submodule.piTensorFiltration F t).map q) < 0 ∧
      ∃ b' : ∀ j, Basis (ι j) k (E j),
        ∀ j t, F j t = Submodule.span k (b' j '' {i | t ≤ (a j i : ℝ)}) := by
  let : ∀ j, FiniteDimensional k (E j) := fun j ↦ Module.Finite.of_basis (b j)
  obtain ⟨h₀, hh₀⟩ := exists_binarySL_vanishing_of_extension
    (binaryQuotientCoefficients b d q) a h hz
  let b' := binaryChangedBasis b h₀
  let w : ∀ j, ι j → ℝ := fun j i ↦ a j i
  let F : ∀ j, ℝ → Submodule k (E j) :=
    fun j t ↦ Submodule.span k (b' j '' {i | t ≤ w j i})
  refine ⟨F, ?_, ?_, b', fun _ _ ↦ rfl⟩
  · intro j
    obtain ⟨hb, ht⟩ := Submodule.span_weights_attains_bot_top (b' j) (w j)
    refine ⟨Submodule.antitone_span_weights (b' j) (w j), hb, ht,
      Submodule.span_weights_locallyConstant_left (b' j) (w j), ?_⟩
    rw [Submodule.filtrationExpectation_eq_sum_weights (b' j) (w j) (fun _ ↦ rfl)]
    have hs : ∑ i, w j i = 0 := by
      dsimp only [w]
      exact_mod_cast ha j
    rw [hs, zero_div]
  · obtain ⟨p, hp, he, _⟩ := Submodule.exists_quotient_expectation_maximum
      (Basis.piTensorProduct b') (fun s ↦ ∑ j, w j (s j)) d q hq
    have hp' := (Submodule.mem_quotientDeterminantSupport _ _ _ p).mp hp
    have hn := binary_quotient_weight_negative b d q h₀ a hh₀ p hp'
    have hn' : (∑ l, ∑ j, w j (p l j)) < 0 := by
      dsimp only [w]
      exact_mod_cast hn
    have ht : (fun t ↦ (Submodule.piTensorFiltration F t).map q) =
        (fun t ↦ (Submodule.span k
          (Basis.piTensorProduct b' '' {s | t ≤ ∑ j, w j (s j)})).map q) := by
      funext t
      rw [Submodule.piTensorFiltration_eq_span b' w (fun _ _ ↦ rfl)]
    rw [ht, he]
    exact div_neg_of_neg_of_pos hn' (Nat.cast_pos.mpr hr)

end OriginalQuotient

section OrbitComposition

universe u
variable {k : Type u} [Field k] {ι : Bool → Type u}
  [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]
  {Q : Type*} [AddCommGroup Q] [Module k Q] {r : ℕ}

/-- The generic coefficient polynomial is exactly A8-ORBIT's original quotient
polynomial in standard factor coordinates. This is the shared interface. -/
theorem binaryDeterminantPolynomial_eq_orbit_polynomial
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] Q) (b : Basis (Fin r) k Q)
    (p : BinaryTensorIndex ι r) :
    binaryDeterminantPolynomial
      (binaryQuotientCoefficients (fun j ↦ Pi.basisFun k (ι j)) b q) p =
      binaryQuotientDeterminantPolynomial q b p := by
  simp only [binaryDeterminantPolynomial, binaryQuotientCoefficients,
    binaryQuotientDeterminantPolynomial, Pi.basisFun_apply, Basis.coord_apply]
  rfl

/-- Concrete A8-ORBIT/DVR interface: its actual coordinate quotient determinant,
with inverse Cartan factors, reduces to the original-k polynomial value. The
original model is proved by binaryQuotientDeterminantPolynomial_actual_eval;
it is not inferred from the generic DVR theorem. -/
theorem binaryQuotientDeterminantPolynomial_residue
    {R L : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L]
    [IsScalarTower k R L] [IsFractionRing R L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] Q) (b : Basis (Fin r) k Q)
    (H : ∀ j, Matrix.SpecialLinearGroup (ι j) R) (p : BinaryTensorIndex ι r) (c : R)
    (hc : Matrix.det (Matrix.of fun l t ↦ binaryQuotientCoordinateBaseChange L q b
      (tensorSLRepresentation (k := L) (fun j ↦ ι j → L)
        (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv
          (Matrix.SpecialLinearGroup.map (algebraMap R L) (H j)))⁻¹)
        (⨂ₜ[L] j, Pi.single (p l j) 1)) t) = algebraMap R L c) :
    evalBinarySLPolynomial
      (fun j ↦ Matrix.SpecialLinearGroup.map (IsLocalRing.residue R) ((H j)⁻¹))
      (binaryDeterminantPolynomial
        (binaryQuotientCoefficients (fun j ↦ Pi.basisFun k (ι j)) b q) p) =
      IsLocalRing.residue R c := by
  apply evalBinarySLPolynomial_residue_of_fraction (L := L) (fun j ↦ (H j)⁻¹)
  rw [binaryDeterminantPolynomial_eq_orbit_polynomial]
  exact (binaryQuotientDeterminantPolynomial_actual_eval L q b
    (fun j ↦ Matrix.SpecialLinearGroup.map (algebraMap R L) ((H j)⁻¹)) p).trans
      (by simpa only [map_inv] using hc)

variable [IsAlgClosed k] [FiniteDimensional k Q]

/-- The actual integral determinant support furnished by A8-DVR gives actual
centered negative filtrations after descending the inverse residue matrices.
The support equations refer to the checked coordinate extension of the original
quotient. This fixed-ring interface is also the consumer of A8-ORBIT's output. -/
theorem exists_binary_negative_filtrations_of_dvr_support
    {R L : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field L] [Algebra k R] [Algebra R L] [Algebra k L]
    [IsScalarTower k R L] [IsFractionRing R L]
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] Q) (b : Basis (Fin (finrank k Q)) k Q)
    (hq : Function.Surjective q) (hr : 0 < finrank k Q)
    (H : ∀ j, Matrix.SpecialLinearGroup (ι j) R)
    (a : ∀ j, ι j → ℤ) (c : BinaryTensorIndex ι (finrank k Q) → R)
    (ha : ∀ j, ∑ i, a j i = 0)
    (he : ∀ p, Matrix.det (Matrix.of fun l t ↦ binaryQuotientCoordinateBaseChange L q b
      (tensorSLRepresentation (k := L) (fun j ↦ ι j → L)
        (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv
          (Matrix.SpecialLinearGroup.map (algebraMap R L) (H j)))⁻¹)
        (⨂ₜ[L] j, Pi.single (p l j) 1)) t) = algebraMap R L (c p))
    (hn : ∀ p, IsLocalRing.residue R (c p) ≠ 0 → (∑ l, ∑ j, a j (p l j)) < 0) :
    ∃ F : ∀ j, ℝ → Submodule k (ι j → k),
      (∀ j, Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
        Submodule.filtrationExpectation (F j) = 0) ∧
      Submodule.filtrationExpectation
        (fun t ↦ (Submodule.piTensorFiltration F t).map q) < 0 ∧
      ∃ (a : ∀ j, ι j → ℤ) (b' : ∀ j, Basis (ι j) k (ι j → k)),
        (∀ j, ∑ i, a j i = 0) ∧
        ∀ j t, F j t = Submodule.span k (b' j '' {i | t ≤ (a j i : ℝ)}) := by
  have hz (p : BinaryTensorIndex ι (finrank k Q))
      (hp : 0 ≤ ∑ l, ∑ j, a j (p l j)) :
      evalBinarySLPolynomial
        (fun j ↦ Matrix.SpecialLinearGroup.map (IsLocalRing.residue R) ((H j)⁻¹))
        (binaryDeterminantPolynomial
          (binaryQuotientCoefficients (fun j ↦ Pi.basisFun k (ι j)) b q) p) = 0 := by
    have heq := binaryQuotientDeterminantPolynomial_residue
      (k := k) (ι := ι) (r := finrank k Q)
      (R := R) (L := L) q b H p (c p) (he p)
    apply heq.trans
    by_contra hne
    exact (not_lt_of_ge hp) (hn p hne)
  obtain ⟨F, hF, hneg, b', hb'⟩ := exists_binary_negative_filtrations_of_extension
    (fun j ↦ Pi.basisFun k (ι j)) b q hq hr a ha
    (fun j ↦ Matrix.SpecialLinearGroup.map (IsLocalRing.residue R) ((H j)⁻¹)) hz
  exact ⟨F, hF, hneg, a, b', ha, hb'⟩


/-- Eliminate an actual degeneration with integral negative determinant support.
The determinant equations explicitly identify the coordinate extension of the
original quotient; no relation to an arbitrary fraction-field quotient is assumed. -/
private theorem exists_binary_negative_filtrations_of_degeneration_support
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] Q) (b : Basis (Fin (finrank k Q)) k Q)
    (hq : Function.Surjective q) (hr : 0 < finrank k Q)
    (f : Module.Dual k (⨂[k]^(finrank k Q) (⨂[k] j, (ι j → k))))
    (hd :
    ∃ d : BinaryCovectorDegeneration f,
      ∃ (H : ∀ j, Matrix.SpecialLinearGroup (ι j) d.valuationRing)
        (a : ∀ j, ι j → ℤ) (c : BinaryTensorIndex ι (finrank k Q) → d.valuationRing),
        (∀ j, ∑ u, a j u = 0) ∧
        (∀ p, Matrix.det (Matrix.of fun l t ↦
          binaryQuotientCoordinateBaseChange d.fractionField q b
            (tensorSLRepresentation (k := d.fractionField) (fun j ↦ ι j → d.fractionField)
              (fun j ↦ (Matrix.SpecialLinearGroup.toLin'_equiv
                (Matrix.SpecialLinearGroup.map (algebraMap d.valuationRing d.fractionField)
                  (H j)))⁻¹)
              (⨂ₜ[d.fractionField] j, Pi.single (p l j) 1)) t) =
          algebraMap d.valuationRing d.fractionField (c p)) ∧
        (∀ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0 →
          (∑ l, ∑ j, a j (p l j)) < 0) ∧
        ∃ p, IsLocalRing.residue d.valuationRing (c p) ≠ 0) :
    ∃ F : ∀ j, ℝ → Submodule k (ι j → k),
      (∀ j, Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
        Submodule.filtrationExpectation (F j) = 0) ∧
      Submodule.filtrationExpectation
        (fun t ↦ (Submodule.piTensorFiltration F t).map q) < 0 ∧
      ∃ (a : ∀ j, ι j → ℤ) (b' : ∀ j, Basis (ι j) k (ι j → k)),
        (∀ j, ∑ i, a j i = 0) ∧
        ∀ j t, F j t = Submodule.span k (b' j '' {i | t ≤ (a j i : ℝ)}) := by
  classical
  obtain ⟨d, H, a, c, ha, he, hn, _⟩ := hd
  rcases d with @⟨R, L, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact exists_binary_negative_filtrations_of_dvr_support
    (R := R) (L := L) q b hq hr H a c ha he hn

omit [∀ j, DecidableEq (ι j)] in
/-- Polynomial closure of the actual binary quotient orbit produces genuine
centered negative filtrations over the original algebraically closed field.
This is the Bost p31 negative-candidate implication in standard factor coordinates;
the coordinate quotient maps above handle arbitrary chosen factor bases. It does
not assert optimizer descent or semistability under further field extensions. -/
theorem exists_binary_negative_filtrations_of_orbit_closure
    (q : (⨂[k] j, (ι j → k)) →ₗ[k] Q) (b : Basis (Fin (finrank k Q)) k Q)
    (hq : Function.Surjective q) (hr : 0 < finrank k Q)
    (hclosure : ∀ P : MvPolynomial (BinaryTensorIndex ι (finrank k Q)) k,
      (∀ g : ∀ j, _root_.SpecialLinearGroup k (ι j → k),
        MvPolynomial.eval (fun p ↦ (tensorPowerRepresentation (finrank k Q)
          (tensorSLRepresentation (k := k) (fun j ↦ ι j → k))).dual g
          (exteriorCovector (finrank k Q) (exteriorPower.map (finrank k Q) q.dualMap
            (exteriorPower.ιMulti k (finrank k Q) b.coord)))
          (binaryTensorBasis k ι (finrank k Q) p)) P = 0) → MvPolynomial.eval 0 P = 0) :
    ∃ F : ∀ j, ℝ → Submodule k (ι j → k),
      (∀ j, Antitone (F j) ∧ (∃ t, F j t = ⊥) ∧ (∃ t, F j t = ⊤) ∧
        (∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F j s = F j t) ∧
        Submodule.filtrationExpectation (F j) = 0) ∧
      Submodule.filtrationExpectation
        (fun t ↦ (Submodule.piTensorFiltration F t).map q) < 0 ∧
      ∃ (a : ∀ j, ι j → ℤ) (b' : ∀ j, Basis (ι j) k (ι j → k)),
        (∀ j, ∑ i, a j i = 0) ∧
        ∀ j t, F j t = Submodule.span k (b' j '' {i | t ≤ (a j i : ℝ)}) := by
  classical
  exact exists_binary_negative_filtrations_of_degeneration_support q b hq hr _
    (exists_binary_quotient_negative_support_of_orbit_closure
      (k := k) (ι := ι) (r := finrank k Q) q b hq hclosure)

end OrbitComposition

end ArakelovGeometry.InvariantTheory
