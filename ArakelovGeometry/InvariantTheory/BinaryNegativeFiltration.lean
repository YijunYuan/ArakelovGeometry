/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import ArakelovGeometry.InvariantTheory.PolynomialSolutionDescent
public import ArakelovGeometry.InvariantTheory.BinaryOrbitCoordinates
public import ArakelovGeometry.InvariantTheory.DVRWeights
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.QuotientDegree

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

end ArakelovGeometry.InvariantTheory
