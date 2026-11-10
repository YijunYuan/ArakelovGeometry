/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.TensorNorm
import ArakelovGeometry.Analysis.CountableNormEvaluation
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Countable exact projective tensor decompositions

Enlarging a countable rational subfield by finitely many tensor coordinates
keeps it countable. Rational approximations can then be corrected exactly in
the tensor basis, with correction cost tending to zero.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

variable {K : Type*} [Field K]

/-- Closing a countable set under field operations remains countable. -/
theorem countable_subfield_closure (s : Set K) (hs : s.Countable) :
    Countable (Subfield.closure s) := by
  let : Countable s := hs.to_subtype
  exact Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max s).trans (max_le Cardinal.mk_le_aleph0 le_rfl))

/-- Adjoining finitely many tensor coordinates preserves countability and
contains the original subfield and every requested coordinate. -/
theorem exists_countable_subfield_ge_range (K₀ : Subfield K) [Countable K₀]
    {α : Type*} [Finite α] (a : α → K) :
    ∃ K₁ : Subfield K, Countable K₁ ∧ K₀ ≤ K₁ ∧ ∀ i, a i ∈ K₁ := by
  let T : Set K := (K₀ : Set K) ∪ Set.range a
  refine ⟨Subfield.closure T,
    countable_subfield_closure T ((Set.to_countable _).union (Set.countable_range a)), ?_, ?_⟩
  · exact fun x hx => Subfield.subset_closure (Or.inl hx)
  · exact fun i => Subfield.subset_closure (Or.inr (Set.mem_range_self i))

section Coordinates

variable {R L ι : Type*} [Field R] [Field L] [Fintype ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module L (V i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)]
  (b : ∀ i, Module.Basis (κ i) L (V i)) (σ : R →+* L)

/-- A tuple of rational coordinates, interpreted in the prescribed normed factors. -/
def tensorCoordinateVector (c : ∀ i, κ i → R) : ∀ i, V i :=
  fun i => (b i).equivFun.symm (fun j => σ (c i j))

/-- A finite scalar-weighted pure-tensor decomposition in rational coordinates. -/
def tensorCoordinateSum (p : List (R × (∀ i, κ i → R))) : ⨂[L] i, V i :=
  (p.map fun q => σ q.1 • ⨂ₜ[L] i, tensorCoordinateVector b σ q.2 i).sum

/-- Coefficients of the finite tensor decomposition are polynomials in its
rational scalar and factor coordinates. -/
def tensorCoordinateCoefficients (p : List (R × (∀ i, κ i → R))) (j : ∀ i, κ i) : R :=
  (p.map fun q => q.1 * ∏ i, q.2 i (j i)).sum

/-- The tensor with a prescribed rational coordinate vector in the tensor basis. -/
def tensorFromCoordinates (c : (∀ i, κ i) → R) : ⨂[L] i, V i :=
  (Basis.piTensorProduct b).equivFun.symm (fun j => σ (c j))

/-- Completed tensor coordinates are the images of the rational coefficient polynomials. -/
theorem tensorCoordinateSum_equivFun (p : List (R × (∀ i, κ i → R))) (j : ∀ i, κ i) :
    (Basis.piTensorProduct b).equivFun (tensorCoordinateSum b σ p) j =
      σ (tensorCoordinateCoefficients p j) := by
  induction p with
  | nil => simp [tensorCoordinateSum, tensorCoordinateCoefficients]
  | cons q p hp =>
    simp only [tensorCoordinateSum, tensorCoordinateCoefficients, List.map_cons, List.sum_cons,
      map_add, map_mul, map_prod, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (Basis.piTensorProduct b).equivFun
        (⨂ₜ[L] i, tensorCoordinateVector b σ q.2 i) j = ∏ i, σ (q.2 i (j i)) by
      simp only [Module.Basis.equivFun_apply, Basis.piTensorProduct_repr_tprod_apply]
      apply Finset.prod_congr rfl
      intro i _
      change (b i).equivFun ((b i).equivFun.symm _) (j i) = _
      rw [LinearEquiv.apply_symm_apply]]
    exact congrArg (fun t => σ q.1 * (∏ i, σ (q.2 i (j i))) + t) hp

/-- Unit coordinate tuples giving the factor basis vectors of a tensor basis vector. -/
def tensorBasisCoordinates (j : ∀ i, κ i) : ∀ i, κ i → R := by
  classical
  exact fun i => Pi.single (j i) 1

omit [Fintype ι] in
@[simp]
theorem tensorCoordinateVector_basis (j : ∀ i, κ i) (i : ι) :
    tensorCoordinateVector b σ (tensorBasisCoordinates j) i = b i (j i) := by
  classical
  simp [tensorCoordinateVector, tensorBasisCoordinates,
    Module.Basis.equivFun_symm_apply, Pi.single_apply]

/-- The finite tensor-basis decomposition of a coordinate vector. -/
def tensorCoordinateCorrection (c : (∀ i, κ i) → R) : List (R × (∀ i, κ i → R)) := by
  classical
  exact Finset.univ.toList.map fun j => (c j, tensorBasisCoordinates j)

/-- Coordinate correction is an exact decomposition of the prescribed tensor. -/
theorem tensorCoordinateSum_correction (c : (∀ i, κ i) → R) :
    tensorCoordinateSum b σ (tensorCoordinateCorrection c) = tensorFromCoordinates b σ c := by
  classical
  simp only [tensorCoordinateSum, tensorCoordinateCorrection, List.map_map, Function.comp_def,
    tensorCoordinateVector_basis, Finset.sum_map_toList, tensorFromCoordinates,
    Module.Basis.equivFun_symm_apply, Basis.piTensorProduct_apply]

/-- Appending the rational coefficient error corrects a decomposition exactly. -/
theorem tensorCoordinateSum_corrected (c : (∀ i, κ i) → R)
    (p : List (R × (∀ i, κ i → R))) :
    tensorCoordinateSum b σ (p ++ tensorCoordinateCorrection
      (fun j => c j - tensorCoordinateCoefficients p j)) = tensorFromCoordinates b σ c := by
  apply (Basis.piTensorProduct b).equivFun.injective
  ext j
  simp only [tensorCoordinateSum, List.map_append, List.sum_append, map_add, Pi.add_apply]
  change (Basis.piTensorProduct b).equivFun (tensorCoordinateSum b σ p) j +
    (Basis.piTensorProduct b).equivFun (tensorCoordinateSum b σ
      (tensorCoordinateCorrection (fun j => c j - tensorCoordinateCoefficients p j))) j = _
  rw [tensorCoordinateSum_equivFun, tensorCoordinateSum_correction]
  simp only [tensorFromCoordinates, LinearEquiv.apply_symm_apply, map_sub, add_sub_cancel]

/-- Exact rational tensor equality is equivalent to exact rational coefficient equality. -/
theorem tensorCoordinateSum_eq_iff (c : (∀ i, κ i) → R)
    (p : List (R × (∀ i, κ i → R))) :
    tensorCoordinateSum b σ p = tensorFromCoordinates b σ c ↔
      tensorCoordinateCoefficients p = c := by
  constructor
  · intro h
    ext j
    apply σ.injective
    have hj := congrArg (fun z => (Basis.piTensorProduct b).equivFun z j) h
    simpa only [tensorCoordinateSum_equivFun, tensorFromCoordinates,
      LinearEquiv.apply_symm_apply] using hj
  · intro h
    apply (Basis.piTensorProduct b).equivFun.injective
    ext j
    simp only [tensorCoordinateSum_equivFun, h, tensorFromCoordinates,
      LinearEquiv.apply_symm_apply]

end Coordinates

section NormedCoordinates

variable {R L ι : Type*} [Field R] [NormedField L] [Fintype ι] [DecidableEq ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace L (V i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)]
  (b : ∀ i, Module.Basis (κ i) L (V i)) (σ : R →+* L)

/-- The projective cost of the actual rational-coordinate decomposition. -/
def tensorCoordinateCost (p : List (R × (∀ i, κ i → R))) : ℝ :=
  (p.map fun q => ‖σ q.1‖ * ∏ i, ‖tensorCoordinateVector b σ q.2 i‖).sum

/-- The exact correction cost is a finite sum of absolute coordinate errors
times fixed products of factor-basis norms. -/
theorem tensorCoordinateCost_correction (c : (∀ i, κ i) → R) :
    tensorCoordinateCost b σ (tensorCoordinateCorrection c) =
      ∑ j, ‖σ (c j)‖ * ∏ i, ‖b i (j i)‖ := by
  classical
  simp only [tensorCoordinateCost, tensorCoordinateCorrection, List.map_map, Function.comp_def,
    tensorCoordinateVector_basis, Finset.sum_map_toList]
  congr 1
  ext j
  simp

/-- Corrected decomposition costs split into the approximation cost and a
finite coordinate-error cost. -/
theorem tensorCoordinateCost_corrected (c : (∀ i, κ i) → R)
    (p : List (R × (∀ i, κ i → R))) :
    tensorCoordinateCost b σ (p ++ tensorCoordinateCorrection
      (fun j => c j - tensorCoordinateCoefficients p j)) =
      tensorCoordinateCost b σ p +
        ∑ j, ‖σ (c j) - σ (tensorCoordinateCoefficients p j)‖ * ∏ i, ‖b i (j i)‖ := by
  simp only [tensorCoordinateCost, List.map_append, List.sum_append]
  rw [show ((tensorCoordinateCorrection (fun j => c j - tensorCoordinateCoefficients p j)).map
      fun q => ‖σ q.1‖ * ∏ i, ‖tensorCoordinateVector b σ q.2 i‖).sum =
      ∑ j, ‖σ (c j - tensorCoordinateCoefficients p j)‖ * ∏ i, ‖b i (j i)‖ from
        tensorCoordinateCost_correction b σ _]
  simp only [map_sub]

omit [DecidableEq ι] in
/-- Every coordinate decomposition bounds the actual projective norm. -/
theorem projectiveSeminorm_tensorCoordinateSum_le_cost
    (p : List (R × (∀ i, κ i → R))) :
    PiTensorProduct.projectiveSeminorm (tensorCoordinateSum b σ p) ≤
      tensorCoordinateCost b σ p := by
  induction p with
  | nil => simp [tensorCoordinateSum, tensorCoordinateCost]
  | cons q p hp =>
    simp only [tensorCoordinateSum, tensorCoordinateCost, List.map_cons, List.sum_cons]
    apply (map_add_le_add _ _ _).trans
    apply add_le_add _ hp
    rw [map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (PiTensorProduct.projectiveSeminorm_tprod_le _) (norm_nonneg _)

omit [DecidableEq ι] in
/-- Decomposition costs are nonnegative, including the empty decomposition. -/
theorem tensorCoordinateCost_nonneg (p : List (R × (∀ i, κ i → R))) :
    0 ≤ tensorCoordinateCost b σ p := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

omit [DecidableEq ι] in
/-- For a fixed decomposition length, the projective cost is continuous in all
scalar and factor coordinates. -/
theorem continuous_tensorCoordinateCost (n : ℕ) :
    Continuous (fun q : Fin n → L × (∀ i, κ i → L) =>
      tensorCoordinateCost b (RingHom.id L) (List.ofFn q)) := by
  simp only [tensorCoordinateCost, List.map_ofFn, List.sum_ofFn, RingHom.id_apply,
    tensorCoordinateVector, Module.Basis.equivFun_symm_apply]
  fun_prop

omit [DecidableEq ι] [∀ i, Fintype (κ i)] in
/-- Each coefficient polynomial of a fixed-length decomposition is continuous. -/
theorem continuous_tensorCoordinateCoefficients (n : ℕ) (j : ∀ i, κ i) :
    Continuous (fun q : Fin n → L × (∀ i, κ i → L) =>
      tensorCoordinateCoefficients (List.ofFn q) j) := by
  simp only [tensorCoordinateCoefficients, List.map_ofFn, List.sum_ofFn]
  fun_prop

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)] in
/-- Simultaneous scalar and factor-coordinate approximation uses the same dense subfield. -/
theorem denseRange_tensorCoordinateParameters (hσ : DenseRange σ) (n : ℕ) :
    DenseRange (fun q : Fin n → R × (∀ i, κ i → R) => fun a =>
      (σ (q a).1, fun i j => σ ((q a).2 i j))) := by
  exact DenseRange.piMap (fun _ => hσ.prodMap
    (DenseRange.piMap fun _ => DenseRange.piMap fun _ => hσ))

omit [DecidableEq ι] in
/-- A lower bound on exact rational-coordinate costs is a lower bound on the
actual projective norm. The proof approximates an arbitrary completed
decomposition and corrects its tensor coordinates exactly. -/
theorem le_projectiveSeminorm_of_le_tensorCoordinateCost (hσ : DenseRange σ)
    (c : (∀ i, κ i) → R) (C : ℝ)
    (hC : ∀ p : List (R × (∀ i, κ i → R)),
      tensorCoordinateCoefficients p = c → C ≤ tensorCoordinateCost b σ p) :
    C ≤ PiTensorProduct.projectiveSeminorm (tensorFromCoordinates b σ c) := by
  classical
  have hb (n : ℕ) (q : Fin n → L × (∀ i, κ i → L)) :
      C ≤ tensorCoordinateCost b (RingHom.id L) (List.ofFn q) +
        ∑ j, ‖σ (c j) - tensorCoordinateCoefficients (List.ofFn q) j‖ *
          ∏ i, ‖b i (j i)‖ := by
    let F : (Fin n → L × (∀ i, κ i → L)) → ℝ := fun q =>
      tensorCoordinateCost b (RingHom.id L) (List.ofFn q) +
        ∑ j, ‖σ (c j) - tensorCoordinateCoefficients (List.ofFn q) j‖ *
          ∏ i, ‖b i (j i)‖
    have hcont : Continuous F := by
      apply (continuous_tensorCoordinateCost b n).add
      apply continuous_finsetSum
      intro j _
      exact ((continuous_const.sub
        (continuous_tensorCoordinateCoefficients n j)).norm).mul continuous_const
    apply (denseRange_tensorCoordinateParameters σ hσ n).induction_on
      (p := fun q => C ≤ F q) q (isClosed_le continuous_const hcont)
    intro a
    have ha := hC ((List.ofFn a) ++ tensorCoordinateCorrection
        (fun j => c j - tensorCoordinateCoefficients (List.ofFn a) j))
      ((tensorCoordinateSum_eq_iff b σ c _).mp
        (tensorCoordinateSum_corrected b σ c (List.ofFn a)))
    rw [tensorCoordinateCost_corrected] at ha
    simpa only [F, tensorCoordinateCost, tensorCoordinateVector,
      tensorCoordinateCoefficients, List.map_ofFn, List.sum_ofFn, RingHom.id_apply,
      Function.comp_def, map_sum, map_mul, map_prod] using ha
  change C ≤ ‖tensorFromCoordinates b σ c‖
  rw [PiTensorProduct.norm_def]
  apply le_ciInf
  rintro ⟨p, hp⟩
  let l : List (L × (∀ i, κ i → L)) :=
    p.toList.map fun a => (a.1, fun i => (b i).equivFun (a.2 i))
  have hs : tensorCoordinateSum b (RingHom.id L) l = tensorFromCoordinates b σ c := by
    simpa only [l, tensorCoordinateSum, tensorCoordinateVector, List.map_map,
      Function.comp_def, RingHom.id_apply, LinearEquiv.symm_apply_apply] using
      (PiTensorProduct.mem_lifts_iff _ p).mp hp
  have hc (j : ∀ i, κ i) : tensorCoordinateCoefficients l j = σ (c j) := by
    have hj := congrArg (fun z => (Basis.piTensorProduct b).equivFun z j) hs
    simpa only [tensorCoordinateSum_equivFun, RingHom.id_apply, tensorFromCoordinates,
      LinearEquiv.apply_symm_apply] using hj
  have hh := hb l.length l.get
  simp only [List.ofFn_get, hc, sub_self, norm_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at hh
  simpa only [tensorCoordinateCost, tensorCoordinateVector, l, List.map_map,
    Function.comp_def, RingHom.id_apply, LinearEquiv.symm_apply_apply,
    PiTensorProduct.projectiveSeminormAux] using hh

omit [DecidableEq ι] in
/-- The actual projective norm is the infimum over exact subfield-coordinate
finite decompositions. When the subfield is countable, the indexing type is
countable. Scalar weights retain the empty tensor-product case. -/
theorem projectiveSeminorm_eq_iInf_tensorCoordinateCost (hσ : DenseRange σ)
    (c : (∀ i, κ i) → R) :
    PiTensorProduct.projectiveSeminorm (tensorFromCoordinates b σ c) =
      ⨅ p : {p : List (R × (∀ i, κ i → R)) // tensorCoordinateCoefficients p = c},
        tensorCoordinateCost b σ p.val := by
  let : Nonempty {p : List (R × (∀ i, κ i → R)) //
      tensorCoordinateCoefficients p = c} :=
    ⟨⟨tensorCoordinateCorrection c,
      (tensorCoordinateSum_eq_iff b σ c _).mp (tensorCoordinateSum_correction b σ c)⟩⟩
  apply le_antisymm
  · apply le_ciInf
    intro p
    rw [← (tensorCoordinateSum_eq_iff b σ c p.val).mpr p.property]
    exact projectiveSeminorm_tensorCoordinateSum_le_cost b σ p.val
  · apply le_projectiveSeminorm_of_le_tensorCoordinateCost b σ hσ c
    intro p hp
    apply ciInf_le (f := fun q : {q : List (R × (∀ i, κ i → R)) //
      tensorCoordinateCoefficients q = c} => tensorCoordinateCost b σ q.val) ?_ ⟨p, hp⟩
    exact ⟨0, by rintro _ ⟨q, rfl⟩; exact tensorCoordinateCost_nonneg b σ q.val⟩

end NormedCoordinates

end ArakelovGeometry
