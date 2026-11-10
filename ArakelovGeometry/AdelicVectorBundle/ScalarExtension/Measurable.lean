/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.Basic
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Free
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
import ArakelovGeometry.AdelicVectorBundle.Measurability.Density.FiniteExtension
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Rational
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Dual.Basic
import ArakelovGeometry.Analysis.NormedSpace.CountableNormEvaluation
import ArakelovGeometry.Analysis.Tensor.CountableTensorFormula
import Mathlib.CategoryTheory.Category.Init

/-!
# Measurability of actual scalar-extension norms

A common countable subfield of the base field gives a countable supremum
formula for the injective scalar-extension norm on the actual completed
fibres. Measurability of fixed extended-field evaluations and original dual
norm evaluations then proves measurability of the injective extension.

The dual of projective scalar extension is computed by restriction to the
original completed vector space. Countable base vector tests prove its
measurability for arbitrary algebraic extensions as well.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

private theorem projective_operator_norm_eq_restriction
    {k l V : Type*} [NormedField k] [CompleteSpace k]
    [NormedField l] [CompleteSpace l] [NormedAlgebra k l]
    [NormedAddCommGroup V] [NormedSpace k V] [FiniteDimensional k V]
    (f : l ⊗[k] V →ₗ[l] l) :
    let g := (f.restrictScalars k).comp (TensorProduct.mk k l V (1 : l))
    letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := l) (E := V)
    letI := scalarExtensionProjectiveNormedSpace (k := k) (L := l) (E := V)
    linearMapOperatorSeminorm f = linearMapOperatorSeminorm g := by
  intro g
  let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := l) (E := V)
  let := scalarExtensionProjectiveNormedSpace (k := k) (L := l) (E := V)
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    let C := linearMapOperatorSeminorm g + ε
    have hC : 0 < C := add_pos_of_nonneg_of_pos (apply_nonneg _ _) hε
    let p : Seminorm l (l ⊗[k] V) :=
      NNReal.mk C⁻¹ (inv_nonneg.mpr hC.le) • (normSeminorm l l).comp f
    have hp : p ≤ scalarExtensionProjectiveSeminorm := by
      apply le_scalarExtensionProjectiveSeminorm
      intro x
      change C⁻¹ * ‖g x‖ ≤ ‖x‖
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_iff₀ hC).mpr
      simpa only [mul_comm] using (norm_linearMap_apply_le g x).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hε.le) (norm_nonneg x))
    apply linearMapOperatorSeminorm_le f hC.le
    intro z
    have hz := hp z
    change C⁻¹ * ‖f z‖ ≤ ‖z‖ at hz
    rw [mul_comm, ← div_eq_mul_inv] at hz
    simpa only [mul_comm] using (div_le_iff₀ hC).mp hz
  · apply linearMapOperatorSeminorm_le g (apply_nonneg _ _)
    intro x
    change ‖f ((1 : l) ⊗ₜ[k] x)‖ ≤ linearMapOperatorSeminorm f * ‖x‖
    exact (norm_linearMap_apply_le f ((1 : l) ⊗ₜ[k] x)).trans
      (mul_le_mul_of_nonneg_left (scalarExtensionProjectiveSeminorm_one_tmul_le x)
        (apply_nonneg _ _))

section ScalarCoordinates

variable {R T k l V ι : Type*} [Field R] [Field T] [Field k] [Field l]
  [Algebra k l] [AddCommGroup V] [Module k V] [Fintype ι]
  (b : Module.Basis ι k V) (σ : R →+* k) (τ : T →+* l) (ρ : R →+* T)

/-- A base vector with coordinates in a prescribed rational subfield. -/
def scalarCoordinateVector (c : ι → R) : V :=
  b.equivFun.symm (fun j => σ (c j))

/-- An exact scalar-extension decomposition in two rational coordinate fields. -/
def scalarCoordinateSum (p : List (T × (ι → R))) : l ⊗[k] V :=
  (p.map fun q => τ q.1 ⊗ₜ[k] scalarCoordinateVector b σ q.2).sum

/-- Scalar-extension coefficients are polynomial in the scalar and vector coordinates. -/
def scalarCoordinateCoefficients (p : List (T × (ι → R))) (j : ι) : T :=
  (p.map fun q => q.1 * ρ (q.2 j)).sum

/-- A scalar-extension vector given by rational coordinates in its actual base-changed basis. -/
def scalarFromCoordinates (c : ι → T) : l ⊗[k] V :=
  (b.baseChange l).equivFun.symm (fun j => τ (c j))

theorem scalarCoordinateSum_equivFun
    (hστ : ∀ a, algebraMap k l (σ a) = τ (ρ a))
    (p : List (T × (ι → R))) (j : ι) :
    (b.baseChange l).equivFun (scalarCoordinateSum b σ τ p) j =
      τ (scalarCoordinateCoefficients ρ p j) := by
  induction p with
  | nil => simp [scalarCoordinateSum, scalarCoordinateCoefficients]
  | cons q p hp =>
    simp only [scalarCoordinateSum, scalarCoordinateCoefficients, List.map_cons,
      List.sum_cons, map_add, map_mul, Pi.add_apply]
    rw [show (b.baseChange l).equivFun
        (τ q.1 ⊗ₜ[k] scalarCoordinateVector b σ q.2) j =
        τ q.1 * τ (ρ (q.2 j)) by
      simp only [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
      change b.equivFun (b.equivFun.symm _) j • τ q.1 = _
      rw [LinearEquiv.apply_symm_apply, Algebra.smul_def, hστ, mul_comm]]
    exact congrArg (fun t => τ q.1 * τ (ρ (q.2 j)) + t) hp

/-- Unit rational coordinates give the actual original basis vectors. -/
def scalarBasisCoordinates (j : ι) : ι → R := by
  classical
  exact Pi.single j 1

@[simp]
theorem scalarCoordinateVector_single (j : ι) :
    scalarCoordinateVector b σ (scalarBasisCoordinates j) = b j := by
  classical
  simp [scalarCoordinateVector, scalarBasisCoordinates,
    Module.Basis.equivFun_symm_apply, Pi.single_apply]

/-- The canonical finite basis correction uses only the rational scalar coordinates. -/
def scalarCoordinateCorrection (c : ι → T) : List (T × (ι → R)) := by
  classical
  exact Finset.univ.toList.map fun j => (c j, scalarBasisCoordinates j)

theorem scalarCoordinateSum_correction (c : ι → T) :
    scalarCoordinateSum b σ τ (scalarCoordinateCorrection (R := R) c) =
      scalarFromCoordinates b τ c := by
  classical
  simp only [scalarCoordinateSum, scalarCoordinateCorrection, List.map_map,
    Function.comp_def, scalarCoordinateVector_single, Finset.sum_map_toList,
    scalarFromCoordinates, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Appending the rational coordinate error corrects every approximate decomposition exactly. -/
theorem scalarCoordinateSum_corrected
    (hστ : ∀ a, algebraMap k l (σ a) = τ (ρ a))
    (c : ι → T) (p : List (T × (ι → R))) :
    scalarCoordinateSum b σ τ
      (p ++ scalarCoordinateCorrection (fun j => c j - scalarCoordinateCoefficients ρ p j)) =
      scalarFromCoordinates b τ c := by
  apply (b.baseChange l).equivFun.injective
  ext j
  simp only [scalarCoordinateSum, List.map_append, List.sum_append, map_add, Pi.add_apply]
  change (b.baseChange l).equivFun (scalarCoordinateSum b σ τ p) j +
    (b.baseChange l).equivFun (scalarCoordinateSum b σ τ
      (scalarCoordinateCorrection (fun j => c j - scalarCoordinateCoefficients ρ p j))) j = _
  rw [scalarCoordinateSum_equivFun b σ τ ρ hστ, scalarCoordinateSum_correction]
  simp only [scalarFromCoordinates, LinearEquiv.apply_symm_apply, map_sub, add_sub_cancel]

/-- Exact rational equality is equivalent to an exact coordinate constraint independent of place. -/
theorem scalarCoordinateSum_eq_iff
    (hστ : ∀ a, algebraMap k l (σ a) = τ (ρ a))
    (c : ι → T) (p : List (T × (ι → R))) :
    scalarCoordinateSum b σ τ p = scalarFromCoordinates b τ c ↔
      scalarCoordinateCoefficients ρ p = c := by
  constructor
  · intro h
    ext j
    apply τ.injective
    have hj := congrArg (fun z => (b.baseChange l).equivFun z j) h
    simpa only [scalarCoordinateSum_equivFun b σ τ ρ hστ, scalarFromCoordinates,
      LinearEquiv.apply_symm_apply] using hj
  · intro h
    apply (b.baseChange l).equivFun.injective
    ext j
    simp only [scalarCoordinateSum_equivFun b σ τ ρ hστ, h, scalarFromCoordinates,
      LinearEquiv.apply_symm_apply]

end ScalarCoordinates

section NormedScalarCoordinates

variable {R T k l V ι : Type*} [Field R] [Field T] [NormedField k]
  [CompleteSpace k] [NormedField l] [NormedAlgebra k l]
  [NormedAddCommGroup V] [NormedSpace k V] [Fintype ι]
  (b : Module.Basis ι k V) (σ : R →+* k) (τ : T →+* l) (ρ : R →+* T)

/-- The actual projective cost of a rational scalar-extension decomposition. -/
def scalarCoordinateCost (p : List (T × (ι → R))) : ℝ :=
  (p.map fun q => ‖τ q.1‖ * ‖scalarCoordinateVector b σ q.2‖).sum

omit [CompleteSpace k] [NormedAlgebra k l] in
theorem scalarCoordinateCost_correction (c : ι → T) :
    scalarCoordinateCost b σ τ (scalarCoordinateCorrection (R := R) c) =
      ∑ j, ‖τ (c j)‖ * ‖b j‖ := by
  classical
  simp only [scalarCoordinateCost, scalarCoordinateCorrection, List.map_map,
    Function.comp_def, scalarCoordinateVector_single, Finset.sum_map_toList]

omit [CompleteSpace k] [NormedAlgebra k l] in
theorem scalarCoordinateCost_corrected (c : ι → T) (p : List (T × (ι → R))) :
    scalarCoordinateCost b σ τ
      (p ++ scalarCoordinateCorrection (fun j => c j - scalarCoordinateCoefficients ρ p j)) =
      scalarCoordinateCost b σ τ p +
        ∑ j, ‖τ (c j) - τ (scalarCoordinateCoefficients ρ p j)‖ * ‖b j‖ := by
  simp only [scalarCoordinateCost, List.map_append, List.sum_append]
  rw [show ((scalarCoordinateCorrection (fun j => c j - scalarCoordinateCoefficients ρ p j)).map
      fun q => ‖τ q.1‖ * ‖scalarCoordinateVector b σ q.2‖).sum =
      ∑ j, ‖τ (c j - scalarCoordinateCoefficients ρ p j)‖ * ‖b j‖ from
        scalarCoordinateCost_correction b σ τ _]
  simp only [map_sub]

omit [CompleteSpace k] in
/-- Each exact decomposition bounds the actual projective scalar-extension norm. -/
theorem scalarExtensionProjectiveSeminorm_scalarCoordinateSum_le_cost
    (p : List (T × (ι → R))) :
    scalarExtensionProjectiveSeminorm (scalarCoordinateSum b σ τ p) ≤
      scalarCoordinateCost b σ τ p := by
  induction p with
  | nil => simp [scalarCoordinateSum, scalarCoordinateCost]
  | cons q p hp =>
    simp only [scalarCoordinateSum, scalarCoordinateCost, List.map_cons, List.sum_cons]
    exact (map_add_le_add _ _ _).trans
      (add_le_add (scalarExtensionProjectiveSeminorm_tmul_le _ _) hp)

omit [CompleteSpace k] [NormedAlgebra k l] in
theorem scalarCoordinateCost_nonneg (p : List (T × (ι → R))) :
    0 ≤ scalarCoordinateCost b σ τ p := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

omit [CompleteSpace k] [NormedAlgebra k l] in
/-- A fixed-length projective cost is continuous in both sets of completed coordinates. -/
theorem continuous_scalarCoordinateCost (n : ℕ) :
    Continuous (fun q : Fin n → l × (ι → k) =>
      scalarCoordinateCost b (RingHom.id k) (RingHom.id l) (List.ofFn q)) := by
  simp only [scalarCoordinateCost, List.map_ofFn, List.sum_ofFn, RingHom.id_apply,
    scalarCoordinateVector, Module.Basis.equivFun_symm_apply]
  fun_prop

omit [CompleteSpace k] [Fintype ι] in
/-- Coefficient polynomials are continuous even when the two coordinate fields differ. -/
theorem continuous_scalarCoordinateCoefficients (n : ℕ) (j : ι) :
    Continuous (fun q : Fin n → l × (ι → k) =>
      scalarCoordinateCoefficients (algebraMap k l) (List.ofFn q) j) := by
  simp only [scalarCoordinateCoefficients, List.map_ofFn, List.sum_ofFn]
  fun_prop

omit [CompleteSpace k] [NormedAlgebra k l] [Fintype ι] in
/-- Both dense coordinate fields approximate the parameters simultaneously. -/
theorem denseRange_scalarCoordinateParameters (hσ : DenseRange σ) (hτ : DenseRange τ)
    (n : ℕ) :
    DenseRange (fun q : Fin n → T × (ι → R) =>
      fun a => (τ (q a).1, fun j => σ ((q a).2 j))) :=
  DenseRange.piMap (fun _ => hτ.prodMap (DenseRange.piMap fun _ => hσ))

omit [CompleteSpace k] in
/-- Lower bounds on exact rational costs bound the actual projective scalar-extension norm.
Completed decompositions are approximated in both coordinate fields and corrected exactly. -/
theorem le_scalarExtensionProjectiveSeminorm_of_le_scalarCoordinateCost
    (hσ : DenseRange σ) (hτ : DenseRange τ)
    (hστ : ∀ a, algebraMap k l (σ a) = τ (ρ a)) (c : ι → T) (C : ℝ)
    (hC : ∀ p : List (T × (ι → R)),
      scalarCoordinateCoefficients ρ p = c → C ≤ scalarCoordinateCost b σ τ p) :
    C ≤ scalarExtensionProjectiveSeminorm (scalarFromCoordinates b τ c) := by
  classical
  have hb (n : ℕ) (q : Fin n → l × (ι → k)) :
      C ≤ scalarCoordinateCost b (RingHom.id k) (RingHom.id l) (List.ofFn q) +
        ∑ j, ‖τ (c j) - scalarCoordinateCoefficients (algebraMap k l) (List.ofFn q) j‖ *
          ‖b j‖ := by
    let F : (Fin n → l × (ι → k)) → ℝ := fun q =>
      scalarCoordinateCost b (RingHom.id k) (RingHom.id l) (List.ofFn q) +
        ∑ j, ‖τ (c j) - scalarCoordinateCoefficients (algebraMap k l) (List.ofFn q) j‖ *
          ‖b j‖
    have hcont : Continuous F := by
      apply (continuous_scalarCoordinateCost b n).add
      apply continuous_finsetSum
      intro j _
      exact ((continuous_const.sub
        (continuous_scalarCoordinateCoefficients n j)).norm).mul continuous_const
    apply (denseRange_scalarCoordinateParameters σ τ hσ hτ n).induction_on
      (p := fun q => C ≤ F q) q (isClosed_le continuous_const hcont)
    intro a
    have ha := hC ((List.ofFn a) ++ scalarCoordinateCorrection
        (fun j => c j - scalarCoordinateCoefficients ρ (List.ofFn a) j))
      ((scalarCoordinateSum_eq_iff b σ τ ρ hστ c _).mp
        (scalarCoordinateSum_corrected b σ τ ρ hστ c (List.ofFn a)))
    rw [scalarCoordinateCost_corrected] at ha
    simpa only [F, scalarCoordinateCost, scalarCoordinateVector, scalarCoordinateCoefficients,
      List.map_ofFn, List.sum_ofFn, RingHom.id_apply, Function.comp_def, map_sum,
      map_mul, hστ] using ha
  rw [scalarExtensionProjectiveSeminorm_eq_sInf]
  have hn : Set.Nonempty {d : ℝ | ∃ p : List (l × V),
      (p.map fun q => q.1 ⊗ₜ[k] q.2).sum = scalarFromCoordinates b τ c ∧
        (p.map fun q => ‖q.1‖ * ‖q.2‖).sum = d} := by
    let p := (scalarCoordinateCorrection (R := R) c).map
      fun q => (τ q.1, scalarCoordinateVector b σ q.2)
    refine ⟨(p.map fun q => ‖q.1‖ * ‖q.2‖).sum, p, ?_, rfl⟩
    simpa only [p, List.map_map, Function.comp_def, scalarCoordinateSum] using
      scalarCoordinateSum_correction b σ τ c
  apply le_csInf hn
  rintro _ ⟨p, hp, rfl⟩
  let q : List (l × (ι → k)) := p.map fun a => (a.1, b.equivFun a.2)
  have hs : scalarCoordinateSum b (RingHom.id k) (RingHom.id l) q =
      scalarFromCoordinates b τ c := by
    simpa only [q, scalarCoordinateSum, scalarCoordinateVector, List.map_map,
      Function.comp_def, RingHom.id_apply, LinearEquiv.symm_apply_apply] using hp
  have hc (j : ι) :
      scalarCoordinateCoefficients (algebraMap k l) q j = τ (c j) := by
    have hj := congrArg (fun z => (b.baseChange l).equivFun z j) hs
    simpa only [scalarCoordinateSum_equivFun b (RingHom.id k) (RingHom.id l)
        (algebraMap k l) (fun _ => rfl), RingHom.id_apply, scalarFromCoordinates,
      LinearEquiv.apply_symm_apply] using hj
  have hh := hb q.length q.get
  simp only [List.ofFn_get, hc, sub_self, norm_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at hh
  simpa only [scalarCoordinateCost, scalarCoordinateVector, q, List.map_map,
    Function.comp_def, RingHom.id_apply, LinearEquiv.symm_apply_apply] using hh

omit [CompleteSpace k] in
/-- The actual projective scalar-extension norm is an infimum over exact rational costs.
Countable coordinate fields give a countable indexing type, including rank zero. -/
theorem scalarExtensionProjectiveSeminorm_eq_iInf_scalarCoordinateCost
    (hσ : DenseRange σ) (hτ : DenseRange τ)
    (hστ : ∀ a, algebraMap k l (σ a) = τ (ρ a)) (c : ι → T) :
    scalarExtensionProjectiveSeminorm (scalarFromCoordinates b τ c) =
      ⨅ p : {p : List (T × (ι → R)) // scalarCoordinateCoefficients ρ p = c},
        scalarCoordinateCost b σ τ p.val := by
  let : Nonempty {p : List (T × (ι → R)) // scalarCoordinateCoefficients ρ p = c} :=
    ⟨⟨scalarCoordinateCorrection c,
      (scalarCoordinateSum_eq_iff b σ τ ρ hστ c _).mp
        (scalarCoordinateSum_correction b σ τ c)⟩⟩
  apply le_antisymm
  · apply le_ciInf
    intro p
    rw [← (scalarCoordinateSum_eq_iff b σ τ ρ hστ c p.val).mpr p.property]
    exact scalarExtensionProjectiveSeminorm_scalarCoordinateSum_le_cost b σ τ p.val
  · apply le_scalarExtensionProjectiveSeminorm_of_le_scalarCoordinateCost b σ τ ρ hσ hτ hστ c
    intro p hp
    apply ciInf_le (f := fun q : {q : List (T × (ι → R)) //
      scalarCoordinateCoefficients ρ q = c} => scalarCoordinateCost b σ τ q.val) ?_ ⟨p, hp⟩
    exact ⟨0, by rintro _ ⟨q, rfl⟩; exact scalarCoordinateCost_nonneg b σ τ q.val⟩

end NormedScalarCoordinates

end ArakelovGeometry

namespace ArakelovGeometry.NormFamily

universe u v w wE wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)

/-- An extended completed vector evaluates the original completed dual.
Linearity is over the original completed field, with its canonical embedding
into the extending completion. -/
def completedScalarExtensionDualEvaluation (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ((S.ϕ x.base).Completion ⊗[K] Module.Dual K E) →ₗ[(S.ϕ x.base).Completion]
      x.abv.Completion := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let y := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z
  refine {
    toFun := fun f => scalarExtensionDualEval
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E f) y
    map_add' := fun f g => ?_
    map_smul' := fun a f => ?_ }
  · induction y using TensorProduct.inductionOn with
    | tmul a t => simp [scalarExtensionDualEval_tmul, mul_add]
    | add y t hy ht =>
      simp only [map_add] at hy ht ⊢
      rw [hy, ht]
      ring
  · induction y using TensorProduct.inductionOn with
    | tmul b t =>
      simp [scalarExtensionDualEval_tmul, Algebra.smul_def, mul_left_comm]
    | add y t hy ht => simp only [map_add, hy, ht, smul_add]

/-- The injective scalar-extension norm is the operator norm of evaluation
on the actual original completed dual. -/
theorem injectiveScalarExtension_norm_eq_operatorSeminorm
    (x : S.ParameterSpaceExtension L) (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := ξ.dual.fibreNormedAddCommGroup x.base
    letI := ξ.dual.fibreNormedSpace x.base
    (ξ.injectiveScalarExtension (L := L)).norm x z =
      linearMapOperatorSeminorm (ξ.completedScalarExtensionDualEvaluation x z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := ξ.dual.fibreNormedAddCommGroup x.base
  let := ξ.dual.fibreNormedSpace x.base
  let d := dualBaseChangeEquiv K (S.ϕ x.base).Completion E
  let y := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z
  change scalarExtensionInjectiveSeminorm y =
    linearMapOperatorSeminorm (ξ.completedScalarExtensionDualEvaluation x z)
  rw [scalarExtensionInjectiveSeminorm_eq_sSup, linearMapOperatorSeminorm_eq_sSup]
  congr 1
  ext c
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨d.symm f, ?_⟩
    change ‖scalarExtensionDualEval (d (d.symm f)) y‖ /
      linearMapOperatorSeminorm (d (d.symm f)) = _
    rw [d.apply_symm_apply]
  · rintro ⟨f, rfl⟩
    exact ⟨d f, rfl⟩

variable {ι : Type wι} [Fintype ι]

/-- The countable dense original dual computes the injective norm on every
actual completed extended vector. The zero tuple contributes zero. -/
theorem injectiveScalarExtension_norm_eq_iSup_basisSubfield
    (b : Module.Basis ι K (Module.Dual K E)) (K₀ : Subfield K)
    (x : S.ParameterSpaceExtension L) (hK₀ : S.IsDenseSubfieldAt K₀ x.base)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.injectiveScalarExtension (L := L)).norm x z = ⨆ c : ι → K₀,
      ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
        ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L (basisSubfieldMap b K₀ c)) z‖ /
        ξ.dual.norm x.base
          ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := ξ.dual.fibreNormedAddCommGroup x.base
  let := ξ.dual.fibreNormedSpace x.base
  have he (f : ((S.ϕ x.base).Completion ⊗[K] E) →ₗ[(S.ϕ x.base).Completion]
      (S.ϕ x.base).Completion) :
      scalarExtensionDualEval (L := x.abv.Completion) f =
        Module.Dual.baseChange x.abv.Completion f := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    simp [scalarExtensionDualEval_tmul, Module.Dual.baseChange, Algebra.smul_def, mul_comm]
  rw [ξ.injectiveScalarExtension_norm_eq_operatorSeminorm]
  rw [linearMapOperatorSeminorm_eq_sSup_of_denseRange
    (ξ.completedScalarExtensionDualEvaluation x z) _
    (ξ.dual.denseRange_basisSubfieldMap b K₀ x.base hK₀)]
  apply iSup_congr
  intro c
  change ‖scalarExtensionDualEval
      (dualBaseChangeEquiv K (S.ϕ x.base).Completion E
        ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c))
      (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z)‖ / _ = _
  rw [he, completedScalarExtensionEquiv_baseChange_dual_apply]
  rfl

/-- For a fixed extended rational vector the numerator of the countable
formula is an absolute-value evaluation of one fixed element of the extension. -/
theorem injectiveScalarExtension_norm_rational_eq_iSup_basisSubfield
    (b : Module.Basis ι K (Module.Dual K E)) (K₀ : Subfield K)
    (x : S.ParameterSpaceExtension L) (hK₀ : S.IsDenseSubfieldAt K₀ x.base)
    (z : L ⊗[K] E) :
    (ξ.injectiveScalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L] z) =
      ⨆ c : ι → K₀, x.abv (Module.Dual.baseChange L (basisSubfieldMap b K₀ c) z) /
        ξ.dual.norm x.base
          ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  have hn (a : L) : ‖algebraMap L x.abv.Completion a‖ = x.abv a :=
    (S.algebraicExtension L).norm_algebraMap_eq_absValue x a
  calc
    _ = ⨆ c : ι → K₀,
        ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
          ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L (basisSubfieldMap b K₀ c))
          ((1 : x.abv.Completion) ⊗ₜ[L] z)‖ /
          ξ.dual.norm x.base
            ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) :=
      ξ.injectiveScalarExtension_norm_eq_iSup_basisSubfield b K₀ x hK₀
        ((1 : x.abv.Completion) ⊗ₜ[L] z)
    _ = _ := by
      apply iSup_congr
      intro c
      simp only [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, hn]

/-- Under a single common countable dense base subfield, the actual injective
scalar extension is measurable for every algebraic extension. -/
theorem IsMeasurable.injectiveScalarExtension_of_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω) :
    (ξ.injectiveScalarExtension (L := L)).IsMeasurable := by
  intro z
  let b := Module.finBasis K (Module.Dual K E)
  have hd := hξ.dual_of_countable_dense_subfield K₀ hK₀
  have he : (fun x : S.ParameterSpaceExtension L =>
      (ξ.injectiveScalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L] z)) =
      fun x => ⨆ c : Fin (Module.finrank K (Module.Dual K E)) → K₀,
        x.abv (Module.Dual.baseChange L (basisSubfieldMap b K₀ c) z) /
          ξ.dual.norm x.base
            ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) :=
    funext fun x => ξ.injectiveScalarExtension_norm_rational_eq_iSup_basisSubfield
      b K₀ x (hK₀ x.base) z
  change Measurable[AdelicStructure.Algebraic.projectiveMeasurableSpace S L]
    (fun x : S.ParameterSpaceExtension L =>
    (ξ.injectiveScalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L] z))
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq]
  rw [he]
  exact Measurable.iSup fun c =>
    (AdelicStructure.ParameterSpaceExtension.measurable_eval S L _).div
      ((hd _).comp (AdelicStructure.ParameterSpaceExtension.measurable_proj S L))

/-- The source's existential common-subfield assumption gives actual
injective scalar-extension measurability, including rank zero. -/
theorem IsMeasurable.injectiveScalarExtension_of_common_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.injectiveScalarExtension (L := L)).IsMeasurable := by
  obtain ⟨K₀, hc, hd⟩ := hS
  let : Countable K₀ := hc
  exact hξ.injectiveScalarExtension_of_countable_dense_subfield K₀ hd

/-- The ordinary scalar-extension norm is measurable on its actual finite
place locus, for every algebraic extension. -/
theorem IsMeasurable.scalarExtension_norm_finite
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield)
    (z : L ⊗[K] E) :
    Measurable (fun x : (S.algebraicExtension L).Ωfin =>
      (ξ.scalarExtension (L := L)).norm x.val
        ((1 : ((S.algebraicExtension L).ϕ x.val).Completion) ⊗ₜ[L] z)) := by
  have he : (fun x : (S.algebraicExtension L).Ωfin =>
      (ξ.scalarExtension (L := L)).norm x.val
        ((1 : ((S.algebraicExtension L).ϕ x.val).Completion) ⊗ₜ[L] z)) =
      fun x => (ξ.injectiveScalarExtension (L := L)).norm x.val
        ((1 : ((S.algebraicExtension L).ϕ x.val).Completion) ⊗ₜ[L] z) := by
    funext x
    exact ξ.scalarExtension_norm_of_mem_Ωfin x.val
      ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x.val).mp x.property) _
  rw [he]
  exact ((hξ.injectiveScalarExtension_of_common_countable_dense_subfield
    (L := L) hS) z).comp measurable_subtype_coe

/-- If the original structure has no infinite places, its ordinary scalar
extension is measurable under the source's common-density assumption. -/
theorem IsMeasurable.scalarExtension_of_empty_infinity
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield)
    (hinf : S.Ωinf = ∅) : (ξ.scalarExtension (L := L)).IsMeasurable := by
  classical
  intro z
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      fun x => (ξ.injectiveScalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z) := by
    funext x
    change S.ParameterSpaceExtension L at x
    have hx : x.base ∈ S.Ωfin := by
      by_contra hx
      have hi : x.base ∈ S.Ωinf := hx
      simp only [hinf, Set.mem_empty_iff_false] at hi
    exact ξ.scalarExtension_norm_of_mem_Ωfin x hx _
  rw [he]
  exact (hξ.injectiveScalarExtension_of_common_countable_dense_subfield (L := L) hS) z

/-- Restriction of an actual extended completed dual vector to the original
completed vector space, in canonical scalar-extension coordinates. -/
def completedScalarExtensionDualRestriction (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    ((S.ϕ x.base).Completion ⊗[K] E) →ₗ[(S.ϕ x.base).Completion]
      x.abv.Completion := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let f := dualBaseChangeEquiv (S.ϕ x.base).Completion x.abv.Completion
    ((S.ϕ x.base).Completion ⊗[K] E)
    ((dualBaseChangeEquiv K (S.ϕ x.base).Completion E).toLinearMap.baseChange
      x.abv.Completion
      (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv x.restrict_eq z))
  exact (f.restrictScalars (S.ϕ x.base).Completion).comp
    (TensorProduct.mk (S.ϕ x.base).Completion x.abv.Completion
      ((S.ϕ x.base).Completion ⊗[K] E) (1 : x.abv.Completion))

/-- The actual projective dual norm is the operator norm of its restriction
to the original completed fibre. No Archimedean hypothesis is needed. -/
theorem projectiveScalarExtension_dual_norm_eq_operatorSeminorm
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) =
      linearMapOperatorSeminorm (completedScalarExtensionDualRestriction x z) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let f := dualBaseChangeEquiv (S.ϕ x.base).Completion x.abv.Completion
    ((S.ϕ x.base).Completion ⊗[K] E)
    ((dualBaseChangeEquiv K (S.ϕ x.base).Completion E).toLinearMap.baseChange
      x.abv.Completion
      (completedScalarExtensionEquiv (Module.Dual K E) (S.ϕ x.base) x.abv x.restrict_eq z))
  have he :
      letI := scalarExtensionProjectiveNormedAddCommGroup
        (k := (S.ϕ x.base).Completion) (L := x.abv.Completion)
        (E := (S.ϕ x.base).Completion ⊗[K] E)
      letI := scalarExtensionProjectiveNormedSpace
        (k := (S.ϕ x.base).Completion) (L := x.abv.Completion)
        (E := (S.ϕ x.base).Completion ⊗[K] E)
      (ξ.projectiveScalarExtension (L := L)).dual.norm x
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) =
        linearMapOperatorSeminorm f :=
    ξ.projectiveScalarExtension_dual_norm_apply x z
  exact he.trans (projective_operator_norm_eq_restriction f)

/-- Countable original vector tests compute the actual projective dual norm
on all extended completed dual vectors. -/
theorem projectiveScalarExtension_dual_norm_eq_iSup_basisSubfield
    (b : Module.Basis ι K E) (K₀ : Subfield K)
    (x : S.ParameterSpaceExtension L) (hK₀ : S.IsDenseSubfieldAt K₀ x.base)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] Module.Dual K E)) :
    (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z) =
      ⨆ c : ι → K₀,
        ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
          ((dualBaseChangeEquiv K L E).toLinearMap.baseChange x.abv.Completion z)
          ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c))‖ /
          ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  rw [ξ.projectiveScalarExtension_dual_norm_eq_operatorSeminorm]
  rw [linearMapOperatorSeminorm_eq_sSup_of_denseRange
    (completedScalarExtensionDualRestriction x z) _
    (ξ.denseRange_basisSubfieldMap b K₀ x.base hK₀)]
  apply iSup_congr
  intro c
  have h := completedScalarExtensionEquiv_dual_apply (S.ϕ x.base) x.abv x.restrict_eq z
    ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c))
  change ‖completedScalarExtensionDualRestriction x z
    ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c)‖ / _ = _
  exact congrArg (fun a => ‖a‖ /
    ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c))
    (by simpa only [completedScalarExtensionDualRestriction, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      completedScalarExtensionEquiv_tmul, map_one, one_mul] using h)

/-- The countable formula for an extended rational projective-dual vector
has only fixed extension-field evaluations in its numerator. -/
theorem projectiveScalarExtension_dual_norm_rational_eq_iSup_basisSubfield
    (b : Module.Basis ι K E) (K₀ : Subfield K)
    (x : S.ParameterSpaceExtension L) (hK₀ : S.IsDenseSubfieldAt K₀ x.base)
    (ℓ : Module.Dual L (L ⊗[K] E)) :
    (ξ.projectiveScalarExtension (L := L)).dual.norm x ((1 : x.abv.Completion) ⊗ₜ[L] ℓ) =
      ⨆ c : ι → K₀, x.abv (ℓ ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c)) /
        ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := by
  let d := dualBaseChangeEquiv K L E
  have he : d.toLinearMap.baseChange x.abv.Completion
      ((1 : x.abv.Completion) ⊗ₜ[L] d.symm ℓ) = (1 : x.abv.Completion) ⊗ₜ[L] ℓ := by
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, d.apply_symm_apply]
  have h := ξ.projectiveScalarExtension_dual_norm_eq_iSup_basisSubfield b K₀ x hK₀
    ((1 : x.abv.Completion) ⊗ₜ[L] d.symm ℓ)
  change (ξ.projectiveScalarExtension (L := L)).dual.norm x
      (d.toLinearMap.baseChange x.abv.Completion ((1 : x.abv.Completion) ⊗ₜ[L] d.symm ℓ)) =
    ⨆ c : ι → K₀, ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
      (d.toLinearMap.baseChange x.abv.Completion ((1 : x.abv.Completion) ⊗ₜ[L] d.symm ℓ))
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c))‖ /
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) at h
  rw [he] at h
  have hn (a : L) : ‖algebraMap L x.abv.Completion a‖ = x.abv a :=
    (S.algebraicExtension L).norm_algebraMap_eq_absValue x a
  calc
    _ = ⨆ c : ι → K₀, ‖dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)
        ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)
        ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c))‖ /
        ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) := h
    _ = _ := by
      apply iSup_congr
      intro c
      simp only [dualBaseChangeEquiv_tmul_apply_tmul, one_mul, hn]

/-- The actual dual of projective scalar extension is measurable for every
algebraic extension, using only common countable density in the base fields. -/
theorem IsMeasurable.projectiveScalarExtension_dual_of_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω) :
    (ξ.projectiveScalarExtension (L := L)).dual.IsMeasurable := by
  intro ℓ
  let b := Module.finBasis K E
  have he : (fun x : S.ParameterSpaceExtension L =>
      (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] ℓ)) =
      fun x => ⨆ c : Fin (Module.finrank K E) → K₀,
        x.abv (ℓ ((1 : L) ⊗ₜ[K] basisSubfieldMap b K₀ c)) /
          ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ c) :=
    funext fun x => ξ.projectiveScalarExtension_dual_norm_rational_eq_iSup_basisSubfield
      b K₀ x (hK₀ x.base) ℓ
  change Measurable[AdelicStructure.Algebraic.projectiveMeasurableSpace S L]
    (fun x : S.ParameterSpaceExtension L =>
      (ξ.projectiveScalarExtension (L := L)).dual.norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] ℓ))
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq, he]
  exact Measurable.iSup fun c =>
    (AdelicStructure.ParameterSpaceExtension.measurable_eval S L _).div
      ((hξ _).comp (AdelicStructure.ParameterSpaceExtension.measurable_proj S L))

/-- The existential common-density assumption gives the same measurable
projective-dual family, including rank zero. -/
theorem IsMeasurable.projectiveScalarExtension_dual_of_common_countable_dense_subfield
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable) (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.projectiveScalarExtension (L := L)).dual.IsMeasurable := by
  obtain ⟨K₀, hc, hd⟩ := hS
  let : Countable K₀ := hc
  exact hξ.projectiveScalarExtension_dual_of_countable_dense_subfield K₀ hd

/-- Finite-extension common density makes the actual bidual of the
projective extension measurable, without a normalization assumption. -/
theorem IsMeasurable.projectiveScalarExtension_bidual_of_finiteDimensional
    [FiniteDimensional K L] {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.projectiveScalarExtension (L := L)).dual.dual.IsMeasurable :=
  IsMeasurable.dual_of_common_countable_dense_subfield
    (hξ.projectiveScalarExtension_dual_of_common_countable_dense_subfield (L := L) hS)
    (hS.algebraicExtension_of_finiteDimensional (L := L))

/-- Ordinary finite scalar extension is measurable when its actual
Archimedean completed fields have the usual real or complex norm. -/
theorem IsMeasurable.scalarExtension_of_finiteDimensional
    [FiniteDimensional K L] {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield)
    (hL : ∀ ω ∈ (S.algebraicExtension L).Ωinf,
      IsRCLikeNormedField (((S.algebraicExtension L).ϕ ω).Completion)) :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  classical
  let η := ξ.projectiveScalarExtension (L := L)
  let ζ := η.dual.dual.pullback (Module.Dual.eval L (L ⊗[K] E))
    (Module.eval_apply_injective L)
  have hζ : ζ.IsMeasurable :=
    (hξ.projectiveScalarExtension_bidual_of_finiteDimensional hS).pullback
      (Module.Dual.eval L (L ⊗[K] E)) (Module.eval_apply_injective L)
  have hi := hξ.injectiveScalarExtension_of_common_countable_dense_subfield (L := L) hS
  have hfin : MeasurableSet (S.algebraicExtension L).Ωfin := by
    have he : (S.algebraicExtension L).Ωfin = ((S.algebraicExtension L).Ωinf)ᶜ := by
      ext x
      simp only [AdelicStructure.Ωfin, AdelicStructure.Ωinf, Set.mem_ofPred_eq,
        Set.mem_compl_iff, not_not]
    rw [he]
    exact (S.algebraicExtension L).measurableSet_Ωinf.compl
  intro z
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      Set.piecewise (S.algebraicExtension L).Ωfin
        (fun x => (ξ.injectiveScalarExtension (L := L)).norm x
          ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z))
        (fun x => ζ.norm x ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) := by
    funext x
    by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      change S.ParameterSpaceExtension L at x
      exact ξ.scalarExtension_norm_of_mem_Ωfin x ((AdelicStructure.mem_Ωfin_algebraicExtension_iff
        x).mp hx) _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      change S.ParameterSpaceExtension L at x
      have hx' : x.base ∉ S.Ωfin :=
        fun h => hx ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr h)
      have hb := η.dual_dual_norm_eval_eq_of_isRCLike x (hL x hx)
        ((1 : x.abv.Completion) ⊗ₜ[L] z)
      change (ξ.scalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L] z) =
        η.dual.dual.norm x ((Module.Dual.eval L (L ⊗[K] E)).baseChange x.abv.Completion
          ((1 : x.abv.Completion) ⊗ₜ[L] z))
      exact (ξ.scalarExtension_norm_of_not_mem_Ωfin x hx' _).trans hb.symm
  rw [he]
  exact Measurable.piecewise hfin (hi z) (hζ z)

/-- Exact countable-coordinate formula for the actual projective extension.
The rational coefficient constraint is independent of the extending place. -/
theorem projectiveScalarExtension_norm_eq_iInf_scalarCoordinateCost
    (b : Module.Basis ι K E) (K₀ : Subfield K) (L₀ : Subfield L)
    (ρ : K₀ →+* L₀) (hρ : ∀ a : K₀, (ρ a : L) = algebraMap K L (a : K))
    (c : ι → L₀) (x : S.ParameterSpaceExtension L)
    (hK₀ : S.IsDenseSubfieldAt K₀ x.base)
    (hL₀ : (S.algebraicExtension L).IsDenseSubfieldAt L₀ x) :
    (ξ.projectiveScalarExtension (L := L)).norm x
        ((1 : x.abv.Completion) ⊗ₜ[L] scalarFromCoordinates b L₀.subtype c) =
      ⨅ p : {p : List (L₀ × (ι → K₀)) // scalarCoordinateCoefficients ρ p = c},
        (p.val.map fun q => x.abv (q.1 : L) *
          ξ.norm x.base
            ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ q.2)).sum := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let B := b.baseChange (S.ϕ x.base).Completion
  let σ := (algebraMap K (S.ϕ x.base).Completion).comp K₀.subtype
  let τ := (algebraMap L x.abv.Completion).comp L₀.subtype
  have hστ (a : K₀) : algebraMap (S.ϕ x.base).Completion x.abv.Completion (σ a) =
      τ (ρ a) := by
    change algebraMap (S.ϕ x.base).Completion x.abv.Completion
      (algebraMap K (S.ϕ x.base).Completion (a : K)) =
        algebraMap L x.abv.Completion (ρ a : L)
    rw [hρ, AbsoluteValue.algebraMap_normedAlgebraCompletionOfEq_coe]
  have hv (d : ι → K₀) : scalarCoordinateVector B σ d =
      (1 : (S.ϕ x.base).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ d :=
    (basisSubfieldMap_tmul b K₀ x.base d).symm
  have hz : completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
      ((1 : x.abv.Completion) ⊗ₜ[L] scalarFromCoordinates b L₀.subtype c) =
        scalarFromCoordinates B τ c := by
    simp only [scalarFromCoordinates, Module.Basis.equivFun_symm_apply,
      TensorProduct.tmul_sum, map_sum, Module.Basis.baseChange_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    simp only [completedScalarExtensionEquiv_tmul, map_one, one_mul]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [B, Module.Basis.baseChange_apply, τ, RingHom.comp_apply]
  have hn (a : L₀) : ‖τ a‖ = x.abv (a : L) :=
    (S.algebraicExtension L).norm_algebraMap_eq_absValue x a
  calc
    _ = scalarExtensionProjectiveSeminorm (scalarFromCoordinates B τ c) := by
      change scalarExtensionProjectiveSeminorm
        (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq _) = _
      exact congrArg (fun y => scalarExtensionProjectiveSeminorm
        (k := (S.ϕ x.base).Completion) (L := x.abv.Completion) y) hz
    _ = ⨅ p : {p : List (L₀ × (ι → K₀)) // scalarCoordinateCoefficients ρ p = c},
        scalarCoordinateCost B σ τ p.val :=
      scalarExtensionProjectiveSeminorm_eq_iInf_scalarCoordinateCost B σ τ ρ hK₀ hL₀ hστ c
    _ = _ := by
      apply iInf_congr
      intro p
      simp only [scalarCoordinateCost, hn, hv]
      rfl

/-- Two compatible common countable dense subfields make the actual projective
extension measurable, with no normalization assumption on either completion. -/
theorem IsMeasurable.projectiveScalarExtension_of_countable_dense_subfields
    {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (K₀ : Subfield K) [Countable K₀] (L₀ : Subfield L) [Countable L₀]
    (ρ : K₀ →+* L₀) (hρ : ∀ a : K₀, (ρ a : L) = algebraMap K L (a : K))
    (hK₀ : ∀ ω, S.IsDenseSubfieldAt K₀ ω)
    (hL₀ : ∀ x, (S.algebraicExtension L).IsDenseSubfieldAt L₀ x) :
    (ξ.projectiveScalarExtension (L := L)).IsMeasurable := by
  classical
  intro z
  let b := Module.finBasis K E
  obtain ⟨L₁, hc, hge, hcoord⟩ :=
    exists_countable_subfield_ge_range L₀ ((b.baseChange L).equivFun z)
  let : Countable L₁ := hc
  let ρ₁ : K₀ →+* L₁ := (Subfield.inclusion hge).comp ρ
  have hρ₁ (a : K₀) : (ρ₁ a : L) = algebraMap K L (a : K) := hρ a
  have hd₁ (x : S.ParameterSpaceExtension L) :
      (S.algebraicExtension L).IsDenseSubfieldAt L₁ x := by
    apply Dense.mono (hd := hL₀ x)
    rintro _ ⟨a, rfl⟩
    exact ⟨Subfield.inclusion hge a, rfl⟩
  let c : Fin (Module.finrank K E) → L₁ :=
    fun j => ⟨(b.baseChange L).equivFun z j, hcoord j⟩
  have hz : scalarFromCoordinates b L₁.subtype c = z := by
    apply (b.baseChange L).equivFun.injective
    simp only [scalarFromCoordinates, LinearEquiv.apply_symm_apply]
    rfl
  change Measurable[AdelicStructure.Algebraic.projectiveMeasurableSpace S L]
    (fun x : S.ParameterSpaceExtension L =>
      (ξ.projectiveScalarExtension (L := L)).norm x ((1 : x.abv.Completion) ⊗ₜ[L] z))
  rw [AdelicStructure.Algebraic.projectiveMeasurableSpace_eq, ← hz]
  simp_rw [ξ.projectiveScalarExtension_norm_eq_iInf_scalarCoordinateCost
    b K₀ L₁ ρ₁ hρ₁ c _ (hK₀ _) (hd₁ _)]
  apply Measurable.iInf
  intro p
  induction p.val with
  | nil => exact measurable_const
  | cons q p hp =>
    simp only [List.map_cons, List.sum_cons]
    apply Measurable.add _ hp
    exact (AdelicStructure.ParameterSpaceExtension.measurable_eval S L (q.1 : L)).mul
      ((hξ (basisSubfieldMap b K₀ q.2)).comp
        (AdelicStructure.ParameterSpaceExtension.measurable_proj S L))

/-- Finite algebraic extension preserves projective measurability using exact
countable decompositions on the actual completed fibres. -/
theorem IsMeasurable.projectiveScalarExtension_of_finiteDimensional
    [FiniteDimensional K L] {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.projectiveScalarExtension (L := L)).IsMeasurable := by
  obtain ⟨K₀, hc, hd⟩ := hS
  let : Countable K₀ := hc
  let b := Module.finBasis K L
  let L₀ := finiteExtensionDenseSubfield b K₀
  let : Countable L₀ := countable_finiteExtensionDenseSubfield b K₀
  let ρ : K₀ →+* L₀ := ((algebraMap K L).comp K₀.subtype).codRestrict L₀
    (fun a => algebraMap_mem_finiteExtensionDenseSubfield b K₀ a)
  exact hξ.projectiveScalarExtension_of_countable_dense_subfields K₀ L₀ ρ
    (fun _ => rfl) hd
    (fun x => AdelicStructure.isDenseSubfieldAt_finiteExtensionDenseSubfield
      b K₀ x (hd x.base))

/-- Measurability of both actual scalar-extension norms gives measurability
of their finite/Archimedean mixture. -/
theorem IsMeasurable.scalarExtension_of_injective_projective
    {ξ : NormFamily S E}
    (hi : (ξ.injectiveScalarExtension (L := L)).IsMeasurable)
    (hp : (ξ.projectiveScalarExtension (L := L)).IsMeasurable) :
    (ξ.scalarExtension (L := L)).IsMeasurable := by
  classical
  have hfin : MeasurableSet (S.algebraicExtension L).Ωfin := by
    have he : (S.algebraicExtension L).Ωfin = ((S.algebraicExtension L).Ωinf)ᶜ := by
      ext x
      simp only [AdelicStructure.Ωfin, AdelicStructure.Ωinf, Set.mem_ofPred_eq,
        Set.mem_compl_iff, not_not]
    rw [he]
    exact (S.algebraicExtension L).measurableSet_Ωinf.compl
  intro z
  have he : (fun x : (S.algebraicExtension L).Ω =>
      (ξ.scalarExtension (L := L)).norm x
        ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) =
      Set.piecewise (S.algebraicExtension L).Ωfin
        (fun x => (ξ.injectiveScalarExtension (L := L)).norm x
          ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z))
        (fun x => (ξ.projectiveScalarExtension (L := L)).norm x
          ((1 : ((S.algebraicExtension L).ϕ x).Completion) ⊗ₜ[L] z)) := by
    funext x
    by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      exact ξ.scalarExtension_norm_of_mem_Ωfin x ((AdelicStructure.mem_Ωfin_algebraicExtension_iff
        x).mp hx) _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact ξ.scalarExtension_norm_of_not_mem_Ωfin x
        (fun h => hx ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mpr h)) _
  rw [he]
  exact Measurable.piecewise hfin (hi z) (hp z)

/-- Ordinary finite scalar extension preserves measurability under common
countable base density, with no Archimedean normalization assumption. -/
theorem IsMeasurable.scalarExtension_of_finiteDimensional_of_common_countable_dense_subfield
    [FiniteDimensional K L] {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    (hS : S.HasCommonCountableDenseSubfield) :
    (ξ.scalarExtension (L := L)).IsMeasurable :=
  IsMeasurable.scalarExtension_of_injective_projective
    (hξ.injectiveScalarExtension_of_common_countable_dense_subfield hS)
    (hξ.projectiveScalarExtension_of_finiteDimensional hS)

end ArakelovGeometry.NormFamily
