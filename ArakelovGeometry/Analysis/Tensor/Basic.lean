/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NormedSpace.LinearMapBound
public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.NormNum.GCD

/-!
# Norms on finite tensor products

Projective separation and the injective norm defined by products of dual
functionals, for finite-dimensional spaces over arbitrary complete normed
fields. The tensor products are Mathlib's canonical `PiTensorProduct`.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {ι L : Type*} [Fintype ι] [NormedField L]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace L (E i)]

/-- Evaluation by a pure tensor of algebraic dual functionals. -/
def tensorDualEval (φ : ∀ i, E i →ₗ[L] L) : (⨂[L] i, E i) →ₗ[L] L :=
  PiTensorProduct.dualDistrib (⨂ₜ[L] i, φ i)

@[simp]
theorem tensorDualEval_tprod (φ : ∀ i, E i →ₗ[L] L) (x : ∀ i, E i) :
    tensorDualEval φ (⨂ₜ[L] i, x i) = ∏ i, φ i (x i) := by
  exact PiTensorProduct.dualDistrib_apply φ x

/-- The universal projective bound for a linear map whose values on pure tensors
are bounded. This form includes trivially normed fields. -/
theorem norm_linearMap_le_projective_of_tprod_le {F : Type*}
    [SeminormedAddCommGroup F] [NormedSpace L F]
    (f : (⨂[L] i, E i) →ₗ[L] F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ∀ i, E i, ‖f (⨂ₜ[L] i, x i)‖ ≤ C * ∏ i, ‖x i‖)
    (z : ⨂[L] i, E i) : ‖f z‖ ≤ C * PiTensorProduct.projectiveSeminorm z := by
  change ‖f z‖ ≤ C * ‖z‖
  rw [PiTensorProduct.norm_def, mul_comm, Real.iInf_mul_of_nonneg
    hC]
  apply le_ciInf
  rintro ⟨p, hp⟩
  change ‖f z‖ ≤ PiTensorProduct.projectiveSeminormAux p *
    C
  rw [← (PiTensorProduct.mem_lifts_iff z p).mp hp, map_list_sum]
  have hnorm (l : List F) : ‖l.sum‖ ≤ (l.map norm).sum := by
    simpa only [Multiset.sum_coe, Multiset.map_coe] using
      norm_multiset_sum_le (l : Multiset F)
  calc
    ‖(List.map (f) (List.map (fun q ↦ q.1 • ⨂ₜ[L] i, q.2 i) p.toList)).sum‖
        ≤ (List.map (fun q : L × (∀ i, E i) ↦
          ‖q.1‖ * ((C) * ∏ i, ‖q.2 i‖)) p.toList).sum := by
      apply (hnorm _).trans
      simp only [List.map_map, Function.comp_def, map_smul, norm_smul]
      apply List.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hf q.2) (norm_nonneg q.1)
    _ = PiTensorProduct.projectiveSeminormAux p * C := by
      simp only [PiTensorProduct.projectiveSeminormAux, ← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro q hq
      ring

variable [CompleteSpace L] [∀ i, FiniteDimensional L (E i)]

/-- Product evaluation on a pure tensor is bounded by the product of dual norms. -/
theorem norm_tensorDualEval_tprod_le (φ : ∀ i, E i →ₗ[L] L) (x : ∀ i, E i) :
    ‖tensorDualEval φ (⨂ₜ[L] i, x i)‖ ≤
      (∏ i, linearMapOperatorSeminorm (φ i)) * ∏ i, ‖x i‖ := by
  rw [tensorDualEval_tprod, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    (fun i _ ↦ norm_linearMap_apply_le (φ i) (x i))

/-- Every product of dual evaluations is bounded by the projective seminorm.
The proof uses the defining finite decompositions, so it also covers trivial valuations. -/
theorem norm_tensorDualEval_le_projective (φ : ∀ i, E i →ₗ[L] L)
    (z : ⨂[L] i, E i) :
    ‖tensorDualEval φ z‖ ≤
      (∏ i, linearMapOperatorSeminorm (φ i)) * PiTensorProduct.projectiveSeminorm z :=
  norm_linearMap_le_projective_of_tprod_le (tensorDualEval φ)
    (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) (norm_tensorDualEval_tprod_le φ) z

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- Products of coordinate functionals are exactly tensor-basis coordinates. -/
theorem tensorDualEval_coord {κ : ι → Type*}
    (b : ∀ i, Module.Basis (κ i) L (E i)) (j : ∀ i, κ i) :
    tensorDualEval (fun i ↦ (b i).coord (j i)) = (Basis.piTensorProduct b).coord j := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, tensorDualEval_tprod,
    Module.Basis.coord_apply, Basis.piTensorProduct_repr_tprod_apply]

omit [CompleteSpace L] in
/-- Products of dual evaluations separate every tensor, including empty products
and products with a zero-dimensional factor. -/
theorem eq_zero_of_tensorDualEval_eq_zero (z : ⨂[L] i, E i)
    (h : ∀ φ : ∀ i, E i →ₗ[L] L, tensorDualEval φ z = 0) : z = 0 := by
  let b i := Module.finBasis L (E i)
  apply (Basis.piTensorProduct b).ext_elem
  intro j
  have hj := h (fun i ↦ (b i).coord (j i))
  rw [tensorDualEval_coord] at hj
  simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using hj

/-- The projective tensor seminorm separates points over every complete normed field. -/
theorem projectiveSeminorm_eq_zero_iff (z : ⨂[L] i, E i) :
    PiTensorProduct.projectiveSeminorm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply eq_zero_of_tensorDualEval_eq_zero
    intro φ
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hz, mul_zero] using norm_tensorDualEval_le_projective φ z
  · rintro rfl
    exact map_zero _

/-- A normalized product of dual evaluations, as a seminorm on the tensor product.
A zero factor in the denominator contributes the zero seminorm. -/
def tensorDualRatioSeminorm (φ : ∀ i, E i →ₗ[L] L) : Seminorm L (⨂[L] i, E i) :=
  NNReal.mk (∏ i, linearMapOperatorSeminorm (φ i))⁻¹
    (inv_nonneg.mpr (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)) •
      (normSeminorm L L).comp (tensorDualEval φ)

@[simp]
theorem tensorDualRatioSeminorm_apply (φ : ∀ i, E i →ₗ[L] L)
    (z : ⨂[L] i, E i) :
    tensorDualRatioSeminorm φ z =
      ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i) := by
  change (∏ i, linearMapOperatorSeminorm (φ i))⁻¹ * ‖tensorDualEval φ z‖ = _
  rw [div_eq_mul_inv, mul_comm]

/-- Every normalized dual product is dominated by the projective seminorm. -/
theorem tensorDualRatioSeminorm_le_projective (φ : ∀ i, E i →ₗ[L] L) :
    tensorDualRatioSeminorm φ ≤ PiTensorProduct.projectiveSeminorm := by
  intro z
  rw [tensorDualRatioSeminorm_apply]
  by_cases h : ∏ i, linearMapOperatorSeminorm (φ i) = 0
  · simp [h, apply_nonneg PiTensorProduct.projectiveSeminorm z]
  have hpos : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
    lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) (Ne.symm h)
  apply (div_le_iff₀ hpos).mpr
  simpa only [mul_comm] using norm_tensorDualEval_le_projective φ z

private theorem tensorDualRatioSeminorm_bddAbove :
    BddAbove (Set.range (tensorDualRatioSeminorm (L := L) (E := E))) :=
  ⟨PiTensorProduct.projectiveSeminorm, by
    rintro _ ⟨φ, rfl⟩
    exact tensorDualRatioSeminorm_le_projective φ⟩

/-- The injective tensor seminorm from products of dual functionals. This is
the source's injective norm, distinct from the deprecated Mathlib declaration
with a similar name. Empty families use the same product convention. -/
def injectiveTensorSeminorm : Seminorm L (⨂[L] i, E i) :=
  sSup (Set.range tensorDualRatioSeminorm)

/-- Each product of dual ratios is bounded by the injective seminorm. -/
theorem tensorDualRatioSeminorm_le_injective (φ : ∀ i, E i →ₗ[L] L) :
    tensorDualRatioSeminorm φ ≤ injectiveTensorSeminorm :=
  le_csSup tensorDualRatioSeminorm_bddAbove ⟨φ, rfl⟩

/-- The injective tensor seminorm is bounded by the projective tensor seminorm. -/
theorem injectiveTensorSeminorm_le_projective :
    injectiveTensorSeminorm (L := L) (E := E) ≤ PiTensorProduct.projectiveSeminorm := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨φ, rfl⟩
  exact tensorDualRatioSeminorm_le_projective φ

/-- Pointwise bounds on the injective seminorm are exactly bounds for every dual ratio. -/
theorem injectiveTensorSeminorm_le_iff (z : ⨂[L] i, E i) (C : ℝ) :
    injectiveTensorSeminorm z ≤ C ↔
      ∀ φ : ∀ i, E i →ₗ[L] L,
        ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i) ≤ C := by
  constructor
  · intro h φ
    exact (tensorDualRatioSeminorm_apply φ z).symm.le.trans
      ((tensorDualRatioSeminorm_le_injective φ z).trans h)
  · intro h
    rw [injectiveTensorSeminorm, Seminorm.sSup_apply tensorDualRatioSeminorm_bddAbove]
    apply ciSup_le
    rintro ⟨p, φ, rfl⟩
    exact (tensorDualRatioSeminorm_apply φ z).le.trans (h φ)

/-- The injective norm is the supremum of the source's product-evaluation ratios,
with zero functionals admitted using the harmless `0/0 = 0` convention. -/
theorem injectiveTensorSeminorm_eq_sSup (z : ⨂[L] i, E i) :
    injectiveTensorSeminorm z = sSup (Set.range fun φ : ∀ i, E i →ₗ[L] L ↦
      ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i)) := by
  have hb : BddAbove (Set.range fun φ : ∀ i, E i →ₗ[L] L ↦
      ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i)) := by
    refine ⟨PiTensorProduct.projectiveSeminorm z, ?_⟩
    rintro _ ⟨φ, rfl⟩
    simpa only [tensorDualRatioSeminorm_apply] using tensorDualRatioSeminorm_le_projective φ z
  apply le_antisymm
  · apply (injectiveTensorSeminorm_le_iff z _).2
    intro φ
    exact le_csSup hb ⟨φ, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨φ, rfl⟩
    simpa only [tensorDualRatioSeminorm_apply] using tensorDualRatioSeminorm_le_injective φ z

/-- A tuple containing a zero functional contributes the zero seminorm. -/
theorem tensorDualRatioSeminorm_eq_zero_of_exists_zero
    (φ : ∀ i, E i →ₗ[L] L) (hφ : ∃ i, φ i = 0) :
    tensorDualRatioSeminorm φ = 0 := by
  obtain ⟨i, hi⟩ := hφ
  have hD : ∏ j, linearMapOperatorSeminorm (φ j) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi, map_zero]
  ext z
  simp [tensorDualRatioSeminorm_apply, hD]

/-- The source formula with every individual functional required to be nonzero.
If there are no such tuples, the supremum is zero. -/
theorem injectiveTensorSeminorm_eq_sSup_nonzero (z : ⨂[L] i, E i) :
    injectiveTensorSeminorm z = sSup {r : ℝ | ∃ φ : ∀ i, E i →ₗ[L] L,
      (∀ i, φ i ≠ 0) ∧ ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i) = r} := by
  classical
  let R := {r : ℝ | ∃ φ : ∀ i, E i →ₗ[L] L,
    (∀ i, φ i ≠ 0) ∧ ‖tensorDualEval φ z‖ / ∏ i, linearMapOperatorSeminorm (φ i) = r}
  have hb : BddAbove R := by
    refine ⟨PiTensorProduct.projectiveSeminorm z, ?_⟩
    rintro _ ⟨φ, _, rfl⟩
    simpa only [tensorDualRatioSeminorm_apply] using tensorDualRatioSeminorm_le_projective φ z
  change injectiveTensorSeminorm z = sSup R
  by_cases hR : R.Nonempty
  · have h0 : 0 ≤ sSup R := by
      obtain ⟨r, φ, hφ, rfl⟩ := hR
      exact (div_nonneg (norm_nonneg _)
        (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _)).trans (le_csSup hb ⟨φ, hφ, rfl⟩)
    apply le_antisymm
    · apply (injectiveTensorSeminorm_le_iff z _).2
      intro φ
      by_cases hφ : ∀ i, φ i ≠ 0
      · exact le_csSup hb ⟨φ, hφ, rfl⟩
      · push Not at hφ
        rw [← tensorDualRatioSeminorm_apply, tensorDualRatioSeminorm_eq_zero_of_exists_zero φ hφ]
        exact h0
    · apply csSup_le hR
      rintro _ ⟨φ, _, rfl⟩
      simpa only [tensorDualRatioSeminorm_apply] using tensorDualRatioSeminorm_le_injective φ z
  · have hempty : R = ∅ := Set.not_nonempty_iff_eq_empty.mp hR
    rw [hempty, Real.sSup_empty]
    apply le_antisymm _ (apply_nonneg _ _)
    apply (injectiveTensorSeminorm_le_iff z 0).2
    intro φ
    have hφ : ¬ ∀ i, φ i ≠ 0 := fun h ↦ hR ⟨_, φ, h, rfl⟩
    push Not at hφ
    rw [← tensorDualRatioSeminorm_apply, tensorDualRatioSeminorm_eq_zero_of_exists_zero φ hφ]
    exact le_rfl

/-- The genuine injective tensor seminorm separates points. -/
theorem injectiveTensorSeminorm_eq_zero_iff (z : ⨂[L] i, E i) :
    injectiveTensorSeminorm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply eq_zero_of_tensorDualEval_eq_zero
    intro φ
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    by_cases hD : ∏ i, linearMapOperatorSeminorm (φ i) = 0
    · simpa only [hD, zero_mul] using norm_tensorDualEval_le_projective φ z
    · have hDpos : 0 < ∏ i, linearMapOperatorSeminorm (φ i) :=
        lt_of_le_of_ne (Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _) (Ne.symm hD)
      have h := (injectiveTensorSeminorm_le_iff z 0).mp hz.le φ
      simpa only [zero_mul] using (div_le_iff₀ hDpos).mp h
  · rintro rfl
    exact map_zero _

/-- A non-Archimedean scalar norm makes the injective norm ultrametric, without
an ultrametric hypothesis on the norms of the tensor factors. -/
theorem injectiveTensorSeminorm_add_le_max
    (hL : ∀ a b : L, ‖a + b‖ ≤ max ‖a‖ ‖b‖) (z t : ⨂[L] i, E i) :
    injectiveTensorSeminorm (z + t) ≤
      max (injectiveTensorSeminorm z) (injectiveTensorSeminorm t) := by
  apply (injectiveTensorSeminorm_le_iff _ _).2
  intro φ
  have hD : 0 ≤ ∏ i, linearMapOperatorSeminorm (φ i) :=
    Finset.prod_nonneg fun _ _ ↦ apply_nonneg _ _
  calc
    ‖tensorDualEval φ (z + t)‖ / ∏ i, linearMapOperatorSeminorm (φ i)
        ≤ max ‖tensorDualEval φ z‖ ‖tensorDualEval φ t‖ /
          ∏ i, linearMapOperatorSeminorm (φ i) := by
      rw [map_add]
      exact div_le_div_of_nonneg_right (hL _ _) hD
    _ = max (tensorDualRatioSeminorm φ z) (tensorDualRatioSeminorm φ t) := by
      rw [tensorDualRatioSeminorm_apply, tensorDualRatioSeminorm_apply,
        max_div_div_right hD]
    _ ≤ max (injectiveTensorSeminorm z) (injectiveTensorSeminorm t) :=
      max_le_max (tensorDualRatioSeminorm_le_injective φ z)
        (tensorDualRatioSeminorm_le_injective φ t)

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- For an empty family, evaluation is the canonical identification with the field. -/
theorem tensorDualEval_isEmpty [IsEmpty ι] (φ : ∀ i, E i →ₗ[L] L) :
    tensorDualEval φ = (PiTensorProduct.isEmptyEquiv ι).toLinearMap := by
  apply PiTensorProduct.ext
  ext x
  simp [LinearMap.compMultilinearMap_apply]

/-- The projective norm of an empty tensor product is the scalar absolute value. -/
theorem projectiveSeminorm_isEmpty [IsEmpty ι] (z : ⨂[L] i, E i) :
    PiTensorProduct.projectiveSeminorm z = ‖PiTensorProduct.isEmptyEquiv ι z‖ := by
  apply le_antisymm
  · have hz : z = PiTensorProduct.isEmptyEquiv ι z • (⨂ₜ[L] i, (0 : E i)) := by
      apply (PiTensorProduct.isEmptyEquiv ι).injective
      simp
    conv_lhs => rw [hz]
    rw [map_smul_eq_mul]
    calc
      ‖PiTensorProduct.isEmptyEquiv ι z‖ *
          PiTensorProduct.projectiveSeminorm (⨂ₜ[L] i, (0 : E i))
          ≤ ‖PiTensorProduct.isEmptyEquiv ι z‖ * ∏ i, ‖(0 : E i)‖ :=
        mul_le_mul_of_nonneg_left (PiTensorProduct.projectiveSeminorm_tprod_le _)
          (norm_nonneg _)
      _ = _ := by simp
  · simpa [tensorDualEval_isEmpty] using
      norm_tensorDualEval_le_projective (fun i ↦ (0 : E i →ₗ[L] L)) z

/-- The injective norm of an empty tensor product is the same scalar absolute value. -/
theorem injectiveTensorSeminorm_isEmpty [IsEmpty ι] (z : ⨂[L] i, E i) :
    injectiveTensorSeminorm z = ‖PiTensorProduct.isEmptyEquiv ι z‖ := by
  apply le_antisymm
  · exact (injectiveTensorSeminorm_le_projective z).trans_eq (projectiveSeminorm_isEmpty z)
  · simpa [tensorDualRatioSeminorm_apply, tensorDualEval_isEmpty] using
      tensorDualRatioSeminorm_le_injective (fun i ↦ (0 : E i →ₗ[L] L)) z

omit [Fintype ι] [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- A zero-dimensional tensor factor makes every tensor zero. -/
theorem tensor_eq_zero_of_subsingleton (i₀ : ι) [Subsingleton (E i₀)]
    (z : ⨂[L] i, E i) : z = 0 := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [(PiTensorProduct.tprod L).map_coord_zero i₀ (Subsingleton.elim _ 0), smul_zero]
  | add z t hz ht => rw [hz, ht, add_zero]

/-- Both tensor norms vanish if one of the factors is zero-dimensional. -/
theorem tensorSeminorms_eq_zero_of_subsingleton (i₀ : ι) [Subsingleton (E i₀)]
    (z : ⨂[L] i, E i) :
    PiTensorProduct.projectiveSeminorm z = 0 ∧ injectiveTensorSeminorm z = 0 := by
  rw [tensor_eq_zero_of_subsingleton i₀ z]
  exact ⟨map_zero _, map_zero _⟩

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- For a one-factor tensor product, product evaluation is ordinary dual evaluation. -/
theorem tensorDualEval_unique [Unique ι] (φ : ∀ i, E i →ₗ[L] L) (z : ⨂[L] i, E i) :
    tensorDualEval φ z = φ default (PiTensorProduct.subsingletonEquiv default z) := by
  have h : tensorDualEval φ =
      (φ default).comp (PiTensorProduct.subsingletonEquiv default).toLinearMap := by
    apply PiTensorProduct.ext
    ext x
    simp [LinearMap.compMultilinearMap_apply]
  exact DFunLike.congr_fun h z

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- The one-factor projective tensor norm is exactly the original norm. -/
theorem projectiveSeminorm_unique [Unique ι] (z : ⨂[L] i, E i) :
    PiTensorProduct.projectiveSeminorm z = ‖PiTensorProduct.subsingletonEquiv default z‖ := by
  classical
  let e := PiTensorProduct.subsingletonEquiv (R := L) (s := E) default
  apply le_antisymm
  · have hz : z = ⨂ₜ[L] i, Function.update (0 : ∀ i, E i) default (e z) i :=
      (e.symm_apply_apply z).symm.trans (PiTensorProduct.subsingletonEquiv_symm_apply _ _)
    conv_lhs => rw [hz]
    change ‖⨂ₜ[L] i, Function.update (0 : ∀ i, E i) default (e z) i‖ ≤ ‖e z‖
    simpa using PiTensorProduct.projectiveSeminorm_tprod_le
      (Function.update (0 : ∀ i, E i) default (e z))
  · have h := norm_linearMap_le_projective_of_tprod_le e.toLinearMap (C := 1) zero_le_one
      (fun x ↦ by simp [e]) z
    simpa only [one_mul, e, LinearEquiv.coe_coe] using h

/-- The one-factor injective norm is the bidual supremum. Equality with the
original norm requires the separate reflexivity-of-norm hypotheses. -/
theorem injectiveTensorSeminorm_unique [Unique ι] (z : ⨂[L] i, E i) :
    injectiveTensorSeminorm z = sSup (Set.range fun φ : E default →ₗ[L] L ↦
      ‖φ (PiTensorProduct.subsingletonEquiv default z)‖ / linearMapOperatorSeminorm φ) := by
  classical
  rw [injectiveTensorSeminorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ default, by simp [tensorDualEval_unique]⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨Function.update (0 : ∀ i, E i →ₗ[L] L) default φ, ?_⟩
    simp [tensorDualEval_unique]

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- Every pure-tensor decomposition bounds the projective seminorm. -/
theorem projectiveSeminorm_sum_tprod_le (xs : List (∀ i, E i)) :
    PiTensorProduct.projectiveSeminorm (xs.map (PiTensorProduct.tprod L)).sum ≤
      (xs.map fun x ↦ ∏ i, ‖x i‖).sum := by
  change ‖(xs.map (PiTensorProduct.tprod L)).sum‖ ≤ _
  have h := norm_multiset_sum_le
    ((xs.map (PiTensorProduct.tprod L)) : Multiset (⨂[L] i, E i))
  simp only [Multiset.sum_coe, Multiset.map_coe, List.map_map, Function.comp_def] at h
  exact h.trans (List.sum_le_sum fun x _ ↦ PiTensorProduct.projectiveSeminorm_tprod_le x)

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
private theorem prod_norm_update_smul [DecidableEq ι]
    (i₀ : ι) (a : L) (x : ∀ i, E i) :
    (∏ i, ‖Function.update x i₀ (a • x i₀) i‖) = ‖a‖ * ∏ i, ‖x i‖ := by
  calc
    (∏ i, ‖Function.update x i₀ (a • x i₀) i‖) =
        ∏ i, (if i = i₀ then ‖a‖ else 1) * ‖x i‖ := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i = i₀
      · subst i
        simp [norm_smul]
      · simp [h]
    _ = (∏ i, if i = i₀ then ‖a‖ else 1) * ∏ i, ‖x i‖ := Finset.prod_mul_distrib
    _ = _ := by rw [Fintype.prod_ite_eq']

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- Scalar coefficients in a Mathlib tensor decomposition can be absorbed into
one tensor factor without changing the projective cost. -/
theorem exists_tprod_decomposition_same_cost (i₀ : ι)
    (p : FreeAddMonoid (L × (∀ i, E i))) :
    ∃ xs : List (∀ i, E i),
      (xs.map (PiTensorProduct.tprod L)).sum =
        (p.toList.map fun q ↦ q.1 • (⨂ₜ[L] i, q.2 i)).sum ∧
      (xs.map fun x ↦ ∏ i, ‖x i‖).sum = PiTensorProduct.projectiveSeminormAux p := by
  classical
  refine ⟨p.toList.map (fun q ↦ Function.update q.2 i₀ (q.1 • q.2 i₀)), ?_, ?_⟩
  · simp only [List.map_map, Function.comp_def, MultilinearMap.map_update_smul,
      Function.update_eq_self]
  · simp only [List.map_map, Function.comp_def, prod_norm_update_smul,
      PiTensorProduct.projectiveSeminormAux]

omit [CompleteSpace L] [∀ i, FiniteDimensional L (E i)] in
/-- The source formula for the projective norm: the infimum of sums of products
of factor norms over actual finite pure-tensor decompositions. -/
theorem projectiveSeminorm_eq_sInf [Nonempty ι] (z : ⨂[L] i, E i) :
    PiTensorProduct.projectiveSeminorm z = sInf {r : ℝ | ∃ xs : List (∀ i, E i),
      (xs.map (PiTensorProduct.tprod L)).sum = z ∧ (xs.map fun x ↦ ∏ i, ‖x i‖).sum = r} := by
  classical
  let R := {r : ℝ | ∃ xs : List (∀ i, E i),
    (xs.map (PiTensorProduct.tprod L)).sum = z ∧ (xs.map fun x ↦ ∏ i, ‖x i‖).sum = r}
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  have hb : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro _ ⟨xs, _, rfl⟩
    apply List.sum_nonneg
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hmem (p : PiTensorProduct.lifts z) : PiTensorProduct.projectiveSeminormAux p.1 ∈ R := by
    obtain ⟨xs, hx, hcost⟩ := exists_tprod_decomposition_same_cost i₀ p.1
    exact ⟨xs, hx.trans ((PiTensorProduct.mem_lifts_iff z p.1).mp p.2), hcost⟩
  have hne : R.Nonempty := ⟨_, hmem (Classical.choice inferInstance)⟩
  change PiTensorProduct.projectiveSeminorm z = sInf R
  apply le_antisymm
  · apply le_csInf hne
    rintro _ ⟨xs, hx, rfl⟩
    rw [← hx]
    exact projectiveSeminorm_sum_tprod_le xs
  · change sInf R ≤ ‖z‖
    rw [PiTensorProduct.norm_def]
    exact le_ciInf fun p ↦ csInf_le hb (hmem p)

end

end ArakelovGeometry
