/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.Analysis.DeterminantNorm
import ArakelovGeometry.Analysis.ArchimedeanDual
import ArakelovGeometry.Analysis.UltrametricDual
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic

/-!
# Norms on scalar extensions

Projective and injective norms on the actual scalar extension `L ⊗[k] E`
for an isometric extension of complete valued fields. The constructions retain
trivial valuations and the zero-dimensional case.
-/

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {k L E : Type*} [NormedField k] [NormedField L] [NormedAlgebra k L]
  [NormedAddCommGroup E] [NormedSpace k E]

/-- Evaluation of a rational functional after scalar extension. -/
def scalarExtensionDualEval (f : E →ₗ[k] k) : L ⊗[k] E →ₗ[L] L :=
  LinearMap.liftBaseChange L ((Algebra.linearMap k L).comp f)

@[simp]
theorem scalarExtensionDualEval_tmul (f : E →ₗ[k] k) (a : L) (x : E) :
    scalarExtensionDualEval f (a ⊗ₜ[k] x) = a * algebraMap k L (f x) := by
  simp [scalarExtensionDualEval]

@[simp]
theorem scalarExtensionDualEval_zero :
    scalarExtensionDualEval (0 : E →ₗ[k] k) = (0 : L ⊗[k] E →ₗ[L] L) := by
  simp [scalarExtensionDualEval]

private def extensionSum (p : List (L × E)) : L ⊗[k] E :=
  (p.map fun q ↦ q.1 ⊗ₜ[k] q.2).sum

private def extensionCost (p : List (L × E)) : ℝ :=
  (p.map fun q ↦ ‖q.1‖ * ‖q.2‖).sum

private theorem extensionCost_nonneg (p : List (L × E)) : 0 ≤ extensionCost p := by
  apply List.sum_nonneg
  intro r hr
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem exists_extensionSum (z : L ⊗[k] E) : ∃ p, extensionSum p = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨[], rfl⟩
  | tmul a x => exact ⟨[(a, x)], by simp [extensionSum]⟩
  | add z t hz ht =>
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨q, rfl⟩ := ht
    exact ⟨p ++ q, by simp [extensionSum]⟩

private def extensionCosts (z : L ⊗[k] E) : Set ℝ :=
  {c | ∃ p : List (L × E), extensionSum p = z ∧ extensionCost p = c}

private theorem extensionCosts_nonempty (z : L ⊗[k] E) : (extensionCosts z).Nonempty := by
  obtain ⟨p, hp⟩ := exists_extensionSum z
  exact ⟨_, p, hp, rfl⟩

private theorem extensionCosts_bddBelow (z : L ⊗[k] E) : BddBelow (extensionCosts z) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨p, _, rfl⟩
  exact extensionCost_nonneg p

private def extensionProjectiveValue (z : L ⊗[k] E) : ℝ := sInf (extensionCosts z)

private theorem extensionProjectiveValue_nonneg (z : L ⊗[k] E) :
    0 ≤ extensionProjectiveValue z := by
  apply le_csInf (extensionCosts_nonempty z)
  rintro _ ⟨p, _, rfl⟩
  exact extensionCost_nonneg p

private theorem extensionProjectiveValue_le (p : List (L × E)) :
    extensionProjectiveValue (extensionSum (k := k) p) ≤ extensionCost p :=
  csInf_le (extensionCosts_bddBelow _) ⟨p, rfl, rfl⟩

private theorem extensionProjectiveValue_zero :
    extensionProjectiveValue (0 : L ⊗[k] E) = 0 := by
  apply le_antisymm _ (extensionProjectiveValue_nonneg _)
  exact extensionProjectiveValue_le (k := k) ([] : List (L × E))

private theorem exists_extensionCost_lt (z : L ⊗[k] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ p, extensionSum p = z ∧ extensionCost p < extensionProjectiveValue z + ε := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hc⟩ := Real.lt_sInf_add_pos (extensionCosts_nonempty z) hε
  exact ⟨p, hp, hc⟩

private theorem extensionProjectiveValue_add_le (z t : L ⊗[k] E) :
    extensionProjectiveValue (z + t) ≤ extensionProjectiveValue z +
      extensionProjectiveValue t := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, hp, hpc⟩ := exists_extensionCost_lt z (half_pos hε)
  obtain ⟨q, hq, hqc⟩ := exists_extensionCost_lt t (half_pos hε)
  have hpq : extensionSum (p ++ q) = z + t := by
    simp only [extensionSum, List.map_append, List.sum_append] at hp hq ⊢
    rw [hp, hq]
  have hc : extensionCost (p ++ q) = extensionCost p + extensionCost q := by
    simp [extensionCost]
  have h := extensionProjectiveValue_le (k := k) (p ++ q)
  rw [hpq, hc] at h
  linarith

private theorem extensionSum_mul (p : List (L × E)) (a : L) :
    extensionSum (k := k) (p.map fun q ↦ (a * q.1, q.2)) = a • extensionSum p := by
  induction p with
  | nil => simp [extensionSum]
  | cons q p hp =>
    change (a * q.1) ⊗ₜ[k] q.2 + extensionSum (p.map fun q ↦ (a * q.1, q.2)) =
      a • (q.1 ⊗ₜ[k] q.2 + extensionSum p)
    rw [smul_add, hp]
    congr 1

private theorem extensionCost_mul (p : List (L × E)) (a : L) :
    extensionCost (p.map fun q ↦ (a * q.1, q.2)) = ‖a‖ * extensionCost p := by
  simp [extensionCost, List.map_map, Function.comp_def, norm_mul, mul_assoc,
    List.sum_map_mul_left]

private theorem extensionProjectiveValue_smul_le (a : L) (z : L ⊗[k] E) :
    extensionProjectiveValue (a • z) ≤ ‖a‖ * extensionProjectiveValue z := by
  by_cases ha : a = 0
  · simp only [ha, zero_smul, extensionProjectiveValue_zero, norm_zero, zero_mul, le_refl]
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, hp, hc⟩ := exists_extensionCost_lt z (div_pos hε ha0)
  have h := extensionProjectiveValue_le (k := k) (p.map fun q ↦ (a * q.1, q.2))
  rw [extensionSum_mul, hp, extensionCost_mul] at h
  have h' := mul_lt_mul_of_pos_left hc ha0
  rw [mul_add, mul_div_cancel₀ _ ha0.ne'] at h'
  exact h.trans h'.le

/-- The source projective seminorm on the actual scalar extension: the
infimum of the sum of scalar norms times vector norms over tensor decompositions. -/
def scalarExtensionProjectiveSeminorm : Seminorm L (L ⊗[k] E) :=
  .ofSMulLE extensionProjectiveValue extensionProjectiveValue_zero
    extensionProjectiveValue_add_le extensionProjectiveValue_smul_le

/-- Exact finite-decomposition formula for the projective scalar-extension seminorm. -/
theorem scalarExtensionProjectiveSeminorm_eq_sInf (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm z = sInf {c : ℝ |
      ∃ p : List (L × E), (p.map fun q ↦ q.1 ⊗ₜ[k] q.2).sum = z ∧
        (p.map fun q ↦ ‖q.1‖ * ‖q.2‖).sum = c} := rfl

/-- Pure scalar tensors have the expected projective upper bound. -/
theorem scalarExtensionProjectiveSeminorm_tmul_le (a : L) (x : E) :
    scalarExtensionProjectiveSeminorm (a ⊗ₜ[k] x) ≤ ‖a‖ * ‖x‖ := by
  change extensionProjectiveValue (a ⊗ₜ[k] x) ≤ _
  simpa only [extensionSum, extensionCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] using extensionProjectiveValue_le (k := k) [(a, x)]

/-- The projective extension is maximal among seminorms bounded by the
original norm on rational vectors. -/
theorem le_scalarExtensionProjectiveSeminorm (p : Seminorm L (L ⊗[k] E))
    (hp : ∀ x : E, p ((1 : L) ⊗ₜ[k] x) ≤ ‖x‖) :
    p ≤ scalarExtensionProjectiveSeminorm := by
  intro z
  change p z ≤ sInf (extensionCosts z)
  apply le_csInf (extensionCosts_nonempty z)
  rintro _ ⟨xs, hx, rfl⟩
  rw [← hx]
  clear hx
  induction xs with
  | nil => simp [extensionSum, extensionCost]
  | cons q xs hxs =>
    change p (q.1 ⊗ₜ[k] q.2 + extensionSum xs) ≤ ‖q.1‖ * ‖q.2‖ + extensionCost xs
    apply (map_add_le_add p _ _).trans (add_le_add _ hxs)
    have hq : q.1 ⊗ₜ[k] q.2 = q.1 • ((1 : L) ⊗ₜ[k] q.2) := by
      change q.1 ⊗ₜ[k] q.2 = (q.1 * 1) ⊗ₜ[k] q.2
      rw [mul_one]
    rw [hq, map_smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hp q.2) (norm_nonneg q.1)

variable [CompleteSpace k] [FiniteDimensional k E]

/-- A normalized extended rational functional, as an `L`-seminorm. -/
def scalarExtensionDualRatioSeminorm (f : E →ₗ[k] k) : Seminorm L (L ⊗[k] E) :=
  NNReal.mk (linearMapOperatorSeminorm f)⁻¹ (inv_nonneg.mpr (apply_nonneg _ _)) •
    (normSeminorm L L).comp (scalarExtensionDualEval f)

@[simp]
theorem scalarExtensionDualRatioSeminorm_apply (f : E →ₗ[k] k) (z : L ⊗[k] E) :
    scalarExtensionDualRatioSeminorm f z =
      ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f := by
  change (linearMapOperatorSeminorm f)⁻¹ * ‖scalarExtensionDualEval f z‖ = _
  rw [div_eq_mul_inv, mul_comm]

/-- Each normalized extended functional is bounded by the projective norm. -/
theorem scalarExtensionDualRatioSeminorm_le_projective (f : E →ₗ[k] k) :
    scalarExtensionDualRatioSeminorm (L := L) f ≤ scalarExtensionProjectiveSeminorm := by
  apply le_scalarExtensionProjectiveSeminorm
  intro x
  rw [scalarExtensionDualRatioSeminorm_apply, scalarExtensionDualEval_tmul,
    one_mul, norm_algebraMap']
  by_cases hf : linearMapOperatorSeminorm f = 0
  · simp only [hf, div_zero, norm_nonneg]
  · have hfpos : 0 < linearMapOperatorSeminorm f :=
      lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hf)
    exact (div_le_iff₀ hfpos).mpr (by
      simpa only [mul_comm] using norm_linearMap_apply_le f x)

private theorem scalarExtensionDualRatioSeminorm_bddAbove :
    BddAbove (Set.range (scalarExtensionDualRatioSeminorm (k := k) (L := L) (E := E))) :=
  ⟨scalarExtensionProjectiveSeminorm, by
    rintro _ ⟨f, rfl⟩
    exact scalarExtensionDualRatioSeminorm_le_projective f⟩

/-- The injective scalar-extension seminorm from the original field's
bounded linear functionals, as specified by the source supremum. -/
def scalarExtensionInjectiveSeminorm : Seminorm L (L ⊗[k] E) :=
  sSup (Set.range scalarExtensionDualRatioSeminorm)

/-- Every normalized rational dual evaluation is below the injective norm. -/
theorem scalarExtensionDualRatioSeminorm_le_injective (f : E →ₗ[k] k) :
    scalarExtensionDualRatioSeminorm (L := L) f ≤ scalarExtensionInjectiveSeminorm :=
  le_csSup scalarExtensionDualRatioSeminorm_bddAbove ⟨f, rfl⟩

/-- The injective extension is bounded by the projective extension. -/
theorem scalarExtensionInjectiveSeminorm_le_projective :
    scalarExtensionInjectiveSeminorm (k := k) (L := L) (E := E) ≤
      scalarExtensionProjectiveSeminorm := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨f, rfl⟩
  exact scalarExtensionDualRatioSeminorm_le_projective f

/-- A pointwise injective bound is equivalent to a bound on every rational
dual evaluation ratio. -/
theorem scalarExtensionInjectiveSeminorm_le_iff (z : L ⊗[k] E) (C : ℝ) :
    scalarExtensionInjectiveSeminorm z ≤ C ↔ ∀ f : E →ₗ[k] k,
      ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f ≤ C := by
  constructor
  · intro h f
    exact (scalarExtensionDualRatioSeminorm_apply f z).symm.le.trans
      ((scalarExtensionDualRatioSeminorm_le_injective f z).trans h)
  · intro h
    rw [scalarExtensionInjectiveSeminorm,
      Seminorm.sSup_apply scalarExtensionDualRatioSeminorm_bddAbove]
    apply ciSup_le
    rintro ⟨p, f, rfl⟩
    exact (scalarExtensionDualRatioSeminorm_apply f z).le.trans (h f)

omit [CompleteSpace k] [FiniteDimensional k E] in
/-- Extended coordinate functionals are the coordinates of the extended basis. -/
theorem scalarExtensionDualEval_coord {ι : Type*} (b : Module.Basis ι k E) (i : ι) :
    scalarExtensionDualEval (L := L) (b.coord i) = (b.baseChange L).coord i := by
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext
  ext a x
  change scalarExtensionDualEval (b.coord i) (a ⊗ₜ[k] x) =
    (b.baseChange L).coord i (a ⊗ₜ[k] x)
  simp only [scalarExtensionDualEval_tmul,
    Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

omit [CompleteSpace k] in
/-- Rational dual evaluations separate every element of the scalar extension. -/
theorem eq_zero_of_scalarExtensionDualEval_eq_zero (z : L ⊗[k] E)
    (hz : ∀ f : E →ₗ[k] k, scalarExtensionDualEval f z = 0) : z = 0 := by
  let b := Module.finBasis k E
  apply (b.baseChange L).ext_elem
  intro i
  have h := hz (b.coord i)
  rw [scalarExtensionDualEval_coord] at h
  simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using h

/-- The injective scalar-extension seminorm separates zero, even at trivial
valuations and in dimension zero. -/
theorem scalarExtensionInjectiveSeminorm_eq_zero_iff (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply eq_zero_of_scalarExtensionDualEval_eq_zero z
    intro f
    by_cases hf : f = 0
    · simp only [hf, scalarExtensionDualEval_zero, LinearMap.zero_apply]
    · have hfn : 0 < linearMapOperatorSeminorm f :=
        lt_of_le_of_ne (apply_nonneg _ _)
          (fun h ↦ hf ((linearMapOperatorSeminorm_eq_zero_iff f).mp h.symm))
      have h := (scalarExtensionInjectiveSeminorm_le_iff z 0).mp hz.le f
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [zero_mul] using (div_le_iff₀ hfn).mp h)
        (norm_nonneg _)
  · rintro rfl
    exact map_zero _

/-- Separation of the projective norm follows from the injective lower bound. -/
theorem scalarExtensionProjectiveSeminorm_eq_zero_iff (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply (scalarExtensionInjectiveSeminorm_eq_zero_iff z).mp
    exact le_antisymm ((scalarExtensionInjectiveSeminorm_le_projective z).trans hz.le)
      (apply_nonneg _ _)
  · rintro rfl
    exact map_zero _

/-- Exact injective supremum formula, with the zero functional admitted using
the harmless convention `0 / 0 = 0`. -/
theorem scalarExtensionInjectiveSeminorm_eq_sSup (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm z = sSup (Set.range fun f : E →ₗ[k] k ↦
      ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f) := by
  have hb : BddAbove (Set.range fun f : E →ₗ[k] k ↦
      ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f) := by
    refine ⟨scalarExtensionProjectiveSeminorm z, ?_⟩
    rintro _ ⟨f, rfl⟩
    simpa only [scalarExtensionDualRatioSeminorm_apply] using
      scalarExtensionDualRatioSeminorm_le_projective f z
  apply le_antisymm
  · apply (scalarExtensionInjectiveSeminorm_le_iff z _).2
    intro f
    exact le_csSup hb ⟨f, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨f, rfl⟩
    simpa only [scalarExtensionDualRatioSeminorm_apply] using
      scalarExtensionDualRatioSeminorm_le_injective f z

/-- The source formula uses precisely the nonzero rational functionals.
When the dual is zero the supremum is zero. -/
theorem scalarExtensionInjectiveSeminorm_eq_sSup_nonzero (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm z = sSup {c : ℝ | ∃ f : E →ₗ[k] k,
      f ≠ 0 ∧ ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f = c} := by
  let R := {c : ℝ | ∃ f : E →ₗ[k] k,
    f ≠ 0 ∧ ‖scalarExtensionDualEval f z‖ / linearMapOperatorSeminorm f = c}
  have hb : BddAbove R := by
    refine ⟨scalarExtensionProjectiveSeminorm z, ?_⟩
    rintro _ ⟨f, _, rfl⟩
    simpa only [scalarExtensionDualRatioSeminorm_apply] using
      scalarExtensionDualRatioSeminorm_le_projective f z
  change scalarExtensionInjectiveSeminorm z = sSup R
  by_cases hR : R.Nonempty
  · have h0 : 0 ≤ sSup R := by
      obtain ⟨_, f, hf, rfl⟩ := hR
      exact (div_nonneg (norm_nonneg _) (apply_nonneg _ _)).trans
        (le_csSup hb ⟨f, hf, rfl⟩)
    apply le_antisymm
    · apply (scalarExtensionInjectiveSeminorm_le_iff z _).2
      intro f
      by_cases hf : f = 0
      · simpa only [hf, map_zero, div_zero] using h0
      · exact le_csSup hb ⟨f, hf, rfl⟩
    · apply csSup_le hR
      rintro _ ⟨f, _, rfl⟩
      simpa only [scalarExtensionDualRatioSeminorm_apply] using
        scalarExtensionDualRatioSeminorm_le_injective f z
  · rw [Set.not_nonempty_iff_eq_empty.mp hR, Real.sSup_empty]
    apply le_antisymm _ (apply_nonneg _ _)
    apply (scalarExtensionInjectiveSeminorm_le_iff z 0).2
    intro f
    have hf : f = 0 := by
      by_contra hf
      exact hR ⟨_, f, hf, rfl⟩
    simp only [hf, map_zero, div_zero, le_refl]

/-- On rational vectors the injective extension is the bidual supremum of
the original norm; equality with the original norm is a separate assertion. -/
theorem scalarExtensionInjectiveSeminorm_one_tmul (x : E) :
    scalarExtensionInjectiveSeminorm ((1 : L) ⊗ₜ[k] x) =
      sSup (Set.range fun f : E →ₗ[k] k ↦ ‖f x‖ / linearMapOperatorSeminorm f) := by
  rw [scalarExtensionInjectiveSeminorm_eq_sSup]
  simp only [scalarExtensionDualEval_tmul, one_mul, norm_algebraMap']

/-- At a non-Archimedean extension field the injective extension is
ultrametric, whether or not the original vector norm was ultrametric. -/
theorem scalarExtensionInjectiveSeminorm_add_le_max
    (hL : ∀ a b : L, ‖a + b‖ ≤ max ‖a‖ ‖b‖) (z t : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm (z + t) ≤
      max (scalarExtensionInjectiveSeminorm z) (scalarExtensionInjectiveSeminorm t) := by
  apply (scalarExtensionInjectiveSeminorm_le_iff _ _).2
  intro f
  have hD : 0 ≤ linearMapOperatorSeminorm f := apply_nonneg _ _
  calc
    ‖scalarExtensionDualEval f (z + t)‖ / linearMapOperatorSeminorm f ≤
        max ‖scalarExtensionDualEval f z‖ ‖scalarExtensionDualEval f t‖ /
          linearMapOperatorSeminorm f := by
      rw [map_add]
      exact div_le_div_of_nonneg_right (hL _ _) hD
    _ = max (scalarExtensionDualRatioSeminorm f z)
        (scalarExtensionDualRatioSeminorm f t) := by
      rw [scalarExtensionDualRatioSeminorm_apply, scalarExtensionDualRatioSeminorm_apply,
        max_div_div_right hD]
    _ ≤ _ := max_le_max (scalarExtensionDualRatioSeminorm_le_injective f z)
      (scalarExtensionDualRatioSeminorm_le_injective f t)

/-- Both scalar-extension norms have their unique possible value when the
original vector space is zero. -/
theorem scalarExtensionSeminorms_eq_zero_of_subsingleton [Subsingleton E] (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm z = 0 ∧ scalarExtensionInjectiveSeminorm z = 0 := by
  rw [Subsingleton.elim z 0]
  exact ⟨map_zero _, map_zero _⟩

omit [CompleteSpace k] [FiniteDimensional k E] in
/-- Rational vectors have projective extension norm at most their original norm. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_le (x : E) :
    scalarExtensionProjectiveSeminorm ((1 : L) ⊗ₜ[k] x) ≤ ‖x‖ := by
  simpa only [norm_one, one_mul] using scalarExtensionProjectiveSeminorm_tmul_le (1 : L) x

/-- Rational vectors have injective extension norm at most their original norm. -/
theorem scalarExtensionInjectiveSeminorm_one_tmul_le (x : E) :
    scalarExtensionInjectiveSeminorm ((1 : L) ⊗ₜ[k] x) ≤ ‖x‖ :=
  (scalarExtensionInjectiveSeminorm_le_projective _).trans
    (scalarExtensionProjectiveSeminorm_one_tmul_le x)

/-- Extended dual evaluation is bounded by the injective extension times
the original dual norm. -/
theorem norm_scalarExtensionDualEval_le_injective (f : E →ₗ[k] k) (z : L ⊗[k] E) :
    ‖scalarExtensionDualEval f z‖ ≤
      scalarExtensionInjectiveSeminorm z * linearMapOperatorSeminorm f := by
  by_cases hf : f = 0
  · simp only [hf, scalarExtensionDualEval_zero, LinearMap.zero_apply, norm_zero,
      map_zero, mul_zero, le_refl]
  have hfn : 0 < linearMapOperatorSeminorm f :=
    lt_of_le_of_ne (apply_nonneg _ _)
      (fun h ↦ hf ((linearMapOperatorSeminorm_eq_zero_iff f).mp h.symm))
  apply (div_le_iff₀ hfn).mp
  simpa only [scalarExtensionDualRatioSeminorm_apply] using
    scalarExtensionDualRatioSeminorm_le_injective f z

private theorem seminorm_sum_le_of_ultrametric {ι W : Type*} [AddCommGroup W] [Module L W]
    (p : Seminorm L W) (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (s : Finset ι) (x : ι → W) {C : ℝ} (hC : 0 ≤ C) (hx : ∀ i ∈ s, p (x i) ≤ C) :
    p (∑ i ∈ s, x i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, map_zero] using hC
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi]
    exact (hp _ _).trans (max_le (hx i (Finset.mem_insert_self _ _))
      (hs fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)))

/-- The injective scalar extension dominates every ultrametric seminorm
whose restriction to rational vectors is bounded by the original norm.
The proof uses the nearly optimal bases of the original norm. -/
theorem le_scalarExtensionInjectiveSeminorm_of_ultrametric
    (p : Seminorm L (L ⊗[k] E)) (hp : ∀ z t, p (z + t) ≤ max (p z) (p t))
    (hbound : ∀ x : E, p ((1 : L) ⊗ₜ[k] x) ≤ ‖x‖) :
    p ≤ scalarExtensionInjectiveSeminorm := by
  intro z
  have hαbound (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      p z ≤ scalarExtensionInjectiveSeminorm z * α⁻¹ := by
    obtain ⟨b, hb⟩ := exists_finBasis_mul_dual_norm_le (L := k) (E := E) hα hα1
    let B := b.baseChange L
    conv_lhs => rw [← B.sum_repr z]
    apply seminorm_sum_le_of_ultrametric p hp _ _
      (mul_nonneg (apply_nonneg _ _) (inv_nonneg.mpr hα.le))
    intro i _
    have heval := norm_scalarExtensionDualEval_le_injective (L := L) (b.coord i) z
    rw [scalarExtensionDualEval_coord] at heval
    change ‖(B.repr z) i‖ ≤ scalarExtensionInjectiveSeminorm z *
      linearMapOperatorSeminorm (b.coord i) at heval
    have hbi : p (B i) ≤ ‖b i‖ := by
      simpa only [B, Module.Basis.baseChange_apply] using hbound (b i)
    calc
      p ((B.repr z) i • B i) = ‖(B.repr z) i‖ * p (B i) := map_smul_eq_mul _ _ _
      _ ≤ (scalarExtensionInjectiveSeminorm z * linearMapOperatorSeminorm (b.coord i)) *
          ‖b i‖ := mul_le_mul heval hbi (apply_nonneg _ _) (by positivity)
      _ = scalarExtensionInjectiveSeminorm z *
          (‖b i‖ * linearMapOperatorSeminorm (b.coord i)) := by ring
      _ ≤ scalarExtensionInjectiveSeminorm z * α⁻¹ :=
        mul_le_mul_of_nonneg_left (hb i).2 (apply_nonneg _ _)
  have hlim : Filter.Tendsto (fun α : ℝ ↦ scalarExtensionInjectiveSeminorm z * α⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (scalarExtensionInjectiveSeminorm z)) := by
    have hc : ContinuousAt (fun α : ℝ ↦ scalarExtensionInjectiveSeminorm z * α⁻¹) 1 :=
      continuousAt_const.mul (continuousAt_id.inv₀ one_ne_zero)
    simpa only [inv_one, mul_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with α hα1 hα
  exact hαbound α hα hα1

omit [FiniteDimensional k E] in
private theorem norm_le_mul_extensionCost_of_ultrametric [IsUltrametricDist L]
    (x : E) (p : List (L × E)) (hp : extensionSum p = (1 : L) ⊗ₜ[k] x)
    {A : ℝ} (hA : 1 < A) : ‖x‖ ≤ A * extensionCost p := by
  classical
  let s : Finset L := insert 1 (p.map Prod.fst).toFinset
  let H : Submodule k L := Submodule.span k (s : Set L)
  let : FiniteDimensional k H := FiniteDimensional.span_finset k s
  have h1 : (1 : L) ∈ H := Submodule.subset_span (by simp [s])
  let oneH : H := ⟨1, h1⟩
  have h1ne : oneH ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    exact one_ne_zero this
  obtain ⟨u, hu, hun⟩ := exists_ultrametric_norming_functional (L := k) (V := H) h1ne hA
  have huA : linearMapOperatorSeminorm u ≤ A := by
    change linearMapOperatorSeminorm u ≤ A / ‖(1 : L)‖ at hun
    simpa only [norm_one, div_one] using hun
  let coeff (q : {q // q ∈ p}) : H :=
    ⟨q.val.1, Submodule.subset_span (by
      exact Finset.mem_insert_of_mem
        (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q.val, q.property, rfl⟩)))⟩
  let t : H ⊗[k] E := (p.attach.map fun q ↦ coeff q ⊗ₜ[k] q.val.2).sum
  have ht : t = oneH ⊗ₜ[k] x := by
    apply Module.Flat.rTensor_preserves_injective_linearMap H.subtype H.subtype_injective
    simpa only [t, map_list_sum, List.map_map, Function.comp_def, LinearMap.rTensor_tmul,
      Submodule.subtype_apply, coeff, oneH,
      List.attach_map_val (f := fun q : L × E ↦ q.1 ⊗ₜ[k] q.2), extensionSum] using hp
  let ev := (TensorProduct.lid k E).toLinearMap.comp (u.rTensor E)
  have hexp : (p.attach.map fun q ↦ u (coeff q) • q.val.2).sum = x := by
    have h := congrArg ev ht
    simpa only [ev, LinearMap.comp_apply, t, map_list_sum, List.map_map, Function.comp_def,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, hu, one_smul] using h
  rw [← hexp]
  calc
    ‖(p.attach.map fun q ↦ u (coeff q) • q.val.2).sum‖ ≤
        (p.attach.map fun q ↦ ‖u (coeff q) • q.val.2‖).sum := by
      simpa only [List.map_map, Function.comp_def, Multiset.sum_coe, Multiset.map_coe] using
        norm_multiset_sum_le ((p.attach.map fun q ↦ u (coeff q) • q.val.2) : Multiset E)
    _ ≤ (p.attach.map fun q ↦ A * (‖q.val.1‖ * ‖q.val.2‖)).sum := by
      apply List.sum_le_sum
      intro q _
      rw [norm_smul]
      calc
        ‖u (coeff q)‖ * ‖q.val.2‖ ≤
            (linearMapOperatorSeminorm u * ‖coeff q‖) * ‖q.val.2‖ :=
          mul_le_mul_of_nonneg_right (norm_linearMap_apply_le u _) (norm_nonneg _)
        _ ≤ (A * ‖coeff q‖) * ‖q.val.2‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right huA (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by rw [mul_assoc]; rfl
    _ = A * extensionCost p := by
      rw [List.attach_map_val (f := fun q : L × E ↦ A * (‖q.1‖ * ‖q.2‖))]
      simp only [extensionCost, List.sum_map_mul_left]

omit [FiniteDimensional k E] in
/-- Projective scalar extension preserves the original norm on rational
vectors over a non-Archimedean extension field. The original vector norm
need not be ultrametric; trivial valuations are included. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_ultrametric [IsUltrametricDist L]
    (x : E) : scalarExtensionProjectiveSeminorm ((1 : L) ⊗ₜ[k] x) = ‖x‖ := by
  apply le_antisymm (scalarExtensionProjectiveSeminorm_one_tmul_le (k := k) (L := L) x)
  change ‖x‖ ≤ sInf (extensionCosts ((1 : L) ⊗ₜ[k] x))
  apply le_csInf (extensionCosts_nonempty _)
  rintro _ ⟨p, hp, rfl⟩
  have hlim : Filter.Tendsto (fun A : ℝ ↦ A * extensionCost p)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (extensionCost p)) := by
    have hc : ContinuousAt (fun A : ℝ ↦ A * extensionCost p) 1 :=
      continuousAt_id.mul continuousAt_const
    simpa only [one_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with A hA
  exact norm_le_mul_extensionCost_of_ultrametric x p hp hA

/-! These structures install the separated scalar-extension seminorms on the
actual tensor product. They are not global instances, since the projective
and injective constructions generally give different norms. -/

/-- The normed additive group of the projective scalar extension. -/
abbrev scalarExtensionProjectiveNormedAddCommGroup : NormedAddCommGroup (L ⊗[k] E) :=
  (⟨(scalarExtensionProjectiveSeminorm (k := k) (L := L) (E := E)).toAddGroupSeminorm,
    fun z ↦ (scalarExtensionProjectiveSeminorm_eq_zero_iff z).mp⟩ :
    AddGroupNorm (L ⊗[k] E)).toNormedAddCommGroup

/-- Scalar compatibility of the projective scalar-extension norm. -/
abbrev scalarExtensionProjectiveNormedSpace :
    letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    NormedSpace L (L ⊗[k] E) := by
  letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  exact ⟨fun a z ↦ (map_smul_eq_mul scalarExtensionProjectiveSeminorm a z).le⟩

/-- The normed additive group of the injective scalar extension. -/
abbrev scalarExtensionInjectiveNormedAddCommGroup : NormedAddCommGroup (L ⊗[k] E) :=
  (⟨(scalarExtensionInjectiveSeminorm (k := k) (L := L) (E := E)).toAddGroupSeminorm,
    fun z ↦ (scalarExtensionInjectiveSeminorm_eq_zero_iff z).mp⟩ :
    AddGroupNorm (L ⊗[k] E)).toNormedAddCommGroup

/-- Scalar compatibility of the injective scalar-extension norm. -/
abbrev scalarExtensionInjectiveNormedSpace :
    letI := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    NormedSpace L (L ⊗[k] E) := by
  letI := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  exact ⟨fun a z ↦ (map_smul_eq_mul scalarExtensionInjectiveSeminorm a z).le⟩

/-- Extending a functional preserves its dual norm for the projective
scalar-extension norm. This includes the zero space and trivial valuations. -/
theorem scalarExtensionProjective_dualNorm [CompleteSpace L] (f : E →ₗ[k] k) :
    letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
    linearMapOperatorSeminorm (scalarExtensionDualEval (L := L) f) =
      linearMapOperatorSeminorm f := by
  let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le _ (apply_nonneg _ _)
    intro z
    calc
      ‖scalarExtensionDualEval f z‖ ≤
          scalarExtensionInjectiveSeminorm z * linearMapOperatorSeminorm f :=
        norm_scalarExtensionDualEval_le_injective f z
      _ ≤ scalarExtensionProjectiveSeminorm z * linearMapOperatorSeminorm f :=
        mul_le_mul_of_nonneg_right (scalarExtensionInjectiveSeminorm_le_projective z)
          (apply_nonneg _ _)
      _ = linearMapOperatorSeminorm f * ‖z‖ := mul_comm _ _
  · apply linearMapOperatorSeminorm_le f (apply_nonneg _ _)
    intro x
    have h := norm_linearMap_apply_le (scalarExtensionDualEval (L := L) f)
      ((1 : L) ⊗ₜ[k] x)
    rw [scalarExtensionDualEval_tmul, one_mul, norm_algebraMap'] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (scalarExtensionProjectiveSeminorm_one_tmul_le (L := L) x) (apply_nonneg _ _))

/-- Extending a functional preserves its dual norm for the injective
scalar-extension norm, even when rational vector norms decrease. -/
theorem scalarExtensionInjective_dualNorm [CompleteSpace L] (f : E →ₗ[k] k) :
    letI := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
    linearMapOperatorSeminorm (scalarExtensionDualEval (L := L) f) =
      linearMapOperatorSeminorm f := by
  let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
  apply le_antisymm
  · apply linearMapOperatorSeminorm_le _ (apply_nonneg _ _)
    intro z
    change ‖scalarExtensionDualEval f z‖ ≤
      linearMapOperatorSeminorm f * scalarExtensionInjectiveSeminorm z
    simpa only [mul_comm] using norm_scalarExtensionDualEval_le_injective f z
  · apply linearMapOperatorSeminorm_le f (apply_nonneg _ _)
    intro x
    have h := norm_linearMap_apply_le (scalarExtensionDualEval (L := L) f)
      ((1 : L) ⊗ₜ[k] x)
    rw [scalarExtensionDualEval_tmul, one_mul, norm_algebraMap'] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (scalarExtensionInjectiveSeminorm_one_tmul_le (L := L) x) (apply_nonneg _ _))

end

noncomputable section Archimedean

variable {k L E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
  [IsRCLikeNormedField k] [NormedField L] [NormedAlgebra k L]
  [NormedAddCommGroup E] [NormedSpace k E] [FiniteDimensional k E]

/-- Rational vectors retain their norm under injective extension over a
scalar field with its usual real or complex norm. -/
theorem scalarExtensionInjectiveSeminorm_one_tmul_archimedean (x : E) :
    scalarExtensionInjectiveSeminorm ((1 : L) ⊗ₜ[k] x) = ‖x‖ := by
  apply le_antisymm (scalarExtensionInjectiveSeminorm_one_tmul_le x)
  apply norm_le_of_forall_linearMap_apply_le_archimedean (L := k) (apply_nonneg _ _)
  intro f
  simpa only [scalarExtensionDualEval_tmul, one_mul, norm_algebraMap', mul_comm] using
    norm_scalarExtensionDualEval_le_injective f ((1 : L) ⊗ₜ[k] x)

/-- The projective extension is isometric on rational vectors over the
usual real or complex scalar norm. -/
theorem scalarExtensionProjectiveSeminorm_one_tmul_archimedean (x : E) :
    scalarExtensionProjectiveSeminorm ((1 : L) ⊗ₜ[k] x) = ‖x‖ := by
  apply le_antisymm (scalarExtensionProjectiveSeminorm_one_tmul_le (k := k) (L := L) x)
  rw [← scalarExtensionInjectiveSeminorm_one_tmul_archimedean (k := k) (L := L) x]
  exact scalarExtensionInjectiveSeminorm_le_projective _

end Archimedean

noncomputable section Tower

variable {k L M E : Type*} [NormedField k] [NormedField L] [NormedField M]
  [NormedAlgebra k L] [NormedAlgebra k M] [NormedAlgebra L M] [IsScalarTower k L M]
  [CompleteSpace k] [CompleteSpace L]
  [NormedAddCommGroup E] [NormedSpace k E] [FiniteDimensional k E]

omit [CompleteSpace L] in
/-- Projective scalar extension is transitive under the canonical tensor
reassociation. No Archimedean or nontrivial-valuation hypothesis is needed. -/
theorem scalarExtensionProjectiveSeminorm_comp (z : M ⊗[L] (L ⊗[k] E)) :
    letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
    scalarExtensionProjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionProjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E z) := by
  let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
  let p : Seminorm M (M ⊗[k] E) := scalarExtensionProjectiveSeminorm
  let q : Seminorm M (M ⊗[L] (L ⊗[k] E)) := scalarExtensionProjectiveSeminorm
  have hupper : q.comp e.symm.toLinearMap ≤ p := by
    apply le_scalarExtensionProjectiveSeminorm
    intro x
    change q (e.symm ((1 : M) ⊗ₜ[k] x)) ≤ ‖x‖
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    exact (scalarExtensionProjectiveSeminorm_one_tmul_le ((1 : L) ⊗ₜ[k] x)).trans
      (scalarExtensionProjectiveSeminorm_one_tmul_le (L := L) x)
  have hbound (y : L ⊗[k] E) : p (e ((1 : M) ⊗ₜ[L] y)) ≤ ‖y‖ := by
    let s : Seminorm L (L ⊗[k] E) := ((p.comp e.toLinearMap).restrictScalars L).comp
      (TensorProduct.mk L M (L ⊗[k] E) 1)
    have hs : s ≤ scalarExtensionProjectiveSeminorm (k := k) (L := L) := by
      apply le_scalarExtensionProjectiveSeminorm
      intro x
      change p (e ((1 : M) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] x))) ≤ ‖x‖
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
      exact scalarExtensionProjectiveSeminorm_one_tmul_le (L := M) x
    exact hs y
  have hlower : p.comp e.toLinearMap ≤ q :=
    le_scalarExtensionProjectiveSeminorm _ hbound
  apply le_antisymm
  · have h := hupper (e z)
    simpa only [Seminorm.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  · exact hlower z


/-- Injective scalar extension is transitive over a non-Archimedean
extension field. The original vector norm need not be ultrametric. -/
theorem scalarExtensionInjectiveSeminorm_comp [IsUltrametricDist M]
    (z : M ⊗[L] (L ⊗[k] E)) :
    letI := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
    scalarExtensionInjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionInjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E z) := by
  let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
  let p : Seminorm M (M ⊗[k] E) := scalarExtensionInjectiveSeminorm
  let q : Seminorm M (M ⊗[L] (L ⊗[k] E)) := scalarExtensionInjectiveSeminorm
  have hp (u v : M ⊗[k] E) : p (u + v) ≤ max (p u) (p v) :=
    scalarExtensionInjectiveSeminorm_add_le_max IsUltrametricDist.norm_add_le_max u v
  have hq (u v : M ⊗[L] (L ⊗[k] E)) : q (u + v) ≤ max (q u) (q v) :=
    scalarExtensionInjectiveSeminorm_add_le_max IsUltrametricDist.norm_add_le_max u v
  have hupper : q.comp e.symm.toLinearMap ≤ p := by
    apply le_scalarExtensionInjectiveSeminorm_of_ultrametric
    · intro u v
      change q (e.symm (u + v)) ≤ max (q (e.symm u)) (q (e.symm v))
      rw [map_add]
      exact hq _ _
    · intro x
      change q (e.symm ((1 : M) ⊗ₜ[k] x)) ≤ ‖x‖
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      exact (scalarExtensionInjectiveSeminorm_one_tmul_le ((1 : L) ⊗ₜ[k] x)).trans
        (scalarExtensionInjectiveSeminorm_one_tmul_le (L := L) x)
  have hbound (y : L ⊗[k] E) : p (e ((1 : M) ⊗ₜ[L] y)) ≤ ‖y‖ := by
    let s : Seminorm L (L ⊗[k] E) := ((p.comp e.toLinearMap).restrictScalars L).comp
      (TensorProduct.mk L M (L ⊗[k] E) 1)
    have hs : s ≤ scalarExtensionInjectiveSeminorm (k := k) (L := L) := by
      apply le_scalarExtensionInjectiveSeminorm_of_ultrametric
      · intro u v
        change p (e ((1 : M) ⊗ₜ[L] (u + v))) ≤
          max (p (e ((1 : M) ⊗ₜ[L] u))) (p (e ((1 : M) ⊗ₜ[L] v)))
        rw [TensorProduct.tmul_add, map_add]
        exact hp _ _
      · intro x
        change p (e ((1 : M) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] x))) ≤ ‖x‖
        rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
        exact scalarExtensionInjectiveSeminorm_one_tmul_le (L := M) x
    exact hs y
  have hlower : p.comp e.toLinearMap ≤ q := by
    apply le_scalarExtensionInjectiveSeminorm_of_ultrametric _ _ hbound
    intro u v
    change p (e (u + v)) ≤ max (p (e u)) (p (e v))
    rw [map_add]
    exact hp _ _
  apply le_antisymm
  · have h := hupper (e z)
    simpa only [Seminorm.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  · exact hlower z

end Tower


noncomputable section Isometry

variable {k L E F : Type*} [NormedField k] [NormedField L] [NormedAlgebra k L]
  [NormedAddCommGroup E] [NormedSpace k E] [NormedAddCommGroup F] [NormedSpace k F]

/-- Projective scalar extension preserves contractions. -/
theorem scalarExtensionProjectiveSeminorm_baseChange_le (f : E →ₗ[k] F)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm (f.baseChange L z) ≤
      scalarExtensionProjectiveSeminorm z := by
  apply le_scalarExtensionProjectiveSeminorm
    ((scalarExtensionProjectiveSeminorm (E := F)).comp (f.baseChange L)) _ z
  intro x
  change scalarExtensionProjectiveSeminorm (f.baseChange L ((1 : L) ⊗ₜ[k] x)) ≤ ‖x‖
  rw [LinearMap.baseChange_tmul]
  exact (scalarExtensionProjectiveSeminorm_one_tmul_le (f x)).trans (hf x)

/-- Projective scalar-extension norms are unchanged by a linear isometry
of the original normed spaces. -/
theorem scalarExtensionProjectiveSeminorm_baseChange_isometry (e : E ≃ₗᵢ[k] F)
    (z : L ⊗[k] E) :
    scalarExtensionProjectiveSeminorm (LinearEquiv.baseChange k L E F e.toLinearEquiv z) =
      scalarExtensionProjectiveSeminorm z := by
  apply le_antisymm
  · exact scalarExtensionProjectiveSeminorm_baseChange_le e.toLinearMap
      (fun x ↦ (e.norm_map x).le) z
  · have h := scalarExtensionProjectiveSeminorm_baseChange_le e.symm.toLinearMap
      (fun x ↦ (e.symm.norm_map x).le) (LinearEquiv.baseChange k L E F e.toLinearEquiv z)
    change scalarExtensionProjectiveSeminorm
      ((LinearEquiv.baseChange k L E F e.toLinearEquiv).symm
        (LinearEquiv.baseChange k L E F e.toLinearEquiv z)) ≤ _ at h
    simpa only [LinearEquiv.symm_apply_apply] using h

variable [CompleteSpace k] [FiniteDimensional k E] [FiniteDimensional k F]
  [IsUltrametricDist L]

/-- Non-Archimedean injective scalar extension preserves contractions. -/
theorem scalarExtensionInjectiveSeminorm_baseChange_le (f : E →ₗ[k] F)
    (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm (f.baseChange L z) ≤
      scalarExtensionInjectiveSeminorm z := by
  apply le_scalarExtensionInjectiveSeminorm_of_ultrametric
    ((scalarExtensionInjectiveSeminorm (E := F)).comp (f.baseChange L)) _ _ z
  · intro u v
    change scalarExtensionInjectiveSeminorm (f.baseChange L (u + v)) ≤
      max (scalarExtensionInjectiveSeminorm (f.baseChange L u))
        (scalarExtensionInjectiveSeminorm (f.baseChange L v))
    rw [map_add]
    exact scalarExtensionInjectiveSeminorm_add_le_max IsUltrametricDist.norm_add_le_max _ _
  · intro x
    change scalarExtensionInjectiveSeminorm (f.baseChange L ((1 : L) ⊗ₜ[k] x)) ≤ ‖x‖
    rw [LinearMap.baseChange_tmul]
    exact (scalarExtensionInjectiveSeminorm_one_tmul_le (f x)).trans (hf x)

/-- Injective scalar-extension norms over a non-Archimedean extension field
are unchanged by a linear isometry of the original spaces. -/
theorem scalarExtensionInjectiveSeminorm_baseChange_isometry (e : E ≃ₗᵢ[k] F)
    (z : L ⊗[k] E) :
    scalarExtensionInjectiveSeminorm (LinearEquiv.baseChange k L E F e.toLinearEquiv z) =
      scalarExtensionInjectiveSeminorm z := by
  apply le_antisymm
  · exact scalarExtensionInjectiveSeminorm_baseChange_le e.toLinearMap
      (fun x ↦ (e.norm_map x).le) z
  · have h := scalarExtensionInjectiveSeminorm_baseChange_le e.symm.toLinearMap
      (fun x ↦ (e.symm.norm_map x).le) (LinearEquiv.baseChange k L E F e.toLinearEquiv z)
    change scalarExtensionInjectiveSeminorm
      ((LinearEquiv.baseChange k L E F e.toLinearEquiv).symm
        (LinearEquiv.baseChange k L E F e.toLinearEquiv z)) ≤ _ at h
    simpa only [LinearEquiv.symm_apply_apply] using h

end Isometry


noncomputable section TowerIsometry

variable {k L M E F : Type*} [NormedField k] [NormedField L] [NormedField M]
  [NormedAlgebra k L] [NormedAlgebra k M] [NormedAlgebra L M] [IsScalarTower k L M]
  [CompleteSpace k] [NormedAddCommGroup E] [NormedSpace k E] [FiniteDimensional k E]
  [NormedAddCommGroup F] [NormedSpace L F]

/-- Transitivity expressed through an isometry of the first scalar extension.
The conclusion uses the canonical tensor reassociation. -/
theorem scalarExtensionProjectiveSeminorm_comp_isometry :
    letI := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
    ∀ (e : F ≃ₗᵢ[L] (L ⊗[k] E)) (z : M ⊗[L] F),
    scalarExtensionProjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionProjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
          (LinearEquiv.baseChange L M F (L ⊗[k] E) e.toLinearEquiv z)) := by
  let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
  intro e z
  exact (scalarExtensionProjectiveSeminorm_baseChange_isometry e z).symm.trans
    (scalarExtensionProjectiveSeminorm_comp _)

/-- Transitivity for a space equipped with the projective extension norm through
an explicitly specified linear equivalence. The hypothesis is the norm identity
for the first extension only. -/
theorem scalarExtensionProjectiveSeminorm_comp_equiv
    (e : F ≃ₗ[L] (L ⊗[k] E))
    (he : ∀ y, ‖y‖ = scalarExtensionProjectiveSeminorm (e y)) (z : M ⊗[L] F) :
    scalarExtensionProjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionProjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
          (LinearEquiv.baseChange L M F (L ⊗[k] E) e z)) := by
  let := scalarExtensionProjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionProjectiveNormedSpace (k := k) (L := L) (E := E)
  let e' : F ≃ₗᵢ[L] (L ⊗[k] E) := { e with norm_map' := fun y ↦ (he y).symm }
  exact scalarExtensionProjectiveSeminorm_comp_isometry e' z

variable [CompleteSpace L] [FiniteDimensional L F] [IsUltrametricDist M]

/-- Non-Archimedean transitivity through an isometry of the first scalar
extension, with arbitrary original vector norm. -/
theorem scalarExtensionInjectiveSeminorm_comp_isometry :
    letI := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
    letI := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
    ∀ (e : F ≃ₗᵢ[L] (L ⊗[k] E)) (z : M ⊗[L] F),
    scalarExtensionInjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionInjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
          (LinearEquiv.baseChange L M F (L ⊗[k] E) e.toLinearEquiv z)) := by
  let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
  intro e z
  exact (scalarExtensionInjectiveSeminorm_baseChange_isometry e z).symm.trans
    (scalarExtensionInjectiveSeminorm_comp _)

/-- Non-Archimedean transitivity through an explicit description of the first
injective extension norm. -/
theorem scalarExtensionInjectiveSeminorm_comp_equiv
    (e : F ≃ₗ[L] (L ⊗[k] E))
    (he : ∀ y, ‖y‖ = scalarExtensionInjectiveSeminorm (e y)) (z : M ⊗[L] F) :
    scalarExtensionInjectiveSeminorm (k := L) (L := M) z =
      scalarExtensionInjectiveSeminorm (k := k) (L := M)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange k L M M E
          (LinearEquiv.baseChange L M F (L ⊗[k] E) e z)) := by
  let := scalarExtensionInjectiveNormedAddCommGroup (k := k) (L := L) (E := E)
  let := scalarExtensionInjectiveNormedSpace (k := k) (L := L) (E := E)
  let e' : F ≃ₗᵢ[L] (L ⊗[k] E) := { e with norm_map' := fun y ↦ (he y).symm }
  exact scalarExtensionInjectiveSeminorm_comp_isometry e' z

end TowerIsometry


end ArakelovGeometry
