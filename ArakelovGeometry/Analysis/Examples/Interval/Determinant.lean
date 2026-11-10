/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Examples.Interval.Polytope
public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import ArakelovGeometry.Analysis.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Power

/-!
# Determinant bounds for interval norms

The determinant bound on signed consecutive-interval vertices extends by
multilinearity to their actual convex hulls, and then by homogeneity to all
real columns. The norm and unit-ball identification are the produced endpoint
variation norms, rather than assumptions about a determinant gauge.
-/

@[expose] public section

namespace ArakelovGeometry

open scoped TensorProduct

noncomputable section

/-- A linear real functional preserves an absolute-value bound when passing
from a generating set to its convex hull. -/
theorem abs_linearMap_le_of_mem_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] ℝ) (s : Set E) (B : ℝ)
    (h : ∀ x ∈ s, |f x| ≤ B) {x : E} (hx : x ∈ convexHull ℝ s) :
    |f x| ≤ B := by
  have hs : s ⊆ f ⁻¹' Set.Icc (-B) B := fun y hy => abs_le.mp (h y hy)
  exact abs_le.mpr (convexHull_min hs ((convex_Icc (-B) B).linear_preimage f) hx)

/-- An absolute-value bound on all vertex tuples extends to all tuples in
the corresponding convex hull, by successively using each linear slot. -/
theorem abs_multilinearMap_le_of_mem_convexHull
    {ι E : Type*} [Finite ι]
    [AddCommGroup E] [Module ℝ E]
    (f : MultilinearMap ℝ (fun _ : ι => E) ℝ) (s : Set E) (B : ℝ)
    (h : ∀ v : ι → E, (∀ i, v i ∈ s) → |f v| ≤ B)
    (v : ι → E) (hv : ∀ i, v i ∈ convexHull ℝ s) : |f v| ≤ B := by
  classical
  let _ := Fintype.ofFinite ι
  have hall (J : Finset ι) : ∀ u : ι → E,
      (∀ i ∈ J, u i ∈ convexHull ℝ s) →
      (∀ i, i ∉ J → u i ∈ s) → |f u| ≤ B := by
    induction J using Finset.induction_on with
    | empty =>
      intro u _ hu
      exact h u (fun i => hu i (by simp))
    | @insert i J hi ih =>
      intro u hu hs
      have hslot : ∀ x ∈ s, |f.toLinearMap u i x| ≤ B := by
        intro x hx
        apply ih (Function.update u i x)
        · intro j hj
          have hji : j ≠ i := by rintro rfl; exact hi hj
          simp only [Function.update_of_ne hji]
          exact hu j (Finset.mem_insert_of_mem hj)
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa using hx
          · simp only [Function.update_of_ne hji]
            exact hs j (by simp [hji, hj])
      have hm := abs_linearMap_le_of_mem_convexHull
        (f.toLinearMap u i) s B hslot (hu i (Finset.mem_insert_self i J))
      simpa using hm
  exact hall Finset.univ v (fun i _ => hv i) (fun i hi => (hi (Finset.mem_univ i)).elim)

/-- The determinant of any tuple of signed interval plane vertices is bounded
by one. The finite arithmetic proof is checked by the kernel. -/
theorem abs_det_intervalVertices₂ (v : Matrix (Fin 2) (Fin 2) ℝ)
    (hv : ∀ i, v i ∈ intervalVertices₂) : |Matrix.det v| ≤ 1 := by
  have h0 := hv 0
  have h1 := hv 1
  rw [Matrix.det_fin_two]
  simp only [intervalVertices₂, Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1
  rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 <;>
    rw [h0, h1] <;> norm_num

/-- The six positive consecutive-interval vertices in real three-space. -/
def intervalPositiveVertex₃ (i : Fin 6) : Fin 3 → ℝ :=
  match i.val with
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![1, 1, 0]
  | 4 => ![0, 1, 1]
  | _ => ![1, 1, 1]

/-- Every signed interval vertex is a unit-sign multiple of one of the six
positive vertices. -/
theorem exists_sign_intervalPositiveVertex₃ (x : Fin 3 → ℝ)
    (hx : x ∈ intervalVertices₃) :
    ∃ (a : ℝ) (i : Fin 6), |a| = 1 ∧ x = a • intervalPositiveVertex₃ i := by
  simp only [intervalVertices₃, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · exact ⟨1, 1, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · exact ⟨1, 2, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · exact ⟨1, 3, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · exact ⟨1, 4, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · exact ⟨1, 5, by norm_num, by simp [intervalPositiveVertex₃]⟩
  · refine ⟨-1, 0, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]
  · refine ⟨-1, 1, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]
  · refine ⟨-1, 2, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]
  · refine ⟨-1, 3, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]
  · refine ⟨-1, 4, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]
  · refine ⟨-1, 5, by norm_num, ?_⟩
    ext i
    fin_cases i <;> norm_num [intervalPositiveVertex₃, Matrix.cons_val_two]

/-- All 216 positive interval vertex determinants are bounded by one, by
kernel-checked arithmetic. -/
theorem abs_det_intervalPositiveVertex₃ (i j k : Fin 6) :
    |(Matrix.of ![intervalPositiveVertex₃ i, intervalPositiveVertex₃ j,
      intervalPositiveVertex₃ k]).det| ≤ 1 := by
  rw [Matrix.det_fin_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [intervalPositiveVertex₃, Matrix.of_apply, Matrix.cons_val_two]

/-- Every signed interval three-space vertex tuple has determinant bounded
by one, using multilinearity and the positive-vertex arithmetic table. -/
theorem abs_det_intervalVertices₃ (v : Matrix (Fin 3) (Fin 3) ℝ)
    (hv : ∀ i, v i ∈ intervalVertices₃) : |v.det| ≤ 1 := by
  obtain ⟨a, i, ha, h0⟩ := exists_sign_intervalPositiveVertex₃ (v 0) (hv 0)
  obtain ⟨b, j, hb, h1⟩ := exists_sign_intervalPositiveVertex₃ (v 1) (hv 1)
  obtain ⟨c, k, hc, h2⟩ := exists_sign_intervalPositiveVertex₃ (v 2) (hv 2)
  let f := (Matrix.detRowAlternating (n := Fin 3) (R := ℝ)).toMultilinearMap
  let u := ![intervalPositiveVertex₃ i, intervalPositiveVertex₃ j, intervalPositiveVertex₃ k]
  let s : Fin 3 → ℝ := ![a, b, c]
  have he : v = fun t => s t • u t := by
    funext t
    fin_cases t
    · exact h0
    · exact h1
    · exact h2
  change |f v| ≤ 1
  rw [he, f.map_smul_univ, smul_eq_mul, abs_mul]
  have hs : |∏ t, s t| = 1 := by
    simp [s, Fin.prod_univ_succ, abs_mul, ha, hb, hc]
  rw [hs, one_mul]
  exact abs_det_intervalPositiveVertex₃ i j k

/-- A multilinear bound on all norm-unit tuples scales to arbitrary tuples,
including those with a zero entry. -/
theorem abs_multilinearMap_le_prod_seminorm_of_unit_bound
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (f : MultilinearMap ℝ (fun _ : ι => E) ℝ) (p : Seminorm ℝ E)
    (hp : ∀ x, p x = 0 → x = 0)
    (h : ∀ u : ι → E, (∀ i, p (u i) ≤ 1) → |f u| ≤ 1)
    (v : ι → E) : |f v| ≤ ∏ i, p (v i) := by
  classical
  have hprod : 0 ≤ ∏ i, p (v i) := Finset.prod_nonneg (fun i _ => apply_nonneg p _)
  by_cases hz : ∃ i, p (v i) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [f.map_coord_zero i (hp (v i) hi), abs_zero]
    exact hprod
  have hp0 (i : ι) : p (v i) ≠ 0 := fun hi => hz ⟨i, hi⟩
  have hpp (i : ι) : 0 < p (v i) := lt_of_le_of_ne (apply_nonneg p _) (Ne.symm (hp0 i))
  let w : ι → E := fun i => (p (v i))⁻¹ • v i
  have hw (i : ι) : p (w i) ≤ 1 := by
    dsimp [w]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpp i)),
      inv_mul_cancel₀ (hp0 i)]
  have hvw : v = fun i => p (v i) • w i := by
    funext i
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (hp0 i), one_smul]
  have hf : f v = (∏ i, p (v i)) * f w := by
    conv_lhs => rw [hvw]
    exact f.map_smul_univ (fun i => p (v i)) w
  rw [hf, abs_mul, abs_of_nonneg hprod]
  exact (mul_le_mul_of_nonneg_left (h w hw) hprod).trans_eq (mul_one _)

/-- Arbitrary rows in the actual plane interval unit ball satisfy the
determinant bound, using the produced convex-hull characterization. -/
theorem abs_det_le_one_of_intervalSeminorm₂_le_one
    (v : Matrix (Fin 2) (Fin 2) ℝ) (hv : ∀ i, intervalSeminorm₂ (v i) ≤ 1) :
    |v.det| ≤ 1 := by
  exact abs_multilinearMap_le_of_mem_convexHull
    (Matrix.detRowAlternating (n := Fin 2) (R := ℝ)).toMultilinearMap
    intervalVertices₂ 1 (fun u hu => abs_det_intervalVertices₂ (Matrix.of u) hu)
    v (fun i => (mem_convexHull_intervalVertices₂_iff (v i)).mpr (hv i))

/-- Arbitrary rows in the actual three-space interval unit ball satisfy the
determinant bound, using the produced convex-hull characterization. -/
theorem abs_det_le_one_of_intervalSeminorm₃_le_one
    (v : Matrix (Fin 3) (Fin 3) ℝ) (hv : ∀ i, intervalSeminorm₃ (v i) ≤ 1) :
    |v.det| ≤ 1 := by
  exact abs_multilinearMap_le_of_mem_convexHull
    (Matrix.detRowAlternating (n := Fin 3) (R := ℝ)).toMultilinearMap
    intervalVertices₃ 1 (fun u hu => abs_det_intervalVertices₃ (Matrix.of u) hu)
    v (fun i => (mem_convexHull_intervalVertices₃_iff (v i)).mpr (hv i))

/-- The determinant of every real plane matrix is bounded by the product of
the actual interval norms of all its columns, including zero columns. -/
theorem abs_det_le_prod_intervalSeminorm₂ (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |A.det| ≤ ∏ j, intervalSeminorm₂ (fun i => A i j) := by
  have h := abs_multilinearMap_le_prod_seminorm_of_unit_bound
    (Matrix.detRowAlternating (n := Fin 2) (R := ℝ)).toMultilinearMap
    intervalSeminorm₂ (fun x hx => (intervalSeminorm₂_eq_zero_iff x).mp hx)
    (fun u hu => abs_det_le_one_of_intervalSeminorm₂_le_one (Matrix.of u) hu) A.transpose
  change |A.transpose.det| ≤ ∏ j, intervalSeminorm₂ (fun i => A i j) at h
  rwa [Matrix.det_transpose] at h

/-- The determinant of every real three-space matrix is bounded by the product
of the actual interval norms of all its columns, including zero columns. -/
theorem abs_det_le_prod_intervalSeminorm₃ (A : Matrix (Fin 3) (Fin 3) ℝ) :
    |A.det| ≤ ∏ j, intervalSeminorm₃ (fun i => A i j) := by
  have h := abs_multilinearMap_le_prod_seminorm_of_unit_bound
    (Matrix.detRowAlternating (n := Fin 3) (R := ℝ)).toMultilinearMap
    intervalSeminorm₃ (fun x hx => (intervalSeminorm₃_eq_zero_iff x).mp hx)
    (fun u hu => abs_det_le_one_of_intervalSeminorm₃_le_one (Matrix.of u) hu) A.transpose
  change |A.transpose.det| ≤ ∏ j, intervalSeminorm₃ (fun i => A i j) at h
  rwa [Matrix.det_transpose] at h

/-- The actual projective exterior quotient has exact determinant coordinate
length when a unit basis attains the all-tuple determinant bound. -/
theorem projective_exterior_length_smul_basis_eq_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hn : 0 < n) (b : Module.Basis (Fin n) ℝ E)
    (hbound : ∀ v : Fin n → E, |b.det v| ≤ ∏ i, ‖v i‖)
    (hunit : ∀ i, ‖b i‖ = 1) (a : ℝ) :
    sInf {c : ℝ | ∃ z : ⨂[ℝ] (_ : Fin n), E,
      PiTensorProduct.lift (exteriorPower.ιMulti ℝ n).toMultilinearMap z =
          a • exteriorPower.ιMulti ℝ n b ∧ PiTensorProduct.projectiveSeminorm z = c} =
      |a| := by
  classical
  rw [determinant_projective_quotient_eq_sInf_ιMulti hn b]
  let i : Fin n := ⟨0, hn⟩
  let x : Fin n → E := Function.update b i (a • b i)
  have hx : exteriorPower.ιMulti ℝ n x = a • exteriorPower.ιMulti ℝ n b := by
    dsimp [x]
    rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  have hxn : ∏ j, ‖x j‖ = |a| := by
    have he : (fun j => ‖x j‖) = Function.update (fun _ => (1 : ℝ)) i |a| := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [x, norm_smul, hunit, Real.norm_eq_abs]
      · simp [x, hji, hunit]
    rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hne : {c : ℝ | ∃ v : Fin n → E,
      exteriorPower.ιMulti ℝ n v = a • exteriorPower.ιMulti ℝ n b ∧
        (∏ j, ‖v j‖) = c}.Nonempty := ⟨|a|, x, hx, hxn⟩
  have hbelow : BddBelow {c : ℝ | ∃ v : Fin n → E,
      exteriorPower.ιMulti ℝ n v = a • exteriorPower.ιMulti ℝ n b ∧
        (∏ j, ‖v j‖) = c} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact Finset.prod_nonneg (fun j _ => norm_nonneg _)
  apply le_antisymm (csInf_le hbelow ⟨x, hx, hxn⟩)
  apply le_csInf hne
  rintro _ ⟨v, hv, rfl⟩
  let g := exteriorPower.alternatingMapLinearEquiv b.det
  have hd : b.det v = a := by
    have he := congrArg g hv
    simpa only [g, map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      b.det_self, smul_eq_mul, mul_one] using he
  simpa only [hd] using hbound v

/-- The genuine projective tensor quotient length on the actual plane
determinant line, for the endpoint-variation norm. -/
def intervalProjectiveExteriorLength₂ (η : ⋀[ℝ]^2 (Fin 2 → ℝ)) : ℝ :=
  let _ := intervalNorm₂.toNormedAddCommGroup
  let _ : SeminormedAddCommGroup (Fin 2 → ℝ) :=
    intervalNorm₂.toNormedAddCommGroup.toSeminormedAddCommGroup
  let _ : NormedSpace ℝ (Fin 2 → ℝ) :=
    ⟨fun a x => by
      change intervalSeminorm₂ (a • x) ≤ ‖a‖ * intervalSeminorm₂ x
      exact (map_smul_eq_mul intervalSeminorm₂ a x).le⟩
  sInf {c : ℝ | ∃ z : ⨂[ℝ] (_ : Fin 2), (Fin 2 → ℝ),
    PiTensorProduct.lift (exteriorPower.ιMulti ℝ 2).toMultilinearMap z = η ∧
      PiTensorProduct.projectiveSeminorm z = c}

/-- The genuine projective tensor quotient length on the actual three-space
determinant line, for the endpoint-variation norm. -/
def intervalProjectiveExteriorLength₃ (η : ⋀[ℝ]^3 (Fin 3 → ℝ)) : ℝ :=
  let _ := intervalNorm₃.toNormedAddCommGroup
  let _ : SeminormedAddCommGroup (Fin 3 → ℝ) :=
    intervalNorm₃.toNormedAddCommGroup.toSeminormedAddCommGroup
  let _ : NormedSpace ℝ (Fin 3 → ℝ) :=
    ⟨fun a x => by
      change intervalSeminorm₃ (a • x) ≤ ‖a‖ * intervalSeminorm₃ x
      exact (map_smul_eq_mul intervalSeminorm₃ a x).le⟩
  sInf {c : ℝ | ∃ z : ⨂[ℝ] (_ : Fin 3), (Fin 3 → ℝ),
    PiTensorProduct.lift (exteriorPower.ιMulti ℝ 3).toMultilinearMap z = η ∧
      PiTensorProduct.projectiveSeminorm z = c}

/-- The actual plane determinant quotient gives length `|a|` to every scalar
multiple of the standard determinant vector. -/
theorem intervalProjectiveExteriorLength₂_smul_basis (a : ℝ) :
    intervalProjectiveExteriorLength₂
      (a • exteriorPower.ιMulti ℝ 2 (Pi.basisFun ℝ (Fin 2))) = |a| := by
  let _ := intervalNorm₂.toNormedAddCommGroup
  let _ : SeminormedAddCommGroup (Fin 2 → ℝ) :=
    intervalNorm₂.toNormedAddCommGroup.toSeminormedAddCommGroup
  let _ : NormedSpace ℝ (Fin 2 → ℝ) :=
    ⟨fun a x => by
      change intervalSeminorm₂ (a • x) ≤ ‖a‖ * intervalSeminorm₂ x
      exact (map_smul_eq_mul intervalSeminorm₂ a x).le⟩
  unfold intervalProjectiveExteriorLength₂
  apply projective_exterior_length_smul_basis_eq_abs (by decide) (Pi.basisFun ℝ (Fin 2))
  · intro v
    rw [Pi.basisFun_det_apply]
    have h := abs_det_le_prod_intervalSeminorm₂ (Matrix.of v).transpose
    change |(Matrix.of v).transpose.det| ≤ ∏ j, intervalSeminorm₂ (v j) at h
    rw [Matrix.det_transpose] at h
    exact h
  · intro i
    change intervalSeminorm₂ ((Pi.basisFun ℝ (Fin 2)) i) = 1
    fin_cases i <;>
      norm_num [Pi.basisFun_apply, intervalSeminorm₂_apply, Pi.single_apply, Fin.ext_iff]

/-- The actual three-space determinant quotient gives length `|a|` to every
scalar multiple of the standard determinant vector. -/
theorem intervalProjectiveExteriorLength₃_smul_basis (a : ℝ) :
    intervalProjectiveExteriorLength₃
      (a • exteriorPower.ιMulti ℝ 3 (Pi.basisFun ℝ (Fin 3))) = |a| := by
  let _ := intervalNorm₃.toNormedAddCommGroup
  let _ : SeminormedAddCommGroup (Fin 3 → ℝ) :=
    intervalNorm₃.toNormedAddCommGroup.toSeminormedAddCommGroup
  let _ : NormedSpace ℝ (Fin 3 → ℝ) :=
    ⟨fun a x => by
      change intervalSeminorm₃ (a • x) ≤ ‖a‖ * intervalSeminorm₃ x
      exact (map_smul_eq_mul intervalSeminorm₃ a x).le⟩
  unfold intervalProjectiveExteriorLength₃
  apply projective_exterior_length_smul_basis_eq_abs (by decide) (Pi.basisFun ℝ (Fin 3))
  · intro v
    rw [Pi.basisFun_det_apply]
    have h := abs_det_le_prod_intervalSeminorm₃ (Matrix.of v).transpose
    change |(Matrix.of v).transpose.det| ≤ ∏ j, intervalSeminorm₃ (v j) at h
    rw [Matrix.det_transpose] at h
    exact h
  · intro i
    change intervalSeminorm₃ ((Pi.basisFun ℝ (Fin 3)) i) = 1
    fin_cases i <;>
      norm_num [Pi.basisFun_apply, intervalSeminorm₃_apply, Pi.single_apply, Fin.ext_iff]

end

end ArakelovGeometry
