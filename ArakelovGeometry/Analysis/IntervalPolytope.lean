/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Real consecutive-interval norms

The endpoint-extended half variation defines the actual norms used in the
projective tensor determinant counterexample. Its identification with the
signed-interval convex hull is proved before any determinant application.
-/

@[expose] public section

namespace ArakelovGeometry

noncomputable section

/-- Endpoint-extended half variation on the real coordinate plane. -/
def intervalSeminorm₂ : Seminorm ℝ (Fin 2 → ℝ) :=
  Seminorm.of (fun x => (|x 0| + |x 1 - x 0| + |x 1|) / 2)
    (by
      intro x y
      have h0 := abs_add_le (x 0) (y 0)
      have h1 := abs_add_le (x 1 - x 0) (y 1 - y 0)
      have h2 := abs_add_le (x 1) (y 1)
      have he : (x + y) 1 - (x + y) 0 = (x 1 - x 0) + (y 1 - y 0) := by
        simp only [Pi.add_apply]
        ring
      simp only [Pi.add_apply] at he ⊢
      rw [he]
      linarith)
    (by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, Real.norm_eq_abs]
      ring)

/-- Endpoint-extended half variation on the real coordinate three-space. -/
def intervalSeminorm₃ : Seminorm ℝ (Fin 3 → ℝ) :=
  Seminorm.of (fun x => (|x 0| + |x 1 - x 0| + |x 2 - x 1| + |x 2|) / 2)
    (by
      intro x y
      have h0 := abs_add_le (x 0) (y 0)
      have h1 := abs_add_le (x 1 - x 0) (y 1 - y 0)
      have h2 := abs_add_le (x 2 - x 1) (y 2 - y 1)
      have h3 := abs_add_le (x 2) (y 2)
      have he1 : (x + y) 1 - (x + y) 0 = (x 1 - x 0) + (y 1 - y 0) := by
        simp only [Pi.add_apply]
        ring
      have he2 : (x + y) 2 - (x + y) 1 = (x 2 - x 1) + (y 2 - y 1) := by
        simp only [Pi.add_apply]
        ring
      simp only [Pi.add_apply] at he1 he2 ⊢
      rw [he1, he2]
      linarith)
    (by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, Real.norm_eq_abs]
      ring)

@[simp]
theorem intervalSeminorm₂_apply (x : Fin 2 → ℝ) :
    intervalSeminorm₂ x = (|x 0| + |x 1 - x 0| + |x 1|) / 2 := rfl

@[simp]
theorem intervalSeminorm₃_apply (x : Fin 3 → ℝ) :
    intervalSeminorm₃ x = (|x 0| + |x 1 - x 0| + |x 2 - x 1| + |x 2|) / 2 := rfl

/-- Every plane coordinate is bounded by endpoint half variation. -/
theorem abs_coordinate_le_intervalSeminorm₂ (x : Fin 2 → ℝ) (i : Fin 2) :
    |x i| ≤ intervalSeminorm₂ x := by
  have h0 : |x 0| ≤ |x 1 - x 0| + |x 1| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (x 0 - x 1) (x 1)
  have h1 : |x 1| ≤ |x 1 - x 0| + |x 0| := by
    simpa only [sub_add_cancel] using abs_add_le (x 1 - x 0) (x 0)
  have h0' : |x 0| ≤ intervalSeminorm₂ x := by rw [intervalSeminorm₂_apply]; linarith
  have h1' : |x 1| ≤ intervalSeminorm₂ x := by rw [intervalSeminorm₂_apply]; linarith
  fin_cases i
  · exact h0'
  · exact h1'

/-- The endpoint norm is bounded above by the coordinate sum. -/
theorem intervalSeminorm₂_le_sum (x : Fin 2 → ℝ) :
    intervalSeminorm₂ x ≤ |x 0| + |x 1| := by
  rw [intervalSeminorm₂_apply]
  have h : |x 1 - x 0| ≤ |x 1| + |x 0| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (x 1) 0 (x 0)
  linarith

/-- Every three-space coordinate is bounded by endpoint half variation. -/
theorem abs_coordinate_le_intervalSeminorm₃ (x : Fin 3 → ℝ) (i : Fin 3) :
    |x i| ≤ intervalSeminorm₃ x := by
  have h0 : |x 0| ≤ |x 1 - x 0| + |x 2 - x 1| + |x 2| := by
    calc
      |x 0| = |(x 0 - x 1) + (x 1 - x 2) + x 2| := by congr 1; ring
      _ ≤ |(x 0 - x 1) + (x 1 - x 2)| + |x 2| := abs_add_le _ _
      _ ≤ _ := by
        have h := abs_add_le (x 0 - x 1) (x 1 - x 2)
        rw [abs_sub_comm (x 0) (x 1), abs_sub_comm (x 1) (x 2)] at h
        linarith
  have h1a : |x 1| ≤ |x 0| + |x 1 - x 0| := by
    have h := abs_add_le (x 0) (x 1 - x 0)
    have he : x 0 + (x 1 - x 0) = x 1 := by ring
    rwa [he] at h
  have h1b : |x 1| ≤ |x 2 - x 1| + |x 2| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le (x 1 - x 2) (x 2)
  have h2 : |x 2| ≤ |x 0| + |x 1 - x 0| + |x 2 - x 1| := by
    calc
      |x 2| = |x 0 + (x 1 - x 0) + (x 2 - x 1)| := by congr 1; ring
      _ ≤ |x 0 + (x 1 - x 0)| + |x 2 - x 1| := abs_add_le _ _
      _ ≤ _ := by
        have h := abs_add_le (x 0) (x 1 - x 0)
        linarith
  have h0' : |x 0| ≤ intervalSeminorm₃ x := by rw [intervalSeminorm₃_apply]; linarith
  have h1' : |x 1| ≤ intervalSeminorm₃ x := by rw [intervalSeminorm₃_apply]; linarith
  have h2' : |x 2| ≤ intervalSeminorm₃ x := by rw [intervalSeminorm₃_apply]; linarith
  fin_cases i
  · exact h0'
  · exact h1'
  · exact h2'

/-- The three-space norm is bounded above by the coordinate sum. -/
theorem intervalSeminorm₃_le_sum (x : Fin 3 → ℝ) :
    intervalSeminorm₃ x ≤ |x 0| + |x 1| + |x 2| := by
  rw [intervalSeminorm₃_apply]
  have h01 : |x 1 - x 0| ≤ |x 1| + |x 0| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (x 1) 0 (x 0)
  have h12 : |x 2 - x 1| ≤ |x 2| + |x 1| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (x 2) 0 (x 1)
  linarith

/-- The plane endpoint seminorm separates zero. -/
theorem intervalSeminorm₂_eq_zero_iff (x : Fin 2 → ℝ) :
    intervalSeminorm₂ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have h := abs_coordinate_le_intervalSeminorm₂ x i
    rw [hx] at h
    exact abs_nonpos_iff.mp h
  · rintro rfl
    exact map_zero _

/-- The three-space endpoint seminorm separates zero. -/
theorem intervalSeminorm₃_eq_zero_iff (x : Fin 3 → ℝ) :
    intervalSeminorm₃ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    ext i
    have h := abs_coordinate_le_intervalSeminorm₃ x i
    rw [hx] at h
    exact abs_nonpos_iff.mp h
  · rintro rfl
    exact map_zero _

/-- The actual plane norm structure defined by endpoint variation. -/
def intervalNorm₂ : AddGroupNorm (Fin 2 → ℝ) :=
  ⟨intervalSeminorm₂.toAddGroupSeminorm, fun x hx => (intervalSeminorm₂_eq_zero_iff x).mp hx⟩

/-- The actual three-space norm structure defined by endpoint variation. -/
def intervalNorm₃ : AddGroupNorm (Fin 3 → ℝ) :=
  ⟨intervalSeminorm₃.toAddGroupSeminorm, fun x hx => (intervalSeminorm₃_eq_zero_iff x).mp hx⟩

/-- Roots in the zero-sum coordinate hyperplane, including the zero root. -/
def coordinateRoot {ι : Type*} [DecidableEq ι] (i j : ι) : ι → ℝ :=
  Pi.single i 1 - Pi.single j 1

/-- Half the coordinate sum is the intrinsic convex root-polytope bound.
No restriction on the signs or support of the coordinates is imposed. -/
theorem mem_convexHull_coordinateRoot_of_sum_abs_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∑ i, d i = 0) (hab : ∑ i, |d i| ≤ 2) :
    d ∈ convexHull ℝ (Set.range (fun ij : ι × ι => coordinateRoot ij.1 ij.2)) := by
  classical
  let a : ι → ℝ := fun i => max (d i) 0
  let b : ι → ℝ := fun i => max (-d i) 0
  let t := ∑ i, a i
  have ha (i : ι) : 0 ≤ a i := le_max_right _ _
  have hb (i : ι) : 0 ≤ b i := le_max_right _ _
  have hdab (i : ι) : d i = a i - b i := by
    dsimp [a, b]
    by_cases h : 0 ≤ d i
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have habs (i : ι) : |d i| = a i + b i := by
    dsimp [a, b]
    by_cases h : 0 ≤ d i
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith), add_zero]
    · rw [abs_of_neg (lt_of_not_ge h), max_eq_right (by linarith),
        max_eq_left (by linarith), zero_add]
  have hbt : ∑ i, b i = t := by
    have he : ∑ i, d i = (∑ i, a i) - ∑ i, b i := by
      simp only [hdab, Finset.sum_sub_distrib]
    rw [hd] at he
    dsimp [t]
    linarith
  have habst : ∑ i, |d i| = 2 * t := by
    simp only [habs, Finset.sum_add_distrib, hbt]
    dsimp [t]
    ring
  have ht : 0 ≤ t := Finset.sum_nonneg fun i _ => ha i
  have ht1 : t ≤ 1 := by rw [habst] at hab; linarith
  let C := convexHull ℝ (Set.range (fun ij : ι × ι => coordinateRoot ij.1 ij.2))
  have hC : Convex ℝ C := convex_convexHull _ _
  have h0 : (0 : ι → ℝ) ∈ C := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    apply subset_convexHull ℝ _
    exact ⟨(i, i), by simp [coordinateRoot]⟩
  by_cases ht0 : t = 0
  · have hd0 : d = 0 := by
      ext i
      have hi : |d i| ≤ ∑ j, |d j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (d j)) (Finset.mem_univ i)
      rw [habst, ht0, mul_zero] at hi
      exact abs_nonpos_iff.mp hi
    rwa [hd0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let c : ι × ι → ℝ := fun ij => a ij.1 * b ij.2 / t
  have hc (ij : ι × ι) : 0 ≤ c ij := div_nonneg (mul_nonneg (ha _) (hb _)) ht
  have hcsum : ∑ ij, c ij = t := by
    dsimp [c]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hbt]
    change t * t / t = t
    exact mul_div_cancel_right₀ t ht0
  have hcreconstruct : ∑ ij, c ij • coordinateRoot ij.1 ij.2 = d := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, coordinateRoot, Pi.sub_apply,
      Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    dsimp [c]
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    have hleft : (∑ i, ∑ j, a i * b j * (if k = i then 1 else 0)) = a k * t := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
        Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, ← Finset.mul_sum, hbt]
    have hright : (∑ i, ∑ j, a i * b j * (if k = j then 1 else 0)) = t * b k := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, ← Finset.sum_mul]
      rfl
    rw [hleft, hright]
    rw [mul_div_cancel_right₀ _ ht0, mul_div_cancel_left₀ _ ht0]
    exact (hdab k).symm
  let w : Option (ι × ι) → ℝ := fun ij =>
    match ij with
    | none => 1 - t
    | some ij => c ij
  let z : Option (ι × ι) → (ι → ℝ) := fun ij =>
    match ij with
    | none => 0
    | some ij => coordinateRoot ij.1 ij.2
  have hw (ij : Option (ι × ι)) : 0 ≤ w ij := by
    cases ij with
    | none => exact sub_nonneg.mpr ht1
    | some ij => exact hc ij
  have hwsum : ∑ ij, w ij = 1 := by
    rw [Fintype.sum_option]
    change (1 - t) + ∑ ij, c ij = 1
    rw [hcsum]
    ring
  have hz (ij : Option (ι × ι)) : z ij ∈ C := by
    cases ij with
    | none => exact h0
    | some ij => exact subset_convexHull ℝ _ ⟨ij, rfl⟩
  have hm := hC.sum_mem (t := Finset.univ) (fun ij _ => hw ij) hwsum (fun ij _ => hz ij)
  have he : ∑ ij, w ij • z ij = d := by
    rw [Fintype.sum_option]
    change (1 - t) • (0 : ι → ℝ) + ∑ ij, c ij • coordinateRoot ij.1 ij.2 = d
    simp only [smul_zero, zero_add]
    exact hcreconstruct
  rwa [he] at hm

/-- Exactly the signed consecutive intervals in the real coordinate plane. -/
def intervalVertices₂ : Set (Fin 2 → ℝ) :=
  {![1, 0], ![0, 1], ![1, 1], ![-1, 0], ![0, -1], ![-1, -1]}

/-- Exactly the signed consecutive intervals in real coordinate three-space. -/
def intervalVertices₃ : Set (Fin 3 → ℝ) :=
  {![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1],
    ![-1, 0, 0], ![0, -1, 0], ![0, 0, -1], ![-1, -1, 0], ![0, -1, -1], ![-1, -1, -1]}

/-- The actual prefix map from endpoint differences to the plane. -/
def intervalPrefix₂ : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun d := ![d 0, d 0 + d 1]
  map_add' d e := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' a d := by
    ext i
    fin_cases i <;> simp
    all_goals ring

/-- The actual prefix map from endpoint differences to three-space. -/
def intervalPrefix₃ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun d := ![d 0, d 0 + d 1, d 0 + d 1 + d 2]
  map_add' d e := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' a d := by
    ext i
    fin_cases i <;> simp
    all_goals ring

/-- Every signed interval in the plane has norm exactly one. -/
theorem intervalSeminorm₂_vertex (x : Fin 2 → ℝ) (hx : x ∈ intervalVertices₂) :
    intervalSeminorm₂ x = 1 := by
  simp only [intervalVertices₂, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [intervalSeminorm₂_apply]

/-- Every signed interval in three-space has norm exactly one. -/
theorem intervalSeminorm₃_vertex (x : Fin 3 → ℝ) (hx : x ∈ intervalVertices₃) :
    intervalSeminorm₃ x = 1 := by
  simp only [intervalVertices₃, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [intervalSeminorm₃_apply, Matrix.cons_val_two]

private theorem intervalZero₂ :
    (0 : Fin 2 → ℝ) ∈ convexHull ℝ intervalVertices₂ := by
  have h0 : (![1, 0] : Fin 2 → ℝ) ∈ convexHull ℝ intervalVertices₂ :=
    subset_convexHull _ _ (by simp [intervalVertices₂])
  have h1 : (![-1, 0] : Fin 2 → ℝ) ∈ convexHull ℝ intervalVertices₂ :=
    subset_convexHull _ _ (by simp [intervalVertices₂])
  have h := convex_convexHull ℝ intervalVertices₂ h0 h1
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  convert h using 1
  ext i
  fin_cases i <;> norm_num

private theorem intervalZero₃ :
    (0 : Fin 3 → ℝ) ∈ convexHull ℝ intervalVertices₃ := by
  have h0 : (![1, 0, 0] : Fin 3 → ℝ) ∈ convexHull ℝ intervalVertices₃ :=
    subset_convexHull _ _ (by simp [intervalVertices₃])
  have h1 : (![-1, 0, 0] : Fin 3 → ℝ) ∈ convexHull ℝ intervalVertices₃ :=
    subset_convexHull _ _ (by simp [intervalVertices₃])
  have h := convex_convexHull ℝ intervalVertices₃ h0 h1
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  convert h using 1
  ext i
  fin_cases i <;> norm_num

private theorem intervalPrefix₂_root (ij : Fin 3 × Fin 3) :
    intervalPrefix₂ (coordinateRoot ij.1 ij.2) ∈ convexHull ℝ intervalVertices₂ := by
  obtain ⟨i, j⟩ := ij
  have h : intervalPrefix₂ (coordinateRoot i j) = 0 ∨
      intervalPrefix₂ (coordinateRoot i j) ∈ intervalVertices₂ := by
    fin_cases i <;> fin_cases j <;>
      norm_num [intervalPrefix₂, coordinateRoot, Pi.single_apply, intervalVertices₂,
        funext_iff, Fin.forall_fin_succ, Fin.ext_iff]
  rcases h with h | h
  · rw [h]
    exact intervalZero₂
  · exact subset_convexHull _ _ h

private theorem intervalPrefix₃_root (ij : Fin 4 × Fin 4) :
    intervalPrefix₃ (coordinateRoot ij.1 ij.2) ∈ convexHull ℝ intervalVertices₃ := by
  obtain ⟨i, j⟩ := ij
  have h : intervalPrefix₃ (coordinateRoot i j) = 0 ∨
      intervalPrefix₃ (coordinateRoot i j) ∈ intervalVertices₃ := by
    fin_cases i <;> fin_cases j <;>
      norm_num [intervalPrefix₃, coordinateRoot, Pi.single_apply, intervalVertices₃,
        funext_iff, Fin.forall_fin_succ, Fin.ext_iff]
  rcases h with h | h
  · rw [h]
    exact intervalZero₃
  · exact subset_convexHull _ _ h

/-- The half-variation plane norm is precisely the norm of the actual
signed-interval convex hull. -/
theorem mem_convexHull_intervalVertices₂_iff (x : Fin 2 → ℝ) :
    x ∈ convexHull ℝ intervalVertices₂ ↔ intervalSeminorm₂ x ≤ 1 := by
  constructor
  · intro hx
    have h := convexHull_min
      (show intervalVertices₂ ⊆ intervalSeminorm₂.closedBall 0 1 from fun y hy =>
        (Seminorm.mem_closedBall_zero _).mpr (by rw [intervalSeminorm₂_vertex y hy]))
      (intervalSeminorm₂.convex_closedBall 0 1) hx
    exact (Seminorm.mem_closedBall_zero _).mp h
  · intro hx
    let d : Fin 3 → ℝ := ![x 0, x 1 - x 0, -x 1]
    have hd : ∑ i, d i = 0 := by simp [d, Fin.sum_univ_succ]; ring
    have hab : ∑ i, |d i| ≤ 2 := by
      simp [d, Fin.sum_univ_succ]
      rw [intervalSeminorm₂_apply] at hx
      linarith
    have hr := mem_convexHull_coordinateRoot_of_sum_abs_le_two d hd hab
    have hp : intervalPrefix₂ d ∈ convexHull ℝ
        (intervalPrefix₂ '' Set.range (fun ij : Fin 3 × Fin 3 =>
          coordinateRoot ij.1 ij.2)) := by
      rw [← intervalPrefix₂.image_convexHull]
      exact ⟨d, hr, rfl⟩
    have hsub : intervalPrefix₂ '' Set.range (fun ij : Fin 3 × Fin 3 =>
        coordinateRoot ij.1 ij.2) ⊆ convexHull ℝ intervalVertices₂ := by
      rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
      exact intervalPrefix₂_root ij
    have hm := convexHull_min hsub (convex_convexHull ℝ intervalVertices₂) hp
    have he : intervalPrefix₂ d = x := by
      ext i
      fin_cases i <;> simp [intervalPrefix₂, d]
    rwa [he] at hm

/-- The half-variation three-space norm is precisely the norm of the actual
signed-interval convex hull. -/
theorem mem_convexHull_intervalVertices₃_iff (x : Fin 3 → ℝ) :
    x ∈ convexHull ℝ intervalVertices₃ ↔ intervalSeminorm₃ x ≤ 1 := by
  constructor
  · intro hx
    have h := convexHull_min
      (show intervalVertices₃ ⊆ intervalSeminorm₃.closedBall 0 1 from fun y hy =>
        (Seminorm.mem_closedBall_zero _).mpr (by rw [intervalSeminorm₃_vertex y hy]))
      (intervalSeminorm₃.convex_closedBall 0 1) hx
    exact (Seminorm.mem_closedBall_zero _).mp h
  · intro hx
    let d : Fin 4 → ℝ := ![x 0, x 1 - x 0, x 2 - x 1, -x 2]
    have hd : ∑ i, d i = 0 := by simp [d, Fin.sum_univ_succ]; ring
    have hab : ∑ i, |d i| ≤ 2 := by
      simp [d, Fin.sum_univ_succ]
      rw [intervalSeminorm₃_apply] at hx
      linarith
    have hr := mem_convexHull_coordinateRoot_of_sum_abs_le_two d hd hab
    have hp : intervalPrefix₃ d ∈ convexHull ℝ
        (intervalPrefix₃ '' Set.range (fun ij : Fin 4 × Fin 4 =>
          coordinateRoot ij.1 ij.2)) := by
      rw [← intervalPrefix₃.image_convexHull]
      exact ⟨d, hr, rfl⟩
    have hsub : intervalPrefix₃ '' Set.range (fun ij : Fin 4 × Fin 4 =>
        coordinateRoot ij.1 ij.2) ⊆ convexHull ℝ intervalVertices₃ := by
      rintro _ ⟨_, ⟨ij, rfl⟩, rfl⟩
      exact intervalPrefix₃_root ij
    have hm := convexHull_min hsub (convex_convexHull ℝ intervalVertices₃) hp
    have he : intervalPrefix₃ d = x := by
      ext i
      fin_cases i <;> simp [intervalPrefix₃, d]
    rwa [he] at hm

end

end ArakelovGeometry
