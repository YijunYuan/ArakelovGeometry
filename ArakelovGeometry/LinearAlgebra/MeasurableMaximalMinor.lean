/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import ArakelovGeometry.LinearAlgebra.MaximalMinor
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable selection of actual maximal minors

For a fixed full-column-rank matrix and a measurably varying absolute value,
an actual maximal minor can be selected on a finite measurable partition. The
normalization coefficients are fixed field elements on every part. The
parameter space itself need not be discrete or countable.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace ArakelovGeometry.Matrix

variable {K m n X : Type*} [Field K] [Fintype m] [Fintype n] [DecidableEq n]
  [MeasurableSpace X]

omit [Fintype m] in
/-- Actual fixed field coefficients produce a finite measurable maximal-minor partition. -/
theorem exists_measurable_maximal_minor [Finite m] (A : Matrix m n K)
    (hA : LinearIndependent K A.col) (v : X → AbsoluteValue K ℝ)
    (hv : ∀ a : K, Measurable (fun x ↦ v x a)) :
    ∃ I : X → n → m,
      (∀ J : n → m, MeasurableSet {x | I x = J}) ∧
      ∀ x, Function.Injective (I x) ∧ (A.submatrix (I x) id).det ≠ 0 ∧
        (∀ J : n → m, v x (A.submatrix J id).det ≤ v x (A.submatrix (I x) id).det) ∧
        (A * (A.submatrix (I x) id)⁻¹).submatrix (I x) id = 1 ∧
        ∀ i j, v x ((A * (A.submatrix (I x) id)⁻¹) i j) ≤ 1 := by
  classical
  let := Fintype.ofFinite m
  obtain ⟨I₀, _⟩ := exists_row_minor_det_ne_zero A hA
  let P (J : n → m) (x : X) : Prop :=
    Function.Injective J ∧ (A.submatrix J id).det ≠ 0 ∧
      (∀ J' : n → m, v x (A.submatrix J' id).det ≤ v x (A.submatrix J id).det) ∧
      (A * (A.submatrix J id)⁻¹).submatrix J id = 1 ∧
      ∀ i j, v x ((A * (A.submatrix J id)⁻¹) i j) ≤ 1
  have hP : ∀ J, MeasurableSet {x | P J x} := by
    intro J
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    refine MeasurableSet.inter ?_ ?_
    · change MeasurableSet {x | ∀ J' : n → m,
        v x (A.submatrix J' id).det ≤ v x (A.submatrix J id).det}
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun J' : n → m ↦
          measurableSet_le (hv (A.submatrix J' id).det) (hv (A.submatrix J id).det)
    · refine MeasurableSet.inter (MeasurableSet.const _) ?_
      change MeasurableSet {x | ∀ i : m, ∀ j : n,
        v x ((A * (A.submatrix J id)⁻¹) i j) ≤ 1}
      simp_rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i : m ↦ MeasurableSet.iInter fun j : n ↦
          measurableSet_le (hv ((A * (A.submatrix J id)⁻¹) i j))
            (measurable_const (a := (1 : ℝ)))
  let e := Fintype.equivFin (n → m)
  let enum (r : ℕ) : n → m := if h : r < Fintype.card (n → m) then e.symm ⟨r, h⟩ else I₀
  have hex : ∀ x, ∃ r : ℕ, P (enum r) x := by
    intro x
    obtain ⟨J, hJ⟩ := exists_maximal_row_minor_normalization A hA (v x)
    refine ⟨(e J).val, ?_⟩
    simpa only [enum, dite_eq_left (e J).isLt, e.symm_apply_apply] using hJ
  let I (x : X) : n → m := enum (Nat.find (hex x))
  have hI : ∀ x, P (I x) x := fun x ↦ Nat.find_spec (hex x)
  let : MeasurableSpace (n → m) := ⊤
  have hmeas : Measurable I := Measurable.find (fun _ ↦ measurable_const)
    (fun r ↦ hP (enum r)) hex
  refine ⟨I, ?_, hI⟩
  intro J
  exact hmeas (MeasurableSet.singleton J)

private theorem measurable_selected_absoluteValue {Y : Type*} [Finite Y]
    (v : X → AbsoluteValue K ℝ) (hv : ∀ a : K, Measurable (fun x ↦ v x a))
    (I : X → Y) (hI : ∀ y, MeasurableSet {x | I x = y}) (c : Y → K) :
    Measurable (fun x ↦ v x (c (I x))) := by
  classical
  let := Fintype.ofFinite Y
  let : MeasurableSpace Y := ⊤
  have hIm : Measurable I := measurable_to_countable' hI
  have hm : Measurable (fun p : X × Y ↦ v p.1 (c p.2)) :=
    measurable_from_prod_countable_left (fun y ↦ hv (c y))
  exact hm.comp (measurable_id.prodMk hIm)

omit [Fintype m] in
/-- The selected normalization has measurable absolute-value evaluations, including
the actual residual of every fixed vector modulo the original column space. -/
theorem exists_measurable_maximal_minor_evaluations [Finite m] (A : Matrix m n K)
    (hA : LinearIndependent K A.col) (v : X → AbsoluteValue K ℝ)
    (hv : ∀ a : K, Measurable (fun x ↦ v x a)) :
    ∃ I : X → n → m,
      (∀ J, MeasurableSet {x | I x = J}) ∧
      (∀ x, Function.Injective (I x) ∧ (A.submatrix (I x) id).det ≠ 0 ∧
        (∀ J, v x (A.submatrix J id).det ≤ v x (A.submatrix (I x) id).det) ∧
        (A * (A.submatrix (I x) id)⁻¹).submatrix (I x) id = 1 ∧
        ∀ i j, v x ((A * (A.submatrix (I x) id)⁻¹) i j) ≤ 1) ∧
      Measurable (fun x ↦ v x (A.submatrix (I x) id).det) ∧
      (∀ i j, Measurable (fun x ↦ v x ((A * (A.submatrix (I x) id)⁻¹) i j))) ∧
      (∀ (z : m → K) i, Measurable (fun x ↦
        v x ((z - (A * (A.submatrix (I x) id)⁻¹) *ᵥ (z ∘ I x)) i))) ∧
      ∀ z : m → K, Measurable (fun x ↦ ⨆ i : m,
        v x ((z - (A * (A.submatrix (I x) id)⁻¹) *ᵥ (z ∘ I x)) i)) := by
  obtain ⟨I, hI, hnorm⟩ := exists_measurable_maximal_minor A hA v hv
  have hres : ∀ (z : m → K) i, Measurable (fun x ↦
      v x ((z - (A * (A.submatrix (I x) id)⁻¹) *ᵥ (z ∘ I x)) i)) := by
    intro z i
    exact measurable_selected_absoluteValue v hv I hI
      (fun J ↦ (z - (A * (A.submatrix J id)⁻¹) *ᵥ (z ∘ J)) i)
  refine ⟨I, hI, hnorm, ?_, ?_, hres, ?_⟩
  · exact measurable_selected_absoluteValue v hv I hI
      (fun J ↦ (A.submatrix J id).det)
  · intro i j
    exact measurable_selected_absoluteValue v hv I hI
      (fun J ↦ (A * (A.submatrix J id)⁻¹) i j)
  · intro z
    exact Measurable.iSup (hres z)

end ArakelovGeometry.Matrix
