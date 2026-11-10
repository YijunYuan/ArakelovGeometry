/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicDivisor.Principal
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The real adelic divisor class space

The class space is the actual Banach quotient by the closed principal
subspace. Properness is used only to descend the continuous degree form.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicDivisor

universe u v

variable {K : Type u} [Field K] (S : AdelicStructure.{u, v} K)

/-- Closedness supplies the separated canonical quotient norm. -/
instance instIsClosedPrincipalSubspace :
    IsClosed (principalSubspace S : Set (AdelicDivisor S)) := isClosed_principalSubspace S

/-- The real adelic divisor class space, as the canonical quotient by the
closed real principal subspace. -/
abbrev Class := AdelicDivisor S ⧸ principalSubspace S

/-- The divisor class space is a Banach space. -/
theorem class_completeSpace : CompleteSpace (Class S) := inferInstance

/-- Passage to the class of a divisor is a continuous real-linear map. -/
noncomputable def classOf : AdelicDivisor S →L[ℝ] Class S := (principalSubspace S).mkQL

/-- The canonical quotient norm is exactly the infimum over principal translations. -/
theorem norm_classOf_eq_sInf (ζ : AdelicDivisor S) :
    ‖classOf S ζ‖ = sInf ((fun η => ‖ζ + η‖) '' (principalSubspace S : Set (AdelicDivisor S))) :=
  quotient_norm_mk_eq (principalSubspace S).toAddSubgroup ζ

/-- The quotient map does not increase norms. -/
theorem norm_classOf_le (ζ : AdelicDivisor S) : ‖classOf S ζ‖ ≤ ‖ζ‖ :=
  Submodule.Quotient.norm_mk_le (principalSubspace S) ζ

/-- The quotient map has operator norm at most one. -/
theorem norm_classOf_le_one : ‖classOf S‖ ≤ 1 :=
  (classOf S).opNorm_le_bound zero_le_one fun ζ => by
    simpa only [one_mul] using norm_classOf_le S ζ

/-- Two divisors have the same class exactly when their difference is principal
in the source's closed-subspace sense. -/
theorem classOf_eq_iff (ζ η : AdelicDivisor S) :
    classOf S ζ = classOf S η ↔ ζ - η ∈ principalSubspace S :=
  Submodule.Quotient.eq (principalSubspace S)

/-- The kernel of the quotient map is the whole closed principal subspace. -/
theorem classOf_eq_zero_iff (ζ : AdelicDivisor S) :
    classOf S ζ = 0 ↔ ζ ∈ principalSubspace S := by
  simpa only [map_zero, sub_zero] using classOf_eq_iff S ζ 0

/-- Closedness makes the quotient norm separate exactly the principal classes. -/
theorem norm_classOf_eq_zero_iff (ζ : AdelicDivisor S) :
    ‖classOf S ζ‖ = 0 ↔ ζ ∈ principalSubspace S := by
  rw [norm_eq_zero, classOf_eq_zero_iff]

/-- Divisors associated with units give the zero class. -/
@[simp]
theorem classOf_principal (a : Kˣ) : classOf S (principal S a) = 0 :=
  (classOf_eq_zero_iff S _).mpr (principal_mem_principalSubspace S a)

/-- Real linear equivalence is equality in the actual divisor class space. -/
def IsLinearlyEquivalent (ζ η : AdelicDivisor S) : Prop := classOf S ζ = classOf S η

/-- The difference criterion for real linear equivalence. -/
theorem isLinearlyEquivalent_iff (ζ η : AdelicDivisor S) :
    IsLinearlyEquivalent S ζ η ↔ ζ - η ∈ principalSubspace S := classOf_eq_iff S ζ η

variable [S.IsProper]

/-- On a proper adelic curve, degree descends through the full closed principal
subspace as a continuous real-linear form on the Banach class space. -/
noncomputable def classDegree : Class S →L[ℝ] ℝ :=
  (principalSubspace S).liftQL (degree S) (principalSubspace_le_ker_degree S)

/-- The descended degree agrees with divisor degree on each representative. -/
@[simp]
theorem classDegree_classOf (ζ : AdelicDivisor S) :
    classDegree S (classOf S ζ) = degree S ζ := rfl

/-- The quotient-norm bound follows from representatives with arbitrarily
small norm excess; it uses the actual quotient norm. -/
theorem abs_classDegree_le_norm (q : Class S) : |classDegree S q| ≤ ‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ζ, rfl, hζ⟩ := Submodule.Quotient.norm_mk_lt q hε
  exact (abs_degree_le_norm S ζ).trans hζ.le

/-- The degree of a divisor class has operator norm at most one. -/
theorem norm_classDegree_le_one : ‖classDegree S‖ ≤ 1 :=
  (classDegree S).opNorm_le_bound zero_le_one fun q => by
    simpa only [Real.norm_eq_abs, one_mul] using abs_classDegree_le_norm S q

/-- Real-linearly equivalent divisors have equal degree on a proper curve. -/
theorem IsLinearlyEquivalent.degree_eq {ζ η : AdelicDivisor S}
    (h : IsLinearlyEquivalent S ζ η) : degree S ζ = degree S η :=
  congrArg (classDegree S) h

/-- Degree on the class space is uniquely determined by its value on divisors. -/
theorem classDegree_unique (f : Class S →L[ℝ] ℝ)
    (hf : ∀ ζ, f (classOf S ζ) = degree S ζ) : f = classDegree S := by
  ext q
  obtain ⟨ζ, rfl⟩ := (principalSubspace S).mkQ_surjective q
  exact hf ζ

end ArakelovGeometry.AdelicDivisor
