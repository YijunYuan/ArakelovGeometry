/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite intermediate fields

The filtered family of finite subextensions used in the projective construction
of algebraic scalar extensions (Chen–Moriwaki, §3.4.2).
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

universe u v w

variable {K : Type u} [Field K] (L : Type w) [Field L] [Algebra K L]

/-- The filtered indexing type `E_{L/K}` of finite subextensions of an algebraic extension
`L/K`. -/
structure FiniteIntermediateField (K : Type u) [Field K] (L : Type w) [Field L]
    [Algebra K L] extends IntermediateField K L where
  finite_dimensional : FiniteDimensional K toIntermediateField

attribute [instance] FiniteIntermediateField.finite_dimensional

instance instCoeFiniteIntermediateFieldIntermediateField :
    Coe (FiniteIntermediateField K L) (IntermediateField K L) := ⟨fun F ↦ F.1⟩
attribute [coe] FiniteIntermediateField.toIntermediateField

instance instCoeSortFiniteIntermediateFieldType :
    CoeSort (FiniteIntermediateField K L) (Type w) := ⟨fun F ↦ F.1⟩

namespace FiniteIntermediateField

variable {K : Type u} [Field K] {L : Type w} [Field L] [Algebra K L]

/-- The trivial finite subextension `K/K`, as an element of `E_{L/K}`. -/
def bot : FiniteIntermediateField K L :=
  ⟨⊥, by infer_instance⟩

/-- The compositum of two finite subextensions, giving the filtered upper bound in `E_{L/K}`. -/
def sup (F G : FiniteIntermediateField K L) : FiniteIntermediateField K L :=
  ⟨F.1 ⊔ G.1, by
    have hF : FiniteDimensional K F.1 := F.2
    have hG : FiniteDimensional K G.1 := G.2
    infer_instance⟩

/-- The left finite subextension is contained in its compositum with another one. -/
theorem left_le_sup (F G : FiniteIntermediateField K L) : F.1 ≤ (sup F G).1 :=
  le_sup_left

/-- The right finite subextension is contained in its compositum with another one. -/
theorem right_le_sup (F G : FiniteIntermediateField K L) : G.1 ≤ (sup F G).1 :=
  le_sup_right

end FiniteIntermediateField

end ArakelovGeometry.AdelicStructure
