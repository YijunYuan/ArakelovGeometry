/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Height.Northcott

/-!
# The Northcott property under finite extension

The degree of every element in a finite extension is uniformly bounded by the
extension degree. Claim 3.5.6 therefore implies Chen–Moriwaki, Corollary 3.5.7.
Both existing constructions of the extension adelic structure are covered.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicStructure

variable {K : Type*} [Field K] (AS : AdelicStructure K)
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]

/-- Northcott finiteness for the algebraic extension construction at a finite extension. -/
theorem hasNorthcott_algebraicExtension_of_finite (hS : AS.HasNorthcott) :
    (AS.algebraicExtension E).HasNorthcott := by
  intro C _
  apply (AS.finite_affineHeight_le_degree_le (L := E) hS C
    (Module.finrank K E)).subset
  intro a ha
  refine ⟨ha, ?_⟩
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral a)]
  exact_mod_cast minpoly.natDegree_le a

/-- Chen–Moriwaki, Corollary 3.5.7: every finite extension preserves the Northcott property.
The proof includes inseparable extensions and needs no further assumption on the places. -/
theorem hasNorthcott_finiteExtension (hS : AS.HasNorthcott) :
    (AS.finiteExtension E).HasNorthcott := by
  intro C hC
  apply ((AS.hasNorthcott_algebraicExtension_of_finite E hS) C hC).subset
  intro a ha
  have he := AS.affineHeight_comp_finiteEmbedding (AlgHom.id K E) a
  exact he.trans_le ha

end ArakelovGeometry.AdelicStructure
