/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Selected semisimple centralizer theorem

Selected from mathlib-initiative/EtingofRepresentationTheory, commit
752fe269b3233f08f0795aa4bcdc5b4c84be7a50. See provenance.json for exact origins.
Only the centralizer theorem is retained; the donor's detailed decomposition
theorems are omitted. It will supply the image algebra for each fixed tensor
degree in Bost p31's binary instability route. It does not assert general
linear reductivity or complete the orbit-separation argument.
-/

@[expose] public section

namespace RepresentationTheory.CentralizerDecomposition

variable (k : Type*) [Field k]
  (E : Type*) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- The centralizer of a semisimple endomorphism subalgebra on a finite-dimensional
space is semisimple. This selected donor theorem supplies the image algebra in
the fixed-degree tensor-power input for Bost p31; no decomposition data or
general linear reductivity is asserted. -/
theorem isSemisimpleRing_centralizer
    (A : Subalgebra k (Module.End k E))
    [IsSemisimpleRing A] :
    IsSemisimpleRing
      (Subalgebra.centralizer k
        (A : Set (Module.End k E))) := by
  have : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  have : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  have : IsSemisimpleRing (Module.End A E) := IsSemisimpleRing.moduleEnd A E
  let toEnd : (Subalgebra.centralizer k (A : Set (Module.End k E))) →+* Module.End A E :=
    { toFun := fun ⟨f, hf⟩ =>
        { f with
          map_smul' := fun (a : A) e => by
            rw [Subalgebra.mem_centralizer_iff] at hf
            have h := hf a.1 a.2
            exact (LinearMap.congr_fun h e).symm }
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let fromEnd : Module.End A E →+* (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    { toFun := fun g =>
        ⟨g.restrictScalars k, by
          rw [Subalgebra.mem_centralizer_iff]
          intro a ha
          ext e
          have := g.map_smul (⟨a, ha⟩ : A) e
          exact this.symm⟩
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }
  let e : (Subalgebra.centralizer k (A : Set (Module.End k E))) ≃+* Module.End A E :=
    RingEquiv.ofRingHom toEnd fromEnd (by ext; rfl) (by ext; rfl)
  exact e.symm.isSemisimpleRing

end RepresentationTheory.CentralizerDecomposition
