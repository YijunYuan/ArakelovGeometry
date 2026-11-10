/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NumberFieldHermitianLatticeCovolume
import ArakelovGeometry.NumberTheory.NormFamilyNumberFieldFullLatticeModel

/-!
# Integral rational bases inside full number-field lattices

Clearing a nonzero integral denominator in each vector of a rational basis
produces a rational basis contained in the original full lattice. This
discharges the basis-containment hypothesis of the actual index/covolume
formula for every finitely generated full integral lattice.
-/

noncomputable section
open NumberField
open scoped NumberField

namespace ArakelovGeometry.NumberFieldHermitianLatticeCovolume

open AdelicStructure NumberFieldHermitianBasisCovolume NumberFieldArchimedeanCovolume

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E]
  [Module K E] [FiniteDimensional K E]

/-- Full rational span alone produces a rational basis inside the original module. -/
theorem exists_basis_mem (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E, ∀ i, b i ∈ M := by
  classical
  let b := Module.finBasis K E
  choose a ha0 ha using fun i => NumberFieldFullLattice.exists_integral_smul_mem M hspan (b i)
  have haK (i) : (a i : K) ≠ 0 := by
    exact_mod_cast ha0 i
  let u (i) : Kˣ := Units.mk0 (a i : K) (haK i)
  refine ⟨b.unitsSMul u, ?_⟩
  intro i
  simpa only [Module.Basis.unitsSMul_apply, Units.smul_def, u, Units.val_mk0] using ha i

theorem exists_principalModule_le (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E, principalModule b ≤ M := by
  obtain ⟨b, hb⟩ := exists_basis_mem M hspan
  refine ⟨b, Submodule.span_le.mpr ?_⟩
  rintro x ⟨i, rfl⟩
  exact hb i

/-- Every full finitely generated original lattice has the proved actual index formula. -/
theorem exists_principal_index_covolume
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsHermitian normalizedNumberFieldArchimedeanCompletions)
    (M : Submodule (𝓞 K) E) (hfg : M.FG)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      principalModule b ≤ M ∧
      0 < (principalModule b).toAddSubgroup.relIndex M.toAddSubgroup ∧
      euclideanCovolume ξ hξ M =
        (basisDeterminantFactor ξ b *
          (((2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K *
            Real.sqrt |(NumberField.discr K : ℝ)|) ^ Module.finrank K E)) /
          (principalModule b).toAddSubgroup.relIndex M.toAddSubgroup := by
  obtain ⟨b, hb⟩ := exists_principalModule_le M hspan
  exact ⟨b, hb, principal_index_pos ξ hξ b M hfg hspan hb,
    euclideanCovolume_eq_div_principal_index ξ hξ b M hfg hspan hb⟩

end ArakelovGeometry.NumberFieldHermitianLatticeCovolume
