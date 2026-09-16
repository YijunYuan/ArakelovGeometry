/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.AlgebraicTowerBasic
import ArakelovGeometry.AdelicCurve.AlgebraicFiniteProjection
import ArakelovGeometry.ExternalResults.AlgebraicTowerSupport

/-!
# Algebraic tower integration on finite cylinders

Finite descent reduces the tower identity for finite-cylinder functions to
finite base change, finite tower integration, and finite embedding naturality.
-/

open MeasureTheory
open scoped ENNReal
namespace ArakelovGeometry.AdelicStructure.Algebraic
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- A finite subextension lies in a finite stage above any intermediate field. -/
theorem exists_finite_upper_stage (F : IntermediateField K L)
    (H : IntermediateField K L) [FiniteDimensional K H] :
    ∃ N : IntermediateField F L, Module.Finite F N ∧
      ∃ i : H →ₐ[K] N, ∀ a : H, (i a : L) = a := by
  classical
  let b := Module.finBasis K H
  let s : Set L := Set.range (fun j ↦ (b j : L))
  let N := IntermediateField.adjoin F s
  have hs : s.Finite := Set.finite_range _
  let : Finite s := hs.to_subtype
  have hN : FiniteDimensional F N :=
    IntermediateField.finiteDimensional_adjoin (fun a _ ↦ Algebra.IsIntegral.isIntegral a)
  have hn (a : H) : (a : L) ∈ N := by
    have hb (j) : (b j : L) ∈ N := IntermediateField.subset_adjoin F s ⟨j, rfl⟩
    have hh := (N.restrictScalars K).toSubmodule.sum_mem
      (fun j (_ : j ∈ Finset.univ) ↦
        (N.restrictScalars K).toSubmodule.smul_mem (b.repr a j) (hb j))
    have hsum : ∑ j, b.repr a j • (b j : L) = (a : L) := by
      exact_mod_cast b.sum_repr a
    rw [hsum] at hh
    exact hh
  let i : H →ₐ[K] N := {
    toFun a := ⟨a.val, hn a⟩
    map_zero' := rfl
    map_one' := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' a := by apply Subtype.ext; rfl }
  exact ⟨N, hN, i, fun _ ↦ rfl⟩

/-- Successive algebraic fibre integration agrees with the finite marginal on every cylinder. -/
theorem fibreLIntegral_tower_projFinite (AS : AdelicStructure K) (F : IntermediateField K L)
    (H : FiniteIntermediateField K L)
    (g : ParameterSpaceFinExtension AS H → ℝ≥0∞) (ω : AS.Ω) :
    fibreLIntegral AS F
      (fibreLIntegral (AS.algebraicExtension F) L
        (fun z ↦ g (projFinite AS H (towerMeasurableEquiv AS F z)))) ω =
      ParameterSpaceFinExtension.fibreLIntegral AS H g ω := by
  classical
  obtain ⟨N, hN, i, hi⟩ := exists_finite_upper_stage F H.1
  let : FiniteDimensional F N := hN
  let : FiniteDimensional K i.fieldRange := i.equivFieldRange.toLinearEquiv.finiteDimensional
  obtain ⟨A, hA, E, hE, hrange, hgen, hdim, hsep⟩ :=
    IntermediateField.exists_finite_descent (B := F) i.fieldRange
  let : FiniteDimensional K A := hA
  let : FiniteDimensional A E := hE
  let : FiniteDimensional K E := Module.Finite.trans A E
  let j : H →ₐ[K] E := {
    toFun a := ⟨i a, hrange ⟨a, rfl⟩⟩
    map_zero' := by apply Subtype.ext; exact i.map_zero
    map_one' := by apply Subtype.ext; exact i.map_one
    map_add' a b := by apply Subtype.ext; exact i.map_add a b
    map_mul' a b := by apply Subtype.ext; exact i.map_mul a b
    commutes' a := by apply Subtype.ext; exact i.commutes a }
  let q (x : ParameterSpaceFinExtension AS E) :=
    projFiniteAlong AS j (ParameterSpaceFinExtension.measurableEquivFull AS E x)
  let h (x : ParameterSpaceFinExtension (AS.finiteExtension A) E) :=
    g (q (ParameterSpaceFinExtension.towerMeasurableEquiv AS E A x))
  have hinner (y : ParameterSpaceExtension AS F) :
      fibreLIntegral (AS.algebraicExtension F) L
          (fun z ↦ g (projFinite AS H (towerMeasurableEquiv AS F z))) y =
        ParameterSpaceFinExtension.fibreLIntegral (AS.finiteExtension A) E h
          (projFiniteAlong AS A.val y) := by
    let x := projFiniteAlong AS A.val y
    have hxy : ((AS.algebraicExtension F).ϕ y).restriction A =
        (AS.finiteExtension A).ϕ x :=
      (projFiniteAlong_ϕ AS A.val y).symm
    let p := ParameterSpaceFinExtension.baseChangeFiber
      (AS.finiteExtension A) (AS.algebraicExtension F) E x y hxy
    have hp := ParameterSpaceFinExtension.lintegral_baseChangeFiber
      (AS.finiteExtension A) (AS.algebraicExtension F) E x y hxy hgen hsep
      (fun z ↦ h z.val)
    have hn := lintegral_projFiniteFiberAlong (AS.algebraicExtension F) N.val y
      (fun z ↦ h (p z).val)
    change _ = ∫⁻ v, h v.val ∂ParameterSpaceFinExtension.fibreProbabilityMeasure
      (AS.finiteExtension A) E x
    erw [← hp, ← hn]
    apply lintegral_congr
    intro z
    apply congrArg g
    apply (ParameterSpaceFinExtension.measurableEquivFull AS H).injective
    apply ParameterSpaceExtension.ext AS H
    · change z.val.base.base = y.base
      exact congrArg (fun t : ParameterSpaceExtension AS F ↦ t.base) z.property
    · change _ = ParameterSpaceFinExtension.ϕ AS H
        (q (ParameterSpaceFinExtension.towerMeasurableEquiv AS E A
          (p (projFiniteFiberAlong (AS.algebraicExtension F) N.val y z)).val))
      dsimp only [q]
      rw [projFiniteAlong_ϕ]
      change _ = (ParameterSpaceFinExtension.ϕ AS E
        (ParameterSpaceFinExtension.towerMeasurableEquiv AS E A
          (p (projFiniteFiberAlong (AS.algebraicExtension F) N.val y z)).val)).pullback j.toRingHom
      rw [ParameterSpaceFinExtension.towerMeasurableEquiv_ϕ]
      dsimp only [p]
      erw [ParameterSpaceFinExtension.baseChangeFiber_ϕ]
      change _ = ((ParameterSpaceFinExtension.ϕ (AS.algebraicExtension F) N
        (projFiniteAlong (AS.algebraicExtension F) N.val z.val)).restriction E).pullback j.toRingHom
      rw [projFiniteAlong_ϕ]
      have hleft : ParameterSpaceFinExtension.ϕ AS H
          (projFinite AS H (towerMeasurableEquiv AS F z.val)) =
          (towerMeasurableEquiv AS F z.val).abv.restriction H :=
        ParameterSpaceFinExtension.extendAbsoluteValue_restriction H _
      change ParameterSpaceFinExtension.ϕ AS H
        (projFinite AS H (towerMeasurableEquiv AS F z.val)) = _
      rw [hleft]
      ext a
      exact congrArg z.val.abv (hi a).symm
  rw [show (fibreLIntegral (AS.algebraicExtension F) L
      (fun z ↦ g (projFinite AS H (towerMeasurableEquiv AS F z)))) =
      (fun y ↦ ParameterSpaceFinExtension.fibreLIntegral (AS.finiteExtension A) E h
        (projFiniteAlong AS A.val y)) from funext hinner]
  erw [fibreLIntegral_comp_projFiniteAlong, ParameterSpaceFinExtension.fibreLIntegral_tower]
  have hcomp : h ∘ (ParameterSpaceFinExtension.towerMeasurableEquiv AS E A).symm =
      fun z ↦ g (q z) := by
    funext z
    exact congrArg (fun t ↦ g (q t))
      ((ParameterSpaceFinExtension.towerMeasurableEquiv AS E A).apply_symm_apply z)
  rw [hcomp]
  have hn := ParameterSpaceFinExtension.lintegral_homFiber AS j ω (fun z ↦ g z.val)
  convert hn using 1
  · apply lintegral_congr
    intro z
    apply congrArg g
    apply (ParameterSpaceFinExtension.measurableEquivFull AS H).injective
    apply ParameterSpaceExtension.ext AS H
    · exact z.property
    · dsimp only [q]
      change ParameterSpaceFinExtension.ϕ AS H
        (projFiniteAlong AS j (ParameterSpaceFinExtension.measurableEquivFull AS E z.val)) = _
      rw [projFiniteAlong_ϕ]
      exact (ParameterSpaceFinExtension.homFiber_ϕ AS j ω z).symm
  · rfl
end ArakelovGeometry.AdelicStructure.Algebraic
