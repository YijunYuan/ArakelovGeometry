/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Degree
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Basic
import ArakelovGeometry.AdelicVectorBundle.Determinant.Comparison
import ArakelovGeometry.AdelicVectorBundle.Determinant.HermitianBasis
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.HermitianComparison.Comparison
import Mathlib.CategoryTheory.Category.Init
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Determinants of actual Hermitian scalar extensions

The canonical scalar extension of a completed orthonormal basis and its
coordinate dual are bounded by one for the actual Hermitian norm. These
bounds prove that the extended basis wedge has determinant volume one.
Purely algebraic completed exterior transport identifies this wedge with
the image of the original orthonormal determinant generator.
Monotonicity and scalar contraction normalize the same generator for the
ordinary extended determinant. Homogeneity on the completed determinant
line then proves the actual Hermitian determinant isometry in every rank.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical completed determinant transport sends a basis wedge to
its canonically extended basis wedge. This statement is purely algebraic. -/
theorem determinantScalarExtensionEquiv_baseChange_completedBasis
    (x : S.ParameterSpaceExtension L)
    (b : Module.Basis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] E)) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let a := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
    let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
      finCongr Module.finrank_baseChange.symm
    let c : Module.Basis (Fin (Module.finrank L (L ⊗[K] E)))
        ((S.algebraicExtension L).ϕ x).Completion
        (((S.algebraicExtension L).ϕ x).Completion ⊗[L] (L ⊗[K] E)) :=
      ((b.baseChange x.abv.Completion).map a.symm).reindex e
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion)
      ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm
        ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion]
          ((exteriorBaseChangeEquiv K (S.ϕ x.base).Completion E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti (S.ϕ x.base).Completion (Module.finrank K E) b)))) =
    (exteriorBaseChangeEquiv L ((S.algebraicExtension L).ϕ x).Completion
      (L ⊗[K] E) (Module.finrank L (L ⊗[K] E))).symm
      (_root_.exteriorPower.ιMulti ((S.algebraicExtension L).ϕ x).Completion
        (Module.finrank L (L ⊗[K] E)) c) := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  intro a e c
  have h := determinantScalarExtensionEquiv_baseChange_completed_ιMulti E
    (S.ϕ x.base) x.abv x.restrict_eq (fun i => b i)
  refine h.trans ?_
  congr 1
  congr 1
  funext j
  change a.symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] b (e.symm j)) =
    (((b.baseChange x.abv.Completion).map a.symm).reindex e) j
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.baseChange_apply]

end

end ArakelovGeometry

namespace ArakelovGeometry.NormFamily

noncomputable section

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
    IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
  (hξ : ξ.IsHermitian hS)

/-- The actual completed Hermitian norm is the Euclidean norm of the
extended coordinates in any original orthonormal basis. -/
theorem hermitianScalarExtension_norm_coordinates
    (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    letI := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    letI := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    letI : IsRCLikeNormedField x.abv.Completion := hL x hx
    letI := IsRCLikeNormedField.rclike x.abv.Completion
    ∀ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] E),
    ∀ z : x.abv.Completion ⊗[L] (L ⊗[K] E),
      (hermitianScalarExtension ξ hS hL hξ).norm x z =
        ‖ArakelovGeometry.hermitianScalarExtensionCoordinates (L := x.abv.Completion) b
          (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z)‖ := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  intro b z
  refine (hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx z).trans ?_
  let b₀ := stdOrthonormalBasis (S.ϕ x.base).Completion
    ((S.ϕ x.base).Completion ⊗[K] E)
  change ArakelovGeometry.hermitianScalarExtensionSeminorm b₀
    (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z) =
      ArakelovGeometry.hermitianScalarExtensionSeminorm b
        (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z)
  exact congrArg (fun p : Seminorm x.abv.Completion
    (x.abv.Completion ⊗[(S.ϕ x.base).Completion] ((S.ϕ x.base).Completion ⊗[K] E)) =>
      p (completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z))
    (ArakelovGeometry.hermitianScalarExtensionSeminorm_eq b₀ b)

/-- The actual canonically extended completed basis and its coordinate dual
are bounded by one for the Hermitian scalar norm. The dual estimate uses
all completed vectors and also covers an empty basis. -/
theorem hermitianScalarExtension_completedBasis_unit_bounds
    (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    letI := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    letI := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    ∀ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] E),
    let η := hermitianScalarExtension ξ hS hL hξ
    let a := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
    let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
      finCongr Module.finrank_baseChange.symm
    let c := ((b.toBasis.baseChange x.abv.Completion).map a.symm).reindex e
    (∀ j, η.norm x (c j) ≤ 1) ∧
      (∀ j, η.dual.norm x
        ((dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)).symm (c.coord j)) ≤ 1) := by
  classical
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  intro b
  let η := hermitianScalarExtension ξ hS hL hξ
  let a := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
  let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
    finCongr Module.finrank_baseChange.symm
  let c := ((b.toBasis.baseChange x.abv.Completion).map a.symm).reindex e
  have hc (j) : c j = a.symm ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion]
      b (e.symm j)) := by
    simp only [c, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Module.Basis.baseChange_apply, OrthonormalBasis.coe_toBasis]
  have hbound :
      (∀ j, η.norm x (c j) ≤ 1) ∧
        (∀ j, η.dual.norm x
          ((dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)).symm (c.coord j)) ≤ 1) := by
    let : IsRCLikeNormedField x.abv.Completion := hL x hx
    let := IsRCLikeNormedField.rclike x.abv.Completion
    have hn := hermitianScalarExtension_norm_coordinates ξ hS hL hξ x hx b
    let p : Seminorm x.abv.Completion (x.abv.Completion ⊗[L] (L ⊗[K] E)) := η.norm x
    have hp (z) : p z = ‖ArakelovGeometry.hermitianScalarExtensionCoordinates b (a z)‖ := hn z
    have hb (j) : η.norm x (c j) ≤ 1 := by
      refine ((congrArg (η.norm x) (hc j)).trans
        (hermitianScalarExtension_norm_tmul_of_infinite ξ hS hL hξ x hx
          (1 : x.abv.Completion) (b (e.symm j)))).trans_le ?_
      change ‖(1 : x.abv.Completion)‖ * ‖b (e.symm j)‖ ≤ 1
      simp only [norm_one, b.norm_eq_one, one_mul, le_refl]
    have hf (j) : η.dual.norm x
        ((dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)).symm (c.coord j)) ≤ 1 := by
      apply η.dual_norm_le x _ zero_le_one
      intro z
      change x.abv.Completion ⊗[L] (L ⊗[K] E) at z
      change ‖(dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E))
        ((dualBaseChangeEquiv L x.abv.Completion (L ⊗[K] E)).symm (c.coord j)) z‖ ≤
          1 * p z
      rw [LinearEquiv.apply_symm_apply]
      change ‖c.repr z j‖ ≤ 1 * p z
      rw [one_mul, hp z]
      change ‖(((b.toBasis.baseChange x.abv.Completion).map a.symm).reindex e).repr z j‖ ≤ _
      rw [Module.Basis.repr_reindex_apply, Module.Basis.map_repr, LinearEquiv.trans_apply]
      change ‖ArakelovGeometry.hermitianScalarExtensionCoordinates b (a z) (e.symm j)‖ ≤
        ‖ArakelovGeometry.hermitianScalarExtensionCoordinates b (a z)‖
      exact PiLp.norm_apply_le _ _
    exact ⟨hb, hf⟩
  exact hbound

/-- The canonically extended completed basis has Hermitian determinant
volume one. The exterior power is formed in the canonical target completion;
the coordinate and dual estimates come from the actual scalar norm. -/
theorem hermitianScalarExtension_determinant_norm_completedBasis
    (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    letI := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    letI := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    ∀ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] E),
    let η := hermitianScalarExtension ξ hS hL hξ
    let a := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq
    let e : Fin (Module.finrank K E) ≃ Fin (Module.finrank L (L ⊗[K] E)) :=
      finCongr Module.finrank_baseChange.symm
    let c : Module.Basis (Fin (Module.finrank L (L ⊗[K] E)))
        ((S.algebraicExtension L).ϕ x).Completion
        (((S.algebraicExtension L).ϕ x).Completion ⊗[L] (L ⊗[K] E)) :=
      ((b.toBasis.baseChange x.abv.Completion).map a.symm).reindex e
    η.determinant.norm x
      ((exteriorBaseChangeEquiv L ((S.algebraicExtension L).ϕ x).Completion
        (L ⊗[K] E) (Module.finrank L (L ⊗[K] E))).symm
        (_root_.exteriorPower.ιMulti ((S.algebraicExtension L).ϕ x).Completion
          (Module.finrank L (L ⊗[K] E)) c)) = 1 := by
  classical
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  intro b η a e c
  let q : Seminorm ((S.algebraicExtension L).ϕ x).Completion
      (((S.algebraicExtension L).ϕ x).Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) := η.determinant.norm x
  have hbound := hermitianScalarExtension_completedBasis_unit_bounds ξ hS hL hξ x hx b
  have hη : η.IsHermitian hL := hermitianScalarExtension_isHermitian ξ hS hL hξ
  have hq (w : ((S.algebraicExtension L).ϕ x).Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
      q w = η.determinant.norm x w := rfl
  have hv := hη.determinant_norm_completedBasis_eq_one η x c hbound.1 hbound.2
  have hvq := (hq _).trans hv
  change q _ = 1
  convert hvq using 1

/-- The actual Hermitian determinant norm of a transported original
orthonormal determinant generator is one. Canonical completed exterior
naturality identifies the transported generator with the extended basis wedge. -/
theorem hermitianScalarExtension_determinant_norm_orthonormalBasis
    (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωinf) :
    letI := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    let η := hermitianScalarExtension ξ hS hL hξ
    let W (t : Fin (Module.finrank K E) → (S.ϕ x.base).Completion ⊗[K] E) :=
      ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion)
        ((completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
          (S.ϕ x.base) x.abv x.restrict_eq).symm
          ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion]
            ((exteriorBaseChangeEquiv K (S.ϕ x.base).Completion E
              (Module.finrank K E)).symm
              (_root_.exteriorPower.ιMulti (S.ϕ x.base).Completion
                (Module.finrank K E) t))))
    letI := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    letI := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    letI := ξ.fibreNormedAddCommGroup x.base
    letI := ξ.fibreNormedSpace x.base
    letI := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
    ∀ b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ x.base).Completion
      ((S.ϕ x.base).Completion ⊗[K] E),
      η.determinant.norm x (W (fun i => b i)) = 1 := by
  classical
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  intro η W
  let := hS x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base ((scalarExtension_mem_Ωinf_iff x).mp hx)
  intro b
  let q : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) := η.determinant.norm x
  have hq (w : ((S.algebraicExtension L).ϕ x).Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
      q w = (hermitianScalarExtension ξ hS hL hξ).determinant.norm x w := rfl
  have hv := hermitianScalarExtension_determinant_norm_completedBasis ξ hS hL hξ x hx b
  have hvq := (hq _).trans hv
  have hm := determinantScalarExtensionEquiv_baseChange_completedBasis x b.toBasis
  have hmnorm := congrArg q hm
  change q _ = 1
  have hvolume := hmnorm.trans hvq
  convert hvolume using 1
  congr 1

/-- The actual Hermitian and ordinary scalar extensions have the same
determinant norm on every completed determinant vector, including rank zero. -/
theorem hermitianScalarExtension_determinant_norm_eq_scalarExtension
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
    (hermitianScalarExtension ξ hS hL hξ).determinant.norm x z =
      (ξ.scalarExtension (L := L)).determinant.norm x z := by
  classical
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let η := hermitianScalarExtension ξ hS hL hξ
  let qH : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) := η.determinant.norm x
  let qO : Seminorm x.abv.Completion
      (x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :=
    (ξ.scalarExtension (L := L)).determinant.norm x
  let A : x.abv.Completion ⊗[(S.ϕ x.base).Completion]
      ((S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) →ₗ[x.abv.Completion]
      x.abv.Completion ⊗[L]
        (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E)) :=
    ((determinantScalarExtensionEquiv K L E).toLinearMap.baseChange x.abv.Completion).comp
      (completedScalarExtensionEquiv (⋀[K]^(Module.finrank K E) E)
        (S.ϕ x.base) x.abv x.restrict_eq).symm.toLinearMap
  let U (t : Fin (Module.finrank K E) → (S.ϕ x.base).Completion ⊗[K] E) :
      (S.ϕ x.base).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E) :=
    (exteriorBaseChangeEquiv K (S.ϕ x.base).Completion E (Module.finrank K E)).symm
      (_root_.exteriorPower.ιMulti (S.ϕ x.base).Completion (Module.finrank K E) t)
  have hm : ∀ v, qH v ≤ qO v :=
    determinant_mono (hermitianScalarExtension_le_scalarExtension ξ hS hL hξ) x
  change qH z = qO z
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · apply le_antisymm (hm z)
    exact determinant_norm_mono (ξ.scalarExtension (L := L)) η x
      (fun v => (scalarExtension_norm_eq_hermitian_of_finite ξ hS hL hξ x hx v).le) z
  · have hbase := (scalarExtension_mem_Ωinf_iff x).mp hx
    let := hS x.base hbase
    let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
    let := ξ.fibreNormedAddCommGroup x.base
    let := ξ.fibreNormedSpace x.base
    let := hξ.fibreInnerProductSpace x.base hbase
    obtain ⟨b, hb⟩ := hξ.exists_completedOrthonormalBasis_determinant_norm_eq_one ξ x.base hbase
    let w := A ((1 : x.abv.Completion) ⊗ₜ[(S.ϕ x.base).Completion] U (fun i => b i))
    have hH : qH w = 1 := by
      have h := hermitianScalarExtension_determinant_norm_orthonormalBasis ξ hS hL hξ x hx b
      convert h using 1
    have hbU : ξ.determinant.norm x.base (U (fun i => b i)) = 1 := by
      convert hb using 1
    have hO_le : qO w ≤ 1 :=
      (ξ.determinant_scalarExtension_norm_completed_one_tmul_le x (U (fun i => b i))).trans_eq hbU
    have hO : qO w = 1 := le_antisymm hO_le (hH.symm.trans_le (hm w))
    have hw : w ≠ 0 := by
      intro he
      rw [he, show qH 0 = 0 from η.determinant.norm_zero x] at hH
      norm_num at hH
    have hr : Module.finrank x.abv.Completion
        (x.abv.Completion ⊗[L]
          (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) = 1 := by
      rw [Module.finrank_baseChange, determinant_finrank]
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one hr hw z
    rw [← ha, map_smul_eq_mul, map_smul_eq_mul, hH, hO]

/-- Determinants commute isometrically with the actual Hermitian scalar
extension under the canonical completed determinant identification. -/
theorem hermitianScalarExtension_determinant_norm_eq
    (x : S.ParameterSpaceExtension L)
    (z : x.abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (L ⊗[K] E)) (L ⊗[K] E))) :
    (hermitianScalarExtension ξ hS hL hξ).determinant.norm x z =
      (ξ.determinant.scalarExtension (L := L)).norm x
        (((determinantScalarExtensionEquiv K L E).symm.toLinearMap.baseChange
          x.abv.Completion) z) :=
  (hermitianScalarExtension_determinant_norm_eq_scalarExtension ξ hS hL hξ x z).trans
    (ξ.determinant_scalarExtension_norm_eq x z)

/-- The actual Hermitian and ordinary extended determinant families agree. -/
theorem hermitianScalarExtension_determinant_eq_scalarExtension :
    (hermitianScalarExtension ξ hS hL hξ).determinant =
      (ξ.scalarExtension (L := L)).determinant := by
  apply NormFamily.ext
  intro x z
  exact hermitianScalarExtension_determinant_norm_eq_scalarExtension ξ hS hL hξ x z

/-- The actual Hermitian extended determinant is the rational pullback of
the scalar extension of the original determinant along the canonical map. -/
theorem hermitianScalarExtension_determinant_eq_pullback :
    (hermitianScalarExtension ξ hS hL hξ).determinant =
      (ξ.determinant.scalarExtension (L := L)).pullback
        (determinantScalarExtensionEquiv K L E).symm.toLinearMap
        (determinantScalarExtensionEquiv K L E).symm.injective := by
  apply NormFamily.ext
  intro x z
  exact hermitianScalarExtension_determinant_norm_eq ξ hS hL hξ x z

/-- Original determinant measurability transfers to the actual Hermitian
extended determinant without requiring whole-vector extension measurability. -/
theorem IsMeasurable.determinant_hermitianScalarExtension
    (hm : ξ.determinant.IsMeasurable) :
    (hermitianScalarExtension ξ hS hL hξ).determinant.IsMeasurable := by
  rw [hermitianScalarExtension_determinant_eq_scalarExtension ξ hS hL hξ]
  exact hm.determinant_scalarExtension

/-- Domination of the original measurable determinant transfers to the
actual Hermitian extended determinant through its proved norm identity. -/
theorem IsDominated.determinant_hermitianScalarExtension
    (hd : ξ.determinant.IsDominated) (hm : ξ.determinant.IsMeasurable) :
    (hermitianScalarExtension ξ hS hL hξ).determinant.IsDominated := by
  rw [hermitianScalarExtension_determinant_eq_scalarExtension ξ hS hL hξ]
  exact hd.determinant_scalarExtension hm

end

end ArakelovGeometry.NormFamily
