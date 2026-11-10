/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AlgebraicGeometry.CompletedFibreTensorSection
import ArakelovGeometry.Analysis.GeometricModelLineNorm

/-!
# Pullback norms on actual completed line fibres

The canonical geometric tensor isomorphism transports the existing projective
scalar-extension norm. Local frames produce the required finite dimension;
neither a fibre comparison nor a global supremum comparison is assumed.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry.ValuedPoint

universe u

variable {X Y : Scheme.{u}}

/-- A local structure-module frame produces finite dimension of the actual fibre. -/
theorem finiteDimensional_completedFibre_of_frame (M : X.Modules) (x : ValuedPoint X)
    (U : X.Opens) (hx : x.point ∈ U)
    (frame : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    FiniteDimensional x.CompletedResidueField (completedFibre M x) :=
  (completedFibreOfFrameIso M x U hx frame).symm.toLinearEquiv.finiteDimensional

/-- Scalar extension of a given norm on the actual completed line fibre. -/
def completedFibreScalarExtensionNorm (f : X ⟶ Y) (M : Y.Modules) (x : ValuedPoint X)
    (U : Y.Opens) (hx : f x.point ∈ U)
    (frame : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)
    (p : Seminorm (x.map f).CompletedResidueField (completedFibre M (x.map f)))
    (hp : ∀ z, p z = 0 ↔ z = 0) :
    Seminorm x.CompletedResidueField
      ((ModuleCat.extendScalars (completedResidueMap f x)).obj (completedFibre M (x.map f))) := by
  letI := finiteDimensional_completedFibre_of_frame M (x.map f) U hx frame
  exact geometricModuleScalarExtensionSeminorm (completedResidueMap f x)
    (isometry_completedResidueMap f x) (completedFibre M (x.map f)) p hp

/-- Pullback of a fibre norm through the canonical geometric tensor isomorphism. -/
def pullbackFibreNorm (f : X ⟶ Y) (M : Y.Modules) (x : ValuedPoint X)
    (U : Y.Opens) (hx : f x.point ∈ U)
    (frame : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)
    (p : Seminorm (x.map f).CompletedResidueField (completedFibre M (x.map f)))
    (hp : ∀ z, p z = 0 ↔ z = 0) :
    Seminorm x.CompletedResidueField (completedFibre ((Scheme.Modules.pullback f).obj M) x) :=
  (completedFibreScalarExtensionNorm f M x U hx frame p hp).comp
    (completedFibreBaseChangeOfFrameIso f M x U hx frame).hom.hom

theorem pullbackFibreNorm_eq_zero_iff (f : X ⟶ Y) (M : Y.Modules) (x : ValuedPoint X)
    (U : Y.Opens) (hx : f x.point ∈ U)
    (frame : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf)
    (p : Seminorm (x.map f).CompletedResidueField (completedFibre M (x.map f)))
    (hp : ∀ z, p z = 0 ↔ z = 0)
    (z : completedFibre ((Scheme.Modules.pullback f).obj M) x) :
    pullbackFibreNorm f M x U hx frame p hp z = 0 ↔ z = 0 := by
  let := finiteDimensional_completedFibre_of_frame M (x.map f) U hx frame
  change geometricModuleScalarExtensionSeminorm (completedResidueMap f x)
    (isometry_completedResidueMap f x) (completedFibre M (x.map f)) p hp
      ((completedFibreBaseChangeOfFrameIso f M x U hx frame).hom z) = 0 ↔ z = 0
  rw [geometricModuleScalarExtensionSeminorm_eq_zero_iff]
  exact (completedFibreBaseChangeOfFrameIso f M x U hx frame).toLinearEquiv.map_eq_zero_iff

/-- Norm compatibility for an affine field square, before its geometric specialization. -/
theorem affineSectionNorm_square {k L : Type u} [NormedField k] [CompleteSpace k]
    [NormedField L] (φ : k →+* L) (hφ : Isometry φ) {Z : Scheme.{u}}
    (b : Spec (CommRingCat.of k) ⟶ Z) (c : Spec (CommRingCat.of L) ⟶ Y)
    (d : Y ⟶ Z) (h : Spec.map (CommRingCat.ofHom φ) ≫ b = c ≫ d) (M : Z.Modules)
    [((Scheme.Modules.pullback b).obj M).IsQuasicoherent]
    [FiniteDimensional k
      ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj ((Scheme.Modules.pullback b).obj M))]
    (p : Seminorm k
      ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj ((Scheme.Modules.pullback b).obj M)))
    (hp : ∀ z, p z = 0 ↔ z = 0)
    (hr : Module.finrank k
      ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj ((Scheme.Modules.pullback b).obj M)) = 1)
    (s : Γ(M, ⊤)) :
    let e := (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom φ)) b).app M ≪≫
      (Scheme.Modules.pullbackCongr h).app M ≪≫ ((Scheme.Modules.pullbackComp c d).app M).symm
    let q := geometricModuleScalarExtensionSeminorm φ hφ
      ((moduleSpecΓFunctor (R := CommRingCat.of k)).obj ((Scheme.Modules.pullback b).obj M)) p hp
    q (((moduleSpecΓFunctor (R := CommRingCat.of L)).mapIso e.symm ≪≫
        affinePullbackSectionsIso (CommRingCat.ofHom φ) ((Scheme.Modules.pullback b).obj M)).hom
      (pullbackSection c _ (pullbackSection d M s))) = p (pullbackSection b M s) := by
  intro e q
  have ht := affineSection_square_unit (CommRingCat.ofHom φ) b c d h M s
  have hn := congrArg q ht
  exact hn.trans (geometricModuleScalarExtensionSeminorm_unit φ hφ _ p hp hr
    (pullbackSection b M s))

end ArakelovGeometry.ValuedPoint
