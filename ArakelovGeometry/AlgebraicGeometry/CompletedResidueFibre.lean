/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.AffineFibreBaseChange
public import ArakelovGeometry.AlgebraicGeometry.ValuedPoint
public import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# Completed residue fields and actual geometric fibres

Complete the absolute value on each actual scheme residue field. Restriction
along a scheme morphism produces an isometric embedding of those completions.
The induced square of completed field points gives base change of actual
quasi-coherent sheaf fibres on affine schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ArakelovGeometry.ValuedPoint

universe u

variable {X Y : Scheme.{u}}

/-- The completion of the actual valued residue field. -/
abbrev CompletedResidueField (x : ValuedPoint X) := x.value.Completion

/-- The canonical field embedding into the completed residue field. -/
def residueToCompletion (x : ValuedPoint X) :
    X.residueField x.point →+* x.CompletedResidueField :=
  UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv x.value).symm.toRingHom

/-- The canonical residue-field map with the two absolute-value norm structures. -/
def normedResidueMap (f : X ⟶ Y) (x : ValuedPoint X) :
    WithAbs (x.map f).value →+* WithAbs x.value :=
  WithAbs.map (x.map f).value x.value (f.residueFieldMap x.point).hom

theorem isometry_normedResidueMap (f : X ⟶ Y) (x : ValuedPoint X) :
    Isometry (normedResidueMap f x) :=
  AddMonoidHomClass.isometry_of_norm (normedResidueMap f x) (fun _ ↦ rfl)

/-- The canonical isometric map of completed residue fields. -/
def completedResidueMap (f : X ⟶ Y) (x : ValuedPoint X) :
    (x.map f).CompletedResidueField →+* x.CompletedResidueField :=
  UniformSpace.Completion.mapRingHom (normedResidueMap f x)
    (isometry_normedResidueMap f x).continuous

theorem isometry_completedResidueMap (f : X ⟶ Y) (x : ValuedPoint X) :
    Isometry (completedResidueMap f x) :=
  (isometry_normedResidueMap f x).completion_map

@[simp]
theorem completedResidueMap_residueToCompletion (f : X ⟶ Y) (x : ValuedPoint X)
    (a : Y.residueField (f x.point)) :
    completedResidueMap f x ((x.map f).residueToCompletion a) =
      x.residueToCompletion ((f.residueFieldMap x.point) a) :=
  UniformSpace.Completion.mapRingHom_coe _ _

/-- The actual completed-valued-field point of the scheme. -/
def completedPoint (x : ValuedPoint X) : Spec (CommRingCat.of x.CompletedResidueField) ⟶ X :=
  Spec.map (CommRingCat.ofHom x.residueToCompletion) ≫ X.fromSpecResidueField x.point

theorem completedPoint_naturality (f : X ⟶ Y) (x : ValuedPoint X) :
    Spec.map (CommRingCat.ofHom (completedResidueMap f x)) ≫ (x.map f).completedPoint =
      x.completedPoint ≫ f := by
  have h : CommRingCat.ofHom (x.map f).residueToCompletion ≫
        CommRingCat.ofHom (completedResidueMap f x) =
      f.residueFieldMap x.point ≫ CommRingCat.ofHom x.residueToCompletion := by
    ext a
    exact completedResidueMap_residueToCompletion f x a
  change Spec.map (CommRingCat.ofHom (completedResidueMap f x)) ≫
      (Spec.map (CommRingCat.ofHom (x.map f).residueToCompletion) ≫
        Y.fromSpecResidueField (f x.point)) =
    (Spec.map (CommRingCat.ofHom x.residueToCompletion) ≫
      X.fromSpecResidueField x.point) ≫ f
  calc
    _ = Spec.map (CommRingCat.ofHom (x.map f).residueToCompletion ≫
        CommRingCat.ofHom (completedResidueMap f x)) ≫ Y.fromSpecResidueField (f x.point) :=
      (Spec.map_comp_assoc _ _ _).symm
    _ = Spec.map (f.residueFieldMap x.point ≫ CommRingCat.ofHom x.residueToCompletion) ≫
        Y.fromSpecResidueField (f x.point) :=
      congrArg (fun a ↦ Spec.map a ≫ Y.fromSpecResidueField (f x.point)) h
    _ = Spec.map (CommRingCat.ofHom x.residueToCompletion) ≫
        (Spec.map (f.residueFieldMap x.point) ≫ Y.fromSpecResidueField (f x.point)) :=
      Spec.map_comp_assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom x.residueToCompletion) ≫
        (X.fromSpecResidueField x.point ≫ f) :=
      congrArg (fun a ↦ Spec.map (CommRingCat.ofHom x.residueToCompletion) ≫ a)
        (f.SpecMap_residueFieldMap_fromSpecResidueField x.point)
    _ = _ := (Category.assoc _ _ _).symm

/-- The completed geometric fibre of an actual sheaf of modules. -/
def completedFibre (M : X.Modules) (x : ValuedPoint X) : ModuleCat x.CompletedResidueField := by
  let R := CommRingCat.of x.CompletedResidueField
  let N : (Spec R).Modules := (Scheme.Modules.pullback x.completedPoint).obj M
  letI : Module R (Γ(N, ⊤)) :=
    inferInstanceAs (Module R (((modulesSpecToSheaf (R := R)).obj N).obj.obj (.op ⊤)))
  exact ModuleCat.of R (Γ(N, ⊤))

/-- The square of actual completed-field points induces the corresponding
square of pullbacks of sheaves. -/
def completedFibreSheafPullbackIso (f : X ⟶ Y) (M : Y.Modules) (x : ValuedPoint X) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (completedResidueMap f x)))).obj
        ((Scheme.Modules.pullback (x.map f).completedPoint).obj M) ≅
      (Scheme.Modules.pullback x.completedPoint).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (completedResidueMap f x)))
    (x.map f).completedPoint).app M ≪≫
  (Scheme.Modules.pullbackCongr (completedPoint_naturality f x)).app M ≪≫
  ((Scheme.Modules.pullbackComp x.completedPoint f).app M).symm

variable {R : CommRingCat.{u}}

theorem completedPointPullback_isQuasicoherent (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : ValuedPoint (Spec R)) :
    ((Scheme.Modules.pullback x.completedPoint).obj M).IsQuasicoherent := by
  have h := affinePullback_isQuasicoherent (Spec.preimage x.completedPoint) M
  simpa only [Spec.map_preimage] using h

/-- Completed fibres of an actual affine quasi-coherent sheaf commute with
pullback along the canonical isometric embedding of completed residue fields. -/
def completedAffineFibreBaseChangeIso (f : X ⟶ Spec R)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (x : ValuedPoint X) :
    completedFibre ((Scheme.Modules.pullback f).obj M) x ≅
      (ModuleCat.extendScalars (completedResidueMap f x)).obj (completedFibre M (x.map f)) := by
  let : ((Scheme.Modules.pullback (x.map f).completedPoint).obj M).IsQuasicoherent :=
    completedPointPullback_isQuasicoherent M (x.map f)
  exact (moduleSpecΓFunctor (R := CommRingCat.of x.CompletedResidueField)).mapIso
    (completedFibreSheafPullbackIso f M x).symm ≪≫
    affinePullbackSectionsIso (CommRingCat.ofHom (completedResidueMap f x)) _

end ArakelovGeometry.ValuedPoint
