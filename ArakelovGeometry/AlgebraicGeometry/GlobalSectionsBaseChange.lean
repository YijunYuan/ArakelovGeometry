/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AlgebraicGeometry.AffineSectionTensor
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts

/-!
# Finite-cover descent for global sections under scalar extension

Flat extension of scalars preserves the finite diagram of sections on an
open cover and its pairwise intersections. This is the descent input for
global sections of an actual quasi-coherent sheaf under field base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings TensorProduct

noncomputable section

namespace ArakelovGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Flat scalar extension preserves the actual finite sheaf gluing cone.
The vertex is the tensor extension of sections over the union, and all
arrows are tensor extensions of the original restriction maps. -/
def flatTensorSectionsIsLimit (φ : R →+* S) (hφ : φ.Flat)
    {T : TopCat.{u}} (F : T.Sheaf (ModuleCat.{u} R))
    {ι : Type u} [Finite ι] (U : ι → Opens T) :
    IsLimit ((F.obj ⋙ ModuleCat.extendScalars φ).mapCone (Pairwise.cocone U).op) := by
  classical
  letI := Fintype.ofFinite ι
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  exact isLimitOfPreserves (ModuleCat.extendScalars φ)
    (((TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections F.obj).mp F.property U).some)

/-- A presheaf comparison out of flat tensor extension is an isomorphism
on a finite union if it is an isomorphism on the cover and its overlaps.
No global comparison equivalence is assumed. -/
theorem isIso_tensorSections_of_finite_cover (φ : R →+* S) (hφ : φ.Flat)
    {T : TopCat.{u}} (F : T.Sheaf (ModuleCat.{u} R))
    (G : T.Sheaf (ModuleCat.{u} S))
    (α : F.obj ⋙ ModuleCat.extendScalars φ ⟶ G.obj)
    {ι : Type u} [Finite ι] (U : ι → Opens T)
    (hU : ∀ i, IsIso (α.app (op (U i))))
    (hI : ∀ i j, IsIso (α.app (op (U i ⊓ U j)))) :
    IsIso (α.app (op (iSup U))) := by
  classical
  let θ := Functor.whiskerLeft (Pairwise.diagram U).op α
  have : IsIso θ := by
    apply (NatTrans.isIso_iff_isIso_app θ).mpr
    rintro ⟨j⟩
    cases j with
    | single i => exact hU i
    | pair i j => exact hI i j
  let c := (F.obj ⋙ ModuleCat.extendScalars φ).mapCone (Pairwise.cocone U).op
  have hc : IsLimit ((Cone.postcompose θ).obj c) :=
    (IsLimit.postcomposeHomEquiv (asIso θ) c).symm (flatTensorSectionsIsLimit φ hφ F U)
  have hd := ((TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections G.obj).mp
    G.property U).some
  let f : (Cone.postcompose θ).obj c ⟶ G.obj.mapCone (Pairwise.cocone U).op :=
    { hom := α.app (op (iSup U))
      w := fun j => (α.naturality ((Pairwise.cocone U).op.π.app j)).symm }
  have : IsIso f := hc.hom_isIso hd f
  exact (Cone.forget _).map_isIso f

section SchemeSections

variable {A B : CommRingCat.{u}} {X Y : Scheme.{u}}

/-- The actual module sheaf, regarded as a sheaf of modules over the
base ring through the given structural morphism. -/
def modulesToBaseSheaf (b : X ⟶ Spec A) :
    X.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} A) X := by
  let E := ModuleCat.restrictScalars.{u} ((Scheme.ΓSpecIso A).inv ≫ b.appTop).hom
  letI hE : (Opens.grothendieckTopology X).HasSheafCompose E :=
    hasSheafCompose_of_preservesLimitsOfSize _
  exact
  SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
    @sheafCompose _ _ _ _ _ _ _ E hE

/-- On an affine spectrum the base-ring scalar action is restriction of
the coordinate-ring scalar action. The isomorphism is the identity on
actual sections, with scalar compatibility given by `ΓSpecIso` naturality. -/
def affineBaseSectionsIso (a : A ⟶ B) (M : (Spec B).Modules) (U : (Spec B).Opens) :
    ((modulesToBaseSheaf (Spec.map a)).obj M).obj.obj (op U) ≅
      (ModuleCat.restrictScalars a.hom).obj
        (((modulesSpecToSheaf (R := B)).obj M).obj.obj (op U)) :=
  ModuleCat.restrictScalarsComp'App a.hom (Scheme.ΓSpecIso B).inv.hom
    ((Scheme.ΓSpecIso A).inv ≫ (Spec.map a).appTop).hom
    (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality a).symm) _

@[simp]
theorem affineBaseSectionsIso_hom_apply (a : A ⟶ B) (M : (Spec B).Modules)
    (U : (Spec B).Opens) (s : ((modulesToBaseSheaf (Spec.map a)).obj M).obj.obj (op U)) :
    (affineBaseSectionsIso a M U).hom s = s := rfl

/-- Compatibility of scalar actions on local sections in a square over
a base-ring homomorphism. -/
theorem baseSections_scalar_square (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ) (U : X.Opens) :
    (Scheme.ΓSpecIso A).inv ≫ b.appTop ≫ X.presheaf.map U.leTop.op ≫ f.app U =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ c.appTop ≫
        Y.presheaf.map (f ⁻¹ᵁ U).leTop.op := by
  rw [f.naturality]
  have hh := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at hh
  change (Scheme.ΓSpecIso A).inv ≫ b.appTop ≫ f.appTop ≫
    Y.presheaf.map (f ⁻¹ᵁ U).leTop.op = _
  rw [← Category.assoc b.appTop, hh, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]

/-- The actual pullback module sheaf, pushed forward topologically while
retaining its module structure over the new base ring. -/
def pullbackToBaseSheaf (c : Y ⟶ Spec B) (f : Y ⟶ X) (M : X.Modules) :
    TopCat.Sheaf (ModuleCat.{u} B) X :=
  (TopCat.Sheaf.pushforward (ModuleCat.{u} B) f.base).obj
    ((modulesToBaseSheaf c).obj ((Scheme.Modules.pullback f).obj M))

/-- On every open, the actual sheaf-pullback unit is linear over the old
base ring in a commuting square of schemes. -/
def baseSectionPullback (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    (M : X.Modules) (U : X.Opens) :
    ((modulesToBaseSheaf b).obj M).obj.obj (op U) ⟶
      (ModuleCat.restrictScalars φ.hom).obj ((pullbackToBaseSheaf c f M).obj.obj (op U)) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  refine ModuleCat.ofHom
    (X := ((modulesToBaseSheaf b).obj M).obj.obj (op U))
    (Y := (ModuleCat.restrictScalars φ.hom).obj
      ((pullbackToBaseSheaf c f M).obj.obj (op U)))
    { toFun := η.app U
      map_add' := fun s t => map_add (η.app U).hom s t
      map_smul' := ?_ }
  intro r s
  change Γ(M, U) at s
  change η.app U
      (@SMul.smul Γ(X, U) Γ(M, U) inferInstance
        (X.presheaf.map U.leTop.op (((Scheme.ΓSpecIso A).inv ≫ b.appTop) r)) s) =
    @SMul.smul Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) inferInstance
      (Y.presheaf.map (f ⁻¹ᵁ U).leTop.op
        (((Scheme.ΓSpecIso B).inv ≫ c.appTop) (φ r))) (η.app U s)
  erw [Scheme.Modules.Hom.app_smul η]
  change @SMul.smul Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U)
    inferInstance (f.app U (X.presheaf.map U.leTop.op
      (((Scheme.ΓSpecIso A).inv ≫ b.appTop) r))) (η.app U s) = _
  exact congrArg (fun a =>
      @SMul.smul Γ(Y, f ⁻¹ᵁ U) Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U)
        inferInstance a (η.app U s))
    (ConcreteCategory.congr_hom (baseSections_scalar_square φ b c f h U) r)

/-- The actual pullback units on all opens form a morphism of presheaves
over the old base ring. -/
def baseSectionPullbackNat (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    (M : X.Modules) :
    ((modulesToBaseSheaf b).obj M).obj ⟶
      (pullbackToBaseSheaf c f M).obj ⋙ ModuleCat.restrictScalars φ.hom where
  app U := baseSectionPullback φ b c f h M U.unop
  naturality U V g := by
    ext s
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality g) s

/-- The canonical scalar-extension comparison on actual section presheaves.
It is constructed from the pullback unit, rather than supplied as data. -/
def tensorSectionComparison (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    (M : X.Modules) :
    ((modulesToBaseSheaf b).obj M).obj ⋙ ModuleCat.extendScalars φ.hom ⟶
      (pullbackToBaseSheaf c f M).obj where
  app U := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    ((baseSectionPullbackNat φ b c f h M).app U)
  naturality U V g := by
    dsimp only [Functor.comp_map]
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    exact congrArg _ ((baseSectionPullbackNat φ b c f h M).naturality g)

/-- The canonical comparison sends `1 ⊗ s` to the actual pulled-back
section, on each open. -/
theorem tensorSectionComparison_one_tmul (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    (M : X.Modules) (U : X.Opens)
    (s : ((modulesToBaseSheaf b).obj M).obj.obj (op U)) :
    (tensorSectionComparison φ b c f h M).app (op U) ((1 : B) ⊗ₜ[A,φ.hom] s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s := by
  exact ConcreteCategory.congr_hom
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).apply_symm_apply
      ((baseSectionPullbackNat φ b c f h M).app (op U))) s

/-- The actual pure-tensor formula, with the scalar action on the
pulled-back section supplied by the new structural morphism. -/
theorem tensorSectionComparison_tmul (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    (M : X.Modules) (U : X.Opens) (a : B)
    (s : ((modulesToBaseSheaf b).obj M).obj.obj (op U)) :
    (tensorSectionComparison φ b c f h M).app (op U) (a ⊗ₜ[A,φ.hom] s) =
      a • (baseSectionPullback φ b c f h M U s :
        (pullbackToBaseSheaf c f M).obj.obj (op U)) := by
  have ha := ModuleCat.ExtendScalars.smul_tmul φ.hom
    (M := ((modulesToBaseSheaf b).obj M).obj.obj (op U)) a 1 s
  simp only [mul_one] at ha
  erw [← ha, map_smul]
  exact congrArg (fun t => a • t) (tensorSectionComparison_one_tmul φ b c f h M U s)

/-- Pullback followed by topological pushforward, with scalars retained
over the new base ring, is functorial in the original module sheaf. -/
def pullbackModulesToBaseSheaf (c : Y ⟶ Spec B) (f : Y ⟶ X) :
    X.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} B) X :=
  Scheme.Modules.pullback f ⋙ modulesToBaseSheaf c ⋙
    TopCat.Sheaf.pushforward (ModuleCat.{u} B) f.base

/-- Naturality of the actual tensor-section comparison in a morphism of
module sheaves, on every open. -/
theorem tensorSectionComparison_naturality (φ : A ⟶ B) (b : X ⟶ Spec A)
    (c : Y ⟶ Spec B) (f : Y ⟶ X) (h : f ≫ b = c ≫ Spec.map φ)
    {M N : X.Modules} (q : M ⟶ N) (U : X.Opens) :
    (ModuleCat.extendScalars φ.hom).map (((modulesToBaseSheaf b).map q).hom.app (op U)) ≫
        (tensorSectionComparison φ b c f h N).app (op U) =
      (tensorSectionComparison φ b c f h M).app (op U) ≫
        ((pullbackModulesToBaseSheaf c f).map q).hom.app (op U) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  erw [ConcreteCategory.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    tensorSectionComparison_one_tmul, ConcreteCategory.comp_apply,
    tensorSectionComparison_one_tmul]
  have hn := congrArg (fun t => t.app U)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality q)
  exact ConcreteCategory.congr_hom hn s

/-- On affine spectra over their own coordinate rings, the constructed
comparison is the canonical affine quasi-coherent section isomorphism. -/
theorem tensorSectionComparison_affine (φ : A ⟶ B) (M : (Spec A).Modules)
    [M.IsQuasicoherent] :
    (tensorSectionComparison φ (𝟙 (Spec A)) (𝟙 (Spec B)) (Spec.map φ)
      (by simp) M).app (op ⊤) = (affinePullbackSectionsIso φ M).inv := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  erw [tensorSectionComparison_one_tmul]
  apply (affinePullbackSectionsIso φ M).toLinearEquiv.injective
  exact (affinePullbackSectionsIso_apply_unit φ M s).trans
    ((affinePullbackSectionsIso φ M).inv_hom_id_apply _).symm

end SchemeSections

section AlgebraTensorBridge

variable (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]

/-- Bundled extension along an algebra map agrees with the usual algebra
tensor product. Its scalar-action bridge is explicit. -/
def extendScalarsAlgebraMapIso (N : ModuleCat.{u} K) :
    (ModuleCat.extendScalars (algebraMap K L)).obj N ≅ ModuleCat.of L (L ⊗[K] N) := by
  let Q := (ModuleCat.restrictScalars (algebraMap K L)).obj (ModuleCat.of L L)
  letI : Module L Q := inferInstanceAs (Module L L)
  letI : IsScalarTower K L Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : Q ≃ₗ[L] L := { __ := AddEquiv.refl L, map_smul' := fun _ _ => rfl }
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl K N)).toModuleIso

@[simp]
theorem extendScalarsAlgebraMapIso_tmul (N : ModuleCat.{u} K) (a : L) (s : N) :
    (extendScalarsAlgebraMapIso K L N).hom (a ⊗ₜ[K,algebraMap K L] s) = a ⊗ₜ[K] s := rfl

@[simp]
theorem extendScalarsAlgebraMapIso_inv_tmul (N : ModuleCat.{u} K) (a : L) (s : N) :
    (extendScalarsAlgebraMapIso K L N).inv (a ⊗ₜ[K] s) = a ⊗ₜ[K,algebraMap K L] s := rfl

end AlgebraTensorBridge

section AffineRelativeSections

variable (K L C D : Type u) [CommRing K] [CommRing L] [CommRing C] [CommRing D]
  [Algebra K L] [Algebra K C] [Algebra K D] [Algebra C D] [Algebra L D]
  [IsScalarTower K C D] [IsScalarTower K L D] [Algebra.IsPushout K L C D]

/-- Restriction of the tensor module action along an algebra map agrees
with its usual action through the left tensor factor. -/
def restrictTensorScalarsIso (N : ModuleCat.{u} C) :
    (ModuleCat.restrictScalars (algebraMap L D)).obj (ModuleCat.of D (D ⊗[C] N)) ≅
      ModuleCat.of L (D ⊗[C] N) := by
  let P := (ModuleCat.restrictScalars (algebraMap L D)).obj (ModuleCat.of D (D ⊗[C] N))
  letI : Module L P := P.isModule
  refine LinearEquiv.toModuleIso
    (X₁ := P) (g₁ := P.isAddCommGroup) (m₁ := P.isModule)
    (X₂ := D ⊗[C] N) { __ := AddEquiv.refl _, map_smul' := ?_ }
  intro a s
  exact IsScalarTower.algebraMap_smul (M := D ⊗[C] N) D a s

@[simp]
theorem restrictTensorScalarsIso_inv_apply (N : ModuleCat.{u} C) (s : D ⊗[C] N) :
    (restrictTensorScalarsIso L C D N).inv s = s := rfl

/-- Tensor cancellation for the affine relative base-change diagram,
with the actual bundled extension and restriction of scalar actions. -/
def affineTensorBaseChangeIso (N : ModuleCat.{u} C) :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        ((ModuleCat.restrictScalars (algebraMap K C)).obj N) ≅
      (ModuleCat.restrictScalars (algebraMap L D)).obj
        ((ModuleCat.extendScalars (algebraMap C D)).obj N) := by
  letI : Module K N := Module.compHom N (algebraMap K C)
  letI : IsScalarTower K C N := IsScalarTower.of_compHom K C N
  exact extendScalarsAlgebraMapIso K L _ ≪≫
    (Algebra.IsPushout.cancelBaseChange K L C D N).symm.toModuleIso ≪≫
    (restrictTensorScalarsIso L C D N).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap L D)).mapIso (extendScalarsAlgebraMapIso C D N).symm

@[simp]
theorem affineTensorBaseChangeIso_tmul (N : ModuleCat.{u} C) (a : L) (s : N) :
    letI : Module K N := Module.compHom N (algebraMap K C)
    (affineTensorBaseChangeIso K L C D N).hom (a ⊗ₜ[K,algebraMap K L] s) =
      (algebraMap L D a) ⊗ₜ[C,algebraMap C D] s := by
  let : Module K N := Module.compHom N (algebraMap K C)
  dsimp only [affineTensorBaseChangeIso]
  erw [Iso.trans_hom, ConcreteCategory.comp_apply, extendScalarsAlgebraMapIso_tmul]
  erw [Iso.trans_hom, ConcreteCategory.comp_apply]
  erw [LinearEquiv.toModuleIso_hom, ModuleCat.ofHom_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

omit [Algebra.IsPushout K L C D] in
/-- The square of affine scheme maps induced by a pushout algebra diagram
commutes through its actual structural maps. -/
theorem affineRelativeSectionSquare :
    Spec.map (CommRingCat.ofHom (algebraMap C D)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K C)) =
      Spec.map (CommRingCat.ofHom (algebraMap L D)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact (IsScalarTower.algebraMap_apply K C D a).symm.trans
    (IsScalarTower.algebraMap_apply K L D a)

/-- Relative affine global-section base change for the actual
quasi-coherent pullback. The tensor cancellation is constructed above. -/
def affineRelativePullbackSectionsIso (M : (Spec (.of C)).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (algebraMap K L)).obj
        (((modulesToBaseSheaf (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj M).obj.obj
          (op ⊤)) ≅
      (pullbackToBaseSheaf (Spec.map (CommRingCat.ofHom (algebraMap L D)))
        (Spec.map (CommRingCat.ofHom (algebraMap C D))) M).obj.obj (op ⊤) := by
  let N : ModuleCat.{u} C := (moduleSpecΓFunctor (R := CommRingCat.of C)).obj M
  let e₁ := (ModuleCat.extendScalars (algebraMap K L)).mapIso
    (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap K C)) M ⊤)
  let e₂ := affineTensorBaseChangeIso K L C D N
  let e₃ := (ModuleCat.restrictScalars (algebraMap L D)).mapIso
    (affinePullbackSectionsIso (CommRingCat.ofHom (algebraMap C D)) M).symm
  let e₄ := (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap L D))
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).obj M) ⊤).symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- Function-level composition of the four canonical maps defining the
relative affine comparison. -/
theorem affineRelativePullbackSectionsIso_hom_apply
    (M : (Spec (.of C)).Modules) [M.IsQuasicoherent]
    (z : (ModuleCat.extendScalars (algebraMap K L)).obj
      (((modulesToBaseSheaf (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj M).obj.obj
        (op ⊤))) :
    let N : ModuleCat.{u} C := (moduleSpecΓFunctor (R := CommRingCat.of C)).obj M
    let e₁ := (ModuleCat.extendScalars (algebraMap K L)).mapIso
      (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap K C)) M ⊤)
    let e₂ := affineTensorBaseChangeIso K L C D N
    let e₃ := (ModuleCat.restrictScalars (algebraMap L D)).mapIso
      (affinePullbackSectionsIso (CommRingCat.ofHom (algebraMap C D)) M).symm
    let e₄ := (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap L D))
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).obj M) ⊤).symm
    (affineRelativePullbackSectionsIso K L C D M).hom z = e₄.hom (e₃.hom (e₂.hom (e₁.hom z))) := rfl

/-- The constructed relative affine equivalence sends the tensor-unit
section to the genuine pullback unit. -/
theorem affineRelativePullbackSectionsIso_one_tmul
    (M : (Spec (.of C)).Modules) [M.IsQuasicoherent]
    (s : ((modulesToBaseSheaf (Spec.map (CommRingCat.ofHom (algebraMap K C)))).obj M).obj.obj
      (op ⊤)) :
    (affineRelativePullbackSectionsIso K L C D M).hom
        ((1 : L) ⊗ₜ[K,algebraMap K L] s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap C D)))).unit.app M).app ⊤ s := by
  let N : ModuleCat.{u} C := (moduleSpecΓFunctor (R := CommRingCat.of C)).obj M
  let e₁ := (ModuleCat.extendScalars (algebraMap K L)).mapIso
    (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap K C)) M ⊤)
  let e₂ := affineTensorBaseChangeIso K L C D N
  let e₃ := (ModuleCat.restrictScalars (algebraMap L D)).mapIso
    (affinePullbackSectionsIso (CommRingCat.ofHom (algebraMap C D)) M).symm
  let e₄ := (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap L D))
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).obj M) ⊤).symm
  let sc : N := (affineBaseSectionsIso (CommRingCat.ofHom (algebraMap K C)) M ⊤).hom s
  let : Module K N := Module.compHom N (algebraMap K C)
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (algebraMap C D)))).unit.app M).app ⊤
  have h₁ : e₁.hom ((1 : L) ⊗ₜ[K,algebraMap K L] s) =
      (1 : L) ⊗ₜ[K,algebraMap K L] (sc : (ModuleCat.restrictScalars (algebraMap K C)).obj N) := rfl
  have h₂ : e₂.hom ((1 : L) ⊗ₜ[K,algebraMap K L]
      (sc : (ModuleCat.restrictScalars (algebraMap K C)).obj N)) =
      (1 : D) ⊗ₜ[C,algebraMap C D] sc := by
    simpa only [map_one] using affineTensorBaseChangeIso_tmul K L C D N 1 sc
  have h₃ : e₃.hom ((1 : D) ⊗ₜ[C,algebraMap C D] sc) = η sc := by
    apply (affinePullbackSectionsIso (CommRingCat.ofHom (algebraMap C D)) M).toLinearEquiv.injective
    exact ((affinePullbackSectionsIso (CommRingCat.ofHom (algebraMap C D)) M).inv_hom_id_apply
      _).trans
      (affinePullbackSectionsIso_apply_unit (CommRingCat.ofHom (algebraMap C D)) M sc).symm
  have hc := affineRelativePullbackSectionsIso_hom_apply K L C D M
    ((1 : L) ⊗ₜ[K,algebraMap K L] s)
  have h₁' := congrArg (fun x => e₄.hom (e₃.hom (e₂.hom x))) h₁
  have h₂' := congrArg (fun x => e₄.hom (e₃.hom x)) h₂
  have h₃' := congrArg e₄.hom h₃
  exact hc.trans (h₁'.trans (h₂'.trans h₃'))

/-- Identification with the constructed canonical comparison: the
relative affine isomorphism has precisely the pullback-unit formula. -/
theorem affineRelativePullbackSectionsIso_hom_eq_comparison
    (M : (Spec (.of C)).Modules) [M.IsQuasicoherent] :
    (affineRelativePullbackSectionsIso K L C D M).hom =
      (tensorSectionComparison (CommRingCat.ofHom (algebraMap K L))
        (Spec.map (CommRingCat.ofHom (algebraMap K C)))
        (Spec.map (CommRingCat.ofHom (algebraMap L D)))
        (Spec.map (CommRingCat.ofHom (algebraMap C D)))
        (affineRelativeSectionSquare K L C D) M).app (op ⊤) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  exact (affineRelativePullbackSectionsIso_one_tmul K L C D M s).trans
    (tensorSectionComparison_one_tmul (CommRingCat.ofHom (algebraMap K L))
      (Spec.map (CommRingCat.ofHom (algebraMap K C)))
      (Spec.map (CommRingCat.ofHom (algebraMap L D)))
      (Spec.map (CommRingCat.ofHom (algebraMap C D)))
      (affineRelativeSectionSquare K L C D) M ⊤ s).symm

end AffineRelativeSections

section SchemeIsoSections

variable {X Y Z : Scheme.{u}}

/-- Composition of genuine section pullback units on every open, under
the canonical composition isomorphism of pullback sheaves. -/
theorem pullbackUnit_comp_app (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := ConcreteCategory.congr_hom (congrArg (fun t => t.app U) h) s
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app] at h'
  exact h'.symm

/-- Pullback along an actual scheme isomorphism induces an isomorphism
on sections over every open. No quasi-coherence is required. -/
theorem isIso_pullbackUnit_app_of_isIso (i : X ⟶ Y) [IsIso i]
    (M : Y.Modules) (U : Y.Opens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U) := by
  have hi : IsIso (homOfLE (i.image_preimage_le U)) :=
    homOfLE_isIso_of_eq _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq])
  have hu : IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    exact M.presheaf.map_isIso _
  have he := congrArg (fun t => t.app U)
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction i)
      (Scheme.Modules.pullbackPushforwardAdjunction i) M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at he
  have hv : IsIso ((((Scheme.Modules.restrictAdjunction i).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction i)).hom.app M).app (i ⁻¹ᵁ U)) :=
    inferInstance
  rw [← he]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hu hv

/-- The base-linear section-pullback map is an isomorphism whenever the
underlying scheme morphism is an isomorphism. -/
theorem isIso_baseSectionPullback_of_isIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (b : Y ⟶ Spec A) (c : X ⟶ Spec B) (i : X ⟶ Y) [IsIso i]
    (h : i ≫ b = c ≫ Spec.map φ) (M : Y.Modules) (U : Y.Opens) :
    IsIso (baseSectionPullback φ b c i h M U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hb := (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U)).mp
    (isIso_pullbackUnit_app_of_isIso i M U)
  exact hb

end SchemeIsoSections

end ArakelovGeometry
