/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Measurability.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Strong
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic

import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Line
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Adelic vector bundles

Chen–Moriwaki, Definition 4.1.28, requires a norm family on a finite-dimensional
vector space over the base field, measurability of that family and its completed
dual, and domination.

`NormFamily.IsAdelic` records the three properties of a specified norm family.
`AdelicVectorBundle S` bundles the vector space, its linear structure, the family and
this certificate. It coerces to its carrier, so vectors can be written `x : V`, while
`NormFamily.toAdelicVectorBundle` packages a family whose certificate is available.
The norm family remains a parameter of the certificate, allowing distinct metrics
on the same vector space.

Pullback, quotient and dual constructors take the additional measurability
hypotheses their operations require. The rank-one constructors obtain dual
measurability from the exact completed-dual formulas.
-/

@[expose] public section

open MeasureTheory

namespace ArakelovGeometry

universe u w w'

variable {K : Type u} [Field K] {S : AdelicStructure K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type w'} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

namespace NormFamily

/-- Measurability of the dual reflects measurability on a line. -/
theorem IsMeasurable.of_dual_of_finrank_one {ξ : NormFamily S E}
    (hξ : ξ.dual.IsMeasurable) (hr : Module.finrank K E = 1) : ξ.IsMeasurable := by
  have hb := hξ.dual_of_finrank_one (Subspace.dual_finrank_eq.trans hr)
  have hp := hb.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  simpa only [ξ.dual_dual_pullback_eq_of_finrank_le_one hr.le] using hp

/-- Measurability of the ambient dual gives measurability of every quotient line. -/
theorem IsMeasurable.pushforward_of_dual_of_finrank_one {ξ : NormFamily S E}
    (hξ : ξ.dual.IsMeasurable) (π : E →ₗ[K] F) (hπ : Function.Surjective π)
    (hr : Module.finrank K F = 1) : (ξ.pushforward π hπ).IsMeasurable := by
  apply IsMeasurable.of_dual_of_finrank_one (hr := hr)
  rw [ξ.pushforward_dual π hπ]
  exact hξ.pullback π.dualMap (LinearMap.dualMap_injective_of_surjective hπ)

end NormFamily

/-- Adelicity is a property of a specified norm family: the family and its completed dual
are measurable, and the family is dominated. Keeping the norm family as an explicit parameter
allows different adelic norms on the same rational vector space. -/
class NormFamily.IsAdelic (ξ : NormFamily S E) : Prop where
  /-- Measurability on fixed rational vectors. -/
  isMeasurable : ξ.IsMeasurable
  /-- Measurability of the actual completed dual family. -/
  dual_isMeasurable : ξ.dual.IsMeasurable
  /-- Upper domination of the family and its actual dual. -/
  isDominated : ξ.IsDominated

attribute [instance] NormFamily.IsAdelic.isMeasurable NormFamily.IsAdelic.dual_isMeasurable
  NormFamily.IsAdelic.isDominated

namespace NormFamily

/-- An injective pullback is adelic once its completed dual is measurable. -/
theorem IsAdelic.pullback {ξ : NormFamily S E} (hξ : ξ.IsAdelic) (f : F →ₗ[K] E)
    (hf : Function.Injective f) (hm : (ξ.pullback f hf).dual.IsMeasurable) :
    (ξ.pullback f hf).IsAdelic where
  isMeasurable := hξ.isMeasurable.pullback f hf
  dual_isMeasurable := hm
  isDominated := hξ.isDominated.pullback f hf

/-- Restriction preserves adelicity under the restricted-dual measurability hypothesis. -/
theorem IsAdelic.restrict {ξ : NormFamily S E} (hξ : ξ.IsAdelic) (F : Submodule K E)
    (hm : (ξ.restrict F).dual.IsMeasurable) : (ξ.restrict F).IsAdelic :=
  hξ.pullback F.subtype F.subtype_injective hm

/-- A surjective quotient is adelic once the quotient norm family is measurable. -/
theorem IsAdelic.pushforward {ξ : NormFamily S E} (hξ : ξ.IsAdelic) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (hm : (ξ.pushforward π hπ).IsMeasurable) :
    (ξ.pushforward π hπ).IsAdelic where
  isMeasurable := hm
  dual_isMeasurable := by
    rw [ξ.pushforward_dual π hπ]
    exact hξ.dual_isMeasurable.pullback π.dualMap
      (LinearMap.dualMap_injective_of_surjective hπ)
  isDominated := hξ.isDominated.pushforward π hπ

/-- Quotient by a subspace preserves adelicity under quotient measurability. -/
theorem IsAdelic.quotient {ξ : NormFamily S E} (hξ : ξ.IsAdelic) (F : Submodule K E)
    (hm : (ξ.quotient F).IsMeasurable) : (ξ.quotient F).IsAdelic :=
  hξ.pushforward F.mkQ F.mkQ_surjective hm

/-- Duality preserves adelicity under the completed-bidual measurability hypothesis. -/
theorem IsAdelic.dual {ξ : NormFamily S E} (hξ : ξ.IsAdelic)
    (hm : ξ.dual.dual.IsMeasurable) : ξ.dual.IsAdelic where
  isMeasurable := hξ.dual_isMeasurable
  dual_isMeasurable := hm
  isDominated := hξ.isDominated.dual

/-- A measurable dominated norm family on a line is adelic. -/
theorem isAdelic_of_finrank_one (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    [hm : ξ.IsMeasurable] [hd : ξ.IsDominated] : ξ.IsAdelic where
  isMeasurable := hm
  dual_isMeasurable := hm.dual_of_finrank_one hr
  isDominated := hd

/-- The unique norm family on a zero-dimensional vector space is adelic. -/
instance (priority := 100) isAdelic_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsAdelic where
  isMeasurable := ξ.isMeasurable_of_subsingleton
  dual_isMeasurable := ξ.dual.isMeasurable_of_subsingleton
  isDominated := ξ.isDominated_of_subsingleton

end NormFamily

/-- An adelic vector bundle over `S`: its finite-dimensional rational vector space,
completed norm family and adelicity certificate are all part of the object.
For norms on a specified space, use `NormFamily S E` and `NormFamily.IsAdelic`. -/
structure AdelicVectorBundle.{wE, uK, uΩ} {K : Type uK} [Field K]
    (S : AdelicStructure.{uK, uΩ} K) where
  /-- The underlying rational vector space. -/
  carrier : Type wE
  /-- Addition on the rational vector space. -/
  [instAddCommGroup : AddCommGroup carrier]
  /-- The scalar action of the base field. -/
  [instModule : Module K carrier]
  /-- Finite dimensionality of the rational vector space. -/
  [instFiniteDimensional : FiniteDimensional K carrier]
  /-- The family of norms on the completed fibres. -/
  toNormFamily : NormFamily S carrier
  /-- Measurability of the family and its dual, and domination. -/
  [toIsAdelic : toNormFamily.IsAdelic]

attribute [instance] AdelicVectorBundle.instAddCommGroup AdelicVectorBundle.instModule
  AdelicVectorBundle.instFiniteDimensional AdelicVectorBundle.toIsAdelic

namespace AdelicVectorBundle

instance : CoeSort (AdelicVectorBundle S) (Type w) := ⟨carrier⟩

/-- An explicit norm-family view of a bundled vector space. -/
instance (V : AdelicVectorBundle S) :
    CoeDep (AdelicVectorBundle S) V (NormFamily S V) := ⟨V.toNormFamily⟩

/-- The actual norm on a completed fibre. -/
abbrev norm (V : AdelicVectorBundle S) := V.toNormFamily.norm

/-- The completed fibre norms separate zero. -/
theorem norm_eq_zero_iff (V : AdelicVectorBundle S) :
    ∀ ω x, V.norm ω x = 0 ↔ x = 0 := V.toNormFamily.norm_eq_zero_iff

/-- Primal measurability supplied by adelicity. -/
abbrev isMeasurable (V : AdelicVectorBundle S) := V.toIsAdelic.isMeasurable

/-- Completed-dual measurability supplied by adelicity. -/
abbrev dual_isMeasurable (V : AdelicVectorBundle S) := V.toIsAdelic.dual_isMeasurable

/-- Domination supplied by adelicity. -/
abbrev isDominated (V : AdelicVectorBundle S) := V.toIsAdelic.isDominated

end AdelicVectorBundle

namespace AdelicCurve

/-- Adelic vector bundles over a bundled adelic curve. The underlying implementation
uses its adelic structure; no additional properness assumption is introduced. -/
abbrev AdelicVectorBundle.{wE, uK, uΩ} (C : AdelicCurve.{uK, uΩ}) :=
  ArakelovGeometry.AdelicVectorBundle.{wE} C.AS

end AdelicCurve

/-- Bundle an adelic norm family without changing any of its fibre norms. -/
abbrev NormFamily.toAdelicVectorBundle (ξ : NormFamily S E) [hξ : ξ.IsAdelic] :
    AdelicVectorBundle S where
  carrier := E
  toNormFamily := ξ
  toIsAdelic := inferInstance

@[simp]
theorem NormFamily.toAdelicVectorBundle_toNormFamily (ξ : NormFamily S E) [ξ.IsAdelic] :
    ξ.toAdelicVectorBundle.toNormFamily = ξ := rfl

@[simp]
theorem AdelicVectorBundle.toNormFamily_toAdelicVectorBundle (V : AdelicVectorBundle S) :
    V.toNormFamily.toAdelicVectorBundle = V := rfl

namespace AdelicVectorBundle

/-- The rational dimension, including rank zero. -/
noncomputable def rank (V : AdelicVectorBundle S) : ℕ := Module.finrank K V

/-- Strong adelicity imposes the source strong-domination condition. -/
abbrev IsStronglyAdelic (V : AdelicVectorBundle S) : Prop :=
  V.toNormFamily.IsStronglyDominated

/-- Hermitian adelicity uses the same completed norm family and scalar action. -/
abbrev IsHermitian (V : AdelicVectorBundle S)
    [hS : S.IsArchimedeanNormalized] : Prop :=
  V.toNormFamily.IsHermitian

/-- An adelic line bundle is an adelic bundle of rational rank one. -/
class IsLine (V : AdelicVectorBundle S) : Prop where
  /-- The rational rank is one. -/
  rank_eq_one : V.rank = 1

/-- The rank characterization of an adelic line bundle. -/
theorem isLine_iff (V : AdelicVectorBundle S) : V.IsLine ↔ V.rank = 1 :=
  ⟨fun h ↦ h.rank_eq_one, fun h ↦ ⟨h⟩⟩

/-- Equal norm families on the same vector space give equal bundled objects. -/
theorem ext {ξ η : NormFamily S E} {hξ : ξ.IsAdelic} {hη : η.IsAdelic} (h : ξ = η) :
    ξ.toAdelicVectorBundle (hξ := hξ) = η.toAdelicVectorBundle (hξ := hη) := by
  subst η
  rfl

/-- Packaging a fixed vector space preserves its carrier definitionally. -/
@[simp]
theorem carrier_toAdelicVectorBundle (ξ : NormFamily S E) [ξ.IsAdelic] :
    ξ.toAdelicVectorBundle.carrier = E := rfl

/-- Every rational logarithmic norm in an adelic bundle is integrable. -/
theorem integrable_logNorm (V : AdelicVectorBundle S) (x : V) :
    Integrable (V.toNormFamily.logNorm x) S.v :=
  V.isDominated.integrable_logNorm V.isMeasurable x

/-- Every Hermitian adelic bundle is strongly adelic. -/
theorem IsHermitian.isStronglyAdelic {V : AdelicVectorBundle S}
    [hS : S.IsArchimedeanNormalized]
    (hV : V.IsHermitian) : V.IsStronglyAdelic :=
  (V.toNormFamily.isStronglyDominated_iff_isDominated_of_ultrametric (hξ := hV.1)).2 V.isDominated

/-- Every adelic line bundle is strongly adelic, without an Archimedean hypothesis. -/
theorem IsLine.isStronglyAdelic {V : AdelicVectorBundle S} (hV : V.IsLine) :
    V.IsStronglyAdelic :=
  (V.toNormFamily.isStronglyDominated_iff_isDominated_of_finrank_le_one hV.rank_eq_one.le).2
      V.isDominated

/-- Every adelic line bundle is Hermitian under the source normalization. -/
theorem IsLine.isHermitian {V : AdelicVectorBundle S} (hV : V.IsLine)
    [hS : S.IsArchimedeanNormalized] : V.IsHermitian :=
  V.toNormFamily.isHermitian_of_finrank_one hV.rank_eq_one

instance isStronglyAdelic_of_isHermitian (V : AdelicVectorBundle S)
    [S.IsArchimedeanNormalized] [hV : V.IsHermitian] : V.IsStronglyAdelic :=
  IsHermitian.isStronglyAdelic hV

instance isStronglyAdelic_of_isLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    V.IsStronglyAdelic := IsLine.isStronglyAdelic hV

instance isHermitian_of_isLine (V : AdelicVectorBundle S)
    [S.IsArchimedeanNormalized] [hV : V.IsLine] : V.IsHermitian :=
  IsLine.isHermitian hV

instance isUltrametric_of_isLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    V.toNormFamily.IsUltrametric :=
  V.toNormFamily.isUltrametric_of_finrank_le_one hV.rank_eq_one.le

/-- Source Proposition 4.1.29: a measurable dominated line family is adelic. -/
abbrev ofLine (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    [hm : ξ.IsMeasurable] [hd : ξ.IsDominated] : AdelicVectorBundle S := by
  letI := ξ.isAdelic_of_finrank_one hr
  exact ξ.toAdelicVectorBundle

@[simp]
theorem ofLine_toNormFamily (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    [hm : ξ.IsMeasurable] [hd : ξ.IsDominated] : (ofLine ξ hr).toNormFamily = ξ := rfl

theorem ofLine_isLine (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    [hm : ξ.IsMeasurable] [hd : ξ.IsDominated] : (ofLine ξ hr).IsLine := ⟨hr⟩

/-- Source Proposition 4.1.30: the actual dual of an adelic line is an adelic line. -/
noncomputable abbrev dualLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    AdelicVectorBundle S :=
  ofLine V.toNormFamily.dual (Subspace.dual_finrank_eq.trans hV.rank_eq_one)
    (hd := V.isDominated.dual)

@[simp]
theorem dualLine_toNormFamily (V : AdelicVectorBundle S) [hV : V.IsLine] :
    (V.dualLine).toNormFamily = V.toNormFamily.dual := rfl

theorem dualLine_isLine (V : AdelicVectorBundle S) [hV : V.IsLine] :
    (V.dualLine).IsLine := ⟨Subspace.dual_finrank_eq.trans hV.rank_eq_one⟩

/-- Source Proposition 4.1.31(1): an arbitrary rational subline is adelic. -/
noncomputable abbrev restrictLine (V : AdelicVectorBundle S) (F : Submodule K V)
    (hr : Module.finrank K F = 1) : AdelicVectorBundle S :=
  ofLine (V.toNormFamily.restrict F) hr (hm := (V.isMeasurable.restrict F))
      (hd := (V.isDominated.restrict F))

@[simp]
theorem restrictLine_toNormFamily (V : AdelicVectorBundle S) (F : Submodule K V)
    (hr : Module.finrank K F = 1) :
    (V.restrictLine F hr).toNormFamily = V.toNormFamily.restrict F := rfl

theorem restrictLine_isLine (V : AdelicVectorBundle S) (F : Submodule K V)
    (hr : Module.finrank K F = 1) : (V.restrictLine F hr).IsLine := ⟨hr⟩

/-- Source Proposition 4.1.31(2): every quotient line is adelic.
Quotient measurability is proved from ambient dual measurability and rank-one biduality. -/
noncomputable abbrev quotientLine (V : AdelicVectorBundle S) (π : V →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) : AdelicVectorBundle S :=
  ofLine (V.toNormFamily.pushforward π hπ) hr
    (hm := (V.dual_isMeasurable.pushforward_of_dual_of_finrank_one π hπ hr))
    (hd := (V.isDominated.pushforward π hπ))

@[simp]
theorem quotientLine_toNormFamily (V : AdelicVectorBundle S) (π : V →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) :
    (V.quotientLine π hπ hr).toNormFamily = V.toNormFamily.pushforward π hπ := rfl

theorem quotientLine_isLine (V : AdelicVectorBundle S) (π : V →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) :
    (V.quotientLine π hπ hr).IsLine := ⟨hr⟩

/-- An injective pullback is adelic when its dual norm family is measurable. -/
noncomputable abbrev pullback (V : AdelicVectorBundle S) (f : F →ₗ[K] V)
    (hf : Function.Injective f) [hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable] :
    AdelicVectorBundle S := by
  letI := V.toIsAdelic.pullback f hf hm
  exact (V.toNormFamily.pullback f hf).toAdelicVectorBundle

/-- Source Proposition 4.1.32(1), ordinary adelicity with its stated measurability condition. -/
noncomputable abbrev restrict (V : AdelicVectorBundle S) (F : Submodule K V)
    [hm : (V.toNormFamily.restrict F).dual.IsMeasurable] : AdelicVectorBundle S := by
  letI := V.toIsAdelic.restrict F hm
  exact (V.toNormFamily.restrict F).toAdelicVectorBundle

/-- Source Proposition 4.1.32(2), ordinary adelicity with its stated measurability condition. -/
noncomputable abbrev pushforward (V : AdelicVectorBundle S) (π : V →ₗ[K] F)
    (hπ : Function.Surjective π) [hm : (V.toNormFamily.pushforward π hπ).IsMeasurable] :
    AdelicVectorBundle S := by
  letI := V.toIsAdelic.pushforward π hπ hm
  exact (V.toNormFamily.pushforward π hπ).toAdelicVectorBundle

/-- Source Proposition 4.1.32(3): duality retains the required bidual measurability hypothesis. -/
noncomputable abbrev dual (V : AdelicVectorBundle S)
    [hm : V.toNormFamily.dual.dual.IsMeasurable] : AdelicVectorBundle S := by
  letI := V.toIsAdelic.dual hm
  exact V.toNormFamily.dual.toAdelicVectorBundle

/-- The dual bundle from the source's measurability assumption is strongly adelic. -/
theorem dual_isStronglyAdelic (V : AdelicVectorBundle S)
    [V.toNormFamily.dual.dual.IsMeasurable] : (V.dual).IsStronglyAdelic :=
  V.isDominated.strong_dual

/-- The zero-dimensional norm family is adelic. -/
abbrev ofSubsingleton [Subsingleton E] (ξ : NormFamily S E) : AdelicVectorBundle S :=
  ξ.toAdelicVectorBundle

/-- The rank-zero construction is strongly adelic. -/
theorem ofSubsingleton_isStronglyAdelic [Subsingleton E] (ξ : NormFamily S E) :
    (ofSubsingleton ξ).IsStronglyAdelic := ξ.isStronglyDominated_of_subsingleton

/-- The zero-dimensional adelic bundle is Hermitian. -/
theorem ofSubsingleton_isHermitian [Subsingleton E] (ξ : NormFamily S E)
    [hS : S.IsArchimedeanNormalized] :
    (ofSubsingleton ξ).IsHermitian := ξ.isHermitian_of_subsingleton

/-- On a fixed zero vector space, any two adelic norm families give the same bundle. -/
theorem toAdelicVectorBundle_eq_of_subsingleton [Subsingleton E]
    (ξ η : NormFamily S E) [ξ.IsAdelic] [η.IsAdelic] :
    ξ.toAdelicVectorBundle = η.toAdelicVectorBundle :=
  ext (Subsingleton.elim ξ η)

end AdelicVectorBundle
end ArakelovGeometry

namespace ArakelovGeometry.AdelicVectorBundle
attribute [instance] ofLine_isLine dualLine_isLine restrictLine_isLine quotientLine_isLine
end ArakelovGeometry.AdelicVectorBundle
