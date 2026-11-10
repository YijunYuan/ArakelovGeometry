/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.Line
import ArakelovGeometry.AdelicVectorBundle.StrongDomination
import ArakelovGeometry.AdelicVectorBundle.HermitianLine

/-!
# Adelic vector bundles

Chen–Moriwaki, Definition 4.1.28: on a finite-dimensional rational vector
space, an adelic vector bundle is an actual completed norm family such that
the family and its dual are measurable and the family is dominated.

The underlying vector space is a parameter. No measurability of a general
quotient or bidual is built into the definition. The line constructors prove
the additional measurability they need from the exact completed dual formulas.
-/

open MeasureTheory

namespace ArakelovGeometry

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
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

/-- An adelic vector bundle on the finite-dimensional rational space `E`.
Both measurability clauses in source Definition 4.1.28 are retained. -/
structure AdelicVectorBundle (S : AdelicStructure.{u, v} K) (E : Type w)
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] extends NormFamily S E where
  /-- Measurability on fixed rational vectors. -/
  isMeasurable : toNormFamily.IsMeasurable
  /-- Measurability of the actual completed dual family. -/
  dual_isMeasurable : toNormFamily.dual.IsMeasurable
  /-- Upper domination of the family and its actual dual. -/
  isDominated : toNormFamily.IsDominated

namespace AdelicVectorBundle

/-- The rational dimension, including rank zero. -/
noncomputable def rank (_ : AdelicVectorBundle S E) : ℕ := Module.finrank K E

/-- Strong adelicity imposes the source strong-domination condition. -/
def IsStronglyAdelic (V : AdelicVectorBundle S E) : Prop :=
  V.toNormFamily.IsStronglyDominated

/-- Hermitian adelicity uses the same completed norm family and scalar action. -/
def IsHermitian (V : AdelicVectorBundle S E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : Prop :=
  V.toNormFamily.IsHermitian hS

/-- An adelic line bundle is an adelic bundle of rational rank one. -/
def IsLine (V : AdelicVectorBundle S E) : Prop := V.rank = 1

@[ext]
theorem ext {V W : AdelicVectorBundle S E} (h : V.toNormFamily = W.toNormFamily) : V = W := by
  cases V
  cases W
  cases h
  rfl

/-- Every rational logarithmic norm in an adelic bundle is integrable. -/
theorem integrable_logNorm (V : AdelicVectorBundle S E) (x : E) :
    Integrable (V.toNormFamily.logNorm x) S.v :=
  V.isDominated.integrable_logNorm V.isMeasurable x

/-- Every Hermitian adelic bundle is strongly adelic. -/
theorem IsHermitian.isStronglyAdelic {V : AdelicVectorBundle S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hV : V.IsHermitian hS) : V.IsStronglyAdelic :=
  (V.toNormFamily.isStronglyDominated_iff_isDominated_of_ultrametric hV.1 hS).2 V.isDominated

/-- Every adelic line bundle is strongly adelic, without an Archimedean hypothesis. -/
theorem IsLine.isStronglyAdelic {V : AdelicVectorBundle S E} (hV : V.IsLine) :
    V.IsStronglyAdelic :=
  (V.toNormFamily.isStronglyDominated_iff_isDominated_of_finrank_le_one hV.le).2 V.isDominated

/-- Every adelic line bundle is Hermitian under the source normalization. -/
theorem IsLine.isHermitian {V : AdelicVectorBundle S E} (hV : V.IsLine)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) : V.IsHermitian hS :=
  V.toNormFamily.isHermitian_of_finrank_one hV hS

/-- Source Proposition 4.1.29: a measurable dominated line family is adelic. -/
def ofLine (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    (hm : ξ.IsMeasurable) (hd : ξ.IsDominated) : AdelicVectorBundle S E where
  toNormFamily := ξ
  isMeasurable := hm
  dual_isMeasurable := hm.dual_of_finrank_one hr
  isDominated := hd

@[simp]
theorem ofLine_toNormFamily (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    (hm : ξ.IsMeasurable) (hd : ξ.IsDominated) : (ofLine ξ hr hm hd).toNormFamily = ξ := rfl

theorem ofLine_isLine (ξ : NormFamily S E) (hr : Module.finrank K E = 1)
    (hm : ξ.IsMeasurable) (hd : ξ.IsDominated) : (ofLine ξ hr hm hd).IsLine := hr

/-- Source Proposition 4.1.30: the actual dual of an adelic line is an adelic line. -/
noncomputable def dualLine (V : AdelicVectorBundle S E) (hV : V.IsLine) :
    AdelicVectorBundle S (Module.Dual K E) :=
  ofLine V.toNormFamily.dual (Subspace.dual_finrank_eq.trans hV)
    V.dual_isMeasurable V.isDominated.dual

@[simp]
theorem dualLine_toNormFamily (V : AdelicVectorBundle S E) (hV : V.IsLine) :
    (V.dualLine hV).toNormFamily = V.toNormFamily.dual := rfl

theorem dualLine_isLine (V : AdelicVectorBundle S E) (hV : V.IsLine) :
    (V.dualLine hV).IsLine := Subspace.dual_finrank_eq.trans hV

/-- Source Proposition 4.1.31(1): an arbitrary rational subline is adelic. -/
noncomputable def restrictLine (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hr : Module.finrank K F = 1) : AdelicVectorBundle S F :=
  ofLine (V.toNormFamily.restrict F) hr (V.isMeasurable.restrict F) (V.isDominated.restrict F)

@[simp]
theorem restrictLine_toNormFamily (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hr : Module.finrank K F = 1) :
    (V.restrictLine F hr).toNormFamily = V.toNormFamily.restrict F := rfl

theorem restrictLine_isLine (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hr : Module.finrank K F = 1) : (V.restrictLine F hr).IsLine := hr

/-- Source Proposition 4.1.31(2): every quotient line is adelic.
Quotient measurability is proved from ambient dual measurability and rank-one biduality. -/
noncomputable def quotientLine (V : AdelicVectorBundle S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) : AdelicVectorBundle S F :=
  ofLine (V.toNormFamily.pushforward π hπ) hr
    (V.dual_isMeasurable.pushforward_of_dual_of_finrank_one π hπ hr)
    (V.isDominated.pushforward π hπ)

@[simp]
theorem quotientLine_toNormFamily (V : AdelicVectorBundle S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) :
    (V.quotientLine π hπ hr).toNormFamily = V.toNormFamily.pushforward π hπ := rfl

theorem quotientLine_isLine (V : AdelicVectorBundle S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (hr : Module.finrank K F = 1) :
    (V.quotientLine π hπ hr).IsLine := hr

/-- An injective pullback is adelic when its dual norm family is measurable. -/
noncomputable def pullback (V : AdelicVectorBundle S E) (f : F →ₗ[K] E)
    (hf : Function.Injective f) (hm : (V.toNormFamily.pullback f hf).dual.IsMeasurable) :
    AdelicVectorBundle S F where
  toNormFamily := V.toNormFamily.pullback f hf
  isMeasurable := V.isMeasurable.pullback f hf
  dual_isMeasurable := hm
  isDominated := V.isDominated.pullback f hf

/-- Source Proposition 4.1.32(1), ordinary adelicity with its stated measurability condition. -/
noncomputable def restrict (V : AdelicVectorBundle S E) (F : Submodule K E)
    (hm : (V.toNormFamily.restrict F).dual.IsMeasurable) : AdelicVectorBundle S F :=
  V.pullback F.subtype F.subtype_injective hm

/-- Source Proposition 4.1.32(2), ordinary adelicity with its stated measurability condition. -/
noncomputable def pushforward (V : AdelicVectorBundle S E) (π : E →ₗ[K] F)
    (hπ : Function.Surjective π) (hm : (V.toNormFamily.pushforward π hπ).IsMeasurable) :
    AdelicVectorBundle S F where
  toNormFamily := V.toNormFamily.pushforward π hπ
  isMeasurable := hm
  dual_isMeasurable := by
    rw [V.toNormFamily.pushforward_dual π hπ]
    exact V.dual_isMeasurable.pullback π.dualMap
      (LinearMap.dualMap_injective_of_surjective hπ)
  isDominated := V.isDominated.pushforward π hπ

/-- Source Proposition 4.1.32(3): duality retains the required bidual measurability hypothesis. -/
noncomputable def dual (V : AdelicVectorBundle S E)
    (hm : V.toNormFamily.dual.dual.IsMeasurable) : AdelicVectorBundle S (Module.Dual K E) where
  toNormFamily := V.toNormFamily.dual
  isMeasurable := V.dual_isMeasurable
  dual_isMeasurable := hm
  isDominated := V.isDominated.dual

/-- The dual bundle from the source's measurability assumption is strongly adelic. -/
theorem dual_isStronglyAdelic (V : AdelicVectorBundle S E)
    (hm : V.toNormFamily.dual.dual.IsMeasurable) : (V.dual hm).IsStronglyAdelic :=
  V.isDominated.strong_dual

/-- The zero-dimensional norm family is adelic. -/
def ofSubsingleton [Subsingleton E] (ξ : NormFamily S E) : AdelicVectorBundle S E where
  toNormFamily := ξ
  isMeasurable := ξ.isMeasurable_of_subsingleton
  dual_isMeasurable := ξ.dual.isMeasurable_of_subsingleton
  isDominated := ξ.isDominated_of_subsingleton

/-- The rank-zero construction is strongly adelic. -/
theorem ofSubsingleton_isStronglyAdelic [Subsingleton E] (ξ : NormFamily S E) :
    (ofSubsingleton ξ).IsStronglyAdelic := ξ.isStronglyDominated_of_subsingleton

/-- The zero-dimensional adelic bundle is Hermitian. -/
theorem ofSubsingleton_isHermitian [Subsingleton E] (ξ : NormFamily S E)
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofSubsingleton ξ).IsHermitian hS := NormFamily.isHermitian_of_subsingleton

/-- There is only one adelic bundle on a fixed zero vector space. -/
instance instSubsingleton [Subsingleton E] : Subsingleton (AdelicVectorBundle S E) where
  allEq V W := by
    apply ext
    apply NormFamily.ext
    intro ω x
    rw [V.toNormFamily.norm_eq_zero_of_subsingleton, W.toNormFamily.norm_eq_zero_of_subsingleton]

end AdelicVectorBundle
end ArakelovGeometry
