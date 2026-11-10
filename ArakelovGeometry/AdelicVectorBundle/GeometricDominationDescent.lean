/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Valued overfields for geometric domination descent

Common valued overfields provide the field-theoretic lift of an analytic
point through finite base change. The geometric section-space and metric
interfaces required for Corollary 4.1.18 remain separate prerequisites.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

variable {k L H : Type*} [Field k] [Field L] [Field H]
  [Algebra k L] [Algebra k H] [FiniteDimensional k L]

/-- A specified finite valued extension and a valued residue field embed in
one actual algebraically closed field, preserving both absolute values.
Completeness of the ground value forces the specified value on `L`. -/
theorem exists_compatible_absoluteValue_on_algebraicClosure
    (v : AbsoluteValue k ℝ) [CompleteSpace (WithAbs v)]
    (vL : AbsoluteValue L ℝ) (vH : AbsoluteValue H ℝ)
    (hL : vL.under k = v) (hH : vH.under k = v) :
    ∃ (i : L →ₐ[k] AlgebraicClosure H) (u : AbsoluteValue (AlgebraicClosure H) ℝ),
      u.under H = vH ∧ u.comp i.toRingHom.injective = vL := by
  let i : L →ₐ[k] AlgebraicClosure H := IsAlgClosed.lift
  obtain ⟨u, hu⟩ := AbsoluteValue.exists_extension (L := AlgebraicClosure H) vH
  have hbase : (u.comp i.toRingHom.injective).under k = v := by
    ext a
    change u (i (algebraMap k L a)) = v a
    rw [i.commutes, IsScalarTower.algebraMap_apply k H (AlgebraicClosure H)]
    have hu' := congrArg (fun w : AbsoluteValue H ℝ => w (algebraMap k H a)) hu
    have hH' := congrArg (fun w : AbsoluteValue k ℝ => w a) hH
    exact hu'.trans hH'
  obtain ⟨w, hw, huniq⟩ := AbsoluteValue.existsUnique_extension_of_complete (L := L) v
  exact ⟨i, u, hu, (huniq _ hbase).trans (huniq _ hL).symm⟩

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- A genuine valued scheme point lifts through finite field base change
after a produced common valued extension. Both projections and both absolute
values are compatible, with no analytification model assumed. -/
theorem exists_valued_scheme_baseChange_lift.{u}
    {k L H : Type u} [Field k] [Field L] [Field H]
    [Algebra k L] [Algebra k H] [FiniteDimensional k L]
    (v : AbsoluteValue k ℝ) [CompleteSpace (WithAbs v)]
    (vL : AbsoluteValue L ℝ) (vH : AbsoluteValue H ℝ)
    (hL : vL.under k = v) (hH : vH.under k = v)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of H) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H))) :
    ∃ (i : L →ₐ[k] AlgebraicClosure H) (u : AbsoluteValue (AlgebraicClosure H) ℝ),
      u.under H = vH ∧ u.comp i.toRingHom.injective = vL ∧
      ∃ y : Spec (CommRingCat.of (AlgebraicClosure H)) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))),
        y ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
            Spec.map (CommRingCat.ofHom (algebraMap H (AlgebraicClosure H))) ≫ x ∧
          y ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
            Spec.map (CommRingCat.ofHom i.toRingHom) := by
  obtain ⟨i, u, huH, huL⟩ :=
    exists_compatible_absoluteValue_on_algebraicClosure v vL vH hL hH
  have hcomm : (Spec.map (CommRingCat.ofHom (algebraMap H (AlgebraicClosure H))) ≫ x) ≫ f =
      Spec.map (CommRingCat.ofHom i.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change algebraMap H (AlgebraicClosure H) (algebraMap k H a) = i (algebraMap k L a)
    rw [i.commutes, ← IsScalarTower.algebraMap_apply k H (AlgebraicClosure H)]
  refine ⟨i, u, huH, huL,
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap H (AlgebraicClosure H))) ≫ x)
      (Spec.map (CommRingCat.ofHom i.toRingHom)) hcomm, ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

end ArakelovGeometry

end
