/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Morphism.Basic
import ArakelovGeometry.AdelicCurve.Restriction

/-!
# The subfield-restriction morphism

The inclusion of a subfield, together with identity maps on the parameter space
and on `L¹`, is the morphism of Chen–Moriwaki, Example 3.7.2(2).
-/

namespace ArakelovGeometry.AdelicCurve.Hom

open MeasureTheory

/-- Example 3.7.2(2): restriction to a subfield is an adelic-curve morphism. -/
noncomputable def fRestriction (C : AdelicCurve) (F : Subfield C.K) :
    Hom C (C.fRestriction F) where
  fieldMap := F.subtype
  baseMap := _root_.id
  measurePreserving := MeasurePreserving.id C.v
  absoluteValue_comp _ _ := rfl
  fibreIntegral := LinearMap.id
  integral_fibreIntegral _ := rfl
  fibreIntegral_pullback := Lp.compMeasurePreserving_id_apply

@[simp]
theorem fRestriction_fieldMap (C : AdelicCurve) (F : Subfield C.K) :
    (fRestriction C F).fieldMap = F.subtype := rfl

@[simp]
theorem fRestriction_baseMap (C : AdelicCurve) (F : Subfield C.K) (ω : C.Ω) :
    (fRestriction C F).baseMap ω = ω := rfl

@[simp]
theorem fRestriction_fibreIntegral (C : AdelicCurve) (F : Subfield C.K)
    (f : Lp ℝ 1 C.v) :
    (fRestriction C F).fibreIntegral f = f := rfl

end ArakelovGeometry.AdelicCurve.Hom
