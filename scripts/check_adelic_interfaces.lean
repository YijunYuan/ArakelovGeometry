import ArakelovGeometry

/-!
# Adelic structure and bundled curve interfaces

Check instance inference, Northcott hypotheses, and morphism composition across the
structure and curve interfaces. Run with `lake env lean scripts/check_adelic_interfaces.lean`
after `lake build`.
-/

open ArakelovGeometry MeasureTheory CategoryTheory

noncomputable section

universe u v u' v'

section Properties

variable (C : AdelicCurve.{u, v})

-- Properness has a single instance on the underlying structure.
example [C.IsProper] : C.AS.IsProper := inferInstance
example [C.AS.IsProper] : C.IsProper := inferInstance

-- A bundled properness assumption can drive the structure's height API.
example [C.IsProper] (a : Fin 2 → C.K) : 0 ≤ C.AS.logHeight a :=
  C.AS.logHeight_nonneg a

example [C.IsProper] (x : C.K) (hx : x ≠ 0) :
    ∫ ω, Real.log (C.ϕ ω x) ∂C.v = 0 :=
  AdelicCurve.IsProper.product_formula (C := C) x hx

example (h : C.IsProper) (x : C.K) (hx : x ≠ 0) :
    ∫ ω, Real.log (C.ϕ ω x) ∂C.v = 0 :=
  h.product_formula x hx

example [C.IsProper] (F : Subfield C.K) : (C.AS.fRestriction F).IsProper :=
  AdelicStructure.isProper_fRestriction F

example [C.IsProper] (F : Subfield C.K) : (C.fRestriction F).IsProper :=
  AdelicCurve.isProper_fRestriction F

-- Northcott remains an ordinary proposition, usable by the structure's theorem.
example (h : C.HasNorthcott) (B : ℝ) :
    Set.Finite {a : C.K | C.AS.affineHeight a ≤ B} :=
  C.AS.hasNorthcott_iff.mp h B

end Properties

section Examples

variable (K : Type u) [Field K] (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω)

example : (AdelicStructure.trivialAdelicStructure K Ω μ).IsProper := inferInstance
example : (AdelicCurve.trivialAdelicCurve K Ω μ).IsProper := inferInstance

example [NumberField K] : (AdelicStructure.numberFieldAdelicStructure K).IsProper :=
  inferInstance
example [NumberField K] : (AdelicCurve.numberFieldAdelicCurve K).IsProper := inferInstance

example : (AdelicStructure.functionFieldAdelicStructure K).IsProper := inferInstance
example : (AdelicCurve.functionFieldAdelicCurve K).IsProper := inferInstance

end Examples

section Morphisms

variable {K : Type u} {L : Type u'} [Field K] [Field L]
variable (S : AdelicStructure.{u, v} K) (T : AdelicStructure.{u', v'} L)

example [S.IsProper] : S.toAdelicCurve.IsProper := inferInstance
example [S.toAdelicCurve.IsProper] : S.IsProper := inferInstance

-- Structures over different fields can have morphisms without first being bundled.
example (f : AdelicStructure.Hom S T) : L →+* K := f.fieldMap

example (f : AdelicStructure.Hom S T) :
    f.comp (AdelicStructure.Hom.id S) = f := by simp

example (f : AdelicStructure.Hom S T) :
    AdelicCurve.Hom S.toAdelicCurve T.toAdelicCurve := f

example (F : Subfield K) : AdelicStructure.Hom S (S.fRestriction F) :=
  AdelicStructure.Hom.fRestriction S F

example [Algebra K L] [Algebra.IsAlgebraic K L] :
    AdelicStructure.Hom (S.algebraicExtension L) S :=
  AdelicStructure.Hom.algebraicExtension S L

end Morphisms

section Category

variable (C D E : AdelicCurve.{u, v})

example (f : AdelicStructure.Hom C.AS D.AS) : C ⟶ D := f
example (f : C ⟶ D) : AdelicStructure.Hom C.AS D.AS := f

example : (𝟙 C : C ⟶ C) = AdelicStructure.Hom.id C.AS := rfl

example (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = g.comp f := rfl

example (f : C ⟶ D) : AdelicCurve.Hom.comp f (AdelicCurve.Hom.id C) = f := by simp

example (f : C ⟶ D) : f.pullback = AdelicCurve.Hom.pullback f := rfl

example (f g : C ⟶ D) (hfield : f.fieldMap = g.fieldMap)
    (hbase : f.baseMap = g.baseMap) (hintegral : f.fibreIntegral = g.fibreIntegral) :
    f = g :=
  AdelicCurve.Hom.ext hfield hbase hintegral

example (f : C ⟶ D) : AdelicCurve.Hom.comp f (AdelicCurve.Hom.id C) = f := by
  ext <;> rfl

example (f : C ⟶ D) {g : D.Ω → ℝ} (hg : Integrable g D.v) :
    ∫ ω, g (f.baseMap ω) ∂C.v = ∫ ω, g ω ∂D.v :=
  AdelicCurve.Hom.integral_comp f hg

end Category
