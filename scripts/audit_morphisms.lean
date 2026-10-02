import ArakelovGeometry.AdelicCurve.Morphism
import ArakelovGeometry.ExternalResults.ProbabilityCollapse

/-!
Transitive axiom evidence for Chen–Moriwaki, Section 3.7.
Run with `horizon check --lean scripts/audit_morphisms.lean` after the configured build.
-/

#print axioms ArakelovGeometry.AdelicCurve.Hom
#print axioms ArakelovGeometry.AdelicCurve.Hom.id
#print axioms ArakelovGeometry.AdelicCurve.Hom.comp
#print axioms ArakelovGeometry.AdelicCurve.category
#print axioms ArakelovGeometry.AdelicCurve.Hom.integral_comp
#print axioms ArakelovGeometry.AdelicCurve.Hom.algebraicExtension
#print axioms ArakelovGeometry.AdelicCurve.Hom.algebraicExtension_fibreIntegral_toL1
#print axioms ArakelovGeometry.AdelicCurve.Hom.fRestriction
#print axioms ArakelovGeometry.ProbabilityCollapse.averageL1LinearMap
#print axioms ArakelovGeometry.ProbabilityCollapse.averageL1_toL1
#print axioms ArakelovGeometry.ProbabilityCollapse.integral_averageL1
#print axioms ArakelovGeometry.ProbabilityCollapse.averageL1_compMeasurePreserving
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.horizontalAdelicStructure
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.primeAdelicStructure
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.archimedeanAdelicStructure
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.adelicCurve
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.augmentedRationalAdelicCurve
#print axioms ArakelovGeometry.AdelicCurve.RationalFunction.morphismToRationals
#print axioms
  ArakelovGeometry.AdelicCurve.RationalFunction.morphismToRationals_fibreIntegral_toL1
