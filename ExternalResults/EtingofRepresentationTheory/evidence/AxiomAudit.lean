import ArakelovGeometry.InvariantTheory.TensorPower.Semisimple

#print axioms RepresentationTheory.CentralizerDecomposition.isSemisimpleRing_centralizer
#print axioms RepresentationTheory.TensorProducts.Auxiliary.span_range_map_eq_top
#print axioms RepresentationTheory.TensorProducts.Auxiliary.sum_reindexConjugates_mem_auxiliary
#print axioms RepresentationTheory.Auxiliary.MutualCentralizers.centralizer_permutationActionAlgebra
#print axioms RepresentationTheory.Auxiliary.MutualCentralizers.associatedSubalgebras_semisimple
#print axioms RepresentationTheory.PiTensorProduct.MapSpanCentralizer.span_range_piTensorProduct_map_eq_auxiliary
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_span_eq_gl_span
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_image_eq
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_isSemisimpleModule
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_isSemisimpleRepresentation
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_submodule_surjection_splits
#print axioms ArakelovGeometry.InvariantTheory.tensorPowerSL_exists_invariant_lift

example {k E : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup E] [Module k E] [FiniteDimensional k E] [Nontrivial E] :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k E))
      (ArakelovGeometry.InvariantTheory.tensorPowerSLRepresentation k E 0).asModule :=
  ArakelovGeometry.InvariantTheory.tensorPowerSL_isSemisimpleModule k E 0
