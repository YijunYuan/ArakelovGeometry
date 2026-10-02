import ArakelovGeometry

/-!
Transitive axiom evidence for the substantive Section 3.5 producers. Run through
`horizon check --lean scripts/audit_heights.lean` after the configured project build.
The all-project audit in `audit_axioms.lean` additionally checks every declaration.
-/

#print axioms ArakelovGeometry.AdelicStructure.integrable_log_localHeight
#print axioms ArakelovGeometry.AdelicStructure.logHeight_smul_eq
#print axioms ArakelovGeometry.AdelicStructure.absoluteHeight_mk_one
#print axioms ArakelovGeometry.AdelicStructure.affineHeight_pow
#print axioms ArakelovGeometry.AdelicStructure.affineHeight_div_le_logHeight
#print axioms ArakelovGeometry.AdelicStructure.logHeight_comp_finiteEmbedding
#print axioms ArakelovGeometry.AdelicStructure.logHeight_comp_aut
#print axioms ArakelovGeometry.AdelicStructure.affineHeight_coeff_le_polynomialHeight
#print axioms ArakelovGeometry.AdelicStructure.polynomialHeight_mul_le
#print axioms ArakelovGeometry.AdelicStructure.κ_algebraicExtension
#print axioms
  ArakelovGeometry.AdelicStructure.ofReal_polynomialHeight_mul_le_measure_Ωinf_algebraicExtension
#print axioms ArakelovGeometry.AdelicStructure.polynomialHeight_prod_X_sub_C_le_algebraicExtension
#print axioms ArakelovGeometry.AdelicStructure.finite_roots_of_coeff_height_le
