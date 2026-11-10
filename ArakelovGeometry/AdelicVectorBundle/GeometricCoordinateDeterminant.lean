/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeDeterminantIsometry
public import ArakelovGeometry.AdelicVectorBundle.DeterminantHermitianBasis
public import ArakelovGeometry.AdelicVectorBundle.GeometricCoordinateDual
public import ArakelovGeometry.AdelicVectorBundle.GeometricCoordinateRestrictionEquiv
public import ArakelovGeometry.AdelicVectorBundle.Line
public import ArakelovGeometry.Analysis.DeterminantExactSequence

/-!
# Actual determinants of finitely selected coordinate norms

Actual completed unit bases and their coordinate duals determine determinant
volume through the Hermitian determinant pairing. Finite measurable selection
then proves rational determinant measurability without ground-field or
parameter-space countability.
-/

@[expose] public section

open MeasureTheory
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

noncomputable section

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily S E}
  {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}

/-- An actual completed coordinate maximum identifies the genuine determinant
norm with the absolute value of its rational top exterior coordinate. -/
theorem IsHermitian.determinant_norm_rational_eq_absValue_of_coordinates
    (hξ : ξ.IsHermitian hS) (b : Module.Basis (Fin (Module.finrank K E)) K E)
    (ω : S.Ω)
    (hcoord : ∀ z : (S.ϕ ω).Completion ⊗[K] E,
      ξ.norm ω z = ‖(b.baseChange (S.ϕ ω).Completion).equivFun z‖)
    (t : ⋀[K]^(Module.finrank K E) E) :
    ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) =
      (S.ϕ ω) (determinantCoordinateEquiv b t) := by
  classical
  let B := b.baseChange (S.ϕ ω).Completion
  have hb (i : Fin (Module.finrank K E)) : ξ.norm ω (B i) ≤ 1 := by
    rw [hcoord]
    simpa only [B, Module.Basis.baseChange_apply, ofBasis_norm, norm_one] using
      (ofBasis_norm_tmul_basis (S := S) (E := E) b ω (1 : (S.ϕ ω).Completion) i).le
  have hf (i : Fin (Module.finrank K E)) : ξ.dual.norm ω
      ((dualBaseChangeEquiv K (S.ϕ ω).Completion E).symm (B.coord i)) ≤ 1 := by
    apply ξ.dual_norm_le ω _ zero_le_one
    intro z
    rw [LinearEquiv.apply_symm_apply, one_mul, hcoord]
    simpa only [Module.Basis.coord_apply, Module.Basis.equivFun_apply] using
      norm_le_pi_norm (B.equivFun z) i
  have hvol := hξ.determinant_norm_completedBasis_eq_one ξ ω B hb hf
  have hw : ξ.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] exteriorPower.ιMulti K _ b) = 1 := by
    have hB : ⇑B = fun i ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] b i := by
      ext i
      exact Module.Basis.baseChange_apply _ _ _
    rw [hB, exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one] at hvol
    exact hvol
  have ht : t = determinantCoordinateEquiv b t • exteriorPower.ιMulti K _ b := by
    rw [← determinantCoordinateEquiv_symm b, LinearEquiv.symm_apply_apply]
  calc
    _ = ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K]
        (determinantCoordinateEquiv b t • exteriorPower.ιMulti K _ b)) :=
      congrArg (fun t ↦ ξ.determinant.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t)) ht
    _ = _ := by rw [ξ.determinant.norm_rational_smul, hw, mul_one]

/-- A finite measurable choice of actual rational coordinate bases produces
measurability of the genuine determinant family. -/
theorem IsHermitian.determinant_isMeasurable_of_finite_coordinate_bases
    (hξ : ξ.IsHermitian hS) {J : Type*} [Finite J]
    (I : S.Ω → J) (hI : ∀ j, MeasurableSet {ω | I ω = j})
    (b : J → Module.Basis (Fin (Module.finrank K E)) K E)
    (hcoord : ∀ ω (z : (S.ϕ ω).Completion ⊗[K] E),
      ξ.norm ω z = ‖((b (I ω)).baseChange (S.ϕ ω).Completion).equivFun z‖) :
    ξ.determinant.IsMeasurable := by
  classical
  let := Fintype.ofFinite J
  intro t
  have hp (j : J) : Measurable (fun ω ↦
      if I ω = j then (S.ϕ ω) (determinantCoordinateEquiv (b j) t) else 0) :=
    (S.measurable_absValue _).piecewise (hI j) measurable_const
  have hm : Measurable (fun ω ↦ ∑ j : J,
      if I ω = j then (S.ϕ ω) (determinantCoordinateEquiv (b j) t) else 0) := by
    fun_prop
  convert hm using 1
  funext ω
  rw [hξ.determinant_norm_rational_eq_absValue_of_coordinates (b (I ω)) ω (hcoord ω)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The actual dual determinant is measurable on the same finite partition,
using the produced determinant measurability and its genuine line dual. -/
theorem IsHermitian.determinant_dual_isMeasurable_of_finite_coordinate_bases
    (hξ : ξ.IsHermitian hS) {J : Type*} [Finite J]
    (I : S.Ω → J) (hI : ∀ j, MeasurableSet {ω | I ω = j})
    (b : J → Module.Basis (Fin (Module.finrank K E)) K E)
    (hcoord : ∀ ω (z : (S.ϕ ω).Completion ⊗[K] E),
      ξ.norm ω z = ‖((b (I ω)).baseChange (S.ϕ ω).Completion).equivFun z‖) :
    ξ.determinant.dual.IsMeasurable :=
  (hξ.determinant_isMeasurable_of_finite_coordinate_bases I hI b hcoord).dual_of_finrank_one
    (determinant_finrank (K := K) (E := E))

variable {m : Type*} [Fintype m]

omit [FiniteDimensional K E] in
/-- Coordinate maximum families are Hermitian when all places are finite;
the infinite-place condition has an empty domain. -/
theorem ofBasis_isHermitian_of_all_finite (b : Module.Basis m K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin)
    (harch : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    (ofBasis S E b).IsHermitian harch := by
  have he : ofBasis S E b = ofBasisMixed S E b := by
    ext ω z
    exact (ofBasisMixed_norm_of_finite b ω (hfin ω) z).symm
  refine ⟨?_, fun ω hω ↦ False.elim (hω (hfin ω))⟩
  rw [he]
  exact ofBasisMixed_isUltrametric b

/-- The actual completed restriction norms use fixed rational coordinate bases
on a finite measurable partition produced from maximal ground minors. -/
theorem exists_measurable_ofBasis_restrict_coordinate_bases
    (b : Module.Basis m K E) (F : Submodule K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ∃ I : S.Ω → (Fin (Module.finrank K F) → m),
      (∀ J, MeasurableSet {ω | I ω = J}) ∧
      ∃ d : (Fin (Module.finrank K F) → m) → Module.Basis (Fin (Module.finrank K F)) K F,
        ∀ ω (z : (S.ϕ ω).Completion ⊗[K] F),
          ((ofBasis S E b).restrict F).norm ω z =
            ‖((d (I ω)).baseChange (S.ϕ ω).Completion).equivFun z‖ := by
  classical
  let c := Module.finBasis K F
  obtain ⟨I, hI, hs⟩ := exists_measurable_ofBasis_restrict_selected_coordinates b F c hfin
  let d (J : Fin (Module.finrank K F) → m) :
      Module.Basis (Fin (Module.finrank K F)) K F :=
    if hd : (Matrix.submatrix (fun i j ↦ b.equivFun (c j).val i) J id).det ≠ 0 then
      selectedSubspaceBasis b F c J hd else c
  refine ⟨I, hI, d, fun ω z ↦ ?_⟩
  obtain ⟨_, hd, hn⟩ := hs ω
  dsimp only [d]
  rw [dite_eq_left hd, selectedSubspaceBasis_completed_coordinates]
  exact hn z

/-- The actual determinant of every coordinate subspace restriction has
measurable rational evaluations, without countability hypotheses. -/
theorem ofBasis_restrict_determinant_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (F : Submodule K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ((ofBasis S E b).restrict F).determinant.IsMeasurable := by
  obtain ⟨I, hI, d, hcoord⟩ := exists_measurable_ofBasis_restrict_coordinate_bases b F hfin
  have harch : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
    intro ω hω
    exact False.elim (hω (hfin ω))
  exact ((ofBasis_isHermitian_of_all_finite b hfin harch).restrict F)
    |>.determinant_isMeasurable_of_finite_coordinate_bases I hI d hcoord

/-- The actual line dual of the coordinate restriction determinant is
measurable, including the determinant of a zero subspace. -/
theorem ofBasis_restrict_determinant_dual_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (F : Submodule K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ((ofBasis S E b).restrict F).determinant.dual.IsMeasurable :=
  (ofBasis_restrict_determinant_isMeasurable_of_all_finite b F hfin).dual_of_finrank_one
    (determinant_finrank (K := K) (E := F))

/-- A prescribed normalized maximal minor computes the actual determinant
volume of the original rational subspace basis, including the empty basis. -/
theorem ofBasis_restrict_determinant_norm_basis_eq_absValue_minor
    (b : Module.Basis m K E) (F : Submodule K E)
    (c : Module.Basis (Fin (Module.finrank K F)) K F)
    (I : Fin (Module.finrank K F) → m)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) (ω : S.Ω) :
    let A : Matrix m (Fin (Module.finrank K F)) K := fun i j ↦ b.equivFun (c j).val i
    ∀ (_hd : (A.submatrix I id).det ≠ 0),
      (A * (A.submatrix I id)⁻¹).submatrix I id = 1 →
      (∀ i j, (S.ϕ ω) ((A * (A.submatrix I id)⁻¹) i j) ≤ 1) →
      ((ofBasis S E b).restrict F).determinant.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] exteriorPower.ιMulti K _ c) =
          (S.ϕ ω) (A.submatrix I id).det := by
  intro A hd hid hB
  have harch : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
    intro ω hω
    exact False.elim (hω (hfin ω))
  let d := selectedSubspaceBasis b F c I hd
  have hξ := (ofBasis_isHermitian_of_all_finite b hfin harch).restrict F
  have hcoord := ofBasis_restrict_norm_eq_selectedSubspaceBasis b F c I ω (hfin ω) hd hid hB
  rw [hξ.determinant_norm_rational_eq_absValue_of_coordinates d ω hcoord,
    determinantCoordinateEquiv_ιMulti, Module.Basis.det_apply]
  congr 2
  ext i j
  exact selectedSubspaceBasis_repr_apply b F c I hd (c j) i

/-- Actual coordinate quotient determinants are measurable through the
produced annihilator restriction and genuine Hermitian determinant duality. -/
theorem ofBasis_quotient_determinant_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (F : Submodule K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ((ofBasis S E b).quotient F).determinant.IsMeasurable := by
  classical
  let ζ := (ofBasis S (Module.Dual K E) b.dualBasis).restrict F.dualAnnihilator
  let e := F.dualQuotEquivDualAnnihilator
  have hm : ζ.determinant.IsMeasurable :=
    ofBasis_restrict_determinant_isMeasurable_of_all_finite b.dualBasis F.dualAnnihilator hfin
  have hp : (ζ.pullback e.toLinearMap e.injective).determinant.IsMeasurable := by
    apply ζ.determinant_isMeasurable_of_completed_isometry
      (ζ.pullback e.toLinearMap e.injective) e.symm _ hm
    intro ω z
    rw [pullback_norm]
    change ζ.norm ω ((e.baseChange K (S.ϕ ω).Completion _ _)
      ((e.baseChange K (S.ϕ ω).Completion _ _).symm z)) = ζ.norm ω z
    rw [LinearEquiv.apply_symm_apply]
  have hd : ((ofBasis S E b).quotient F).dual.determinant.IsMeasurable := by
    rw [(ofBasis S E b).quotient_dual_annihilator F, ofBasis_dual_of_all_finite b hfin]
    exact hp
  have harch : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion := by
    intro ω hω
    exact False.elim (hω (hfin ω))
  have hξ := (ofBasis_isHermitian_of_all_finite b hfin harch).quotient F
  rw [hξ.determinant_dual] at hd
  have hdual := ((ofBasis S E b).quotient F).determinant.dual.isMeasurable_pullback_iff
    (determinantDualEquiv K (E ⧸ F)) |>.mp hd
  have hdd := hdual.dual_of_finrank_one (by
    rw [Subspace.dual_finrank_eq, determinant_finrank])
  have he := hdd.pullback (Module.Dual.eval K (⋀[K]^(Module.finrank K (E ⧸ F)) (E ⧸ F)))
    (Module.eval_apply_injective K)
  rw [dual_dual_pullback_eq_of_finrank_le_one _ (by rw [determinant_finrank])] at he
  exact he

/-- The genuine line dual of each actual coordinate quotient determinant
is measurable, with no base or ground-field countability hypothesis. -/
theorem ofBasis_quotient_determinant_dual_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (F : Submodule K E)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    ((ofBasis S E b).quotient F).determinant.dual.IsMeasurable :=
  (ofBasis_quotient_determinant_isMeasurable_of_all_finite b F hfin).dual_of_finrank_one
    (determinant_finrank (K := K) (E := E ⧸ F))

/-- Every literal native quotient of a coordinate restriction has a measurable
actual determinant, including arbitrary relative and equal endpoints. -/
theorem ofBasis_restrict_quotient_determinant_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (B : Submodule K E) (U : Submodule K B)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (((ofBasis S E b).restrict B).quotient U).determinant.IsMeasurable := by
  classical
  obtain ⟨I, hI, d, hcoord⟩ := exists_measurable_ofBasis_restrict_coordinate_bases b B hfin
  let ξ := (ofBasis S E b).restrict B
  let η (J : Fin (Module.finrank K B) → m) := ofBasis S B (d J)
  have hquot (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (B ⧸ U)) :
      (ξ.quotient U).norm ω z = ((η (I ω)).quotient U).norm ω z := by
    change ξ.quotientSeminorm U.mkQ U.mkQ_surjective ω z =
      (η (I ω)).quotientSeminorm U.mkQ U.mkQ_surjective ω z
    rw [quotientSeminorm_eq_sInf, quotientSeminorm_eq_sInf]
    have he : (ξ.norm ω : ((S.ϕ ω).Completion ⊗[K] B) → ℝ) = (η (I ω)).norm ω :=
      funext (hcoord ω)
    rw [he]
  have hdet (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K (B ⧸ U)) (B ⧸ U))) :
      (ξ.quotient U).determinant.norm ω z = ((η (I ω)).quotient U).determinant.norm ω z :=
    le_antisymm
      ((ξ.quotient U).determinant_norm_mono ((η (I ω)).quotient U) ω
        (fun z ↦ (hquot ω z).le) z)
      (((η (I ω)).quotient U).determinant_norm_mono (ξ.quotient U) ω
        (fun z ↦ (hquot ω z).ge) z)
  intro t
  have hp (J : Fin (Module.finrank K B) → m) : Measurable (fun ω ↦
      if I ω = J then ((η J).quotient U).determinant.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) else 0) :=
    ((ofBasis_quotient_determinant_isMeasurable_of_all_finite (d J) U hfin) t)
      |>.piecewise (hI J) measurable_const
  have hm : Measurable (fun ω ↦ ∑ J : Fin (Module.finrank K B) → m,
      if I ω = J then ((η J).quotient U).determinant.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] t) else 0) := by
    fun_prop
  convert hm using 1
  funext ω
  rw [hdet ω]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The genuine line dual of the determinant on the native completed fibres
of every coordinate restricted quotient is measurable. -/
theorem ofBasis_restrict_quotient_determinant_dual_isMeasurable_of_all_finite
    (b : Module.Basis m K E) (B : Submodule K E) (U : Submodule K B)
    (hfin : ∀ ω : S.Ω, ω ∈ S.Ωfin) :
    (((ofBasis S E b).restrict B).quotient U).determinant.dual.IsMeasurable :=
  (ofBasis_restrict_quotient_determinant_isMeasurable_of_all_finite b B U hfin)
    |>.dual_of_finrank_one (determinant_finrank (K := K) (E := B ⧸ U))

end

end ArakelovGeometry.NormFamily
