/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianScalarExtensionDual
public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionDomination

/-!
# Domination of Hermitian scalar extensions

The actual Hermitian extension contracts original rational vectors and their
dual vectors. The resulting primal and dual basis bounds yield an integrable
distance from the extended mixed basis family.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
    IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
  (hξ : ξ.IsHermitian hS)

/-- The actual Hermitian extension contracts every original rational vector.
At infinite places the norm is exactly preserved. -/
theorem hermitianScalarExtension_norm_one_tmul_le (x : S.ParameterSpaceExtension L)
    (e : E) :
    (hermitianScalarExtension ξ hS hL hξ).norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] e)) ≤
      ξ.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e) := by
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · exact (hermitianScalarExtension_norm_of_finite ξ hS hL hξ x hx
      ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] e))).trans_le
      ((ξ.injectiveScalarExtension_norm_le_scalarExtension_norm x _).trans
        (ξ.scalarExtension_norm_one_tmul_le x e))
  · let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    have ht := completedScalarExtensionEquiv_tmul E (S.ϕ x.base) x.abv x.restrict_eq
      (1 : x.abv.Completion) (1 : L) e
    simp only [map_one, one_mul] at ht
    have hn := hermitianScalarExtension_norm_tmul_of_infinite ξ hS hL hξ x hx
      (1 : x.abv.Completion) ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] e)
    rw [← ht, LinearEquiv.symm_apply_apply, norm_one, one_mul] at hn
    exact hn.le

/-- Canonical extension of a rational functional has no larger actual
Hermitian dual norm than the original rational functional. -/
theorem hermitianScalarExtension_dual_norm_baseChange_one_tmul_le
    (x : S.ParameterSpaceExtension L) (f : Module.Dual K E) :
    (hermitianScalarExtension ξ hS hL hξ).dual.norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] Module.Dual.baseChange L f) ≤
        ξ.dual.norm x.base ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] f) := by
  have he := hermitianScalarExtension_dual ξ hS hL hξ x
    ((1 : x.abv.Completion) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] f))
  simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    dualBaseChangeEquiv_tmul, one_smul] at he
  exact he.symm.trans_le
    (hermitianScalarExtension_norm_one_tmul_le ξ.dual hS hL hξ.dual x f)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K E)

/-- Original primal and dual basis bounds control the actual Hermitian
extension at every extending place. The rank term is supported at infinity. -/
theorem hermitianScalarExtension_localDist_ofBasisMixed_le
    (x : S.ParameterSpaceExtension L) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, ξ.norm x.base ((b.baseChange (S.ϕ x.base).Completion) i) ≤ Real.exp A)
    (hb : ∀ i, ξ.dual.norm x.base
      ((1 : (S.ϕ x.base).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp B) :
    (hermitianScalarExtension ξ hS hL hξ).localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x ≤
        A + B + S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) x.base := by
  let η := hermitianScalarExtension ξ hS hL hξ
  let R := S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ))
  have hR : 0 ≤ R x.base :=
    Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _) _
  have ha' : ∀ i, η.norm x (((b.baseChange L).baseChange x.abv.Completion) i) ≤
      Real.exp A := by
    intro i
    rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
    apply (hermitianScalarExtension_norm_one_tmul_le ξ hS hL hξ x (b i)).trans
    simpa only [Module.Basis.baseChange_apply] using ha i
  have hb' : ∀ i, η.dual.norm x
      ((1 : x.abv.Completion) ⊗ₜ[L] (b.baseChange L).dualBasis i) ≤ Real.exp B := by
    intro i
    rw [Module.Basis.dualBasis_baseChange]
    exact (hermitianScalarExtension_dual_norm_baseChange_one_tmul_le
      ξ hS hL hξ x (b.dualBasis i)).trans (hb i)
  have hRI : (S.algebraicExtension L).Ωinf.indicator
      (fun _ => Real.log (Fintype.card ι : ℝ)) x = R x.base := by
    by_cases hx : x.base ∈ S.Ωinf
    · exact (Set.indicator_of_mem ((scalarExtension_mem_Ωinf_iff x).mpr hx)
        (fun _ => Real.log (Fintype.card ι : ℝ))).trans
          (Set.indicator_of_mem hx (fun _ => Real.log (Fintype.card ι : ℝ))).symm
    · exact (Set.indicator_of_notMem
        (fun h => hx ((scalarExtension_mem_Ωinf_iff x).mp h))
        (fun _ => Real.log (Fintype.card ι : ℝ))).trans (Set.indicator_of_notMem hx _).symm
  apply (η.localDist_le_iff_norm_le
    (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)) x
    (add_nonneg (add_nonneg hA hB) hR)).mpr
  intro z
  constructor
  · exact (norm_le_mul_of_basis_norm_le (S := S.algebraicExtension L)
      (b.baseChange L) η (hermitianScalarExtension_isUltrametric ξ hS hL hξ)
      x (Real.exp_pos _).le ha' z).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        ((ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E)
          (b.baseChange L)).norm_nonneg x z))
  · have hq := ofBasisMixed_norm_le_mul_of_dual_basis_norm_le
      (S := S.algebraicExtension L) (b.baseChange L) η x (Real.exp_pos _).le hb' z
    rw [hRI] at hq
    calc
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)).norm x z ≤
          Real.exp (R x.base) * Real.exp B * η.norm x z := hq
      _ = Real.exp (B + R x.base) * η.norm x z := by
        rw [← Real.exp_add, add_comm (R x.base)]
      _ ≤ Real.exp (A + B + R x.base) * η.norm x z :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (η.norm_nonneg x z)

omit [DecidableEq ι] in
/-- Domination of the original Hermitian family gives an integrable
basis-distance envelope on the actual algebraically extended curve. -/
theorem IsDominated.hermitianScalarExtension_localDist_ofBasisMixed
    (hd : ξ.IsDominated) :
    HasIntegrableBounds ((hermitianScalarExtension ξ hS hL hξ).localDist
      (ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)))
        (S.algebraicExtension L).v := by
  classical
  let η := hermitianScalarExtension ξ hS hL hξ
  let η₀ := ofBasisMixed (S.algebraicExtension L) (L ⊗[K] E) (b.baseChange L)
  change HasIntegrableBounds (η.localDist η₀) (S.algebraicExtension L).v
  obtain ⟨A, hA, hA0, ha⟩ := IsUpperDominated.exists_basis_norm_bound (ξ := ξ) b hd.1
  obtain ⟨B, hB, hB0, hb⟩ :=
    IsUpperDominated.exists_basis_norm_bound (ξ := ξ.dual) b.dualBasis hd.2
  have hb' : ∀ᵐ ω ∂S.v, ∀ i,
      ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp (B ω) := by
    simpa only [Module.Basis.baseChange_apply] using hb
  let R := S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr
      (integrableOn_const (S.v_Ωinf_lt_top_of_isRCLike hS).ne)
  have hproj : MeasurePreserving (fun x : (S.algebraicExtension L).Ω => x.base)
      (S.algebraicExtension L).v S.v :=
    ⟨AdelicStructure.Algebraic.measurable_proj_projective S L,
      AdelicStructure.Algebraic.map_measure_proj S L⟩
  let C : S.Ω → ℝ := fun ω => A ω + B ω + R ω
  have hC : Integrable C S.v := (hA.add hB).add hR
  have hi : Integrable (fun x : (S.algebraicExtension L).Ω => C x.base)
      (S.algebraicExtension L).v :=
    AdelicStructure.Algebraic.integrable_comp_proj_measure S L hC
  have hbound : ∀ᵐ x ∂(S.algebraicExtension L).v, η.localDist η₀ x ≤ C x.base := by
    filter_upwards [hproj.quasiMeasurePreserving.ae ha,
      hproj.quasiMeasurePreserving.ae hb'] with x hax hbx
    exact hermitianScalarExtension_localDist_ofBasisMixed_le ξ hS hL hξ b x
      (hA0 x.base) (hB0 x.base) hax hbx
  have hupper : HasIntegrableUpperBound (η.localDist η₀) (S.algebraicExtension L).v :=
    ⟨fun x => C x.base, hi, hbound⟩
  have hlower : HasIntegrableLowerBound (η.localDist η₀) (S.algebraicExtension L).v :=
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (η.localDist_nonneg η₀)⟩
  exact ⟨hupper, hlower⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The actual Hermitian scalar extension of a dominated Hermitian family
is strongly dominated. The normalizations imply the required finite measure. -/
theorem IsDominated.hermitianScalarExtension_isStronglyDominated
    (hd : ξ.IsDominated) :
    (hermitianScalarExtension ξ hS hL hξ).IsStronglyDominated := by
  classical
  let b := Module.finBasis K E
  have hfinL : (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf < ⊤ := by
    rw [scalarExtension_measure_Ωinf]
    exact S.v_Ωinf_lt_top_of_isRCLike hS
  exact (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    (b.baseChange L) (hermitianScalarExtension ξ hS hL hξ) hfinL).mpr
      (IsDominated.hermitianScalarExtension_localDist_ofBasisMixed ξ hS hL hξ b hd)

omit [Fintype ι] [DecidableEq ι] in
/-- The Hermitian-extension conclusion of Remark 4.1.14, for the actual
completed norm family and explicit usual Archimedean normalizations. -/
theorem IsDominated.hermitianScalarExtension (hd : ξ.IsDominated) :
    (hermitianScalarExtension ξ hS hL hξ).IsDominated :=
  (IsDominated.hermitianScalarExtension_isStronglyDominated ξ hS hL hξ hd).isDominated

end ArakelovGeometry.NormFamily

end
