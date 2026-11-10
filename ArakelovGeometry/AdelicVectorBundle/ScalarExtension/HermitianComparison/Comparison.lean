/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Hermitian.Basic
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicVectorBundle.ScalarExtension.Domination.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Ordinary and Hermitian scalar-extension comparison

The two-vector real/imaginary decomposition gives the dimension-independent
factor `√2` between the projective and Hermitian norms on completed fibres.
-/

@[expose] public section

open scoped TensorProduct
open MeasureTheory

noncomputable section

namespace ArakelovGeometry

variable {k l V ι : Type*} [RCLike k] [RCLike l] [NormedAlgebra k l]
  [NormedAddCommGroup V] [InnerProductSpace k V] [Fintype ι]
  (b : OrthonormalBasis ι k V)

/-- Real-coordinate part of an extended vector, as an actual base vector. -/
def hermitianScalarExtensionRealPart (z : l ⊗[k] V) : V :=
  b.repr.symm (WithLp.toLp 2 fun i =>
    (RCLike.re (hermitianScalarExtensionCoordinates b z i) : k))

/-- Imaginary-coordinate part of an extended vector, as an actual base vector. -/
def hermitianScalarExtensionImagPart (z : l ⊗[k] V) : V :=
  b.repr.symm (WithLp.toLp 2 fun i =>
    (RCLike.im (hermitianScalarExtensionCoordinates b z i) : k))

/-- Every extended vector has a two-term decomposition over real coordinates.
This works for arbitrary isometric `RCLike` field embeddings. -/
theorem hermitianScalarExtension_real_imag_decomposition (z : l ⊗[k] V) :
    z = (1 : l) ⊗ₜ[k] hermitianScalarExtensionRealPart b z +
      (RCLike.I : l) ⊗ₜ[k] hermitianScalarExtensionImagPart b z := by
  apply (hermitianScalarExtensionCoordinates b).injective
  ext i
  simp only [map_add, hermitianScalarExtensionCoordinates_tmul,
    hermitianScalarExtensionRealPart, hermitianScalarExtensionImagPart,
    LinearIsometryEquiv.apply_symm_apply, one_mul, PiLp.add_apply]
  change hermitianScalarExtensionCoordinates b z i =
    algebraMap k l (algebraMap ℝ k (RCLike.re
      (hermitianScalarExtensionCoordinates b z i))) +
    RCLike.I * algebraMap k l (algebraMap ℝ k (RCLike.im
      (hermitianScalarExtensionCoordinates b z i)))
  rw [normedAlgebra_map_ofReal, normedAlgebra_map_ofReal, mul_comm]
  exact (RCLike.re_add_im _).symm

/-- The real and imaginary base vectors have the Hermitian square-norm sum. -/
theorem hermitianScalarExtension_real_imag_norm_sq (z : l ⊗[k] V) :
    ‖hermitianScalarExtensionRealPart b z‖ ^ 2 +
      ‖hermitianScalarExtensionImagPart b z‖ ^ 2 =
        hermitianScalarExtensionSeminorm b z ^ 2 := by
  rw [hermitianScalarExtensionRealPart, hermitianScalarExtensionImagPart,
    b.repr.symm.norm_map, b.repr.symm.norm_map]
  change ‖WithLp.toLp 2 (fun i =>
    (RCLike.re (hermitianScalarExtensionCoordinates b z i) : k))‖ ^ 2 +
    ‖WithLp.toLp 2 (fun i =>
    (RCLike.im (hermitianScalarExtensionCoordinates b z i) : k))‖ ^ 2 =
      ‖hermitianScalarExtensionCoordinates b z‖ ^ 2
  simp only [EuclideanSpace.norm_sq_eq, RCLike.norm_ofReal, sq_abs,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.norm_sq_eq_def]
  ring

/-- The exact Hermitian extension is bounded by the defining projective infimum. -/
theorem hermitianScalarExtensionSeminorm_le_projective :
    hermitianScalarExtensionSeminorm b ≤
      scalarExtensionProjectiveSeminorm (k := k) (L := l) (E := V) := by
  apply le_scalarExtensionProjectiveSeminorm
  intro x
  simp only [hermitianScalarExtensionSeminorm_tmul, norm_one, one_mul, le_refl]

/-- The two-vector decomposition gives the dimension-independent factor `√2`. -/
theorem scalarExtensionProjectiveSeminorm_le_sqrt_two_mul_hermitian
    (z : l ⊗[k] V) :
    scalarExtensionProjectiveSeminorm z ≤
      Real.sqrt 2 * hermitianScalarExtensionSeminorm b z := by
  have hI : ‖(RCLike.I : l)‖ ≤ 1 := by
    rw [RCLike.norm_I]
    split <;> norm_num
  have hsum : scalarExtensionProjectiveSeminorm z ≤
      ‖hermitianScalarExtensionRealPart b z‖ +
        ‖hermitianScalarExtensionImagPart b z‖ := by
    conv_lhs => rw [hermitianScalarExtension_real_imag_decomposition b z]
    exact (map_add_le_add scalarExtensionProjectiveSeminorm _ _).trans
      (add_le_add
        (by simpa only [norm_one, one_mul] using
          (scalarExtensionProjectiveSeminorm_tmul_le (1 : l)
            (hermitianScalarExtensionRealPart b z)))
        ((scalarExtensionProjectiveSeminorm_tmul_le (RCLike.I : l)
          (hermitianScalarExtensionImagPart b z)).trans
          (mul_le_of_le_one_left (norm_nonneg _) hI)))
  apply hsum.trans
  have hsquare := hermitianScalarExtension_real_imag_norm_sq b z
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdiff := sq_nonneg
    (‖hermitianScalarExtensionRealPart b z‖ - ‖hermitianScalarExtensionImagPart b z‖)
  have hnonneg := mul_nonneg (Real.sqrt_nonneg 2)
    (apply_nonneg (hermitianScalarExtensionSeminorm (L := l) b) z)
  nlinarith [norm_nonneg (hermitianScalarExtensionRealPart b z),
    norm_nonneg (hermitianScalarExtensionImagPart b z)]

namespace NormFamily

universe u v w wE

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {L : Type w} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  {E : Type wE} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hL : ∀ x ∈ (S.algebraicExtension L).Ωinf,
    IsRCLikeNormedField ((S.algebraicExtension L).ϕ x).Completion)
  (hξ : ξ.IsHermitian hS)

/-- Ordinary and Hermitian scalar extension agree on every finite completed fibre. -/
theorem scalarExtension_norm_eq_hermitian_of_finite (x : S.ParameterSpaceExtension L)
    (hx : x ∈ (S.algebraicExtension L).Ωfin)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (ξ.scalarExtension (L := L)).norm x z =
      (hermitianScalarExtension ξ hS hL hξ).norm x z := by
  exact (ξ.scalarExtension_norm_of_mem_Ωfin x
    ((AdelicStructure.mem_Ωfin_algebraicExtension_iff x).mp hx) z).trans
      (hermitianScalarExtension_norm_of_finite ξ hS hL hξ x hx z).symm

/-- On every infinite completed fibre, the actual norms satisfy `H ≤ π ≤ √2 H`. -/
theorem scalarExtension_hermitian_norm_comparison_of_infinite
    (x : S.ParameterSpaceExtension L) (hx : x ∈ (S.algebraicExtension L).Ωinf)
    (z : x.abv.Completion ⊗[L] (L ⊗[K] E)) :
    (hermitianScalarExtension ξ hS hL hξ).norm x z ≤
        (ξ.scalarExtension (L := L)).norm x z ∧
      (ξ.scalarExtension (L := L)).norm x z ≤
        Real.sqrt 2 * (hermitianScalarExtension ξ hS hL hξ).norm x z := by
  have hbase := (scalarExtension_mem_Ωinf_iff x).mp hx
  let := hS x.base hbase
  let := IsRCLikeNormedField.rclike (S.ϕ x.base).Completion
  let : IsRCLikeNormedField x.abv.Completion := hL x hx
  let := IsRCLikeNormedField.rclike x.abv.Completion
  let : NormedAlgebra (S.ϕ x.base).Completion x.abv.Completion :=
    AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := ξ.fibreNormedAddCommGroup x.base
  let := ξ.fibreNormedSpace x.base
  let := hξ.fibreInnerProductSpace x.base hbase
  let b := stdOrthonormalBasis (S.ϕ x.base).Completion ((S.ϕ x.base).Completion ⊗[K] E)
  let y := completedScalarExtensionEquiv E (S.ϕ x.base) x.abv x.restrict_eq z
  rw [hermitianScalarExtension_norm_of_infinite ξ hS hL hξ x hx z,
    ξ.scalarExtension_norm_of_not_mem_Ωfin x hbase z]
  change hermitianScalarExtensionSeminorm b y ≤ scalarExtensionProjectiveSeminorm y ∧
    scalarExtensionProjectiveSeminorm y ≤ Real.sqrt 2 * hermitianScalarExtensionSeminorm b y
  exact ⟨hermitianScalarExtensionSeminorm_le_projective b y,
    scalarExtensionProjectiveSeminorm_le_sqrt_two_mul_hermitian b y⟩

/-- The Hermitian extension is bounded by the ordinary extension at every place. -/
theorem hermitianScalarExtension_le_scalarExtension :
    hermitianScalarExtension ξ hS hL hξ ≤ ξ.scalarExtension (L := L) := by
  intro x z
  change S.ParameterSpaceExtension L at x
  change x.abv.Completion ⊗[L] (L ⊗[K] E) at z
  by_cases hx : x ∈ (S.algebraicExtension L).Ωfin
  · exact (scalarExtension_norm_eq_hermitian_of_finite ξ hS hL hξ x hx z).symm.le
  · exact (scalarExtension_hermitian_norm_comparison_of_infinite ξ hS hL hξ x hx z).1

/-- The two scalar extensions have zero distance at every finite place. -/
theorem scalarExtension_localDist_hermitian_eq_zero_of_finite
    (x : S.ParameterSpaceExtension L) (hx : x ∈ (S.algebraicExtension L).Ωfin) :
    (ξ.scalarExtension (L := L)).localDist (hermitianScalarExtension ξ hS hL hξ) x = 0 := by
  apply ((ξ.scalarExtension (L := L)).localDist_eq_zero_iff
    (hermitianScalarExtension ξ hS hL hξ) x).mpr
  ext z
  exact scalarExtension_norm_eq_hermitian_of_finite ξ hS hL hξ x hx z

/-- The sharp source upper bound is one half of `log 2` at infinity and zero elsewhere. -/
theorem scalarExtension_localDist_hermitian_le (x : S.ParameterSpaceExtension L) :
    (ξ.scalarExtension (L := L)).localDist (hermitianScalarExtension ξ hS hL hξ) x ≤
      (S.algebraicExtension L).Ωinf.indicator (fun _ => (1 / 2 : ℝ) * Real.log 2) x := by
  classical
  have hlog : 0 ≤ (1 / 2 : ℝ) * Real.log 2 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  by_cases hx : x ∈ (S.algebraicExtension L).Ωinf
  · have hbound : (ξ.scalarExtension (L := L)).localDist
        (hermitianScalarExtension ξ hS hL hξ) x ≤ (1 / 2 : ℝ) * Real.log 2 := by
      apply ((ξ.scalarExtension (L := L)).localDist_le_iff_norm_le
        (hermitianScalarExtension ξ hS hL hξ) x hlog).mpr
      intro z
      have h := scalarExtension_hermitian_norm_comparison_of_infinite ξ hS hL hξ x hx z
      have hsqrt : Real.sqrt 2 = Real.exp ((1 / 2 : ℝ) * Real.log 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), mul_comm]
      refine ⟨?_, ?_⟩
      · exact h.2.trans_eq (congrArg (fun c => c *
          (hermitianScalarExtension ξ hS hL hξ).norm x z) hsqrt)
      · exact h.1.trans
          (le_mul_of_one_le_left ((ξ.scalarExtension (L := L)).norm_nonneg x z)
            (Real.one_le_exp_iff.mpr hlog))
    exact hbound.trans_eq (Set.indicator_of_mem hx
      (fun _ : (S.algebraicExtension L).Ω => (1 / 2 : ℝ) * Real.log 2)).symm
  · have hfin : x ∈ (S.algebraicExtension L).Ωfin := not_not.mp hx
    exact (scalarExtension_localDist_hermitian_eq_zero_of_finite ξ hS hL hξ x hfin).le.trans_eq
      (Set.indicator_of_notMem hx
        (fun _ : (S.algebraicExtension L).Ω => (1 / 2 : ℝ) * Real.log 2)).symm

/-- The zero-rank case has exactly zero distance at every extending place. -/
theorem scalarExtension_localDist_hermitian_eq_zero_of_finrank_zero
    (hrank : Module.finrank K E = 0) (x : S.ParameterSpaceExtension L) :
    (ξ.scalarExtension (L := L)).localDist (hermitianScalarExtension ξ hS hL hξ) x = 0 := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hrank
  exact (ξ.scalarExtension (L := L)).localDist_eq_zero_of_subsingleton
    (hermitianScalarExtension ξ hS hL hξ) x

/-- The explicit half-log-two correction gives actual integrable distance envelopes. -/
theorem scalarExtension_localDist_hermitian_hasIntegrableBounds
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds ((ξ.scalarExtension (L := L)).localDist
      (hermitianScalarExtension ξ hS hL hξ)) (S.algebraicExtension L).v := by
  have hfinL : (S.algebraicExtension L).v (S.algebraicExtension L).Ωinf < ⊤ := by
    rw [scalarExtension_measure_Ωinf]
    exact hfin
  refine ⟨⟨(S.algebraicExtension L).Ωinf.indicator
    (fun _ => (1 / 2 : ℝ) * Real.log 2), ?_,
    Filter.Eventually.of_forall (scalarExtension_localDist_hermitian_le ξ hS hL hξ)⟩,
    ⟨0, integrable_zero _ _ _, Filter.Eventually.of_forall ?_⟩⟩
  · exact (integrable_indicator_iff (S.algebraicExtension L).measurableSet_Ωinf).mpr
      (integrableOn_const hfinL.ne)
  · intro x
    exact (ξ.scalarExtension (L := L)).localDist_nonneg _ x

end NormFamily

end ArakelovGeometry

end
