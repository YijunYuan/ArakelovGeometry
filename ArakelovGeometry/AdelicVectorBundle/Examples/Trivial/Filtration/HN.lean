/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Basic
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Inverse

import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.FlagUniqueness
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# The actual HN filtration of a trivial-place ultrametric norm

The strict flag is produced from the literal balls. Its factors carry the
canonical restriction followed by quotient norms. Completed tensor naturality
controls every quotient lift before actual general HN uniqueness is used.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u w w'

variable {K : Type u} [Field K] {E : Type w} [AddCommGroup E] [Module K E]
  {G : Type w'} [AddCommGroup G] [Module K G]

namespace AdelicStructure

open Classical in
/-- The canonical trivial completed tensor identification is natural for
every rational linear map and every completed vector. -/
theorem trivialCompletedTensorEquiv_baseChange (π : E →ₗ[K] G)
    (z : (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion ⊗[K] E) :
    trivialCompletedTensorEquiv K G
      (π.baseChange (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion z) =
      π (trivialCompletedTensorEquiv K E z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp only [LinearMap.baseChange_tmul, trivialCompletedTensorEquiv_tmul,
      map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end AdelicStructure

namespace NormFamily

open AdelicStructure

open Classical in
/-- A norm profile on the nonzero images of a rational map holds on all
completed vectors having nonzero image. No isometry is assumed. -/
theorem norm_eq_const_of_trivialSeminorm_eq_const_on_nonzero_image
    (ξ : NormFamily (singleTrivialPlace K) E) (π : E →ₗ[K] G) {c : ℝ}
    (h : ∀ x, π x ≠ 0 → ξ.trivialSeminorm x = c)
    (ω : (singleTrivialPlace K).Ω)
    (z : ((singleTrivialPlace K).ϕ ω).Completion ⊗[K] E)
    (hz : π.baseChange ((singleTrivialPlace K).ϕ ω).Completion z ≠ 0) :
    ξ.norm ω z = c := by
  cases ω
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  change C ⊗[K] E at z
  change π.baseChange C z ≠ 0 at hz
  have hn : π (trivialCompletedTensorEquiv K E z) ≠ 0 := by
    rw [← trivialCompletedTensorEquiv_baseChange]
    exact (trivialCompletedTensorEquiv K G).map_eq_zero_iff.not.mpr hz
  have he := h _ hn
  change ξ.norm PUnit.unit ((trivialCompletedTensorEquiv K E).symm
    (trivialCompletedTensorEquiv K E z)) = c at he
  simpa only [LinearEquiv.symm_apply_apply] using he

open Classical in
/-- The genuine quotient infimum is constant when the original norm is
constant on every vector whose quotient image is nonzero. -/
theorem trivialSeminorm_pushforward_eq_const_on_nonzero_image
    [FiniteDimensional K E] (ξ : NormFamily (singleTrivialPlace K) E)
    (π : E →ₗ[K] G) (hπ : Function.Surjective π) {c : ℝ}
    (h : ∀ x, π x ≠ 0 → ξ.trivialSeminorm x = c)
    (y : G) (hy : y ≠ 0) : (ξ.pushforward π hπ).trivialSeminorm y = c := by
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let z : C ⊗[K] G := (1 : C) ⊗ₜ[K] y
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  let qG : Seminorm C (C ⊗[K] G) := (ξ.pushforward π hπ).norm PUnit.unit
  have hz : z ≠ 0 := by
    intro hz
    have he := congrArg (trivialCompletedTensorEquiv K G) hz
    change trivialCompletedTensorEquiv K G ((1 : C) ⊗ₜ[K] y) =
      trivialCompletedTensorEquiv K G 0 at he
    rw [trivialCompletedTensorEquiv_one_tmul, map_zero] at he
    exact hy he
  have hq : ∀ x : C ⊗[K] E, π.baseChange C x = z → q x = c := by
    intro x hx
    exact ξ.norm_eq_const_of_trivialSeminorm_eq_const_on_nonzero_image π h _ x
      (hx ▸ hz)
  change qG z = c
  apply le_antisymm
  · obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective C hπ z
    calc
      _ ≤ q x := by
        have hl := ξ.pushforward_norm_le π hπ PUnit.unit x
        change qG (π.baseChange C x) ≤ q x at hl
        rw [hx] at hl
        exact hl
      _ = c := hq x hx
  · apply (ξ.le_quotientSeminorm_iff π hπ PUnit.unit z c).mpr
    intro x hx
    change C ⊗[K] E at x
    change π.baseChange C x = z at hx
    exact (hq x hx).ge

open Classical in
/-- A vector at an included ball endpoint but outside the literal union
of strictly higher balls has exactly the endpoint's norm. -/
theorem trivialSeminorm_eq_exp_neg_of_ball_difference
    (ξ : NormFamily (singleTrivialPlace K) E) [hξ : ξ.IsUltrametric]
    (b : ℝ) (x : E) (hx : x ∈ ξ.trivialFiltration b)
    (hn : x ∉ ⨆ s : {s : ℝ // b < s}, ξ.trivialFiltration s.val) :
    ξ.trivialSeminorm x = Real.exp (-b) := by
  apply le_antisymm hx
  by_contra h
  have hx0 : x ≠ 0 := by
    intro he
    exact hn (he ▸ Submodule.zero_mem _)
  have hp : 0 < ξ.trivialSeminorm x := by
    rw [trivialSeminorm_apply]
    exact ξ.norm_rational_pos PUnit.unit hx0
  have hl := Real.log_lt_log hp (lt_of_not_ge h)
  rw [Real.log_exp] at hl
  have hb : b < -Real.log (ξ.trivialSeminorm x) := by linarith
  have hm : x ∈ ξ.trivialFiltration (-Real.log (ξ.trivialSeminorm x)) :=
    (ξ.mem_trivialFiltration_iff_le_neg_log _ x hx0).mpr le_rfl
  exact hn ((le_iSup (fun s : {s : ℝ // b < s} ↦ ξ.trivialFiltration s.val)
    ⟨_, hb⟩) hm)

open Classical in
/-- An actual restriction-then-quotient at consecutive ball levels has
constant nonzero rational norm. Its norm is proved from every completed lift. -/
theorem trivialSeminorm_subquotient_eq_exp_neg_of_ball_endpoints
    [FiniteDimensional K E] (ξ : NormFamily (singleTrivialPlace K) E)
    [hξ : ξ.IsUltrametric] (A B : Submodule K E) (b : ℝ)
    (hB : ξ.trivialFiltration b = B)
    (hA : (⨆ s : {s : ℝ // b < s}, ξ.trivialFiltration s.val) = A)
    (y : B ⧸ A.comap B.subtype) (hy : y ≠ 0) :
    ((ξ.restrict B).quotient (A.comap B.subtype)).trivialSeminorm y =
      Real.exp (-b) := by
  apply (ξ.restrict B).trivialSeminorm_pushforward_eq_const_on_nonzero_image
    (A.comap B.subtype).mkQ (A.comap B.subtype).mkQ_surjective _ y hy
  intro x hx
  have hxn : (x : E) ∉ A := by
    intro hm
    exact hx ((Submodule.Quotient.mk_eq_zero (A.comap B.subtype)).mpr hm)
  have hn : (x : E) ∉ ⨆ s : {s : ℝ // b < s}, ξ.trivialFiltration s.val := by
    rw [hA]
    exact hxn
  have hm : (x : E) ∈ ξ.trivialFiltration b := by
    rw [hB]
    exact x.property
  have he := ξ.trivialSeminorm_eq_exp_neg_of_ball_difference b x hm hn
  rw [trivialSeminorm_apply] at he ⊢
  let C := (AbsoluteValue.trivial : AbsoluteValue K ℝ).Completion
  let q : Seminorm C (C ⊗[K] E) := ξ.norm PUnit.unit
  change q ((1 : C) ⊗ₜ[K] (x : E)) = Real.exp (-b) at he
  change q (B.subtype.baseChange C ((1 : C) ⊗ₜ[K] x)) = Real.exp (-b)
  rw [LinearMap.baseChange_tmul]
  exact he

end NormFamily

namespace AdelicVectorBundle

open AdelicStructure

variable [FiniteDimensional K E]
  (V : AdelicVectorBundle.{w} (singleTrivialPlace K))
  [hS : (singleTrivialPlace K).HasMeasurableBase]
  [hN : (singleTrivialPlace K).IsArchimedeanNormalized]

open Classical in
/-- The actual literal balls produce a full strict flag whose canonical
factors are constant, semistable, and have their genuine jumps as means. -/
theorem exists_strictMono_trivialFiltration_semistableFlag
    [hV : V.toNormFamily.IsUltrametric] :
    ∃ (n : ℕ) (U : Fin (n + 1) → Submodule K V) (b : Fin n → ℝ),
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ ∧ StrictAnti b ∧
      (∀ t, V.toNormFamily.trivialFiltration t =
        ⨆ (i : Fin n) (_ : t ≤ b i), U i.succ) ∧
      (∀ (i : Fin n) x, x ≠ 0 →
        (V.flagQuotientOfMeasurableBase U i).toNormFamily.trivialSeminorm x =
          Real.exp (-b i)) ∧
      (∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).IsSemistable) ∧
      (∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).minimalSlope =
        (b i : EReal)) ∧
      (∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).modifiedSlope = b i) := by
  obtain ⟨n, U, b, hU, hz, ht, _, hb, _, hlevel, hright, hrec⟩ :=
    V.toNormFamily.exists_strictMono_flag_and_jumps_trivialFiltration
  have hc : ∀ (i : Fin n) x, x ≠ 0 →
      (V.flagQuotientOfMeasurableBase U i).toNormFamily.trivialSeminorm x =
        Real.exp (-b i) := by
    intro i x hx
    exact V.toNormFamily.trivialSeminorm_subquotient_eq_exp_neg_of_ball_endpoints
       (U i.castSucc) (U i.succ) (b i) (hlevel i) (hright i) x hx
  have hr : ∀ i : Fin n,
      0 < Module.finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) := by
    intro i
    rw [Submodule.finrank_quotient,
      (Submodule.comapSubtypeEquivOfLe (hU Fin.castSucc_lt_succ).le).finrank_eq]
    exact Nat.sub_pos_of_lt (Submodule.finrank_lt_finrank_of_lt (hU Fin.castSucc_lt_succ))
  have hs : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).IsSemistable := by
    intro i
    exact (V.flagQuotientOfMeasurableBase U i).isSemistable_of_trivialSeminorm_eq_const
      (Real.exp_pos _) (hc i) (hr i)
  have hm : ∀ i : Fin n, (V.flagQuotientOfMeasurableBase U i).minimalSlope =
      (b i : EReal) := by
    intro i
    have he := minimalSlope_eq_neg_log_of_trivialSeminorm_eq_const
      (V.flagQuotientOfMeasurableBase U i)
        (Real.exp_pos _) (hc i) (hr i)
    simpa only [Real.log_exp, neg_neg] using he
  refine ⟨n, U, b, hU, hz, ht, hb, hrec, hc, hs, hm, ?_⟩
  intro i
  have he := ((V.flagQuotientOfMeasurableBase U i).isSemistable_iff_modifiedSlope_eq_minimalSlope
    (hr i)).mp (hs i)
  exact EReal.coe_eq_coe_iff.mp (he.trans (hm i))

open Classical in
/-- General HN uniqueness identifies the actual ultrametric bundle's
filtration with its literal closed balls, in every rank. -/
theorem generalHNFiltration_eq_trivialFiltration [hV : V.toNormFamily.IsUltrametric]
    (t : ℝ) :
    V.generalHNFiltration t = V.toNormFamily.trivialFiltration t := by
  obtain ⟨n, U, b, hU, hz, ht, hb, hrec, _, hs, _, hm⟩ :=
    V.exists_strictMono_trivialFiltration_semistableFlag
  have hanti : StrictAnti (fun i : Fin n ↦
      (V.flagQuotientOfMeasurableBase U i).modifiedSlope) := by
    simpa only [hm] using hb
  rw [V.generalHNFiltration_eq_of_semistableFlag U hU hz ht (hsemi := hs) hanti t]
  simp only [hm]
  exact (hrec t).symm

open Classical in
/-- The actual adelic bundle constructed from a source real filtration
has exactly that original general HN filtration. -/
theorem generalHNFiltration_ofTrivialFiltration (F : ℝ → Submodule K E)
    (hF : Antitone F) (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t) (t : ℝ) :
    (ofTrivialFiltration F hF hbot htop hleft).generalHNFiltration t = F t := by
  rw [(ofTrivialFiltration F hF hbot htop hleft).generalHNFiltration_eq_trivialFiltration
    (hV := (NormFamily.ofTrivialFiltration_isUltrametric F hF hbot htop hleft)) t]
  exact NormFamily.trivialFiltration_ofTrivialFiltration F hF hbot htop hleft t

end AdelicVectorBundle

end

end ArakelovGeometry
