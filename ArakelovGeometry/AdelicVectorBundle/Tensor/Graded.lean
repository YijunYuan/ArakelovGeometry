/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.TensorGraded
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual norms and contractions on filtration grades

Every grade carries the restriction followed by the quotient of the original
norm family. The canonical graded map descends a completed contraction by
comparing every completed lift, including at trivially valued places.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {V : Type w'} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The actual grade norm: first restrict the ambient family, then take its
canonical quotient by the strict right limit inside the step. -/
noncomputable def filtrationGraded (ξ : NormFamily S E)
    (F : ℝ → Submodule K E) (t : ℝ) :
    NormFamily S (Submodule.FiltrationGraded F t) :=
  (ξ.restrict (F t)).quotient
    ((Submodule.filtrationRightLimit F t).comap (F t).subtype)

/-- Actual grades of Hermitian norm families are Hermitian, also in rank zero. -/
theorem IsHermitian.filtrationGraded {ξ : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hN) (F : ℝ → Submodule K E) (t : ℝ) :
    (ξ.filtrationGraded F t).IsHermitian hN :=
  (hξ.restrict (F t)).quotient _

/-- Every completed lift bounds the actual grade norm. -/
theorem filtrationGraded_norm_mk_le (ξ : NormFamily S E)
    (F : ℝ → Submodule K E) (t : ℝ) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] F t) :
    (ξ.filtrationGraded F t).norm ω
        ((Submodule.filtrationGradedMk F t).baseChange (S.ϕ ω).Completion x) ≤
      (ξ.restrict (F t)).norm ω x :=
  (ξ.restrict (F t)).quotient_norm_mk_le _ ω x

/-- A commuting pair of quotient maps descends a completed contraction. -/
theorem quotientMap_norm_le (ξ : NormFamily S E) (η : NormFamily S V)
    (f : E →ₗ[K] V) (U : Submodule K E) (T : Submodule K V)
    (g : (E ⧸ U) →ₗ[K] (V ⧸ T)) (hc : g.comp U.mkQ = T.mkQ.comp f)
    (ω : S.Ω)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⧸ U)) :
    (η.quotient T).norm ω (g.baseChange (S.ϕ ω).Completion z) ≤
      (ξ.quotient U).norm ω z := by
  apply (ξ.le_quotientSeminorm_iff U.mkQ U.mkQ_surjective ω z _).mpr
  intro x hx
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [← hx, he]
  exact (η.quotient_norm_mk_le T ω _).trans (hf x)

/-- A threshold-preserving contraction induces A5's canonical graded map as a
contraction on every completed vector for the actual subquotient norms. -/
theorem filtrationGradedMap_norm_le (ξ : NormFamily S E) (η : NormFamily S V)
    {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}
    (f : E →ₗ[K] V) (hf : ∀ t, F t ≤ (G t).comap f) (t : ℝ) (ω : S.Ω)
    (hn : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Submodule.FiltrationGraded F t) :
    (η.filtrationGraded G t).norm ω
        ((Submodule.filtrationGradedMap f hf t).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.filtrationGraded F t).norm ω z := by
  apply quotientMap_norm_le (ξ.restrict (F t)) (η.restrict (G t))
    (Submodule.filtrationStepMap f hf t) _ _ _ (by ext x; rfl) ω
  intro x
  have hc : (G t).subtype.comp (Submodule.filtrationStepMap f hf t) =
      f.comp (F t).subtype := by ext y; rfl
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  simp only [restrict_norm]
  rw [he]
  exact hn _

/-- In particular, the canonical graded map to an actual quotient contracts;
its target uses the quotient bundle's original subquotient norm. -/
theorem filtrationGradedMap_pushforward_norm_le (ξ : NormFamily S E)
    (q : E →ₗ[K] V) (hq : Function.Surjective q)
    (F : ℝ → Submodule K E) (t : ℝ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Submodule.FiltrationGraded F t) :
    ((ξ.pushforward q hq).filtrationGraded (fun s ↦ (F s).map q) t).norm ω
        ((Submodule.filtrationGradedMap q
          (fun s ↦ Submodule.le_comap_map q (F s)) t).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.filtrationGraded F t).norm ω z :=
  filtrationGradedMap_norm_le ξ (ξ.pushforward q hq) q _ t ω
    (ξ.pushforward_norm_le q hq ω) z

omit [FiniteDimensional K V] in
/-- At an infinite place the actual quotient map has a linear isometric
section, obtained from the orthogonal complement of its completed kernel. -/
theorem IsHermitian.exists_pushforward_section {ξ : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hN) (q : E →ₗ[K] V) (hq : Function.Surjective q)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    ∃ s : ((S.ϕ ω).Completion ⊗[K] V) →ₗ[(S.ϕ ω).Completion]
        ((S.ϕ ω).Completion ⊗[K] E),
      (∀ z, q.baseChange (S.ϕ ω).Completion (s z) = z) ∧
      (∀ z, ξ.norm ω (s z) = (ξ.pushforward q hq).norm ω z) := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := hξ.fibreInnerProductSpace ω hω
  let W := (q.baseChange L).ker
  let e := (q.baseChange L).quotKerEquivOfSurjective
    (LinearMap.baseChange_surjective L hq)
  let s := Wᗮ.subtype.comp
    (W.quotientEquivOrthogonal.toLinearEquiv.toLinearMap.comp e.symm.toLinearMap)
  refine ⟨s, ?_, ?_⟩
  · intro z
    have hm : W.mkQ (s z) = e.symm z := by
      change Submodule.Quotient.mk
        (W.quotientEquivOrthogonal (e.symm z) : L ⊗[K] E) = e.symm z
      rw [← W.quotientEquivOrthogonal_symm_eq_mk]
      exact W.quotientEquivOrthogonal.symm_apply_apply _
    have he := congrArg e hm
    change e (Submodule.Quotient.mk (s z)) = e (e.symm z) at he
    simpa only [e, LinearMap.quotKerEquivOfSurjective_apply_mk,
      LinearEquiv.apply_symm_apply] using he
  · intro z
    change ‖W.quotientEquivOrthogonal (e.symm z)‖ = ‖e.symm z‖
    exact W.quotientEquivOrthogonal.norm_map _

/-- A nonnegative multiple of the actual quotient norm is determined by all
completed lifts. This includes a zero multiplier and a zero quotient. -/
theorem le_mul_pushforward_norm (ξ : NormFamily S E)
    (q : E →ₗ[K] V) (hq : Function.Surjective q) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] V) {a C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, q.baseChange (S.ϕ ω).Completion x = z → a ≤ C * ξ.norm ω x) :
    a ≤ C * (ξ.pushforward q hq).norm ω z := by
  by_cases hzero : C = 0
  · obtain ⟨x, hx⟩ := LinearMap.baseChange_surjective (S.ϕ ω).Completion hq z
    simpa only [hzero, zero_mul] using h x hx
  · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
    rw [mul_comm C]
    apply (div_le_iff₀ hpos).mp
    apply (ξ.le_quotientSeminorm_iff q hq ω z _).mpr
    intro x hx
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using h x hx)

section Binary

variable {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The canonical tensor lift from two filtration steps to their tensor grade
contracts the actual restricted Hermitian tensor norm on every completed vector. -/
theorem tensorFiltrationGradedLift_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F)
    {t u γ : ℝ} (h : t + u = γ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (P t ⊗[K] R u)) :
    ((ξ.orthogonalTensorPair η hN hξ hη).filtrationGraded
        (Submodule.tensorFiltration P R) γ).norm ω
      ((Submodule.tensorFiltrationGradedLift P R h).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.restrict (P t)).orthogonalTensorPair (η.restrict (R u)) hN
        (hξ.restrict _) (hη.restrict _)).norm ω z := by
  let σ := ξ.orthogonalTensorPair η hN hξ hη
  have hc : (Submodule.tensorFiltration P R γ).subtype.comp
      (Submodule.tensorFiltrationStepMap P R h) =
        TensorProduct.map (P t).subtype (R u).subtype := by ext x y; rfl
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [Submodule.tensorFiltrationGradedLift, LinearMap.baseChange_comp, LinearMap.comp_apply]
  apply (σ.filtrationGraded_norm_mk_le _ _ ω _).trans
  simp only [restrict_norm, he]
  exact orthogonalTensorPair_restrict_map_norm_le ξ η hN hξ hη _ _ ω z

/-- The canonical binary-to-finite completed tensor identification is natural
for the given rational factor maps. -/
theorem tensorPairFibre_map
    {G H : Type w} [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H]
    (L : Type*) [Field L] [Algebra K L] (f : E →ₗ[K] G) (g : F →ₗ[K] H)
    (z : L ⊗[K] (E ⊗[K] F)) :
    tensorBaseChangeEquiv K L (BinaryTensorFactors G H)
      ((binaryTensorEquiv K (BinaryTensorFactors G H)).symm.toLinearMap.baseChange L
        ((TensorProduct.map f g).baseChange L z)) =
      PiTensorProduct.map (fun i ↦
        (show BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors G H i from
          match i with | .inl _ => f | .inr _ => g).baseChange L)
        (tensorBaseChangeEquiv K L (BinaryTensorFactors E F)
          ((binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap.baseChange L z)) := by
  let ff : ∀ i, BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors G H i :=
    fun i ↦ match i with | .inl _ => f | .inr _ => g
  let B₁ := binaryTensorEquiv K (BinaryTensorFactors E F)
  let B₂ := binaryTensorEquiv K (BinaryTensorFactors G H)
  have hc : B₂.symm.toLinearMap.comp (TensorProduct.map f g) =
      (PiTensorProduct.map ff).comp B₁.symm.toLinearMap := by
    apply LinearMap.ext
    intro y
    apply B₂.injective
    change TensorProduct.map f g y = B₂ (PiTensorProduct.map ff (B₁.symm y))
    obtain ⟨x, rfl⟩ := B₁.surjective y
    rw [LinearEquiv.symm_apply_apply]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod a x =>
      simp [B₁, B₂, ff, binaryTensorEquiv_tprod]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hz := DFunLike.congr_fun (congrArg (fun h ↦ h.baseChange L) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  rw [hz, tensorBaseChangeEquiv_map]

end Binary

end ArakelovGeometry.NormFamily
