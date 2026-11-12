/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
public import ArakelovGeometry.LinearAlgebra.Filtration.TensorGraded

import ArakelovGeometry.Analysis.Tensor.Bilinear
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual norms and contractions on filtration grades

Every grade carries the restriction followed by the quotient of the original
norm family. The canonical graded map descends a completed contraction by
comparing every completed lift, including at trivially valued places.

The binary pair and quotient-composite statements supply the componentwise
route to Bost, Section 7, Lemmas 7.1--7.2 (pages 29--30). Chen--Moriwaki's
October 2019 Remark 5.5.6 treats individual refinement subquotients; here only
the canonical binary real grades needed by this consumer are constructed.
No contraction of a whole orthogonal direct sum is asserted. The image-flag
degree argument is in `Degree.Flag.ImageHN`; the chosen HN-lift variation
assembly is a separate consumer.
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
    [hN : S.IsArchimedeanNormalized]
    (hξ : ξ.IsHermitian) (F : ℝ → Submodule K E) (t : ℝ) :
    (ξ.filtrationGraded F t).IsHermitian :=
  (hξ.restrict (F t)).quotient _

instance instIsHermitianFiltrationGraded (ξ : NormFamily S E)
    [S.IsArchimedeanNormalized] [hξ : ξ.IsHermitian]
    (F : ℝ → Submodule K E) (t : ℝ) :
    (ξ.filtrationGraded F t).IsHermitian := hξ.filtrationGraded F t

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
    [hN : S.IsArchimedeanNormalized]
    (hξ : ξ.IsHermitian) (q : E →ₗ[K] V) (hq : Function.Surjective q)
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
  let := ξ.fiberInnerProductSpace ω hω
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

omit [FiniteDimensional K V] in
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
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    (P : ℝ → Submodule K E) (R : ℝ → Submodule K F)
    {t u γ : ℝ} (h : t + u = γ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (P t ⊗[K] R u)) :
    ((ξ ⊗ʰ η).filtrationGraded
        (Submodule.tensorFiltration P R) γ).norm ω
      ((Submodule.tensorFiltrationGradedLift P R h).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.restrict (P t)).orthogonalTensorPair (η.restrict (R u))).norm ω z := by
  let σ := ξ.orthogonalTensorPair η
  have hc : (Submodule.tensorFiltration P R γ).subtype.comp
      (Submodule.tensorFiltrationStepMap P R h) =
        TensorProduct.map (P t).subtype (R u).subtype := by ext x y; rfl
  have he := DFunLike.congr_fun
    (congrArg (fun p ↦ p.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [Submodule.tensorFiltrationGradedLift, LinearMap.baseChange_comp, LinearMap.comp_apply]
  apply (σ.filtrationGraded_norm_mk_le _ _ ω _).trans
  simp only [restrict_norm, he]
  exact orthogonalTensorPair_restrict_map_norm_le ξ η _ _ ω z

omit [FiniteDimensional K E] [FiniteDimensional K F] in
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
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
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

omit [FiniteDimensional K V] in
/-- A contraction from the tensor of two spaces which descends through both
factor quotients contracts their actual quotient tensor norms. -/
theorem orthogonalTensorPair_descend_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F) (θ : NormFamily S V)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] [hθ : θ.IsHermitian]
    (U : Submodule K E) (T : Submodule K F)
    (f : ((E ⧸ U) ⊗[K] (F ⧸ T)) →ₗ[K] V) (ω : S.Ω)
    (hf : ∀ z, θ.norm ω
      ((f.comp (TensorProduct.map U.mkQ T.mkQ)).baseChange (S.ϕ ω).Completion z) ≤
        (ξ ⊗ʰ η).norm ω z)
    (z : (S.ϕ ω).Completion ⊗[K] ((E ⧸ U) ⊗[K] (F ⧸ T))) :
    θ.norm ω (f.baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.quotient U).orthogonalTensorPair (η.quotient T)).norm ω z := by
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] BinaryTensorFactors E F i
  let Y i := L ⊗[K] BinaryTensorFactors (E ⧸ U) (F ⧸ T) i
  let ξs := tensorPairFactors ξ η
  let ηs := tensorPairFactors (ξ.quotient U) (η.quotient T)
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (ξs i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (ξs i).fibreNormedSpace ω
  let : ∀ i, NormedAddCommGroup (Y i) := fun i ↦ (ηs i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (Y i) := fun i ↦ (ηs i).fibreNormedSpace ω
  let := θ.fibreNormedAddCommGroup ω
  let := θ.fibreNormedSpace ω
  let B₁ := (binaryTensorEquiv K (BinaryTensorFactors E F)).baseChange K L _ _
  let B₂ := (binaryTensorEquiv K (BinaryTensorFactors (E ⧸ U) (F ⧸ T))).baseChange K L _ _
  let A₁ := B₁.symm.trans (tensorBaseChangeEquiv K L (BinaryTensorFactors E F))
  let A₂ := B₂.symm.trans
    (tensorBaseChangeEquiv K L (BinaryTensorFactors (E ⧸ U) (F ⧸ T)))
  let q : ∀ i, X i →ₗ[L] Y i := fun i ↦
    (show BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors (E ⧸ U) (F ⧸ T) i from
      match i with | .inl _ => U.mkQ | .inr _ => T.mkQ).baseChange L
  have hc (x : L ⊗[K] (E ⊗[K] F)) :
      A₂ ((TensorProduct.map U.mkQ T.mkQ).baseChange L x) =
        PiTensorProduct.map q (A₁ x) := tensorPairFibre_map L U.mkQ T.mkQ x
  let g := (f.baseChange L).comp A₂.symm.toLinearMap
  have hpre (x : ⨂[L] i, X i) :
      θ.norm ω (g (PiTensorProduct.map q x)) ≤
        (ξ ⊗ʰ η).norm ω (A₁.symm x) := by
    have he := hc (A₁.symm x)
    rw [LinearEquiv.apply_symm_apply] at he
    change θ.norm ω (f.baseChange L (A₂.symm (PiTensorProduct.map q x))) ≤ _
    rw [← he, LinearEquiv.symm_apply_apply]
    simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using hf (A₁.symm x)
  have hxnorm (x : ⨂[L] i, X i) :
      (ξ ⊗ʰ η).norm ω (A₁.symm x) =
        (orthogonalTensor ξs).norm ω
          ((tensorBaseChangeEquiv K L (BinaryTensorFactors E F)).symm x) := by
    change (orthogonalTensor ξs).norm ω
      (B₁.symm (B₁ ((tensorBaseChangeEquiv K L (BinaryTensorFactors E F)).symm x))) = _
    rw [LinearEquiv.symm_apply_apply]
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let : ∀ i, InnerProductSpace L (X i) :=
      fun i ↦ (tensorPairFactors ξ η i).fiberInnerProductSpace ω hω
    let : ∀ i, InnerProductSpace L (Y i) :=
      fun i ↦ (tensorPairFactors (ξ.quotient U) (η.quotient T) i).fiberInnerProductSpace ω hω
    obtain ⟨s₁, hs₁, hn₁⟩ := hξ.exists_pushforward_section U.mkQ U.mkQ_surjective ω hω
    obtain ⟨s₂, hs₂, hn₂⟩ := hη.exists_pushforward_section T.mkQ T.mkQ_surjective ω hω
    let s : ∀ i, Y i →ₗᵢ[L] X i := fun i ↦ match i with
      | .inl _ => { toLinearMap := s₁, norm_map' := hn₁ }
      | .inr _ => { toLinearMap := s₂, norm_map' := hn₂ }
    have hqs (y : ⨂[L] i, Y i) :
        PiTensorProduct.map q (PiTensorProduct.map (fun i ↦ (s i).toLinearMap) y) = y := by
      induction y using PiTensorProduct.induction_on with
      | smul_tprod a y =>
        simp only [map_smul, PiTensorProduct.map_tprod]
        congr 2
        funext i
        cases i with
        | inl i => exact hs₁ _
        | inr i => exact hs₂ _
      | add x y hx hy => simp only [map_add, hx, hy]
    have hb := hpre (PiTensorProduct.map (fun i ↦ (s i).toLinearMap) (A₂ z))
    rw [hqs, hxnorm, orthogonalTensor_norm_of_infinite _ ω hω] at hb
    change θ.norm ω (f.baseChange L (A₂.symm (A₂ z))) ≤
      orthogonalTensorSeminorm (fun i ↦ stdOrthonormalBasis L (X i))
        (tensorBaseChangeEquiv K L (BinaryTensorFactors E F)
          ((tensorBaseChangeEquiv K L (BinaryTensorFactors E F)).symm
            (PiTensorProduct.map (fun i ↦ (s i).toLinearMap) (A₂ z)))) at hb
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
      orthogonalTensorSeminorm_map_eq
      (fun i ↦ stdOrthonormalBasis L (Y i)) (fun i ↦ stdOrthonormalBasis L (X i)) s] at hb
    change θ.norm ω (f.baseChange L z) ≤
      (orthogonalTensor ηs).norm ω
        (B₂.symm z)
    rw [orthogonalTensor_norm_of_infinite _ ω hω]
    exact hb
  · have hfin : ω ∈ S.Ωfin := not_not.mp hω
    have hp₀ (x : ∀ i, X i) :
        θ.norm ω (g (⨂ₜ[L] i, q i (x i))) ≤ ∏ i, ‖x i‖ := by
      have hb := hpre (⨂ₜ[L] i, x i)
      rw [PiTensorProduct.map_tprod, hxnorm, orthogonalTensor_norm_tprod] at hb
      exact hb
    have hp (y : ∀ i, Y i) : ‖g (⨂ₜ[L] i, y i)‖ ≤ ∏ i, ‖y i‖ := by
      change θ.norm ω (g (⨂ₜ[L] i, y i)) ≤ _
      simp only [Fintype.prod_sum_type, Fintype.prod_unique]
      change θ.norm ω (g (⨂ₜ[L] i, y i)) ≤
        (ξ.quotient U).norm ω (y (.inl ())) * (η.quotient T).norm ω (y (.inr ()))
      rw [mul_comm]
      apply ξ.le_mul_pushforward_norm U.mkQ U.mkQ_surjective ω (y (.inl ()))
        ((η.quotient T).norm_nonneg ω _)
      intro x hx
      rw [mul_comm]
      apply η.le_mul_pushforward_norm T.mkQ T.mkQ_surjective ω (y (.inr ()))
        (ξ.norm_nonneg ω x)
      intro v hv
      let xv : ∀ i, X i := fun i ↦ match i with | .inl _ => x | .inr _ => v
      have he : (fun i ↦ q i (xv i)) = y := by
        funext i
        cases i with
        | inl i => simpa using hx
        | inr i => simpa using hv
      have hb := hp₀ xv
      rw [he] at hb
      simp only [Fintype.prod_sum_type, Fintype.prod_unique] at hb
      change θ.norm ω (g (⨂ₜ[L] i, y i)) ≤ ξ.norm ω x * η.norm ω v at hb
      exact hb
    have hb := norm_linearMap_le_injective_of_ultrametric_factors g (hθ.1 ω hfin) hp (A₂ z)
    change θ.norm ω (f.baseChange L (A₂.symm (A₂ z))) ≤ _ at hb
    rw [LinearEquiv.symm_apply_apply] at hb
    rw [orthogonalTensorPair_norm_of_finite _ _ ω hfin]
    exact hb

/-- A5's canonical graded pair map contracts the actual tensor of the two
grade norms into the actual tensor grade norm, on all completed fibre vectors.
This is the binary component bound used in Bost Lemmas 7.1--7.2, rather than
the paper's whole-sum bound or a general refinement theorem. -/
theorem tensorFiltrationGradedPair_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R) {t u γ : ℝ} (h : t + u = γ)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (Submodule.FiltrationGraded P t ⊗[K] Submodule.FiltrationGraded R u)) :
    ((ξ ⊗ʰ η).filtrationGraded
        (Submodule.tensorFiltration P R) γ).norm ω
      ((Submodule.tensorFiltrationGradedPair hP hR h).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.filtrationGraded P t).orthogonalTensorPair (η.filtrationGraded R u)
        (hξ := (hξ.filtrationGraded P t)) (hη := (hη.filtrationGraded R u))).norm ω z := by
  apply orthogonalTensorPair_descend_norm_le (ξ.restrict (P t)) (η.restrict (R u))
    ((ξ ⊗ʰ η).filtrationGraded _ γ)
    (hθ := ((orthogonalTensorPair_isHermitian ξ η).filtrationGraded _ _))
    _ _ (Submodule.tensorFiltrationGradedPair hP hR h) ω
  intro x
  have hc : (Submodule.tensorFiltrationGradedPair hP hR h).comp
      (TensorProduct.map (Submodule.filtrationGradedMk P t)
        (Submodule.filtrationGradedMk R u)) =
      Submodule.tensorFiltrationGradedLift P R h := by ext x y; rfl
  change ((ξ ⊗ʰ η).filtrationGraded _ γ).norm ω
    (((Submodule.tensorFiltrationGradedPair hP hR h).comp
      (TensorProduct.map (Submodule.filtrationGradedMk P t)
        (Submodule.filtrationGradedMk R u))).baseChange (S.ϕ ω).Completion x) ≤ _
  rw [hc]
  exact tensorFiltrationGradedLift_norm_le ξ η P R h ω x

/-- Each canonical graded pair contracts into the actual quotient grade, with
its original subquotient norm from the actual quotient of the tensor bundle. -/
theorem tensorFiltrationGradedPair_pushforward_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    (q : (E ⊗[K] F) →ₗ[K] V) (hq : Function.Surjective q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R) {t u γ : ℝ} (h : t + u = γ)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (Submodule.FiltrationGraded P t ⊗[K] Submodule.FiltrationGraded R u)) :
    (((ξ ⊗ʰ η).pushforward q hq).filtrationGraded
        (fun s ↦ (Submodule.tensorFiltration P R s).map q) γ).norm ω
      (((Submodule.filtrationGradedMap q
          (fun s ↦ Submodule.le_comap_map q (Submodule.tensorFiltration P R s)) γ).comp
        (Submodule.tensorFiltrationGradedPair hP hR h)).baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.filtrationGraded P t).orthogonalTensorPair (η.filtrationGraded R u)
        (hξ := (hξ.filtrationGraded P t)) (hη := (hη.filtrationGraded R u))).norm ω z := by
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact (filtrationGradedMap_pushforward_norm_le
    (ξ ⊗ʰ η) q hq _ γ ω _).trans
      (tensorFiltrationGradedPair_norm_le ξ η hP hR h ω z)

end Binary

end ArakelovGeometry.NormFamily
