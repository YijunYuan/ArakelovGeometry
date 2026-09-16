/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValueFinite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Local degrees and field norms

Embeddings of a finite extension into an algebraic closure of the completed base
are partitioned by the absolute values they induce. The embeddings in each part
are exactly the embeddings of the corresponding completed extension. Counting
them gives the local-degree sum of Chen–Moriwaki, §3.3, formula (3.3),
and grouping the conjugates gives the norm product in Theorem 3.3.7(4).
-/

open UniformSpace

namespace AbsoluteValue

/-- Every embedding into the algebraic closure of the completed base that induces
`w` extends uniquely to the completion at `w`. -/
theorem existsUnique_completion_algHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion)
    (σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion)
    (hσ : u.pullback σ.toRingHom = w) :
    ∃! τ : w.Completion →ₐ[(w.restriction K).Completion]
        AlgebraicClosure (w.restriction K).Completion,
      ∀ x : L, τ (algebraMap L w.Completion x) = σ x := by
  let B := (w.restriction K).Completion
  let C := AlgebraicClosure B
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  let f : WithAbs w →+* WithAbs u := WithAbs.map w u σ.toRingHom
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f (fun x ↦ by
    exact congrArg (fun z : AbsoluteValue L ℝ ↦ z x.ofAbs) hσ)
  let h : w.Completion →+* u.Completion := hf.mapRingHom
  have hb : Isometry (algebraMap B u.Completion) :=
    AddMonoidHomClass.isometry_of_norm (algebraMap B u.Completion) fun b ↦ by
      change ‖(WithAbs.toAbs u (algebraMap B C b) : u.Completion)‖ = ‖b‖
      rw [Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
      exact congrArg (fun z : AbsoluteValue B ℝ ↦ z b) hu
  have hcomm (b : B) : h (algebraMap B w.Completion b) = algebraMap B u.Completion b := by
    induction b using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (hf.isometry_mapRingHom.continuous.comp (isometry_algebraMap_completion w K).continuous)
        hb.continuous
    | ih a =>
      rw [algebraMap_completion_def, Completion.mapRingHom_coe, Isometry.mapRingHom_coe]
      change (WithAbs.toAbs u (σ (algebraMap K L a.ofAbs)) : u.Completion) =
        algebraMap B u.Completion (a : B)
      rw [σ.commutes]
      rfl
  let ha : w.Completion →ₐ[B] u.Completion := { h with commutes' := hcomm }
  let e := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits
    (F := B) (K := w.Completion) u.Completion C (fun _ ↦ IsAlgClosed.splits _)
  have he (x : L) : e.symm ha (algebraMap L w.Completion x) = σ x := by
    apply (algebraMap C u.Completion).injective
    change e (e.symm ha) (algebraMap L w.Completion x) =
      algebraMap C u.Completion (σ x)
    rw [e.apply_symm_apply]
    exact hf.mapRingHom_coe (WithAbs.toAbs w x)
  refine ⟨e.symm ha, he, fun τ hτ ↦ ?_⟩
  have heq : τ.toLinearMap = (e.symm ha).toLinearMap :=
    LinearMap.ext_on_range (span_coe_basis_eq_top w K (Module.Free.chooseBasis K L))
      (fun i ↦ (hτ _).trans (he _).symm)
  ext x
  exact LinearMap.congr_fun heq x

/-- An embedding of a completed finite extension into an algebraic closure
preserves the unique extending absolute value. -/
theorem apply_completion_algHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion)
    (τ : w.Completion →ₐ[(w.restriction K).Completion]
      AlgebraicClosure (w.restriction K).Completion) (x : w.Completion) :
    u (τ x) = ‖x‖ := by
  let B := (w.restriction K).Completion
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  have ht : (u.pullback τ.toRingHom).restriction B = n := by
    ext b
    change u (τ (algebraMap B w.Completion b)) = ‖b‖
    rw [τ.commutes]
    exact congrArg (fun z : AbsoluteValue B ℝ ↦ z b) hu
  have hn : (NormedField.toAbsoluteValue w.Completion).restriction B = n := by
    ext b
    exact norm_algebraMap_completion w K b
  exact congrArg (fun z : AbsoluteValue w.Completion ℝ ↦ z x)
    ((existsUnique_extension_of_complete (L := w.Completion) n).unique ht hn)


/-- Completed embeddings are exactly embeddings inducing the given absolute value. -/
noncomputable def completionEmbeddingEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion) :
    (w.Completion →ₐ[(w.restriction K).Completion]
      AlgebraicClosure (w.restriction K).Completion) ≃
    {σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion //
      u.pullback σ.toRingHom = w} := by
  let B := (w.restriction K).Completion
  let C := AlgebraicClosure B
  have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
  have : IsScalarTower K B w.Completion := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change ((WithAbs.toAbs w (algebraMap K L x)) : w.Completion) = _
    rw [algebraMap_completion_def]
    exact (Completion.mapRingHom_coe
      (isometry_algebraMap_withAbs w K).continuous (WithAbs.toAbs (w.restriction K) x)).symm
  let f₀ (τ : w.Completion →ₐ[B] C) : L →ₐ[K] C := {
    toRingHom := τ.toRingHom.comp (algebraMap L w.Completion)
    commutes' a := by
      change τ (algebraMap K w.Completion a) = algebraMap K C a
      rw [IsScalarTower.algebraMap_apply K B w.Completion, τ.commutes,
        ← IsScalarTower.algebraMap_apply K B C] }
  have hf₀ (τ : w.Completion →ₐ[B] C) : u.pullback (f₀ τ).toRingHom = w := by
    ext x
    change u (τ (algebraMap L w.Completion x)) = w x
    rw [apply_completion_algHom w u hu]
    exact Completion.norm_coe (WithAbs.toAbs w x)
  let f (τ : w.Completion →ₐ[B] C) :
      {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w} := ⟨f₀ τ, hf₀ τ⟩
  have hf : Function.Bijective f := by
    constructor
    · intro τ τ' heq
      have hh : τ.toLinearMap = τ'.toLinearMap :=
        LinearMap.ext_on_range (span_coe_basis_eq_top w K (Module.Free.chooseBasis K L))
          (fun i ↦ congrArg (fun z ↦ z.val (Module.Free.chooseBasis K L i)) heq)
      ext x
      exact LinearMap.congr_fun hh x
    · intro σ
      obtain ⟨τ, hτ, -⟩ := existsUnique_completion_algHom w u hu σ.val σ.property
      refine ⟨τ, ?_⟩
      apply Subtype.ext
      ext x
      exact hτ x
  exact Equiv.ofBijective f hf

/-- The number of embeddings inducing a place is its local separable degree. -/
theorem card_embeddings_eq_localFinSepDegree {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion) :
    Nat.card {σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion //
      u.pullback σ.toRingHom = w} =
      Field.finSepDegree (w.restriction K).Completion w.Completion := by
  have : FiniteDimensional (w.restriction K).Completion w.Completion :=
    finiteDimensional_completion w K
  calc
    _ = Nat.card (w.Completion →ₐ[(w.restriction K).Completion]
        AlgebraicClosure (w.restriction K).Completion) :=
      (Nat.card_congr (completionEmbeddingEquiv w u hu)).symm
    _ = Field.finSepDegree (w.restriction K).Completion w.Completion :=
      (Field.finSepDegree_eq_of_isAlgClosed _ _ _).symm

/-- The number of embeddings inducing a fixed absolute value is its local degree. -/
theorem card_embeddings_eq_localDegree {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (w : AbsoluteValue L ℝ)
    (u : AbsoluteValue (AlgebraicClosure (w.restriction K).Completion) ℝ)
    (hu : u.restriction (w.restriction K).Completion =
      NormedField.toAbsoluteValue (w.restriction K).Completion) :
    Nat.card {σ : L →ₐ[K] AlgebraicClosure (w.restriction K).Completion //
      u.pullback σ.toRingHom = w} = w.localDegree K := by
  have : Algebra.IsSeparable (w.restriction K).Completion w.Completion := isSeparable_completion w
  simpa only [Field.finSepDegree_eq_finrank_of_isSeparable, localDegree] using
    card_embeddings_eq_localFinSepDegree w u hu

/-- The sum of the local degrees over a finite separable extension equals its degree. -/
theorem sum_localDegree {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}] :
    ∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, w.val.localDegree K =
      Module.finrank K L := by
  classical
  let B := v.Completion
  let C := AlgebraicClosure B
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let e : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := e.completeSpace
  obtain ⟨u, hu, -⟩ := existsUnique_extension_of_complete (L := C) n
  let E := {w : AbsoluteValue L ℝ // w.restriction K = v}
  have hr (σ : L →ₐ[K] C) : (u.pullback σ.toRingHom).restriction K = v := by
    ext a
    change u (σ (algebraMap K L a)) = v a
    rw [σ.commutes, IsScalarTower.algebraMap_apply K B C]
    rw [show u (algebraMap B C (algebraMap K B a)) = ‖algebraMap K B a‖ from
      congrArg (fun z : AbsoluteValue B ℝ ↦ z (algebraMap K B a)) hu]
    exact Completion.norm_coe (WithAbs.toAbs v a)
  let f (σ : L →ₐ[K] C) : E := ⟨u.pullback σ.toRingHom, hr σ⟩
  have hc (w : E) :
      Nat.card {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w.val} = w.val.localDegree K := by
    rcases w with ⟨w, hw⟩
    subst v
    exact card_embeddings_eq_localDegree w u hu
  have hf (w : E) : Fintype.card {σ : L →ₐ[K] C // f σ = w} = w.val.localDegree K := by
    rw [Fintype.card_eq_nat_card]
    calc
      _ = Nat.card {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w.val} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun σ ↦ by
          exact Subtype.ext_iff))
      _ = w.val.localDegree K := hc w
  have hh := Fintype.sum_fiberwise f (fun _ ↦ (1 : ℕ))
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hf,
    AlgHom.card] using hh

/-- Local separable embedding counts are independent of the algebraically closed ambient field. -/
theorem card_embeddings_eq_localFinSepDegree_of_isAlgClosed {K L C₀ : Type*}
    [Field K] [Field L] [Field C₀] [Algebra K L] [Algebra K C₀]
    [FiniteDimensional K L] [IsAlgClosed C₀]
    (w : AbsoluteValue L ℝ) (u₀ : AbsoluteValue C₀ ℝ)
    (hu₀ : u₀.restriction K = w.restriction K) :
    Nat.card {σ : L →ₐ[K] C₀ // u₀.pullback σ.toRingHom = w} =
      Field.finSepDegree (w.restriction K).Completion w.Completion := by
  let v := w.restriction K
  let B := v.Completion
  let C := AlgebraicClosure B
  let n : AbsoluteValue B ℝ := NormedField.toAbsoluteValue B
  let eB : WithAbs n ≃ᵢ B := {
    (WithAbs.equiv n).toEquiv with
    isometry_toFun := AddMonoidHomClass.isometry_of_norm (WithAbs.equiv n) (fun _ ↦ rfl) }
  have : CompleteSpace (WithAbs n) := eB.completeSpace
  obtain ⟨u, hu, -⟩ := existsUnique_extension_of_complete (L := C) n
  let N := IntermediateField.normalClosure K L C₀
  have : IsNormalClosure K L N :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun _ ↦ IsAlgClosed.splits _)
  have hr : (u₀.restriction N).restriction K = v := by
    ext a
    change u₀ (algebraMap N C₀ (algebraMap K N a)) = v a
    rw [← IsScalarTower.algebraMap_apply K N C₀]
    exact congrArg (fun z : AbsoluteValue K ℝ ↦ z a) hu₀
  obtain ⟨j, hj⟩ := exists_algHom_eq_pullback v (u₀.restriction N) hr u hu
  let : Algebra N C := j.toRingHom.toAlgebra
  have : IsScalarTower K N C :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (j.commutes a).symm)
  let e₀ := normalClosure.algHomEquiv K L C₀
  let e₁ := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (F := K) (K := L) C N
    (fun x ↦ IsNormalClosure.splits x)
  let e := e₀.symm.trans e₁
  have he (σ : L →ₐ[K] C₀) : u.pullback (e σ).toRingHom = u₀.pullback σ.toRingHom := by
    ext x
    change u (j (e₀.symm σ x)) = u₀ (σ x)
    have hh := congrArg (fun z : AbsoluteValue N ℝ ↦ z (e₀.symm σ x)) hj
    exact hh.symm
  calc
    _ = Nat.card {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w} :=
      Nat.card_congr (e.subtypeEquiv (fun σ ↦ by rw [he]))
    _ = Field.finSepDegree (w.restriction K).Completion w.Completion :=
      card_embeddings_eq_localFinSepDegree w u hu

/-- The number of embeddings inducing a fixed place is independent of the
algebraically closed ambient field. -/
theorem card_embeddings_eq_localDegree_of_isAlgClosed {K L C₀ : Type*}
    [Field K] [Field L] [Field C₀] [Algebra K L] [Algebra K C₀]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed C₀]
    (w : AbsoluteValue L ℝ) (u₀ : AbsoluteValue C₀ ℝ)
    (hu₀ : u₀.restriction K = w.restriction K) :
    Nat.card {σ : L →ₐ[K] C₀ // u₀.pullback σ.toRingHom = w} = w.localDegree K := by
  have : Algebra.IsSeparable (w.restriction K).Completion w.Completion := isSeparable_completion w
  simpa only [Field.finSepDegree_eq_finrank_of_isSeparable, localDegree] using
    card_embeddings_eq_localFinSepDegree_of_isAlgClosed w u₀ hu₀

/-- Counting embeddings with their induced absolute values, in multiplicative form. -/
theorem prod_pow_localDegree_eq_prod_embeddings {K L C M : Type*}
    [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C] [IsAlgClosed C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [CommMonoid M]
    (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    (u : AbsoluteValue C ℝ) (hu : u.restriction K = v) (φ : AbsoluteValue L ℝ → M) :
    ∏ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, φ w.val ^ w.val.localDegree K =
      ∏ σ : L →ₐ[K] C, φ (u.pullback σ.toRingHom) := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.restriction K = v}
  have hr (σ : L →ₐ[K] C) : (u.pullback σ.toRingHom).restriction K = v := by
    ext a
    change u (σ (algebraMap K L a)) = v a
    rw [σ.commutes]
    exact congrArg (fun z : AbsoluteValue K ℝ ↦ z a) hu
  let f (σ : L →ₐ[K] C) : E := ⟨u.pullback σ.toRingHom, hr σ⟩
  have hf (w : E) : Fintype.card {σ : L →ₐ[K] C // f σ = w} = w.val.localDegree K := by
    rw [Fintype.card_eq_nat_card]
    calc
      _ = Nat.card {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w.val} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun σ ↦ Subtype.ext_iff))
      _ = w.val.localDegree K :=
        card_embeddings_eq_localDegree_of_isAlgClosed w.val u (hu.trans w.property.symm)
  have hh := Fintype.prod_fiberwise' f (fun w : E ↦ φ w.val)
  simpa only [Finset.prod_const, Finset.card_univ, hf] using hh

/-- Counting embeddings by their absolute values for any finite extension. -/
theorem sum_localFinSepDegree_nsmul_eq_sum_embeddings {K L C M : Type*}
    [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C] [IsAlgClosed C]
    [FiniteDimensional K L] [AddCommMonoid M]
    (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    (u : AbsoluteValue C ℝ) (hu : u.restriction K = v) (φ : AbsoluteValue L ℝ → M) :
    ∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
      Field.finSepDegree (w.val.restriction K).Completion w.val.Completion • φ w.val =
      ∑ σ : L →ₐ[K] C, φ (u.pullback σ.toRingHom) := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.restriction K = v}
  have hr (σ : L →ₐ[K] C) : (u.pullback σ.toRingHom).restriction K = v := by
    ext a
    change u (σ (algebraMap K L a)) = v a
    rw [σ.commutes]
    exact congrArg (fun z : AbsoluteValue K ℝ ↦ z a) hu
  let f (σ : L →ₐ[K] C) : E := ⟨u.pullback σ.toRingHom, hr σ⟩
  have hf (w : E) : Fintype.card {σ : L →ₐ[K] C // f σ = w} =
      Field.finSepDegree (w.val.restriction K).Completion w.val.Completion := by
    rw [Fintype.card_eq_nat_card]
    calc
      _ = Nat.card {σ : L →ₐ[K] C // u.pullback σ.toRingHom = w.val} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun σ ↦ Subtype.ext_iff))
      _ = Field.finSepDegree (w.val.restriction K).Completion w.val.Completion :=
        card_embeddings_eq_localFinSepDegree_of_isAlgClosed w.val u (hu.trans w.property.symm)
  have hh := Fintype.sum_fiberwise' f (fun w : E ↦ φ w.val)
  simpa only [Finset.sum_const, Finset.card_univ, hf] using hh

/-- Counting embeddings with their induced absolute values, in additive form. -/
theorem sum_localDegree_nsmul_eq_sum_embeddings {K L C M : Type*}
    [Field K] [Field L] [Field C] [Algebra K L] [Algebra K C] [IsAlgClosed C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [AddCommMonoid M]
    (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    (u : AbsoluteValue C ℝ) (hu : u.restriction K = v) (φ : AbsoluteValue L ℝ → M) :
    ∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v}, w.val.localDegree K • φ w.val =
      ∑ σ : L →ₐ[K] C, φ (u.pullback σ.toRingHom) := by
  classical
  rw [← sum_localFinSepDegree_nsmul_eq_sum_embeddings v u hu φ]
  apply Finset.sum_congr rfl
  intro w hw
  have : Algebra.IsSeparable (w.val.restriction K).Completion w.val.Completion :=
    isSeparable_completion w.val
  rw [Field.finSepDegree_eq_finrank_of_isSeparable]
  rfl

/-- The absolute value of a field norm is the product over all extending places,
with each absolute value raised to its local degree. -/
theorem apply_norm_eq_prod {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}] (a : L) :
    v (Algebra.norm K a) =
      ∏ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
        w.val a ^ w.val.localDegree K := by
  obtain ⟨u, hu⟩ := exists_extension (L := AlgebraicClosure K) v
  rw [prod_pow_localDegree_eq_prod_embeddings v u hu (fun w ↦ w a)]
  change v (Algebra.norm K a) = ∏ σ : L →ₐ[K] AlgebraicClosure K, u (σ a)
  rw [← map_prod, ← Algebra.norm_eq_prod_embeddings K (AlgebraicClosure K)]
  exact (congrArg (fun z : AbsoluteValue K ℝ ↦ z (Algebra.norm K a)) hu).symm

/-- Completion respects an intermediate-field tower. -/
theorem isScalarTower_completion_restriction {K L : Type*} [Field K] [Field L]
    [Algebra K L] (w : AbsoluteValue L ℝ) (F : IntermediateField K L) :
    let : Algebra (w.restriction K).Completion (w.restriction F).Completion :=
      algebraCompletion (w.restriction F) K
    IsScalarTower (w.restriction K).Completion (w.restriction F).Completion
      w.Completion := by
  let B := (w.restriction K).Completion
  let D := (w.restriction F).Completion
  let : Algebra B D := algebraCompletion (w.restriction F) K
  apply IsScalarTower.of_algebraMap_eq
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (isometry_algebraMap_completion w K).continuous
      ((isometry_algebraMap_completion w F).continuous.comp
        (isometry_algebraMap_completion (w.restriction F) K).continuous)
  · intro a
    change (algebraMap (w.restriction K).Completion w.Completion)
          (a : (w.restriction K).Completion) =
        (algebraMap (w.restriction F).Completion w.Completion)
          ((algebraMap ((w.restriction F).restriction K).Completion
            (w.restriction F).Completion)
            ((show WithAbs ((w.restriction F).restriction K) from a) :
              ((w.restriction F).restriction K).Completion))
    rw [algebraMap_completion_def, algebraMap_completion_def,
      algebraMap_completion_def]
    erw [Completion.mapRingHom_coe, Completion.mapRingHom_coe, Completion.mapRingHom_coe]
    rfl

/-- Local degrees multiply along an intermediate-field tower. -/
theorem localDegree_mul {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (w : AbsoluteValue L ℝ) (F : IntermediateField K L) :
    (w.restriction F).localDegree K * w.localDegree F = w.localDegree K := by
  let B := (w.restriction K).Completion
  let D := (w.restriction F).Completion
  let : Algebra B D := algebraCompletion (w.restriction F) K
  have : IsScalarTower B D w.Completion := isScalarTower_completion_restriction w F
  have : FiniteDimensional B D := finiteDimensional_completion (w.restriction F) K
  have : FiniteDimensional D w.Completion := finiteDimensional_completion w F
  exact Module.finrank_mul_finrank B D w.Completion

/-- The local degrees above a fixed intermediate place sum to its local degree
times the relative global degree. -/
theorem sum_localDegree_restriction {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (F : IntermediateField K L) [Algebra.IsSeparable F L]
    (v : AbsoluteValue F ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction F = v}] :
    ∑ w : {w : AbsoluteValue L ℝ // w.restriction F = v}, w.val.localDegree K =
      v.localDegree K * Module.finrank F L := by
  have hd (w : {w : AbsoluteValue L ℝ // w.restriction F = v}) :
      w.val.localDegree K = v.localDegree K * w.val.localDegree F := by
    rw [← localDegree_mul w.val F, w.property]
  simp_rw [hd]
  rw [← Finset.mul_sum, sum_localDegree v]

/-- Restriction of places preserves local-degree weighted sums after multiplying
by the relative extension degree. -/
theorem sum_localDegree_nsmul_restriction {K L M : Type*}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [AddCommMonoid M]
    (F : IntermediateField K L) [Algebra.IsSeparable F L]
    (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    [Fintype {w : AbsoluteValue F ℝ // w.restriction K = v}]
    (φ : {w : AbsoluteValue F ℝ // w.restriction K = v} → M) :
    ∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
        w.val.localDegree K • φ ⟨w.val.restriction F, w.property⟩ =
      Module.finrank F L •
        ∑ w : {w : AbsoluteValue F ℝ // w.restriction K = v},
          w.val.localDegree K • φ w := by
  classical
  let E := {w : AbsoluteValue L ℝ // w.restriction K = v}
  let D := {w : AbsoluteValue F ℝ // w.restriction K = v}
  let r (w : E) : D := ⟨w.val.restriction F, w.property⟩
  have hf (x : D) :
      ∑ w : {w : E // r w = x}, w.val.val.localDegree K =
        x.val.localDegree K * Module.finrank F L := by
    let e : {w : E // r w = x} ≃ {w : AbsoluteValue L ℝ // w.restriction F = x.val} := {
      toFun w := ⟨w.val.val, congrArg Subtype.val w.property⟩
      invFun w := ⟨⟨w.val,
        (congrArg (fun z : AbsoluteValue F ℝ ↦ z.restriction K) w.property).trans x.property⟩,
        Subtype.ext w.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    let : Fintype {w : AbsoluteValue L ℝ // w.restriction F = x.val} :=
      Fintype.ofEquiv _ e
    exact (e.sum_comp (fun w ↦ w.val.localDegree K)).trans (sum_localDegree_restriction F x.val)
  change ∑ w : E, w.val.localDegree K • φ (r w) = _
  rw [← Fintype.sum_fiberwise r (fun w : E ↦ w.val.localDegree K • φ (r w))]
  simp_rw [show ∀ x : D, ∀ w : {w : E // r w = x}, r w.val = x from fun _ w ↦ w.property]
  simp_rw [← Finset.sum_smul, hf, mul_nsmul]
  exact (Finset.smul_sum).symm

/-- Extensions of an embedding are counted by the relative separable degree. -/
theorem _root_.AlgHom.natCard_comp_eq_finSepDegree {K F L C : Type*}
    [Field K] [Field F] [Field L] [Field C]
    [Algebra K F] [Algebra K L] [Algebra K C] [Algebra F L]
    [IsScalarTower K F L] [FiniteDimensional F L] [IsAlgClosed C]
    (τ : F →ₐ[K] C) :
    Nat.card {σ : L →ₐ[K] C // σ.comp (IsScalarTower.toAlgHom K F L) = τ} =
      Field.finSepDegree F L := by
  let : Algebra F C := τ.toRingHom.toAlgebra
  have : IsScalarTower K F C := IsScalarTower.of_algebraMap_eq (fun a ↦ (τ.commutes a).symm)
  let e : {σ : L →ₐ[K] C // σ.comp (IsScalarTower.toAlgHom K F L) = τ} ≃
      (L →ₐ[F] C) := {
    toFun σ := {
      σ.val.toRingHom with
      commutes' a := congrArg (fun z : F →ₐ[K] C ↦ z a) σ.property }
    invFun σ := ⟨σ.restrictScalars K, by ext a; exact σ.commutes a⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (Field.finSepDegree_eq_of_isAlgClosed F L C).symm

/-- An embedding of the intermediate field into an algebraically closed field
has as many extensions as the relative separable degree. -/
theorem _root_.AlgHom.natCard_comp_eq_finrank {K F L C : Type*}
    [Field K] [Field F] [Field L] [Field C]
    [Algebra K F] [Algebra K L] [Algebra K C] [Algebra F L]
    [IsScalarTower K F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsAlgClosed C]
    (τ : F →ₐ[K] C) :
    Nat.card {σ : L →ₐ[K] C // σ.comp (IsScalarTower.toAlgHom K F L) = τ} =
      Module.finrank F L := by
  simpa only [Field.finSepDegree_eq_finrank_of_isSeparable] using
    AlgHom.natCard_comp_eq_finSepDegree (L := L) τ

/-- Local separable-degree weighted sums commute with pullback along any finite field embedding. -/
theorem finSepDegree_nsmul_sum_localFinSepDegree_pullback {K F L M : Type*}
    [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    [FiniteDimensional K F] [FiniteDimensional K L]
    [AddCommMonoid M]
    (i : F →ₐ[K] L) (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    [Fintype {w : AbsoluteValue F ℝ // w.restriction K = v}]
    (φ : AbsoluteValue F ℝ → M) :
    Field.finSepDegree K F •
        (∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
          Field.finSepDegree (w.val.restriction K).Completion w.val.Completion •
            φ (w.val.pullback i.toRingHom)) =
      Field.finSepDegree K L •
        ∑ w : {w : AbsoluteValue F ℝ // w.restriction K = v},
          Field.finSepDegree (w.val.restriction K).Completion w.val.Completion • φ w.val := by
  classical
  let : Algebra F L := i.toRingHom.toAlgebra
  have : IsScalarTower K F L :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (i.commutes a).symm)
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite K F L
  obtain ⟨u, hu⟩ := exists_extension (L := AlgebraicClosure K) v
  rw [sum_localFinSepDegree_nsmul_eq_sum_embeddings v u hu (fun w ↦ φ (w.pullback i.toRingHom)),
    sum_localFinSepDegree_nsmul_eq_sum_embeddings v u hu φ]
  let C := AlgebraicClosure K
  let r (σ : L →ₐ[K] C) := σ.comp i
  have hc (τ : F →ₐ[K] C) : Fintype.card {σ : L →ₐ[K] C // r σ = τ} =
      Field.finSepDegree F L := by
    rw [Fintype.card_eq_nat_card]
    exact AlgHom.natCard_comp_eq_finSepDegree τ
  have hh := Fintype.sum_fiberwise' r (fun τ : F →ₐ[K] C ↦ φ (u.pullback τ.toRingHom))
  simp only [Finset.sum_const, Finset.card_univ, hc, ← Finset.smul_sum] at hh
  change Field.finSepDegree K F •
      (∑ σ : L →ₐ[K] C, φ (u.pullback (r σ).toRingHom)) = _
  rw [← hh, ← mul_smul, Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K F L]

/-- Local-degree weighted sums commute with pullback along a field embedding,
after multiplying by the corresponding global degrees. -/
theorem finrank_nsmul_sum_localDegree_pullback {K F L M : Type*}
    [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    [FiniteDimensional K F] [FiniteDimensional K L]
    [Algebra.IsSeparable K F] [Algebra.IsSeparable K L] [AddCommMonoid M]
    (i : F →ₐ[K] L) (v : AbsoluteValue K ℝ)
    [Fintype {w : AbsoluteValue L ℝ // w.restriction K = v}]
    [Fintype {w : AbsoluteValue F ℝ // w.restriction K = v}]
    (φ : AbsoluteValue F ℝ → M) :
    Module.finrank K F •
        (∑ w : {w : AbsoluteValue L ℝ // w.restriction K = v},
          w.val.localDegree K • φ (w.val.pullback i.toRingHom)) =
      Module.finrank K L •
        ∑ w : {w : AbsoluteValue F ℝ // w.restriction K = v},
          w.val.localDegree K • φ w.val := by
  classical
  let : Algebra F L := i.toRingHom.toAlgebra
  have : IsScalarTower K F L :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (i.commutes a).symm)
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite K F L
  have : Algebra.IsSeparable F L :=
    Algebra.isSeparable_tower_top_of_isSeparable K F L
  obtain ⟨u, hu⟩ := exists_extension (L := AlgebraicClosure K) v
  rw [sum_localDegree_nsmul_eq_sum_embeddings v u hu (fun w ↦ φ (w.pullback i.toRingHom)),
    sum_localDegree_nsmul_eq_sum_embeddings v u hu φ]
  let C := AlgebraicClosure K
  let r (σ : L →ₐ[K] C) := σ.comp i
  have hc (τ : F →ₐ[K] C) : Fintype.card {σ : L →ₐ[K] C // r σ = τ} =
      Module.finrank F L := by
    rw [Fintype.card_eq_nat_card]
    exact AlgHom.natCard_comp_eq_finrank τ
  have hh := Fintype.sum_fiberwise' r (fun τ : F →ₐ[K] C ↦ φ (u.pullback τ.toRingHom))
  simp only [Finset.sum_const, Finset.card_univ, hc, ← Finset.smul_sum] at hh
  change Module.finrank K F •
      (∑ σ : L →ₐ[K] C, φ (u.pullback (r σ).toRingHom)) = _
  rw [← hh, ← mul_smul, Module.finrank_mul_finrank K F L]

end AbsoluteValue

namespace IntermediateField

/-- Generating descent with unchanged separable degree preserves all embeddings. -/
theorem bijective_restrict_embeddings_of_adjoin_eq_top
    {A B N C : Type*} [Field A] [Field B] [Field N] [Field C]
    [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [IsAlgClosed C] [FiniteDimensional B N]
    (E : IntermediateField A N) [FiniteDimensional A E]
    (hgen : IntermediateField.adjoin B (E : Set N) = ⊤)
    (hsep : Field.finSepDegree A E = Field.finSepDegree B N) :
    Function.Bijective (fun σ : N →ₐ[B] C ↦ (σ.restrictScalars A).comp E.val) := by
  classical
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro σ τ h
    ext x
    have hx : x ∈ IntermediateField.adjoin B (E : Set N) := by rw [hgen]; trivial
    induction hx using IntermediateField.adjoin_induction with
    | mem a ha => exact congrArg (fun f : E →ₐ[A] C ↦ f ⟨a, ha⟩) h
    | algebraMap a => rw [σ.commutes, τ.commutes]
    | add a b ha hb ia ib => simp only [map_add, ia, ib]
    | inv a ha ia => simp only [map_inv₀, ia]
    | mul a b ha hb ia ib => simp only [map_mul, ia, ib]
  · rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      ← Field.finSepDegree_eq_of_isAlgClosed B N C,
      ← Field.finSepDegree_eq_of_isAlgClosed A E C, hsep]

end IntermediateField

namespace AbsoluteValue

/-- Weighted absolute-value sums are preserved by descended finite base change. -/
theorem sum_localFinSepDegree_nsmul_baseChange
    {A B N M : Type*} [Field A] [Field B] [Field N]
    [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N]
    [FiniteDimensional B N] [AddCommMonoid M]
    (E : IntermediateField A N) [FiniteDimensional A E]
    (hgen : IntermediateField.adjoin B (E : Set N) = ⊤)
    (hsep : Field.finSepDegree A E = Field.finSepDegree B N)
    (y : AbsoluteValue B ℝ) (x : AbsoluteValue A ℝ) (hxy : y.restriction A = x)
    [Fintype {w : AbsoluteValue N ℝ // w.restriction B = y}]
    [Fintype {v : AbsoluteValue E ℝ // v.restriction A = x}]
    (φ : AbsoluteValue E ℝ → M) :
    (∑ w : {w : AbsoluteValue N ℝ // w.restriction B = y},
      Field.finSepDegree (w.val.restriction B).Completion w.val.Completion •
        φ (w.val.restriction E)) =
    ∑ v : {v : AbsoluteValue E ℝ // v.restriction A = x},
      Field.finSepDegree (v.val.restriction A).Completion v.val.Completion • φ v.val := by
  classical
  subst x
  obtain ⟨u, hu⟩ := exists_extension (L := AlgebraicClosure B) y
  have huA : u.restriction A = y.restriction A := by
    ext a
    change u (algebraMap A (AlgebraicClosure B) a) = y (algebraMap A B a)
    rw [IsScalarTower.algebraMap_apply A B (AlgebraicClosure B)]
    exact congrArg (fun v : AbsoluteValue B ℝ ↦ v (algebraMap A B a)) hu
  rw [sum_localFinSepDegree_nsmul_eq_sum_embeddings y u hu
      (fun w ↦ φ (w.restriction E)),
    sum_localFinSepDegree_nsmul_eq_sum_embeddings (y.restriction A) u huA φ]
  exact (Equiv.ofBijective _ (IntermediateField.bijective_restrict_embeddings_of_adjoin_eq_top
    (C := AlgebraicClosure B) E hgen hsep)).sum_comp
      (fun σ : E →ₐ[A] AlgebraicClosure B ↦ φ (u.pullback σ.toRingHom))

end AbsoluteValue
