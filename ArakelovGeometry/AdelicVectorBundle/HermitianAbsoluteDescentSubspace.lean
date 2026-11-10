/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismSubspace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Actual finite Galois descent of scalar-extended subspaces

Trace-dual rational coordinates descend every Galois-stable actual tensor
subspace. This is algebraic infrastructure for Hermitian flag descent; it does
not assume or prove that a particular Harder--Narasimhan term is stable.
-/

@[expose] public section

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry
namespace HermitianAbsoluteDescent
variable {K L E : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E]


/-- The actual rational inverse image of an extension-field subspace. -/
def rationalPart (W : Submodule L (L ⊗[K] E)) : Submodule K E :=
  (W.restrictScalars K).comap (TensorProduct.mk K L E 1)

/-- A genuine original subspace has a stable actual scalar extension. -/
theorem scalarExtensionSemilinearEquiv_mem_baseChange (U : Submodule K E)
    (σ : L ≃ₐ[K] L) (x : L ⊗[K] E) (hx : x ∈ U.baseChange L) :
    scalarExtensionSemilinearEquiv σ x ∈ U.baseChange L := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨TensorProduct.map σ.toLinearMap (LinearMap.id : U →ₗ[K] U) y, ?_⟩
  change U.subtype.baseChange L
      (TensorProduct.map σ.toLinearMap (LinearMap.id : U →ₗ[K] U) y) =
    TensorProduct.map σ.toLinearMap (LinearMap.id : E →ₗ[K] E) (U.subtype.baseChange L y)
  induction y using TensorProduct.inductionOn with
  | tmul a e => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Trace-dual coefficient extraction is an actual sum of Galois images. -/
theorem one_tmul_coordinate_eq_galois_sum [FiniteDimensional K L] [IsGalois K L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (x : L ⊗[K] E) (i : ι) :
    (1 : L) ⊗ₜ[K] ((TensorProduct.equivFinsuppOfBasisLeft b) x i) =
      ∑ σ : L ≃ₐ[K] L, σ (b.traceDual i) • scalarExtensionSemilinearEquiv σ x := by
  let := Fintype.ofFinite ι
  have hcoord (a : L) : b.repr a i = Algebra.trace K L (b.traceDual i * a) := by
    simpa only [b.traceDual_traceDual, Algebra.traceForm_apply, mul_comm]
      using b.traceDual.traceDual_repr_apply a i
  induction x using TensorProduct.inductionOn with
  | tmul a e =>
    simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, hcoord,
      scalarExtensionSemilinearEquiv_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      ← map_mul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms]
    simp only [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, TensorProduct.tmul_add, hx, hy,
      smul_add, Finset.sum_add_distrib]


/-- Every stable actual subspace is the scalar extension of its rational inverse image. -/
theorem baseChange_rationalPart_eq_of_stable [FiniteDimensional K L] [IsGalois K L]
    (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    (rationalPart W).baseChange L = W := by
  classical
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    exact he
  · intro x hx
    let b := Module.finBasis K L
    let c := TensorProduct.equivFinsuppOfBasisLeft b x
    have hc (i) : c i ∈ rationalPart W := by
      change (1 : L) ⊗ₜ[K] (TensorProduct.equivFinsuppOfBasisLeft b x i) ∈ W
      rw [one_tmul_coordinate_eq_galois_sum]
      exact W.sum_mem fun σ _ => W.smul_mem _ (hW σ x hx)
    have hrec : c.sum (fun i e => b i ⊗ₜ[K] e) = x := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply x
    rw [← hrec]
    exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (hc i)

/-- The descended actual subspace is unique, rather than chosen in a descent certificate. -/
theorem existsUnique_baseChange_eq_of_stable [FiniteDimensional K L] [IsGalois K L]
    (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    ∃! U : Submodule K E, U.baseChange L = W := by
  refine ⟨rationalPart W, baseChange_rationalPart_eq_of_stable W hW, ?_⟩
  intro U hU
  exact Submodule.baseChange_injective
    (hU.trans (baseChange_rationalPart_eq_of_stable W hW).symm)

/-- Descent recovers a genuine original subspace exactly. -/
theorem rationalPart_baseChange [FiniteDimensional K L] [IsGalois K L]
    (U : Submodule K E) : rationalPart (U.baseChange L) = U := by
  apply Submodule.baseChange_injective (A := L)
  exact baseChange_rationalPart_eq_of_stable (U.baseChange L)
    (scalarExtensionSemilinearEquiv_mem_baseChange U)

/-- Actual finite Galois descent preserves each actual dimension. -/
theorem finrank_rationalPart_eq_of_stable [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K E] (W : Submodule L (L ⊗[K] E))
    (hW : ∀ (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ W →
      scalarExtensionSemilinearEquiv σ x ∈ W) :
    Module.finrank K (rationalPart W) = Module.finrank L W := by
  calc
    Module.finrank K (rationalPart W) =
        Module.finrank L (L ⊗[K] rationalPart W) := Module.finrank_baseChange.symm
    _ = Module.finrank L ((rationalPart W).baseChange L) :=
      (Submodule.toBaseChange.toLinearEquiv L (rationalPart W)).finrank_eq
    _ = Module.finrank L W := congrArg (fun A : Submodule L (L ⊗[K] E) =>
      Module.finrank L A) (baseChange_rationalPart_eq_of_stable W hW)


/-- A stable actual strict exhaustive flag descends with literal tensor equalities and ranks. -/
theorem exists_descended_strict_flag [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K E] (n : ℕ) (A : Fin (n + 1) → Submodule L (L ⊗[K] E))
    (hstable : ∀ i (σ : L ≃ₐ[K] L) (x : L ⊗[K] E), x ∈ A i →
      scalarExtensionSemilinearEquiv σ x ∈ A i)
    (hA : StrictMono A) (hbot : A 0 = ⊥) (htop : A (Fin.last n) = ⊤) :
    ∃ U : Fin (n + 1) → Submodule K E,
      (∀ i, (U i).baseChange L = A i) ∧
      (∀ i, Module.finrank K (U i) = Module.finrank L (A i)) ∧
      StrictMono U ∧ U 0 = ⊥ ∧ U (Fin.last n) = ⊤ := by
  let U := fun i => rationalPart (A i)
  have he (i) : (U i).baseChange L = A i :=
    baseChange_rationalPart_eq_of_stable (A i) (hstable i)
  refine ⟨U, he, fun i => finrank_rationalPart_eq_of_stable (A i) (hstable i), ?_, ?_, ?_⟩
  · intro i j hij
    apply (Submodule.baseChangeOrderEmbedding K E L).lt_iff_lt.mp
    change (U i).baseChange L < (U j).baseChange L
    rw [he i, he j]
    exact hA hij
  · apply Submodule.baseChange_injective (A := L)
    rw [he 0, hbot, Submodule.baseChange_bot]
  · apply Submodule.baseChange_injective (A := L)
    rw [he (Fin.last n), htop, Submodule.baseChange_top]

end HermitianAbsoluteDescent
end ArakelovGeometry
