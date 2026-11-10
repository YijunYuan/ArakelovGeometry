/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DeterminantMap
public import ArakelovGeometry.Analysis.DeterminantExactSequence
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# The canonical determinant map for a subspace and quotient

The map uses the existing top exterior powers and the canonical equality
between the sum of the two ranks and the ambient rank. Its adapted-coordinate
construction is independent of both chosen bases.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] (W : Submodule K E)

/-- Rank additivity for the subspace and its actual quotient. -/
theorem finrank_subspace_add_quotient :
    Module.finrank K W + Module.finrank K (E ⧸ W) = Module.finrank K E := by
  rw [add_comm, W.finrank_quotient_add_finrank]

/-- The canonical exact-sequence map on the existing determinant lines. -/
def determinantSequenceEquiv :
    ((⋀[K]^(Module.finrank K W) W) ⊗[K]
      (⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W))) ≃ₗ[K]
        (⋀[K]^(Module.finrank K E) E) :=
  (determinantSequenceEquivOfBases W (Module.finBasis K W)
    (Module.finBasis K (E ⧸ W))).trans
      (exteriorPowerDegreeEquiv K E (finrank_subspace_add_quotient W))

/-- Every adapted-basis construction gives the canonical map. -/
theorem determinantSequenceEquiv_eq_of_bases
    (bW : Module.Basis (Fin (Module.finrank K W)) K W)
    (bQ : Module.Basis (Fin (Module.finrank K (E ⧸ W))) K (E ⧸ W)) :
    determinantSequenceEquiv W =
      (determinantSequenceEquivOfBases W bW bQ).trans
        (exteriorPowerDegreeEquiv K E (finrank_subspace_add_quotient W)) := by
  unfold determinantSequenceEquiv
  rw [determinantSequenceEquivOfBases_eq W (Module.finBasis K W)
    (Module.finBasis K (E ⧸ W)) bW bQ]

/-- The canonical map sends two wedges to the ordered wedge of subspace
vectors followed by arbitrary lifts of the quotient vectors. -/
theorem determinantSequenceEquiv_ιMulti
    (w : Fin (Module.finrank K W) → W)
    (v : Fin (Module.finrank K (E ⧸ W)) → E) :
    determinantSequenceEquiv W
      (exteriorPower.ιMulti K (Module.finrank K W) w ⊗ₜ[K]
        exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) (fun j ↦ W.mkQ (v j))) =
      exteriorPower.ιMulti K (Module.finrank K E)
        (fun i ↦ Fin.append (fun j ↦ (w j : E)) v
          ((finCongr (finrank_subspace_add_quotient W)).symm i)) := by
  simp only [determinantSequenceEquiv, LinearEquiv.trans_apply,
    determinantSequenceEquivOfBases_ιMulti, exteriorPowerDegreeEquiv_ιMulti]

variable (L : Type*) [Field L] [Algebra K L]

/-- The same canonical map on actual scalar-extended exterior powers. -/
def determinantSequenceEquivCompleted :
    ((⋀[L]^(Module.finrank K W) (L ⊗[K] W)) ⊗[L]
      (⋀[L]^(Module.finrank K (E ⧸ W)) (L ⊗[K] (E ⧸ W)))) ≃ₗ[L]
        (⋀[L]^(Module.finrank K E) (L ⊗[K] E)) :=
  ((TensorProduct.congr
    (exteriorBaseChangeEquiv K L W (Module.finrank K W)).symm
    (exteriorBaseChangeEquiv K L (E ⧸ W) (Module.finrank K (E ⧸ W))).symm).trans
      (TensorProduct.AlgebraTensorModule.distribBaseChange K L _ _).symm).trans
        (((determinantSequenceEquiv W).baseChange K L).trans
          (exteriorBaseChangeEquiv K L E (Module.finrank K E)))

/-- Scalar extension retains the wedge formula on all original vectors. -/
theorem determinantSequenceEquivCompleted_ιMulti_one_tmul
    (w : Fin (Module.finrank K W) → W)
    (v : Fin (Module.finrank K (E ⧸ W)) → E) :
    determinantSequenceEquivCompleted W L
      (exteriorPower.ιMulti L (Module.finrank K W) (fun i ↦ (1 : L) ⊗ₜ[K] w i) ⊗ₜ[L]
        exteriorPower.ιMulti L (Module.finrank K (E ⧸ W))
          (fun j ↦ (1 : L) ⊗ₜ[K] W.mkQ (v j))) =
      exteriorPower.ιMulti L (Module.finrank K E)
        (fun i ↦ (1 : L) ⊗ₜ[K]
          Fin.append (fun j ↦ (w j : E)) v
            ((finCongr (finrank_subspace_add_quotient W)).symm i)) := by
  simp only [determinantSequenceEquivCompleted, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, exteriorBaseChangeEquiv_symm_ιMulti_tmul,
    Finset.prod_const_one, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    one_mul, LinearEquiv.baseChange_tmul, determinantSequenceEquiv_ιMulti,
    exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]

/-- The scalar-extended determinant map has the canonical wedge formula
for arbitrary completed vectors and arbitrary completed quotient lifts. -/
theorem determinantSequenceEquivCompleted_ιMulti
    (w : Fin (Module.finrank K W) → L ⊗[K] W)
    (v : Fin (Module.finrank K (E ⧸ W)) → L ⊗[K] E) :
    determinantSequenceEquivCompleted W L
      (exteriorPower.ιMulti L (Module.finrank K W) w ⊗ₜ[L]
        exteriorPower.ιMulti L (Module.finrank K (E ⧸ W))
          (fun j ↦ W.mkQ.baseChange L (v j))) =
      exteriorPower.ιMulti L (Module.finrank K E)
        (fun i ↦ Fin.append (fun j ↦ W.subtype.baseChange L (w j)) v
          ((finCongr (finrank_subspace_add_quotient W)).symm i)) := by
  classical
  obtain ⟨P, hP⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let f : MultilinearMap L
      (fun _ : Fin (Module.finrank K W) ⊕ Fin (Module.finrank K (E ⧸ W)) ↦ L ⊗[K] E)
      (⋀[L]^(Module.finrank K E) (L ⊗[K] E)) :=
    (determinantSequenceEquivCompleted W L).toLinearMap.compMultilinearMap
      (((exteriorPower.ιMulti L (Module.finrank K W)).toMultilinearMap.compLinearMap
        (fun _ ↦ P.baseChange L)).domCoprod
          ((exteriorPower.ιMulti L (Module.finrank K (E ⧸ W))).toMultilinearMap.compLinearMap
            (fun _ ↦ W.mkQ.baseChange L)))
  let e := (finCongr (finrank_subspace_add_quotient W)).symm.trans finSumFinEquiv.symm
  let g : MultilinearMap L
      (fun _ : Fin (Module.finrank K W) ⊕ Fin (Module.finrank K (E ⧸ W)) ↦ L ⊗[K] E)
      (⋀[L]^(Module.finrank K E) (L ⊗[K] E)) :=
    ((exteriorPower.ιMulti L (Module.finrank K E)).toMultilinearMap.domDomCongr e).compLinearMap
      (Sum.elim (fun _ ↦ (W.subtype.comp P).baseChange L) (fun _ ↦ LinearMap.id))
  have hfg : f = g := by
    apply Module.Basis.ext_multilinear (fun _ ↦ (Module.finBasis K E).baseChange L)
    intro j
    simp only [f, g, LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
      MultilinearMap.compLinearMap_apply,
      Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
    change determinantSequenceEquivCompleted W L
      (exteriorPower.ιMulti L (Module.finrank K W)
        (fun i ↦ (1 : L) ⊗ₜ[K] P (Module.finBasis K E (j (Sum.inl i)))) ⊗ₜ[L]
      exteriorPower.ιMulti L (Module.finrank K (E ⧸ W))
        (fun i ↦ (1 : L) ⊗ₜ[K] W.mkQ (Module.finBasis K E (j (Sum.inr i))))) = _
    rw [determinantSequenceEquivCompleted_ιMulti_one_tmul W L
      (fun i ↦ P (Module.finBasis K E (j (Sum.inl i))))
      (fun i ↦ Module.finBasis K E (j (Sum.inr i)))]
    change _ = exteriorPower.ιMulti L (Module.finrank K E)
      (fun i ↦ (Sum.elim (fun _ ↦ (W.subtype.comp P).baseChange L)
        (fun _ ↦ LinearMap.id) (e i))
          ((1 : L) ⊗ₜ[K] Module.finBasis K E (j (e i))))
    congr 1
    funext i
    simp only [e, Equiv.trans_apply]
    obtain ⟨u, hu⟩ := finSumFinEquiv.surjective
      ((finCongr (finrank_subspace_add_quotient W)).symm i)
    rw [← hu]
    cases u <;> simp
  have hPc : (P.baseChange L).comp (W.subtype.baseChange L) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hP, LinearMap.baseChange_id]
  have hPx (x : L ⊗[K] W) : P.baseChange L (W.subtype.baseChange L x) = x :=
    DFunLike.congr_fun hPc x
  have he := DFunLike.congr_fun hfg (Sum.elim (fun j ↦ W.subtype.baseChange L (w j)) v)
  calc
    _ = g (Sum.elim (fun j ↦ W.subtype.baseChange L (w j)) v) := by
      simpa [f, hPx] using he
    _ = _ := by
      change exteriorPower.ιMulti L (Module.finrank K E)
        (fun i ↦ (Sum.elim (fun _ ↦ (W.subtype.comp P).baseChange L)
          (fun _ ↦ LinearMap.id) (e i))
            (Sum.elim (fun j ↦ W.subtype.baseChange L (w j)) v (e i))) =
        exteriorPower.ιMulti L (Module.finrank K E)
          (fun i ↦ Fin.append (fun j ↦ W.subtype.baseChange L (w j)) v
            ((finCongr (finrank_subspace_add_quotient W)).symm i))
      congr 1
      funext i
      simp only [e, Equiv.trans_apply]
      obtain ⟨u, hu⟩ := finSumFinEquiv.surjective
        ((finCongr (finrank_subspace_add_quotient W)).symm i)
      rw [← hu]
      cases u <;> simp [LinearMap.baseChange_comp, hPx]

end

end ArakelovGeometry
