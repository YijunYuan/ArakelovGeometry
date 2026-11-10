/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.DeterminantSequenceOperator
import ArakelovGeometry.AdelicVectorBundle.DeterminantDualNorm
import ArakelovGeometry.AdelicVectorBundle.DeterminantFunctor
import ArakelovGeometry.AdelicVectorBundle.DualRestriction
import ArakelovGeometry.AdelicVectorBundle.MajorantDiscrepancyBound

/-!
# Duality of exact-sequence determinant maps

Adapted bases identify the actual primal and dual determinant maps. Reversing
the two end spaces contributes a permutation sign of norm one.
Canonical annihilator isometries transport determinant contraction to the
actual dual end spaces.
-/

open scoped TensorProduct

noncomputable section

namespace ArakelovGeometry

section AdaptedBasis

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  (W : Submodule K E) {ι κ : Type*} [Finite ι] [Finite κ]
  [DecidableEq ι] [DecidableEq κ]
  (bW : Module.Basis ι K W) (bQ : Module.Basis κ K (E ⧸ W))

/-- The quotient block of an adapted dual basis is the actual pullback of
the quotient dual basis along the quotient map. -/
theorem sumQuot_dualBasis_inr (j : κ) :
    (bW.sumQuot bQ).dualBasis (Sum.inr j) = (bQ.dualBasis j).comp W.mkQ := by
  apply LinearMap.ext
  intro x
  simp only [Module.Basis.coe_dualBasis, LinearMap.comp_apply]
  simp

/-- Restriction of the subspace block of an adapted dual basis is the actual
subspace dual basis. -/
theorem sumQuot_dualBasis_inl_comp_subtype (i : ι) :
    ((bW.sumQuot bQ).dualBasis (Sum.inl i)).comp W.subtype = bW.dualBasis i := by
  apply LinearMap.ext
  intro x
  simp only [Module.Basis.coe_dualBasis, LinearMap.comp_apply]
  simp

end AdaptedBasis

section Pairing

variable {L : Type*} [NormedField L] {V : Type*} [AddCommGroup V] [Module L V]
  {n : ℕ}

/-- Permuting the dual wedge leaves the norm of the actual exterior
pairing unchanged. -/
theorem norm_exteriorPairingDual_permute
    (f : Fin n → Module.Dual L V) (x : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    ‖_root_.exteriorPower.pairingDual L V n
      (_root_.exteriorPower.ιMulti L n (f ∘ σ))
      (_root_.exteriorPower.ιMulti L n x)‖ =
      ‖_root_.exteriorPower.pairingDual L V n
        (_root_.exteriorPower.ιMulti L n f) (_root_.exteriorPower.ιMulti L n x)‖ := by
  simp only [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
  change ‖((Matrix.of fun i j ↦ f j (x i)).submatrix id σ).det‖ = _
  rw [Matrix.det_permute', norm_mul]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : L)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]

/-- A permutation of a basis dual wedge pairs with the original basis wedge
with norm one, including the empty wedge. -/
theorem norm_exteriorPairingDual_permuted_dualBasis
    (b : Module.Basis (Fin n) L V) (σ : Equiv.Perm (Fin n)) :
    ‖_root_.exteriorPower.pairingDual L V n
      (_root_.exteriorPower.ιMulti L n (fun j ↦ b.dualBasis (σ j)))
      (_root_.exteriorPower.ιMulti L n b)‖ = 1 := by
  rw [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
  have hm : (Matrix.of fun i j ↦ b.dualBasis (σ j) (b i)) =
      (1 : Matrix (Fin n) (Fin n) L).submatrix id σ := by
    ext i j
    simp [Matrix.one_apply, Finsupp.single_apply]
  rw [hm, Matrix.det_permute', Matrix.det_one, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

end Pairing

section BlockPairing

variable {L : Type*} [NormedField L] {V : Type*} [AddCommGroup V] [Module L V]
  {a b : ℕ}

/-- The actual pairing of appended primal and dual wedges is the product
of the end pairings whenever the quotient functionals vanish on the
subspace vectors. Arbitrary quotient lifts and empty tuples are allowed. -/
theorem norm_exteriorPairingDual_append
    (w : Fin a → V) (v : Fin b → V)
    (f : Fin a → Module.Dual L V) (g : Fin b → Module.Dual L V)
    (hg : ∀ i j, g j (w i) = 0) :
    ‖_root_.exteriorPower.pairingDual L V (a + b)
      (_root_.exteriorPower.ιMulti L (a + b) (Fin.append f g))
      (_root_.exteriorPower.ιMulti L (a + b) (Fin.append w v))‖ =
      ‖_root_.exteriorPower.pairingDual L V a (_root_.exteriorPower.ιMulti L a f)
        (_root_.exteriorPower.ιMulti L a w)‖ *
      ‖_root_.exteriorPower.pairingDual L V b (_root_.exteriorPower.ιMulti L b g)
        (_root_.exteriorPower.ιMulti L b v)‖ := by
  classical
  simp only [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
  let A := Matrix.of fun i j ↦ f j (w i)
  let C := Matrix.of fun i j ↦ f j (v i)
  let D := Matrix.of fun i j ↦ g j (v i)
  have hm : (Matrix.of fun i j ↦ Fin.append f g j (Fin.append w v i)) =
      (Matrix.fromBlocks A 0 C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [A, C, D, Matrix.fromBlocks, hg]
  rw [hm, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, norm_mul]

/-- Reversing the end order in the dual exact sequence preserves the norm
of its pairing with the primal exact-sequence wedge. -/
theorem norm_exteriorPairingDual_append_reverse
    (w : Fin a → V) (v : Fin b → V)
    (f : Fin a → Module.Dual L V) (g : Fin b → Module.Dual L V)
    (hg : ∀ i j, g j (w i) = 0) :
    ‖_root_.exteriorPower.pairingDual L V (a + b)
      (_root_.exteriorPower.ιMulti L (a + b)
        (fun j ↦ Fin.append g f (finCongr (Nat.add_comm a b) j)))
      (_root_.exteriorPower.ιMulti L (a + b) (Fin.append w v))‖ =
      ‖_root_.exteriorPower.pairingDual L V a (_root_.exteriorPower.ιMulti L a f)
        (_root_.exteriorPower.ιMulti L a w)‖ *
      ‖_root_.exteriorPower.pairingDual L V b (_root_.exteriorPower.ιMulti L b g)
        (_root_.exteriorPower.ιMulti L b v)‖ := by
  let e : Fin (a + b) ≃ Fin (b + a) :=
    finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin a) (Fin b)).trans finSumFinEquiv)
  let σ : Equiv.Perm (Fin (a + b)) := (finCongr (Nat.add_comm a b)).trans e.symm
  have he (i : Fin (a + b)) : Fin.append g f (e i) = Fin.append f g i := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i <;> simp [e]
  have hf : (fun j ↦ Fin.append g f (finCongr (Nat.add_comm a b) j)) =
      (Fin.append f g) ∘ σ := by
    funext j
    simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, Function.comp_apply]
      using he (σ j)
  rw [hf, norm_exteriorPairingDual_permute]
  exact norm_exteriorPairingDual_append w v f g hg

end BlockPairing

section CompletedPairing

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The canonical completed determinant pairing evaluates pure tensors by
scalar extension of the actual rational determinant pairing. -/
theorem completedDeterminantPairing_tmul (a b : L)
    (z : ⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E))
    (w : ⋀[K]^(Module.finrank K E) E) :
    completedDeterminantPairing K L E (a ⊗ₜ[K] z) (b ⊗ₜ[K] w) =
      a * b * algebraMap K L (determinantDualEquiv K E z w) := by
  simp only [completedDeterminantPairing, LinearMap.comp_apply,
    LinearMap.baseChange_tmul, LinearEquiv.coe_toLinearMap,
    dualBaseChangeEquiv_tmul_apply_tmul]

end CompletedPairing

section DegreeTransport

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  {F : Type*} [AddCommGroup F] [Module K F]

private theorem exteriorDegreeEquiv_symm_apply {n m : ℕ} (h : n = m)
    (z : ⋀[K]^m E) :
    (exteriorPowerDegreeEquiv K E h).symm z = exteriorPowerDegreeEquiv K E h.symm z := by
  subst m
  rfl

private theorem exteriorDegreeEquiv_trans_apply {n m r : ℕ}
    (h : n = m) (h' : m = r) (z : ⋀[K]^n E) :
    exteriorPowerDegreeEquiv K E h' (exteriorPowerDegreeEquiv K E h z) =
      exteriorPowerDegreeEquiv K E (h.trans h') z := by
  subst m
  subst r
  rfl

private theorem exteriorDegreeEquiv_map_ιMulti {n m r : ℕ}
    (h : n = m) (h' : m = r) (f : E →ₗ[K] F) (x : Fin n → E) :
    exteriorPowerDegreeEquiv K F h'
      (_root_.exteriorPower.map m f
        (exteriorPowerDegreeEquiv K E h (_root_.exteriorPower.ιMulti K n x))) =
      exteriorPowerDegreeEquiv K F (h.trans h')
        (_root_.exteriorPower.ιMulti K n (fun i ↦ f (x i))) := by
  subst m
  subst r
  simp only [exteriorPowerDegreeEquiv_rfl, LinearEquiv.refl_apply,
    _root_.exteriorPower.map_apply_ιMulti, Function.comp_def]

private theorem determinantEquiv_degreeTransport_ιMulti (e : E ≃ₗ[K] F) {n : ℕ}
    (h : n = Module.finrank K E) (x : Fin n → E) :
    determinantEquiv K e
      (exteriorPowerDegreeEquiv K E h (_root_.exteriorPower.ιMulti K n x)) =
      exteriorPowerDegreeEquiv K F (h.trans e.finrank_eq)
        (_root_.exteriorPower.ιMulti K n (fun i ↦ e (x i))) :=
  exteriorDegreeEquiv_map_ιMulti h e.finrank_eq e.toLinearMap x

private theorem exteriorPairingDual_degreeTransport {n m : ℕ} (h : n = m)
    (z : ⋀[K]^n (Module.Dual K E)) (w : ⋀[K]^n E) :
    _root_.exteriorPower.pairingDual K E m
      (exteriorPowerDegreeEquiv K (Module.Dual K E) h z)
      (exteriorPowerDegreeEquiv K E h w) =
      _root_.exteriorPower.pairingDual K E n z w := by
  subst m
  rfl

end DegreeTransport

section DualSequence

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The actual dual basis wedge in the determinant of the dual space. -/
def determinantDualBasisWedge
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    ⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E) :=
  (exteriorPowerDegreeEquiv K (Module.Dual K E) Subspace.dual_finrank_eq).symm
    (_root_.exteriorPower.ιMulti K (Module.finrank K E) b.dualBasis)

/-- The basis wedge and its actual dual basis wedge pair to one,
including the empty basis. -/
theorem determinantDualBasisWedge_pairing
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    determinantDualEquiv K E (determinantDualBasisWedge b)
      (_root_.exteriorPower.ιMulti K (Module.finrank K E) b) = 1 := by
  simpa only [determinantDualBasisWedge, determinantDualEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, exteriorDualEquiv_apply] using
    exteriorPairingDual_dualBasis (K := K) (E := E) (Module.finrank K E) b

private theorem determinantSequenceEquiv_degreeTransport_ιMulti
    (W : Submodule K E) {n m : ℕ}
    (hn : n = Module.finrank K W) (hm : m = Module.finrank K (E ⧸ W))
    (w : Fin n → W) (v : Fin m → E) :
    determinantSequenceEquiv W
      (exteriorPowerDegreeEquiv K W hn (_root_.exteriorPower.ιMulti K n w) ⊗ₜ[K]
        exteriorPowerDegreeEquiv K (E ⧸ W) hm
          (_root_.exteriorPower.ιMulti K m (fun j ↦ W.mkQ (v j)))) =
      exteriorPowerDegreeEquiv K E
        ((congrArg₂ Nat.add hn hm).trans (finrank_subspace_add_quotient W))
        (_root_.exteriorPower.ιMulti K (n + m) (Fin.append (fun i ↦ (w i : E)) v)) := by
  subst n
  subst m
  change determinantSequenceEquiv W
    (_root_.exteriorPower.ιMulti K (Module.finrank K W) w ⊗ₜ[K]
      _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) (fun j ↦ W.mkQ (v j))) =
    exteriorPowerDegreeEquiv K E (finrank_subspace_add_quotient W)
      (_root_.exteriorPower.ιMulti K (Module.finrank K W + Module.finrank K (E ⧸ W))
        (Fin.append (fun i ↦ (w i : E)) v))
  exact (determinantSequenceEquiv_ιMulti W w v).trans
    (exteriorPowerDegreeEquiv_ιMulti K E (finrank_subspace_add_quotient W)
      (Fin.append (fun i ↦ (w i : E)) v)).symm

/-- The actual determinant map of the dual exact sequence, with its two
end determinants identified by the canonical annihilator equivalences. -/
def determinantDualSequenceEquiv (W : Submodule K E) :
    ((⋀[K]^(Module.finrank K (Module.Dual K (E ⧸ W))) (Module.Dual K (E ⧸ W)))
      ⊗[K] (⋀[K]^(Module.finrank K (Module.Dual K W)) (Module.Dual K W))) ≃ₗ[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)) :=
  (TensorProduct.congr (determinantEquiv K W.dualQuotEquivDualAnnihilator)
    (determinantEquiv K (Subspace.quotAnnihilatorEquiv W).symm)).trans
      (determinantSequenceEquiv W.dualAnnihilator)

private theorem finrank_dual_quotient_add_dual_subspace (W : Submodule K E) :
    Module.finrank K (E ⧸ W) + Module.finrank K W =
      Module.finrank K (Module.Dual K E) :=
  (Nat.add_comm _ _).trans
    ((finrank_subspace_add_quotient W).trans Subspace.dual_finrank_eq.symm)

private theorem determinantDualSequenceEquiv_degreeTransport_ιMulti
    (W : Submodule K E)
    (g : Fin (Module.finrank K (E ⧸ W)) → Module.Dual K (E ⧸ W))
    (f : Fin (Module.finrank K W) → Module.Dual K E) :
    determinantDualSequenceEquiv W
      (exteriorPowerDegreeEquiv K (Module.Dual K (E ⧸ W))
          Subspace.dual_finrank_eq.symm
          (_root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) g) ⊗ₜ[K]
        exteriorPowerDegreeEquiv K (Module.Dual K W) Subspace.dual_finrank_eq.symm
          (_root_.exteriorPower.ιMulti K (Module.finrank K W)
            (fun i ↦ (f i).comp W.subtype))) =
      exteriorPowerDegreeEquiv K (Module.Dual K E)
        (finrank_dual_quotient_add_dual_subspace W)
        (_root_.exteriorPower.ιMulti K
          (Module.finrank K (E ⧸ W) + Module.finrank K W)
          (Fin.append (fun j ↦ (g j).comp W.mkQ) f)) := by
  let A := W.dualAnnihilator
  let eQ := W.dualQuotEquivDualAnnihilator
  let eW := Subspace.quotAnnihilatorEquiv W
  have hQ : Module.finrank K (E ⧸ W) = Module.finrank K A :=
    Subspace.dual_finrank_eq.symm.trans eQ.finrank_eq
  have hW : Module.finrank K W = Module.finrank K (Module.Dual K E ⧸ A) :=
    Subspace.dual_finrank_eq.symm.trans eW.symm.finrank_eq
  have hf : (fun i ↦ eW.symm ((f i).comp W.subtype)) = (fun i ↦ A.mkQ (f i)) := by
    funext i
    apply eW.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (Subspace.quotAnnihilatorEquiv_apply W (f i)).symm
  have hg : (fun j ↦ (eQ (g j) : Module.Dual K E)) =
      (fun j ↦ (g j).comp W.mkQ) := by
    funext j
    apply LinearMap.ext
    intro x
    exact Submodule.dualQuotEquivDualAnnihilator_apply W (g j) x
  simp only [determinantDualSequenceEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, determinantEquiv_degreeTransport_ιMulti]
  change determinantSequenceEquiv A
    (exteriorPowerDegreeEquiv K A hQ
        (_root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) (fun j ↦ eQ (g j))) ⊗ₜ[K]
      exteriorPowerDegreeEquiv K (Module.Dual K E ⧸ A) hW
        (_root_.exteriorPower.ιMulti K (Module.finrank K W)
          (fun i ↦ eW.symm ((f i).comp W.subtype)))) = _
  rw [hf, determinantSequenceEquiv_degreeTransport_ιMulti]
  simp only [hg]

namespace NormFamily

variable {S : AdelicStructure K} (ξ : NormFamily S E)

/-- The actual dual exact-sequence determinant map contracts rational
completed tensors under the local functional-extension hypothesis,
including either zero-dimensional end. -/
theorem determinantDualSequence_norm_rational_tmul_le (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (z : ⋀[K]^(Module.finrank K (Module.Dual K (E ⧸ W))) (Module.Dual K (E ⧸ W)))
    (u : ⋀[K]^(Module.finrank K (Module.Dual K W)) (Module.Dual K W)) :
    ξ.dual.determinant.norm ω
      (1 ⊗ₜ[K] determinantDualSequenceEquiv W (z ⊗ₜ[K] u)) ≤
      (ξ.quotient W).dual.determinant.norm ω (1 ⊗ₜ[K] z) *
        (ξ.restrict W).dual.determinant.norm ω (1 ⊗ₜ[K] u) := by
  let A := W.dualAnnihilator
  let eQ := W.dualQuotEquivDualAnnihilator
  let eW := Subspace.quotAnnihilatorEquiv W
  have hQ := ((ξ.quotient W).dual).determinantEquiv_norm_eq
    (ξ.dual.restrict A) ω eQ
      (fun x ↦ (ξ.quotient_dual_annihilator_norm_eq W ω x).symm) (1 ⊗ₜ[K] z)
  have hW (x : (S.ϕ ω).Completion ⊗[K] Module.Dual K W) :
      (ξ.dual.quotient A).norm ω
        (eW.symm.toLinearMap.baseChange (S.ϕ ω).Completion x) =
      (ξ.restrict W).dual.norm ω x := by
    have h := ξ.dual_quotient_annihilator_norm_eq_of_isRCLike_or_ultrametric W ω hω
      (eW.symm.toLinearMap.baseChange (S.ϕ ω).Completion x)
    change (ξ.dual.quotient A).norm ω
      ((eW.baseChange K (S.ϕ ω).Completion).symm x) =
      (ξ.restrict W).dual.norm ω
        ((eW.baseChange K (S.ϕ ω).Completion)
          ((eW.baseChange K (S.ϕ ω).Completion).symm x)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hWdet := ((ξ.restrict W).dual).determinantEquiv_norm_eq
    (ξ.dual.quotient A) ω eW.symm hW (1 ⊗ₜ[K] u)
  change (ξ.dual.restrict A).determinant.norm ω
    ((determinantEquiv K eQ).toLinearMap.baseChange
      (S.ϕ ω).Completion (1 ⊗ₜ[K] z)) = _ at hQ
  change (ξ.dual.quotient A).determinant.norm ω
    ((determinantEquiv K eW.symm).toLinearMap.baseChange
      (S.ϕ ω).Completion (1 ⊗ₜ[K] u)) = _ at hWdet
  rw [LinearMap.baseChange_tmul] at hQ hWdet
  change (ξ.dual.restrict A).determinant.norm ω
    (1 ⊗ₜ[K] determinantEquiv K eQ z) = _ at hQ
  change (ξ.dual.quotient A).determinant.norm ω
    (1 ⊗ₜ[K] determinantEquiv K eW.symm u) = _ at hWdet
  have h := ξ.dual.determinantSequence_norm_rational_tmul_le A ω
    (determinantEquiv K eQ z) (determinantEquiv K eW.symm u)
  rw [hQ, hWdet] at h
  simpa only [determinantDualSequenceEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul] using h

/-- The actual dual determinant map has operator norm at most one under
the local extension hypothesis. Its source is the existing injective
tensor norm on the two actual dual determinant lines. -/
theorem determinantDualSequence_operatorNorm_le_one (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    ((ξ.quotient W).dual.determinant.injectiveTensorPair
      (ξ.restrict W).dual.determinant).operatorNorm
      ξ.dual.determinant ω (determinantDualSequenceEquiv W).toLinearMap ≤ 1 := by
  classical
  let DQ := ⋀[K]^(Module.finrank K (Module.Dual K (E ⧸ W)))
    (Module.Dual K (E ⧸ W))
  let DW := ⋀[K]^(Module.finrank K (Module.Dual K W)) (Module.Dual K W)
  let D := (ξ.quotient W).dual.determinant.injectiveTensorPair
    (ξ.restrict W).dual.determinant
  have hQ : Module.finrank K DQ = 1 := determinant_finrank
  have hW : Module.finrank K DW = 1 := determinant_finrank
  let z := (Module.finBasisOfFinrankEq K DQ hQ) 0
  let u := (Module.finBasisOfFinrankEq K DW hW) 0
  have hz : z ≠ 0 := (Module.finBasisOfFinrankEq K DQ hQ).ne_zero 0
  have hu : u ≠ 0 := (Module.finBasisOfFinrankEq K DW hW).ne_zero 0
  have hn := ((ξ.quotient W).dual.determinant).injectiveTensorPair_norm_rational_generators
    (ξ.restrict W).dual.determinant hQ hW hz hu ω
  have hp := mul_pos ((ξ.quotient W).dual.determinant.norm_rational_pos ω hz)
    ((ξ.restrict W).dual.determinant.norm_rational_pos ω hu)
  have hzu : z ⊗ₜ[K] u ≠ 0 := by
    intro h
    rw [h, TensorProduct.tmul_zero, D.norm_zero] at hn
    linarith
  have hr : Module.finrank K (DQ ⊗[K] DW) = 1 := by
    rw [Module.finrank_tensorProduct, hQ, hW, mul_one]
  rw [D.operatorNorm_eq_div_of_finrank_one ξ.dual.determinant hr
    (determinantDualSequenceEquiv W).toLinearMap hzu ω, hn]
  apply (div_le_one hp).mpr
  exact ξ.determinantDualSequence_norm_rational_tmul_le W ω hω z u

/-- The canonical dual exact-sequence determinant map contracts every
actual completed tensor vector, including the two degree-zero end lines. -/
theorem determinantDualSequence_norm_le (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⋀[K]^(Module.finrank K (Module.Dual K (E ⧸ W))) (Module.Dual K (E ⧸ W)))
        ⊗[K] (⋀[K]^(Module.finrank K (Module.Dual K W)) (Module.Dual K W)))) :
    ξ.dual.determinant.norm ω
      ((determinantDualSequenceEquiv W).toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
      ((ξ.quotient W).dual.determinant.injectiveTensorPair
        (ξ.restrict W).dual.determinant).norm ω z := by
  let D := (ξ.quotient W).dual.determinant.injectiveTensorPair
    (ξ.restrict W).dual.determinant
  have h := D.norm_baseChange_le_operatorNorm ξ.dual.determinant ω
    (determinantDualSequenceEquiv W).toLinearMap z
  exact h.trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (ξ.determinantDualSequence_operatorNorm_le_one W ω hω)
      (D.norm_nonneg ω z)))

end NormFamily

end DualSequence

section NormedPairing
variable {K : Type*} [NormedField K] {E : Type*} [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The canonical sequence images of actual basis and dual basis wedges
pair with norm one, including both empty end bases. -/
theorem norm_determinantDualSequence_pairing_basis (W : Submodule K E)
    (bW : Module.Basis (Fin (Module.finrank K W)) K W)
    (bQ : Module.Basis (Fin (Module.finrank K (E ⧸ W))) K (E ⧸ W)) :
    ‖determinantDualEquiv K E
      (determinantDualSequenceEquiv W
        (determinantDualBasisWedge bQ ⊗ₜ[K] determinantDualBasisWedge bW))
      (determinantSequenceEquiv W
        (_root_.exteriorPower.ιMulti K (Module.finrank K W) bW ⊗ₜ[K]
          _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) bQ))‖ = 1 := by
  classical
  choose v hv using fun j ↦ W.mkQ_surjective (bQ j)
  let f : Fin (Module.finrank K W) → Module.Dual K E :=
    fun i ↦ (bW.sumQuot bQ).dualBasis (Sum.inl i)
  let g : Fin (Module.finrank K (E ⧸ W)) → Module.Dual K E :=
    fun j ↦ (bW.sumQuot bQ).dualBasis (Sum.inr j)
  have hg (j) : g j = (bQ.dualBasis j).comp W.mkQ :=
    sumQuot_dualBasis_inr W bW bQ j
  have hgg : g = (fun j ↦ (bQ.dualBasis j).comp W.mkQ) := funext hg
  let w : Fin (Module.finrank K W) → E := fun i ↦ (bW i : E)
  have hf (i) : (f i).comp W.subtype = bW.dualBasis i :=
    sumQuot_dualBasis_inl_comp_subtype W bW bQ i
  have hff : (fun i ↦ (f i).comp W.subtype) = bW.dualBasis := funext hf
  have hvv : (fun j ↦ W.mkQ (v j)) = bQ := funext hv
  have hprim := determinantSequenceEquiv_ιMulti W bW v
  have hprim' :
      determinantSequenceEquiv W
        (_root_.exteriorPower.ιMulti K (Module.finrank K W) bW ⊗ₜ[K]
          _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) bQ) =
        exteriorPowerDegreeEquiv K E (finrank_subspace_add_quotient W)
          (_root_.exteriorPower.ιMulti K
            (Module.finrank K W + Module.finrank K (E ⧸ W)) (Fin.append w v)) := by
    simpa only [hvv, exteriorPowerDegreeEquiv_ιMulti] using hprim
  have hdual :
      determinantDualSequenceEquiv W
        (determinantDualBasisWedge bQ ⊗ₜ[K] determinantDualBasisWedge bW) =
        exteriorPowerDegreeEquiv K (Module.Dual K E)
          (finrank_dual_quotient_add_dual_subspace W)
          (_root_.exteriorPower.ιMulti K
            (Module.finrank K (E ⧸ W) + Module.finrank K W) (Fin.append g f)) := by
    simpa only [determinantDualBasisWedge, exteriorDegreeEquiv_symm_apply, hff, ← hgg] using
      determinantDualSequenceEquiv_degreeTransport_ιMulti W bQ.dualBasis f
  have hwp :
      _root_.exteriorPower.pairingDual K E (Module.finrank K W)
        (_root_.exteriorPower.ιMulti K (Module.finrank K W) f)
        (_root_.exteriorPower.ιMulti K (Module.finrank K W) w) = 1 := by
    rw [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
    have hm : (Matrix.of fun i j ↦ f j (w i)) =
        Matrix.of (fun i j ↦ bW.dualBasis j (bW i)) := by
      ext i j
      change ((f j).comp W.subtype) (bW i) = bW.dualBasis j (bW i)
      rw [hf]
    rw [hm]
    simpa only [_root_.exteriorPower.pairingDual_ιMulti_ιMulti] using
      exteriorPairingDual_dualBasis (K := K) (E := W) (Module.finrank K W) bW
  have hqp :
      _root_.exteriorPower.pairingDual K E (Module.finrank K (E ⧸ W))
        (_root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) g)
        (_root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) v) = 1 := by
    rw [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
    have hm : (Matrix.of fun i j ↦ g j (v i)) =
        Matrix.of (fun i j ↦ bQ.dualBasis j (bQ i)) := by
      ext i j
      change g j (v i) = bQ.dualBasis j (bQ i)
      rw [hg]
      change bQ.dualBasis j (W.mkQ (v i)) = bQ.dualBasis j (bQ i)
      rw [hv]
    rw [hm]
    simpa only [_root_.exteriorPower.pairingDual_ιMulti_ιMulti] using
      exteriorPairingDual_dualBasis (K := K) (E := E ⧸ W) (Module.finrank K (E ⧸ W)) bQ
  have hg0 (i) (j) : g j (w i) = 0 := by
    have hz : W.mkQ (bW i : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).mpr (bW i).property
    rw [hg]
    change bQ.dualBasis j (W.mkQ (bW i)) = 0
    rw [hz, map_zero]
  rw [hdual, hprim']
  simp only [determinantDualEquiv, LinearEquiv.trans_apply, exteriorDualEquiv_apply,
    exteriorDegreeEquiv_trans_apply]
  have ht :
      exteriorPowerDegreeEquiv K (Module.Dual K E)
        ((finrank_dual_quotient_add_dual_subspace W).trans Subspace.dual_finrank_eq)
        (_root_.exteriorPower.ιMulti K
          (Module.finrank K (E ⧸ W) + Module.finrank K W) (Fin.append g f)) =
      exteriorPowerDegreeEquiv K (Module.Dual K E) (finrank_subspace_add_quotient W)
        (exteriorPowerDegreeEquiv K (Module.Dual K E)
          (Nat.add_comm (Module.finrank K (E ⧸ W)) (Module.finrank K W))
          (_root_.exteriorPower.ιMulti K
            (Module.finrank K (E ⧸ W) + Module.finrank K W) (Fin.append g f))) :=
    (exteriorDegreeEquiv_trans_apply _ _ _).symm
  rw [ht, exteriorPairingDual_degreeTransport, exteriorPowerDegreeEquiv_ιMulti]
  change ‖_root_.exteriorPower.pairingDual K E
    (Module.finrank K W + Module.finrank K (E ⧸ W))
    (_root_.exteriorPower.ιMulti K _
      (fun j ↦ Fin.append g f (finCongr
        (Nat.add_comm (Module.finrank K W) (Module.finrank K (E ⧸ W))) j)))
    (_root_.exteriorPower.ιMulti K _ (Fin.append w v))‖ = 1
  rw [norm_exteriorPairingDual_append_reverse w v f g hg0, hwp, hqp, norm_one, one_mul]
end NormedPairing

section CompletedSequencePairing

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The actual canonical primal and dual sequence images pair with norm one
on basis generators, including the two empty end bases. -/
theorem completedDeterminantDualSequence_pairing_basis_norm (W : Submodule K E) (ω : S.Ω)
    (bW : Module.Basis (Fin (Module.finrank K W)) K W)
    (bQ : Module.Basis (Fin (Module.finrank K (E ⧸ W))) K (E ⧸ W)) :
    ‖completedDeterminantPairing K (S.ϕ ω).Completion E
      (1 ⊗ₜ[K] determinantDualSequenceEquiv W
        (determinantDualBasisWedge bQ ⊗ₜ[K] determinantDualBasisWedge bW))
      (1 ⊗ₜ[K] determinantSequenceEquiv W
        (_root_.exteriorPower.ιMulti K (Module.finrank K W) bW ⊗ₜ[K]
          _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) bQ))‖ = 1 := by
  let := (S.ϕ ω).toNormedField
  rw [completedDeterminantPairing_tmul]
  simp only [one_mul]
  rw [S.norm_algebraMap_eq_absValue]
  change ‖determinantDualEquiv K E
    (determinantDualSequenceEquiv W
      (determinantDualBasisWedge bQ ⊗ₜ[K] determinantDualBasisWedge bW))
    (determinantSequenceEquiv W
      (_root_.exteriorPower.ιMulti K (Module.finrank K W) bW ⊗ₜ[K]
        _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) bQ))‖ = 1
  exact norm_determinantDualSequence_pairing_basis W bW bQ

end CompletedSequencePairing

section LocalDiscrepancy
variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem determinantBasisWedge_ne_zero
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    _root_.exteriorPower.ιMulti K (Module.finrank K E) b ≠ 0 := by
  intro h
  have hp := determinantDualBasisWedge_pairing b
  rw [h, map_zero] at hp
  exact zero_ne_one hp

private theorem determinantDualBasisWedge_ne_zero
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    determinantDualBasisWedge b ≠ 0 := by
  intro h
  have hp := determinantDualBasisWedge_pairing b
  rw [h, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

private theorem completedDeterminantDualBasisWedge_pairing (ω : S.Ω)
    (b : Module.Basis (Fin (Module.finrank K E)) K E) :
    completedDeterminantPairing K (S.ϕ ω).Completion E
      (1 ⊗ₜ[K] determinantDualBasisWedge b)
      (1 ⊗ₜ[K] _root_.exteriorPower.ιMulti K (Module.finrank K E) b) = 1 := by
  rw [completedDeterminantPairing_tmul, determinantDualBasisWedge_pairing]
  simp only [one_mul, map_one]

namespace NormFamily
variable (ξ : NormFamily S E)

private theorem inverse_norm_products_ratio
    {pW pQ qW qQ pE qE : ℝ}
    (hpW : pW ≠ 0) (hpQ : pQ ≠ 0) (hqW : qW ≠ 0) (hqQ : qQ ≠ 0) :
    (pW * qW)⁻¹ * (pQ * qQ)⁻¹ / (pE * qE)⁻¹ =
      (pE / (pW * pQ)) * (qE / (qQ * qW)) := by
  rw [div_inv_eq_mul]
  field_simp [hpW, hpQ, hqW, hqQ]

/-- A unit-norm actual determinant pairing computes intrinsic discrepancy,
so permutation signs do not affect the reciprocal norm formula. -/
theorem determinantDiscrepancy_eq_inv_norm_mul_of_norm_pairing_eq_one (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)))
    (w : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E))
    (hp : ‖completedDeterminantPairing K (S.ϕ ω).Completion E z w‖ = 1) :
    ξ.determinantDiscrepancy ω =
      (ξ.determinant.norm ω w * ξ.dual.determinant.norm ω z)⁻¹ := by
  let c := completedDeterminantPairing K (S.ϕ ω).Completion E z w
  change ‖c‖ = 1 at hp
  have hc : c ≠ 0 := by
    intro h
    have hn := hp
    rw [h, _root_.norm_zero] at hn
    exact zero_ne_one hn
  have hpair : completedDeterminantPairing K (S.ϕ ω).Completion E (c⁻¹ • z) w = 1 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, c] using inv_mul_cancel₀ hc
  have h := ξ.determinantDiscrepancy_eq_inv_norm_mul ω (c⁻¹ • z) w hpair
  rw [ξ.dual.determinant.norm_smul, norm_inv, hp, inv_one, one_mul] at h
  exact h
/-- The actual canonical primal operator is bounded below by the intrinsic
discrepancy ratio. The completed dual contraction and canonical basis
pairing supply the comparison; no pairing witness is assumed. -/
theorem determinantSequence_operatorNorm_lower_bound (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    (ξ.restrict W).determinantDiscrepancy ω *
        (ξ.quotient W).determinantDiscrepancy ω / ξ.determinantDiscrepancy ω ≤
      ((ξ.restrict W).determinant.injectiveTensorPair
        (ξ.quotient W).determinant).operatorNorm
        ξ.determinant ω (determinantSequenceEquiv W).toLinearMap := by
  classical
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let D := (ξ.restrict W).determinant.injectiveTensorPair (ξ.quotient W).determinant
  let bW := Module.finBasis K W
  let bQ := Module.finBasis K (E ⧸ W)
  let w := _root_.exteriorPower.ιMulti K (Module.finrank K W) bW
  let q := _root_.exteriorPower.ιMulti K (Module.finrank K (E ⧸ W)) bQ
  let zW := determinantDualBasisWedge bW
  let zQ := determinantDualBasisWedge bQ
  let pW := (ξ.restrict W).determinant.norm ω (1 ⊗ₜ[K] w)
  let pQ := (ξ.quotient W).determinant.norm ω (1 ⊗ₜ[K] q)
  let qW := (ξ.restrict W).dual.determinant.norm ω (1 ⊗ₜ[K] zW)
  let qQ := (ξ.quotient W).dual.determinant.norm ω (1 ⊗ₜ[K] zQ)
  let pE := ξ.determinant.norm ω (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q))
  let qE := ξ.dual.determinant.norm ω
    (1 ⊗ₜ[K] determinantDualSequenceEquiv W (zQ ⊗ₜ[K] zW))
  let a := D.operatorNorm ξ.determinant ω (determinantSequenceEquiv W).toLinearMap
  have hw : w ≠ 0 := determinantBasisWedge_ne_zero bW
  have hq : q ≠ 0 := determinantBasisWedge_ne_zero bQ
  have hzW : zW ≠ 0 := determinantDualBasisWedge_ne_zero bW
  have hzQ : zQ ≠ 0 := determinantDualBasisWedge_ne_zero bQ
  have hpW : 0 < pW := (ξ.restrict W).determinant.norm_rational_pos ω hw
  have hpQ : 0 < pQ := (ξ.quotient W).determinant.norm_rational_pos ω hq
  have hqW : 0 < qW := (ξ.restrict W).dual.determinant.norm_rational_pos ω hzW
  have hqQ : 0 < qQ := (ξ.quotient W).dual.determinant.norm_rational_pos ω hzQ
  have hdW := (ξ.restrict W).determinantDiscrepancy_eq_inv_norm_mul ω
    (1 ⊗ₜ[K] zW) (1 ⊗ₜ[K] w) (completedDeterminantDualBasisWedge_pairing ω bW)
  change (ξ.restrict W).determinantDiscrepancy ω = (pW * qW)⁻¹ at hdW
  have hdQ := (ξ.quotient W).determinantDiscrepancy_eq_inv_norm_mul ω
    (1 ⊗ₜ[K] zQ) (1 ⊗ₜ[K] q) (completedDeterminantDualBasisWedge_pairing ω bQ)
  change (ξ.quotient W).determinantDiscrepancy ω = (pQ * qQ)⁻¹ at hdQ
  have hdE := ξ.determinantDiscrepancy_eq_inv_norm_mul_of_norm_pairing_eq_one ω
    (1 ⊗ₜ[K] determinantDualSequenceEquiv W (zQ ⊗ₜ[K] zW))
    (1 ⊗ₜ[K] determinantSequenceEquiv W (w ⊗ₜ[K] q))
    (completedDeterminantDualSequence_pairing_basis_norm W ω bW bQ)
  change ξ.determinantDiscrepancy ω = (pE * qE)⁻¹ at hdE
  have hWline : Module.finrank K DW = 1 := determinant_finrank
  have hQline : Module.finrank K DQ = 1 := determinant_finrank
  have hn := (ξ.restrict W).determinant.injectiveTensorPair_norm_rational_generators
    (ξ.quotient W).determinant hWline hQline hw hq ω
  change D.norm ω (1 ⊗ₜ[K] (w ⊗ₜ[K] q)) = pW * pQ at hn
  have ht : w ⊗ₜ[K] q ≠ 0 := by
    intro h
    rw [h, TensorProduct.tmul_zero, D.norm_zero] at hn
    linarith [mul_pos hpW hpQ]
  have hr : Module.finrank K (DW ⊗[K] DQ) = 1 := by
    rw [Module.finrank_tensorProduct, hWline, hQline, mul_one]
  have ha : a = pE / (pW * pQ) := by
    change D.operatorNorm ξ.determinant ω (determinantSequenceEquiv W).toLinearMap =
      pE / (pW * pQ)
    rw [D.operatorNorm_eq_div_of_finrank_one ξ.determinant hr
      (determinantSequenceEquiv W).toLinearMap ht ω, hn]
    rfl
  have hdual := ξ.determinantDualSequence_norm_le W ω hω (1 ⊗ₜ[K] (zQ ⊗ₜ[K] zW))
  have hDQdual :
      Module.finrank K (⋀[K]^(Module.finrank K (Module.Dual K (E ⧸ W)))
        (Module.Dual K (E ⧸ W))) = 1 := determinant_finrank
  have hDWdual :
      Module.finrank K (⋀[K]^(Module.finrank K (Module.Dual K W))
        (Module.Dual K W)) = 1 := determinant_finrank
  have hndual := (ξ.quotient W).dual.determinant.injectiveTensorPair_norm_rational_generators
    (ξ.restrict W).dual.determinant hDQdual hDWdual hzQ hzW ω
  rw [LinearMap.baseChange_tmul, hndual] at hdual
  change qE ≤ qQ * qW at hdual
  have hb : qE / (qQ * qW) ≤ 1 := (div_le_one (mul_pos hqQ hqW)).2 hdual
  have hratio :
      (ξ.restrict W).determinantDiscrepancy ω *
          (ξ.quotient W).determinantDiscrepancy ω / ξ.determinantDiscrepancy ω =
        a * (qE / (qQ * qW)) := by
    rw [hdW, hdQ, hdE, ha]
    exact inverse_norm_products_ratio hpW.ne' hpQ.ne' hqW.ne' hqQ.ne'
  rw [hratio]
  exact (mul_le_mul_of_nonneg_left hb
    (D.operatorNorm_nonneg ξ.determinant ω (determinantSequenceEquiv W).toLinearMap)).trans
    (by rw [mul_one])

/-- Restriction and quotient discrepancies multiply to at most the original
discrepancy under the local Hahn–Banach hypotheses. -/
theorem determinantDiscrepancy_restrict_mul_quotient_le
    (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    (ξ.restrict W).determinantDiscrepancy ω *
      (ξ.quotient W).determinantDiscrepancy ω ≤ ξ.determinantDiscrepancy ω :=
  (div_le_one (ξ.determinantDiscrepancy_pos ω)).1
    ((ξ.determinantSequence_operatorNorm_lower_bound W ω hω).trans
      (ξ.determinantSequence_operatorNorm_le_one W ω))

/-- Restriction cannot increase intrinsic determinant discrepancy. -/
theorem determinantDiscrepancy_restrict_le (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    (ξ.restrict W).determinantDiscrepancy ω ≤ ξ.determinantDiscrepancy ω := by
  calc
    (ξ.restrict W).determinantDiscrepancy ω =
        (ξ.restrict W).determinantDiscrepancy ω * 1 := (mul_one _).symm
    _ ≤ (ξ.restrict W).determinantDiscrepancy ω *
        (ξ.quotient W).determinantDiscrepancy ω :=
      mul_le_mul_of_nonneg_left ((ξ.quotient W).one_le_determinantDiscrepancy ω)
        ((ξ.restrict W).determinantDiscrepancy_pos ω).le
    _ ≤ ξ.determinantDiscrepancy ω :=
      ξ.determinantDiscrepancy_restrict_mul_quotient_le W ω hω

/-- Quotient cannot increase intrinsic determinant discrepancy. -/
theorem determinantDiscrepancy_quotient_le (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y)) :
    (ξ.quotient W).determinantDiscrepancy ω ≤ ξ.determinantDiscrepancy ω := by
  calc
    (ξ.quotient W).determinantDiscrepancy ω =
        1 * (ξ.quotient W).determinantDiscrepancy ω := (one_mul _).symm
    _ ≤ (ξ.restrict W).determinantDiscrepancy ω *
        (ξ.quotient W).determinantDiscrepancy ω :=
      mul_le_mul_of_nonneg_right ((ξ.restrict W).one_le_determinantDiscrepancy ω)
        ((ξ.quotient W).determinantDiscrepancy_pos ω).le
    _ ≤ ξ.determinantDiscrepancy ω :=
      ξ.determinantDiscrepancy_restrict_mul_quotient_le W ω hω

/-- Unit original discrepancy forces the actual determinant sequence operator
norm to be one, including zero-dimensional ends. -/
theorem determinantSequence_operatorNorm_eq_one_of_discrepancy_eq_one
    (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (hδ : ξ.determinantDiscrepancy ω = 1) :
    ((ξ.restrict W).determinant.injectiveTensorPair
      (ξ.quotient W).determinant).operatorNorm ξ.determinant ω
        (determinantSequenceEquiv W).toLinearMap = 1 := by
  apply le_antisymm (ξ.determinantSequence_operatorNorm_le_one W ω)
  have hl := ξ.determinantSequence_operatorNorm_lower_bound W ω hω
  rw [hδ, div_one] at hl
  have hp : 1 ≤ (ξ.restrict W).determinantDiscrepancy ω *
      (ξ.quotient W).determinantDiscrepancy ω := by
    simpa only [one_mul] using
      mul_le_mul ((ξ.restrict W).one_le_determinantDiscrepancy ω)
        ((ξ.quotient W).one_le_determinantDiscrepancy ω) zero_le_one
        ((ξ.restrict W).determinantDiscrepancy_pos ω).le
  exact hp.trans hl

/-- The unit-discrepancy determinant sequence preserves the actual norm on
every completed vector, rather than only on rational generators. -/
theorem determinantSequence_norm_eq_of_discrepancy_eq_one
    (W : Submodule K E) (ω : S.Ω)
    (hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, ξ.norm ω (x + y) ≤ max (ξ.norm ω x) (ξ.norm ω y))
    (hδ : ξ.determinantDiscrepancy ω = 1)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⋀[K]^(Module.finrank K W) W) ⊗[K]
        (⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)))) :
    ξ.determinant.norm ω
      ((determinantSequenceEquiv W).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    ((ξ.restrict W).determinant.injectiveTensorPair
      (ξ.quotient W).determinant).norm ω z := by
  classical
  let DW := ⋀[K]^(Module.finrank K W) W
  let DQ := ⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)
  let D := (ξ.restrict W).determinant.injectiveTensorPair (ξ.quotient W).determinant
  have hrW : Module.finrank K DW = 1 := determinant_finrank
  have hrQ : Module.finrank K DQ = 1 := determinant_finrank
  have hr : Module.finrank K (DW ⊗[K] DQ) = 1 := by
    rw [Module.finrank_tensorProduct, hrW, hrQ, mul_one]
  let : Nontrivial (DW ⊗[K] DQ) :=
    Module.nontrivial_of_finrank_pos (by rw [hr]; exact zero_lt_one)
  obtain ⟨x, hx⟩ := exists_ne (0 : DW ⊗[K] DQ)
  have hpos := D.norm_rational_pos ω hx
  have hratio : 1 = ξ.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantSequenceEquiv W x) /
      D.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) :=
    (ξ.determinantSequence_operatorNorm_eq_one_of_discrepancy_eq_one W ω hω hδ).symm.trans
      (D.operatorNorm_eq_div_of_finrank_one ξ.determinant hr
        (determinantSequenceEquiv W).toLinearMap hx ω)
  have hgen : ξ.determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] determinantSequenceEquiv W x) =
      D.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
    have h := (eq_div_iff (ne_of_gt hpos)).1 hratio
    simpa only [one_mul] using h.symm
  have hc : Module.finrank (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] (DW ⊗[K] DQ)) = 1 :=
    Module.finrank_baseChange.trans hr
  have hx' : (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x ≠ 0 :=
    fun h => (ne_of_gt hpos) (h ▸ D.norm_zero ω)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one hc hx' z
  rw [← ha, map_smul, ξ.determinant.norm_smul, D.norm_smul,
    LinearMap.baseChange_tmul]
  exact congrArg (fun r : ℝ => ‖a‖ * r) hgen

/-- At an elementary fibre the canonical determinant exact-sequence map is
an isometry of the actual completed determinant tensor line. -/
theorem IsElementaryAt.determinantSequence_norm_eq {η : NormFamily S E}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion} {ω : S.Ω}
    (he : η.IsElementaryAt hN ω) (W : Submodule K E)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⋀[K]^(Module.finrank K W) W) ⊗[K]
        (⋀[K]^(Module.finrank K (E ⧸ W)) (E ⧸ W)))) :
    η.determinant.norm ω
      ((determinantSequenceEquiv W).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    ((η.restrict W).determinant.injectiveTensorPair
      (η.quotient W).determinant).norm ω z := by
  have hω : IsRCLikeNormedField (S.ϕ ω).Completion ∨
      ∀ x y, η.norm ω (x + y) ≤ max (η.norm ω x) (η.norm ω y) := by
    by_cases hi : ω ∈ S.Ωinf
    · exact Or.inl (hN ω hi)
    · exact Or.inr (he.1 (not_not.mp hi))
  exact η.determinantSequence_norm_eq_of_discrepancy_eq_one W ω hω
    he.determinantDiscrepancy_eq_one z

end NormFamily
end LocalDiscrepancy

end ArakelovGeometry
