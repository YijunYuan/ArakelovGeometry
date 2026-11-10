/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicVectorBundle.ScalarExtensionIsomorphismRestriction
import ArakelovGeometry.AdelicVectorBundle.DeterminantUniversal

/-!
# Actual determinant transport under scalar-field isomorphisms

The exterior universal property induces semilinear maps. Their application to
the actual completed native subquotient maps transports the determinant norms.
-/

open scoped TensorProduct
noncomputable section
namespace ArakelovGeometry

section SemilinearExterior
variable {R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [AddCommGroup W] [Module R V] [Module S W]

/-- The canonical exterior map of a semilinear map, characterized by its
formula on wedges, including the empty wedge. -/
def exteriorPowerSemilinearMap (τ : R →+* S) (f : V →ₛₗ[τ] W) (n : ℕ) :
    (⋀[R]^n V) →ₛₗ[τ] (⋀[S]^n W) := by
  letI : Module R (⋀[S]^n W) := Module.compHom _ τ
  let a : V [⋀^Fin n]→ₗ[R] (⋀[S]^n W) :=
    { toFun := fun v ↦ _root_.exteriorPower.ιMulti S n (fun i ↦ f (v i))
      map_update_add' := by
        intro _ v i x y
        change _root_.exteriorPower.ιMulti S n (f ∘ Function.update v i (x + y)) =
          _root_.exteriorPower.ιMulti S n (f ∘ Function.update v i x) +
            _root_.exteriorPower.ιMulti S n (f ∘ Function.update v i y)
        simpa only [Function.comp_update, map_add] using
          (_root_.exteriorPower.ιMulti S n).map_update_add (f ∘ v) i (f x) (f y)
      map_update_smul' := by
        intro _ v i r x
        change _root_.exteriorPower.ιMulti S n (f ∘ Function.update v i (r • x)) =
          τ r • _root_.exteriorPower.ιMulti S n (f ∘ Function.update v i x)
        simpa only [Function.comp_update, f.map_smulₛₗ] using
          (_root_.exteriorPower.ιMulti S n).map_update_smul (f ∘ v) i (τ r) (f x)
      map_eq_zero_of_eq' := by
        intro v i j hij hne
        exact (_root_.exteriorPower.ιMulti S n).map_eq_zero_of_eq
          (fun k ↦ f (v k)) (congrArg f hij) hne }
  let g := _root_.exteriorPower.alternatingMapLinearEquiv a
  exact { g.toAddHom with map_smul' := g.map_smul }

@[simp]
theorem exteriorPowerSemilinearMap_ιMulti (τ : R →+* S) (f : V →ₛₗ[τ] W)
    (n : ℕ) (v : Fin n → V) :
    exteriorPowerSemilinearMap τ f n (_root_.exteriorPower.ιMulti R n v) =
      _root_.exteriorPower.ιMulti S n (fun i ↦ f (v i)) := by
  let : Module R (⋀[S]^n W) := Module.compHom _ τ
  exact _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

variable (τ : R ≃+* S)
local instance : RingHomInvPair (τ : R →+* S) (τ.symm : S →+* R) :=
  RingHomInvPair.of_ringEquiv τ
local instance : RingHomInvPair (τ.symm : S →+* R) (τ : R →+* S) :=
  RingHomInvPair.of_ringEquiv_symm τ

private theorem exteriorPowerSemilinearMap_inverse (e : V ≃ₛₗ[(τ : R →+* S)] W)
    (n : ℕ) (z : ⋀[R]^n V) :
    exteriorPowerSemilinearMap (τ.symm : S →+* R) e.symm.toLinearMap n
      (exteriorPowerSemilinearMap (τ : R →+* S) e.toLinearMap n z) = z := by
  have hz : z ∈ Submodule.span R (Set.range (_root_.exteriorPower.ιMulti R n)) := by
    rw [_root_.exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    simp only [exteriorPowerSemilinearMap_ιMulti, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  | zero => simp only [map_zero]
  | add z w hz hw ihz ihw => simp only [map_add, ihz, ihw]
  | smul a z hz ih =>
    simp only [map_smulₛₗ, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, ih]

/-- The canonical semilinear equivalence on exterior powers induced by a
semilinear equivalence. The inverse is induced by the inverse map. -/
def exteriorPowerSemilinearEquiv (e : V ≃ₛₗ[(τ : R →+* S)] W) (n : ℕ) :
    (⋀[R]^n V) ≃ₛₗ[(τ : R →+* S)] (⋀[S]^n W) :=
  { exteriorPowerSemilinearMap (τ : R →+* S) e.toLinearMap n with
    invFun := exteriorPowerSemilinearMap (τ.symm : S →+* R) e.symm.toLinearMap n
    left_inv := exteriorPowerSemilinearMap_inverse τ e n
    right_inv := exteriorPowerSemilinearMap_inverse τ.symm e.symm n }

@[simp]
theorem exteriorPowerSemilinearEquiv_ιMulti (e : V ≃ₛₗ[(τ : R →+* S)] W)
    (n : ℕ) (v : Fin n → V) :
    exteriorPowerSemilinearEquiv τ e n (_root_.exteriorPower.ιMulti R n v) =
      _root_.exteriorPower.ιMulti S n (fun i ↦ e (v i)) :=
  exteriorPowerSemilinearMap_ιMulti _ _ _ _

end SemilinearExterior



section CompletedDeterminant
variable {K L E F A C : Type*} [Field K] [Field L] [Field A] [Field C]
  [Algebra K A] [Algebra L C]
  [AddCommGroup E] [AddCommGroup F] [Module K E] [Module L F]
  (τ : A ≃+* C)

local instance : RingHomInvPair (τ : A →+* C)
    (τ.symm : C →+* A) :=
  RingHomInvPair.of_ringEquiv τ
local instance : RingHomInvPair (τ.symm : C →+* A)
    (τ : A →+* C) :=
  RingHomInvPair.of_ringEquiv_symm τ

/-- Semilinear transport on the actual completed determinant fibres, formed
from the canonical exterior base-change identifications. -/
def completedDeterminantSemilinearEquiv
    (e : (A ⊗[K] E)
      ≃ₛₗ[(τ : A →+* C)]
        (C ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F) :
    (A ⊗[K] (⋀[K]^(Module.finrank K E) E))
      ≃ₛₗ[(τ : A →+* C)]
        (C ⊗[L] (⋀[L]^(Module.finrank L F) F)) := by
  let p := exteriorBaseChangeEquiv K A E (Module.finrank K E)
  let q := exteriorBaseChangeEquiv L C F (Module.finrank L F)
  let g := exteriorPowerSemilinearEquiv
    (R := A) (S := C)
    (V := A ⊗[K] E) (W := C ⊗[L] F)
    τ e (Module.finrank K E)
  let h := exteriorPowerDegreeEquiv C
    (C ⊗[L] F) hr
  let d := p.toAddEquiv.trans
    (g.toAddEquiv.trans (h.toAddEquiv.trans q.symm.toAddEquiv))
  refine { d with map_smul' := ?_ }
  intro a z
  change q.symm (h (g (p (a • z)))) = τ a • q.symm (h (g (p z)))
  simp only [map_smul, map_smulₛₗ, RingEquiv.coe_toRingHom]

/-- The completed determinant map acts on arbitrary completed wedges by the
same actual semilinear fibre map. -/
theorem completedDeterminantSemilinearEquiv_ιMulti
    (e : (A ⊗[K] E)
      ≃ₛₗ[(τ : A →+* C)]
        (C ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F)
    (v : Fin (Module.finrank K E) → A ⊗[K] E) :
    completedDeterminantSemilinearEquiv τ e hr
      ((exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v)) =
      (exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F)
          (fun i ↦ e (v ((finCongr hr).symm i)))) := by
  change (exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
    (exteriorPowerDegreeEquiv C (C ⊗[L] F) hr
      (exteriorPowerSemilinearEquiv τ e (Module.finrank K E)
        ((exteriorBaseChangeEquiv K A E (Module.finrank K E))
          ((exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
            (_root_.exteriorPower.ιMulti A (Module.finrank K E) v))))) = _
  simp only [
    LinearEquiv.apply_symm_apply, exteriorPowerSemilinearEquiv_ιMulti,
    exteriorPowerDegreeEquiv_ιMulti]

end CompletedDeterminant

section DeterminantSeminormTransport
variable {K L E F A C : Type*} [Field K] [Field L] [NormedField A] [NormedField C]
  [Algebra K A] [Algebra L C] [AddCommGroup E] [AddCommGroup F]
  [Module K E] [Module L F] (τ : A ≃+* C)
  (p : Seminorm A (A ⊗[K] E))
  (pd : Seminorm A (A ⊗[K] (⋀[K]^(Module.finrank K E) E)))
  (q : Seminorm C (C ⊗[L] F))
  (qd : Seminorm C (C ⊗[L] (⋀[L]^(Module.finrank L F) F)))

local instance : RingHomInvPair (τ : A →+* C) (τ.symm : C →+* A) :=
  RingHomInvPair.of_ringEquiv τ
local instance : RingHomInvPair (τ.symm : C →+* A) (τ : A →+* C) :=
  RingHomInvPair.of_ringEquiv_symm τ

private theorem completedDeterminantSeminorm_norm_le
    (e : (A ⊗[K] E) ≃ₛₗ[(τ : A →+* C)] (C ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F)
    (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (he : ∀ v, q (e v) ≤ p v)
    (haP : ∀ z ε, 0 < ε → ∃ (a : A) (v : Fin (Module.finrank K E) → A ⊗[K] E),
      a • (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v) = z ∧
      ‖a‖ * (∏ i, p (v i)) < pd z + ε)
    (hwQ : ∀ v : Fin (Module.finrank L F) → C ⊗[L] F,
      qd ((exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F) v)) ≤ ∏ i, q (v i))
    (z : A ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    qd (completedDeterminantSemilinearEquiv τ e hr z) ≤ pd z := by
  let d := completedDeterminantSemilinearEquiv τ e hr
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, v, hv, hc⟩ := haP z ε hε
  have hd : d ((exteriorBaseChangeEquiv K A E
      (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v)) =
      (exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F)
          (fun i ↦ e (v ((finCongr hr).symm i)))) :=
    completedDeterminantSemilinearEquiv_ιMulti τ e hr v
  have hp : (∏ i, q (e (v ((finCongr hr).symm i)))) ≤
      ∏ i, p (v i) := by
    rw [(finCongr hr).symm.prod_comp (fun i ↦ q (e (v i)))]
    exact Finset.prod_le_prod (fun _ _ ↦ apply_nonneg q _) (fun i _ ↦ he (v i))
  calc
    qd (d z) = ‖a‖ * qd
        ((exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
          (_root_.exteriorPower.ιMulti C (Module.finrank L F)
            (fun i ↦ e (v ((finCongr hr).symm i))))) := by
      rw [← hv, d.map_smulₛₗ]
      change qd (τ a • d _) = _
      rw [map_smul_eq_mul, hτ]
      exact congrArg (fun u ↦ ‖a‖ * qd u) hd
    _ ≤ ‖a‖ * (∏ i, p (v i)) :=
      mul_le_mul_of_nonneg_left
        ((hwQ _).trans hp) (_root_.norm_nonneg a)
    _ ≤ pd z + ε := hc.le

/-- A semilinear isometry preserves determinant seminorms satisfying the
actual decomposable-vector bounds and scalar approximation properties. -/
theorem completedDeterminantSeminorm_norm_eq
    (e : (A ⊗[K] E) ≃ₛₗ[(τ : A →+* C)] (C ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F)
    (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (he : ∀ v, q (e v) = p v)
    (haP : ∀ z ε, 0 < ε → ∃ (a : A) (v : Fin (Module.finrank K E) → A ⊗[K] E),
      a • (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v) = z ∧
      ‖a‖ * (∏ i, p (v i)) < pd z + ε)
    (haQ : ∀ z ε, 0 < ε → ∃ (a : C) (v : Fin (Module.finrank L F) → C ⊗[L] F),
      a • (exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F) v) = z ∧
      ‖a‖ * (∏ i, q (v i)) < qd z + ε)
    (hwP : ∀ v : Fin (Module.finrank K E) → A ⊗[K] E,
      pd ((exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
        (_root_.exteriorPower.ιMulti A (Module.finrank K E) v)) ≤ ∏ i, p (v i))
    (hwQ : ∀ v : Fin (Module.finrank L F) → C ⊗[L] F,
      qd ((exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F) v)) ≤ ∏ i, q (v i))
    (z : A ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    qd (completedDeterminantSemilinearEquiv τ e hr z) = pd z := by
  let d := completedDeterminantSemilinearEquiv τ e hr
  apply le_antisymm
    (completedDeterminantSeminorm_norm_le τ p pd q qd e hr hτ
      (fun v ↦ (he v).le) haP hwQ z)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, v, hv, hc⟩ := haQ (d z) ε hε
  let u : Fin (Module.finrank K E) → A ⊗[K] E :=
    fun i ↦ e.symm (v (finCongr hr i))
  let w := (exteriorBaseChangeEquiv K A E (Module.finrank K E)).symm
    (_root_.exteriorPower.ιMulti A (Module.finrank K E) u)
  have hd : d w =
      (exteriorBaseChangeEquiv L C F (Module.finrank L F)).symm
        (_root_.exteriorPower.ιMulti C (Module.finrank L F) v) := by
    simpa only [u, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] using
      completedDeterminantSemilinearEquiv_ιMulti τ e hr u
  have hz : τ.symm a • w = z := by
    apply d.injective
    rw [d.map_smulₛₗ]
    change τ (τ.symm a) • d w = d z
    rw [RingEquiv.apply_symm_apply, hd]
    exact hv
  have ha : ‖τ.symm a‖ = ‖a‖ := by
    simpa only [RingEquiv.apply_symm_apply] using (hτ (τ.symm a)).symm
  have hp : (∏ i, p (u i)) = ∏ i, q (v i) := by
    rw [← (finCongr hr).prod_comp (fun i ↦ q (v i))]
    apply Finset.prod_congr rfl
    intro i _
    exact (he (u i)).symm.trans (congrArg (q) (e.apply_symm_apply _))
  calc
    pd z = ‖a‖ * pd w := by
      rw [← hz, map_smul_eq_mul, ha]
    _ ≤ ‖a‖ * (∏ i, q (v i)) :=
      mul_le_mul_of_nonneg_left
        ((hwP u).trans_eq hp) (_root_.norm_nonneg a)
    _ ≤ qd (d z) + ε := hc.le

end DeterminantSeminormTransport

namespace NormFamily
section SemilinearDeterminantNorm
variable {K L E F : Type*} [Field K] [Field L]
  [AddCommGroup E] [AddCommGroup F] [Module K E] [Module L F]
  [FiniteDimensional K E] [FiniteDimensional L F]
  {S : AdelicStructure K} {T : AdelicStructure L}
  (ξ : NormFamily S E) (η : NormFamily T F)
  (ω : S.Ω) (ω' : T.Ω)
  (τ : (S.ϕ ω).Completion ≃+* (T.ϕ ω').Completion)

local instance : RingHomInvPair (τ : (S.ϕ ω).Completion →+* (T.ϕ ω').Completion)
    (τ.symm : (T.ϕ ω').Completion →+* (S.ϕ ω).Completion) :=
  RingHomInvPair.of_ringEquiv τ
local instance : RingHomInvPair (τ.symm : (T.ϕ ω').Completion →+* (S.ϕ ω).Completion)
    (τ : (S.ϕ ω).Completion →+* (T.ϕ ω').Completion) :=
  RingHomInvPair.of_ringEquiv_symm τ

/-- A semilinear contraction over an isometric coefficient isomorphism induces
a contraction on the actual determinant norms, without a rank restriction. -/
theorem completedDeterminantSemilinearEquiv_norm_le
    (e : ((S.ϕ ω).Completion ⊗[K] E)
      ≃ₛₗ[(τ : (S.ϕ ω).Completion →+* (T.ϕ ω').Completion)]
        ((T.ϕ ω').Completion ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F)
    (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (he : ∀ v, η.norm ω' (e v) ≤ ξ.norm ω v)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω' (completedDeterminantSemilinearEquiv τ e hr z) ≤
      ξ.determinant.norm ω z := by
  exact completedDeterminantSeminorm_norm_le τ (ξ.norm ω) (ξ.determinant.norm ω)
    (η.norm ω') (η.determinant.norm ω') e hr hτ he
    (fun z ε hε ↦ ξ.exists_smul_determinant_ιMulti_norm_lt ω z hε)
    (η.determinant_norm_ιMulti_le ω') z

/-- Every semilinear isometry over an isometric coefficient-field isomorphism
induces an isometry of the actual completed determinant norms, in every rank. -/
theorem completedDeterminantSemilinearEquiv_norm_eq
    (e : ((S.ϕ ω).Completion ⊗[K] E)
      ≃ₛₗ[(τ : (S.ϕ ω).Completion →+* (T.ϕ ω').Completion)]
        ((T.ϕ ω').Completion ⊗[L] F))
    (hr : Module.finrank K E = Module.finrank L F)
    (hτ : ∀ a, ‖τ a‖ = ‖a‖)
    (he : ∀ v, η.norm ω' (e v) = ξ.norm ω v)
    (z : (S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K E) E)) :
    η.determinant.norm ω' (completedDeterminantSemilinearEquiv τ e hr z) =
      ξ.determinant.norm ω z := by
  exact completedDeterminantSeminorm_norm_eq τ (ξ.norm ω) (ξ.determinant.norm ω)
    (η.norm ω') (η.determinant.norm ω') e hr hτ he
    (fun z ε hε ↦ ξ.exists_smul_determinant_ιMulti_norm_lt ω z hε)
    (fun z ε hε ↦ η.exists_smul_determinant_ιMulti_norm_lt ω' z hε)
    (ξ.determinant_norm_ιMulti_le ω) (η.determinant_norm_ιMulti_le ω') z

end SemilinearDeterminantNorm
end NormFamily

section ScalarExtensionSubquotient
open AdelicStructure.ParameterSpaceExtension
variable {K L M E : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K}

/-- The actual completed determinant-line equivalence induced by the produced
native completed subquotient map, using the produced equality of ranks. -/
def completedScalarExtensionSubquotientDeterminantEquiv (σ : L ≃ₐ[K] M)
    (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B) :
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
      (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
    let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
    letI := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
    letI := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
    let Q := B ⧸ T.comap B.subtype
    let Q' := scalarExtensionSubspaceOrderIso (E := E) σ B ⧸
      (scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype
    ((pullbackAlgEquiv S σ x).abv.Completion ⊗[L] (⋀[L]^(Module.finrank L Q) Q))
      ≃ₛₗ[((algEquivCompletedFields S σ x).toRingEquiv :
        (pullbackAlgEquiv S σ x).abv.Completion →+* x.abv.Completion)]
      (x.abv.Completion ⊗[M] (⋀[M]^(Module.finrank M Q') Q')) := by
  intro aL aM
  let := aL
  let := aM
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  exact completedDeterminantSemilinearEquiv (algEquivCompletedFields S σ x).toRingEquiv
    (completedScalarExtensionSubquotientEquiv σ x B T hTB)
    (scalarExtensionSubquotientSemilinearEquiv_finrank σ B T).symm

namespace NormFamily
variable [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

/-- Actual native subquotient determinant norms are preserved on every
completed vector by the produced coefficient and subquotient maps. No
determinant-isometry hypothesis or positive-rank hypothesis is required. -/
theorem scalarExtension_subquotient_determinant_norm_algEquiv (ξ : NormFamily S E)
    (σ : L ≃ₐ[K] M) (x : AdelicStructure.ParameterSpaceExtension S M)
    (B T : Submodule L (L ⊗[K] E)) (hTB : T ≤ B)
    (z : (pullbackAlgEquiv S σ x).abv.Completion ⊗[L]
      (⋀[L]^(Module.finrank L (B ⧸ T.comap B.subtype)) (B ⧸ T.comap B.subtype))) :
    (((ξ.scalarExtension (L := M)).restrict
      (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
        ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
          (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)).determinant.norm x
            (completedScalarExtensionSubquotientDeterminantEquiv σ x B T hTB z) =
      (((ξ.scalarExtension (L := L)).restrict B).quotient
        (T.comap B.subtype)).determinant.norm (pullbackAlgEquiv S σ x) z := by
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base)
    (pullbackAlgEquiv S σ x).abv (pullbackAlgEquiv S σ x).restrict_eq
  let := AbsoluteValue.normedAlgebraCompletionOfEq (S.ϕ x.base) x.abv x.restrict_eq
  let := RingHomInvPair.of_ringEquiv (algEquivCompletedFields S σ x).toRingEquiv
  let := RingHomInvPair.of_ringEquiv_symm (algEquivCompletedFields S σ x).toRingEquiv
  let η := ((ξ.scalarExtension (L := L)).restrict B).quotient (T.comap B.subtype)
  let θ := ((ξ.scalarExtension (L := M)).restrict
    (scalarExtensionSubspaceOrderIso (E := E) σ B)).quotient
      ((scalarExtensionSubspaceOrderIso (E := E) σ T).comap
        (scalarExtensionSubspaceOrderIso (E := E) σ B).subtype)
  let τ := (algEquivCompletedFields S σ x).toRingEquiv
  let e := completedScalarExtensionSubquotientEquiv σ x B T hTB
  let hr := (scalarExtensionSubquotientSemilinearEquiv_finrank σ B T).symm
  have hτ : ∀ a, ‖τ a‖ = ‖a‖ :=
    (isometry_algEquivCompletedFields S σ x).norm_map_of_map_zero
      (map_zero (algEquivCompletedFields S σ x))
  have he : ∀ v, θ.norm x (e v) = η.norm (pullbackAlgEquiv S σ x) v :=
    ξ.scalarExtension_subquotient_norm_algEquiv σ x B T hTB
  change θ.determinant.norm x (completedDeterminantSemilinearEquiv τ e hr z) =
    η.determinant.norm (pullbackAlgEquiv S σ x) z
  exact completedDeterminantSeminorm_norm_eq τ
    (η.norm (pullbackAlgEquiv S σ x)) (η.determinant.norm (pullbackAlgEquiv S σ x))
    (θ.norm x) (θ.determinant.norm x) e hr hτ he
    (fun z ε hε ↦ η.exists_smul_determinant_ιMulti_norm_lt (pullbackAlgEquiv S σ x) z hε)
    (fun z ε hε ↦ θ.exists_smul_determinant_ιMulti_norm_lt x z hε)
    (η.determinant_norm_ιMulti_le (pullbackAlgEquiv S σ x))
    (θ.determinant_norm_ιMulti_le x) z

end NormFamily
end ScalarExtensionSubquotient
end ArakelovGeometry
