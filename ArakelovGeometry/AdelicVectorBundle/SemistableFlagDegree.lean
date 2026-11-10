/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DegreeFlagHermitian
public import ArakelovGeometry.AdelicVectorBundle.Destabilizing
public import ArakelovGeometry.AdelicVectorBundle.QuotientRestriction

/-!
# Subspace degrees under actual semistable flags

The intersection subquotient contracts into its actual image in each flag
factor. Semistability bounds its degree; Hermitian degree additivity then
sums the bounds. The comparison is a contraction on every completed vector,
without an isometry assumption on the intersection quotient.
-/

@[expose] public section

open scoped BigOperators TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The rational intersection map into the canonical subquotient of `B` by `A`. -/
def intersectionToSubquotientLinearMap (U A B : Submodule K E) :
    ↥(U ⊓ B) →ₗ[K] B ⧸ (A.comap B.subtype) :=
  (A.comap B.subtype).mkQ.comp (Submodule.inclusion inf_le_right)

omit [FiniteDimensional K E] in
/-- The kernel is exactly the preceding intersection, with its canonical
embedding into the next intersection. -/
theorem ker_intersectionToSubquotientLinearMap (U A B : Submodule K E) :
    (intersectionToSubquotientLinearMap U A B).ker =
      (U ⊓ A).comap (U ⊓ B).subtype := by
  ext x
  change (A.comap B.subtype).mkQ (Submodule.inclusion inf_le_right x) = 0 ↔
    (x : E) ∈ U ⊓ A
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (x : E) ∈ A ↔ (x : E) ∈ U ∧ (x : E) ∈ A
  exact ⟨fun hx ↦ ⟨x.property.1, hx⟩, fun hx ↦ hx.2⟩

namespace NormFamily

/-- Inclusion followed by the actual quotient map is contractive on all
completed vectors of the intersection. -/
theorem intersectionToSubquotient_norm_le (ξ : NormFamily S E)
    (U A B : Submodule K E) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] ↥(U ⊓ B)) :
    ((ξ.restrict B).quotient (A.comap B.subtype)).norm ω
        ((intersectionToSubquotientLinearMap U A B).baseChange
          (S.ϕ ω).Completion x) ≤ (ξ.restrict (U ⊓ B)).norm ω x := by
  have hc : B.subtype.comp (Submodule.inclusion (show U ⊓ B ≤ B from inf_le_right)) =
      (U ⊓ B).subtype := Submodule.subtype_comp_inclusion _ _ _
  have ht := DFunLike.congr_fun
    (congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion) hc) x
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at ht
  simpa only [intersectionToSubquotientLinearMap, LinearMap.baseChange_comp,
    LinearMap.comp_apply, restrict_norm, ht] using
    (ξ.restrict B).quotient_norm_mk_le (A.comap B.subtype) ω
      ((Submodule.inclusion (show U ⊓ B ≤ B from inf_le_right)).baseChange
        (S.ϕ ω).Completion x)

/-- The actual intersection quotient contracts into the actual restricted
image in the flag factor, through the canonical first-isomorphism map. -/
theorem intersectionQuotient_range_norm_le (ξ : NormFamily S E)
    (U A B : Submodule K E) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (↥(U ⊓ B) ⧸ (intersectionToSubquotientLinearMap U A B).ker)) :
    (((ξ.restrict B).quotient (A.comap B.subtype)).restrict
      (intersectionToSubquotientLinearMap U A B).range).norm ω
        ((intersectionToSubquotientLinearMap U A B).quotKerEquivRange.toLinearMap.baseChange
          (S.ϕ ω).Completion z) ≤
      ((ξ.restrict (U ⊓ B)).quotient
        (intersectionToSubquotientLinearMap U A B).ker).norm ω z := by
  exact quotKerEquivRange_norm_le _ _ _
    (ξ.intersectionToSubquotient_norm_le U A B) ω z

end NormFamily

/-- Rank-nullity identifies the intersection factor rank with the dimension
increment, including repeated terms. -/
theorem finrank_intersection_quotient_eq_sub (U A B : Submodule K E) (hAB : A ≤ B) :
    Module.finrank K (↥(U ⊓ B) ⧸ ((U ⊓ A).comap (U ⊓ B).subtype)) =
      Module.finrank K ↥(U ⊓ B) - Module.finrank K ↥(U ⊓ A) := by
  rw [Submodule.finrank_quotient,
    (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left U hAB)).finrank_eq]

/-- The canonical injection bounds the intersection factor rank by that of
the actual flag factor. -/
theorem finrank_intersection_quotient_le (U A B : Submodule K E) :
    Module.finrank K (↥(U ⊓ B) ⧸ ((U ⊓ A).comap (U ⊓ B).subtype)) ≤
      Module.finrank K (B ⧸ (A.comap B.subtype)) := by
  let g := intersectionToSubquotientLinearMap U A B
  have h := g.quotKerEquivRange.finrank_eq.le.trans g.range.finrank_le
  have hk : g.ker = (U ⊓ A).comap (U ⊓ B).subtype :=
    ker_intersectionToSubquotientLinearMap U A B
  rw [hk] at h
  exact h

/-- The dimension of each actual finite-flag factor is its dimension increment. -/
theorem finrank_flagQuotient_eq_sub {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (i : Fin n) :
    Module.finrank K ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) =
      Module.finrank K (F i.succ) - Module.finrank K (F i.castSucc) := by
  rw [Submodule.finrank_quotient,
    (Submodule.comapSubtypeEquivOfLe (hF i.castSucc_le_succ)).finrank_eq]

/-- Actual quotient ranks telescope along any finite monotone flag starting
at zero, including empty flags and repeated subspaces. -/
theorem sum_finrank_flagQuotient_eq_last {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) :
    (∑ i : Fin n,
      Module.finrank K ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype))) =
        Module.finrank K (F (Fin.last n)) := by
  induction n with
  | zero =>
      change 0 = Module.finrank K (F 0)
      rw [hzero, finrank_bot]
  | succ n ih =>
      let G : Fin (n + 1) → Submodule K E := fun i ↦ F i.castSucc
      let A : Submodule K E := F (Fin.last n).castSucc
      let B : Submodule K E := F (Fin.last (n + 1))
      have hG : Monotone G := hF.comp Fin.strictMono_castSucc.monotone
      have hzG : G 0 = ⊥ := hzero
      have hprefix := ih G hG hzG
      change (∑ i : Fin n, Module.finrank K
        ((F i.castSucc.succ) ⧸ ((F i.castSucc.castSucc).comap
          (F i.castSucc.succ).subtype))) = Module.finrank K A at hprefix
      have hAB : A ≤ B := hF (Fin.le_last _)
      have hstep := (A.comap B.subtype).finrank_quotient_add_finrank
      rw [(Submodule.comapSubtypeEquivOfLe hAB).finrank_eq] at hstep
      rw [Fin.sum_univ_castSucc, hprefix]
      exact (add_comm _ _).trans hstep

/-- Intersection factor ranks sum to the dimension of the chosen subspace. -/
theorem sum_finrank_intersection_flagQuotient_eq {n : ℕ}
    (F : Fin (n + 1) → Submodule K E) (hF : Monotone F) (hzero : F 0 = ⊥)
    (htop : F (Fin.last n) = ⊤) (U : Submodule K E) :
    (∑ i : Fin n, Module.finrank K
      (↥(U ⊓ F i.succ) ⧸ ((U ⊓ F i.castSucc).comap (U ⊓ F i.succ).subtype))) =
        Module.finrank K U := by
  have hG : Monotone (fun i ↦ U ⊓ F i) := fun i j hij ↦ inf_le_inf_left U (hF hij)
  have hzG : U ⊓ F 0 = ⊥ := by rw [hzero, inf_bot_eq]
  have h := sum_finrank_flagQuotient_eq_last (fun i ↦ U ⊓ F i) hG hzG
  rw [htop, inf_top_eq] at h
  exact h

/-- Each intersection dimension increment is bounded by the ambient factor
rank; its nonnegativity is the natural-number rank convention. -/
theorem intersection_rank_increment_le {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (U : Submodule K E) (i : Fin n) :
    Module.finrank K (U ⊓ F i.succ : Submodule K E) -
      Module.finrank K (U ⊓ F i.castSucc : Submodule K E) ≤
        Module.finrank K ((F i.succ) ⧸ ((F i.castSucc).comap (F i.succ).subtype)) := by
  rw [← finrank_intersection_quotient_eq_sub U (F i.castSucc) (F i.succ)
    (hF i.castSucc_le_succ)]
  exact finrank_intersection_quotient_le U (F i.castSucc) (F i.succ)

/-- The intersection dimension increments telescope to the chosen subspace's
rank, in the source's dimension-difference notation. -/
theorem sum_intersection_rank_increment_eq {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (U : Submodule K E) :
    (∑ i : Fin n, (Module.finrank K (U ⊓ F i.succ : Submodule K E) -
      Module.finrank K (U ⊓ F i.castSucc : Submodule K E))) = Module.finrank K U := by
  calc
    _ = ∑ i : Fin n, Module.finrank K
        (↥(U ⊓ F i.succ) ⧸ ((U ⊓ F i.castSucc).comap (U ⊓ F i.succ).subtype)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (finrank_intersection_quotient_eq_sub U (F i.castSucc) (F i.succ)
        (hF i.castSucc_le_succ)).symm
    _ = Module.finrank K U := sum_finrank_intersection_flagQuotient_eq F hF hzero htop U

namespace AdelicVectorBundle

variable [S.IsProper]

/-- A semistable actual flag factor bounds the degree of every intersection
subquotient. The image carries its restriction norm, and zero image rank is
handled by degree zero rather than a division by rank. -/
theorem degree_intersection_quotient_le_rank_mul_slope (V : AdelicVectorBundle S E)
    (U A B : Submodule K E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hsemi : ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
      (A.comap B.subtype) hS).IsMeanSlopeSemistable hS hN) :
    ((V.restrictOfMeasurableBase (U ⊓ B) hS).quotientOfMeasurableBase
        ((U ⊓ A).comap (U ⊓ B).subtype) hS).degree hS hN ≤
      (Module.finrank K (↥(U ⊓ B) ⧸ ((U ⊓ A).comap (U ⊓ B).subtype)) : ℝ) *
        ((V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
          (A.comap B.subtype) hS).slope hS hN := by
  let g := intersectionToSubquotientLinearMap U A B
  let Q := (V.restrictOfMeasurableBase B hS).quotientOfMeasurableBase
    (A.comap B.subtype) hS
  have hk : g.ker = (U ⊓ A).comap (U ⊓ B).subtype :=
    ker_intersectionToSubquotientLinearMap U A B
  have hr : Module.finrank K (↥(U ⊓ B) ⧸ ((U ⊓ A).comap (U ⊓ B).subtype)) =
      Module.finrank K g.range := by
    rw [← hk]
    exact g.quotKerEquivRange.finrank_eq
  by_cases hz : Module.finrank K (↥(U ⊓ B) ⧸ ((U ⊓ A).comap (U ⊓ B).subtype)) = 0
  · rw [degree_eq_zero_of_finrank_eq_zero _ hS hN hz, hz]
    simp
  · have hp : 0 < Module.finrank K g.range := by rw [← hr]; exact Nat.pos_of_ne_zero hz
    have hd := degree_le_of_completed_contraction
      ((V.restrictOfMeasurableBase (U ⊓ B) hS).quotientOfMeasurableBase g.ker hS)
      (Q.restrictOfMeasurableBase g.range hS) g.quotKerEquivRange hS hN
      (V.toNormFamily.intersectionQuotient_range_norm_le U A B)
    rw [hk] at hd
    apply hd.trans
    rw [degree_eq_rank_mul_slope, hr]
    exact mul_le_mul_of_nonneg_left (hsemi.2 g.range hp) (Nat.cast_nonneg _)

/-- Each actual intersection flag factor satisfies the semistable degree
bound for the corresponding actual flag factor. -/
theorem degree_intersection_flagQuotient_le (V : AdelicVectorBundle S E)
    {n : ℕ} (F : Fin (n + 1) → Submodule K E) (U : Submodule K E) (i : Fin n)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hsemi : (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN) :
    (V.flagQuotientOfMeasurableBase (fun j ↦ U ⊓ F j) hS i).degree hS hN ≤
      (Module.finrank K (↥(U ⊓ F i.succ) ⧸
        ((U ⊓ F i.castSucc).comap (U ⊓ F i.succ).subtype)) : ℝ) *
          (V.flagQuotientOfMeasurableBase F hS i).slope hS hN :=
  V.degree_intersection_quotient_le_rank_mul_slope U (F i.castSucc) (F i.succ)
    hS hN hsemi

/-- The source-facing subspace degree bound from a complete semistable flag.
The intersection flag may have repeated terms. Slopes need not be ordered
for this inequality; ordering is an additional uniqueness hypothesis later. -/
theorem degree_restrict_le_sum_intersection_rank_mul_slope_of_semistableFlag
    (V : AdelicVectorBundle S E) {n : ℕ} (F : Fin (n + 1) → Submodule K E)
    (hF : Monotone F) (hzero : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN)
    (hsemi : ∀ i, (V.flagQuotientOfMeasurableBase F hS i).IsMeanSlopeSemistable hS hN)
    (U : Submodule K E) :
    (V.restrictOfMeasurableBase U hS).degree hS hN ≤
      ∑ i : Fin n, (Module.finrank K (U ⊓ F i.succ : Submodule K E) -
        Module.finrank K (U ⊓ F i.castSucc : Submodule K E) : ℕ) *
          (V.flagQuotientOfMeasurableBase F hS i).slope hS hN := by
  let G : Fin (n + 1) → Submodule K E := fun i ↦ U ⊓ F i
  have hG : Monotone G := fun i j hij ↦ inf_le_inf_left U (hF hij)
  have hzG : G 0 = ⊥ := by simp only [G, hzero, inf_bot_eq]
  have hlG : G (Fin.last n) = U := by simp only [G, htop, inf_top_eq]
  have hsum := V.sum_flagQuotient_degree_eq_restrict_of_isHermitian G hG hzG hS hN hV
  rw [hlG] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  have h := V.degree_intersection_flagQuotient_le F U i hS hN (hsemi i)
  rw [finrank_intersection_quotient_eq_sub U (F i.castSucc) (F i.succ)
    (hF i.castSucc_le_succ)] at h
  exact h

end AdelicVectorBundle

end

end ArakelovGeometry
