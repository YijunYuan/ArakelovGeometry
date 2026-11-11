/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HNLift
public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.Hermitian
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability

/-!
# Finite images of actual Harder--Narasimhan filtrations

The image at a threshold is the sum of the images of the source thresholds.
The strict right limit commutes with this sum. All induced graded maps use
actual subquotient norms, as required in the componentwise proof of Bost's
Lemmas 7.1 and 7.2.
-/

@[expose] public section

open scoped TensorProduct BigOperators

namespace Submodule

variable {K ι Q : Type*} [Field K] [AddCommGroup Q] [Module K Q]
  {C : ι → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]

/-- The actual common image filtration of a family of filtered linear maps. -/
noncomputable def imageFiltration (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) : Submodule K Q :=
  ⨆ i, (H i t).map (f i)

/-- Each source map preserves its filtration and the actual common image. -/
theorem le_comap_imageFiltration (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (i : ι) (t : ℝ) :
    H i t ≤ (imageFiltration f H t).comap (f i) :=
  map_le_iff_le_comap.mp (le_iSup (fun i ↦ (H i t).map (f i)) i)

/-- Taking strict right limits commutes with the common image, including the
empty family. This is an equality of actual subspaces. -/
theorem imageFiltration_rightLimit (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) :
    filtrationRightLimit (imageFiltration f H) t =
      ⨆ i, (filtrationRightLimit (H i) t).map (f i) := by
  simp only [filtrationRightLimit, imageFiltration, map_iSup]
  exact iSup_comm

/-- The common image of decreasing filtrations is decreasing. -/
theorem imageFiltration_antitone (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i)) :
    Antitone (imageFiltration f H) := by
  intro s t hst
  exact iSup_mono fun i ↦ map_mono (hH i hst)

variable [Finite ι]

/-- Finitely many separated decreasing filtrations have a zero common image
above some threshold. -/
theorem imageFiltration_exists_bot (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i))
    (hbot : ∀ i, ∃ t, H i t = ⊥) : ∃ t, imageFiltration f H t = ⊥ := by
  classical
  choose t ht using hbot
  obtain ⟨b, hb⟩ := (Set.finite_range t).bddAbove
  refine ⟨b, bot_unique (iSup_le fun i ↦ ?_)⟩
  have hi : H i b = ⊥ := bot_unique ((hH i (hb ⟨i, rfl⟩)).trans_eq (ht i))
  simp only [hi, map_bot, le_refl]

/-- Finitely many exhaustive sources with spanning images give an exhaustive
common image filtration. -/
theorem imageFiltration_exists_top (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (hH : ∀ i, Antitone (H i))
    (htop : ∀ i, ∃ t, H i t = ⊤) (hspan : (⨆ i, (f i).range) = ⊤) :
    ∃ t, imageFiltration f H t = ⊤ := by
  classical
  choose t ht using htop
  obtain ⟨b, hb⟩ := (Set.finite_range t).bddBelow
  refine ⟨b, ?_⟩
  have hi (i : ι) : H i b = ⊤ := top_unique ((ht i).symm.le.trans (hH i (hb ⟨i, rfl⟩)))
  simpa only [imageFiltration, hi, map_top] using hspan

/-- Local constancy from the left passes to a finite common image. -/
theorem imageFiltration_left (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i))
    (hleft : ∀ i t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → H i s = H i t) (t : ℝ) :
    ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → imageFiltration f H s = imageFiltration f H t := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hn : Nonempty ι
  · let : Nonempty ι := hn
    choose ε hε hc using fun i ↦ hleft i t
    let δ := Finset.univ.inf' Finset.univ_nonempty ε
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ ↦ hε i)
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    apply iSup_congr
    intro i
    have hδε : δ ≤ ε i := Finset.inf'_le _ (Finset.mem_univ i)
    rw [hc i s (by linarith) hst]
  · have : IsEmpty ι := not_nonempty_iff.mp hn
    exact ⟨1, zero_lt_one, fun _ _ _ ↦ by simp [imageFiltration]⟩

omit [Finite ι] in
/-- The canonical maps from the source grades jointly span the actual image
grade. No splitting of any source or target filtration is chosen. -/
theorem imageFiltration_graded_range (f : ∀ i, C i →ₗ[K] Q)
    (H : ∀ i, ℝ → Submodule K (C i)) (t : ℝ) :
    (⨆ i, (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range) = ⊤ := by
  let R := ⨆ i, (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range
  have hm (x : Q) (hx : x ∈ imageFiltration f H t) :
      filtrationGradedMk (imageFiltration f H) t ⟨x, hx⟩ ∈ R := by
    change x ∈ ⨆ i, (H i t).map (f i) at hx
    induction hx using iSup_induction' (fun i ↦ (H i t).map (f i)) with
    | mem i x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      apply (le_iSup (fun i ↦
        (filtrationGradedMap (f i) (le_comap_imageFiltration f H i) t).range) i)
      exact ⟨filtrationGradedMk (H i) t ⟨y, hy⟩, rfl⟩
    | zero =>
      change filtrationGradedMk (imageFiltration f H) t 0 ∈ R
      rw [map_zero]
      exact R.zero_mem
    | add x y hx hy ihx ihy =>
      change filtrationGradedMk (imageFiltration f H) t (⟨x, hx⟩ + ⟨y, hy⟩) ∈ R
      rw [map_add]
      exact R.add_mem ihx ihy
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := ((filtrationRightLimit (imageFiltration f H) t).comap
    (imageFiltration f H t).subtype).mkQ_surjective z
  exact hm x x.property

end Submodule

namespace Submodule

variable {K Q : Type*} [Field K] [AddCommGroup Q] [Module K Q]
  {n : ℕ} {D : Fin n → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]

/-- The flag obtained by successively adjoining the actual images. -/
noncomputable def imageFlag (f : ∀ i, D i →ₗ[K] Q) (k : Fin (n + 1)) : Submodule K Q :=
  ⨆ (i : Fin n) (_ : i.val < k.val), (f i).range

theorem imageFlag_monotone (f : ∀ i, D i →ₗ[K] Q) : Monotone (imageFlag f) := by
  intro k l hkl
  exact iSup_le fun i ↦ iSup_le fun hi ↦ le_iSup_of_le i (le_iSup_of_le (hi.trans_le hkl) le_rfl)

theorem imageFlag_zero (f : ∀ i, D i →ₗ[K] Q) : imageFlag f 0 = ⊥ := by
  simp [imageFlag]

theorem imageFlag_last (f : ∀ i, D i →ₗ[K] Q) : imageFlag f (Fin.last n) = ⨆ i, (f i).range := by
  simp [imageFlag]

theorem imageFlag_succ (f : ∀ i, D i →ₗ[K] Q) (i : Fin n) :
    imageFlag f i.succ = imageFlag f i.castSucc ⊔ (f i).range := by
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    by_cases hji : j = i
    · subst j
      exact le_sup_right
    · have hlt : j.val < i.val := by
        have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
        simp only [Fin.val_succ] at hj
        omega
      have hmem : (f j).range ≤ imageFlag f i.castSucc :=
        le_iSup_of_le j (le_iSup_of_le (show j.val < i.castSucc.val from hlt) le_rfl)
      exact hmem.trans le_sup_left
  · apply sup_le
    · exact imageFlag_monotone f i.castSucc_le_succ
    · exact le_iSup_of_le i (le_iSup_of_le (Nat.lt_succ_self _) le_rfl)

/-- The next source maps canonically to the next accumulated image. -/
noncomputable def imageFlagStep (f : ∀ i, D i →ₗ[K] Q) (i : Fin n) :
    D i →ₗ[K] imageFlag f i.succ :=
  (f i).codRestrict _ (fun x ↦ by
    apply mem_iSup_of_mem i
    apply mem_iSup_of_mem (show i.val < i.succ.val from Nat.lt_succ_self _)
    exact ⟨x, rfl⟩)

/-- The actual adjacent image-flag quotient receives the source canonically. -/
noncomputable def imageFlagQuotientMap (f : ∀ i, D i →ₗ[K] Q) (i : Fin n) :
    D i →ₗ[K] ((imageFlag f i.succ) ⧸
      (imageFlag f i.castSucc).comap (imageFlag f i.succ).subtype) :=
  ((imageFlag f i.castSucc).comap (imageFlag f i.succ).subtype).mkQ.comp (imageFlagStep f i)

/-- Every adjacent actual quotient is a surjective image of the newly
adjoined source, including repeated flag steps. -/
theorem imageFlagQuotientMap_surjective (f : ∀ i, D i →ₗ[K] Q) (i : Fin n) :
    Function.Surjective (imageFlagQuotientMap f i) := by
  intro z
  obtain ⟨x, rfl⟩ := ((imageFlag f i.castSucc).comap (imageFlag f i.succ).subtype).mkQ_surjective z
  have hx : (x : Q) ∈ imageFlag f i.castSucc ⊔ (f i).range :=
    (imageFlag_succ f i).le x.property
  obtain ⟨a, ha, b, ⟨y, rfl⟩, hab⟩ := mem_sup.mp hx
  refine ⟨y, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change f i y - (x : Q) ∈ imageFlag f i.castSucc
  rw [← hab]
  convert (imageFlag f i.castSucc).neg_mem ha using 1
  abel

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E Q : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The adelic bundle on the canonical grade, with the actual restriction
followed by quotient norms. -/
noncomputable def filtrationGraded (V : AdelicVectorBundle S E)
    (F : ℝ → Submodule K E) (t : ℝ)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S (Submodule.FiltrationGraded F t) :=
  (V.restrictOfMeasurableBase (F t) hS).quotientOfMeasurableBase
    ((Submodule.filtrationRightLimit F t).comap (F t).subtype) hS

variable [S.IsProper]

/-- A semistable source of slope `a` maps contractively onto an actual target
of degree at least `a` times its rank. Rank-zero targets are included. This
is the one-step degree argument in the adapted Bost Lemma 7.1 proof. -/
theorem degree_ge_of_semistable_surjective_contraction
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (a : ℝ)
    (hsemi : V.IsMeanSlopeSemistable hS hN) (ha : V.slope hS hN = a)
    (f : E →ₗ[K] Q) (hs : Function.Surjective f)
    (hf : ∀ ω x, W.toNormFamily.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤
      V.toNormFamily.norm ω x) :
    a * (Module.finrank K Q : ℝ) ≤ W.degree hS hN := by
  by_cases hr : Module.finrank K Q = 0
  · rw [hr, Nat.cast_zero, mul_zero, W.degree_eq_zero_of_finrank_eq_zero hS hN hr]
  · have hh := V.mapHeight_le_zero_of_completed_contraction W f hf
    have hm := V.minimalSlope_le_slope_add_mapHeight_of_surjective W hS hN f hs
      (Nat.pos_of_ne_zero hr)
    have he := (V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
      hS hN hV hsemi.1).mp hsemi
    rw [he, ha] at hm
    have hw : a ≤ W.slope hS hN := EReal.coe_le_coe_iff.mp
      (hm.trans (by simpa [add_comm] using add_le_add_left hh (W.slope hS hN : EReal)))
    rw [W.degree_eq_rank_mul_slope hS hN, mul_comm a]
    exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

section ImageFlag

variable {n : ℕ} {D : Fin n → Type*} [∀ i, AddCommGroup (D i)]
  [∀ i, Module K (D i)] [∀ i, FiniteDimensional K (D i)]

omit [S.IsProper] in
/-- The newly adjoined source contracts onto the actual adjacent image-flag
quotient, with the norms inherited from the original target bundle. -/
theorem imageFlagQuotientMap_norm_le
    (V : ∀ i, AdelicVectorBundle S (D i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, D i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) (i : Fin n) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] D i) :
    (W.flagQuotientOfMeasurableBase (Submodule.imageFlag f) hS i).toNormFamily.norm ω
      ((Submodule.imageFlagQuotientMap f i).baseChange (S.ϕ ω).Completion z) ≤
        (V i).toNormFamily.norm ω z := by
  have hc : (Submodule.imageFlag f i.succ).subtype.comp
      (Submodule.imageFlagStep f i) = f i := by ext x; rfl
  have he := DFunLike.congr_fun
    (congrArg (fun g ↦ g.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  dsimp only [Submodule.imageFlagQuotientMap]
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  apply ((W.toNormFamily.restrict (Submodule.imageFlag f i.succ)).quotient_norm_mk_le
    ((Submodule.imageFlag f i.castSucc).comap (Submodule.imageFlag f i.succ).subtype) ω _).trans
  simpa only [NormFamily.restrict_norm, he] using hf i ω z

/-- The componentwise form of Bost Lemma 7.1: finitely many zero or semistable
sources of slope `a`, mapping contractively with spanning images into an actual
Hermitian target, force degree at least `a` times rank. The proof uses the
actual accumulated-image flag, not a norm on their direct sum. -/
theorem degree_ge_of_same_slope_spanning_contractions
    (V : ∀ i, AdelicVectorBundle S (D i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, D i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (a : ℝ)
    (hsemi : ∀ i, Module.finrank K (D i) = 0 ∨
      ((V i).IsMeanSlopeSemistable hS hN ∧ (V i).slope hS hN = a))
    (hspan : (⨆ i, (f i).range) = ⊤)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) :
    a * (Module.finrank K Q : ℝ) ≤ W.degree hS hN := by
  let F := Submodule.imageFlag f
  have hF := Submodule.imageFlag_monotone f
  have hzero := Submodule.imageFlag_zero f
  have htop : F (Fin.last n) = ⊤ := (Submodule.imageFlag_last f).trans hspan
  have hd (i : Fin n) :
      a * (Module.finrank K ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype) : ℝ) ≤
        (W.flagQuotientOfMeasurableBase F hS i).degree hS hN := by
    have hs := Submodule.imageFlagQuotientMap_surjective f i
    rcases hsemi i with hz | ⟨hss, ha⟩
    · have hr : Module.finrank K ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype) = 0 :=
        Nat.eq_zero_of_le_zero (hz ▸ LinearMap.finrank_le_finrank_of_surjective hs)
      rw [hr, Nat.cast_zero, mul_zero,
        (W.flagQuotientOfMeasurableBase F hS i).degree_eq_zero_of_finrank_eq_zero hS hN hr]
    · exact degree_ge_of_semistable_surjective_contraction (V i) _ hS hN (hV i) a hss ha
        (Submodule.imageFlagQuotientMap f i) hs (imageFlagQuotientMap_norm_le V W f hS hf i)
  have hr : (∑ i : Fin n, Module.finrank K
      ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)) = Module.finrank K Q := by
    have h := Submodule.card_flag_quotient_basis F (fun i ↦ Module.finBasis K
      ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype)) hF hzero
    have ht : Module.finrank K (F (Fin.last n)) = Module.finrank K Q := by
      rw [htop, finrank_top]
    refine Eq.trans ?_ ht
    simpa only [Fintype.card_sigma, Fintype.card_fin] using h
  calc
    _ = ∑ i : Fin n, a * (Module.finrank K
        ((F i.succ) ⧸ (F i.castSucc).comap (F i.succ).subtype) : ℝ) := by
      rw [← Finset.mul_sum, ← Nat.cast_sum, hr]
    _ ≤ ∑ i : Fin n, (W.flagQuotientOfMeasurableBase F hS i).degree hS hN :=
      Finset.sum_le_sum fun i _ ↦ hd i
    _ = W.degree hS hN := W.sum_flagQuotient_degree_eq_of_isHermitian
      F hF hzero htop hS hN hW

end ImageFlag

variable {ι : Type*} {C : ι → Type*} [∀ i, AddCommGroup (C i)]
  [∀ i, Module K (C i)] [∀ i, FiniteDimensional K (C i)]

/-- The same-slope image bound is independent of any enumeration of its finite
source family. Internally the enumeration gives the actual image flag. -/
theorem degree_ge_of_finite_same_slope_spanning_contractions [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (a : ℝ)
    (hsemi : ∀ i, Module.finrank K (C i) = 0 ∨
      ((V i).IsMeanSlopeSemistable hS hN ∧ (V i).slope hS hN = a))
    (hspan : (⨆ i, (f i).range) = ⊤)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) :
    a * (Module.finrank K Q : ℝ) ≤ W.degree hS hN := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  apply degree_ge_of_same_slope_spanning_contractions (fun i ↦ V (e i)) W
    (fun i ↦ f (e i)) hS hN (fun i ↦ hV (e i)) hW a (fun i ↦ hsemi (e i)) _
    (fun i ↦ hf (e i))
  exact (Equiv.iSup_comp (g := fun i ↦ (f i).range) e).trans hspan

/-- The same source family bounds the slope of every nonzero actual quotient
of the target. This is the quotient half of the componentwise Bost Lemma 7.1
argument, retaining the target's quotient norm. -/
theorem slope_quotient_ge_of_finite_same_slope_spanning_contractions [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (a : ℝ)
    (hsemi : ∀ i, Module.finrank K (C i) = 0 ∨
      ((V i).IsMeanSlopeSemistable hS hN ∧ (V i).slope hS hN = a))
    (hspan : (⨆ i, (f i).range) = ⊤)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x)
    (U : Submodule K Q) (hr : 0 < Module.finrank K (Q ⧸ U)) :
    a ≤ (W.quotientOfMeasurableBase U hS).slope hS hN := by
  have hspan' : (⨆ i, (U.mkQ.comp (f i)).range) = ⊤ := by
    simp only [LinearMap.range_comp, ← Submodule.map_iSup, hspan, Submodule.map_top,
      LinearMap.range_eq_top.mpr U.mkQ_surjective]
  have hn (i : ι) (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] C i) :
      (W.toNormFamily.quotient U).norm ω
        ((U.mkQ.comp (f i)).baseChange (S.ϕ ω).Completion x) ≤
          (V i).toNormFamily.norm ω x := by
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact (W.toNormFamily.quotient_norm_mk_le U ω _).trans (hf i ω x)
  exact (le_div_iff₀ (Nat.cast_pos.mpr hr)).mpr
    (degree_ge_of_finite_same_slope_spanning_contractions V (W.quotientOfMeasurableBase U hS)
      (fun i ↦ U.mkQ.comp (f i)) hS hN hV (hW.quotient U) a hsemi hspan' hn)

omit [FiniteDimensional K Q] in
/-- For a finite family of actual Hermitian bundles, its common HN image is
a finite real filtration whenever the images span the target. The source
bundles need not have equal slopes. -/
theorem hermitianHN_imageFiltration_finite [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN)
    (hspan : (⨆ i, (f i).range) = ⊤) :
    let F := Submodule.imageFiltration f (fun i ↦ (V i).hermitianHNFiltration hS hN (hV i))
    Antitone F ∧ (∃ t, F t = ⊥) ∧ (∃ t, F t = ⊤) ∧
      ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t := by
  let H := fun i ↦ (V i).hermitianHNFiltration hS hN (hV i)
  have hH : ∀ i, Antitone (H i) := fun i ↦
    (V i).hermitianHNFiltration_antitone hS hN (hV i)
  refine ⟨Submodule.imageFiltration_antitone f H hH,
    Submodule.imageFiltration_exists_bot f H hH ?_,
    Submodule.imageFiltration_exists_top f H hH ?_ hspan,
    Submodule.imageFiltration_left f H ?_⟩
  · intro i
    obtain ⟨t, ht⟩ := (V i).hermitianHNFiltration_separated hS hN (hV i)
    exact ⟨t + 1, ht _ (by linarith)⟩
  · intro i
    obtain ⟨t, ht⟩ := (V i).hermitianHNFiltration_exhaustive hS hN (hV i)
    exact ⟨t, ht _ le_rfl⟩
  · intro i t
    obtain ⟨δ, hδ, hd⟩ := (V i).hermitianHNFiltration_locallyConstantLeft hS hN (hV i) t
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    simpa using hd (t - s) (by linarith) (by linarith)

/-- The canonical maps into the common HN image grade contract its original
actual subquotient norms. No same-slope premise is imposed on the sources. -/
theorem hermitianHN_imageFiltration_gradedMap_norm_le
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) (i : ι) (t : ℝ) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      Submodule.FiltrationGraded ((V i).hermitianHNFiltration hS hN (hV i)) t) :
    let H := fun i ↦ (V i).hermitianHNFiltration hS hN (hV i)
    (W.filtrationGraded (Submodule.imageFiltration f H) t hS).toNormFamily.norm ω
      ((Submodule.filtrationGradedMap (f i) (Submodule.le_comap_imageFiltration f H i) t).baseChange
        (S.ϕ ω).Completion z) ≤
      ((V i).filtrationGraded (H i) t hS).toNormFamily.norm ω z :=
  NormFamily.filtrationGradedMap_norm_le (V i).toNormFamily W.toNormFamily
    (f i) _ t ω (hf i ω) z

/-- The canonical source HN grade, with the actual norm used by the graded
maps above, is zero or semistable of slope equal to its threshold. -/
theorem filtrationGraded_hermitianHN_zero_or_semistable
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (t : ℝ) :
    Module.finrank K (Submodule.FiltrationGraded (V.hermitianHNFiltration hS hN hV) t) = 0 ∨
      ((V.filtrationGraded (V.hermitianHNFiltration hS hN hV) t hS).IsMeanSlopeSemistable hS hN ∧
        (V.filtrationGraded (V.hermitianHNFiltration hS hN hV) t hS).slope hS hN = t) := by
  have h := V.hermitianHNGradedPiece_zero_or_semistable hS hN hV t
  unfold hermitianHNGradedPiece at h
  dsimp only at h
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h
  exact h

/-- Each grade of the actual finite HN image filtration has degree at least
its threshold times its rank. The source HN grades, rather than the ungraded
bundles, supply the common slope. -/
theorem hermitianHN_imageFiltration_grade_degree_ge [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) (t : ℝ) :
    let H := fun i ↦ (V i).hermitianHNFiltration hS hN (hV i)
    let F := Submodule.imageFiltration f H
    t * (Module.finrank K (Submodule.FiltrationGraded F t) : ℝ) ≤
      (W.filtrationGraded F t hS).degree hS hN := by
  let H := fun i ↦ (V i).hermitianHNFiltration hS hN (hV i)
  let F := Submodule.imageFiltration f H
  apply degree_ge_of_finite_same_slope_spanning_contractions
    (fun i ↦ (V i).filtrationGraded (H i) t hS) (W.filtrationGraded F t hS)
    (fun i ↦ Submodule.filtrationGradedMap (f i) (Submodule.le_comap_imageFiltration f H i) t)
    hS hN (fun i ↦ (hV i).filtrationGraded (H i) t) (hW.filtrationGraded F t) t
    (fun i ↦ filtrationGraded_hermitianHN_zero_or_semistable (V i) hS hN (hV i) t)
    (Submodule.imageFiltration_graded_range f H t)
  exact fun i ↦ hermitianHN_imageFiltration_gradedMap_norm_le V W f hS hN hV hf i t

/-- Hermitian flag additivity sums actual graded lower degree bounds over a
finite real filtration. The endpoint identifications retain the ambient
bundle's original norms. -/
theorem finsum_weight_rank_le_degree_of_grade_bounds
    (W : AdelicVectorBundle S Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hW : W.toNormFamily.IsHermitian hN)
    (F : ℝ → Submodule K Q) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hgrade : ∀ t, t * (Module.finrank K (Submodule.FiltrationGraded F t) : ℝ) ≤
      (W.filtrationGraded F t hS).degree hS hN) :
    (∑ᶠ t : ℝ, t * (Module.finrank K (Submodule.FiltrationGraded F t) : ℝ)) ≤
      W.degree hS hN := by
  obtain ⟨n, U, a, hU, hz, ht, _, ha, _, hlevel, hright, hrec⟩ :=
    Submodule.exists_strictMono_flag_and_jumps_of_antitone hF hbot htop hleft
  rw [Submodule.finsum_weight_mul_finrank_filtrationGraded_eq_flag
    U a ha.injective hlevel hright hrec]
  rw [← W.sum_flagQuotient_degree_eq_of_isHermitian U hU.monotone hz ht hS hN hW]
  apply Finset.sum_le_sum
  intro i _
  have hp : (F (a i), Submodule.filtrationRightLimit F (a i)) =
      (U i.succ, U i.castSucc) := Prod.ext (hlevel i) (hright i)
  have he := congrArg (fun p : Submodule K Q × Submodule K Q ↦
    a i * (Module.finrank K (p.1 ⧸ p.2.comap p.1.subtype) : ℝ) ≤
      ((W.restrictOfMeasurableBase p.1 hS).quotientOfMeasurableBase
        (p.2.comap p.1.subtype) hS).degree hS hN) hp
  exact Eq.mp he (hgrade (a i))

/-- The finite-image HN degree inequality needed in Bost Lemma 7.2. Its
hypotheses concern actual completed contractions and spanning images only;
the HN filtration, semistable source grades, image flags, and their lower
degree bounds are all produced by the proof. -/
theorem finsum_hermitianHN_imageFiltration_le_degree [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (hspan : (⨆ i, (f i).range) = ⊤)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) :
    let F := Submodule.imageFiltration f (fun i ↦ (V i).hermitianHNFiltration hS hN (hV i))
    (∑ᶠ t : ℝ, t * (Module.finrank K (Submodule.FiltrationGraded F t) : ℝ)) ≤
      W.degree hS hN := by
  obtain ⟨hF, hbot, htop, hleft⟩ := hermitianHN_imageFiltration_finite V f hS hN hV hspan
  exact finsum_weight_rank_le_degree_of_grade_bounds W hS hN hW _ hF hbot htop hleft
    (hermitianHN_imageFiltration_grade_degree_ge V W f hS hN hV hW hf)

/-- The intrinsic expectation of the finite HN image filtration is at most
the target's actual slope. Rank zero is harmless and is also included. -/
theorem expectation_hermitianHN_imageFiltration_le_slope [Finite ι]
    (V : ∀ i, AdelicVectorBundle S (C i)) (W : AdelicVectorBundle S Q)
    (f : ∀ i, C i →ₗ[K] Q)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : ∀ i, (V i).toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (hspan : (⨆ i, (f i).range) = ⊤)
    (hf : ∀ i ω x, W.toNormFamily.norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤
      (V i).toNormFamily.norm ω x) :
    Submodule.filtrationExpectation (Submodule.imageFiltration f
      (fun i ↦ (V i).hermitianHNFiltration hS hN (hV i))) ≤ W.slope hS hN :=
  div_le_div_of_nonneg_right
    (finsum_hermitianHN_imageFiltration_le_degree V W f hS hN hV hW hspan hf)
    (Nat.cast_nonneg _)

end ArakelovGeometry.AdelicVectorBundle
