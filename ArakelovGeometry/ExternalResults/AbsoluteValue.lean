/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.ExternalResults.Ostrowski
public import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Completions and restrictions of absolute values

This file collects general facts about absolute values on fields: transfer of the
nonarchimedean property to the completion, characteristic zero and rational normalization for
archimedean absolute values (via Gelfand–Tornheim/Ostrowski), pullback and restriction of
absolute values, and finite-dimensionality of completions in finite extensions.
-/

@[expose] public section

namespace AbsoluteValue

/-- An absolute value is nonarchimedean iff the induced absolute value on the completion is. -/
theorem isNonarchimedean_completion_iff {K : Type*} [Field K] (abs : AbsoluteValue K ℝ) :
    letI := abs.toNormedField;
    IsNonarchimedean abs ↔
      IsNonarchimedean
        (UniformSpace.Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue := by
  let := abs.toNormedField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro z w
    have hnorm := h
    change IsNonarchimedean (norm : K → ℝ) at hnorm
    refine UniformSpace.Completion.induction_on₂ z w ?_ ?_
    · change IsClosed {p : UniformSpace.Completion K × UniformSpace.Completion K |
          ‖p.1 + p.2‖ ≤ max ‖p.1‖ ‖p.2‖}
      exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x y
      rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk]
      simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using
        hnorm x y
  · intro x y
    specialize h x y
    rw [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] at h
    change ‖x + y‖ ≤ max ‖x‖ ‖y‖
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using h

/-- A field carrying an archimedean absolute value has characteristic zero. -/
theorem charZero_of_not_isNonarchimedean {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
    (habs : ¬IsNonarchimedean abs) : CharZero K := by
  let := abs.toNormedField
  replace habs : ¬IsNonarchimedean
      (UniformSpace.Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue := by
    contrapose habs
    rwa [isNonarchimedean_completion_iff]
  rcases exists_ringEquiv_real_or_complex_of_complete _ habs (CauSeq.isComplete_completion abs)
    with ⟨σ, -⟩ | ⟨σ, -⟩ <;>
  · have : CharZero (UniformSpace.Completion K) := RingHom.charZero σ.toRingHom
    exact RingHom.charZero UniformSpace.Completion.coeRingHom

/-- An archimedean absolute value restricts to a power `|·| ^ s`, `s ∈ (0, 1]`, of the usual
absolute value on `ℚ`. -/
theorem exists_rpow_eq_of_not_isNonarchimedean {K : Type*} [Field K] (abs : AbsoluteValue K ℝ)
    (habs : ¬IsNonarchimedean abs) :
    ∃ s : ℝ, s ∈ Set.Ioc 0 1 ∧ ∀ q : ℚ, abs q = Rat.AbsoluteValue.real q ^ s := by
  let := abs.toNormedField
  have := exists_ringEquiv_real_or_complex_of_complete
    (UniformSpace.Completion.instNormedFieldOfCompletableTopField K).toAbsoluteValue ?_ ?_
  · rcases this with h1 | h1
    · rcases h1 with ⟨σ, s, hs1, hs2⟩
      use s
      refine ⟨hs1, fun q ↦ ?_⟩
      specialize hs2 q
      simp only [map_ratCast, Rat.norm_cast_real] at hs2
      convert hs2
      · simpa [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
          (calc
            abs (q : K) = ‖((q : K) : UniformSpace.Completion K)‖ := by
              rw [UniformSpace.Completion.norm_coe]; rfl
            _ = ‖(q : UniformSpace.Completion K)‖ := by
              congr
              exact map_ratCast
                (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) q)
      · simp [← Rat.norm_cast_real]
    · rcases h1 with ⟨σ, s, hs1, hs2⟩
      use s
      refine ⟨hs1, fun q ↦ ?_⟩
      specialize hs2 q
      simp only [map_ratCast] at hs2
      convert hs2
      · simpa [NormedField.toAbsoluteValue, AbsoluteValue.coe_mk, MulHom.coe_mk] using
          (calc
            abs (q : K) = ‖((q : K) : UniformSpace.Completion K)‖ := by
              rw [UniformSpace.Completion.norm_coe]; rfl
            _ = ‖(q : UniformSpace.Completion K)‖ := by
              congr
              exact map_ratCast
                (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) q)
      · simp
  · contrapose habs
    exact (isNonarchimedean_completion_iff abs).mpr habs
  · exact CauSeq.isComplete_completion abs

/-- The pullback of an absolute value along a ring homomorphism of fields. -/
def pullback {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {L : Type*} [Field L]
    (i : L →+* K) : AbsoluteValue L ℝ where
  toFun x := v (i x)
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' x y := by simp [v.add_le (i x) (i y)]

/-- The restriction of an absolute value on `K` to a field `L` embedded via `algebraMap L K`. -/
abbrev restriction {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L]
    [Algebra L K] : AbsoluteValue L ℝ := pullback v (algebraMap L K)

/-- An absolute value on a finite field extension is trivial if its restriction is trivial. -/
theorem not_isNontrivial_of_finite {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type*) [Field L] [Algebra L K] [FiniteDimensional L K]
    (hv : ¬(v.restriction L).IsNontrivial) : ¬v.IsNontrivial := by
  classical
  let b := Module.Free.chooseBasis L K
  have hscalar (c : L) : v (algebraMap L K c) ≤ 1 := by
    by_cases hc : c = 0
    · simp [hc]
    · exact le_of_eq (not_isNontrivial_apply hv hc)
  have hbound (y : K) : v y ≤ ∑ i, v (b i) := by
    conv_lhs => rw [← b.sum_repr y]
    refine (v.sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left (v.nonneg _) (hscalar _)
  intro hn
  obtain ⟨x, hx⟩ := hn.exists_abv_gt_one
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ i, v (b i)) hx
  exact (not_lt_of_ge (by simpa only [map_pow] using hbound (x ^ n))) hn

/-- Triviality of absolute values is preserved by algebraic extension. -/
theorem not_isNontrivial_of_isAlgebraic {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type*) [Field L] [Algebra L K] [Algebra.IsAlgebraic L K]
    (hv : ¬(v.restriction L).IsNontrivial) : ¬v.IsNontrivial := by
  intro hn
  obtain ⟨x, hx⟩ := hn.exists_abv_gt_one
  let F := IntermediateField.adjoin L ({x} : Set K)
  have : FiniteDimensional L F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hF : ¬(v.restriction F).IsNontrivial :=
    not_isNontrivial_of_finite (v.restriction F) L (by simpa [restriction, pullback] using hv)
  let y : F := ⟨x, IntermediateField.subset_adjoin L {x} (Set.mem_singleton x)⟩
  have hy : y ≠ 0 := by
    intro hy
    have hx0 : x = 0 := congrArg Subtype.val hy
    simp [hx0] at hx
    norm_num at hx
  have hy1 := not_isNontrivial_apply hF hy
  exact (ne_of_gt hx) hy1

/-- A field with the trivial absolute value is complete. -/
theorem completeSpace_withAbs_of_not_isNontrivial {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : ¬v.IsNontrivial) : CompleteSpace (WithAbs v) := by
  have : DiscreteUniformity (WithAbs v) := ⟨Metric.uniformSpace_eq_bot.mpr ⟨1, zero_lt_one,
    fun x y hxy ↦ by
      change 1 ≤ dist x y
      rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs,
        not_isNontrivial_apply hv (by
          simpa using sub_ne_zero.mpr ((WithAbs.ofAbs_injective v).ne hxy))]⟩⟩
  infer_instance

/-- The completion of a trivially valued field has no new elements. -/
theorem surjective_coe_completion_of_not_isNontrivial {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hv : ¬v.IsNontrivial) :
    Function.Surjective (fun x : WithAbs v ↦ (x : v.Completion)) := by
  have := completeSpace_withAbs_of_not_isNontrivial v hv
  intro x
  have hx := UniformSpace.Completion.denseRange_coe (α := WithAbs v) x
  rwa [(UniformSpace.Completion.coe_isometry.isClosedEmbedding.isClosed_range).closure_eq] at hx

open WithAbs in
/-- The `algebraMap` from `WithAbs (v.restriction L)` to `WithAbs v` is an isometry. -/
theorem isometry_algebraMap_withAbs {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*)
    [Field L] [Algebra L K] : Isometry (algebraMap (WithAbs (v.restriction L)) (WithAbs v)) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap]; rfl

/-- `v.Completion` is an algebra over the completion of the restriction of `v`. -/
noncomputable instance algebraCompletion {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type*) [Field L] [Algebra L K] :
    Algebra (v.restriction L).Completion v.Completion :=
  (UniformSpace.Completion.mapRingHom (algebraMap (WithAbs (v.restriction L)) (WithAbs v))
    (isometry_algebraMap_withAbs v L).continuous).toAlgebra

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra L K]

/-- The algebra map between the completions is the map induced by the `algebraMap` on the
underlying `WithAbs` types. -/
theorem algebraMap_completion_def :
    (algebraMap (v.restriction L).Completion v.Completion) =
      UniformSpace.Completion.mapRingHom (algebraMap (WithAbs (v.restriction L)) (WithAbs v))
        (isometry_algebraMap_withAbs v L).continuous := rfl

/-- The algebra map between the completions is an isometry. -/
theorem isometry_algebraMap_completion :
    Isometry (algebraMap (v.restriction L).Completion v.Completion) := by
  rw [algebraMap_completion_def]
  exact UniformSpace.Completion.isometry_mapRingHom (isometry_algebraMap_withAbs v L)

/-- The algebra map between the completions preserves the norm. -/
theorem norm_algebraMap_completion (a : (v.restriction L).Completion) :
    ‖algebraMap (v.restriction L).Completion v.Completion a‖ = ‖a‖ := by
  simpa using (isometry_algebraMap_completion v L).norm_map_of_map_zero (map_zero _) a

/-- `v.Completion` is a normed space over `(v.restriction L).Completion`. -/
noncomputable instance : NormedSpace (v.restriction L).Completion v.Completion where
  norm_smul_le a b := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_completion]

/-- The coercion `WithAbs v → v.Completion` is semilinear over the scalar action of
`(v.restriction L).Completion`. -/
theorem coe_smul_completion (c : WithAbs (v.restriction L)) (y : WithAbs v) :
    ((c • y : WithAbs v) : v.Completion)
      = (c : (v.restriction L).Completion) • (y : v.Completion) := by
  rw [Algebra.smul_def, Algebra.smul_def, UniformSpace.Completion.coe_mul,
    algebraMap_completion_def, UniformSpace.Completion.mapRingHom_coe]

/-- A finite basis of a field extension spans the completed extension over the completed base. -/
theorem span_coe_basis_eq_top {ι : Type*} [Finite ι] (b : Module.Basis ι L K) :
    Submodule.span (v.restriction L).Completion
      (Set.range fun i ↦ (WithAbs.toAbs v (b i) : v.Completion)) = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  have : FiniteDimensional L K := Module.Finite.of_basis b
  let b' : ι → WithAbs v := fun i ↦ WithAbs.toAbs v (b i)
  let s : Set v.Completion := Set.range (fun i ↦ ((b' i : WithAbs v) : v.Completion))
  let W : Submodule (v.restriction L).Completion v.Completion := Submodule.span _ s
  change W = ⊤
  -- Every element of `WithAbs v` (i.e. of `K`) lies in `W`.
  have hmemK : ∀ y : WithAbs v, ((y : v.Completion)) ∈ W := by
    intro y
    have hrepr : ∑ i, WithAbs.toAbs (v.restriction L) (b.repr (WithAbs.ofAbs y) i) • b' i = y := by
      apply WithAbs.ofAbs_injective v
      rw [show (∑ i, WithAbs.toAbs (v.restriction L) (b.repr (WithAbs.ofAbs y) i) • b' i).ofAbs
          = ∑ i, (WithAbs.toAbs (v.restriction L) (b.repr (WithAbs.ofAbs y) i) • b' i).ofAbs from
        map_sum (WithAbs.equiv v) _ _]
      simp only [WithAbs.smul_left_def, WithAbs.smul_right_def, WithAbs.ofAbs_toAbs, b']
      exact b.sum_repr (WithAbs.ofAbs y)
    rw [← hrepr, show ((∑ i, WithAbs.toAbs (v.restriction L) (b.repr (WithAbs.ofAbs y) i) • b' i :
          WithAbs v) : v.Completion)
        = ∑ i, ((WithAbs.toAbs (v.restriction L) (b.repr (WithAbs.ofAbs y) i) • b' i :
          WithAbs v) : v.Completion) from map_sum (UniformSpace.Completion.coeRingHom) _ _]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [coe_smul_completion]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  by_cases hv : (v.restriction L).IsNontrivial
  · let : NontriviallyNormedField (v.restriction L).Completion :=
      { (inferInstance : NormedField (v.restriction L).Completion) with
        non_trivial := by
          obtain ⟨x, hx⟩ := hv.exists_abv_gt_one
          exact ⟨((WithAbs.toAbs (v.restriction L) x : WithAbs (v.restriction L)) :
            (v.restriction L).Completion), by
            rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]; exact hx⟩ }
    have : FiniteDimensional (v.restriction L).Completion W :=
      FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have hWclosed : IsClosed (W : Set v.Completion) :=
      Submodule.closed_of_finiteDimensional (𝕜 := (v.restriction L).Completion) W
    have hdense : Dense (W : Set v.Completion) := by
      refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithAbs v))
      rintro _ ⟨y, rfl⟩
      exact hmemK y
    have := Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rwa [hWclosed.submodule_topologicalClosure_eq] at this
  · apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := surjective_coe_completion_of_not_isNontrivial v
      (not_isNontrivial_of_finite v L hv) x
    exact hmemK y

/-- Completion preserves finiteness of a field extension, including at the trivial absolute
value. -/
theorem finiteDimensional_completion [FiniteDimensional L K] :
    FiniteDimensional (v.restriction L).Completion v.Completion := by
  classical
  have hfg := Submodule.fg_span (R := (v.restriction L).Completion) (Set.finite_range
    (fun i ↦ (WithAbs.toAbs v (Module.Free.chooseBasis L K i) : v.Completion)))
  rw [span_coe_basis_eq_top v L (Module.Free.chooseBasis L K)] at hfg
  exact Module.Finite.of_fg_top hfg

/-- For a nontrivial restricted absolute value, the completed extension is finite dimensional. -/
theorem finiteDimensional_completion_of_isNontrivial [FiniteDimensional L K]
    (_hv : (v.restriction L).IsNontrivial) :
    FiniteDimensional (v.restriction L).Completion v.Completion :=
  finiteDimensional_completion v L

/-- Completion cannot increase the degree of a finite field extension. -/
theorem finrank_completion_le [FiniteDimensional L K] :
    Module.finrank (v.restriction L).Completion v.Completion ≤ Module.finrank L K := by
  classical
  have h := finrank_range_le_card (R := (v.restriction L).Completion)
    (fun i ↦ (WithAbs.toAbs v (Module.Free.chooseBasis L K i) : v.Completion))
  rw [Set.finrank, span_coe_basis_eq_top v L (Module.Free.chooseBasis L K), finrank_top] at h
  exact h.trans_eq (Module.finrank_eq_card_chooseBasisIndex L K).symm

/-- The local degree of `K / L` at `v`: the dimension of the completion of `v` over the
completion of its restriction to `L`. -/
noncomputable def localDegree [FiniteDimensional L K] : ℕ :=
  Module.finrank (v.restriction L).Completion v.Completion

end AbsoluteValue
