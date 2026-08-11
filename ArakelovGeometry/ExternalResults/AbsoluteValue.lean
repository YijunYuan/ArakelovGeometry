/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.FiniteDimension
import ArakelovGeometry.ExternalResults.Ostrowski

/-!
# Completions and restrictions of absolute values

This file collects general facts about absolute values on fields: transfer of the
nonarchimedean property to the completion, characteristic zero and rational normalization for
archimedean absolute values (via Gelfand–Tornheim/Ostrowski), pullback and restriction of
absolute values, and finite-dimensionality of completions in finite extensions.
-/

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
  exact (isometry_algebraMap_withAbs v L).isometry_mapRingHom

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

open UniformSpace in
/-- If the restricted absolute value is nontrivial, then the completion of `K` is a
finite-dimensional vector space over the completion of `L`.

The argument: an `L`-basis of `K` also generates `v.Completion` as a
`(v.restriction L).Completion`-module (although it is not a basis in general). Concretely, the
`(v.restriction L).Completion`-span of such a basis is finite-dimensional, hence closed, and
contains the dense image of `K`, so it is everything. Nontriviality of the absolute value is
needed to make the base completion a `NontriviallyNormedField`, which is what makes
finite-dimensional subspaces closed. -/
theorem finiteDimensional_completion_of_isNontrivial [FiniteDimensional L K]
    (hv : (v.restriction L).IsNontrivial) :
    FiniteDimensional (v.restriction L).Completion v.Completion := by
  classical
  -- Endow the base completion with its nontrivially normed field structure (needed for the
  -- closedness of finite-dimensional subspaces), sharing the canonical `NormedField`.
  let : NontriviallyNormedField (v.restriction L).Completion :=
    { (inferInstance : NormedField (v.restriction L).Completion) with
      non_trivial := by
        obtain ⟨x, hx⟩ := hv.exists_abv_gt_one
        exact ⟨((WithAbs.toAbs (v.restriction L) x : WithAbs (v.restriction L)) :
          (v.restriction L).Completion), by
          rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]; exact hx⟩ }
  -- An `L`-basis of `K`, indexed by a finite type, transported to `WithAbs v`.
  let ι := Module.Free.ChooseBasisIndex L K
  let b : Module.Basis ι L K := Module.Free.chooseBasis L K
  let b' : ι → WithAbs v := fun i ↦ WithAbs.toAbs v (b i)
  set s : Set v.Completion := Set.range (fun i ↦ ((b' i : WithAbs v) : v.Completion)) with hs
  set W : Submodule (v.restriction L).Completion v.Completion := Submodule.span _ s with hW
  -- `W` is finite-dimensional, hence closed.
  have hsfin : s.Finite := Set.finite_range _
  have : FiniteDimensional (v.restriction L).Completion W :=
    FiniteDimensional.span_of_finite _ hsfin
  have hWclosed : IsClosed (W : Set v.Completion) :=
    Submodule.closed_of_finiteDimensional (𝕜 := (v.restriction L).Completion) W
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
  -- `W` contains the dense range of the coercion, so `W = ⊤`.
  have hdense : Dense (W : Set v.Completion) := by
    refine Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := WithAbs v))
    rintro _ ⟨y, rfl⟩
    exact hmemK y
  have hWtop : W = ⊤ := by
    have := Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rwa [hWclosed.submodule_topologicalClosure_eq] at this
  -- Hence the whole completion is finite over the base completion.
  have hfg : (⊤ : Submodule (v.restriction L).Completion v.Completion).FG :=
    hWtop ▸ Submodule.fg_span hsfin
  exact Module.Finite.of_fg_top hfg

/-- The local degree of `K / L` at `v`: the dimension of the completion of `v` over the
completion of its restriction to `L`. -/
noncomputable def localDegree [FiniteDimensional L K] : ℕ :=
  Module.finrank (v.restriction L).Completion v.Completion

end AbsoluteValue
