/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.AlgebraicClosureDense

/-!
# Polynomial approximation over a dense subfield

Approximation of the lower coefficients of a vanishing monic polynomial
produces a monic polynomial over the original dense subfield with arbitrarily
small actual evaluation. No finite-extension or separability premise is used.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Approximating the lower coefficients over the original dense subfield gives
an actual monic polynomial of the same degree with arbitrarily small evaluation. -/
theorem exists_monic_aeval_abv_lt (K₀ : Subfield K) (w : AbsoluteValue L ℝ)
    (hK₀ : DenseRange (fun c : K₀ =>
      algebraMap K (w.restriction K).Completion (c : K)))
    (f : Polynomial K) (hf : f.Monic) (a : L) (ha : (Polynomial.aeval a) f = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : Polynomial K₀, g.Monic ∧ g.natDegree = f.natDegree ∧
      w ((Polynomial.aeval a) g) < δ := by
  classical
  let B := (w.restriction K).Completion
  let C := w.Completion
  let α : C := algebraMap L C a
  let d := Fintype.linearCombination B (fun i : Fin f.natDegree => α ^ (i : ℕ))
  let c₀ : Fin f.natDegree → B := fun i => algebraMap K B (f.coeff i)
  let u : (Fin f.natDegree → B) → C := fun c => α ^ f.natDegree + d c
  have hd : Continuous d := (linearMapToNormedAddGroupHom d).continuous
  have hu : Continuous u := continuous_const.add hd
  have hfC : (Polynomial.aeval α) f = 0 := by
    change (Polynomial.aeval ((IsScalarTower.toAlgHom K L C) a)) f = 0
    rw [Polynomial.aeval_algHom_apply]
    simp [ha]
  have hd₀ : d c₀ = ∑ i ∈ Finset.range f.natDegree,
      algebraMap K C (f.coeff i) * α ^ i := by
    simp only [d, Fintype.linearCombination_apply, c₀, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply K B C]
    exact Fin.sum_univ_eq_sum_range
      (fun i : ℕ => algebraMap K C (f.coeff i) * α ^ i) f.natDegree
  have hu₀ : u c₀ = 0 := by
    dsimp only [u]
    rw [hd₀]
    rw [hf.as_sum] at hfC
    simpa only [map_add, map_sum, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X_pow] using hfC
  have hD : DenseRange (fun c : Fin f.natDegree → K₀ =>
      fun i => algebraMap K B (c i : K)) := DenseRange.piMap (fun _ => hK₀)
  obtain ⟨c, hc⟩ := hD.exists_mem_open (isOpen_lt hu.norm continuous_const)
    ⟨c₀, by simpa [hu₀] using hδ⟩
  let g : Polynomial K₀ := Polynomial.X ^ f.natDegree +
    ∑ i : Fin f.natDegree, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
  have hg : g.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)
  have hdeg : g.natDegree = f.natDegree := by
    dsimp only [g]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt
      (by simpa only [Polynomial.degree_X_pow] using Polynomial.degree_sum_fin_lt c),
      Polynomial.natDegree_X_pow]
  have he : algebraMap L C ((Polynomial.aeval a) g) =
      u (fun i => algebraMap K B (c i : K)) := by
    change (IsScalarTower.toAlgHom K₀ L C) ((Polynomial.aeval a) g) = _
    rw [← Polynomial.aeval_algHom_apply]
    simp only [g, u, d, Fintype.linearCombination_apply, map_add, map_sum,
      map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← IsScalarTower.algebraMap_apply K B C]
    rw [IsScalarTower.algebraMap_apply K₀ K C]
    rfl
  refine ⟨g, hg, hdeg, ?_⟩
  change ‖u (fun i => algebraMap K B (c i : K))‖ < δ at hc
  rw [← he] at hc
  change ‖((WithAbs.toAbs w ((Polynomial.aeval a) g) : WithAbs w) : C)‖ < δ at hc
  simpa only [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.ofAbs_toAbs] using hc

variable [IsAlgClosed L] [Algebra.IsAlgebraic K L]
/-- Approximated monic polynomials produce nearby elements of the actual
relative algebraic closure of the original dense subfield. -/
theorem exists_nearby_mem_algebraicClosure
    (K₀ : Subfield K) (w : AbsoluteValue L ℝ)
    (hK₀ : DenseRange (fun c : K₀ =>
      algebraMap K (w.restriction K).Completion (c : K)))
    (a : L) (ε : ℝ) (hε : 0 < ε) :
    ∃ b ∈ algebraicClosure K₀ L, w (a - b) < ε := by
  let f := minpoly K a
  have hf : f.Monic := minpoly.monic (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  obtain ⟨g, hg, hdeg, hv⟩ := exists_monic_aeval_abv_lt K₀ w hK₀ f hf a
    (minpoly.aeval K a) (ε ^ f.natDegree) (pow_pos hε _)
  let p := g.map (algebraMap K₀ L)
  have hp : p.Monic := hg.map (algebraMap K₀ L)
  have hvp : w (p.eval a) < ε ^ p.natDegree := by
    simpa only [p, Polynomial.eval_map_algebraMap, Polynomial.natDegree_map, hdeg] using hv
  obtain ⟨b, hb, hc⟩ := exists_root_abv_sub_lt w p hp (IsAlgClosed.splits p) a ε hε hvp
  refine ⟨b, mem_algebraicClosure_iff.mpr ?_, hc⟩
  refine ⟨g, hg.ne_zero, ?_⟩
  have hb₀ := (Polynomial.mem_roots hp.ne_zero).mp hb
  change p.eval b = 0 at hb₀
  simpa only [p, Polynomial.eval_map_algebraMap] using hb₀
/-- The same canonical relative algebraic closure is dense in an extending
completion, with no separability or countability premise on this local assertion. -/
theorem denseRange_algebraicClosure_subfield
    (K₀ : Subfield K) (w : AbsoluteValue L ℝ)
    (hK₀ : DenseRange (fun c : K₀ =>
      algebraMap K (w.restriction K).Completion (c : K))) :
    DenseRange (fun b : (algebraicClosure K₀ L).toSubfield =>
      algebraMap L w.Completion (b : L)) := by
  have hd : DenseRange (fun b : (algebraicClosure K₀ L).toSubfield =>
      WithAbs.toAbs w (b : L)) := by
    rw [Metric.denseRange_iff]
    intro a ε hε
    obtain ⟨b, hb, hc⟩ := exists_nearby_mem_algebraicClosure K₀ w hK₀ a.ofAbs ε hε
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
    simpa only [WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs] using hc
  have hdc := (UniformSpace.Completion.denseRange_coe (α := WithAbs w)).comp hd
    (UniformSpace.Completion.continuous_coe (WithAbs w))
  exact hdc
universe w
variable {S : AdelicStructure.{u, w} K}
/-- One canonical countable relative algebraic closure works simultaneously
at every actual place of the algebraic-closure extension. -/
theorem AdelicStructure.HasCommonCountableDenseSubfield.algebraicExtension_of_isAlgClosed
    (hS : S.HasCommonCountableDenseSubfield) :
    (S.algebraicExtension L).HasCommonCountableDenseSubfield := by
  obtain ⟨K₀, hc, hd⟩ := hS
  let : Countable K₀ := hc
  refine ⟨(algebraicClosure K₀ L).toSubfield, countable_algebraicClosure_subfield K₀, ?_⟩
  intro x
  change S.ParameterSpaceExtension L at x
  have hb : DenseRange (fun c : K₀ =>
      algebraMap K (x.abv.restriction K).Completion (c : K)) := by
    rw [x.restrict_eq]
    exact hd x.base
  exact denseRange_algebraicClosure_subfield K₀ x.abv hb

end ArakelovGeometry
