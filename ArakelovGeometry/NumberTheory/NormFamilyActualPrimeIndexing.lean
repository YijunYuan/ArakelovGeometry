/-
Copyright (c) 2026 ArakelovGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArakelovGeometry contributors
-/
module

public import ArakelovGeometry.NumberTheory.PrincipalPrimeSupport
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Actual finite primes and scalar unit-ball bounds

Arithmetic producers use the actual finite places and actual adic valuations of
the ring of integers. No completion-degree normalization formula is assumed.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField NNReal

namespace ArakelovGeometry.ActualPrimeIndexing

variable (K : Type*) [Field K] [NumberField K]

/-- A genuine algebraic integer contracts at precisely the prescribed actual finite place. -/
theorem exists_integral_isolated_finitePlace (p : FinitePlace K) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ p (algebraMap (𝓞 K) K f) < 1 ∧
      ∀ q : FinitePlace K, q ≠ p → q (algebraMap (𝓞 K) K f) = 1 := by
  classical
  obtain ⟨f, hf, hvalues, hlt⟩ :=
    PrincipalPrimeSupport.exists_numberField_intValuation_support K {p.maximalIdeal}
  have hnorm (q : FinitePlace K) : q (algebraMap (𝓞 K) K f) =
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero q.maximalIdeal)
        (q.maximalIdeal.intValuation f) : ℝ) :=
    (FinitePlace.norm_embedding_eq q _).symm.trans
      (FinitePlace.norm_embedding_int K q.maximalIdeal f)
  refine ⟨f, hf, ?_, ?_⟩
  · rw [hnorm p]
    have hval : p.maximalIdeal.intValuation f < 1 := (hlt _).mpr (by simp)
    have hnn := (WithZeroMulInt.toNNReal_lt_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal p.maximalIdeal)).mpr hval
    exact_mod_cast hnn
  · intro q hq
    have hprime : q.maximalIdeal ≠ p.maximalIdeal := by
      intro heq
      apply hq
      have hmk := congrArg FinitePlace.mk heq
      simpa only [FinitePlace.mk_maximalIdeal] using hmk
    rw [hnorm q, hvalues q.maximalIdeal, ite_eq_right (by simpa using hprime), map_one]
    rfl

end ArakelovGeometry.ActualPrimeIndexing
