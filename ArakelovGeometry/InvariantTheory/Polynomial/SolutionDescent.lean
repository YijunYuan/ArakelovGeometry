/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-!
# Descent of simultaneous polynomial solutions

Polynomial equations in finitely many variables that have a simultaneous
solution over an extension of an algebraically closed field already have a
solution over the base field. No algebraicity assumption on the extension is
required. In the binary instability construction, this descends matrix equations
from a residue field.
-/

@[expose] public section

namespace ArakelovGeometry.InvariantTheory

open MvPolynomial

/-- Simultaneous roots of any set of polynomials in finitely many
variables descend from an arbitrary extension to an algebraically closed base field. -/
theorem exists_polynomial_solution_of_extension
    {k κ σ : Type*} [Field k] [IsAlgClosed k] [Field κ] [Algebra k κ] [Finite σ]
    (S : Set (MvPolynomial σ k))
    (h : ∃ x : σ → κ, ∀ p ∈ S, aeval x p = 0) :
    ∃ x : σ → k, ∀ p ∈ S, aeval x p = 0 := by
  obtain ⟨x, hx⟩ := h
  let φ := (aeval x : MvPolynomial σ k →ₐ[k] κ).toRingHom
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ) (RingHom.ker_ne_top φ)
  obtain ⟨y, hy⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hm
  refine ⟨y, fun p hp ↦ (mem_vanishingIdeal_singleton_iff y p).mp ?_⟩
  rw [← hy]
  exact hle (hx p hp)

end ArakelovGeometry.InvariantTheory
