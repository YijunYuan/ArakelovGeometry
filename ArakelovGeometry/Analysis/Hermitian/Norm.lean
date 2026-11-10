/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Inner products inducing prescribed norms

The inner-product core used here fixes the existing scalar action.  Its diagonal
identity constructs an inner-product space with the existing norm and module.
The parallelogram characterization then transports this property along additive
isometries, including the conjugate-linear Riesz equivalence of a Hilbert space
with its continuous dual.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry

variable {L V : Type*} [RCLike L] [NormedAddCommGroup V] [NormedSpace L V]

/-- A positive definite inner-product core whose diagonal gives the prescribed
norm defines an inner-product space with the prescribed scalar action. -/
@[instance_reducible]
def innerProductSpaceOfCoreNorm (c : InnerProductSpace.Core L V)
    (hc : ∀ x, ‖x‖ ^ 2 = RCLike.re (c.inner x x)) : InnerProductSpace L V where
  toNormedSpace := inferInstance
  inner := c.inner
  norm_sq_eq_re_inner := hc
  conj_inner_symm := c.conj_inner_symm
  add_left := c.add_left
  smul_left := c.smul_left

/-- Existence of an inner product for the fixed module and norm is equivalent to
the parallelogram law.  The reverse implication uses Mathlib's polarization
construction, whose scalar action is definitionally the given one. -/
theorem exists_innerProductCore_iff_innerProductSpaceable :
    (∃ c : InnerProductSpace.Core L V, ∀ x, ‖x‖ ^ 2 = RCLike.re (c.inner x x)) ↔
      InnerProductSpaceable V := by
  constructor
  · rintro ⟨c, hc⟩
    let := innerProductSpaceOfCoreNorm c hc
    exact InnerProductSpace.toInnerProductSpaceable L
  · intro h
    let := InnerProductSpace.ofNorm L h.parallelogram_identity
    exact ⟨InnerProductSpace.toCore, norm_sq_eq_re_inner⟩

/-- An additive norm-preserving map pulls back the parallelogram law. -/
theorem innerProductSpaceable_of_norm_preserving_addMonoidHom
    {U W : Type*} [NormedAddCommGroup U] [NormedAddCommGroup W]
    [InnerProductSpaceable W] (f : U →+ W) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    InnerProductSpaceable U := by
  constructor
  intro x y
  simpa only [← hf, map_add, map_sub] using
    InnerProductSpaceable.parallelogram_identity (f x) (f y)

/-- The continuous dual of a complete inner-product norm satisfies the
parallelogram law for its actual operator norm.  The proof transports along the
conjugate-linear Riesz equivalence. -/
theorem innerProductSpaceable_strongDual [CompleteSpace V]
    [InnerProductSpaceable V] : InnerProductSpaceable (StrongDual L V) := by
  let := InnerProductSpace.ofNorm L (InnerProductSpaceable.parallelogram_identity (E := V))
  let e := (InnerProductSpace.toDual L V).symm
  exact innerProductSpaceable_of_norm_preserving_addMonoidHom
    e.toLinearEquiv.toAddEquiv.toAddMonoidHom e.norm_map

end ArakelovGeometry
