/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Coordinate estimates for linear functionals

Finite coordinate-sum norms have coordinate-maximum dual norms.  Over an
ultrametric field the same bound holds for the coordinate-maximum norm.
The estimates below include an empty basis.
-/

@[expose] public section

namespace ArakelovGeometry

variable {L V ι : Type*} [NormedField L] [AddCommGroup V] [Module L V] [Fintype ι]

/-- A functional is bounded for the coordinate sum norm by the maximum of its
values on the basis. -/
theorem norm_linearMap_apply_le_basis_sum (b : Module.Basis ι L V)
    (f : V →ₗ[L] L) (x : V) :
    ‖f x‖ ≤ ‖fun i => f (b i)‖ * ∑ i, ‖b.equivFun x i‖ := by
  classical
  have he : f x = ∑ i, f (b i) * b.equivFun x i := by
    calc
      f x = f (∑ i, b.equivFun x i • b i) := congrArg f (b.sum_equivFun x).symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [he, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm (fun i => f (b i)) i) (norm_nonneg _)

/-- Over an ultrametric field the coordinate maximum norm has the same
functional bound.  The finite-sum inequality includes an empty index set. -/
theorem norm_linearMap_apply_le_basis_max [IsUltrametricDist L]
    (b : Module.Basis ι L V) (f : V →ₗ[L] L) (x : V) :
    ‖f x‖ ≤ ‖fun i => f (b i)‖ * ‖b.equivFun x‖ := by
  classical
  have he : f x = ∑ i, f (b i) * b.equivFun x i := by
    calc
      f x = f (∑ i, b.equivFun x i • b i) := congrArg f (b.sum_equivFun x).symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  rw [he]
  have hh : ‖∑ i, f (b i) * b.equivFun x i‖₊ ≤
      ‖fun i => f (b i)‖₊ * ‖b.equivFun x‖₊ := by
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro i hi
    rw [nnnorm_mul]
    exact mul_le_mul' (nnnorm_le_pi_nnnorm (fun i => f (b i)) i)
      (nnnorm_le_pi_nnnorm (b.equivFun x) i)
  exact_mod_cast hh

end ArakelovGeometry
