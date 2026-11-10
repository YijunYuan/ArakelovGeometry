/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.JohnContact
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Actual Hermitian polars of norm balls

The polar is defined by the absolute Hermitian pairing. For the image of an
actual norm ball under a continuous linear equivalence, Hahn–Banach and the
Riesz representation theorem prove the bipolar identity. Thus no bidual-ball
equality is supplied as a separate hypothesis in the ellipsoid construction.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

noncomputable section

namespace ArakelovGeometry

variable {L F : Type*} [RCLike L] [NormedAddCommGroup F] [InnerProductSpace L F]

/-- The Hermitian polar uses the absolute value of the actual pairing. -/
def hermitianPolar (B : Set F) : Set F := {u | ∀ x ∈ B, ‖inner L u x‖ ≤ 1}

/-- The Hermitian polar is the pullback of Mathlib's canonical continuous-dual polar. -/
theorem hermitianPolar_eq_preimage_polar (B : Set F) :
    hermitianPolar (L := L) B =
      InnerProductSpace.toDualMap L F ⁻¹' StrongDual.polar L B := by
  ext u
  simp only [hermitianPolar, Set.mem_ofPred_eq, Set.mem_preimage, StrongDual.mem_polar_iff,
    InnerProductSpace.toDualMap_apply_apply]

/-- Hermitian polars are closed without any regularity assumption on the set. -/
theorem isClosed_hermitianPolar (B : Set F) : IsClosed (hermitianPolar (L := L) B) := by
  simp only [hermitianPolar, Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le ((continuous_id.inner continuous_const).norm) continuous_const

/-- Testing against the Euclidean unit ball detects the norm of an actual vector. -/
theorem norm_le_one_of_inner_unitBall_le (u : F)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ‖inner L u x‖ ≤ 1) : ‖u‖ ≤ 1 := by
  have hn : ‖InnerProductSpace.toDualMap L F u‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one (fun x hx => h x hx.le)
  simpa only [LinearIsometry.norm_map] using hn

/-- Containing the Euclidean unit ball bounds the actual Hermitian polar by it. -/
theorem hermitianPolar_subset_unitBall {B : Set F} (hB : Metric.closedBall 0 1 ⊆ B) :
    hermitianPolar (L := L) B ⊆ Metric.closedBall 0 1 := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  apply norm_le_one_of_inner_unitBall_le (L := L) u
  intro x hx
  exact hu x (hB (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx))

/-- In finite-dimensional Hilbert geometry such polars are actual compact sets. -/
theorem isCompact_hermitianPolar_of_unitBall_subset [ProperSpace F]
    {B : Set F} (hB : Metric.closedBall 0 1 ⊆ B) :
    IsCompact (hermitianPolar (L := L) B) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_hermitianPolar B)
    (hermitianPolar_subset_unitBall hB)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace L E]

/-- The original norm unit ball expressed through a genuine continuous linear
equivalence to Hilbert coordinates. -/
def unitBallInCoordinates (e : E ≃L[L] F) : Set F := {x | ‖e.symm x‖ ≤ 1}

/-- This coordinate body is exactly the image of the original closed unit ball. -/
theorem unitBallInCoordinates_eq_image (e : E ≃L[L] F) :
    unitBallInCoordinates e = e '' Metric.closedBall 0 1 := by
  ext x
  constructor
  · intro hx
    change ‖e.symm x‖ ≤ 1 at hx
    exact ⟨e.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx,
      e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change ‖e.symm (e y)‖ ≤ 1
    simpa only [e.symm_apply_apply, Metric.mem_closedBall, dist_zero_right] using hy

/-- The actual coordinate norm ball is compact in finite-dimensional Hilbert geometry. -/
theorem isCompact_unitBallInCoordinates [ProperSpace F] (e : E ≃L[L] F) :
    IsCompact (unitBallInCoordinates e) := by
  have hclosed : IsClosed (unitBallInCoordinates e) :=
    isClosed_le e.symm.continuous.norm continuous_const
  refine (isCompact_closedBall 0 ‖e.toContinuousLinearMap‖).of_isClosed_subset hclosed ?_
  intro x hx
  change ‖e.symm x‖ ≤ 1 at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖x‖ = ‖e (e.symm x)‖ := congrArg norm (e.apply_symm_apply x).symm
    _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm x‖ := e.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.toContinuousLinearMap‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _ = _ := mul_one _

/-- A genuine positive-radius Euclidean ball lies in the coordinate norm ball. -/
theorem exists_closedBall_subset_unitBallInCoordinates (e : E ≃L[L] F) :
    ∃ c > 0, Metric.closedBall 0 c ⊆ unitBallInCoordinates e := by
  let C := ‖e.symm.toContinuousLinearMap‖
  have hC : 0 ≤ C := norm_nonneg _
  have hCp : 0 < C + 1 := by positivity
  refine ⟨1 / (C + 1), one_div_pos.mpr hCp, fun x hx => ?_⟩
  have hx' : ‖x‖ ≤ 1 / (C + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  change ‖e.symm x‖ ≤ 1
  have hbound := e.symm.toContinuousLinearMap.le_opNorm x
  have hscale := (le_div_iff₀ hCp).mp hx'
  change ‖e.symm x‖ ≤ C * ‖x‖ at hbound
  nlinarith [norm_nonneg x]

/-- Hahn–Banach in the original norm, followed by actual Riesz representation,
proves the bipolar test for the coordinate unit ball, including dimension zero. -/
theorem mem_unitBallInCoordinates_iff_forall_polar [CompleteSpace F]
    (e : E ≃L[L] F) (x : F) :
    x ∈ unitBallInCoordinates e ↔
      ∀ u ∈ hermitianPolar (L := L) (unitBallInCoordinates e), ‖inner L u x‖ ≤ 1 := by
  constructor
  · intro hx u hu
    exact hu x hx
  · intro hx
    obtain ⟨g, hg, hval⟩ := exists_dual_vector'' L (e.symm x)
    let f := g.comp e.symm.toContinuousLinearMap
    let u := (InnerProductSpace.toDual L F).symm f
    have hu : u ∈ hermitianPolar (L := L) (unitBallInCoordinates e) := by
      intro y hy
      rw [show inner L u y = f y from InnerProductSpace.toDual_symm_apply]
      change ‖g (e.symm y)‖ ≤ 1
      calc
        _ ≤ ‖g‖ * ‖e.symm y‖ := g.le_opNorm _
        _ ≤ 1 * 1 := mul_le_mul hg hy (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    have hux := hx u hu
    rw [show inner L u x = f x from InnerProductSpace.toDual_symm_apply] at hux
    change ‖g (e.symm x)‖ ≤ 1 at hux
    rw [hval, RCLike.norm_of_nonneg (norm_nonneg _)] at hux
    exact hux

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For an actual norm ball and a Hermitian matrix, ellipsoid feasibility is
equivalent to mapping every point of its actual polar into the Euclidean unit ball. -/
theorem hermitian_ellipsoid_feasible_iff_polar
    (e : E ≃L[L] EuclideanSpace L n) {A : Matrix n n L} (hA : A.IsHermitian) :
    (∀ x : EuclideanSpace L n, ‖x‖ ≤ 1 →
      (Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A x ∈ unitBallInCoordinates e) ↔
    ∀ u ∈ hermitianPolar (L := L) (unitBallInCoordinates e),
      ‖(Matrix.toEuclideanCLM (𝕜 := L) (n := n)) A u‖ ≤ 1 := by
  have hT := (hA.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := L) (n := n))).isSymmetric
  constructor
  · intro h u hu
    apply norm_le_one_of_inner_unitBall_le (L := L)
    intro x hx
    rw [hT.apply_clm]
    exact hu _ (h x hx)
  · intro h x hx
    rw [mem_unitBallInCoordinates_iff_forall_polar]
    intro u hu
    rw [← hT.apply_clm]
    exact (norm_inner_le_norm _ _).trans
      (by simpa only [one_mul] using mul_le_mul (h u hu) hx (norm_nonneg _) zero_le_one)

end ArakelovGeometry
