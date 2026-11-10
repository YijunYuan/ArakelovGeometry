/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The actual integer dual in normed spaces and Euclidean reciprocal covolume -/

@[expose] public section

noncomputable section
open Module MeasureTheory

namespace ArakelovGeometry.GeometryOfNumbers

variable {E : Type*} [NormedAddCommGroup E]

section Normed

variable [NormedSpace ℝ E]

/-- The actual continuous real functionals taking integer values on the original lattice. -/
def integralDual (L : Submodule ℤ E) : Submodule ℤ (StrongDual ℝ E) where
  carrier := {f | ∀ x ∈ L, f x ∈ LinearMap.range (Algebra.linearMap ℤ ℝ)}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro f g hf hg x hx
    simpa using (LinearMap.range (Algebra.linearMap ℤ ℝ)).add_mem (hf x hx) (hg x hx)
  smul_mem' := by
    intro a f hf x hx
    simpa using (LinearMap.range (Algebra.linearMap ℤ ℝ)).smul_mem a (hf x hx)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The canonical algebraic dual basis interpreted in the actual continuous dual. -/
def continuousDualBasis {ι : Type*} [Finite ι] (b : Basis ι ℝ E) :
    Basis ι ℝ (StrongDual ℝ E) := by
  classical
  exact b.dualBasis.map LinearMap.toContinuousLinearMap

@[simp]
theorem continuousDualBasis_apply {ι : Type*} [Finite ι] (b : Basis ι ℝ E)
    (i : ι) (x : E) : continuousDualBasis b i x = b.repr x i := by
  classical
  simp [continuousDualBasis]

@[simp]
theorem continuousDualBasis_repr {ι : Type*} [Finite ι] (b : Basis ι ℝ E)
    (f : StrongDual ℝ E) (i : ι) : (continuousDualBasis b).repr f i = f (b i) := by
  classical
  simp [continuousDualBasis, Basis.map_repr]

/-- The actual integer dual is the integer span of the constructed continuous dual basis. -/
theorem integralDual_span {ι : Type*} [Finite ι] (b : Basis ι ℝ E) :
    integralDual (Submodule.span ℤ (Set.range b)) =
      Submodule.span ℤ (Set.range (continuousDualBasis b)) := by
  ext f
  rw [(continuousDualBasis b).mem_span_iff_repr_mem ℤ]
  simp only [continuousDualBasis_repr]
  constructor
  · intro hf i
    exact hf _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hf x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hf i
    | zero => simp
    | add x y hx hy hfx hfy =>
      simpa only [map_add] using
        (LinearMap.range (Algebra.linearMap ℤ ℝ)).add_mem hfx hfy
    | smul a x hx hfx =>
      simpa only [map_zsmul] using
        (LinearMap.range (Algebra.linearMap ℤ ℝ)).smul_mem a hfx

/-- The constructed integer dual is discrete for every genuine primal full lattice. -/
theorem integralDual_discrete (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] : DiscreteTopology (integralDual L) := by
  classical
  rw [← Basis.ofZLatticeBasis_span ℝ L (Module.finBasis ℤ L), integralDual_span]
  infer_instance

/-- The constructed actual integer dual spans the full continuous dual over the reals. -/
theorem integralDual_isZLattice (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    letI := integralDual_discrete L
    IsZLattice ℝ (integralDual L) := by
  classical
  let := integralDual_discrete L
  refine ⟨?_⟩
  rw [← Basis.ofZLatticeBasis_span ℝ L (Module.finBasis ℤ L), integralDual_span]
  exact ZSpan.span_top _

end FiniteDimensional

end Normed

section Euclidean

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The unique real inner product compatible with the existing StrongDual operator norm.
It is constructed from the actual Riesz isometry and is not a global instance. -/
@[instance_reducible]
def strongDualInnerProduct : InnerProductSpace ℝ (StrongDual ℝ E) := by
  apply InnerProductSpace.ofNorm ℝ
  intro f g
  have h := parallelogram_law_with_norm ℝ
    ((InnerProductSpace.toDual ℝ E).symm f) ((InnerProductSpace.toDual ℝ E).symm g)
  simpa only [← map_add, ← map_sub, LinearIsometryEquiv.norm_map, pow_two] using h

attribute [local instance] strongDualInnerProduct

/-- The Riesz image of an original orthonormal basis is an actual dual orthonormal basis. -/
def rieszOrthonormalBasis {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) :
    OrthonormalBasis ι ℝ (StrongDual ℝ E) :=
  e.map (InnerProductSpace.toDual ℝ E)

/-- The actual dual coordinate matrix is the transpose of the reverse basis change. -/
theorem continuousDualBasis_toMatrix {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) :
    (rieszOrthonormalBasis e).toBasis.toMatrix (continuousDualBasis b) =
      (b.toMatrix e.toBasis).transpose := by
  ext i j
  simp only [Basis.toMatrix_apply, Matrix.transpose_apply]
  change (e.repr ((InnerProductSpace.toDual ℝ E).symm (continuousDualBasis b j))) i = _
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, continuousDualBasis_apply]
  rw [OrthonormalBasis.coe_toBasis]

/-- Actual primal and constructed dual coordinate determinants multiply to one. -/
theorem continuousDualBasis_det_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) :
    e.toBasis.det b * (rieszOrthonormalBasis e).toBasis.det (continuousDualBasis b) = 1 := by
  rw [Basis.det_apply, Basis.det_apply, continuousDualBasis_toMatrix, Matrix.det_transpose]
  change e.toBasis.det b * b.det e.toBasis = 1
  rw [Basis.det_mul_det]
  exact Basis.det_self _

section Covolume

variable [MeasurableSpace E] [BorelSpace E]

local instance integralDualPrimalMeasureSpace : MeasureSpace E := measureSpaceOfInnerProductSpace

/-- The actual integer span covolume is the absolute coordinate determinant in any
orthonormal basis, for canonical ordinary Euclidean volume. -/
theorem covolume_span_eq_abs_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |e.toBasis.det b| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume e.toBasis]
  have he : volume.real (ZSpan.fundamentalDomain e.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped e.toBasis volume)]
    change (volume (parallelepiped e)).toReal = 1
    rw [e.volume_parallelepiped, ENNReal.toReal_one]
  rw [he, mul_one]

/-- The reciprocal determinant identity gives actual ordinary dual covolume for every
real basis lattice, including the empty basis in dimension zero. -/
theorem integralDual_span_covolume {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) :
    letI : MeasurableSpace (StrongDual ℝ E) := borel _
    letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
    ZLattice.covolume (integralDual (Submodule.span ℤ (Set.range b))) =
      (ZLattice.covolume (Submodule.span ℤ (Set.range b)))⁻¹ := by
  classical
  let : MeasurableSpace (StrongDual ℝ E) := borel _
  let : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
  rw [integralDual_span,
    covolume_span_eq_abs_det (rieszOrthonormalBasis e) (continuousDualBasis b),
    covolume_span_eq_abs_det e b]
  apply eq_inv_of_mul_eq_one_right
  rw [← abs_mul, continuousDualBasis_det_product, abs_one]

/-- The actual integer dual of every genuine full Euclidean lattice has reciprocal
canonical ordinary covolume. Its dual basis is constructed from an actual integer basis. -/
theorem integralDual_covolume (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    letI : MeasurableSpace (StrongDual ℝ E) := borel _
    letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
    letI := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
    ZLattice.covolume (integralDual L) = (ZLattice.covolume L)⁻¹ := by
  classical
  let : MeasurableSpace (StrongDual ℝ E) := borel _
  let : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  let := measureSpaceOfInnerProductSpace (E := StrongDual ℝ E)
  let := ZLattice.module_free ℝ L
  let := ZLattice.module_finite ℝ L
  let a := (Module.finBasis ℤ L).reindex (finCongr (ZLattice.rank ℝ L))
  let b := a.ofZLatticeBasis ℝ L
  have hs : Submodule.span ℤ (Set.range b) = L :=
    Basis.ofZLatticeBasis_span ℝ L a
  rw [← hs]
  exact integralDual_span_covolume (stdOrthonormalBasis ℝ E) b

end Covolume

end Euclidean

end ArakelovGeometry.GeometryOfNumbers
