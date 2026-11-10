/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.DualBaseChange
public import ArakelovGeometry.NumberTheory.NumberFieldArchimedeanTrace
public import ArakelovGeometry.NumberTheory.NumberFieldIntegralTraceDual

/-!
# The actual Archimedean vector trace pairing

The pairing evaluates the canonical completed duals on the original completed
vectors and applies the real/complex coefficient trace. Its real dual
equivalence is algebraic; no metric or covolume claim is made.
-/

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct
namespace ArakelovGeometry.NumberFieldArchimedeanTracePairing
open NumberFieldArchimedeanVectorDiagonal NumberFieldArchimedeanTrace

variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Trace composition on the actual completed local dual. -/
def localTraceDualMap (w : InfinitePlace K) :
    CompletedCoefficient w ⊗[K] Module.Dual K E →ₗ[ℝ]
      Module.Dual ℝ (CompletedCoefficient w ⊗[K] E) where
  toFun f := (coefficientTrace w).comp
    ((dualBaseChangeEquiv K (CompletedCoefficient w) E f).restrictScalars ℝ)
  map_add' f g := by ext x; simp
  map_smul' r f := by
    ext x
    change coefficientTrace w
      (dualBaseChangeEquiv K (CompletedCoefficient w) E (r • f) x) =
        r • coefficientTrace w (dualBaseChangeEquiv K (CompletedCoefficient w) E f x)
    rw [← IsScalarTower.algebraMap_smul (CompletedCoefficient w) r f, map_smul,
      LinearMap.smul_apply, IsScalarTower.algebraMap_smul (CompletedCoefficient w)]
    exact (coefficientTrace w).map_smul r _

@[simp]
theorem localTraceDualMap_apply (w : InfinitePlace K)
    (f : CompletedCoefficient w ⊗[K] Module.Dual K E)
    (x : CompletedCoefficient w ⊗[K] E) :
    localTraceDualMap (K := K) (E := E) w f x =
      coefficientTrace w (dualBaseChangeEquiv K (CompletedCoefficient w) E f x) := rfl

/-- The real bilinear trace pairing on the literal completed vector products. -/
def tracePairing :
    CompletedVectorProduct K (Module.Dual K E) →ₗ[ℝ]
      Module.Dual ℝ (CompletedVectorProduct K E) where
  toFun f :=
    { toFun := fun x => ∑ w, localTraceDualMap (K := K) (E := E) w (f w) (x w)
      map_add' x y := by simp [Finset.sum_add_distrib]
      map_smul' r x := by simp [Finset.mul_sum] }
  map_add' f g := by ext x; simp [Finset.sum_add_distrib]
  map_smul' r f := by ext x; simp [Finset.mul_sum]

@[simp]
theorem tracePairing_apply (f : CompletedVectorProduct K (Module.Dual K E))
    (x : CompletedVectorProduct K E) :
    tracePairing (K := K) (E := E) f x = ∑ w,
      coefficientTrace w (dualBaseChangeEquiv K (CompletedCoefficient w) E (f w) (x w)) :=
  rfl

open scoped Classical in
theorem tracePairing_single (f : CompletedVectorProduct K (Module.Dual K E))
    (w : InfinitePlace K) (x : CompletedCoefficient w ⊗[K] E) :
    tracePairing (K := K) (E := E) f (Pi.single w x) =
      coefficientTrace w (dualBaseChangeEquiv K (CompletedCoefficient w) E (f w) x) := by
  classical
  rw [tracePairing_apply]
  rw [Finset.sum_eq_single w]
  · rw [Pi.single_eq_same]
  · intro v _ hv
    simp [Pi.single_eq_of_ne hv]
  · simp

theorem tracePairing_original (f : Module.Dual K E) (x : E) :
    tracePairing (K := K) (E := E) (vectorDiagonalMap (K := K) f) (vectorDiagonalMap (K := K) x) =
      (Algebra.trace ℚ K (f x) : ℝ) := by
  rw [tracePairing_apply]
  simp only [vectorDiagonalMap_apply, dualBaseChangeEquiv_tmul_apply_tmul, one_mul]
  simpa only [totalTrace_apply, Pi.algebraMap_apply] using totalTrace_original (f x)

theorem tracePairing_injective :
    Function.Injective (tracePairing (K := K) (E := E)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  classical
  ext w
  apply (dualBaseChangeEquiv K (CompletedCoefficient w) E).injective
  apply LinearMap.ext
  intro x
  change dualBaseChangeEquiv K (CompletedCoefficient w) E (f w) x = 0
  by_contra ha
  have h := congrArg
    (fun ℓ : Module.Dual ℝ (CompletedVectorProduct K E) =>
      ℓ (Pi.single w
        ((dualBaseChangeEquiv K (CompletedCoefficient w) E (f w) x)⁻¹ • x))) hf
  rw [tracePairing_single, map_smul, smul_eq_mul, inv_mul_cancel₀ ha] at h
  have hm : coefficientTrace w (1 : CompletedCoefficient w) = (w.mult : ℝ) := by
    simpa using coefficientTrace_algebraMap w (1 : ℝ)
  rw [hm] at h
  exact (Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero) h

theorem tracePairing_surjective :
    Function.Surjective (tracePairing (K := K) (E := E)) := by
  let : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  let : IsScalarTower ℚ K E := IsScalarTower.of_compHom ℚ K E
  have hd :
      Module.finrank ℝ (CompletedVectorProduct K (Module.Dual K E)) =
        Module.finrank ℝ (Module.Dual ℝ (CompletedVectorProduct K E)) := by
    rw [Subspace.dual_finrank_eq, vectorDiagonal_dimension,
      vectorDiagonal_dimension, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
    tracePairing_injective

/-- Actual completed K-duals identify with the real dual of the original product. -/
def tracePairingEquiv :
    CompletedVectorProduct K (Module.Dual K E) ≃ₗ[ℝ]
      Module.Dual ℝ (CompletedVectorProduct K E) :=
  LinearEquiv.ofBijective tracePairing ⟨tracePairing_injective, tracePairing_surjective⟩

@[simp]
theorem tracePairingEquiv_apply (f : CompletedVectorProduct K (Module.Dual K E))
    (x : CompletedVectorProduct K E) :
    tracePairingEquiv (K := K) (E := E) f x = tracePairing (K := K) (E := E) f x := rfl


/-- Original K-linear functionals act through their literal completed diagonals. -/
def originalTraceDualMap :
    Module.Dual K E →ₗ[ℤ] Module.Dual ℝ (CompletedVectorProduct K E) :=
  (tracePairing (K := K) (E := E)).restrictScalars ℤ |>.comp
    ((vectorDiagonalMap (K := K) (E := Module.Dual K E)).restrictScalars ℤ)

@[simp]
theorem originalTraceDualMap_apply (f : Module.Dual K E) (x : E) :
    originalTraceDualMap (K := K) f (vectorDiagonalMap (K := K) x) =
      (Algebra.trace ℚ K (f x) : ℝ) :=
  tracePairing_original f x

omit [FiniteDimensional K E] in
/-- Actual real functionals taking integer values on the original diagonal lattice. -/
def integralRealDual (M : Submodule (𝓞 K) E) :
    Submodule ℤ (Module.Dual ℝ (CompletedVectorProduct K E)) where
  carrier := {ℓ | ∀ m : M, ℓ (vectorDiagonalMap (K := K) (m : E)) ∈
    LinearMap.range (Algebra.linearMap ℤ ℝ)}
  zero_mem' := by intro m; simp
  add_mem' hℓ hψ := by
    intro m
    simpa using (LinearMap.range (Algebra.linearMap ℤ ℝ)).add_mem (hℓ m) (hψ m)
  smul_mem' a ℓ hℓ := by
    intro m
    simpa using (LinearMap.range (Algebra.linearMap ℤ ℝ)).smul_mem a (hℓ m)

omit [FiniteDimensional K E] in
theorem mem_integralRealDual_iff (M : Submodule (𝓞 K) E)
    (ℓ : Module.Dual ℝ (CompletedVectorProduct K E)) :
    ℓ ∈ integralRealDual M ↔ ∀ z ∈ diagonalLattice M,
      ℓ z ∈ LinearMap.range (Algebra.linearMap ℤ ℝ) := by
  constructor
  · intro h z hz
    obtain ⟨m, rfl⟩ := (mem_diagonalLattice_iff M z).mp hz
    exact h m
  · intro h m
    exact h _ ((mem_diagonalLattice_iff M _).mpr ⟨m, rfl⟩)

/-- Integers identify with the range of their canonical embedding into the reals. -/
def integerRealRangeEquiv : ℤ ≃ₗ[ℤ] LinearMap.range (Algebra.linearMap ℤ ℝ) :=
  LinearEquiv.ofInjective (Algebra.linearMap ℤ ℝ) Int.cast_injective

/-- Recovering the integer representative preserves its value in the reals. -/
@[simp]
theorem integerRealRangeEquiv_symm_cast
    (r : LinearMap.range (Algebra.linearMap ℤ ℝ)) :
    (integerRealRangeEquiv.symm r : ℝ) = (r : ℝ) :=
  congrArg Subtype.val (integerRealRangeEquiv.apply_symm_apply r)

omit [FiniteDimensional K E] in
/-- The unique integer values of an actual integral real functional. -/
def integerRestriction (M : Submodule (𝓞 K) E) :
    integralRealDual M →ₗ[ℤ] Module.Dual ℤ M where
  toFun ℓ :=
    { toFun := fun m => integerRealRangeEquiv.symm
        ⟨ℓ.1 (vectorDiagonalMap (K := K) (m : E)), ℓ.2 m⟩
      map_add' m n := by
        apply (Int.cast_injective (α := ℝ))
        simp
      map_smul' a m := by
        apply (Int.cast_injective (α := ℝ))
        simp only [integerRealRangeEquiv_symm_cast, RingHom.id_apply,
          zsmul_eq_mul, Int.cast_mul]
        change ℓ.1 (vectorDiagonalMap (K := K) (a • (m : E))) =
          (a : ℝ) * ℓ.1 (vectorDiagonalMap (K := K) (m : E))
        rw [(vectorDiagonalMap (K := K) (E := E)).map_smul_of_tower]
        simp }
  map_add' ℓ ψ := by
    ext m
    apply (Int.cast_injective (α := ℝ))
    simp
  map_smul' a ℓ := by
    ext m
    apply (Int.cast_injective (α := ℝ))
    simp

omit [FiniteDimensional K E] in
@[simp]
theorem integerRestriction_apply (M : Submodule (𝓞 K) E)
    (ℓ : integralRealDual M) (m : M) :
    (integerRestriction M ℓ m : ℝ) = ℓ.1 (vectorDiagonalMap (K := K) (m : E)) :=
  integerRealRangeEquiv_symm_cast _

open NumberFieldIntegralTraceDual

theorem originalTraceDualMap_mem_integralRealDual_iff
    (M : Submodule (𝓞 K) E) (f : Module.Dual K E) :
    originalTraceDualMap (K := K) f ∈ integralRealDual M ↔ f ∈ integralTraceDual M := by
  constructor
  · intro hf m
    obtain ⟨a, ha⟩ := hf m
    rw [originalTraceDualMap_apply] at ha
    refine ⟨a, ?_⟩
    change (a : ℝ) = (Algebra.trace ℚ K (f (m : E)) : ℝ) at ha
    change (a : ℚ) = Algebra.trace ℚ K (f (m : E))
    exact_mod_cast ha
  · intro hf m
    rw [originalTraceDualMap_apply]
    obtain ⟨a, ha⟩ := hf m
    refine ⟨a, ?_⟩
    change (a : ℚ) = Algebra.trace ℚ K (f (m : E)) at ha
    change (a : ℝ) = (Algebra.trace ℚ K (f (m : E)) : ℝ)
    exact_mod_cast ha

/-- The literal diagonal trace map restricted to the original integral trace dual. -/
def integralDiagonalMap (M : Submodule (𝓞 K) E) :
    integralTraceDual M →ₗ[ℤ] integralRealDual M :=
  (((originalTraceDualMap (K := K) (E := E)).comp
    ((integralTraceDual M).subtype.restrictScalars ℤ))).codRestrict
      (integralRealDual M) (by
        intro f m
        rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
          Submodule.subtype_apply, originalTraceDualMap_apply]
        obtain ⟨a, ha⟩ := f.2 m
        refine ⟨a, ?_⟩
        change (a : ℝ) = (Algebra.trace ℚ K (f.1 (m : E)) : ℝ)
        exact_mod_cast ha)

@[simp]
theorem integralDiagonalMap_apply (M : Submodule (𝓞 K) E)
    (f : integralTraceDual M) (x : CompletedVectorProduct K E) :
    (integralDiagonalMap M f).1 x = originalTraceDualMap (K := K) f.1 x := rfl

@[simp]
theorem integerRestriction_integralDiagonalMap (M : Submodule (𝓞 K) E)
    (f : integralTraceDual M) :
    integerRestriction M (integralDiagonalMap M f) = traceRestriction M f := by
  ext m
  apply (Int.cast_injective (α := ℝ))
  rw [integerRestriction_apply, integralDiagonalMap_apply, originalTraceDualMap_apply]
  exact_mod_cast (traceRestriction_apply M f m).symm

theorem integralDiagonalMap_injective (M : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Injective (integralDiagonalMap M) := by
  intro f g h
  apply traceRestriction_injective M hspan
  simpa only [integerRestriction_integralDiagonalMap] using
    congrArg (integerRestriction M) h

theorem integralDiagonalMap_surjective (M : Submodule (𝓞 K) E)
    (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    Function.Surjective (integralDiagonalMap M) := by
  intro ℓ
  let φ := integerRestriction M ℓ
  let f := (integralTraceEquiv M hspan).symm φ
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply (diagonalLatticeBasis M hfg hspan).ext
  intro i
  rw [diagonalLatticeBasis_apply, integralDiagonalMap_apply, originalTraceDualMap_apply]
  have hf : (traceRestriction M f (NumberFieldFullLattice.integerBasis M hfg i) : ℝ) =
      ℓ.1 (vectorDiagonalMap (K := K) (NumberFieldFullLattice.integerBasis M hfg i : E)) := by
    change ((integralTraceEquiv M hspan f) _ : ℝ) = _
    rw [show integralTraceEquiv M hspan f = φ from
      (integralTraceEquiv M hspan).apply_symm_apply φ]
    exact integerRestriction_apply M ℓ _
  have ht : (traceRestriction M f (NumberFieldFullLattice.integerBasis M hfg i) : ℝ) =
      (Algebra.trace ℚ K (f.1 (NumberFieldFullLattice.integerBasis M hfg i : E)) : ℝ) := by
    exact_mod_cast traceRestriction_apply M f _
  exact ht.symm.trans hf

/-- The original trace-integral dual equals the actual integral real dual lattice. -/
def integralDiagonalEquiv (M : Submodule (𝓞 K) E)
    (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    integralTraceDual M ≃ₗ[ℤ] integralRealDual M :=
  LinearEquiv.ofBijective (integralDiagonalMap M)
    ⟨integralDiagonalMap_injective M hspan, integralDiagonalMap_surjective M hfg hspan⟩

theorem integral_trace_dual_image (M : Submodule (𝓞 K) E)
    (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    ((integralTraceDual M).restrictScalars ℤ).map
      (originalTraceDualMap (K := K) (E := E)) = integralRealDual M := by
  ext ℓ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (integralDiagonalMap M ⟨f, hf⟩).2
  · intro hℓ
    obtain ⟨f, hf⟩ := integralDiagonalMap_surjective M hfg hspan ⟨ℓ, hℓ⟩
    exact ⟨f.1, f.2, congrArg Subtype.val hf⟩




/-- Under the actual completed pairing, the literal trace-dual diagonal is integral dual. -/
theorem tracePairing_diagonal_integralTraceDual_image (M : Submodule (𝓞 K) E)
    (hfg : M.FG) (hspan : Submodule.span K (M : Set E) = ⊤) :
    (diagonalLattice (integralTraceDual M)).map
      ((tracePairing (K := K) (E := E)).restrictScalars ℤ) = integralRealDual M := by
  ext ℓ
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨f, rfl⟩ := (mem_diagonalLattice_iff (integralTraceDual M) z).mp hz
    exact (integralDiagonalMap M f).2
  · intro hℓ
    obtain ⟨f, hf⟩ := integralDiagonalMap_surjective M hfg hspan ⟨ℓ, hℓ⟩
    exact ⟨vectorDiagonalMap (K := K) f.1,
      (mem_diagonalLattice_iff (integralTraceDual M) _).mpr ⟨f, rfl⟩,
      congrArg Subtype.val hf⟩

theorem tracePairing_nondegenerate_right (x : CompletedVectorProduct K E)
    (h : ∀ f : CompletedVectorProduct K (Module.Dual K E), tracePairing (K := K) f x = 0) :
    x = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ x).mp
  intro ℓ
  obtain ⟨f, rfl⟩ := tracePairing_surjective (K := K) (E := E) ℓ
  exact h f

end ArakelovGeometry.NumberFieldArchimedeanTracePairing

namespace ArakelovGeometry.NormFamily
open AdelicStructure NumberFieldArchimedeanTracePairing
  NumberFieldArchimedeanVectorDiagonal NumberFieldIntegralTraceDual
variable {K E : Type*} [Field K] [NumberField K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E}

/-- The actual dominated pure global ball has precisely its real integral dual. -/
def IsDominated.pure_normalizedGlobalUnitBall_integralRealDualEquiv
    (hdom : ξ.IsDominated) (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    integralTraceDual (ξ.globalUnitBallModule hξ) ≃ₗ[ℤ]
      integralRealDual (ξ.globalUnitBallModule hξ) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  integralDiagonalEquiv (ξ.globalUnitBallModule hξ) hm.1 hm.2.2

theorem IsDominated.pure_normalizedGlobalUnitBall_integral_trace_dual_image
    (hdom : ξ.IsDominated) (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    ((integralTraceDual (ξ.globalUnitBallModule hξ)).restrictScalars ℤ).map
      (originalTraceDualMap (K := K) (E := E)) =
        integralRealDual (ξ.globalUnitBallModule hξ) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  integral_trace_dual_image (ξ.globalUnitBallModule hξ) hm.1 hm.2.2


theorem IsDominated.pure_normalizedGlobalUnitBall_tracePairing_diagonal_image
    (hdom : ξ.IsDominated) (hξ : ξ.IsUltrametric) (hpure : ξ.IsPureAtFinitePlaces) :
    (diagonalLattice (integralTraceDual (ξ.globalUnitBallModule hξ))).map
      ((tracePairing (K := K) (E := E)).restrictScalars ℤ) =
        integralRealDual (ξ.globalUnitBallModule hξ) :=
  let hm := hdom.pure_normalizedGlobalUnitBall_finite_projective_span hξ hpure
  tracePairing_diagonal_integralTraceDual_image (ξ.globalUnitBallModule hξ) hm.1 hm.2.2

end ArakelovGeometry.NormFamily
