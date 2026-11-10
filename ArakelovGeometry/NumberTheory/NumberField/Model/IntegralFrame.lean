/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.UnitBall.Global
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Localization.Free

/-!
# Actual generic and principal frames of integral number-field lattices

A full rational span produces actual integral denominators and the canonical
generic-fibre equivalence. Finite generation then produces a principal-open
integral frame and its finite actual prime-divisor set. These algebraic
producers do not identify an arbitrary open-set coherent sheaf with a lattice.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ArakelovGeometry.NumberFieldModel

variable {K : Type*} [Field K] [NumberField K]
  {E : Type*} [AddCommGroup E] [Module K E]

/-- Full literal rational span gives a genuine nonzero integral denominator
for every original vector, without a denominator certificate. -/
theorem exists_integral_smul_mem_of_span (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (x : E) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set E) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h := L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
    simpa only [smul_add, ← mul_smul, mul_comm b a] using h
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨u, v, hv, hcv⟩ := IsFractionRing.div_surjective (𝓞 K) c
    have hv0 : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
    have hvK : algebraMap (𝓞 K) K v ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hv0
    refine ⟨v * a, mul_ne_zero hv0 ha, ?_⟩
    have he : (v * a) • (c • x) = u • (a • x) := by
      simp only [integralVector_smul, smul_smul, map_mul]
      congr 1
      rw [← hcv]
      field_simp
    rw [he]
    exact L.smul_mem u hax

/-- The actual lattice inclusion is genuinely localization at nonzero integers. -/
theorem isLocalizedModule_subtype_of_span (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
  let : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (LinearMap.id : E →ₗ[𝓞 K] E) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) E K
  refine ⟨IsLocalizedModule.map_units (LinearMap.id : E →ₗ[𝓞 K] E), ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, hax⟩ := exists_integral_smul_mem_of_span L hspan x
    exact ⟨(⟨a • x, hax⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
  · intro x y h
    exact ⟨1, congrArg (fun z => (1 : nonZeroDivisors (𝓞 K)) • z) (Subtype.ext h)⟩

/-- The actual canonical generic-fibre identification of the integral lattice. -/
def genericFibreEquiv (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) : K ⊗[𝓞 K] L ≃ₗ[K] E := by
  letI := isLocalizedModule_subtype_of_span L hspan
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K L.subtype).equiv

@[simp]
theorem genericFibreEquiv_tmul (L : Submodule (𝓞 K) E)
    (hspan : Submodule.span K (L : Set E) = ⊤) (a : K) (x : L) :
    genericFibreEquiv L hspan (a ⊗ₜ[𝓞 K] x) = a • (x : E) := by
  let := isLocalizedModule_subtype_of_span L hspan
  exact IsBaseChange.equiv_tmul
    (IsLocalizedModule.isBaseChange (nonZeroDivisors (𝓞 K)) K L.subtype) a x

omit [NumberField K] in
/-- The literal lattice inclusion is injective. -/
theorem latticeSubtype_injective (L : Submodule (𝓞 K) E) :
    Function.Injective L.subtype := Subtype.val_injective

/-- The canonical principal-localization map to the original generic vector space. -/
def principalGenericMap (L : Submodule (𝓞 K) E) (f : 𝓞 K) (hf : f ≠ 0) :
    LocalizedModule.Away f L →ₗ[𝓞 K] E := by
  let : IsLocalizedModule (nonZeroDivisors (𝓞 K)) (LinearMap.id : E →ₗ[𝓞 K] E) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) E K
  exact LocalizedModule.lift (Submonoid.powers f) L.subtype fun s =>
    IsLocalizedModule.map_units (LinearMap.id : E →ₗ[𝓞 K] E)
      ⟨s.1, (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hf)) s.2⟩

/-- Actual finite generation and full span lift any prescribed rational basis
to an actual principal-localization basis at a produced nonzero integer. -/
theorem exists_principal_integral_frame (L : Submodule (𝓞 K) E) (hFG : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) {ι : Type*} [Finite ι]
    (b : Module.Basis ι K E) :
    ∃ (f : 𝓞 K) (hf : f ≠ 0)
      (bl : Module.Basis ι (Localization (Submonoid.powers f)) (LocalizedModule.Away f L)),
      ∀ i, principalGenericMap L f hf (bl i) = b i := by
  let := isLocalizedModule_subtype_of_span L hspan
  let := Module.Finite.of_fg hFG
  let := Module.finitePresentation_of_finite (𝓞 K) L
  obtain ⟨f, hf, bl, hbl⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    (nonZeroDivisors (𝓞 K)) L.subtype K b
  exact ⟨f, mem_nonZeroDivisors_iff_ne_zero.mp hf, bl, hbl⟩

/-- The produced principal denominator has finitely many actual bad primes. -/
theorem finite_prime_divisors {f : 𝓞 K} (hf : f ≠ 0) :
    {p : HeightOneSpectrum (𝓞 K) | f ∈ p.asIdeal}.Finite := by
  have hi : (Ideal.span {f} : Ideal (𝓞 K)) ≠ 0 := by simpa using hf
  exact (Ideal.finite_factors hi).subset fun p hp => Ideal.dvd_span_singleton.mpr hp

end ArakelovGeometry.NumberFieldModel
