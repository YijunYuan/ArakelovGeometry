/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Completed
public import Mathlib.AlgebraicGeometry.StructureSheaf
import ArakelovGeometry.NumberTheory.NumberField.Local.Lattice.PrincipalFrame
import ArakelovGeometry.NumberTheory.NumberField.Local.Prime.PrincipalSupport

/-!
# Actual regular functions on a nonempty number-field open

Nonempty opens of the actual ring-of-integers spectrum are principal, and
their actual structure-sheaf section rings are principal localizations.
-/

@[expose] public section

open CategoryTheory Opposite NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ArakelovGeometry.NumberFieldOpenRegularFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The actual point of Spec O_K corresponding to an actual nonzero prime. -/
abbrev primePoint (p : HeightOneSpectrum (𝓞 K)) : PrimeSpectrum (𝓞 K) :=
  ⟨p.asIdeal, p.isPrime⟩

/-- The actual generic point of Spec O_K. -/
def genericPoint : PrimeSpectrum (𝓞 K) := ⟨⊥, Ideal.isPrime_bot⟩

omit [NumberField K] in
/-- A genuine nonempty open contains a nonzero basic open. -/
theorem exists_nonzero_basicOpen_le (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    ∃ g : 𝓞 K, g ≠ 0 ∧ PrimeSpectrum.basicOpen g ≤ U := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨V, ⟨g, rfl⟩, hg, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨g, ?_, hle⟩
  intro hzero
  exact (PrimeSpectrum.mem_basicOpen g x).mp hg (hzero ▸ x.asIdeal.zero_mem)

omit [NumberField K] in
/-- The actual generic point belongs to every nonempty open. -/
theorem genericPoint_mem (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) : genericPoint (K := K) ∈ U := by
  obtain ⟨g, hg, hle⟩ := exists_nonzero_basicOpen_le U hU
  apply hle
  simpa [PrimeSpectrum.mem_basicOpen, genericPoint, Ideal.mem_bot] using hg

/-- The excluded actual nonzero primes of a nonempty open form a genuine finite set. -/
theorem finite_excludedPrimes (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    {p : HeightOneSpectrum (𝓞 K) | primePoint p ∉ U}.Finite := by
  obtain ⟨g, hg, hle⟩ := exists_nonzero_basicOpen_le U hU
  have hI : Ideal.span {g} ≠ (0 : Ideal (𝓞 K)) :=
    fun h => hg (Ideal.span_singleton_eq_bot.mp h)
  apply (Ideal.finite_factors hI).subset
  intro p hp
  change p.asIdeal ∣ Ideal.span {g}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnot
  apply hp
  apply hle
  exact (PrimeSpectrum.mem_basicOpen g (primePoint p)).mpr hnot

/-- The actual finite class group produces a principal representation of every
nonempty open, with exactly its actual excluded-prime support. -/
theorem exists_nonzero_eq_basicOpen
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ U = PrimeSpectrum.basicOpen f ∧
      ∀ p : HeightOneSpectrum (𝓞 K), f ∈ p.asIdeal ↔ primePoint p ∉ U := by
  classical
  let T := (finite_excludedPrimes U hU).toFinset
  obtain ⟨f, hf, _, hsupport⟩ :=
    PrincipalPrimeSupport.exists_numberField_intValuation_support K T
  have hmem (p : HeightOneSpectrum (𝓞 K)) : f ∈ p.asIdeal ↔ primePoint p ∉ U := by
    rw [← p.intValuation_lt_one_iff_mem, hsupport p]
    exact Set.Finite.mem_toFinset _
  refine ⟨f, hf, ?_, hmem⟩
  ext x
  by_cases hx : x.asIdeal = ⊥
  · have heq : x = genericPoint (K := K) := PrimeSpectrum.ext hx
    subst x
    change genericPoint (K := K) ∈ U ↔ genericPoint (K := K) ∈ PrimeSpectrum.basicOpen f
    exact ⟨fun _ => by
      simpa [PrimeSpectrum.mem_basicOpen, genericPoint, Ideal.mem_bot] using hf,
      fun _ => genericPoint_mem U hU⟩
  · let p : HeightOneSpectrum (𝓞 K) := ⟨x.asIdeal, x.isPrime, hx⟩
    have heq : primePoint p = x := PrimeSpectrum.ext rfl
    rw [← heq]
    change primePoint p ∈ U ↔ primePoint p ∈ PrimeSpectrum.basicOpen f
    rw [PrimeSpectrum.mem_basicOpen]
    simpa only [not_not, primePoint] using (not_congr (hmem p)).symm

/-- The literal ring of regular functions, as actual structure-sheaf sections. -/
abbrev regularFunctions (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) :=
  ((AlgebraicGeometry.Spec.structureSheaf (𝓞 K)).obj.obj (op U))

/-- The original canonical constant-section algebra, with no new scalar data. -/
instance regularFunctionsAlgebra (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) :
    Algebra (𝓞 K) (regularFunctions U) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra (𝓞 K) (op U)

omit [NumberField K] in
/-- Genuine actual basic-open regular functions carry their canonical localization. -/
theorem isLocalization_regularFunctions_of_eq_basicOpen
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) (f : 𝓞 K)
    (hU : U = PrimeSpectrum.basicOpen f) :
    IsLocalization.Away f (regularFunctions U) := by
  subst U
  exact AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen (𝓞 K) f

/-- A genuine nonempty open has a produced principal localization of its actual
regular functions, through the original integral section map. -/
theorem exists_regularFunctions_localization
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    ∃ f : 𝓞 K, f ≠ 0 ∧ U = PrimeSpectrum.basicOpen f ∧
      IsLocalization.Away f (regularFunctions U) := by
  obtain ⟨f, hf, heq, _⟩ := exists_nonzero_eq_basicOpen U hU
  exact ⟨f, hf, heq, isLocalization_regularFunctions_of_eq_basicOpen U f heq⟩

/-- A selected genuine principal generator for the actual open; no equality is assumed. -/
def openGenerator (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) : 𝓞 K :=
  (exists_nonzero_eq_basicOpen U hU).choose

theorem openGenerator_ne_zero (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) : openGenerator U hU ≠ 0 :=
  (exists_nonzero_eq_basicOpen U hU).choose_spec.1

theorem eq_basicOpen_openGenerator (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    U = PrimeSpectrum.basicOpen (openGenerator U hU) :=
  (exists_nonzero_eq_basicOpen U hU).choose_spec.2.1

theorem openGenerator_mem_iff (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (p : HeightOneSpectrum (𝓞 K)) :
    openGenerator U hU ∈ p.asIdeal ↔ primePoint p ∉ U :=
  (exists_nonzero_eq_basicOpen U hU).choose_spec.2.2 p

/-- The produced open generator localizes the actual section ring. -/
theorem regularFunctionsLocalization (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    IsLocalization.Away (openGenerator U hU) (regularFunctions U) :=
  isLocalization_regularFunctions_of_eq_basicOpen U _ (eq_basicOpen_openGenerator U hU)

/-- The genuine section-ring equivalence with principal localization respects
the original integral coefficient map. -/
def regularFunctionsPrincipalEquiv (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    regularFunctions U ≃ₐ[𝓞 K] Localization (Submonoid.powers (openGenerator U hU)) := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.algEquiv (Submonoid.powers (openGenerator U hU)) _ _

/-- Integral constants embed in the actual regular-function ring of any nonempty open. -/
theorem regularFunctions_algebraMap_injective
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    Function.Injective (algebraMap (𝓞 K) (regularFunctions U)) := by
  let := regularFunctionsLocalization U hU
  apply IsLocalization.injective (M := Submonoid.powers (openGenerator U hU))
  exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (openGenerator_ne_zero U hU))

omit [NumberField K] in
/-- The actual structure-sheaf stalk is canonically the actual prime localization. -/
def stalkLocalizationEquiv (x : PrimeSpectrum (𝓞 K)) :
    Localization.AtPrime x.asIdeal ≃+*
      ((AlgebraicGeometry.Spec.structureSheaf (𝓞 K)).presheaf.stalk x) := by
  let := AlgebraicGeometry.StructureSheaf.stalkAlgebra (𝓞 K) x
  let := AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk (𝓞 K) x
  exact (IsLocalization.algEquiv x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal)
    ((AlgebraicGeometry.Spec.structureSheaf (𝓞 K)).presheaf.stalk x)).toRingEquiv

omit [NumberField K] in
@[simp]
theorem stalkLocalizationEquiv_symm_toStalk (x : PrimeSpectrum (𝓞 K)) (a : 𝓞 K) :
    (stalkLocalizationEquiv x).symm (AlgebraicGeometry.StructureSheaf.toStalk (𝓞 K) x a) =
      algebraMap (𝓞 K) (Localization.AtPrime x.asIdeal) a := by
  let := AlgebraicGeometry.StructureSheaf.stalkAlgebra (𝓞 K) x
  let := AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk (𝓞 K) x
  exact (IsLocalization.algEquiv x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal)
    ((AlgebraicGeometry.Spec.structureSheaf (𝓞 K)).presheaf.stalk x)).symm.commutes a

omit [NumberField K] in
/-- The actual structure-sheaf germ, interpreted in the actual prime localization. -/
def regularFunctionsToLocalization
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) (x : PrimeSpectrum (𝓞 K))
    (hx : x ∈ U) : regularFunctions U →+* Localization.AtPrime x.asIdeal :=
  (stalkLocalizationEquiv x).symm.toRingHom.comp
    ((AlgebraicGeometry.Spec.structureSheaf (𝓞 K)).presheaf.germ U x hx).hom

omit [NumberField K] in
@[simp]
theorem regularFunctionsToLocalization_algebraMap
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K))) (x : PrimeSpectrum (𝓞 K))
    (hx : x ∈ U) (a : 𝓞 K) :
    regularFunctionsToLocalization U x hx (algebraMap (𝓞 K) (regularFunctions U) a) =
      algebraMap (𝓞 K) (Localization.AtPrime x.asIdeal) a := by
  change (stalkLocalizationEquiv x).symm
    (((AlgebraicGeometry.structurePresheafInCommRingCat (𝓞 K)).germ U x hx).hom
      (algebraMap (𝓞 K) (regularFunctions U) a)) = _
  exact (congrArg (stalkLocalizationEquiv x).symm
    (AlgebraicGeometry.StructureSheaf.algebraMap_germ_apply U x hx a)).trans
      (stalkLocalizationEquiv_symm_toStalk x a)

/-- The canonical extension of the integral map from actual regular functions to K. -/
def regularFunctionsToField (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) : regularFunctions U →+* K := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.Away.lift (openGenerator U hU)
    (isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff).not.mpr
      (openGenerator_ne_zero U hU)))

@[simp]
theorem regularFunctionsToField_algebraMap
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (a : 𝓞 K) :
    regularFunctionsToField U hU (algebraMap (𝓞 K) (regularFunctions U) a) =
      algebraMap (𝓞 K) K a := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.Away.lift_eq (openGenerator U hU)
    (isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff).not.mpr
      (openGenerator_ne_zero U hU))) a

theorem regularFunctionsToField_injective
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    Function.Injective (regularFunctionsToField U hU) := by
  let := regularFunctionsLocalization U hU
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (openGenerator U hU)) (regularFunctions U)
  intro a ha
  rw [regularFunctionsToField_algebraMap, IsFractionRing.to_map_eq_zero_iff] at ha
  simp [ha]

omit [NumberField K] in
/-- The canonical map from the actual generic localization to the original field. -/
def genericLocalizationToField : Localization.AtPrime (genericPoint (K := K)).asIdeal →+* K :=
  IsLocalization.lift (M := (genericPoint (K := K)).asIdeal.primeCompl)
    (g := algebraMap (𝓞 K) K) fun s => isUnit_iff_ne_zero.mpr <|
    (IsFractionRing.to_map_eq_zero_iff).not.mpr <| by
      have hs : (s : 𝓞 K) ∉ (⊥ : Ideal (𝓞 K)) := s.property
      simpa only [Ideal.mem_bot] using hs

/-- The generic coefficient map is the actual generic germ followed by its
localization-to-field map. -/
theorem regularFunctionsToField_eq_genericGerm
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) :
    regularFunctionsToField U hU = genericLocalizationToField.comp
      (regularFunctionsToLocalization U (genericPoint (K := K)) (genericPoint_mem U hU)) := by
  let := regularFunctionsLocalization U hU
  apply IsLocalization.ringHom_ext (Submonoid.powers (openGenerator U hU))
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, regularFunctionsToField_algebraMap,
    RingHom.comp_apply, regularFunctionsToLocalization_algebraMap]
  exact (IsLocalization.lift_eq _ a).symm

local notation "openNormalizedStructure" => AdelicStructure.normalizedNumberFieldAdelicStructure K
local notation "openPrimeParameter" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  ActualPrimeIndexing.normalizedPrimeParameter p
local notation "openPrimeMem" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  ActualPrimeIndexing.normalizedPrimeParameter_mem_fin p
local notation "openCompletedRing" => fun (p : HeightOneSpectrum (𝓞 K)) ↦
  AdelicStructure.completedLocalRing (openNormalizedStructure)
    (openPrimeParameter p) (openPrimeMem p)

/-- The canonical actual completed coefficient map on genuine regular functions. -/
def regularFunctionsToCompleted (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (p : HeightOneSpectrum (𝓞 K))
    (hp : primePoint p ∈ U) : regularFunctions U →+* openCompletedRing p := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.Away.lift (openGenerator U hU)
    (g := (openNormalizedStructure).integralCompletedLocalCoefficientMap
      (openPrimeParameter p) (openPrimeMem p)) (by
      exact NumberFieldModel.isUnit_completed_integral_of_not_mem _ p
        (fun hf => ((openGenerator_mem_iff U hU p).mp hf) hp))

@[simp]
theorem regularFunctionsToCompleted_algebraMap
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (p : HeightOneSpectrum (𝓞 K))
    (hp : primePoint p ∈ U) (a : 𝓞 K) :
    regularFunctionsToCompleted U hU p hp (algebraMap (𝓞 K) (regularFunctions U) a) =
      (openNormalizedStructure).integralCompletedLocalCoefficientMap
        (openPrimeParameter p) (openPrimeMem p) a := by
  let := regularFunctionsLocalization U hU
  exact IsLocalization.Away.lift_eq (openGenerator U hU)
    (NumberFieldModel.isUnit_completed_integral_of_not_mem _ p
      (fun hf => ((openGenerator_mem_iff U hU p).mp hf) hp)) a

/-- The actual prime localization maps to its actual completed coefficient ring. -/
def primeLocalizationToCompleted (p : HeightOneSpectrum (𝓞 K)) :
    Localization.AtPrime p.asIdeal →+* openCompletedRing p :=
  IsLocalization.lift (M := p.asIdeal.primeCompl)
    (g := (openNormalizedStructure).integralCompletedLocalCoefficientMap
      (openPrimeParameter p) (openPrimeMem p))
    fun s => by exact NumberFieldModel.isUnit_completed_integral_of_not_mem _ p s.property

/-- The completed coefficient map is the actual prime germ followed by the
actual prime-localization completion map. -/
theorem regularFunctionsToCompleted_eq_primeGerm
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (p : HeightOneSpectrum (𝓞 K))
    (hp : primePoint p ∈ U) :
    regularFunctionsToCompleted U hU p hp = (primeLocalizationToCompleted p).comp
      (regularFunctionsToLocalization U (primePoint p) hp) := by
  let := regularFunctionsLocalization U hU
  apply IsLocalization.ringHom_ext (Submonoid.powers (openGenerator U hU))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply]
  rw [regularFunctionsToCompleted_algebraMap, regularFunctionsToLocalization_algebraMap]
  exact (IsLocalization.lift_eq
    (fun s : p.asIdeal.primeCompl =>
      NumberFieldModel.isUnit_completed_integral_of_not_mem _ p s.property) a).symm

/-- The actual completed coefficient map agrees with the original generic
coefficient map after inclusion into the completed field. -/
theorem regularFunctionsToCompleted_coe
    (U : TopologicalSpace.Opens (PrimeSpectrum (𝓞 K)))
    (hU : (U : Set (PrimeSpectrum (𝓞 K))).Nonempty) (p : HeightOneSpectrum (𝓞 K))
    (hp : primePoint p ∈ U) (s : regularFunctions U) :
    (regularFunctionsToCompleted U hU p hp s :
      ((openNormalizedStructure).ϕ (openPrimeParameter p)).Completion) =
      algebraMap K _ (regularFunctionsToField U hU s) := by
  let := regularFunctionsLocalization U hU
  have heq : (openCompletedRing p).subtype.comp (regularFunctionsToCompleted U hU p hp) =
      (algebraMap K _).comp (regularFunctionsToField U hU) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (openGenerator U hU))
    ext a
    simp only [RingHom.comp_apply, regularFunctionsToCompleted_algebraMap,
      regularFunctionsToField_algebraMap]
    rfl
  exact RingHom.congr_fun heq s

end ArakelovGeometry.NumberFieldOpenRegularFunctions
