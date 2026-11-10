/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.NumberTheory.NormFamilyCompletedLocalUnitBall

/-!
# Intrinsic scalar gauges of actual completed lattices

The scalar-infimum gauge uses nonzero field scalars, as in the source's
lattice norm. Its coordinate formula includes the zero vector by genuine
nontriviality of the scalar norm. No density of the value group is assumed.
-/

open scoped TensorProduct NumberField

noncomputable section

namespace ArakelovGeometry

universe u v w t

section ScalarGauge

variable {F : Type u} [NormedField F] {X : Type v} [AddCommGroup X] [Module F X]

/-- Norms of the nonzero scalars whose inverse carries a vector into a lattice. -/
def scalarLatticeGaugeValues (L : Set X) (x : X) : Set ℝ :=
  {r | ∃ a : F, a ≠ 0 ∧ a⁻¹ • x ∈ L ∧ ‖a‖ = r}

/-- The literal intrinsic lattice gauge, with scalar zero excluded. -/
def scalarLatticeGauge (L : Set X) (x : X) : ℝ :=
  sInf (scalarLatticeGaugeValues (F := F) L x)

theorem scalarLatticeGaugeValues_bddBelow (L : Set X) (x : X) :
    BddBelow (scalarLatticeGaugeValues (F := F) L x) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, _, _, rfl⟩
  exact norm_nonneg a

theorem scalarLatticeGauge_nonneg (L : Set X) (x : X) :
    0 ≤ scalarLatticeGauge (F := F) L x := by
  apply Real.sInf_nonneg
  rintro r ⟨a, _, _, rfl⟩
  exact norm_nonneg a

theorem scalarLatticeGauge_le (L : Set X) (x : X) {a : F} (ha : a ≠ 0)
    (hx : a⁻¹ • x ∈ L) : scalarLatticeGauge (F := F) L x ≤ ‖a‖ :=
  csInf_le (scalarLatticeGaugeValues_bddBelow L x) ⟨a, ha, hx, rfl⟩

end ScalarGauge

section NontrivialScalarGauge

variable {F : Type u} [NontriviallyNormedField F]
  {X : Type v} [AddCommGroup X] [Module F X]

/-- Small nonzero scalars, rather than an admissible zero scalar, give gauge zero. -/
theorem scalarLatticeGauge_zero (L : Set X)
    (hL : (0 : X) ∈ L) : scalarLatticeGauge (F := F) L 0 = 0 := by
  apply le_antisymm _ (scalarLatticeGauge_nonneg L 0)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, hεa⟩ := NormedField.exists_norm_lt F hε
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha
  have hm : a⁻¹ • (0 : X) ∈ L := by simpa only [smul_zero] using hL
  simpa only [zero_add] using (scalarLatticeGauge_le L 0 ha0 hm).trans hεa.le

end NontrivialScalarGauge

section Coordinates

variable {F : Type u} [NormedField F] {X : Type v} [AddCommGroup X] [Module F X]
  {ι : Type t} [Fintype ι]

/-- The actual coefficient submodule of a field basis over an integral subring. -/
def basisCoordinateLattice (O : Subring F) (b : Module.Basis ι F X) : Submodule O X where
  carrier := {x | ∀ i, b.equivFun x i ∈ O}
  zero_mem' := by
    intro i
    change b.equivFun 0 i ∈ O
    rw [map_zero, Pi.zero_apply]
    exact O.zero_mem
  add_mem' hx hy i := by
    simpa only [map_add, Pi.add_apply] using O.add_mem (hx i) (hy i)
  smul_mem' r {x} hx i := by
    simpa only [Subring.smul_def, map_smul, Pi.smul_apply, smul_eq_mul] using
      O.mul_mem r.property (hx i)

@[simp]
theorem mem_basisCoordinateLattice (O : Subring F) (b : Module.Basis ι F X) (x : X) :
    x ∈ basisCoordinateLattice O b ↔ ∀ i, b.equivFun x i ∈ O := Iff.rfl

theorem basisCoordinateLattice_eq_span (O : Subring F) (b : Module.Basis ι F X) :
    basisCoordinateLattice O b = Submodule.span O (Set.range b) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    have hi : b.repr x i ∈ O := hx i
    exact (Submodule.span O (Set.range b)).smul_mem ⟨b.repr x i, hi⟩
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩ j
    simp only [Module.Basis.equivFun_self]
    split_ifs <;> first | exact O.one_mem | exact O.zero_mem

theorem mem_basisCoordinateLattice_iff_norm_le_one (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (b : Module.Basis ι F X) (x : X) :
    x ∈ basisCoordinateLattice O b ↔ ‖b.equivFun x‖ ≤ 1 := by
  rw [mem_basisCoordinateLattice, pi_norm_le_iff_of_nonneg zero_le_one]
  exact forall_congr' fun i => hO (b.equivFun x i)

theorem inv_smul_mem_basisCoordinateLattice_iff (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (b : Module.Basis ι F X)
    (x : X) {a : F} (ha : a ≠ 0) :
    a⁻¹ • x ∈ basisCoordinateLattice O b ↔ ‖b.equivFun x‖ ≤ ‖a‖ := by
  rw [mem_basisCoordinateLattice_iff_norm_le_one O hO, map_smul, norm_smul,
    norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr ha), mul_one]

/-- A nonzero vector has an admissible scalar of exactly its maximum coordinate norm. -/
theorem exists_attaining_basisCoordinateLattice_scalar (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (b : Module.Basis ι F X)
    {x : X} (hx : x ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ a⁻¹ • x ∈ basisCoordinateLattice O b ∧
      ‖a‖ = ‖b.equivFun x‖ := by
  have hf : b.equivFun x ≠ 0 := (map_ne_zero_iff b.equivFun b.equivFun.injective).mpr hx
  have hi : ∃ i, b.equivFun x i ≠ 0 := by
    by_contra! hi
    apply hf
    ext i
    exact hi i
  obtain ⟨i, _⟩ := hi
  let : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := (IsGreatest.pi_norm (b.equivFun x)).1
  change ‖b.equivFun x j‖ = ‖b.equivFun x‖ at hj
  have hj0 : b.equivFun x j ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hj]
    exact norm_pos_iff.mpr hf
  exact ⟨b.equivFun x j, hj0,
    (inv_smul_mem_basisCoordinateLattice_iff O hO b x hj0).mpr hj.ge, hj⟩

theorem scalarLatticeGaugeValues_basisCoordinateLattice_nonempty (O : Subring F)
    (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1) (b : Module.Basis ι F X) (x : X) :
    (scalarLatticeGaugeValues (F := F) (basisCoordinateLattice O b : Set X) x).Nonempty := by
  by_cases hx : x = 0
  · subst x
    exact ⟨1, 1, one_ne_zero, by simp, norm_one⟩
  · obtain ⟨a, ha, hax, _⟩ := exists_attaining_basisCoordinateLattice_scalar O hO b hx
    exact ⟨‖a‖, a, ha, hax, rfl⟩

end Coordinates

section NontrivialCoordinates

variable {F : Type u} [NontriviallyNormedField F]
  {X : Type v} [AddCommGroup X] [Module F X] {ι : Type t} [Fintype ι]

/-- The source's intrinsic infimum is the coordinate maximum, including rank zero. -/
theorem scalarLatticeGauge_basisCoordinateLattice
    (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (b : Module.Basis ι F X) (x : X) :
    scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) x =
      ‖b.equivFun x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [scalarLatticeGauge_zero _ (basisCoordinateLattice O b).zero_mem, map_zero, norm_zero]
  · obtain ⟨a, ha, hax, han⟩ := exists_attaining_basisCoordinateLattice_scalar O hO b hx
    apply le_antisymm
    · exact (scalarLatticeGauge_le _ x ha hax).trans han.le
    · change ‖b.equivFun x‖ ≤ sInf
        (scalarLatticeGaugeValues (F := F) (basisCoordinateLattice O b : Set X) x)
      refine le_csInf ?_ ?_
      · exact ⟨‖a‖, a, ha, hax, rfl⟩
      · rintro r ⟨c, hc, hcx, rfl⟩
        exact (inv_smul_mem_basisCoordinateLattice_iff O hO b x hc).mp hcx

theorem scalarLatticeGauge_basisCoordinateLattice_le_one_iff
    (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (b : Module.Basis ι F X) (x : X) :
    scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) x ≤ 1 ↔
      x ∈ basisCoordinateLattice O b := by
  rw [scalarLatticeGauge_basisCoordinateLattice O hO]
  exact (mem_basisCoordinateLattice_iff_norm_le_one O hO b x).symm

theorem scalarLatticeGauge_basisCoordinateLattice_eq_zero_iff
    (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (b : Module.Basis ι F X) (x : X) :
    scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) x = 0 ↔ x = 0 := by
  rw [scalarLatticeGauge_basisCoordinateLattice O hO, norm_eq_zero]
  constructor
  · intro hx
    apply b.equivFun.injective
    simpa only [map_zero] using hx
  · rintro rfl
    exact map_zero b.equivFun

theorem scalarLatticeGauge_basisCoordinateLattice_smul
    (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (b : Module.Basis ι F X) (a : F) (x : X) :
    scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) (a • x) =
      ‖a‖ * scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) x := by
  rw [scalarLatticeGauge_basisCoordinateLattice O hO,
    scalarLatticeGauge_basisCoordinateLattice O hO, map_smul, norm_smul]

theorem scalarLatticeGauge_basisCoordinateLattice_add_le_max [IsUltrametricDist F]
    (O : Subring F) (hO : ∀ a : F, a ∈ O ↔ ‖a‖ ≤ 1)
    (b : Module.Basis ι F X) (x y : X) :
    scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) (x + y) ≤
      max (scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) x)
        (scalarLatticeGauge (F := F) (basisCoordinateLattice O b : Set X) y) := by
  rw [scalarLatticeGauge_basisCoordinateLattice O hO,
    scalarLatticeGauge_basisCoordinateLattice O hO,
    scalarLatticeGauge_basisCoordinateLattice O hO, map_add]
  apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (le_max_left _ _))).mpr
  intro i
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_le_pi_norm _ i) (norm_le_pi_norm _ i))

end NontrivialCoordinates

namespace AdelicStructure

variable {K : Type u} [Field K] [NumberField K] (S : AdelicStructure.{u, v} K)

/-- An actual contracting algebraic integer makes an actual finite completion
genuinely nontrivially normed, with its original completion norm unchanged. -/
@[instance_reducible]
def completedFinitePlaceNontriviallyNormedField (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) : NontriviallyNormedField (S.ϕ ω).Completion :=
  NontriviallyNormedField.ofNormNeOne (by
    obtain ⟨a, ha0, ha⟩ := NormFamily.exists_integral_absValue_lt_one ω hω hnt
    have haK : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
    refine ⟨algebraMap K (S.ϕ ω).Completion (algebraMap (𝓞 K) K a),
      (map_ne_zero_iff _ (algebraMap K (S.ϕ ω).Completion).injective).mpr haK, ?_⟩
    rw [S.norm_algebraMap_eq_absValue]
    exact ne_of_lt ha)

end AdelicStructure

namespace NormFamily

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] {ι : Type t} [Fintype ι]

/-- The actual completed coefficient lattice generated by a rational basis. -/
def completedBasisLattice (S : AdelicStructure.{u, v} K) (b : Module.Basis ι K E)
    (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    Submodule (S.completedLocalRing ω hω) ((S.ϕ ω).Completion ⊗[K] E) :=
  basisCoordinateLattice (S.completedLocalRing ω hω) (b.baseChange (S.ϕ ω).Completion)

theorem completedBasisLattice_eq_span (b : Module.Basis ι K E) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) :
    completedBasisLattice S b ω hω =
      Submodule.span (S.completedLocalRing ω hω)
        (Set.range fun i => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] b i) := by
  rw [completedBasisLattice, basisCoordinateLattice_eq_span]
  apply congrArg (Submodule.span (S.completedLocalRing ω hω))
  exact congrArg Set.range (funext fun i => b.baseChange_apply (S.ϕ ω).Completion i)

/-- The genuine scalar-infimum gauge of the actual completed integral basis
lattice equals the full completed basis norm. -/
theorem scalarLatticeGauge_completedBasisLattice [NumberField K]
    (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (z : (S.ϕ ω).Completion ⊗[K] E) :
    scalarLatticeGauge (F := (S.ϕ ω).Completion)
        (completedBasisLattice S b ω hω : Set ((S.ϕ ω).Completion ⊗[K] E)) z =
      (ofBasis S E b).norm ω z := by
  let := S.completedFinitePlaceNontriviallyNormedField ω hω hnt
  exact scalarLatticeGauge_basisCoordinateLattice (S.completedLocalRing ω hω)
    (S.mem_completedLocalRing ω hω) (b.baseChange (S.ϕ ω).Completion) z

theorem scalarLatticeGauge_completedBasisLattice_tmul_basis [NumberField K]
    (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (a : (S.ϕ ω).Completion) (i : ι) :
    scalarLatticeGauge (F := (S.ϕ ω).Completion)
        (completedBasisLattice S b ω hω : Set ((S.ϕ ω).Completion ⊗[K] E))
        (a ⊗ₜ[K] b i) = ‖a‖ := by
  rw [scalarLatticeGauge_completedBasisLattice b ω hω hnt, ofBasis_norm_tmul_basis]

theorem scalarLatticeGauge_completedBasisLattice_le_one_iff [NumberField K]
    (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial) (z : (S.ϕ ω).Completion ⊗[K] E) :
    scalarLatticeGauge (F := (S.ϕ ω).Completion)
        (completedBasisLattice S b ω hω : Set ((S.ϕ ω).Completion ⊗[K] E)) z ≤ 1 ↔
      z ∈ completedBasisLattice S b ω hω := by
  let := S.completedFinitePlaceNontriviallyNormedField ω hω hnt
  exact scalarLatticeGauge_basisCoordinateLattice_le_one_iff (S.completedLocalRing ω hω)
    (S.mem_completedLocalRing ω hω) (b.baseChange (S.ϕ ω).Completion) z

/-- A model lattice with the actual completed integral frame supplies the
common-basis norm equality; the equality is a produced conclusion. -/
theorem norm_eq_of_completedLatticeGauge [NumberField K] (ξ : NormFamily S E)
    (b : Module.Basis ι K E) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hnt : (S.ϕ ω).IsNontrivial)
    (L : Submodule (S.completedLocalRing ω hω) ((S.ϕ ω).Completion ⊗[K] E))
    (hL : L = Submodule.span (S.completedLocalRing ω hω)
      (Set.range fun i => (1 : (S.ϕ ω).Completion) ⊗ₜ[K] b i))
    (hξ : ∀ z, ξ.norm ω z = scalarLatticeGauge (F := (S.ϕ ω).Completion)
      (L : Set ((S.ϕ ω).Completion ⊗[K] E)) z)
    (z : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω z = (ofBasis S E b).norm ω z := by
  rw [hξ, hL, ← completedBasisLattice_eq_span b ω hω]
  exact scalarLatticeGauge_completedBasisLattice b ω hω hnt z

end NormFamily

end ArakelovGeometry
