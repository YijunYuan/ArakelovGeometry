module

public import ArakelovGeometry.InvariantTheory.Polynomial.HomogeneousTensor
public import ArakelovGeometry.InvariantTheory.TensorPower.Semisimple
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Finite binary polynomial semisimplicity

The concrete binary tensor representation is generated, for either special-linear
factor, by copies of that factor's fixed tensor power. This is the representation
input for bounded polynomial invariant lifting in Bost p31. No semisimplicity of
the infinite special-linear group algebra as a ring is asserted.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.InvariantTheory

open scoped TensorProduct

variable {k G V U : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]

/-- An injective actual equivariant map transfers module semisimplicity to its source. -/
theorem representation_semisimple_of_injective (ρ : Representation k G V)
    (τ : Representation k G U) [IsSemisimpleModule (MonoidAlgebra k G) τ.asModule]
    (f : V →ₗ[k] U) (hf : ∀ g v, f (ρ g v) = τ g (f v))
    (hi : Function.Injective f) : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule := by
  exact IsSemisimpleModule.of_injective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
      (f.intertwiningMap_of_isIntertwiningMap ρ τ hf)) hi

/-- An equivariant quotient transfers semisimplicity of the actual source module. -/
theorem representation_semisimple_of_surjective (ρ : Representation k G V)
    (τ : Representation k G U) [IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule]
    (f : V →ₗ[k] U) (hf : ∀ g v, f (ρ g v) = τ g (f v))
    (hs : Function.Surjective f) : IsSemisimpleModule (MonoidAlgebra k G) τ.asModule := by
  exact IsSemisimpleModule.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
      (f.intertwiningMap_of_isIntertwiningMap ρ τ hf)) hs

/-- A stable vector subspace inherits semisimplicity of the actual representation. -/
theorem subrepresentation_semisimple (ρ : Representation k G V)
    [IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule]
    (S : Subrepresentation ρ) :
    IsSemisimpleModule (MonoidAlgebra k G) S.toRepresentation.asModule :=
  representation_semisimple_of_injective S.toRepresentation ρ S.toSubmodule.subtype
    (fun _ _ ↦ rfl) Subtype.val_injective

/-- A surjective invariant functional on a stable subspace of a semisimple
representation has an invariant lift of one. The representation, not the group
algebra as a ring, is assumed semisimple. -/
theorem exists_fixed_lift_one (ρ : Representation k G V)
    [IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule]
    (S : Subrepresentation ρ) (e : S.toSubmodule →ₗ[k] k)
    (he : ∀ g v, e (S.toRepresentation g v) = e v)
    (hs : Function.Surjective e) :
    ∃ v : S.toSubmodule, e v = 1 ∧ ∀ g, S.toRepresentation g v = v := by
  let τ : Representation k G k := 1
  have := subrepresentation_semisimple ρ S
  let q := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation τ
    (e.intertwiningMap_of_isIntertwiningMap S.toRepresentation τ he)
  obtain ⟨s, hsec⟩ := IsSemisimpleModule.lifting_property q hs LinearMap.id
  let one : τ.asModule := τ.asModuleEquiv.symm 1
  refine ⟨s one, DFunLike.congr_fun hsec one, ?_⟩
  intro g
  have h := s.map_smul (MonoidAlgebra.single g (1 : k)) one
  simp only [Representation.single_smul, one_smul] at h
  change s one = S.toRepresentation g (s one) at h
  exact h.symm

section TwoFactors

variable {H : Type*} [Group H]

/-- Successive invariant lifting for two commuting semisimple modules.
The first invariant section is used only for surjectivity on the first fixed
subspace; it is not assumed equivariant for the second factor. -/
theorem exists_joint_fixed_lift_one (ρ : Representation k G V) (τ : Representation k H V)
    [IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule]
    [IsSemisimpleModule (MonoidAlgebra k H) τ.asModule]
    (hc : ∀ g h v, ρ g (τ h v) = τ h (ρ g v))
    (S : Submodule k V) (hSρ : ∀ g v, v ∈ S → ρ g v ∈ S)
    (hSτ : ∀ h v, v ∈ S → τ h v ∈ S)
    (e : V →ₗ[k] k) (heρ : ∀ g v, e (ρ g v) = e v)
    (heτ : ∀ h v, e (τ h v) = e v)
    (hs : ∃ v ∈ S, e v = 1) :
    ∃ v ∈ S, e v = 1 ∧ (∀ g, ρ g v = v) ∧ (∀ h, τ h v = v) := by
  let Sρ : Subrepresentation ρ := ⟨S, fun g v hv ↦ hSρ g v hv⟩
  have hsurj : Function.Surjective (e.domRestrict S) := by
    obtain ⟨v, hv, he⟩ := hs
    intro a
    exact ⟨a • (⟨v, hv⟩ : S), by simp [he]⟩
  obtain ⟨v, hv, hfix⟩ := exists_fixed_lift_one ρ Sρ (e.domRestrict S)
    (fun g x ↦ heρ g x) hsurj
  let Sfix : Submodule k V :=
    { carrier := {x | x ∈ S ∧ ∀ g, ρ g x = x}
      zero_mem' := ⟨S.zero_mem, fun g ↦ map_zero _⟩
      add_mem' := fun hx hy ↦ ⟨S.add_mem hx.1 hy.1,
        fun g ↦ by rw [map_add, hx.2, hy.2]⟩
      smul_mem' := fun a x hx ↦ ⟨S.smul_mem a hx.1,
        fun g ↦ by rw [map_smul, hx.2]⟩ }
  have hstable (h : H) {x : V} (hx : x ∈ Sfix) : τ h x ∈ Sfix := by
    exact ⟨hSτ h x hx.1, fun g ↦ by rw [hc, hx.2]⟩
  let Sτ : Subrepresentation τ := ⟨Sfix, hstable⟩
  have hvfix : v.val ∈ Sfix :=
    ⟨v.property, fun g ↦ congrArg Subtype.val (hfix g)⟩
  have hsurj' : Function.Surjective (e.domRestrict Sfix) := by
    intro a
    exact ⟨a • (⟨v.val, hvfix⟩ : Sfix), by simpa using congrArg (a * ·) hv⟩
  obtain ⟨w, hw, hwfix⟩ := exists_fixed_lift_one τ Sτ (e.domRestrict Sfix)
    (fun h x ↦ heτ h x) hsurj'
  exact ⟨w.val, w.property.1, hw, w.property.2,
    fun h ↦ congrArg Subtype.val (hwfix h)⟩

end TwoFactors

section TensorCopies

variable (k) (E : Bool → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module k (E j)]

/-- Restriction to one of the two actual special-linear factors. -/
def binaryFactorHom (j : Bool) :
    SpecialLinearGroup k (E j) →* (∀ i, SpecialLinearGroup k (E i)) :=
  MonoidHom.mulSingle (fun i ↦ SpecialLinearGroup k (E i)) j

/-- The positive diagonal action on a finitely indexed tensor power. -/
def indexedTensorSLRepresentation (j : Bool) (α : Type*) :
    Representation k (SpecialLinearGroup k (E j)) (⨂[k] (_ : α), E j) where
  toFun g := PiTensorProduct.map fun _ ↦ g.val.toLinearMap
  map_one' := PiTensorProduct.map_one
  map_mul' _ _ := PiTensorProduct.map_mul _ _

/-- A finite reindexing transfers the checked fixed-degree tensor-power theorem. -/
theorem indexedTensorSL_semisimple [IsAlgClosed k] [CharZero k]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    (j : Bool) (α : Type*) [Finite α] :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j)))
      (indexedTensorSLRepresentation k E j α).asModule := by
  let := Fintype.ofFinite α
  have := tensorPowerSL_isSemisimpleModule k (E j) (Fintype.card α)
  let e := PiTensorProduct.reindex k (fun _ : α ↦ E j) (Fintype.equivFin α)
  apply representation_semisimple_of_injective (indexedTensorSLRepresentation k E j α)
    (tensorPowerSLRepresentation k (E j) (Fintype.card α)) e.toLinearMap _ e.injective
  intro g x
  exact (PiTensorProduct.map_reindex (fun _ : α ↦ g.val.toLinearMap)
    (Fintype.equivFin α) x).symm

/-- The tensor of tensor powers occurring before polynomial multiplication. -/
def binaryNestedRepresentation (r d : ℕ) :
    Representation k (∀ j, SpecialLinearGroup k (E j))
      (⨂[k]^d (⨂[k]^r (⨂[k] j, E j))) :=
  tensorPowerRepresentation d (tensorPowerRepresentation r (tensorSLRepresentation E))

/-- Fix all other-factor vectors and vary the selected factor in every slot.
This map is a concrete finite tensor-power copy, before multiplication. -/
def binaryTensorCopy (r d : ℕ) (j : Bool)
    (y : Fin d → Fin r → ∀ i, E i) :
    (⨂[k] (_ : (Σ _ : Fin d, Fin r)), E j) →ₗ[k]
      (⨂[k]^d (⨂[k]^r (⨂[k] i, E i))) :=
  PiTensorProduct.lift
    ((PiTensorProduct.tprod k).compMultilinearMap fun i : Fin d ↦
      (PiTensorProduct.tprod k).compLinearMap fun l : Fin r ↦
        (PiTensorProduct.tprod k).toLinearMap (y i l) j)

@[simp]
theorem binaryTensorCopy_tprod (r d : ℕ) (j : Bool)
    (y : Fin d → Fin r → ∀ i, E i) (x : (Σ _ : Fin d, Fin r) → E j) :
    binaryTensorCopy k E r d j y (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i ↦ PiTensorProduct.tprod k (fun l ↦
        PiTensorProduct.tprod k (Function.update (y i l) j (x ⟨i, l⟩)))) := by
  simp [binaryTensorCopy, MultilinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.toLinearMap_apply, Sigma.curry]

private theorem tensorSL_single_update (j : Bool) (g : SpecialLinearGroup k (E j))
    (y : ∀ i, E i) (x : E j) :
    tensorSLRepresentation E (binaryFactorHom k E j g)
        (PiTensorProduct.tprod k (Function.update y j x)) =
      PiTensorProduct.tprod k (Function.update y j (g x)) := by
  change PiTensorProduct.map _ _ = _
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = j
  · subst i; simp [binaryFactorHom]
  · simp [binaryFactorHom, h]

/-- Every tensor copy intertwines the positive SL action with the restriction
of the actual A2 binary tensor action. -/
theorem binaryTensorCopy_equivariant (r d : ℕ) (j : Bool)
    (y : Fin d → Fin r → ∀ i, E i)
    (g : SpecialLinearGroup k (E j)) (x : ⨂[k] (_ : (Σ _ : Fin d, Fin r)), E j) :
    binaryTensorCopy k E r d j y (indexedTensorSLRepresentation k E j _ g x) =
      binaryNestedRepresentation k E r d (binaryFactorHom k E j g)
        (binaryTensorCopy k E r d j y x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [map_smul]
    congr 1
    change binaryTensorCopy k E r d j y (PiTensorProduct.map _ _) = _
    rw [PiTensorProduct.map_tprod, binaryTensorCopy_tprod, binaryTensorCopy_tprod]
    change _ = PiTensorProduct.map _ _
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext i
    change _ = PiTensorProduct.map _ _
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext l
    exact (tensorSL_single_update k E j g (y i l) (x ⟨i, l⟩)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- For either actual binary SL factor, the nested tensor module is generated
by fixed-degree semisimple tensor copies. The other factor supplies finite
multiplicity, with no claim about semisimplicity of its group algebra. -/
theorem binaryNested_factor_semisimple [IsAlgClosed k] [CharZero k]
    [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
    (r d : ℕ) (j : Bool) :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j)))
      (Representation.asModule
        ((binaryNestedRepresentation k E r d).comp (binaryFactorHom k E j))) := by
  classical
  let ρ := indexedTensorSLRepresentation k E j (Σ _ : Fin d, Fin r)
  let τ : Representation k (SpecialLinearGroup k (E j))
      (⨂[k]^d (⨂[k]^r (⨂[k] i, E i))) :=
    (binaryNestedRepresentation k E r d).comp (binaryFactorHom k E j)
  let b (i : Bool) := Module.Free.chooseBasis k (E i)
  let B := Basis.piTensorProduct (fun _ : Fin d ↦
    Basis.piTensorProduct (fun _ : Fin r ↦
      Basis.piTensorProduct b))
  let f (p : Fin d → Fin r → ∀ i, Module.Free.ChooseBasisIndex k (E i)) :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
      ((binaryTensorCopy k E r d j (fun a l i ↦ b i (p a l i))).intertwiningMap_of_isIntertwiningMap
        ρ τ (binaryTensorCopy_equivariant k E r d j _))
  have : IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j))) ρ.asModule :=
    indexedTensorSL_semisimple k E j _
  apply isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun p ↦ (f p).range) (fun p ↦ IsSemisimpleModule.range (f p))
  apply top_unique
  intro x _
  have htop : Submodule.span k (Set.range B) = ⊤ := B.span_eq
  have hx : τ.asModuleEquiv x ∈ Submodule.span k (Set.range B) := by rw [htop]; trivial
  suffices hall : ∀ z ∈ Submodule.span k (Set.range B),
      τ.asModuleEquiv.symm z ∈ ⨆ p, (f p).range from hall _ hx
  intro z hz
  induction hz using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, rfl⟩ := hv
    apply Submodule.mem_iSup_of_mem p
    refine ⟨PiTensorProduct.tprod k (fun a ↦ b j (p a.1 a.2 j)), ?_⟩
    change binaryTensorCopy k E r d j (fun a l i ↦ b i (p a l i)) _ = B p
    simp [binaryTensorCopy_tprod, B, Basis.piTensorProduct_apply]
  | zero => exact Submodule.zero_mem _
  | add x y hx hy hix hiy => exact Submodule.add_mem _ hix hiy
  | smul a x hx hix => exact Submodule.smul_of_tower_mem _ a hix

variable [IsAlgClosed k] [CharZero k]
  [∀ j, FiniteDimensional k (E j)] [∀ j, Nontrivial (E j)]
  {ι : Type*} [Fintype ι]

/-- Each homogeneous block of the actual covector polynomial representation
is semisimple for either binary SL factor, by the actual multiplication quotient. -/
theorem binaryHomogeneous_factor_semisimple (r d : ℕ)
    (b : Module.Basis ι k (Module.Dual k (⨂[k]^r (⨂[k] i, E i)))) (j : Bool) :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j)))
      (Representation.asModule ((homogeneousPolynomialRepresentation b
        (tensorPowerRepresentation r (tensorSLRepresentation E)).dual d).comp
          (binaryFactorHom k E j))) := by
  let ρ := tensorPowerRepresentation r (tensorSLRepresentation (k := k) E)
  let src : Representation k (SpecialLinearGroup k (E j)) (⨂[k]^d (⨂[k]^r (⨂[k] i, E i))) :=
    (binaryNestedRepresentation k E r d).comp (binaryFactorHom k E j)
  let dst : Representation k (SpecialLinearGroup k (E j))
      (MvPolynomial.homogeneousSubmodule ι k d) :=
    (homogeneousPolynomialRepresentation b ρ.dual d).comp (binaryFactorHom k E j)
  have : IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j))) src.asModule :=
    binaryNested_factor_semisimple k E r d j
  apply representation_semisimple_of_surjective src dst
    ((homogeneousTensorMap b d).codRestrict _ (homogeneousTensorMap_mem b d))
    _ (homogeneousTensorMap_surjective b d)
  intro g x
  apply Subtype.ext
  exact homogeneousTensorMap_equivariant b ρ d (binaryFactorHom k E j g) x

/-- Bounded polynomials are generated by their finitely many homogeneous blocks.
This proves semisimplicity degree by degree, without a central-scalar assertion
on mixed degrees, for the actual Bost binary tensor covector representation. -/
theorem binaryBounded_factor_semisimple (r D : ℕ)
    (b : Module.Basis ι k (Module.Dual k (⨂[k]^r (⨂[k] i, E i)))) (j : Bool) :
    IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j)))
      (Representation.asModule ((boundedPolynomialRepresentation b
        (tensorPowerRepresentation r (tensorSLRepresentation E)).dual D).comp
          (binaryFactorHom k E j))) := by
  classical
  let ρ := (tensorPowerRepresentation r (tensorSLRepresentation (k := k) E)).dual
  let τ : Representation k (SpecialLinearGroup k (E j))
      (MvPolynomial.restrictTotalDegree ι k D) :=
    (boundedPolynomialRepresentation b ρ D).comp (binaryFactorHom k E j)
  let σ (d : Fin (D + 1)) : Representation k (SpecialLinearGroup k (E j))
      (MvPolynomial.homogeneousSubmodule ι k d.val) :=
    (homogeneousPolynomialRepresentation b ρ d.val).comp (binaryFactorHom k E j)
  let incl (d : Fin (D + 1)) :
      MvPolynomial.homogeneousSubmodule ι k d.val →ₗ[k]
        MvPolynomial.restrictTotalDegree ι k D :=
    (MvPolynomial.homogeneousSubmodule ι k d.val).inclusion
      (fun p hp ↦ (MvPolynomial.mem_restrictTotalDegree ι D p).mpr
        (hp.totalDegree_le.trans (Nat.le_of_lt_succ d.isLt)))
  let f (d : Fin (D + 1)) := Representation.IntertwiningMap.equivLinearMapAsModule (σ d) τ
    ((incl d).intertwiningMap_of_isIntertwiningMap (σ d) τ (fun _ _ ↦ rfl))
  have hsemi (d : Fin (D + 1)) :
      IsSemisimpleModule (MonoidAlgebra k (SpecialLinearGroup k (E j))) (σ d).asModule :=
    binaryHomogeneous_factor_semisimple k E r d.val b j
  apply isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun d ↦ (f d).range) (fun d ↦ by have := hsemi d; exact IsSemisimpleModule.range (f d))
  apply top_unique
  intro p _
  let q := (τ.asModuleEquiv p).val
  have hq : q.totalDegree ≤ D :=
    (MvPolynomial.mem_restrictTotalDegree ι D q).mp (τ.asModuleEquiv p).property
  let u (d : Fin (q.totalDegree + 1)) : τ.asModule := τ.asModuleEquiv.symm
    ⟨MvPolynomial.homogeneousComponent d.val q,
      (MvPolynomial.mem_restrictTotalDegree ι D _).mpr
        ((MvPolynomial.homogeneousComponent_isHomogeneous d.val q).totalDegree_le.trans
          ((Nat.le_of_lt_succ d.isLt).trans hq))⟩
  have hmem (d : Fin (q.totalDegree + 1)) : u d ∈ ⨆ d, (f d).range := by
    let a : Fin (D + 1) := ⟨d.val, Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans hq)⟩
    apply Submodule.mem_iSup_of_mem a
    exact ⟨⟨MvPolynomial.homogeneousComponent d.val q,
      MvPolynomial.homogeneousComponent_mem d.val q⟩, rfl⟩
  have hs := Submodule.sum_mem (⨆ d, (f d).range) (fun d (_ : d ∈ Finset.univ) ↦ hmem d)
  convert hs using 1
  apply τ.asModuleEquiv.injective
  apply Subtype.ext
  simp only [map_sum, Submodule.coe_sum]
  change q = ∑ d : Fin (q.totalDegree + 1), MvPolynomial.homogeneousComponent d.val q
  rw [Fin.sum_univ_eq_sum_range (fun n ↦ MvPolynomial.homogeneousComponent n q),
    MvPolynomial.sum_homogeneousComponent]

end TensorCopies

end ArakelovGeometry.InvariantTheory
