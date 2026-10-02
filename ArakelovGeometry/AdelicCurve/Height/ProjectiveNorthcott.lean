/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Height.Projective
import ArakelovGeometry.AdelicCurve.Height.Northcott

/-!
# Northcott finiteness in projective space

Finite sets of possible normalized coordinates give finitely many projective
points. This is the final finite-set argument in Chen–Moriwaki, Theorem 3.5.3.
-/

namespace Projectivization

variable {L ι : Type*} [Field L] [Finite ι]

/-- Projective points admitting representatives in a fixed finite coordinate set
form a finite set. No choice of chart is required in the conclusion. -/
theorem finite_of_representatives_in_finite_set {s : Set (Projectivization L (ι → L))}
    {t : Set L} (ht : t.Finite)
    (hs : ∀ x ∈ s, ∃ (a : ι → L) (ha : a ≠ 0),
      (∀ i, a i ∈ t) ∧ mk L a ha = x) : s.Finite := by
  let v : Set {a : ι → L // a ≠ 0} := {a | ∀ i, a.val i ∈ t}
  have hv : v.Finite := Set.Finite.of_injOn
    (f := Subtype.val) (t := {a : ι → L | ∀ i, a i ∈ t})
    (fun _ h ↦ h) Subtype.val_injective.injOn (Set.Finite.pi' (fun _ ↦ ht))
  apply (hv.image (mk' L)).subset
  intro x hx
  obtain ⟨a, ha, hat, hax⟩ := hs x hx
  exact ⟨⟨a, ha⟩, hat, hax⟩

end Projectivization

namespace ArakelovGeometry.AdelicStructure

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Fintype ι] [Nonempty ι]
    (AS : AdelicStructure K) [AS.IsProper]

/-- Northcott's theorem for projective points over any algebraic extension:
both the height and the degree of the intrinsic field of definition are bounded. -/
theorem finite_projectiveHeight_le_degree_le (hS : AS.HasNorthcott) (C δ : ℝ) :
    letI := Algebraic.isProper_algebraicExtension AS L
    Set.Finite {x : Projectivization L (ι → L) |
      (AS.algebraicExtension L).projectiveHeight x ≤ C ∧
        (Module.finrank K (x.fieldOfDefinition K) : ℝ) ≤ δ} := by
  let := Algebraic.isProper_algebraicExtension AS L
  apply Projectivization.finite_of_representatives_in_finite_set
    (AS.finite_affineHeight_le_degree_le (L := L) hS C δ)
  intro x hx
  obtain ⟨j, hj⟩ : ∃ j, x.rep j ≠ 0 := by
    by_contra! hzero
    exact x.rep_nonzero (funext hzero)
  refine ⟨x.normalizedCoordinates j, x.normalizedCoordinates_ne_zero hj,
    ?_, x.mk_normalizedCoordinates hj⟩
  intro i
  refine ⟨((AS.algebraicExtension L).affineHeight_normalizedCoordinates_le x hj i).trans
    hx.1, ?_⟩
  exact (Nat.cast_le.mpr (x.finrank_adjoin_div_le K i j)).trans hx.2

/-- Chen–Moriwaki, Theorem 3.5.3, for every projective dimension and all real bounds. -/
theorem finite_absoluteHeight_le_degree_le (hS : AS.HasNorthcott) (n : ℕ) (C δ : ℝ) :
    Set.Finite {x : Projectivization (AlgebraicClosure K) (Fin (n + 1) → AlgebraicClosure K) |
      AS.absoluteHeight x ≤ C ∧ (Module.finrank K (x.fieldOfDefinition K) : ℝ) ≤ δ} :=
  AS.finite_projectiveHeight_le_degree_le hS C δ

end ArakelovGeometry.AdelicStructure
