import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower
import ArakelovGeometry.AdelicCurve.Morphism.Algebraic
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Scoped notation for adelic structures

Open `ArakelovGeometry.AdelicStructure` alongside the existing `TensorProduct` and
`CategoryTheory` scopes. Check that each notation selects its intended mathematical
object, including when the base field is named `F` rather than `K`.

Run with `lake env lean scripts/check_adelic_notation.lean` after `lake build`.
-/

open ArakelovGeometry

noncomputable section

universe u v w u' v'

section ScopedNotation

-- This is the user-facing scope declaration; the other two scopes can remain open.
open scoped AdelicStructure TensorProduct CategoryTheory

section OrdinaryNotation

variable (R : Type u) [CommSemiring R]
variable (M : Type v) (N : Type w)
variable [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

-- The ordinary tensor product remains a type, and pure tensors retain their notation.
example : (M ⊗[R] N) = TensorProduct R M N := rfl

example (m : M) (n : N) : M ⊗[R] N := m ⊗ₜ[R] n

variable (p : M ⊗[R] N)

/-- info: p : M ⊗[R] N -/
#guard_msgs in
#check p

-- Ordinary equivalences of types do not become equivalences of adelic structures.
example (e : M ≃ N) : _root_.Equiv M N := e

variable {α β : Type} (e : α ≃ β)

/-- info: e : α ≃ β -/
#guard_msgs in
#check e

end OrdinaryNotation

section StructureMorphisms

variable {F : Type u} {L : Type u'} [Field F] [Field L]
variable (S : AdelicStructure.{u, v} F) (T : AdelicStructure.{u', v'} L)
variable (U : AdelicStructure.{u, w} F)

-- The arrow can connect structures over different fields and keeps the field map
-- contravariant. Its target type is precisely the existing structure-level Hom.
example (f : S ⟶ T) : L →+* F := f.fieldMap
example (f : S ⟶ T) : AdelicStructure.Hom S T := f
example (f : AdelicStructure.Hom S T) : S ⟶ T := f

-- The equivalence notation is for structures over the same underlying field.
example (e : S ≃ U) : AdelicStructure.Equiv S U := e
example (e : AdelicStructure.Equiv S U) : S ≃ U := e

variable (f : S ⟶ T) (e : S ≃ U)

/-- info: f : S ⟶ T -/
#guard_msgs in
#check f

/-- info: e : S ≃ U -/
#guard_msgs in
#check e

end StructureMorphisms

section AlgebraicExtensions

-- Naming the base field `F` checks that the notation does not accidentally rewrite
-- a named argument label when substituting the base-field expression.
variable {F : Type u} {L : Type u'} [Field F] [Field L]
variable [Algebra F L] [Algebra.IsAlgebraic F L]
variable (S : AdelicStructure.{u, v} F)

example : (S ⊗[F] L) = S.algebraicExtension L := rfl

example [S.IsProper] : (S ⊗[F] L).IsProper :=
  AdelicStructure.Algebraic.isProper_algebraicExtension S L

example : (S ⊗[F] L) ⟶ S := AdelicStructure.Hom.algebraicExtension S L

-- Nested extensions are compared by the established tower equivalence, with the
-- intermediate field supplied as a type through its coercion.
example (E : IntermediateField F L) : ((S ⊗[F] E) ⊗[E] L) ≃ (S ⊗[F] L) :=
  AdelicStructure.Algebraic.towerEquiv S E

-- Delaboration recovers the base field even when the term was written by name.
/-- info: S ⊗[F] L : AdelicStructure L -/
#guard_msgs in
#check S.algebraicExtension L

variable (f : (S ⊗[F] L) ⟶ S)

/-- info: f : S ⊗[F] L ⟶ S -/
#guard_msgs in
#check f

-- Disabling notation also disables the custom tensor presentation.
/-- info: S.algebraicExtension L : AdelicStructure L -/
#guard_msgs in
set_option pp.notation false in
#check S.algebraicExtension L

end AlgebraicExtensions

section BundledCategory

variable (C D E : AdelicCurve.{u, v})

-- Curves keep the ordinary category-theoretic arrow, identity, and composition.
example (f : C ⟶ D) : AdelicCurve.Hom C D := f
example : (𝟙 C : C ⟶ C) = AdelicStructure.Hom.id C.AS := rfl
example (f : C ⟶ D) (g : D ⟶ E) : f ≫ g = g.comp f := rfl

-- Categorical isomorphisms use their own notation and remain unchanged.
example (e : C ≅ D) : CategoryTheory.Iso C D := e
example : C ≅ C := CategoryTheory.Iso.refl C

variable (f : C ⟶ D) (e : C ≅ D)

/-- info: f : C ⟶ D -/
#guard_msgs in
#check f

/-- info: e : C ≅ D -/
#guard_msgs in
#check e

end BundledCategory

end ScopedNotation

section OutsideScope

variable {K : Type u} [Field K]
variable (S : AdelicStructure.{u, v} K) (T : AdelicStructure.{u, w} K)
variable (f : AdelicStructure.Hom S T)

-- Importing the notation does not enable it globally; leaving the scope restores
-- the ordinary named presentation of structure morphisms.
/-- info: f : S.Hom T -/
#guard_msgs in
#check f

variable {L : Type u'} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- info: S.algebraicExtension L : AdelicStructure L -/
#guard_msgs in
#check S.algebraicExtension L

end OutsideScope
