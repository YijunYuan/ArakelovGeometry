/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.Map
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init

/-!
# Canonical duality of determinant lines

The exterior pairing, rather than a chosen identification of two lines, defines
the duality map. Its equivalence and scalar-extension formulas include degree
zero and exterior degrees above the dimension.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

variable (K : Type*) [Field K] (E : Type*) [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The canonical exterior pairing is bijective in finite dimension. -/
theorem exteriorPairingDual_bijective (n : ℕ) :
    Function.Bijective (_root_.exteriorPower.pairingDual K E n) := by
  classical
  let b := Module.finBasis K E
  let e := (b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)
  have he : e.toLinearMap = _root_.exteriorPower.pairingDual K E n := by
    apply (b.dualBasis.exteriorPower n).ext
    intro s
    change e ((b.dualBasis.exteriorPower n) s) = _
    rw [Module.Basis.equiv_apply]
    change (b.exteriorPower n).dualBasis s = _
    rw [Module.Basis.coe_dualBasis, _root_.exteriorPower.basis_coord,
      _root_.exteriorPower.basis_apply]
    simp only [_root_.exteriorPower.ιMultiDual,
      Module.Basis.coe_dualBasis]
  rw [← he]
  exact e.bijective

/-- Exterior duality is the actual canonical pairing. -/
def exteriorDualEquiv (n : ℕ) :
    (⋀[K]^n (Module.Dual K E)) ≃ₗ[K] Module.Dual K (⋀[K]^n E) :=
  LinearEquiv.ofBijective (_root_.exteriorPower.pairingDual K E n)
    (exteriorPairingDual_bijective K E n)

@[simp]
theorem exteriorDualEquiv_apply (n : ℕ) (z : ⋀[K]^n (Module.Dual K E)) :
    exteriorDualEquiv K E n z = _root_.exteriorPower.pairingDual K E n z := rfl

/-- The determinant duality includes the canonical equality of dual ranks. -/
def determinantDualEquiv :
    (⋀[K]^(Module.finrank K (Module.Dual K E)) (Module.Dual K E)) ≃ₗ[K]
      Module.Dual K (⋀[K]^(Module.finrank K E) E) :=
  (exteriorPowerDegreeEquiv K (Module.Dual K E) Subspace.dual_finrank_eq).trans
    (exteriorDualEquiv K E (Module.finrank K E))

/-- On decomposable tensors, exterior duality is the determinant pairing. -/
theorem exteriorDualEquiv_ιMulti_ιMulti (n : ℕ)
    (f : Fin n → Module.Dual K E) (x : Fin n → E) :
    exteriorDualEquiv K E n (_root_.exteriorPower.ιMulti K n f)
        (_root_.exteriorPower.ιMulti K n x) =
      (Matrix.of fun i j ↦ f j (x i)).det :=
  _root_.exteriorPower.pairingDual_ιMulti_ιMulti f x

omit [FiniteDimensional K E] in
/-- A basis wedge and its dual wedge pair to one, including the empty basis. -/
theorem exteriorPairingDual_dualBasis (n : ℕ) (b : Module.Basis (Fin n) K E) :
    _root_.exteriorPower.pairingDual K E n (_root_.exteriorPower.ιMulti K n b.dualBasis)
        (_root_.exteriorPower.ιMulti K n b) = 1 := by
  rw [_root_.exteriorPower.pairingDual_ιMulti_ιMulti]
  have h : (Matrix.of fun i j ↦ b.dualBasis j (b i)) = (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.one_apply, Finsupp.single_apply]
  rw [h, Matrix.det_one]

variable (L : Type*) [Field L] [Algebra K L]

/-- The canonical exterior dual pairing commutes with scalar extension. -/
theorem exteriorPairingDual_baseChange (n : ℕ)
    (z : L ⊗[K] (⋀[K]^n (Module.Dual K E))) (w : L ⊗[K] (⋀[K]^n E)) :
    dualBaseChangeEquiv K L (⋀[K]^n E)
        ((_root_.exteriorPower.pairingDual K E n).baseChange L z) w =
      _root_.exteriorPower.pairingDual L (L ⊗[K] E) n
        (_root_.exteriorPower.map n (dualBaseChangeEquiv K L E).toLinearMap
          (exteriorBaseChangeEquiv K L (Module.Dual K E) n z))
        (exteriorBaseChangeEquiv K L E n w) := by
  classical
  let b := Module.finBasis K E
  have he : (dualBaseChangeEquiv K L (⋀[K]^n E)).toLinearMap ∘ₗ
        (_root_.exteriorPower.pairingDual K E n).baseChange L =
      (exteriorBaseChangeEquiv K L E n).dualMap.toLinearMap ∘ₗ
        _root_.exteriorPower.pairingDual L (L ⊗[K] E) n ∘ₗ
          _root_.exteriorPower.map n (dualBaseChangeEquiv K L E).toLinearMap ∘ₗ
            (exteriorBaseChangeEquiv K L (Module.Dual K E) n).toLinearMap := by
    apply ((b.dualBasis.exteriorPower n).baseChange L).ext
    intro s
    apply ((b.exteriorPower n).baseChange L).ext
    intro t
    simp [Module.Basis.baseChange_apply, _root_.exteriorPower.basis_apply,
      _root_.exteriorPower.ιMulti_family, Function.comp_def, RingHom.map_det]
    rfl
  exact congrArg (fun f ↦ f z w) he

end

end ArakelovGeometry
