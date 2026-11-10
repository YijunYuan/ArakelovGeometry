/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Actual locally free sheaves and affine free-section comparison

Native local generator data transports along actual sheaf isomorphisms.
On an affine scheme, free global sections of a quasicoherent sheaf give
an actual isomorphism to a free sheaf through the usual tilde adjunction.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace ArakelovGeometry

universe u

set_option backward.isDefEq.respectTransparency false in
/-- A quasicoherent sheaf on the actual affine spectrum with free global
sections is canonically isomorphic to the corresponding free sheaf. -/
def affineFreeSheafIso (R : CommRingCat.{u}) (M : (Spec R).Modules)
    [M.IsQuasicoherent] [Module.Free R (moduleSpecΓFunctor.obj M)] :
    SheafOfModules.free (Module.Free.ChooseBasisIndex R (moduleSpecΓFunctor.obj M)) ≅ M := by
  let b := Module.Free.chooseBasis R (moduleSpecΓFunctor.obj M)
  let : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) M).mp inferInstance
  exact (tildeFinsupp (R := R)
    (Module.Free.ChooseBasisIndex R (moduleSpecΓFunctor.obj M))).symm ≪≫
    (tilde.functor R).mapIso b.repr.symm.toModuleIso ≪≫
      asIso (C := (Spec R).Modules) (Scheme.Modules.fromTildeΓ (R := R) M)

end ArakelovGeometry
