/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Convex
public import HarderNarasimhan.PayoffFunction.Semistable.Defs

/-!
# Comparison with a semistable game interval

Convexity and semistability bound every interval entering a semistable interval.
-/

@[expose] public section

namespace HarderNarasimhan.PayoffFunction

variable {L C : Type*} [Lattice L] [CompleteLinearOrder C]
  {μ : PayoffFunction L C} [μ.IsConvex]

/-- A semistable interval bounds every interval entering it from below. -/
theorem IsSemistable.A_le_of_not_le {I : StrictIntvl L}
    (h : (μ.restrict I).IsSemistable) {u m : L}
    (hum : u < m) (huA : u ≤ I.left) (hmB : m ≤ I.right) (hmA : ¬ m ≤ I.left) :
    μ.A ⟨u, m, hum⟩ ≤ μ.A I := by
  let J : StrictIntvl L := ⟨u, I.right, hum.trans_le hmB⟩
  have hcvx : μ.IsConvexOn J :=
    ⟨fun x y _ _ hxy ↦ (inferInstance : μ.IsConvex).le x y hxy⟩
  have hc := hcvx.A_le_A_sup (x := m) (w := I.left) (u := u)
    ⟨hum.le, hmB⟩ ⟨huA, I.lt.le⟩ hmA (le_inf hum.le huA)
  have hs := h.not_lt
    (⟨m ⊔ I.left, le_sup_right, sup_le hmB I.lt.le⟩ : ↥I) (right_lt_sup.mpr hmA)
  simp only [A_restrict_apply, StrictIntvl.ofSub_top] at hs
  exact hc.trans (le_of_not_gt hs)

end HarderNarasimhan.PayoffFunction
