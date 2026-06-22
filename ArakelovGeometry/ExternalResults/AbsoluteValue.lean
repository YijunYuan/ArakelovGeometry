import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Algebra.Order.CauSeq.Completion

namespace AbsoluteValue

def pullback {K : Type u_1} [Field K] (v : AbsoluteValue K ℝ) {L : Type u_2} [Field L]
  (i : L →+* K) : AbsoluteValue L ℝ where
  toFun x :=  v (i x)
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' x y:= by simp [v.add_le (i x) (i y)]

abbrev restriction {K : Type u_1} [Field K] (v : AbsoluteValue K ℝ) (L : Type u_2) [Field L]
  [Algebra L K] : AbsoluteValue L ℝ := pullback v (algebraMap L K)

end AbsoluteValue

instance {K : Type u} [Field K] (v : AbsoluteValue K ℝ) (L : Type u_2) [Field L]
  [Algebra L K] : Algebra (v.restriction L).Completion v.Completion := sorry

--instance {K : Type u} [Field K] (v : AbsoluteValue K ℝ) (L : Type u_2) [Field L]
--  [Algebra L K] [FiniteDimensional L K] : FiniteDimensional (v.restriction L).Completion v.Completion := sorry
