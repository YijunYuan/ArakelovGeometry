---
author: sync
content_type: definition
created: '2026-10-02T11:55:12'
decl: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.extendAbsoluteValue
docstring: 'The formula (3.13) extending an absolute value from the separable part
  `K''` to the finite

  extension `L`: `|a| = |a^q|^(1/q)`, where `q = [L : K'']`.'
file: ArakelovGeometry/AdelicCurve/Extension/Finite/Construction.lean
generated: lean
lean_status: lean_ok
title: ArakelovGeometry.AdelicStructure.ParameterSpaceFinExtension.extendAbsoluteValue
type: lean
updated: '2026-10-02T11:55:12'
---
noncomputable def extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) : AbsoluteValue L ℝ where
  toFun a :=
    v ⟨a ^ Field.finInsepDegree K L,
        pow_finInsepDegree_mem_separableClosure K a⟩ ^
      ((Field.finInsepDegree K L : ℝ)⁻¹)
  map_mul' a b := by
    have hmul :
        (⟨(a * b) ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K (a * b)⟩ : separableClosure K L) =
          ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩ *
            ⟨b ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K b⟩ := by
      ext
      exact mul_pow a b _
    rw [hmul, map_mul, Real.mul_rpow (v.nonneg _) (v.nonneg _)]
  nonneg' a := by
    exact Real.rpow_nonneg (v.nonneg _) _
  eq_zero' a := by
    have hq : (Field.finInsepDegree K L : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne _)
    rw [Real.rpow_eq_zero (v.nonneg _) (inv_ne_zero hq), v.eq_zero]
    simp only [Subtype.ext_iff, ZeroMemClass.coe_zero, pow_eq_zero_iff (NeZero.ne _)]
  add_le' a b := by
    obtain ⟨p, hp⟩ := ExpChar.exists L
    let : ExpChar K p := (algebraMap K L).expChar (algebraMap K L).injective p
    obtain ⟨n, hn⟩ := finInsepDegree_eq_pow K L p
    have hadd :
        (⟨(a + b) ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K (a + b)⟩ : separableClosure K L) =
          ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩ +
            ⟨b ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K b⟩ := by
      apply Subtype.ext
      change (a + b) ^ Field.finInsepDegree K L =
        a ^ Field.finInsepDegree K L + b ^ Field.finInsepDegree K L
      rw [hn, add_pow_expChar_pow]
    have hr : 0 ≤ (Field.finInsepDegree K L : ℝ)⁻¹ := by positivity
    have hr₁ : (Field.finInsepDegree K L : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Field.finInsepDegree K L))
    rw [hadd]
    exact (Real.rpow_le_rpow (v.nonneg _) (v.add_le _ _) hr).trans
      (Real.rpow_add_le_add_rpow (v.nonneg _) (v.nonneg _) hr hr₁)