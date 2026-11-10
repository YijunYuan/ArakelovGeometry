/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Separable.Construction
public import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Finite extensions of adelic structures

A finite extension is constructed from its separable part using the unique extension of
absolute values across a purely inseparable extension. This gives Chen–Moriwaki,
Definition 3.4.1, the completion comparison in Lemma 3.4.2, and the fibre weights of
Remark 3.4.3.
-/

@[expose] public section

open MeasureTheory AbsoluteValue
open scoped ENNReal

universe u v w

namespace ArakelovGeometry.AdelicStructure

variable {K : Type u} [Field K] (AS : AdelicStructure.{u, v} K)
variable (L : Type w) [Field L] [Algebra K L]

/-- The parameter space used for the finite extension `S ⊗_K L` in Definition 3.4.1.
It is the parameter space of the finite separable extension `K'/K`, where `K'` is the separable
part of `L/K`; the paper then identifies `M_{K'}` and `M_L` by the purely inseparable
extension formula. -/
abbrev ParameterSpaceFinExtension [FiniteDimensional K L] :=
  ParameterSpaceExtension AS (separableClosure K L)

namespace ParameterSpaceFinExtension

variable [FiniteDimensional K L]

variable (K) {L} in
/-- If `q = [L : K']` is the inseparable degree, then `a^q ∈ K'`.
This is the algebraic input used in formula (3.13). -/
theorem pow_finInsepDegree_mem_separableClosure (a : L) :
    a ^ Field.finInsepDegree K L ∈ separableClosure K L := by
  obtain ⟨p, hp⟩ := ExpChar.exists (separableClosure K L)
  obtain ⟨n, b, hpoly⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C
    (separableClosure K L) p a
  have hpow : a ^ p ^ n = (b : L) := by
    have h := minpoly.aeval (separableClosure K L) a
    simpa [hpoly, sub_eq_zero] using h
  have hdvd : p ^ n ∣ Field.finInsepDegree K L := by
    simpa [Field.finInsepDegree, hpoly] using
      (minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := separableClosure K L) a))
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, hpow]
  exact pow_mem b.property m

variable {L} in
/-- The formula (3.13) extending an absolute value from the separable part `K'` to the finite
extension `L`: `|a| = |a^q|^(1/q)`, where `q = [L : K']`. -/
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

/-- Formula (3.13) as a simp-ready evaluation statement. -/
theorem extendAbsoluteValue_apply
    (v : AbsoluteValue (separableClosure K L) ℝ) (a : L) :
    extendAbsoluteValue v a =
      v ⟨a ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K a⟩ ^
        ((Field.finInsepDegree K L : ℝ)⁻¹) :=
  rfl

variable {L} in
/-- The inseparable extension agrees with the original absolute value on the separable part. -/
theorem extendAbsoluteValue_coe
    (v : AbsoluteValue (separableClosure K L) ℝ) (b : separableClosure K L) :
    extendAbsoluteValue v (b : L) = v b := by
  rw [extendAbsoluteValue_apply]
  change v (b ^ Field.finInsepDegree K L) ^ (Field.finInsepDegree K L : ℝ)⁻¹ = v b
  rw [map_pow, Real.pow_rpow_inv_natCast (v.nonneg _) (NeZero.ne _)]

variable {L} in
/-- Restricting the inseparable extension recovers the given absolute value. -/
theorem restriction_extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) :
    (extendAbsoluteValue v).under (separableClosure K L) = v := by
  ext b
  exact extendAbsoluteValue_coe v b

/-- An absolute value on a finite extension is recovered uniquely from its separable part. -/
theorem extendAbsoluteValue_restriction (w : AbsoluteValue L ℝ) :
    extendAbsoluteValue (w.under (separableClosure K L)) = w := by
  ext a
  rw [extendAbsoluteValue_apply]
  change w (a ^ Field.finInsepDegree K L) ^ (Field.finInsepDegree K L : ℝ)⁻¹ = w a
  rw [map_pow, Real.pow_rpow_inv_natCast (w.nonneg _) (NeZero.ne _)]

/-- The logarithmic form of formula (3.13), giving formula (3.14):
`ln |a| = q⁻¹ ln |a^q|` with `q` the inseparable degree. -/
theorem log_extendAbsoluteValue
    (v : AbsoluteValue (separableClosure K L) ℝ) (a : L) :
    Real.log (extendAbsoluteValue v a) =
      (Field.finInsepDegree K L : ℝ)⁻¹ *
        Real.log (v ⟨a ^ Field.finInsepDegree K L,
          pow_finInsepDegree_mem_separableClosure K a⟩) := by
  by_cases ha : a = 0
  · subst a
    simp [NeZero.ne (Field.finInsepDegree K L), Subtype.ext_iff]
  · rw [extendAbsoluteValue_apply]
    apply Real.log_rpow (v.pos ?_)
    intro h
    exact pow_ne_zero _ ha (congrArg Subtype.val h)

/-- The canonical bijection `M_{K'} ≃ M_L` in Definition 3.4.1, used here as the parameter map
for the finite extension adelic structure. -/
noncomputable def ϕ (x : AS.ParameterSpaceFinExtension L) : AbsoluteValue L ℝ :=
  extendAbsoluteValue (ParameterSpaceExtension.ϕ x)

/-- The measure on the finite extension `S ⊗_K L`: it is the measure already constructed on the
finite separable extension `K'/K`. -/
noncomputable def measure : Measure (ParameterSpaceFinExtension AS L) :=
  ParameterSpaceExtension.inducedMeasure AS (separableClosure K L)

/-- Logarithmic evaluations on a finite, possibly inseparable, extension are measurable by
formula (3.13) and the finite separable construction on `K'`. -/
theorem measurable_log (a : L) :
    Measurable fun x : ParameterSpaceFinExtension AS L ↦
      Real.log ((ϕ AS L x) a) := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  exact (ParameterSpaceExtension.measurable_log AS (separableClosure K L) _).const_mul _

/-- Logarithmic evaluations on a finite, possibly inseparable, extension are integrable by
formula (3.13) and the finite separable construction on `K'`. -/
theorem integrable_log (a : L) (ha : a ≠ 0) :
    Integrable
      (fun x : ParameterSpaceFinExtension AS L ↦
        Real.log ((ϕ AS L x) a))
      (measure AS L) := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  apply (ParameterSpaceExtension.integrable_log_inducedMeasure AS (separableClosure K L)
    _ ?_).const_mul
  intro h
  exact pow_ne_zero _ ha (congrArg Subtype.val h)

/-- Chen--Moriwaki, Definition 3.4.1: the concrete finite extension adelic structure
`S ⊗_K L`, including the inseparable case. -/
noncomputable def _root_.ArakelovGeometry.AdelicStructure.finiteExtension :
    AdelicStructure L where
  Ω := AS.ParameterSpaceFinExtension L
  A := inferInstance
  v := measure AS L
  ϕ := ParameterSpaceFinExtension.ϕ AS L
  measurable_log := fun a _ha ↦ measurable_log AS L a
  integrable_log := integrable_log AS L

variable {AS} in
/-- The finite fibre over `ω`, using the parameter space of Definition 3.4.1. -/
abbrev BaseFiber (ω : AS.Ω) :=
  {x : ParameterSpaceFinExtension AS L // ParameterSpaceExtension.proj x = ω}

/-- The fibre probability measure for the finite extension `L/K`; it is the finite separable
fibre probability measure on the separable part `K'/K`. -/
noncomputable def fibreProbabilityMeasure (ω : AS.Ω) :
    Measure (BaseFiber L ω) :=
  ParameterSpaceExtension.fibreProbabilityMeasure AS (separableClosure K L) ω

/-- The fibre integration operator `I_{L/K}` of a finite (possibly inseparable) extension
`L/K`, computed on the separable part as in Definition 3.4.1 and Remark 3.4.3. -/
noncomputable def fibreIntegral (f : ParameterSpaceFinExtension AS L → ℝ) : AS.Ω → ℝ :=
  fun ω ↦ ∫ x : BaseFiber L ω, f x.1 ∂fibreProbabilityMeasure AS L ω

/-- The remark closing §3.4.1: the σ-algebra of the finite extension parameter space is also
the smallest σ-algebra making the projection to the base and the evaluations of the extended
absolute values at elements of `L` measurable. -/
theorem measurableSpace_eq_comap_sup :
    (ParameterSpaceExtension.instMeasurableSpace AS (separableClosure K L) :
        MeasurableSpace (ParameterSpaceFinExtension AS L)) =
      MeasurableSpace.comap
          (ParameterSpaceExtension.proj (AS := AS) (L := separableClosure K L)) AS.A ⊔
        ⨆ a : L, MeasurableSpace.comap
          (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a) inferInstance := by
  change _ ⊔ ⨆ b : separableClosure K L, _ = _
  apply le_antisymm
  · refine sup_le le_sup_left (iSup_le fun b ↦ ?_)
    have heval :
        (fun x : ParameterSpaceFinExtension AS L ↦ ParameterSpaceExtension.ϕ x b) =
          (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x (b : L)) := by
      funext x
      exact (extendAbsoluteValue_coe _ b).symm
    rw [heval]
    exact le_trans (le_iSup
      (fun a : L ↦ MeasurableSpace.comap
        (fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a) inferInstance) (b : L))
      le_sup_right
  · refine sup_le le_sup_left (iSup_le fun a ↦ ?_)
    have hmeas : Measurable fun x : ParameterSpaceFinExtension AS L ↦ ϕ AS L x a := by
      simp_rw [ϕ, extendAbsoluteValue_apply]
      exact (ParameterSpaceExtension.measurable_eval AS (separableClosure K L) _).pow_const _
    exact hmeas.comap_le

/-- Formula (3.14): the logarithmic integrals against `ν_{K'}` of `a ∈ L` and of its power
`a^q ∈ K'`, `q = [L : K']` the inseparable degree, are proportional with ratio `q⁻¹`. -/
theorem integral_log_eq_inv_finInsepDegree_mul (a : L) :
    ∫ x, Real.log (ϕ AS L x a) ∂measure AS L =
      (Field.finInsepDegree K L : ℝ)⁻¹ *
        ∫ x, Real.log (ParameterSpaceExtension.ϕ x
          ⟨a ^ Field.finInsepDegree K L,
            pow_finInsepDegree_mem_separableClosure K a⟩) ∂measure AS L := by
  simp_rw [ϕ, log_extendAbsoluteValue]
  exact integral_const_mul _ _

/-- The closing remark of Definition 3.4.1 together with Theorem 3.3.7(5): the finite
(possibly inseparable) extension of a proper adelic curve is proper. -/
theorem isProper_finiteExtension [AS.IsProper] :
    (AS.finiteExtension L).IsProper := by
  let : (AS.finiteSeparableExtension (separableClosure K L)).IsProper :=
    ParameterSpaceExtension.isProper_finiteSeparableExtension AS (separableClosure K L)
  constructor
  change ∀ a : L, a ≠ 0 → ∫ x, Real.log (ϕ AS L x a) ∂measure AS L = 0
  intro a ha
  rw [integral_log_eq_inv_finInsepDegree_mul]
  have hzero := AdelicStructure.IsProper.product_formula
    (AS := AS.finiteSeparableExtension (separableClosure K L))
    ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩
    (fun h ↦ pow_ne_zero _ ha (congrArg Subtype.val h))
  change ∫ x, Real.log (ParameterSpaceExtension.ϕ x
    ⟨a ^ Field.finInsepDegree K L, pow_finInsepDegree_mem_separableClosure K a⟩)
    ∂measure AS L = 0 at hzero
  rw [hzero, mul_zero]

/-- Chen--Moriwaki, Lemma 3.4.2: for a finite extension `L/K` and an absolute value `w` on
`L`, the completion of the separable closure `K^sc` of `K` in `L` at `w` identifies, inside
the completion `L_w`, with the separable closure of the completion `K_v` (`v = w|_K`). -/
theorem fieldRange_completion_separableClosure (w : AbsoluteValue L ℝ) :
    (algebraMap (w.under (separableClosure K L)).Completion w.Completion).fieldRange =
      (separableClosure (w.under K).Completion w.Completion).toSubfield := by
  let E := separableClosure K L
  let B := (w.under K).Completion
  let D := (w.under E).Completion
  let : Algebra B D := (normedAlgebraCompletion (w.under E) K).toAlgebra
  have : Algebra.IsSeparable B D := isSeparable_completion (w.under E)
  have : IsScalarTower B D w.Completion := isScalarTower_completion_restriction w E
  let p := ringExpChar w.Completion
  let : ExpChar E p := (algebraMap E w.Completion).expChar
    (algebraMap E w.Completion).injective p
  let : ExpChar D p := (algebraMap D w.Completion).expChar
    (algebraMap D w.Completion).injective p
  have hcoe (y : L) :
      (WithAbs.toAbs w y : w.Completion) ∈ Subalgebra.perfectClosure D w.Completion p := by
    obtain ⟨n, e, he⟩ := IsPurelyInseparable.pow_mem E p y
    apply Subalgebra.mem_perfectClosure_iff.mpr
    refine ⟨n, (WithAbs.toAbs (w.under E) e : D), ?_⟩
    change algebraMap (w.under E).Completion w.Completion
      (WithAbs.toAbs (w.under E) e : (w.under E).Completion) =
        (WithAbs.toAbs w y : w.Completion) ^ p ^ n
    rw [AbsoluteValue.Completion.algebraMap_eq, UniformSpace.Completion.mapRingHom_coe]
    change (WithAbs.toAbs w (algebraMap E L e) : w.Completion) = _
    rw [he]
    change UniformSpace.Completion.coeRingHom _ = _
    exact map_pow UniformSpace.Completion.coeRingHom _ _
  have hp : IsPurelyInseparable D w.Completion := by
    apply (isPurelyInseparable_iff_pow_mem D p).mpr
    intro x
    have hspan : Submodule.span D
        (Set.range fun i ↦ (WithAbs.toAbs w (Module.finBasis E L i) : w.Completion)) ≤
        (Subalgebra.perfectClosure D w.Completion p).toSubmodule := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hcoe _
    rw [span_coe_basis_eq_top w E (Module.finBasis E L)] at hspan
    exact Subalgebra.mem_perfectClosure_iff.mp
      (show x ∈ Subalgebra.perfectClosure D w.Completion p from
        hspan (Submodule.mem_top))
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    apply mem_separableClosure_iff.mpr
    exact (Algebra.IsSeparable.isSeparable B d).map
      (IsScalarTower.toAlgHom B D w.Completion)
      (IsScalarTower.toAlgHom B D w.Completion).injective
  · intro hx
    exact IsPurelyInseparable.inseparable D x
      ((mem_separableClosure_iff.mp hx).tower_top D)

/-- Chen--Moriwaki, Remark 3.4.3: under the canonical bijection `M_{K'} ≃ M_L`, the fibre
weights of the finite extension `L/K` are the ratios of separable degrees
`[L_x : K_ω]_s / [L : K]_s`, computed here on the completions. -/
theorem fibreWeight_eq_finSepDegree (ω : AS.Ω)
    (x : ExtensionFiber AS (separableClosure K L) ω) :
    ParameterSpaceExtension.fibreWeight AS (separableClosure K L) ω x =
      (Field.finSepDegree ((ϕ AS L x.1).under K).Completion
          (ϕ AS L x.1).Completion : ℝ≥0∞) /
        (Field.finSepDegree K L : ℝ≥0∞) := by
  let w := ϕ AS L x.1
  have hd : (w.under (separableClosure K L)).localDegree K =
      Field.finSepDegree (w.under K).Completion w.Completion := by
    let E := separableClosure K L
    let B := (w.under K).Completion
    let D := (w.under E).Completion
    let : Algebra B D := (normedAlgebraCompletion (w.under E) K).toAlgebra
    have : IsScalarTower B D w.Completion := isScalarTower_completion_restriction w E
    let f := IsScalarTower.toAlgHom B D w.Completion
    have hf : f.range = (separableClosure B w.Completion).toSubalgebra := by
      ext y
      exact congrArg (fun S : Subfield w.Completion ↦ y ∈ S)
        (fieldRange_completion_separableClosure L w) |>.to_iff
    have hdim := (AlgEquiv.ofInjectiveField f).toLinearEquiv.finrank_eq
    rw [hf] at hdim
    have : FiniteDimensional B w.Completion := finiteDimensional_completion w K
    have hs := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic B
      (separableClosure B w.Completion) w.Completion
    simp only [IsPurelyInseparable.finSepDegree_eq_one, mul_one,
      Field.finSepDegree_eq_finrank_of_isSeparable] at hs
    exact hdim.trans hs
  simp only [w, ϕ, restriction_extendAbsoluteValue] at hd
  have hg := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K (separableClosure K L) L
  simp only [IsPurelyInseparable.finSepDegree_eq_one, mul_one,
    Field.finSepDegree_eq_finrank_of_isSeparable] at hg
  rw [ParameterSpaceExtension.fibreWeight, hd, hg]
  rfl

end ParameterSpaceFinExtension

end ArakelovGeometry.AdelicStructure
