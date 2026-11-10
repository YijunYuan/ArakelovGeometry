/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicDivisor.Principal
public import ArakelovGeometry.AdelicVectorBundle.Line

/-!
# Divisors and degrees of nonzero rational vectors

Source Definition 4.3.1 uses actual `L¹` classes of negative logarithmic
norms. The negative sign agrees with the source degree formula and corrects
its inconsistent descriptive sentence. Properness is needed only for scalar
invariance of degree, not for the divisor construction or its transformation law.
-/

@[expose] public section

open MeasureTheory Filter

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E) (hd : ξ.IsDominated) (hm : ξ.IsMeasurable)

/-- The vector divisor is the actual integrable class of its negative logarithmic norm.
Its domain consists precisely of nonzero rational vectors. -/
noncomputable def vectorDivisor (s : {x : E // x ≠ 0}) : AdelicDivisor S :=
  AdelicDivisor.ofIntegrable S (fun ω ↦ -ξ.logNorm s.val ω)
    (hd.integrable_logNorm hm s.val).neg

/-- The exact almost-everywhere representative of a vector divisor. -/
theorem coeFn_vectorDivisor (s : {x : E // x ≠ 0}) :
    vectorDivisor ξ hd hm s =ᵐ[S.v] fun ω ↦ -ξ.logNorm s.val ω :=
  (hd.integrable_logNorm hm s.val).neg.coeFn_toL1

/-- The degree of a nonzero vector is the degree of its actual adelic divisor. -/
noncomputable def vectorDegree (s : {x : E // x ≠ 0}) : ℝ :=
  AdelicDivisor.degree S (vectorDivisor ξ hd hm s)

/-- The vector degree is the negative integral of the logarithmic norm. -/
theorem vectorDegree_eq_neg_integral (s : {x : E // x ≠ 0}) :
    vectorDegree ξ hd hm s = -(∫ ω, ξ.logNorm s.val ω ∂S.v) := by
  rw [vectorDegree, vectorDivisor, AdelicDivisor.degree_ofIntegrable, integral_neg]

/-- Multiplication by a field unit adds its genuine principal divisor. -/
theorem vectorDivisor_smul (a : Kˣ) (s : {x : E // x ≠ 0}) :
    vectorDivisor ξ hd hm ⟨(a : K) • s.val, smul_ne_zero a.ne_zero s.property⟩ =
      vectorDivisor ξ hd hm s + AdelicDivisor.principal S a := by
  apply Lp.ext
  filter_upwards [coeFn_vectorDivisor ξ hd hm
    ⟨(a : K) • s.val, smul_ne_zero a.ne_zero s.property⟩,
    coeFn_vectorDivisor ξ hd hm s, AdelicDivisor.coeFn_principal S a,
    Lp.coeFn_add (vectorDivisor ξ hd hm s) (AdelicDivisor.principal S a)]
    with ω hsm hs ha hadd
  rw [hadd, Pi.add_apply, hsm, hs, ha]
  change -ξ.logNorm ((a : K) • s.val) ω = -ξ.logNorm s.val ω - Real.log (S.ϕ ω (a : K))
  rw [ξ.logNorm_smul a.ne_zero s.property]
  ring

/-- The degree transformation law before imposing the product formula. -/
theorem vectorDegree_smul (a : Kˣ) (s : {x : E // x ≠ 0}) :
    vectorDegree ξ hd hm ⟨(a : K) • s.val, smul_ne_zero a.ne_zero s.property⟩ =
      vectorDegree ξ hd hm s + AdelicDivisor.degree S (AdelicDivisor.principal S a) := by
  simp only [vectorDegree, vectorDivisor_smul, map_add]

/-- Properness makes vector degree invariant under multiplication by a nonzero scalar. -/
theorem vectorDegree_smul_of_proper [S.IsProper] (a : Kˣ) (s : {x : E // x ≠ 0}) :
    vectorDegree ξ hd hm ⟨(a : K) • s.val, smul_ne_zero a.ne_zero s.property⟩ =
      vectorDegree ξ hd hm s := by
  rw [vectorDegree_smul, AdelicDivisor.degree_principal_eq_zero, add_zero]

/-- On a line over a proper curve the vector degree is independent of its generator. -/
theorem vectorDegree_eq_of_finrank_one [S.IsProper] (hr : Module.finrank K E = 1)
    (s t : {x : E // x ≠ 0}) : vectorDegree ξ hd hm s = vectorDegree ξ hd hm t := by
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one hr s.property t.val
  have ha0 : a ≠ 0 := by
    intro hz
    apply t.property
    simpa only [hz, zero_smul] using ha.symm
  let u : Kˣ := Units.mk0 a ha0
  have ht : (⟨(u : K) • s.val, smul_ne_zero u.ne_zero s.property⟩ : {x : E // x ≠ 0}) = t :=
    Subtype.ext ha
  simpa only [ht] using (vectorDegree_smul_of_proper ξ hd hm u s).symm

end ArakelovGeometry.NormFamily
