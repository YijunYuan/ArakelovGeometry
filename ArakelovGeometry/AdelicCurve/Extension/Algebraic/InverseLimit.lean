/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Basic

/-!
# Algebraic fibres as inverse limits

The actual absolute-value fibre is homeomorphic to the closed subspace of
compatible finite-stage families, as in Chen–Moriwaki, Proposition 3.4.6.
-/

namespace ArakelovGeometry.AdelicStructure.Algebraic
open MeasureTheory
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (AS : AdelicStructure K) [Algebra.IsAlgebraic K L] (ω : AS.Ω)

/-- The compatible families in the product of all finite-stage fibres. -/
def compatibleFibreFamilies :
    Set (∀ F : FiniteIntermediateField K L, FiniteBaseFiber L F ω) :=
  {x | ∀ (F G : FiniteIntermediateField K L) (hFG : F.1 ≤ G.1),
    projFiniteFiberOfLE hFG ω (x G) = x F}

omit [Algebra.IsAlgebraic K L] in
/-- Compatibility is a closed condition in the product of finite discrete fibres. -/
theorem isClosed_compatibleFibreFamilies : IsClosed (compatibleFibreFamilies (L := L) AS ω) := by
  unfold compatibleFibreFamilies
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro F
  apply isClosed_iInter
  intro G
  apply isClosed_iInter
  intro hFG
  let := ParameterSpaceExtension.finite_extensionFiber AS (separableClosure K G.1) ω
  exact isClosed_eq ((continuous_of_discreteTopology :
    Continuous (projFiniteFiberOfLE hFG ω)).comp (continuous_apply G)) (continuous_apply F)

/-- An actual extending absolute value determines a compatible family of finite restrictions. -/
def fibreToInverseLimit (x : BaseFiber L ω) : compatibleFibreFamilies (L := L) AS ω :=
  ⟨fun F ↦ projFiniteFiber F ω x, fun _ _ hFG ↦ projFiniteFiberOfLE_projFiniteFiber hFG ω x⟩

omit [Algebra.IsAlgebraic K L] in
/-- The finite restrictions vary continuously in the evaluation topology. -/
theorem continuous_fibreToInverseLimit : Continuous (fibreToInverseLimit (L := L) AS ω) :=
  (continuous_pi fun F ↦ continuous_projFiniteFiber AS L F ω).subtype_mk _

/-- All finite restrictions together determine an extending absolute value. -/
theorem injective_fibreToInverseLimit : Function.Injective (fibreToInverseLimit (L := L) AS ω) := by
  intro x y hxy
  apply Subtype.ext
  apply ParameterSpaceExtension.ext AS L (x.property.trans y.property.symm)
  ext a
  let F := ofElement (K := K) L a
  let b : F := ⟨a, mem_ofElement L a⟩
  have hF : projFiniteFiber F ω x = projFiniteFiber F ω y :=
    congrFun (congrArg Subtype.val hxy) F
  have h := congrArg (fun z : FiniteBaseFiber L F ω ↦
    ParameterSpaceFinExtension.ϕ AS F z.val b) hF
  change ParameterSpaceFinExtension.extendAbsoluteValue
    ((x.val.abv.restriction F).restriction (separableClosure K F)) b =
      ParameterSpaceFinExtension.extendAbsoluteValue
        ((y.val.abv.restriction F).restriction (separableClosure K F)) b at h
  rw [ParameterSpaceFinExtension.extendAbsoluteValue_restriction,
    ParameterSpaceFinExtension.extendAbsoluteValue_restriction] at h
  exact h

/-- Every compatible family is realized by an actual absolute value on the full extension. -/
theorem surjective_fibreToInverseLimit :
    Function.Surjective (fibreToInverseLimit (L := L) AS ω) := by
  intro y
  let t (F : FiniteIntermediateField K L) : Set (BaseFiber L ω) :=
    projFiniteFiber F ω ⁻¹' {y.val F}
  have hc (F) : IsClosed (t F) :=
    isClosed_singleton.preimage (continuous_projFiniteFiber AS L F ω)
  have hmono {F G : FiniteIntermediateField K L} (hFG : F.1 ≤ G.1) : t G ⊆ t F := by
    intro x hx
    change projFiniteFiber G ω x = y.val G at hx
    change projFiniteFiber F ω x = y.val F
    rw [← projFiniteFiberOfLE_projFiniteFiber hFG ω x, hx]
    exact y.property F G hFG
  have hd : Directed (· ⊇ ·) t := by
    intro F G
    exact ⟨FiniteIntermediateField.sup F G,
      hmono (FiniteIntermediateField.left_le_sup F G),
      hmono (FiniteIntermediateField.right_le_sup F G)⟩
  have hn (F) : (t F).Nonempty := by
    obtain ⟨x,hx⟩ := surjective_projFiniteFiber AS L F ω (y.val F)
    exact ⟨x,hx⟩
  let : Nonempty (FiniteIntermediateField K L) := ⟨FiniteIntermediateField.bot⟩
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hd hn (fun F ↦ (hc F).isCompact) hc
  refine ⟨x, Subtype.ext ?_⟩
  funext F
  exact Set.mem_iInter.mp hx F

/-- The actual fibre is homeomorphic to the closed space of compatible finite-stage families. -/
noncomputable def fibreInverseLimitHomeomorph :
    BaseFiber L ω ≃ₜ compatibleFibreFamilies (L := L) AS ω := by
  let e := Equiv.ofBijective (fibreToInverseLimit (L := L) AS ω)
    ⟨injective_fibreToInverseLimit AS ω, surjective_fibreToInverseLimit AS ω⟩
  exact e.toHomeomorphOfContinuousClosed (continuous_fibreToInverseLimit AS ω)
    (continuous_fibreToInverseLimit AS ω).isClosedMap

end ArakelovGeometry.AdelicStructure.Algebraic
