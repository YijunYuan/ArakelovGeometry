/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Comparison
public import ArakelovGeometry.MeasureTheory.Integral.Envelope

import ArakelovGeometry.AdelicVectorBundle.Dual.Bidual
import ArakelovGeometry.AdelicVectorBundle.Dual.Map
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Domination of norm families

Upper and lower domination concern integrable envelopes of rational-vector
logarithmic norms, without assuming measurability of the norm family.
Domination requires upper domination of both the family and its actual dual
(Chen–Moriwaki, Definitions 4.1.1–2 and Remark 4.1.3, PDF page 225).
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]

/-- The logarithmic norm of a rational vector, evaluated in each actual completed fibre.
Domination conditions below concern nonzero rational vectors only. -/
noncomputable def logNorm (ξ : NormFamily S E) (x : E) (ω : S.Ω) : ℝ :=
  Real.log (ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x))

/-- Rational vectors embed injectively in each completed fibre. -/
theorem rational_tmul_injective (ω : S.Ω) :
    Function.Injective (fun x : E ↦ (1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective E

/-- Every nonzero rational vector has positive completed-fibre norm. -/
theorem norm_rational_pos (ξ : NormFamily S E) (ω : S.Ω) {x : E} (hx : x ≠ 0) :
    0 < ξ.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) := by
  apply ξ.norm_pos
  intro h
  apply hx
  apply rational_tmul_injective ω
  simpa using h

/-- Each nonzero rational vector has an integrable majorant for its logarithmic norm. -/
class IsUpperDominated (ξ : NormFamily S E) : Prop where
  /-- The defining property. -/
  logNorm_upperBound :
    ∀ x : E, x ≠ 0 → HasIntegrableUpperBound (ξ.logNorm x) S.v

instance (ξ : NormFamily S E) : CoeFun (ξ.IsUpperDominated)
    (fun _ ↦
      ∀ x : E, x ≠ 0 → HasIntegrableUpperBound (ξ.logNorm x) S.v) :=
  ⟨fun h ↦ h.logNorm_upperBound⟩

/-- The defining proposition of `IsUpperDominated`. -/
theorem IsUpperDominated.iff (ξ : NormFamily S E) :
    ξ.IsUpperDominated ↔
    ∀ x : E, x ≠ 0 → HasIntegrableUpperBound (ξ.logNorm x) S.v :=
  ⟨fun h ↦ h.logNorm_upperBound, fun h ↦ ⟨h⟩⟩

/-- Each nonzero rational vector has an integrable minorant for its logarithmic norm. -/
class IsLowerDominated (ξ : NormFamily S E) : Prop where
  /-- The defining property. -/
  logNorm_lowerBound :
    ∀ x : E, x ≠ 0 → HasIntegrableLowerBound (ξ.logNorm x) S.v

instance (ξ : NormFamily S E) : CoeFun (ξ.IsLowerDominated)
    (fun _ ↦
      ∀ x : E, x ≠ 0 → HasIntegrableLowerBound (ξ.logNorm x) S.v) :=
  ⟨fun h ↦ h.logNorm_lowerBound⟩

/-- The defining proposition of `IsLowerDominated`. -/
theorem IsLowerDominated.iff (ξ : NormFamily S E) :
    ξ.IsLowerDominated ↔
    ∀ x : E, x ≠ 0 → HasIntegrableLowerBound (ξ.logNorm x) S.v :=
  ⟨fun h ↦ h.logNorm_lowerBound, fun h ↦ ⟨h⟩⟩

theorem isUpperDominated_iff_upperIntegral (ξ : NormFamily S E) :
    ξ.IsUpperDominated ↔ ∀ x : E, x ≠ 0 →
      upperEnvelopeIntegral (ξ.logNorm x) S.v < ⊤ := by
  simp only [IsUpperDominated.iff, hasIntegrableUpperBound_iff_upperEnvelopeIntegral_lt_top]

theorem isLowerDominated_iff_lowerIntegral (ξ : NormFamily S E) :
    ξ.IsLowerDominated ↔ ∀ x : E, x ≠ 0 →
      ⊥ < lowerEnvelopeIntegral (ξ.logNorm x) S.v := by
  simp only [IsLowerDominated.iff, hasIntegrableLowerBound_iff_bot_lt_lowerEnvelopeIntegral]

theorem isUpperDominated_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsUpperDominated := ⟨fun x hx ↦ (hx (Subsingleton.elim x 0)).elim⟩

theorem isLowerDominated_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsLowerDominated := ⟨fun x hx ↦ (hx (Subsingleton.elim x 0)).elim⟩

theorem IsUpperDominated.mono {ξ η : NormFamily S E} (hη : η.IsUpperDominated)
    (hξη : ξ ≤ η) : ξ.IsUpperDominated := by
  constructor
  intro x hx
  apply (hη x hx).mono
  exact Eventually.of_forall fun ω ↦ Real.log_le_log (ξ.norm_rational_pos ω hx) (hξη ω _)

theorem IsLowerDominated.mono {ξ η : NormFamily S E} (hξ : ξ.IsLowerDominated)
    (hξη : ξ ≤ η) : η.IsLowerDominated := by
  constructor
  intro x hx
  apply (hξ x hx).mono
  exact Eventually.of_forall fun ω ↦ Real.log_le_log (ξ.norm_rational_pos ω hx) (hξη ω _)

variable [FiniteDimensional K E]

/-- Source domination requires upper domination of the family and of its dual. -/
class IsDominated (ξ : NormFamily S E) : Prop where
  /-- Upper domination of the family. -/
  upper : ξ.IsUpperDominated
  /-- Upper domination of the completed dual. -/
  dual_upper : ξ.dual.IsUpperDominated

attribute [instance] IsDominated.upper IsDominated.dual_upper

/-- The two components of domination. -/
theorem isDominated_iff (ξ : NormFamily S E) :
    ξ.IsDominated ↔ ξ.IsUpperDominated ∧ ξ.dual.IsUpperDominated :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Evaluation equal to one yields a lower bound on the sum of logarithmic norms. -/
theorem logNorm_add_dual_logNorm_nonneg (ξ : NormFamily S E) {x : E}
    {ℓ : Module.Dual K E} (he : ℓ x = 1) (ω : S.Ω) :
    0 ≤ ξ.logNorm x ω + ξ.dual.logNorm ℓ ω := by
  have hx : x ≠ 0 := by rintro rfl; simp at he
  have hℓ : ℓ ≠ 0 := by rintro rfl; simp at he
  have heval := ξ.norm_dual_tmul_apply_tmul_le ω 1 1 ℓ x
  simp only [he, map_one, mul_one, norm_one] at heval
  have hp := ξ.norm_rational_pos ω hx
  have hq := ξ.dual.norm_rational_pos ω hℓ
  have hlog := Real.log_le_log zero_lt_one heval
  rw [Real.log_one, Real.log_mul hq.ne' hp.ne'] at hlog
  simpa only [logNorm, add_comm] using hlog

/-- Upper domination of the dual provides lower envelopes for the original family. -/
theorem IsUpperDominated.lower_of_dual {ξ : NormFamily S E}
    (h : ξ.dual.IsUpperDominated) : ξ.IsLowerDominated := by
  constructor
  intro x hx
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one K hx
  have hne : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  apply (h ℓ hne).neg.mono
  exact Eventually.of_forall fun ω ↦ by
    have := ξ.logNorm_add_dual_logNorm_nonneg hℓ ω
    linarith

/-- Upper domination provides lower envelopes for the dual family. -/
theorem IsUpperDominated.lower_dual {ξ : NormFamily S E}
    (h : ξ.IsUpperDominated) : ξ.dual.IsLowerDominated := by
  constructor
  intro ℓ hℓ
  obtain ⟨x, hx⟩ : ∃ x, ℓ x ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hℓ (LinearMap.ext hzero)
  let y := (ℓ x)⁻¹ • x
  have he : ℓ y = 1 := by simp [y, hx]
  have hy : y ≠ 0 := by rintro hz; simp [hz] at he
  apply (h y hy).neg.mono
  exact Eventually.of_forall fun ω ↦ by
    have := ξ.logNorm_add_dual_logNorm_nonneg he ω
    linarith

theorem IsDominated.lower {ξ : NormFamily S E} (h : ξ.IsDominated) :
    ξ.IsLowerDominated := h.2.lower_of_dual

theorem IsDominated.lower_dual {ξ : NormFamily S E} (h : ξ.IsDominated) :
    ξ.dual.IsLowerDominated := h.1.lower_dual

/-- Domination gives two integrable envelopes for each rational log norm. -/
theorem IsDominated.logNorm_bounds {ξ : NormFamily S E} (h : ξ.IsDominated)
    {x : E} (hx : x ≠ 0) : HasIntegrableBounds (ξ.logNorm x) S.v :=
  ⟨h.1 x hx, h.lower x hx⟩

/-- Domination holds for the unique norm family in dimension zero. -/
theorem isDominated_of_subsingleton [Subsingleton E] (ξ : NormFamily S E) :
    ξ.IsDominated :=
  ⟨isUpperDominated_of_subsingleton ξ, isUpperDominated_of_subsingleton ξ.dual⟩

/-- The canonical bidual contraction transfers upper envelopes to the bidual. -/
theorem IsUpperDominated.bidual {ξ : NormFamily S E} (h : ξ.IsUpperDominated) :
    ξ.dual.dual.IsUpperDominated := by
  constructor
  intro Φ hΦ
  obtain ⟨x, rfl⟩ := (Module.evalEquiv K E).surjective Φ
  have hx : x ≠ 0 := by rintro rfl; simp at hΦ
  apply (h x hx).mono
  apply Eventually.of_forall
  intro ω
  apply Real.log_le_log (ξ.dual.dual.norm_rational_pos ω hΦ)
  simpa only [LinearMap.baseChange_tmul, Module.evalEquiv_apply] using
    ξ.dual_dual_norm_eval_le ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)

/-- Domination is preserved by duality, without any bidual-isometry hypothesis. -/
theorem IsDominated.dual {ξ : NormFamily S E} (h : ξ.IsDominated) :
    ξ.dual.IsDominated := ⟨h.2, h.1.bidual⟩

variable {F : Type*} [AddCommGroup F] [Module K F]

omit [FiniteDimensional K E] in
/-- Pullback of upper domination along an injective rational map. -/
theorem IsUpperDominated.pullback {ξ : NormFamily S E} (h : ξ.IsUpperDominated)
    (f : F →ₗ[K] E) (hf : Function.Injective f) : (ξ.pullback f hf).IsUpperDominated := by
  constructor
  intro x hx
  convert h (f x) ((f.map_eq_zero_iff hf).not.mpr hx) using 1
  ext ω
  rfl

omit [FiniteDimensional K E] in
/-- Restriction preserves upper domination. -/
theorem IsUpperDominated.restrict {ξ : NormFamily S E} (h : ξ.IsUpperDominated)
    (F : Submodule K E) : (ξ.restrict F).IsUpperDominated :=
  h.pullback F.subtype F.subtype_injective

/-- Upper envelopes descend to an actual completed quotient norm. -/
theorem IsUpperDominated.pushforward {ξ : NormFamily S E} (h : ξ.IsUpperDominated)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).IsUpperDominated := by
  constructor
  intro y hy
  obtain ⟨x, rfl⟩ := hπ y
  have hx : x ≠ 0 := by rintro rfl; simp at hy
  apply (h x hx).mono
  apply Eventually.of_forall
  intro ω
  apply Real.log_le_log ((ξ.pushforward π hπ).norm_rational_pos ω hy)
  simpa only [LinearMap.baseChange_tmul] using
    ξ.pushforward_norm_le π hπ ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)

/-- Quotient by a subspace preserves upper domination. -/
theorem IsUpperDominated.quotient {ξ : NormFamily S E} (h : ξ.IsUpperDominated)
    (F : Submodule K E) : (ξ.quotient F).IsUpperDominated :=
  h.pushforward F.mkQ F.mkQ_surjective

/-- Under the source's Archimedean normalization, ultrametric biduality
reflects domination from the dual. -/
theorem IsDominated.of_dual {ξ : NormFamily S E} (h : ξ.dual.IsDominated)
    (hξ : ξ.IsUltrametric)
    [hS : S.IsArchimedeanNormalized] :
    ξ.IsDominated := by
  refine ⟨?_, h.1⟩
  have hb := h.2.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)
  rwa [ξ.dual_dual_pullback_eq] at hb

/-- Source Remark 4.1.3, with the usual Archimedean normalization explicit. -/
theorem isDominated_dual_iff {ξ : NormFamily S E} [hξ : ξ.IsUltrametric]
    [hS : S.IsArchimedeanNormalized] :
    ξ.dual.IsDominated ↔ ξ.IsDominated :=
  ⟨fun h ↦ h.of_dual hξ, IsDominated.dual⟩

/-- An upper integrable envelope for the local distance transfers upper domination. -/
theorem IsUpperDominated.of_localDist {ξ η : NormFamily S E} (hξ : ξ.IsUpperDominated)
    (hd : HasIntegrableUpperBound (ξ.localDist η) S.v) : η.IsUpperDominated := by
  constructor
  intro x hx
  apply ((hξ x hx).add hd).mono
  apply Eventually.of_forall
  intro ω
  have hb := ξ.log_norm_sub_le_localDist η ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)
  have hl := (abs_le.mp hb).1
  change η.logNorm x ω ≤ ξ.logNorm x ω + ξ.localDist η ω
  dsimp only [logNorm]
  linarith

/-- Domination passes across a distance with an integrable upper envelope.
Since local distance is nonnegative, this is equivalent to its domination. -/
theorem IsDominated.of_localDist {ξ η : NormFamily S E} (hξ : ξ.IsDominated)
    (hd : HasIntegrableUpperBound (ξ.localDist η) S.v) : η.IsDominated := by
  refine ⟨hξ.1.of_localDist hd, hξ.2.of_localDist ?_⟩
  exact hd.mono (Eventually.of_forall fun ω ↦ ξ.localDist_dual_le η ω)

/-- The main implication of source Proposition 4.1.6. -/
theorem IsDominated.of_localDist_bounds {ξ η : NormFamily S E} (hξ : ξ.IsDominated)
    (hd : HasIntegrableBounds (ξ.localDist η) S.v) : η.IsDominated :=
  hξ.of_localDist hd.1

variable [FiniteDimensional K F]

/-- Every algebraic extension of a subspace functional supplies an upper
envelope for its restricted dual norm. -/
theorem IsDominated.pullback {ξ : NormFamily S E} (h : ξ.IsDominated)
    (f : F →ₗ[K] E) (hf : Function.Injective f) : (ξ.pullback f hf).IsDominated := by
  refine ⟨h.1.pullback f hf, ⟨?_⟩⟩
  intro ℓ hℓ
  obtain ⟨m, rfl⟩ := LinearMap.dualMap_surjective_of_injective hf ℓ
  have hm : m ≠ 0 := by rintro rfl; simp at hℓ
  apply (h.2 m hm).mono
  apply Eventually.of_forall
  intro ω
  apply Real.log_le_log ((ξ.pullback f hf).dual.norm_rational_pos ω hℓ)
  simpa only [LinearMap.baseChange_tmul] using
    ξ.pullback_dual_norm_le f hf ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] m)

/-- Subspace restriction preserves source domination. -/
theorem IsDominated.restrict {ξ : NormFamily S E} (h : ξ.IsDominated)
    (F : Submodule K E) : (ξ.restrict F).IsDominated :=
  h.pullback F.subtype F.subtype_injective

/-- A quotient is dominated because its dual is the actual restriction of
the ambient dual along the injective transpose. -/
theorem IsDominated.pushforward {ξ : NormFamily S E} (h : ξ.IsDominated)
    (π : E →ₗ[K] F) (hπ : Function.Surjective π) :
    (ξ.pushforward π hπ).IsDominated := by
  refine ⟨h.1.pushforward π hπ, ?_⟩
  rw [ξ.pushforward_dual π hπ]
  exact h.2.pullback π.dualMap (LinearMap.dualMap_injective_of_surjective hπ)

/-- Quotient by any subspace preserves source domination. -/
theorem IsDominated.quotient {ξ : NormFamily S E} (h : ξ.IsDominated)
    (F : Submodule K E) : (ξ.quotient F).IsDominated :=
  h.pushforward F.mkQ F.mkQ_surjective

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

variable [FiniteDimensional K E]

instance instIsDominatedDual {ξ : NormFamily S E} [hξ : ξ.IsDominated] :
    ξ.dual.IsDominated := hξ.dual

instance instIsDominatedRestrict {ξ : NormFamily S E} [hξ : ξ.IsDominated]
    (P : Submodule K E) : (ξ.restrict P).IsDominated := hξ.restrict P

instance instIsDominatedQuotient {ξ : NormFamily S E} [hξ : ξ.IsDominated]
    (P : Submodule K E) : (ξ.quotient P).IsDominated := hξ.quotient P

variable [FiniteDimensional K F]

instance instIsDominatedPullback {ξ : NormFamily S E} [hξ : ξ.IsDominated]
    (f : F →ₗ[K] E) (hf : Function.Injective f) : (ξ.pullback f hf).IsDominated :=
  hξ.pullback f hf

instance instIsDominatedPushforward {ξ : NormFamily S E} [hξ : ξ.IsDominated]
    (f : E →ₗ[K] F) (hf : Function.Surjective f) : (ξ.pushforward f hf).IsDominated :=
  hξ.pushforward f hf

end ArakelovGeometry.NormFamily

namespace ArakelovGeometry.NormFamily
attribute [instance] isUpperDominated_of_subsingleton isLowerDominated_of_subsingleton
    isDominated_of_subsingleton
end ArakelovGeometry.NormFamily
