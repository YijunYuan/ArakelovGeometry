/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Coherence.Criteria
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Full.Gauge
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.Gauge

import ArakelovGeometry.NumberTheory.NumberField.Lattice.Norm.GaugeDomination
import Mathlib.Topology.Sheaves.Init

/-!
# Coherent lattice replacement is the actual full-lattice model

The original completed-ball lattice replacement equals the full-lattice gauge
family of its literal finite global ball. Coherence supplies the full span;
finite generation permits the full-lattice constructor. No domination of the
original norm family is assumed, as in the final clause of the model
construction on Chen–Moriwaki PDF310, printed294.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct
noncomputable section

namespace ArakelovGeometry.NormFamily

open AdelicStructure ActualPrimeIndexing CompletedUnitBallGauge NumberFieldFullLattice

variable {K E : Type*} [Field K] [NumberField K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

set_option backward.isDefEq.respectTransparency false in
/-- The two actual gauge constructions agree on every completed fibre. -/
theorem HasFiniteNormExceptions.latticeGaugeFamily_eq_fullLatticeGaugeFamily
    (ξ : NormFamily (normalizedNumberFieldAdelicStructure K) E)
    (hξ : ξ.IsUltrametricAtFinitePlaces) (hc : ξ.HasFiniteNormExceptions)
    (hfg : (ξ.globalUnitBallModule).FG) :
    ξ.latticeGaugeFamily =
      fullLatticeGaugeFamily (ξ.globalUnitBallModule) hfg
        ((hasFiniteNormExceptions_iff_span_normalizedGlobalUnitBall_eq_top ξ).mp hc) ξ := by
  ext ω z
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    rw [ξ.latticeGaugeFamily_norm_finite _ (normalizedPrimeParameter_mem_fin p),
      fullLatticeGaugeFamily_norm_prime]
    unfold completedUnitBallGauge
    rw [← ξ.coe_completedUnitBallModule _ (normalizedPrimeParameter_mem_fin p),
      hc.completedUnitBallModule_eq_completedLatticeSpan ξ p]
  · rw [ξ.latticeGaugeFamily_norm_not_finite ω hω,
      fullLatticeGaugeFamily_norm_not_finite _ _ _ _ ω hω]

end ArakelovGeometry.NormFamily
