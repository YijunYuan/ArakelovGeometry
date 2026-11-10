/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.BasisNorm

/-!
# Comparison with a mixed basis norm

This module proves the base-field part of the domination criteria by comparing
the actual completed norms with the mixed basis family. Algebraic-extension
norms and their compatibility are separate constructions.
-/

@[expose] public section

open MeasureTheory Filter
open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι K E) (ξ : NormFamily S E)

/-- For a family ultrametric at finite places, a common bound on the completed
basis vectors bounds the norm by the source mixed coordinate norm. -/
theorem norm_le_mul_of_basis_norm_le (hξ : ξ.IsUltrametric) (ω : S.Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.norm ω ((b.baseChange (S.ϕ ω).Completion) i) ≤ C)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    ξ.norm ω x ≤ C * (ofBasisMixed S E b).norm ω x := by
  classical
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let B := b.baseChange (S.ϕ ω).Completion
  have he : x = ∑ i, B.equivFun x i • B i := (B.sum_equivFun x).symm
  by_cases hω : ω ∈ S.Ωinf
  · rw [ofBasisMixed_norm_of_infinite b ω hω]
    calc
      ξ.norm ω x = ‖∑ i, B.equivFun x i • B i‖ := congrArg (ξ.norm ω) he
      _ ≤ ∑ i, ‖B.equivFun x i • B i‖ := norm_sum_le _ _
      _ ≤ ∑ i, C * ‖B.equivFun x i‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [_root_.norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hb i) (_root_.norm_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    have : IsUltrametricDist ((S.ϕ ω).Completion ⊗[K] E) :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (hξ ω hf)
    rw [ofBasisMixed_norm_of_finite b ω hf, ofBasis_norm]
    calc
      ξ.norm ω x = ‖∑ i, B.equivFun x i • B i‖ := congrArg (ξ.norm ω) he
      _ ≤ C * ‖B.equivFun x‖ := by
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
          (mul_nonneg hC (_root_.norm_nonneg _))
        intro i _
        rw [_root_.norm_smul, mul_comm]
        exact mul_le_mul (hb i) (norm_le_pi_norm _ i) (_root_.norm_nonneg _) hC

variable [FiniteDimensional K E]

/-- A base-changed member of the rational dual basis extracts the actual
completed coordinate, also for completed vectors that are not rational. -/
theorem dualBaseChange_one_dualBasis_apply {ι' : Type*} [Finite ι'] [DecidableEq ι']
    (b : Module.Basis ι' K E) (ω : S.Ω)
    (i : ι') (x : (S.ϕ ω).Completion ⊗[K] E) :
    dualBaseChangeEquiv K (S.ϕ ω).Completion E
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) x =
      (b.baseChange (S.ϕ ω).Completion).equivFun x i := by
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
      simp only [dualBaseChangeEquiv_tmul_apply_tmul, mul_one,
        Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
        Module.Basis.dualBasis_apply, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Bounds on the actual dual basis norms control every completed coordinate. -/
theorem ofBasis_norm_le_mul_of_dual_basis_norm_le [DecidableEq ι] (ω : S.Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) ≤ C)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasis S E b).norm ω x ≤ C * ξ.norm ω x := by
  rw [ofBasis_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (ξ.norm_nonneg ω x))).mpr
  intro i
  rw [← dualBaseChange_one_dualBasis_apply b ω i x]
  exact (ξ.norm_dual_apply_le ω _ x).trans
    (mul_le_mul_of_nonneg_right (hb i) (ξ.norm_nonneg ω x))

/-- Dual basis bounds control the mixed norm, with a rank factor only on the
infinite locus. No ultrametricity of the original family is assumed. -/
theorem ofBasisMixed_norm_le_mul_of_dual_basis_norm_le [DecidableEq ι] (ω : S.Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ξ.dual.norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) ≤ C)
    (x : (S.ϕ ω).Completion ⊗[K] E) :
    (ofBasisMixed S E b).norm ω x ≤
      Real.exp (S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ)) ω) *
        C * ξ.norm ω x := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · rw [Set.indicator_of_mem hω, mul_assoc]
    exact (ofBasisMixed_norm_le_exp_log_card_mul b ω x).trans
      (mul_le_mul_of_nonneg_left (ofBasis_norm_le_mul_of_dual_basis_norm_le b ξ ω hC hb x)
        (Real.exp_pos _).le)
  · rw [Set.indicator_of_notMem hω, Real.exp_zero, one_mul,
      ofBasisMixed_norm_of_finite b ω (not_not.mp hω)]
    exact ofBasis_norm_le_mul_of_dual_basis_norm_le b ξ ω hC hb x

omit [FiniteDimensional K E] in
/-- Upper domination yields one nonnegative integrable function controlling
all basis vectors almost everywhere. The bound is a finite sum of the
absolute values of independently supplied scalar envelopes. -/
theorem IsUpperDominated.exists_basis_norm_bound {ι' : Type*} [Finite ι']
    (b : Module.Basis ι' K E) (hξ : ξ.IsUpperDominated) :
    ∃ A : S.Ω → ℝ, Integrable A S.v ∧ (∀ ω, 0 ≤ A ω) ∧
      ∀ᵐ ω ∂S.v, ∀ i,
        ξ.norm ω ((b.baseChange (S.ϕ ω).Completion) i) ≤ Real.exp (A ω) := by
  classical
  let := Fintype.ofFinite ι'
  choose A hA hbound using fun i => hξ (b i) (b.ne_zero i)
  refine ⟨fun ω => ∑ i, |A i ω|,
    integrable_finsetSum _ (fun i _ => (hA i).abs),
    fun ω => Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  intro i
  rw [Module.Basis.baseChange_apply]
  apply (Real.log_le_iff_le_exp (ξ.norm_rational_pos ω (b.ne_zero i))).mp
  exact (hω i).trans ((le_abs_self _).trans (Finset.single_le_sum
    (f := fun j => |A j ω|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))

/-- A dominated family that is ultrametric at finite places has an integrably
bounded distance from every mixed basis norm. The proof uses the actual
primal and dual basis norms, not measurability of the original family. -/
theorem IsDominated.localDist_ofBasisMixed_of_ultrametric (hd : ξ.IsDominated)
    (hu : ξ.IsUltrametric) (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v := by
  classical
  obtain ⟨A, hA, hA0, hAb⟩ :=
    IsUpperDominated.exists_basis_norm_bound (ξ := ξ) b hd.1
  obtain ⟨B, hB, hB0, hBb⟩ :=
    IsUpperDominated.exists_basis_norm_bound (ξ := ξ.dual) b.dualBasis hd.2
  let R := S.Ωinf.indicator (fun _ => Real.log (Fintype.card ι : ℝ))
  have hR : Integrable R S.v :=
    (integrable_indicator_iff S.measurableSet_Ωinf).mpr (integrableOn_const hfin.ne)
  have hR0 : ∀ ω, 0 ≤ R ω := Set.indicator_nonneg (fun _ _ => Real.log_natCast_nonneg _)
  refine ⟨⟨fun ω => A ω + B ω + R ω, (hA.add hB).add hR, ?_⟩,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg _)⟩⟩
  filter_upwards [hAb, hBb] with ω ha hb
  apply (ξ.localDist_le_iff_norm_le (ofBasisMixed S E b) ω
    (add_nonneg (add_nonneg (hA0 ω) (hB0 ω)) (hR0 ω))).mpr
  intro x
  constructor
  · exact (norm_le_mul_of_basis_norm_le b ξ hu ω (Real.exp_pos _).le ha x).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hB0 ω, hR0 ω]))
        ((ofBasisMixed S E b).norm_nonneg ω x))
  · have hb' : ∀ i, ξ.dual.norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] b.dualBasis i) ≤ Real.exp (B ω) := by
      simpa only [Module.Basis.baseChange_apply] using hb
    calc
      (ofBasisMixed S E b).norm ω x ≤
          Real.exp (R ω) * Real.exp (B ω) * ξ.norm ω x :=
        ofBasisMixed_norm_le_mul_of_dual_basis_norm_le b ξ ω (Real.exp_pos _).le hb' x
      _ = Real.exp (B ω + R ω) * ξ.norm ω x := by rw [← Real.exp_add, add_comm (R ω)]
      _ ≤ Real.exp (A ω + B ω + R ω) * ξ.norm ω x :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hA0 ω]))
          (ξ.norm_nonneg ω x)

/-- The base-field clause of Proposition 4.1.7: the actual completed bidual
of every dominated family lies at integrably bounded distance from a mixed
basis family. No ultrametricity assumption on the original norm is needed. -/
theorem IsDominated.bidual_localDist_ofBasisMixed (hd : ξ.IsDominated)
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds
      ((ξ.dual.dual.pullback (Module.Dual.eval K E)
        (Module.eval_apply_injective K)).localDist (ofBasisMixed S E b)) S.v := by
  apply IsDominated.localDist_ofBasisMixed_of_ultrametric b _
    (hd.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K))
    (ξ.dual.dual_isUltrametric.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K))
    hfin

/-- Strong domination controls the distance to every mixed basis family.
The extra bidual-distance hypothesis is used in the triangle inequality. -/
theorem IsStronglyDominated.localDist_ofBasisMixed (hd : ξ.IsStronglyDominated)
    (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v := by
  have hb := IsDominated.bidual_localDist_ofBasisMixed b ξ hd.1 hfin
  refine ⟨(hd.2.1.add hb.1).mono ?_,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg _)⟩⟩
  exact Eventually.of_forall fun ω => ξ.localDist_triangle
    (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K))
    (ofBasisMixed S E b) ω

/-- The fixed-basis criterion in Corollary 4.1.10. Finite measure of the
infinite locus suffices: the reverse implication uses mixed-family domination
and actual bidual comparison in the source triangle argument. -/
theorem isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    (hfin : S.v S.Ωinf < ⊤) :
    ξ.IsStronglyDominated ↔
      HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v := by
  constructor
  · intro hd
    exact IsStronglyDominated.localDist_ofBasisMixed b ξ hd hfin
  · intro hd
    have he : (ofBasisMixed S E b).localDist ξ = ξ.localDist (ofBasisMixed S E b) :=
      funext fun ω => (ofBasisMixed S E b).localDist_comm ξ ω
    have hξ : ξ.IsDominated := (ofBasisMixed_isDominated_of_measure_lt_top b hfin).of_localDist
      (by rw [he]; exact hd.1)
    have hb := IsDominated.bidual_localDist_ofBasisMixed b ξ hξ hfin
    refine ⟨hξ, (hd.1.add hb.1).mono ?_,
      ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg _)⟩⟩
    apply Eventually.of_forall
    intro ω
    have ht := ξ.localDist_triangle (ofBasisMixed S E b)
      (ξ.dual.dual.pullback (Module.Dual.eval K E) (Module.eval_apply_injective K)) ω
    rwa [(ofBasisMixed S E b).localDist_comm] at ht

/-- The base-field basis criterion under the source's usual Archimedean
normalization, which supplies finite measure of the infinite locus. -/
theorem isStronglyDominated_iff_localDist_ofBasisMixed
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion) :
    ξ.IsStronglyDominated ↔
      HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v :=
  isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top b ξ
    (S.v_Ωinf_lt_top_of_isRCLike hS)

/-- The mixed family is strongly dominated as soon as the infinite locus
has finite measure; this also covers non-usual Archimedean norms. -/
theorem ofBasisMixed_isStronglyDominated_of_measure_lt_top (hfin : S.v S.Ωinf < ⊤) :
    (ofBasisMixed S E b).IsStronglyDominated := by
  apply (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
    b (ofBasisMixed S E b) hfin).mpr
  have he : (ofBasisMixed S E b).localDist (ofBasisMixed S E b) = 0 :=
    funext fun ω => (ofBasisMixed S E b).localDist_self ω
  rw [he]
  exact integrable_hasIntegrableBounds (integrable_zero _ _ _)

/-- Corollary 4.1.8: two dominated families ultrametric at finite places
have integrably bounded local distance. -/
theorem IsDominated.localDist_of_ultrametric {η : NormFamily S E}
    (hξ : ξ.IsDominated) (hη : η.IsDominated)
    (huξ : ξ.IsUltrametric) (huη : η.IsUltrametric) (hfin : S.v S.Ωinf < ⊤) :
    HasIntegrableBounds (ξ.localDist η) S.v := by
  let b := Module.finBasis K E
  have h₁ := IsDominated.localDist_ofBasisMixed_of_ultrametric b ξ hξ huξ hfin
  have h₂ := IsDominated.localDist_ofBasisMixed_of_ultrametric b η hη huη hfin
  refine ⟨(h₁.1.add h₂.1).mono ?_,
    ⟨0, integrable_zero _ _ _, Eventually.of_forall (ξ.localDist_nonneg η)⟩⟩
  apply Eventually.of_forall
  intro ω
  have ht := ξ.localDist_triangle (ofBasisMixed S E b) η ω
  rwa [(ofBasisMixed S E b).localDist_comm] at ht

/-- The universal-basis formulation of Corollary 4.1.10. The preceding
fixed-basis theorem also applies to every other finite index type. -/
theorem isStronglyDominated_iff_forall_basis_localDist (hfin : S.v S.Ωinf < ⊤) :
    ξ.IsStronglyDominated ↔ ∀ b : Module.Basis (Fin (Module.finrank K E)) K E,
      HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v := by
  constructor
  · intro h b
    exact IsStronglyDominated.localDist_ofBasisMixed b ξ h hfin
  · intro h
    exact (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top
      (Module.finBasis K E) ξ hfin).mpr (h (Module.finBasis K E))

/-- The existential-basis formulation of Corollary 4.1.10, including rank
zero through the actual empty finite basis. -/
theorem isStronglyDominated_iff_exists_basis_localDist (hfin : S.v S.Ωinf < ⊤) :
    ξ.IsStronglyDominated ↔ ∃ b : Module.Basis (Fin (Module.finrank K E)) K E,
      HasIntegrableBounds (ξ.localDist (ofBasisMixed S E b)) S.v := by
  constructor
  · intro h
    exact ⟨Module.finBasis K E,
      IsStronglyDominated.localDist_ofBasisMixed (Module.finBasis K E) ξ h hfin⟩
  · rintro ⟨b, hb⟩
    exact (isStronglyDominated_iff_localDist_ofBasisMixed_of_measure_lt_top b ξ hfin).mpr hb

end ArakelovGeometry.NormFamily
