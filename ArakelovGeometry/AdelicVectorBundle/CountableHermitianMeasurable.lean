/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HermitianTensor
public import ArakelovGeometry.AdelicVectorBundle.Measurable
public import ArakelovGeometry.AdelicVectorBundle.MeasurableArchimedean
public import ArakelovGeometry.Analysis.ComplexPolarization

/-!
# Measurable completed coordinates and Hermitian Gram matrices

The coordinate evaluations use the actual completed fibres and compatible
norm-preserving complex embeddings. The countable density assumption is needed
only at the places visited by the parameter map.
-/

@[expose] public section

open scoped TensorProduct
open Filter Topology

noncomputable section

namespace ArakelovGeometry.NormFamily

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E]
  {ι : Type wι} [Finite ι]

/-- Measurable completed coordinates give a measurable norm. The parameter map
allows arbitrary measurable pullbacks, and density is required only along it. -/
theorem IsMeasurable.norm_of_measurable_coordinates {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable) (b : Module.Basis ι K E)
    {α : Type*} [MeasurableSpace α] (p : α → S.Ω) (hp : Measurable p)
    (σ : ∀ a, (S.ϕ (p a)).Completion →+* ℂ)
    (hσ : ∀ a x, ‖σ a x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun a =>
      σ a (algebraMap K (S.ϕ (p a)).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ a, S.IsDenseSubfieldAt K₀ (p a))
    (y : ∀ a, (S.ϕ (p a)).Completion ⊗[K] E)
    (hy : ∀ i, Measurable (fun a =>
      σ a ((b.baseChange (S.ϕ (p a)).Completion).equivFun (y a) i))) :
    Measurable (fun a => ξ.norm (p a) (y a)) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, hc⟩ := exists_surjective_nat (ι → K₀)
  let z : α → ι → ℂ := fun a i =>
    σ a ((b.baseChange (S.ϕ (p a)).Completion).equivFun (y a) i)
  let d : ℕ → α → ι → ℂ := fun n a i =>
    σ a (algebraMap K (S.ϕ (p a)).Completion (c n i : K))
  have hz : Measurable z := Measurable.of_eval hy
  have hd (n : ℕ) : Measurable (d n) := Measurable.of_eval (fun i => hm _)
  have hi (a : α) : Isometry (fun x : ι → (S.ϕ (p a)).Completion =>
      fun i => σ a (x i)) :=
    Isometry.piMap _ (fun _ => isometry_complexEmbedding_of_norm (σ a) (hσ a))
  have hex (n : ℕ) (a : α) :
      ∃ j, dist (z a) (d j a) < 1 / ((n : ℝ) + 1) := by
    have hdense : DenseRange (fun q : ι → K₀ =>
        fun i => algebraMap K (S.ϕ (p a)).Completion (q i : K)) :=
      DenseRange.piMap (fun _ => hK₀ a)
    obtain ⟨x, ⟨q, rfl⟩, hq⟩ := Metric.mem_closure_iff.mp
      (hdense ((b.baseChange (S.ϕ (p a)).Completion).equivFun (y a)))
      (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨j, rfl⟩ := hc q
    refine ⟨j, ?_⟩
    change dist ((fun x : ι → (S.ϕ (p a)).Completion => fun i => σ a (x i)) _)
      ((fun x : ι → (S.ϕ (p a)).Completion => fun i => σ a (x i)) _) < _
    rw [(hi a).dist_eq]
    exact hq
  let k : ℕ → α → ℕ := fun n a => Nat.find (hex n a)
  have hk (n : ℕ) : Measurable (k n) :=
    measurable_find (hex n) (fun j => measurableSet_lt (hz.dist (hd j)) measurable_const)
  let f : ℕ → α → ℝ := fun n a => ξ.norm (p a)
    ((1 : (S.ϕ (p a)).Completion) ⊗ₜ[K] basisSubfieldMap b K₀ (c n))
  have hf (n : ℕ) : Measurable (f n) := (hξ _).comp hp
  have hsel (n : ℕ) : Measurable (fun a => f (k n a) a) :=
    (measurable_from_prod_countable_left (f := fun q : α × ℕ => f q.2 q.1) hf).comp
      (measurable_id.prodMk (hk n))
  apply measurable_of_tendsto_metrizable hsel
  apply tendsto_pi_nhds.mpr
  intro a
  let := ξ.fibreNormedAddCommGroup (p a)
  let := ξ.fibreNormedSpace (p a)
  let B := b.baseChange (S.ϕ (p a)).Completion
  let v : ℕ → ι → (S.ϕ (p a)).Completion := fun n i =>
    algebraMap K (S.ϕ (p a)).Completion (c (k n a) i : K)
  have hv : Tendsto v atTop (𝓝 (B.equivFun (y a))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← (hi a).dist_eq]
    exact (dist_comm _ _).trans_le (Nat.find_spec (hex n a)).le
  have hcont : Continuous B.equivFun.symm :=
    (linearMapToNormedAddGroupHom B.equivFun.symm.toLinearMap).continuous
  have ht := ((hcont.tendsto (B.equivFun (y a))).comp hv).norm
  change Tendsto (fun n => ξ.norm (p a) (B.equivFun.symm (v n))) atTop
    (𝓝 (ξ.norm (p a) (B.equivFun.symm (B.equivFun (y a))))) at ht
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply,
    f, basisSubfieldMap_tmul, v, B] using ht

/-- The Hermitian pairing on the existing completed fibre, with its prescribed
norm and scalar action. -/
def IsHermitian.archimedeanInner {ξ : NormFamily S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hξ : ξ.IsHermitian hS) (ω : S.Ωinf)
    (x y : (S.ϕ ω.val).Completion ⊗[K] E) : (S.ϕ ω.val).Completion := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let := ξ.fibreNormedAddCommGroup ω.val
  let := ξ.fibreNormedSpace ω.val
  let := hξ.fibreInnerProductSpace ω.val ω.property
  exact inner (S.ϕ ω.val).Completion x y

/-- Rational tests detect the complex locus after any measurable pullback and
for any compatible measurable choice of completed embeddings. -/
theorem measurableSet_complex_locus_pullback
    (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    {α : Type*} [MeasurableSpace α] (p : α → S.Ωinf)
    (σ : ∀ a, (S.ϕ (p a).val).Completion →+* ℂ)
    (hσ : ∀ a x, ‖σ a x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun a =>
      σ a (algebraMap K (S.ϕ (p a).val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ a, S.IsDenseSubfieldAt K₀ (p a).val) :
    MeasurableSet {a | Function.Surjective (σ a)} := by
  have he : {a | Function.Surjective (σ a)} =
      (⋂ q : K₀, {a | (σ a
        (algebraMap K (S.ϕ (p a).val).Completion (q : K))).im = 0})ᶜ := by
    ext a
    let := hS (p a).val (p a).property
    let := IsRCLikeNormedField.rclike (S.ϕ (p a).val).Completion
    rw [Set.mem_compl_iff, Set.mem_iInter]
    simp only [Set.mem_ofPred_eq, complexEmbedding_surjective_iff (σ a) (hσ a)]
    apply not_congr
    refine ⟨fun h q => h _, fun h x => ?_⟩
    exact (hK₀ a).induction_on x
      (isClosed_eq (Complex.continuous_im.comp
        (isometry_complexEmbedding_of_norm (σ a) (hσ a)).continuous) continuous_const) h
  rw [he]
  exact (MeasurableSet.iInter fun q : K₀ =>
    measurableSet_eq_fun (Complex.measurable_im.comp (hm (q : K))) measurable_const).compl

/-- The actual Hermitian pairing is measurable on completed sections with
measurable coordinates, including after an arbitrary measurable pullback. -/
theorem IsMeasurable.archimedeanInner_of_measurable_coordinates {ξ : NormFamily S E}
    (hξ : ξ.IsMeasurable)
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E)
    {α : Type*} [MeasurableSpace α] (p : α → S.Ωinf) (hp : Measurable p)
    (σ : ∀ a, (S.ϕ (p a).val).Completion →+* ℂ)
    (hσ : ∀ a x, ‖σ a x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun a =>
      σ a (algebraMap K (S.ϕ (p a).val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ a, S.IsDenseSubfieldAt K₀ (p a).val)
    (x y : ∀ a, (S.ϕ (p a).val).Completion ⊗[K] E)
    (hx : ∀ i, Measurable (fun a =>
      σ a ((b.baseChange (S.ϕ (p a).val).Completion).equivFun (x a) i)))
    (hy : ∀ i, Measurable (fun a =>
      σ a ((b.baseChange (S.ϕ (p a).val).Completion).equivFun (y a) i))) :
    Measurable (fun a => σ a (hH.archimedeanInner (p a) (x a) (y a))) := by
  classical
  let c : ∀ a, (S.ϕ (p a).val).Completion := fun a =>
    if h : Function.Surjective (σ a) then (h Complex.I).choose else 0
  have hc (a : α) : σ a (c a) =
      if Function.Surjective (σ a) then Complex.I else 0 := by
    by_cases h : Function.Surjective (σ a)
    · simp only [c, dite_eq_left h, ite_eq_left h]
      exact (h Complex.I).choose_spec
    · simp [c, h]
  have hmc : Measurable (fun a => σ a (c a)) := by
    simp_rw [hc]
    exact Measurable.piecewise
      (measurableSet_complex_locus_pullback hS p σ hσ hm K₀ hK₀)
      measurable_const measurable_const
  have hp' : Measurable (fun a => (p a).val) := measurable_subtype_coe.comp hp
  have hplus : Measurable (fun a => ξ.norm (p a).val (x a + y a)) :=
    hξ.norm_of_measurable_coordinates b _ hp' σ hσ hm K₀ hK₀ _
      (fun i => by
        convert (hx i).add (hy i) using 1
        funext a
        simp only [map_add, Pi.add_apply])
  have hminus : Measurable (fun a => ξ.norm (p a).val (x a - y a)) :=
    hξ.norm_of_measurable_coordinates b _ hp' σ hσ hm K₀ hK₀ _
      (fun i => by
        convert (hx i).sub (hy i) using 1
        funext a
        simp only [map_sub, Pi.sub_apply])
  have hic (i : ι) : Measurable (fun a =>
      σ a ((b.baseChange (S.ϕ (p a).val).Completion).equivFun (c a • y a) i)) := by
    convert hmc.mul (hy i) using 1
    funext a
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Pi.mul_apply]
  have hip : Measurable (fun a => ξ.norm (p a).val (x a + c a • y a)) :=
    hξ.norm_of_measurable_coordinates b _ hp' σ hσ hm K₀ hK₀ _
      (fun i => by
        convert (hx i).add (hic i) using 1
        funext a
        simp only [map_add, Pi.add_apply])
  have him : Measurable (fun a => ξ.norm (p a).val (x a - c a • y a)) :=
    hξ.norm_of_measurable_coordinates b _ hp' σ hσ hm K₀ hK₀ _
      (fun i => by
        convert (hx i).sub (hic i) using 1
        funext a
        simp only [map_sub, Pi.sub_apply])
  have hre : (fun a => (σ a (hH.archimedeanInner (p a) (x a) (y a))).re) =
      fun a => (ξ.norm (p a).val (x a + y a) ^ 2 -
        ξ.norm (p a).val (x a - y a) ^ 2) / 4 := by
    funext a
    let := hS (p a).val (p a).property
    let := IsRCLikeNormedField.rclike (S.ϕ (p a).val).Completion
    let := ξ.fibreNormedAddCommGroup (p a).val
    let := ξ.fibreNormedSpace (p a).val
    let := hH.fibreInnerProductSpace (p a).val (p a).property
    exact complexEmbedding_inner_re (σ a) (hσ a) (x a) (y a)
  have himag : (fun a => (σ a (hH.archimedeanInner (p a) (x a) (y a))).im) =
      fun a => (ξ.norm (p a).val (x a - c a • y a) ^ 2 -
        ξ.norm (p a).val (x a + c a • y a) ^ 2) / 4 := by
    funext a
    let := hS (p a).val (p a).property
    let := IsRCLikeNormedField.rclike (S.ϕ (p a).val).Completion
    let := ξ.fibreNormedAddCommGroup (p a).val
    let := ξ.fibreNormedSpace (p a).val
    let := hH.fibreInnerProductSpace (p a).val (p a).property
    by_cases h : Function.Surjective (σ a)
    · exact complexEmbedding_inner_im (σ a) (hσ a) (c a) (by simpa [h] using hc a)
        (x a) (y a)
    · have hr : ∀ z, (σ a z).im = 0 := by
        simpa only [complexEmbedding_surjective_iff (σ a) (hσ a), not_not] using h
      simp [c, h, hr]
  have Hr : Measurable (fun a =>
      (σ a (hH.archimedeanInner (p a) (x a) (y a))).re) := by
    rw [hre]
    exact ((hplus.pow_const 2).sub (hminus.pow_const 2)).div_const 4
  have Hi : Measurable (fun a =>
      (σ a (hH.archimedeanInner (p a) (x a) (y a))).im) := by
    rw [himag]
    exact ((him.pow_const 2).sub (hip.pow_const 2)).div_const 4
  convert (Complex.measurable_ofReal.comp Hr).add
    ((Complex.measurable_ofReal.comp Hi).mul_const Complex.I) using 1
  funext a
  exact (Complex.re_add_im _).symm

/-- The actual completed Hermitian Gram matrix, expressed using a compatible
complex embedding and the scalar extension of the given rational basis. -/
def IsHermitian.archimedeanGram {ξ : NormFamily S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E) (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) : Matrix ι ι ℂ := fun i j =>
  σ (hH.archimedeanInner ω ((b.baseChange (S.ϕ ω.val).Completion) i)
    ((b.baseChange (S.ϕ ω.val).Completion) j))

/-- Every Gram entry is measurable, with the same arbitrary pullback and
infinite-place countable density permitted for completed coordinate evaluation. -/
theorem IsMeasurable.archimedeanGram {ξ : NormFamily S E} (hξ : ξ.IsMeasurable)
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E)
    {α : Type*} [MeasurableSpace α] (p : α → S.Ωinf) (hp : Measurable p)
    (σ : ∀ a, (S.ϕ (p a).val).Completion →+* ℂ)
    (hσ : ∀ a x, ‖σ a x‖ = ‖x‖)
    (hm : ∀ x : K, Measurable (fun a =>
      σ a (algebraMap K (S.ϕ (p a).val).Completion x)))
    (K₀ : Subfield K) [Countable K₀]
    (hK₀ : ∀ a, S.IsDenseSubfieldAt K₀ (p a).val) (i j : ι) :
    Measurable (fun a => hH.archimedeanGram b (p a) (σ a) i j) := by
  classical
  apply hξ.archimedeanInner_of_measurable_coordinates hH b p hp σ hσ hm K₀ hK₀
  all_goals
    intro k
    simpa only [Module.Basis.equivFun_apply, Module.Basis.repr_self_apply,
      apply_ite, map_one, map_zero] using
      (measurable_const : Measurable (fun _ : α => if _ = k then (1 : ℂ) else 0))

omit [Finite ι] in
/-- The Gram matrix has the conjugate symmetry of the actual Hermitian pairing. -/
theorem IsHermitian.conj_archimedeanGram {ξ : NormFamily S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E) (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (i j : ι) :
    starRingEnd ℂ (hH.archimedeanGram b ω σ j i) = hH.archimedeanGram b ω σ i j := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let := ξ.fibreNormedAddCommGroup ω.val
  let := ξ.fibreNormedSpace ω.val
  let := hH.fibreInnerProductSpace ω.val ω.property
  change starRingEnd ℂ (σ (inner _ _ _)) = σ (inner _ _ _)
  rw [← complexEmbedding_map_conj σ hσ, inner_conj_symm]

/-- The Gram quadratic form is exactly the original completed norm squared. -/
theorem IsHermitian.archimedeanGram_norm_sq [Fintype ι] {ξ : NormFamily S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E) (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (c : ι → (S.ϕ ω.val).Completion) :
    ξ.norm ω.val ((b.baseChange (S.ϕ ω.val).Completion).equivFun.symm c) ^ 2 =
      (∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * hH.archimedeanGram b ω σ i j * σ (c j)).re := by
  let := hS ω.val ω.property
  let := IsRCLikeNormedField.rclike (S.ϕ ω.val).Completion
  let := ξ.fibreNormedAddCommGroup ω.val
  let := ξ.fibreNormedSpace ω.val
  let := hH.fibreInnerProductSpace ω.val ω.property
  rw [Module.Basis.equivFun_symm_apply]
  exact complexEmbedding_norm_sum_sq σ hσ c (b.baseChange (S.ϕ ω.val).Completion)

/-- Positive definiteness is asserted on the actual completed coordinate space;
at real places this is precisely the real image of the compatible embedding. -/
theorem IsHermitian.archimedeanGram_quadratic_pos [Fintype ι] {ξ : NormFamily S E}
    {hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    (hH : ξ.IsHermitian hS) (b : Module.Basis ι K E) (ω : S.Ωinf)
    (σ : (S.ϕ ω.val).Completion →+* ℂ) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (c : ι → (S.ϕ ω.val).Completion) (hc : c ≠ 0) :
    0 < (∑ i, ∑ j, starRingEnd ℂ (σ (c i)) *
      hH.archimedeanGram b ω σ i j * σ (c j)).re := by
  rw [← hH.archimedeanGram_norm_sq b ω σ hσ]
  exact pow_pos (ξ.norm_pos ω.val
    ((b.baseChange (S.ϕ ω.val).Completion).equivFun.symm.map_ne_zero_iff.mpr hc)) _

end ArakelovGeometry.NormFamily
