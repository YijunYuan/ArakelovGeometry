/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.LinearAlgebra.Filtration.Graded
public import ArakelovGeometry.LinearAlgebra.Filtration.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Canonical graded tensor maps

Tensoring the two step inclusions and then taking the quotient gives a map
from each pair of grades into the grade at their total weight. The source of
the assembled map retains every pair with that total weight.
-/

@[expose] public section

open scoped TensorProduct DirectSum
open Module

namespace Submodule

variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]

variable {F : ℝ → Submodule K E} {G : ℝ → Submodule K V}

/-- A strict left-factor vector raises the total tensor weight. -/
theorem tmul_mem_tensorFiltration_rightLimit_left (hF : Antitone F)
    {t u γ : ℝ} (h : t + u = γ) {x : E} {y : V}
    (hx : x ∈ filtrationRightLimit F t) (hy : y ∈ G u) :
    x ⊗ₜ[K] y ∈ filtrationRightLimit (tensorFiltration F G) γ := by
  obtain ⟨ε, hε, hx⟩ := (mem_rightLimit_iff hF t x).mp hx
  exact mem_iSup_of_mem ⟨t + ε + u, by linarith⟩
    (tmul_mem_tensorFiltration (F := F) (G := G) le_rfl hx hy)

/-- A strict right-factor vector raises the total tensor weight. -/
theorem tmul_mem_tensorFiltration_rightLimit_right (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) {x : E} {y : V}
    (hx : x ∈ F t) (hy : y ∈ filtrationRightLimit G u) :
    x ⊗ₜ[K] y ∈ filtrationRightLimit (tensorFiltration F G) γ := by
  obtain ⟨ε, hε, hy⟩ := (mem_rightLimit_iff hG u y).mp hy
  exact mem_iSup_of_mem ⟨t + (u + ε), by linarith⟩
    (tmul_mem_tensorFiltration (F := F) (G := G) le_rfl hx hy)

/-- The tensor of the step inclusions, with codomain the step at the total weight. -/
noncomputable def tensorFiltrationStepMap (F : ℝ → Submodule K E)
    (G : ℝ → Submodule K V) {t u γ : ℝ} (h : t + u = γ) :
    F t ⊗[K] G u →ₗ[K] tensorFiltration F G γ :=
  (TensorProduct.mapIncl (F t) (G u)).codRestrict (tensorFiltration F G γ) (by
    intro x
    exact (show LinearMap.range (TensorProduct.mapIncl (F t) (G u)) ≤
        tensorFiltration F G γ from
      le_iSup_of_le t (le_iSup_of_le u (le_iSup_of_le h.symm.le le_rfl))) ⟨x, rfl⟩)

/-- The canonical map from the tensor product of two steps to the total-weight grade. -/
noncomputable def tensorFiltrationGradedLift (F : ℝ → Submodule K E)
    (G : ℝ → Submodule K V) {t u γ : ℝ} (h : t + u = γ) :
    F t ⊗[K] G u →ₗ[K] FiltrationGraded (tensorFiltration F G) γ :=
  (filtrationGradedMk (tensorFiltration F G) γ).comp (tensorFiltrationStepMap F G h)

/-- The two strict-factor tensor subspaces are killed in the total-weight grade. -/
theorem tensorFiltrationGradedLift_ker (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) :
    LinearMap.range (TensorProduct.map
        ((filtrationRightLimit F t).comap (F t).subtype).subtype
        (LinearMap.id : G u →ₗ[K] G u)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : F t →ₗ[K] F t)
        ((filtrationRightLimit G u).comap (G u).subtype).subtype) ≤
      LinearMap.ker (tensorFiltrationGradedLift F G h) := by
  apply sup_le
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul x y =>
      apply (filtrationGradedMk_eq_zero _ _ _).mpr
      exact tmul_mem_tensorFiltration_rightLimit_left hF h x.property y.property
    | add x y hx hy =>
      simpa only [map_add] using add_mem hx hy
  · rintro _ ⟨x, rfl⟩
    induction x with
    | tmul x y =>
      apply (filtrationGradedMk_eq_zero _ _ _).mpr
      exact tmul_mem_tensorFiltration_rightLimit_right hG h x.property y.property
    | add x y hx hy =>
      simpa only [map_add] using add_mem hx hy

/-- The canonical pair map on actual grades; it need not cover the whole grade by itself. -/
noncomputable def tensorFiltrationGradedPair (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) :
    FiltrationGraded F t ⊗[K] FiltrationGraded G u →ₗ[K]
      FiltrationGraded (tensorFiltration F G) γ :=
  (Submodule.liftQ _ (tensorFiltrationGradedLift F G h)
      (tensorFiltrationGradedLift_ker hF hG h)).comp
    (TensorProduct.quotientTensorQuotientEquiv
      ((filtrationRightLimit F t).comap (F t).subtype)
      ((filtrationRightLimit G u).comap (G u).subtype)).toLinearMap

@[simp]
theorem tensorFiltrationGradedPair_mk (hF : Antitone F) (hG : Antitone G)
    {t u γ : ℝ} (h : t + u = γ) (x : F t) (y : G u) :
    tensorFiltrationGradedPair hF hG h
        (filtrationGradedMk F t x ⊗ₜ[K] filtrationGradedMk G u y) =
      filtrationGradedMk (tensorFiltration F G) γ
        (tensorFiltrationStepMap F G h (x ⊗ₜ[K] y)) := rfl

/-- Assemble all pairs with the same total weight, retaining every collision. -/
noncomputable def tensorFiltrationGradedSum (hF : Antitone F) (hG : Antitone G) (γ : ℝ) :
    (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) →ₗ[K]
      FiltrationGraded (tensorFiltration F G) γ :=
  DirectSum.toModule K _ _ (fun p ↦ tensorFiltrationGradedPair hF hG p.property)

/-- Weighted generators prove that all equal-total-weight pair maps together cover the grade. -/
theorem tensorFiltrationGradedSum_surjective {ι κ : Type*} (b : ι → E) (c : κ → V)
    (w : ι → ℝ) (z : κ → ℝ) (hFa : Antitone F) (hGa : Antitone G)
    (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
    (hG : ∀ u, G u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    Function.Surjective (tensorFiltrationGradedSum hFa hGa γ) := by
  classical
  let f := tensorFiltrationGradedSum hFa hGa γ
  have hspan := tensorFiltration_eq_span b c w z hF hG γ
  have hmem : ∀ (v : E ⊗[K] V) (hv : v ∈ tensorFiltration F G γ),
      filtrationGradedMk (tensorFiltration F G) γ ⟨v, hv⟩ ∈ LinearMap.range f := by
    intro v hv
    have hv' := hv
    rw [hspan] at hv'
    induction hv' using span_induction with
    | mem v hv' =>
      obtain ⟨⟨i, j⟩, hij, rfl⟩ := hv'
      by_cases he : w i + z j = γ
      · have hbi : b i ∈ F (w i) := by
          rw [hF]
          exact subset_span ⟨i, show w i ≤ w i from le_rfl, rfl⟩
        have hcj : c j ∈ G (z j) := by
          rw [hG]
          exact subset_span ⟨j, show z j ≤ z j from le_rfl, rfl⟩
        refine ⟨DirectSum.lof K _ _ ⟨(w i, z j), he⟩
          (filtrationGradedMk F (w i) ⟨b i, hbi⟩ ⊗ₜ[K]
            filtrationGradedMk G (z j) ⟨c j, hcj⟩), ?_⟩
        simp only [f, tensorFiltrationGradedSum, DirectSum.toModule_lof,
          tensorFiltrationGradedPair_mk]
        rfl
      · have hzero : filtrationGradedMk (tensorFiltration F G) γ
            ⟨b i ⊗ₜ[K] c j, hv⟩ = 0 := by
          apply (filtrationGradedMk_eq_zero _ _ _).mpr
          change b i ⊗ₜ[K] c j ∈ ⨆ s : {s : ℝ // γ < s}, tensorFiltration F G s.val
          rw [tensorFiltration_rightLimit_eq_span b c w z hF hG]
          exact subset_span ⟨(i, j), lt_of_le_of_ne hij (Ne.symm he), rfl⟩
        rw [hzero]
        exact (LinearMap.range f).zero_mem
    | zero => exact (LinearMap.range f).zero_mem
    | add x y hx hy ihx ihy =>
      have hxT : x ∈ tensorFiltration F G γ := hspan.symm ▸ hx
      have hyT : y ∈ tensorFiltration F G γ := hspan.symm ▸ hy
      change filtrationGradedMk _ _ (⟨x, hxT⟩ + ⟨y, hyT⟩) ∈ _
      rw [map_add]
      exact add_mem (ihx hxT) (ihy hyT)
    | smul a x hx ih =>
      have hxT : x ∈ tensorFiltration F G γ := hspan.symm ▸ hx
      change filtrationGradedMk _ _ (a • ⟨x, hxT⟩) ∈ _
      rw [map_smul]
      exact smul_mem _ a (ih hxT)
  intro y
  obtain ⟨x, rfl⟩ := ((filtrationRightLimit (tensorFiltration F G) γ).comap
    (tensorFiltration F G γ).subtype).mkQ_surjective y
  exact hmem x.val x.property

section Inverse

variable {ι κ : Type*} (b : Basis ι K E) (c : Basis κ K V)
  (w : ι → ℝ) (z : κ → ℝ)
  (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
  (hG : ∀ u, G u = span K (c '' {j | u ≤ z j}))

/-- An adapted tensor basis splits the grade into its original equal-total-weight pairs. -/
noncomputable def tensorFiltrationGradedInverseAux (γ : ℝ) :
    E ⊗[K] V →ₗ[K] (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) := by
  classical
  exact (b.tensorProduct c).constr K fun ij ↦
    if h : w ij.1 + z ij.2 = γ then
      DirectSum.lof K _ _ ⟨(w ij.1, z ij.2), h⟩
        (filtrationGradedMk F (w ij.1) ⟨b ij.1, by
          rw [hF]; exact subset_span ⟨ij.1, show w ij.1 ≤ w ij.1 from le_rfl, rfl⟩⟩ ⊗ₜ[K]
        filtrationGradedMk G (z ij.2) ⟨c ij.2, by
          rw [hG]; exact subset_span ⟨ij.2, show z ij.2 ≤ z ij.2 from le_rfl, rfl⟩⟩)
    else 0

/-- The splitting map vanishes on tensor basis vectors above the threshold. -/
theorem tensorFiltrationGradedInverseAux_tmul_of_ne (γ : ℝ) (i : ι) (j : κ)
    (h : w i + z j ≠ γ) :
    tensorFiltrationGradedInverseAux b c w z hF hG γ (b i ⊗ₜ[K] c j) = 0 := by
  classical
  rw [← Basis.tensorProduct_apply b c i j, tensorFiltrationGradedInverseAux, Basis.constr_basis]
  exact dite_eq_right h

/-- Strict tensor weights lie in the kernel of the adapted splitting map. -/
theorem tensorFiltrationGradedInverseAux_ker (γ : ℝ) :
    filtrationRightLimit (tensorFiltration F G) γ ≤
      LinearMap.ker (tensorFiltrationGradedInverseAux b c w z hF hG γ) := by
  change (⨆ s : {s : ℝ // γ < s}, tensorFiltration F G s.val) ≤ _
  rw [tensorFiltration_rightLimit_eq_span b c w z hF hG]
  apply span_le.mpr
  rintro _ ⟨⟨i, j⟩, hij, rfl⟩
  exact tensorFiltrationGradedInverseAux_tmul_of_ne b c w z hF hG γ i j (ne_of_gt hij)

/-- A basis splitting descends to the actual total-weight quotient. -/
noncomputable def tensorFiltrationGradedInverse (γ : ℝ) :
    FiltrationGraded (tensorFiltration F G) γ →ₗ[K]
      (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
        FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) :=
  Submodule.liftQ _
    ((tensorFiltrationGradedInverseAux b c w z hF hG γ).comp
      (tensorFiltration F G γ).subtype)
    (fun _ hx ↦ tensorFiltrationGradedInverseAux_ker b c w z hF hG γ hx)

/-- On two filtered vectors the splitting recovers their original pair of quotient classes. -/
theorem tensorFiltrationGradedInverseAux_tmul {t u γ : ℝ} (h : t + u = γ)
    (x : F t) (y : G u) :
    tensorFiltrationGradedInverseAux b c w z hF hG γ (x.val ⊗ₜ[K] y.val) =
      DirectSum.lof K {p : ℝ × ℝ // p.1 + p.2 = γ}
        (fun p ↦ FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) ⟨(t, u), h⟩
        (filtrationGradedMk F t x ⊗ₜ[K] filtrationGradedMk G u y) := by
  classical
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have hx' := hx
  rw [hF] at hx'
  induction hx' using span_induction with
  | mem x hx' =>
    obtain ⟨i, hi, rfl⟩ := hx'
    change t ≤ w i at hi
    have hy' := hy
    rw [hG] at hy'
    induction hy' using span_induction with
    | mem y hy' =>
      obtain ⟨j, hj, rfl⟩ := hy'
      change u ≤ z j at hj
      rcases lt_or_eq_of_le hi with hi | rfl
      · rw [tensorFiltrationGradedInverseAux_tmul_of_ne b c w z hF hG γ i j (by linarith)]
        have hz : filtrationGradedMk F t ⟨b i, hx⟩ = 0 := by
          apply (filtrationGradedMk_eq_zero _ _ _).mpr
          apply mem_iSup_of_mem ⟨w i, hi⟩
          rw [hF]
          exact subset_span ⟨i, show w i ≤ w i from le_rfl, rfl⟩
        rw [hz, TensorProduct.zero_tmul, map_zero]
      · rcases lt_or_eq_of_le hj with hj | rfl
        · rw [tensorFiltrationGradedInverseAux_tmul_of_ne b c w z hF hG γ i j (by linarith)]
          have hz : filtrationGradedMk G u ⟨c j, hy⟩ = 0 := by
            apply (filtrationGradedMk_eq_zero _ _ _).mpr
            apply mem_iSup_of_mem ⟨z j, hj⟩
            rw [hG]
            exact subset_span ⟨j, show z j ≤ z j from le_rfl, rfl⟩
          rw [hz, TensorProduct.tmul_zero, map_zero]
        · rw [← Basis.tensorProduct_apply b c i j,
            tensorFiltrationGradedInverseAux, Basis.constr_basis]
          simp only [h, dite_true]
    | zero =>
      rw [show (⟨0, hy⟩ : G u) = 0 from rfl]
      simp
    | add a d ha hd iha ihd =>
      have haG : a ∈ G u := (hG u).symm ▸ ha
      have hdG : d ∈ G u := (hG u).symm ▸ hd
      rw [show (⟨a + d, hy⟩ : G u) = ⟨a, haG⟩ + ⟨d, hdG⟩ from rfl]
      simpa only [Submodule.coe_add, Subtype.coe_mk, TensorProduct.tmul_add, map_add] using
        congrArg₂ (· + ·) (iha haG) (ihd hdG)
    | smul a d hd ih =>
      have hdG : d ∈ G u := (hG u).symm ▸ hd
      rw [show (⟨a • d, hy⟩ : G u) = a • ⟨d, hdG⟩ from rfl]
      simpa only [Submodule.coe_smul, Subtype.coe_mk, TensorProduct.tmul_smul, map_smul] using
        congrArg (a • ·) (ih hdG)
  | zero =>
    rw [show (⟨0, hx⟩ : F t) = 0 from rfl]
    simp
  | add a d ha hd iha ihd =>
    have haF : a ∈ F t := (hF t).symm ▸ ha
    have hdF : d ∈ F t := (hF t).symm ▸ hd
    rw [show (⟨a + d, hx⟩ : F t) = ⟨a, haF⟩ + ⟨d, hdF⟩ from rfl]
    simpa only [Submodule.coe_add, Subtype.coe_mk, TensorProduct.add_tmul, map_add] using
      congrArg₂ (· + ·) (iha haF) (ihd hdF)
  | smul a d hd ih =>
    have hdF : d ∈ F t := (hF t).symm ▸ hd
    rw [show (⟨a • d, hx⟩ : F t) = a • ⟨d, hdF⟩ from rfl]
    simpa only [Submodule.coe_smul, Subtype.coe_mk, ← TensorProduct.smul_tmul', map_smul] using
      congrArg (a • ·) (ih hdF)

/-- The adapted splitting is a left inverse to the canonical map on all pair summands. -/
theorem tensorFiltrationGradedInverse_comp (hFa : Antitone F) (hGa : Antitone G) (γ : ℝ) :
    (tensorFiltrationGradedInverse b c w z hF hG γ).comp
      (tensorFiltrationGradedSum hFa hGa γ) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro p
  apply TensorProduct.ext'
  intro x y
  obtain ⟨x, rfl⟩ := ((filtrationRightLimit F p.val.1).comap (F p.val.1).subtype).mkQ_surjective x
  obtain ⟨y, rfl⟩ := ((filtrationRightLimit G p.val.2).comap (G p.val.2).subtype).mkQ_surjective y
  simp only [LinearMap.comp_apply, LinearMap.id_apply, tensorFiltrationGradedSum,
    DirectSum.toModule_lof]
  change tensorFiltrationGradedInverse b c w z hF hG γ
    (tensorFiltrationGradedPair hFa hGa p.property
      (filtrationGradedMk F p.val.1 x ⊗ₜ[K] filtrationGradedMk G p.val.2 y)) = _
  rw [tensorFiltrationGradedPair_mk]
  exact tensorFiltrationGradedInverseAux_tmul b c w z hF hG p.property x y

include hF hG in
/-- The canonical sum of all equal-total-weight pair maps is bijective. -/
theorem tensorFiltrationGradedSum_bijective (hFa : Antitone F) (hGa : Antitone G) (γ : ℝ) :
    Function.Bijective (tensorFiltrationGradedSum hFa hGa γ) := by
  refine ⟨?_, tensorFiltrationGradedSum_surjective b c w z hFa hGa hF hG γ⟩
  have hleft : Function.LeftInverse (tensorFiltrationGradedInverse b c w z hF hG γ)
      (tensorFiltrationGradedSum hFa hGa γ) :=
    fun x ↦ LinearMap.congr_fun (tensorFiltrationGradedInverse_comp b c w z hF hG hFa hGa γ) x
  exact hleft.injective

/-- The canonical decomposition of a tensor grade, with every equal-total-weight pair retained. -/
noncomputable def tensorFiltrationGradedEquiv (hFa : Antitone F) (hGa : Antitone G) (γ : ℝ) :
    (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) ≃ₗ[K]
      FiltrationGraded (tensorFiltration F G) γ :=
  LinearEquiv.ofBijective (tensorFiltrationGradedSum hFa hGa γ)
    (tensorFiltrationGradedSum_bijective b c w z hF hG hFa hGa γ)

end Inverse

section Naturality

variable {E' V' : Type*} [AddCommGroup E'] [Module K E']
  [AddCommGroup V'] [Module K V']
  {F' : ℝ → Submodule K E'} {G' : ℝ → Submodule K V'}
  (f : E →ₗ[K] E') (g : V →ₗ[K] V')
  (hf : ∀ t, F t ≤ (F' t).comap f) (hg : ∀ u, G u ≤ (G' u).comap g)

include hf hg in
/-- Tensoring two filtered maps preserves their intrinsic convolution filtrations. -/
theorem tensorFiltration_map_le (γ : ℝ) :
    tensorFiltration F G γ ≤ (tensorFiltration F' G' γ).comap (TensorProduct.map f g) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro u
  apply iSup_le
  intro h
  rintro _ ⟨x, rfl⟩
  induction x with
  | tmul x y =>
    exact tmul_mem_tensorFiltration h (hf t x.property) (hg u y.property)
  | add x y hx hy => simpa only [map_add] using add_mem hx hy

/-- Canonical pair maps commute with the grades of filtered tensor maps. -/
theorem tensorFiltrationGradedPair_natural
    (hFa : Antitone F) (hGa : Antitone G) (hFa' : Antitone F') (hGa' : Antitone G')
    {t u γ : ℝ} (h : t + u = γ) :
    (filtrationGradedMap (TensorProduct.map f g) (tensorFiltration_map_le f g hf hg) γ).comp
      (tensorFiltrationGradedPair hFa hGa h) =
    (tensorFiltrationGradedPair hFa' hGa' h).comp
      (TensorProduct.map (filtrationGradedMap f hf t) (filtrationGradedMap g hg u)) := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨x, rfl⟩ := ((filtrationRightLimit F t).comap (F t).subtype).mkQ_surjective x
  obtain ⟨y, rfl⟩ := ((filtrationRightLimit G u).comap (G u).subtype).mkQ_surjective y
  rfl

/-- The full graded decomposition is natural for filtered tensor maps. -/
theorem tensorFiltrationGradedSum_natural
    (hFa : Antitone F) (hGa : Antitone G) (hFa' : Antitone F') (hGa' : Antitone G') (γ : ℝ) :
    (filtrationGradedMap (TensorProduct.map f g) (tensorFiltration_map_le f g hf hg) γ).comp
      (tensorFiltrationGradedSum hFa hGa γ) =
    (tensorFiltrationGradedSum hFa' hGa' γ).comp
      (DirectSum.lmap fun p : {p : ℝ × ℝ // p.1 + p.2 = γ} ↦
        TensorProduct.map (filtrationGradedMap f hf p.val.1)
          (filtrationGradedMap g hg p.val.2)) := by
  apply DirectSum.linearMap_ext
  intro p
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, tensorFiltrationGradedSum, DirectSum.toModule_lof,
    DirectSum.lmap_lof] using
    LinearMap.congr_fun (tensorFiltrationGradedPair_natural f g hf hg hFa hGa hFa' hGa'
      p.property) x

end Naturality

/-- Composition with an image-filtration grade gives the canonical quotient map. -/
noncomputable def tensorFiltrationGradedQuotient {Q : Type*} [AddCommGroup Q] [Module K Q]
    (q : E ⊗[K] V →ₗ[K] Q) (hF : Antitone F) (hG : Antitone G) (γ : ℝ) :
    (⨁ p : {p : ℝ × ℝ // p.1 + p.2 = γ},
      FiltrationGraded F p.val.1 ⊗[K] FiltrationGraded G p.val.2) →ₗ[K]
      FiltrationGraded (fun t ↦ (tensorFiltration F G t).map q) γ :=
  (filtrationGradedMap q (fun t ↦ le_comap_map q (tensorFiltration F G t)) γ).comp
    (tensorFiltrationGradedSum hF hG γ)

/-- Every image-grade class has a lift in the sum of the original pair grades. -/
theorem tensorFiltrationGradedQuotient_surjective {Q ι κ : Type*}
    [AddCommGroup Q] [Module K Q] (q : E ⊗[K] V →ₗ[K] Q)
    (b : ι → E) (c : κ → V) (w : ι → ℝ) (z : κ → ℝ)
    (hFa : Antitone F) (hGa : Antitone G)
    (hF : ∀ t, F t = span K (b '' {i | t ≤ w i}))
    (hG : ∀ u, G u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    Function.Surjective (tensorFiltrationGradedQuotient q hFa hGa γ) :=
  (filtrationGradedMap_surjective q
    (fun t ↦ le_comap_map q (tensorFiltration F G t)) γ rfl).comp
    (tensorFiltrationGradedSum_surjective b c w z hFa hGa hF hG γ)

end Submodule
