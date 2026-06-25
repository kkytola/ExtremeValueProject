/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation
import Mathlib

section weak_convergence_cdf

open Filter Topology NNReal ENNReal Set

/-- Lemma 4.3 (cdf-tight) in blueprint. -/
lemma CumulativeDistributionFunction.forall_pos_exists_lt_gt_continuousAt
    (F : CumulativeDistributionFunction) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (a b : ℝ), a < b ∧ F a < ε ∧ 1 - ε < F b ∧ ContinuousAt F a ∧ ContinuousAt F b := by
  sorry -- **Issue #16**

/-- Lemma 4.4 (subdivision-dense) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that the consecutive
differences are smaller than a given `δ > 0`. -/
lemma forall_exists_subdivision_diff_lt_of_dense {D : Set ℝ} (D_dense : Dense D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b) {δ : ℝ} (δ_pos : 0 < δ) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), cs j.succ - cs (Fin.castAdd _ j) < δ) := by
  sorry -- **Issue #22**

/-- Lemma 4.5 (continuous-function-approximation-subdivision) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that for a given
continuous function `f` the function values on the parts of the subdivision are smaller than
a given `ε > 0`. -/
lemma forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous {D : Set ℝ} (D_dense : Dense D)
    {f : ℝ → ℝ} (f_cont : Continuous f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b)
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), ∀ x ∈ Icc (cs (Fin.castAdd _ j)) (cs j.succ),
        ∀ y ∈ Icc (cs (Fin.castAdd _ j)) (cs j.succ), dist (f x) (f y) < ε) := by
  let I : Set ℝ := Icc a b
  have hI_compact : IsCompact I := isCompact_Icc
  have hI_nonempty : I.Nonempty := nonempty_Icc.mpr (le_of_lt a_lt_b)
  have hf_cont_I : ContinuousOn f I := f_cont.continuousOn
  have hf_unif_cont : UniformContinuousOn f I :=
    hI_compact.uniformContinuousOn_of_continuous hf_cont_I
  have h_δ : ∃ δ > 0, ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (f x) (f y) < ε := by
    rw [Metric.uniformContinuousOn_iff] at hf_unif_cont
    exact hf_unif_cont ε ε_pos
  obtain ⟨δ, hδ_pos, hδ⟩ := h_δ
  obtain ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_diff⟩ :=
    forall_exists_subdivision_diff_lt_of_dense D_dense ha hb a_lt_b hδ_pos
  have h_cs_bound : ∀ i : Fin k, ∀ x ∈ Icc (cs (Fin.castAdd _ i)) (cs i.succ), ∀ y ∈ Icc (cs (Fin.castAdd _ i)) (cs i.succ), dist (f x) (f y) < ε := by
    intro i x hx y hy
    have hx_I : x ∈ I := by
      have h_lower : a ≤ cs (Fin.castAdd _ i) := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hx
    have hy_I : y ∈ I := by
      have h_lower : a ≤ cs (Fin.castAdd _ i) := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hy
    have h_dist_xy : dist x y < δ := by
      have h_bound : dist x y ≤ cs i.succ - cs (Fin.castAdd _ i) := by exact Real.dist_le_of_mem_Icc hx hy
      exact lt_of_le_of_lt h_bound (h_cs_diff i)
    exact hδ x hx_I y hy_I h_dist_xy
  exact ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_bound⟩

open MeasureTheory in
/-- Preliminary to Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (a_le_b : a ≤ b) (α : E) :
    ∫ x, (indicator (Ioc a b) (fun _ ↦ α)) x ∂ F.measure =
      (F b - F a) • α := by
  simp only [integral_indicator (show MeasurableSet (Ioc a b) from measurableSet_Ioc),
             integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
  congr
  simp [Measure.real, F.toStieltjesFunction.measure_Ioc a b,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono a_le_b))]

/-- Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_sum_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : Type*} {s : Finset κ} (as : κ → ℝ) (bs : κ → ℝ) (h : ∀ j, as j ≤ bs j) (α : κ → E) :
    ∫ x, ((∑ j ∈ s, indicator (Ioc (as j) (bs j)) (fun _ ↦ α j)) x) ∂ F.measure =
      ∑ j ∈ s, (F (bs j) - F (as j)) • α j := by
  -- It may be worthwhile to think about an improved phrasing of this.
  -- The previous lemma `CumulativeDistributionFunction.integral_indicator_eq` should be
  -- the key anyway.
  have h_int_sum_change : ∫ (x : ℝ), (∑ j ∈ s, (Ioc (as j) (bs j)).indicator (fun x => α j)) x ∂F.measure  = ∑ j ∈ s, ∫ (x : ℝ), (Ioc (as j) (bs j)).indicator (fun x => α j) x ∂F.measure  := by
    rw [← MeasureTheory.integral_finset_sum]
    simp_all only [Finset.sum_apply]
    intro j _
    exact (MeasureTheory.integrable_const (α j)).indicator measurableSet_Ioc
  rw [h_int_sum_change]
  congr
  ext j
  exact F.integral_indicator_eq (h j) _

open MeasureTheory Topology

/-- Theorem 4.8 (convergence-in-distribution-with-cdf) in blueprint:
Convergence of a sequence of c.d.f.s pointwise at all continuity points of the limit c.d.f. imply
convergence in distribution of the corresponding Borel probability measures on `ℝ`. -/
theorem tendsto_of_forall_continuousAt_tendsto_cdf
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : ∀ x, ContinuousAt μ.cdf x → Tendsto (fun n ↦ (μs n).cdf x) atTop (𝓝 (μ.cdf x))) :
    Tendsto μs atTop (𝓝 μ) := by
  sorry -- **Issue #20** (a big one)

end weak_convergence_cdf



section levy_prokhorov_metric

open MeasureTheory Filter Topology

variable (F G :CumulativeDistributionFunction)

namespace CumulativeDistributionFunction

lemma tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto (fun i ↦ (Fs i).probabilityMeasure) atTop (𝓝 G.probabilityMeasure)
      ↔ ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  constructor
  · intro h x hGx
    have key := @tendsto_apply_of_tendsto_of_continuousAt ℕ atTop
                (fun i ↦ (Fs i).probabilityMeasure) G.probabilityMeasure h x
    simp_all
  · intro h
    apply tendsto_of_forall_continuousAt_tendsto_cdf
    simpa using h

noncomputable def equiv_levyProkhorov :
    CumulativeDistributionFunction ≃ LevyProkhorov (ProbabilityMeasure ℝ) :=
  equiv_probabilityMeasure.trans LevyProkhorov.toMeasureEquiv.symm

noncomputable instance : MetricSpace CumulativeDistributionFunction := by
  apply MetricSpace.induced equiv_levyProkhorov
  · intro F G h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using h
  · exact LevyProkhorov.levyProkhorovDist_metricSpace_probabilityMeasure

noncomputable def homeomorph_levyProkhorov :
    CumulativeDistributionFunction ≃ₜ LevyProkhorov (ProbabilityMeasure ℝ) :=
  Equiv.toHomeomorphOfIsInducing equiv_levyProkhorov ⟨rfl⟩

noncomputable def homeomorph_probabilityMeasure :
    CumulativeDistributionFunction ≃ₜ ProbabilityMeasure ℝ :=
  homeomorph_levyProkhorov.trans LevyProkhorov.probabilityMeasureHomeomorph.symm

lemma homeomorph_probabilityMeasure_apply_eq (F : CumulativeDistributionFunction) :
    homeomorph_probabilityMeasure F = F.probabilityMeasure :=
  rfl

/-- The standard characterization of convergence of cumulative distribution functions. -/
lemma tendsto_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto Fs atTop (𝓝 G) ↔
      ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  rw [← tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto]
  constructor
  · intro h
    simp_rw [← homeomorph_probabilityMeasure_apply_eq]
    apply homeomorph_probabilityMeasure.continuous.continuousAt.tendsto.comp h
  · intro h
    convert homeomorph_probabilityMeasure.symm.continuous.continuousAt.tendsto.comp h
    · ext1 i; simp [← homeomorph_probabilityMeasure_apply_eq]
    · simp [← homeomorph_probabilityMeasure_apply_eq]

end CumulativeDistributionFunction

end levy_prokhorov_metric



section continuous_mulAction

namespace CumulativeDistributionFunction

lemma continuous_mulAction :
    Continuous fun (⟨A, F⟩ : AffineIncrEquiv × CumulativeDistributionFunction) ↦ A • F := by
  rw [continuous_iff_seqContinuous]
  intro AFs BG h_lim
  rw [tendsto_iff_forall_continuousAt_tendsto]
  intro x hBGx
  simp only [Function.comp_apply, mulAction_apply_eq]
  sorry -- **Issue #54** (action-on-cdf-continuous)

end CumulativeDistributionFunction

end continuous_mulAction
