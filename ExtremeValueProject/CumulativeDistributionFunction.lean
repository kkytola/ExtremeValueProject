/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.MeasureTheory.Measure.Portmanteau



section cdf_def

open MeasureTheory Topology Filter Set ENNReal NNReal

/-- The c.d.f. of a finite measure on ℝ. -/
private def MeasureTheory.FiniteMeasure.cdf' (μ : FiniteMeasure ℝ) : ℝ → ℝ := fun x ↦ μ (Iic x)

/-- The c.d.f. of a finite measure on ℝ is an increasing function. -/
private lemma MeasureTheory.FiniteMeasure.monotone_cdf' (μ : FiniteMeasure ℝ) :
    Monotone μ.cdf' :=
  fun _ _ h ↦ apply_mono _ (Iic_subset_Iic.mpr h)

/-- The c.d.f. of a measure on ℝ is a right continuous function. -/
private lemma _root_.MeasureTheory.Measure.right_continuous_cdf'
    (μ : Measure ℝ) (x : ℝ) (h_ex_fin : ∃ (y : ℝ), x < y ∧ μ (Iic y) ≠ ∞) :
    ContinuousWithinAt (fun z ↦ μ (Iic z)) (Ici x) x := by
  have obs_Inter : Iic x = ⋂ (y : ℝ) (_ : y > x), Iic y := by
    refine subset_antisymm ?_ ?_
    · simpa using fun _ hy ↦ Iic_subset_Iic.mpr hy.le
    · intro y hy
      simp only [gt_iff_lt, mem_iInter, mem_Iic] at hy
      exact le_of_forall_gt_imp_ge_of_dense hy
  have mbles : ∀ y, x < y → NullMeasurableSet (Iic y) μ :=
    fun y _ ↦ (measurableSet_Iic).nullMeasurableSet
  have key := tendsto_measure_biInter_gt mbles (fun y z _ hyz ↦ Iic_subset_Iic.mpr hyz) h_ex_fin
  simp_rw [← obs_Inter] at key
  intro V hV
  obtain ⟨y, x_lt_y, Ioo_x_y_subset⟩ : ∃ u, x < u ∧ Ioo x u ⊆ ⇑μ ∘ Iic ⁻¹' V := by
    simpa [mem_nhdsGT_iff_exists_Ioo_subset] using key hV
  simp only [mem_nhdsGE_iff_exists_Ico_subset, mem_map, mem_Ioi, exists_prop]
  refine ⟨y, ⟨x_lt_y, ?_⟩⟩
  intros z hz
  by_cases h: x = z
  · simp only [←h, mem_preimage, mem_of_mem_nhds hV]
  · exact Ioo_x_y_subset <| show z ∈ Ioo x y from ⟨lt_of_le_of_ne hz.1 h, hz.2⟩

#check FiniteMeasure.self_eq_mass_mul_normalize
-- TODO: The @[simp] -tag in `FiniteMeasure.self_eq_mass_mul_normalize` is very bad.

/-- The c.d.f. of a finite measure on ℝ is a right continuous function. -/
private lemma MeasureTheory.FiniteMeasure.right_continuous_cdf'
    (μ : FiniteMeasure ℝ) (x : ℝ) :
    ContinuousWithinAt (fun z ↦ μ (Iic z)) (Ici x) x := by
  have key := MeasureTheory.Measure.right_continuous_cdf' μ x ?_
  swap
  · exact ⟨x + 1, ⟨by linarith, measure_ne_top (↑μ) (Iic (x + 1))⟩⟩
  apply ContinuousWithinAt.comp (β := ℝ≥0∞)
    (f := fun z ↦ μ (Iic z)) (g := ENNReal.toNNReal) (t := {u | u ≠ ∞})
  · apply ENNReal.continuousOn_toNNReal
    simpa only [ennreal_mass] using coe_ne_top
  · simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using key
  · simp only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    intro z _
    simp

private lemma MeasureTheory.FiniteMeasure.right_continuous_cdf
    (μ : FiniteMeasure ℝ) (x : ℝ) :
    ContinuousWithinAt (fun z ↦ (μ (Iic z) : ℝ)) (Ici x) x := by
  have key := μ.right_continuous_cdf' x
  apply ContinuousWithinAt.comp (γ := ℝ)
    (f := fun z ↦ μ (Iic z)) (g := fun p ↦ p) (t := univ) ?_ key ?_
  · exact Continuous.continuousWithinAt NNReal.continuous_coe
  · intro z _
    simp

/-- The cumulative distribution function of a finite measure on ℝ. -/
def MeasureTheory.FiniteMeasure.cdf (μ : FiniteMeasure ℝ) : StieltjesFunction where
  toFun := fun x ↦ μ (Iic x)
  mono' := fun _ _ h ↦ apply_mono _ (Iic_subset_Iic.mpr h)
  right_continuous' := MeasureTheory.FiniteMeasure.right_continuous_cdf μ

/-- The type of cumulative distribution functions of Borel probability measures on ℝ. -/
@[ext] structure CumulativeDistributionFunction extends StieltjesFunction where
  tendsto_atTop : Tendsto toFun atTop (𝓝 (1 : ℝ))
  tendsto_atBot : Tendsto toFun atBot (𝓝 (0 : ℝ))

namespace CumulativeDistributionFunction

instance : Coe CumulativeDistributionFunction StieltjesFunction where
  coe := CumulativeDistributionFunction.toStieltjesFunction

instance : CoeFun CumulativeDistributionFunction (fun _ ↦ ℝ → ℝ) where
  coe F := F.toFun

lemma apply_nonneg (F : CumulativeDistributionFunction) (x : ℝ) :
    0 ≤ F x := by
  exact F.mono'.le_of_tendsto F.tendsto_atBot x

lemma apply_le_one (F : CumulativeDistributionFunction) (x : ℝ) :
    F x ≤ 1 := by
  have F_mono: Monotone F := by
    exact F.mono'

  have F_tendsto_top: Tendsto F atTop (𝓝 (1 : ℝ)) := by
    exact F.tendsto_atTop

  exact Monotone.ge_of_tendsto F_mono F_tendsto_top x

lemma apply_eq_measure_Iic (F : CumulativeDistributionFunction) (x : ℝ) :
    F x = ENNReal.toReal (F.measure (Iic x)) := by
  simp only [StieltjesFunction.measure_Iic F F.tendsto_atBot x, sub_zero,
             ENNReal.toReal_ofReal (F.apply_nonneg x)]

/-- The cumulative distribution function of a probability measure on ℝ. -/
def _root_.MeasureTheory.ProbabilityMeasure.cdf (μ : ProbabilityMeasure ℝ) : CumulativeDistributionFunction where
  toFun := μ.toFiniteMeasure.cdf
  mono' := StieltjesFunction.mono (FiniteMeasure.cdf μ.toFiniteMeasure)
  right_continuous' := StieltjesFunction.right_continuous' (FiniteMeasure.cdf μ.toFiniteMeasure)
  tendsto_atTop := sorry -- **Issue #10**
  tendsto_atBot := sorry -- **Issue #10**

lemma _root_.MeasureTheory.ProbabilityMeasure.cdf_apply_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    μ.cdf x = μ (Iic x) := by rfl

lemma _root_.MeasureTheory.ProbabilityMeasure.cdf_toStieltjesFunction_apply_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    μ.cdf.toStieltjesFunction x = μ (Iic x) := by rfl

instance isProbabilityMeasure_measure_coe (F : CumulativeDistributionFunction) :
    IsProbabilityMeasure F.measure := by
  constructor
  rw [@StieltjesFunction.measure_univ F 0 1 F.tendsto_atBot F.tendsto_atTop]
  simp only [sub_zero, ofReal_one]

/-- The measure associated to the cdf of a probability measure is the same probability measure. -/
lemma _root_.MeasureTheory.ProbabilityMeasure.measure_cdf (μ : ProbabilityMeasure ℝ) :
    (μ.cdf : StieltjesFunction).measure = μ := by
  refine Measure.ext_of_Iic (μ.cdf : StieltjesFunction).measure μ (fun x ↦ ?_)
  simp only [StieltjesFunction.measure_Iic _ (ProbabilityMeasure.cdf μ).tendsto_atBot,
    μ.cdf_toStieltjesFunction_apply_eq x, sub_zero, ofReal_coe_nnreal, ne_eq,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

/-- A bijective correspondence between `CumulativeDistributionFunction`s and Borel
`ProbabilityMeasure`s on ℝ. -/
noncomputable def equiv_probabilityMeasure :
    CumulativeDistributionFunction ≃ ProbabilityMeasure ℝ where
  toFun := fun F ↦ ⟨F.measure, by infer_instance⟩
  invFun := fun μ ↦ μ.cdf
  left_inv := by
    intro F
    ext x
    simp [F.apply_eq_measure_Iic x, ProbabilityMeasure.cdf_toStieltjesFunction_apply_eq]
    rfl
  right_inv := by
    intro μ
    apply Subtype.ext
    apply μ.measure_cdf

lemma continuousAt_iff (F : CumulativeDistributionFunction) (x : ℝ) :
    ContinuousAt F x ↔ F.measure {x} = 0 := by
  rw [StieltjesFunction.measure_singleton]
  rw [Monotone.continuousAt_iff_leftLim_eq_rightLim F.mono']
  sorry -- **Issue #11**

/-- Lemma 4.7 (cdf-convergence-from-convergence-in-distribution) in blueprint:
Convergence in distribution of a sequence of Borel probability measures on `ℝ` implies that the
corresponding c.d.f.s converge pointwise at all continuity points of the limit c.d.f. -/
lemma tendsto_apply_of_tendsto_of_continuousAt {ι : Type*} {L : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} (weak_lim : Tendsto μs L (𝓝 μ))
    {x : ℝ} (cont : ContinuousAt μ.cdf x) :
    Tendsto (fun i ↦ (μs i).cdf x) L (𝓝 (μ.cdf x)) := by
  convert (NNReal.continuous_coe.tendsto _).comp <|
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto weak_lim ?_
  simp only [nonempty_Ioi, frontier_Iic']
  have aux := (μ.cdf.continuousAt_iff x).mp cont
  rw [ProbabilityMeasure.measure_cdf μ] at aux
  exact (ProbabilityMeasure.null_iff_toMeasure_null μ {x}).mpr aux

end CumulativeDistributionFunction

end cdf_def
