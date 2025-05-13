/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Väinö Mäkelä, ...
-/
import ExtremeValueProject.CumulativeDistributionFunction
import Mathlib.MeasureTheory.Measure.DiracProba



section degenerate_cdf

open MeasureTheory Topology Filter Set ENNReal NNReal

namespace CumulativeDistributionFunction

/-- A c.d.f. F is degenerate if its only possible values are 0 or 1. -/
def IsDegenerate (F : CumulativeDistributionFunction) : Prop :=
  ∀ x, F x = 0 ∨ F x = 1

lemma isDegenerate_def (F : CumulativeDistributionFunction) :
    F.IsDegenerate ↔ ∀ x, F x = 0 ∨ F x = 1 := by rfl

/-- A c.d.f. F is degenerate if and only if it jumps from 0 to 1 at some point x₀. -/
lemma isDegenerate_iff (F : CumulativeDistributionFunction) :
    F.IsDegenerate ↔ ∃ x₀, F.toFun = (Set.Ici x₀).indicator (fun _ ↦ 1) := by
  constructor
  · intro is_degen
    have obs (x : ℝ) : F x = 1 ↔ F x ≠ 0 := by
      refine ⟨fun hx ↦ ne_zero_of_eq_one hx, fun hx ↦ ?_⟩
      cases is_degen x
      · contradiction
      · assumption
    have reaches_zero : ∃ x : ℝ, F x = 0 := by
      by_contra! con
      simp only [← obs] at con
      have oops : (0 : ℝ) = 1 := tendsto_nhds_unique F.tendsto_atBot ?_
      · norm_num at oops
      · exact Tendsto.congr (fun x ↦ (con x).symm) tendsto_const_nhds
    have reaches_one : ∃ x : ℝ, F x = 1 := by
      by_contra! con
      have oops : (1 : ℝ) = 0 :=
        tendsto_nhds_unique F.tendsto_atTop (Tendsto.congr ?_ tendsto_const_nhds)
      · norm_num at oops
      · intro x
        symm
        simpa only [con x, or_false] using is_degen x
    have bounded_below : BddBelow {x : ℝ | F x = 1} := by
      obtain ⟨x₀, h⟩ := reaches_zero
      use x₀
      intro x (hx : F x = 1)
      exact (Monotone.reflect_lt F.mono (by norm_num [h, hx])).le
    let x₀ := sInf {x : ℝ | F x = 1}
    have one_after_x₀ : ∀ x > x₀, F x = 1 := by
      intro x hx
      apply le_antisymm (apply_le_one F x)
      obtain ⟨x₁, ⟨is_one : F x₁ = 1, lt_x⟩⟩ := exists_lt_of_csInf_lt reaches_one hx
      simpa only [← is_one] using F.mono lt_x.le
    have one_after_x₀' : F '' Ioi x₀ = {1} := by
      rw [← Set.Nonempty.image_const (show (Ioi x₀).Nonempty from nonempty_Ioi)]
      exact Set.image_congr one_after_x₀
    have one_at_x₀ : F x₀ = 1 := by
      rw [← F.rightLim_eq, ← csInf_singleton 1, ← one_after_x₀']
      exact Monotone.rightLim_eq_sInf F.mono NeBot.ne'
    use x₀
    funext x
    simp only [indicator, mem_Ici]
    by_cases hx : x₀ ≤ x
    · simp only [hx, ↓reduceIte]
      cases' lt_or_eq_of_le hx with x₀_lt x₀_eq
      · exact one_after_x₀ x x₀_lt
      · simpa [← x₀_eq] using one_at_x₀
    · simp only [hx, ↓reduceIte]
      rw [← Iff.not_left (obs x)]
      apply not_mem_of_lt_csInf (not_le.mp hx) bounded_below
  · intro ⟨x₀, h⟩ x
    simp [h, lt_or_le]

-- TODO: This probably belongs to Mathlib?
lemma _root_.MeasureTheory.diracProba_apply' {X : Type*} [MeasurableSpace X] (x₀ : X)
    {s : Set X} (s_mble : MeasurableSet s) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  rw [diracProba, ProbabilityMeasure.mk_apply, Measure.dirac_apply' x₀ s_mble]
  unfold indicator
  split <;> rfl

-- TODO: This probably also belongs to Mathlib? (Note slightly different hypotheses to the above.)
lemma _root_.MeasureTheory.diracProba_apply {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (x₀ : X) (s : Set X) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  rw [diracProba, ProbabilityMeasure.mk_apply, Measure.dirac_apply]
  unfold indicator
  split <;> rfl

lemma cdf_diracProba_apply (x₀ x : ℝ) :
    (diracProba x₀).cdf x = if x < x₀ then 0 else 1 := by
  simp [ProbabilityMeasure.cdf, FiniteMeasure.cdf, diracProba_apply x₀, indicator]
  by_cases h : x₀ ≤ x
  · simp [not_lt_of_ge h]
  · simp [lt_of_not_ge h]

/-- The c.d.f. of Dirac delta mass at a point x₀ is degenerate. -/
lemma diracProba_is_degenerate (x₀ : ℝ) :
    IsDegenerate (diracProba x₀).cdf := by
  rw [isDegenerate_iff]
  use x₀
  ext x
  simp [cdf_diracProba_apply, indicator]
  by_cases hx : x < x₀
  · have aux : ¬ (x₀ ≤ x) := by exact not_le_of_lt hx
    simp [hx, aux]
  · have aux : x₀ ≤ x := by exact le_of_not_lt hx
    simp [hx, aux]

/-- If the c.d.f. of a probability measure μ on ℝ is degenerate, then μ is the Dirac delta mass
at some point x₀. -/
lemma eq_diracProba_of_isDegenerate (μ : ProbabilityMeasure ℝ) (degen : μ.cdf.IsDegenerate) :
    ∃ x₀, μ = diracProba x₀ := by
  rw [isDegenerate_iff] at degen
  obtain ⟨x₀, h⟩ := degen
  use x₀
  ext s hs
  rw [diracProba_toMeasure_apply, indicator, Pi.one_apply]
  simp only [show ⇑μ.cdf = (fun x ↦ (μ (Iic x)).toReal)
              by ext x ; rw [ProbabilityMeasure.cdf_apply_eq]] at h
  have measure_Iic_eq_one : μ.toMeasure (Iic x₀) = 1 := by
    simpa only [← toReal_eq_one_iff, mem_Ici, le_refl, indicator_of_mem] using congr_fun h x₀
  have measure_Iio_eq_zero : μ.toMeasure (Iio x₀) = 0 := by
    apply measure_null_of_locally_null
    intro x (x_lt_x₀ : x < x₀)
    obtain ⟨x₁, ⟨x_lt_x₁, x₁_lt_x₀⟩⟩ := exists_between x_lt_x₀
    use Iic x₁, mem_inf_of_left (Iic_mem_nhds x_lt_x₁)
    simpa [x₁_lt_x₀] using congr_fun h x₁
  have measure_x₀_eq_one : μ.toMeasure {x₀} = 1 := by
    rw [← Iic_diff_Iio_same,
        measure_diff Iio_subset_Iic_self nullMeasurableSet_Iio (measure_ne_top μ (Iio x₀)),
        measure_Iic_eq_one,
        measure_Iio_eq_zero,
        tsub_zero]
  have measure_eq_one_of_contains_x₀ {s : Set ℝ} (hx₀ : x₀ ∈ s) : μ.toMeasure s = 1 := by
    rw [← one_le_prob_iff, ← measure_x₀_eq_one]
    apply measure_mono
    simpa only [singleton_subset_iff] using hx₀
  by_cases hx₀ : x₀ ∈ s
  · simpa [hx₀] using measure_eq_one_of_contains_x₀ hx₀
  · simpa [hx₀, ← prob_compl_eq_one_iff hs] using measure_eq_one_of_contains_x₀ hx₀

end CumulativeDistributionFunction

end degenerate_cdf
