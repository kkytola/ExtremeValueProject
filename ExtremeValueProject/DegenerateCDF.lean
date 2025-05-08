/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
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
      constructor
      · intro h
        exact ne_zero_of_eq_one h
      · intro hx
        cases is_degen x
        · contradiction
        · assumption

    have approaches_zero := isGLB_of_tendsto_atBot F.mono F.tendsto_atBot
    have reaches_zero : ∃ x : ℝ, F x = 0 := by
      rw [← not_forall_not]
      intro h
      have F_one : F.toFun = fun (x : ℝ) => 1 := by
        funext x
        rw [obs]
        exact h x
      rw [F_one, range_const] at approaches_zero
      have := IsGLB.unique approaches_zero isGLB_singleton
      norm_num at this

    have approaches_one := isLUB_of_tendsto_atTop F.mono F.tendsto_atTop
    have reaches_one : ∃ x : ℝ, F x = 1 := by
      rw [← not_forall_not]
      intro h
      have F_zero : F.toFun = fun (x : ℝ) => 0 := by
        funext x
        simp only [obs, not_not] at h
        exact h x
      rw [F_zero, range_const] at approaches_one
      have := IsLUB.unique approaches_one isLUB_singleton
      norm_num at this

    have bounded_below : BddBelow {x : ℝ | F x = 1} := by
      unfold BddBelow
      obtain ⟨x₀, h⟩ := reaches_zero
      use x₀
      intro a (ha : F a = 1)
      apply le_of_lt
      apply Monotone.reflect_lt F.mono
      rw [h, ha]
      norm_num

    let x₀ := sInf {x : ℝ | F x = 1}
    have one_after_x₀ : ∀ x > x₀, F x = 1 := by
      intro x hx
      apply le_antisymm
      · exact apply_le_one F x
      · obtain ⟨x₁, ⟨is_one : F x₁ = 1, lt_x⟩⟩ := exists_lt_of_csInf_lt reaches_one hx
        rw [← is_one]
        exact F.mono (le_of_lt lt_x)
    have one_after_x₀': F '' Ioi x₀ = {1} := by
      rw [← Set.Nonempty.image_const (show (Ioi x₀).Nonempty from nonempty_Ioi)]
      exact Set.image_congr one_after_x₀
    have one_at_x₀ : F x₀ = 1 := by
      rw [← F.rightLim_eq, ← csInf_singleton 1, ← one_after_x₀']
      exact Monotone.rightLim_eq_sInf F.mono NeBot.ne'

    use x₀
    funext x
    unfold indicator
    simp only [mem_Ici]
    split
    · rename_i hx
      cases' lt_or_eq_of_le hx with x₀_lt x₀_eq
      · exact one_after_x₀ x x₀_lt
      · rw [← x₀_eq]
        exact one_at_x₀
    · rename_i hx
      rw [not_le] at hx
      rw [← Iff.not_left (obs x)]
      apply not_mem_of_lt_csInf hx bounded_below
  · intro ⟨x₀, h⟩ x
    rw [h]
    simp [lt_or_le]

-- TODO: This probably belongs to Mathlib?
lemma _root_.MeasureTheory.diracProba_apply' {X : Type*} [MeasurableSpace X] (x₀ : X)
    {s : Set X} (s_mble : MeasurableSet s) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  rw [diracProba, ProbabilityMeasure.mk_apply, Measure.dirac_apply' x₀ s_mble]
  unfold Set.indicator
  split <;> rfl

-- TODO: This probably also belongs to Mathlib? (Note slightly different hypotheses to the above.)
lemma _root_.MeasureTheory.diracProba_apply {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (x₀ : X) (s : Set X) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  rw [diracProba, ProbabilityMeasure.mk_apply, Measure.dirac_apply]
  unfold Set.indicator
  split <;> rfl

lemma cdf_diracProba_apply (x₀ x : ℝ) :
    (diracProba x₀).cdf x = if x < x₀ then 0 else 1 := by
  unfold ProbabilityMeasure.cdf FiniteMeasure.cdf
  simp
  rw [diracProba_apply x₀]
  unfold Set.indicator
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
  sorry -- **Issue #12**

end CumulativeDistributionFunction

end degenerate_cdf
