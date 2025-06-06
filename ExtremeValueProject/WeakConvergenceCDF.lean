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
      (∀ (j : Fin k), cs j.succ - cs j < δ) := by
  let k := Nat.ceil ((b - a) / δ) + 1
  have k_pos : 0 < k := by
    exact Nat.zero_lt_succ ⌈(b - a) / δ⌉₊
  let ε := min ((δ - (b - a) / k) / 2) (((b - a) / k) / 2)
  have ε_pos : 0 < ε := by
    apply lt_min
    · apply half_pos
      refine sub_pos.mpr ?_
      refine (div_lt_comm₀ δ_pos ?_).mp ?_
      · exact Nat.cast_pos'.mpr k_pos
      · have h: ⌈(b - a) / δ⌉₊ < ⌈(b - a) / δ⌉₊ + 1 := by
          exact lt_add_one ⌈(b - a) / δ⌉₊
        exact Nat.lt_of_ceil_lt h
    · apply half_pos
      refine div_pos ?_ ?_
      · exact sub_pos.mpr a_lt_b
      · exact Nat.cast_pos'.mpr k_pos
  let cs₀ : Fin (k + 1) → ℝ := fun i ↦ a + (b - a) * i / k
  have cs₀_0 : cs₀ 0 = a := by simp [cs₀]
  have cs₀_last : cs₀ (Fin.last k) = b := by
    simp [cs₀, Fin.last]
  have cs₀_mono : Monotone cs₀ := by
    intro i j hij
    apply add_le_add_left
    refine (div_le_div_iff_of_pos_right ?_).mpr ?_
    · exact Nat.cast_pos'.mpr k_pos
    · refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
      · exact Preorder.le_refl (b - a)
      · exact Nat.cast_le.mpr hij
      · refine sub_nonneg_of_le ?_
        exact le_of_lt a_lt_b
      · exact Nat.cast_nonneg' ↑j
  choose! cs' hcs_in_D hcs_Ioo using fun i =>
    Dense.exists_between D_dense (lt_add_of_pos_right (cs₀ i - ε / 2) ε_pos)
  let cs : Fin (k + 1) → ℝ := fun i =>
    if i = 0 then a else if i = Fin.last k then b else cs' i
  have hcs_bounds : ∀ i, cs₀ i - ε / 2 < cs i ∧ cs i < cs₀ i + ε / 2 := by
    intro i
    have h := hcs_Ioo i
    simp [Ioo, mem_setOf] at h
    cases' h with h1 h2
    constructor
    · by_cases h0 : i = 0
      · simp [h0, cs, cs₀_0]
        exact ε_pos
      · by_cases hlast : i = Fin.last k
        · simp [hlast, cs, cs₀_last]
          by_cases hk : k = 0
          · have k_pos_1 := k_pos
            rw [hk] at k_pos_1
            exact (StrictAnti.lt_iff_lt fun ⦃a b⦄ a => k_pos_1).mp k_pos_1
          · rw [if_neg hk]
            linarith
        · simp [cs, h0, hlast]
          exact h1
    · by_cases h0 : i = 0
      · simp [h0, cs, cs₀_0]
        exact ε_pos
      · by_cases hlast : i = Fin.last k
        · simp [hlast, cs, cs₀_last]
          by_cases hk : k = 0
          · have k_pos_1 := k_pos
            rw [hk] at k_pos_1
            exact (StrictAnti.lt_iff_lt fun ⦃a b⦄ a => k_pos_1).mp k_pos_1
          · rw [if_neg hk]
            linarith
        · simp [cs, h0, hlast]
          have : cs₀ i - ε / 2 + ε = cs₀ i + ε / 2 := by
            ring
          rw [this] at h2
          exact h2
  have fin_last_ne_zero {k : ℕ} (hk : 0 < k) : (Fin.last k : Fin (k + 1)) ≠ 0 := by
    intro h
    have val_eq : (Fin.last k).val = (0 : ℕ) := congr_arg Fin.val h
    rw [Fin.last] at val_eq
    simp at val_eq
    rw [val_eq] at hk
    contradiction
  have cs_last_b : cs (Fin.last k) = b := by
    simp [cs, fin_last_ne_zero k_pos]
  use k, cs
  constructor
  · -- ⊢ cs 0 = a
    exact rfl
  · constructor
    · -- ⊢ cs (Fin.last k) = b
      exact cs_last_b
    · constructor
      · -- ⊢ Monotone cs
        intro i j hij
        by_cases hije : i = j
        · rw [hije]
        · have h1 : cs i < cs₀ i + ε  / 2 := (hcs_bounds i).2
          have h2 : cs j > cs₀ j - ε / 2 := (hcs_bounds j).1
          have h3 : cs₀ j - cs₀ i - ε > 0 := by
            simp only [cs₀]
            simp
            field_simp
            unfold ε
            apply lt_of_le_of_lt (min_le_right _ _)
            have : ((b - a) * ↑↑j - (b - a) * ↑↑i) / ↑k = ((b - a) * (↑↑j - ↑↑i)) / ↑k := by
              ring
            rw [this]
            have htest1 : (b - a) / ↑k / 2 < (b - a) / ↑k := by 
              refine _root_.half_lt_self ?_
              refine div_pos ?_ ?_
              · exact sub_pos.mpr a_lt_b
              · exact Nat.cast_pos'.mpr k_pos
            have htest2 : (b - a) / ↑k ≤ (b - a) * (↑↑j - ↑↑i) / ↑k := by
              refine (div_le_div_iff_of_pos_right ?_).mpr ?_
              · exact Nat.cast_pos'.mpr k_pos
              · refine (div_le_iff₀' ?_).mp ?_
                · exact sub_pos.mpr a_lt_b
                · have : (b - a) / (b - a) = 1 := by
                    refine div_self ?_
                    refine Ne.symm (ne_of_lt ?_)
                    exact sub_pos.mpr a_lt_b
                  rw [this]
                  refine le_sub_iff_add_le'.mpr ?_
                  have hij' : i < j := lt_of_le_of_ne hij hije
                  have hmm1 : i < j → i + 1 ≤ j := by
                    exact fun a => Fin.add_one_le_of_lt hij'
                  apply hmm1 at hij'
                  have hmm2 : i + 1 ≤ j → ↑i + 1 ≤ ↑j := by
                    refine fun a => ?_
                    · exact_mod_cast hij'
                  apply hmm2 at hij'
                  have hmm2 : (i : ℝ) + 1 ≤ (j : ℝ) := by 
                    -- this is clearly true, but my 'lean online' doesn't work well, so I leave 'sorry'
                    sorry
                  exact hmm2
            have htest3 : (b - a) / ↑k / 2 < (b - a) * (↑↑j - ↑↑i) / ↑k := by
              exact gt_of_ge_of_gt htest2 htest1
            apply htest3
          have h4 : cs j - cs i > cs₀ j - ε / 2 - (cs₀ i + ε / 2) := by
            exact sub_lt_sub h2 h1
          have h5 : cs₀ j - ε / 2 - (cs₀ i + ε / 2) = cs₀ j - cs₀ i - ε := by
            ring
          have h6 : cs j - cs i > cs₀ j - cs₀ i - ε := by
            exact lt_of_eq_of_lt (id (Eq.symm h5)) h4
          have h7 : cs j - cs i > 0 := by
            exact gt_trans h6 h3
          have h8 : cs i < cs j := by
            exact lt_add_neg_iff_lt.mp h7
          exact le_of_lt h8
      · constructor
        · -- ⊢ ∀ (k : Fin (k + 1)), cs k ∈ D
          intro i
          by_cases hi0 : i = 0
          · rw [hi0]
            exact ha
          · by_cases hilast : i = Fin.last k
            · rw [hilast]
              by_cases hk : k = 0
              · have k_pos_1 := k_pos
                rw [hk] at k_pos_1
                contradiction
              · rw [cs_last_b]
                exact hb
            · simp [cs, hi0, hilast]
              exact hcs_in_D i
        · -- ⊢ ∀ (j : Fin k), cs j.succ - cs ↑↑j < δ
          intro j
          have h_bound_succ := hcs_bounds j.succ
          have h_bound_j := hcs_bounds j
          rcases h_bound_succ with ⟨h_succ_lt, h_succ_gt⟩
          rcases h_bound_j with ⟨h_j_lt, h_j_gt⟩
          have h1 : cs j.succ < cs₀ j.succ + ε / 2 := by
            exact h_succ_gt
          have h2 : cs j > cs₀ j - ε / 2 := by
            exact h_j_lt
          have h21 : - cs j < - cs₀ j + ε / 2:= by
            apply neg_lt_neg at h2
            rw [neg_sub] at h2
            have : ε / 2 - cs₀ ↑↑j = -cs₀ ↑↑j + ε / 2 := by
              ring
            rw [← this]
            exact h2
          have h3 : cs j.succ + (- cs j) < (cs₀ j.succ + ε / 2) + (- cs₀ j + ε / 2) := by
            have htest {a b c d : ℝ} (hab : a < b) (hcd : c < d) : a + c < b + d := by
              exact add_lt_add hab hcd
            exact htest h1 h21
          have h33 : cs j.succ - cs j < cs₀ j.succ + ε - cs₀ j := by
            rw [←sub_eq_add_neg] at h3
            have h333 : (cs₀ j.succ + ε / 2) + (- cs₀ j + ε / 2) = cs₀ j.succ + ε - cs₀ j := by
              linarith
            rw [← h333] at ⊢
            exact h3
          have h4t : cs₀ j.succ + ε - cs₀ j = cs₀ j.succ - cs₀ j  + ε := by
            linarith
          have h4 : cs₀ j.succ - cs₀ j  + ε  < δ := by
            refine lt_tsub_iff_left.mp ?_
            have h41 : cs₀ j.succ - cs₀ j = (b - a) / k := by
              simp only [cs₀]
              simp
              ring
            rw [h41]
            unfold ε
            apply lt_of_le_of_lt (min_le_left _ _)
            apply @_root_.half_lt_self
            refine sub_pos.mpr ?_
            refine (div_lt_comm₀ ?_ δ_pos).mpr ?_
            · exact Nat.cast_pos'.mpr k_pos
            · refine Nat.lt_of_ceil_lt ?_
              exact lt_add_one ⌈(b - a) / δ⌉₊
          have h5 : cs j.succ - cs j  < cs₀ j.succ - cs₀ j  + ε := by
            exact lt_of_lt_of_eq h33 h4t
          have h55 : cs j.succ - cs j  < δ := by
            exact gt_trans h4 h5
          exact h55

/-- Lemma 4.5 (continuous-function-approximation-subdivision) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that for a given
continuous function `f` the function values on the parts of the subdivision are smaller than
a given `ε > 0`. -/
lemma forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous {D : Set ℝ} (D_dense : Dense D)
    {f : ℝ → ℝ} (f_cont : Continuous f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b)
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), ∀ x ∈ Icc (cs j) (cs j.succ), ∀ y ∈ Icc (cs j) (cs j.succ),
        dist (f x) (f y) < ε) := by
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
  have h_cs_bound : ∀ i : Fin k, ∀ x ∈ Icc (cs i) (cs i.succ), ∀ y ∈ Icc (cs i) (cs i.succ), dist (f x) (f y) < ε := by
    intro i x hx y hy
    have hx_I : x ∈ I := by
      have h_lower : a ≤ cs i := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hx
    have hy_I : y ∈ I := by
      have h_lower : a ≤ cs i := by simpa [← h_cs_0] using h_cs_mono (Fin.zero_le _)
      have h_upper : cs i.succ ≤ b := by simpa [← h_cs_last] using h_cs_mono (Fin.le_last i.succ)
      exact Icc_subset_Icc h_lower h_upper hy
    have h_dist_xy : dist x y < δ := by
      have h_bound : dist x y ≤ cs i.succ - cs i := by exact Real.dist_le_of_mem_Icc hx hy
      exact lt_of_le_of_lt h_bound (h_cs_diff i)
    exact hδ x hx_I y hy_I h_dist_xy
  exact ⟨k, cs, h_cs_0, h_cs_last, h_cs_mono, h_cs_D, h_cs_bound⟩

/-- Preliminary to Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (a_le_b : a ≤ b) (α : E) :
    ∫ x, (indicator (Ioc a b) (fun _ ↦ α)) x ∂ F.measure =
      (F b - F a) • α := by
  have h_meas : MeasurableSet (Ioc a b) := measurableSet_Ioc
  rw [MeasureTheory.integral_indicator h_meas, MeasureTheory.integral_const]
  have h_cdf : F.measure (Ioc a b) = ENNReal.ofReal (F b - F a) :=
    F.toStieltjesFunction.measure_Ioc a b
  congr
  simp [h_cdf, ENNReal.toReal_ofReal (sub_nonneg.mpr (F.mono a_le_b))]

/-- Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_sum_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {κ : Type*} {s : Finset κ} (as : κ → ℝ) (bs : κ → ℝ) (h : ∀ j, as j ≤ bs j) (α : κ → E) :
    ∫ x, ((∑ j ∈ s, indicator (Ioc (as j) (bs j)) (fun _ ↦ α j)) x) ∂ F.measure =
      ∑ j in s, (F (bs j) - F (as j)) • α j := by
  -- It may be worthwhile to think about an improved phrasing of this.
  -- The previous lemma `CumulativeDistributionFunction.integral_indicator_eq` should be
  -- the key anyway.
  have h_int_sum_change : ∫ (x : ℝ), (∑ j ∈ s, (Ioc (as j) (bs j)).indicator (fun x => α j)) x ∂F.measure  = ∑ j ∈ s, ∫ (x : ℝ), (Ioc (as j) (bs j)).indicator (fun x => α j) x ∂F.measure  := by
    rw [← MeasureTheory.integral_finset_sum]
    simp_all only [measurableSet_Ioc, implies_true, Finset.sum_apply, MeasureTheory.integral_indicator_const]
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
  equiv_probabilityMeasure.trans (LevyProkhorov.equiv (ProbabilityMeasure ℝ)).symm

noncomputable instance : MetricSpace CumulativeDistributionFunction := by
  apply MetricSpace.induced equiv_levyProkhorov
  · intro F G h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using h
  · exact levyProkhorovDist_metricSpace_probabilityMeasure

noncomputable def homeomorph_levyProkhorov :
    CumulativeDistributionFunction ≃ₜ LevyProkhorov (ProbabilityMeasure ℝ) :=
  Equiv.toHomeomorphOfIsInducing equiv_levyProkhorov ⟨rfl⟩

noncomputable def homeomorph_probabilityMeasure :
    CumulativeDistributionFunction ≃ₜ ProbabilityMeasure ℝ :=
  homeomorph_levyProkhorov.trans homeomorph_probabilityMeasure_levyProkhorov.symm

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
    · ext1 i
      exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl
    · exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl

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
