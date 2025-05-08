/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation


section preliminaries_for_type_of_cdf

open Topology Filter

open scoped Topology


/-- Construct an orientation preserving affine isomorphism `x ↦ a * x + b` of `ℝ` from
coefficients `a > 0` and `b ∈ ℝ`. -/
noncomputable def orientationPreservingAffineEquiv.mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    orientationPreservingAffineEquiv where
  val := AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b
  property := by
    change (AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b).IsOrientationPreserving
    rw [AffineEquiv.IsOrientationPreserving]
    convert a_pos
    simp

lemma orientationPreservingAffineEquiv.mkOfCoefs_apply {a : ℝ} (a_pos : 0 < a) (b : ℝ) (x : ℝ) :
    (mkOfCoefs a_pos b).val x = a * x + b :=
  rfl

lemma orientationPreservingAffineEquiv.mkOfCoefs_val {a : ℝ} (a_pos : 0 < a) (b : ℝ) (x : ℝ) :
    (mkOfCoefs a_pos b).val = AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b :=
  rfl

namespace CumulativeDistributionFunction

lemma exists₂_continuousAt_of_not_isDegenerate
    (F : CumulativeDistributionFunction) (hF : ¬ F.IsDegenerate) :
    ∃ x₁ x₂, (x₁ < x₂) ∧ (0 < F x₁) ∧ (F x₂ < 1) ∧ (ContinuousAt F x₁) ∧ (ContinuousAt F x₂) := by
  sorry -- **Issue #38**

lemma unique_orientationPreservingAffineEquiv_smul_eq_not_isDegenerate
    {F G : CumulativeDistributionFunction} {A₁ A₂ : AffineIncrEquiv}
    (hG : ¬ G.IsDegenerate) (h₁ : A₁ • F = G) (h₂ : A₂ • F = G) :
    A₁ = A₂ := by
  sorry -- **Issue #39**

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 0` for all `x < β`. -/
lemma apply_eq_zero_of_tendsto_of_lt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_lt : x < β) :
    G x = 0 := by
  sorry

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 1` for all `x > β`. -/
lemma apply_eq_one_of_tendsto_of_gt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_gt : β < x) :
    G x = 1 := by
  sorry

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'` is degenerate (a delta mass at `β`). -/
lemma isDegenerate_of_tendsto_shrinking
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x))) :
    G.IsDegenerate := by
  rw [isDegenerate_iff]
  use β
  suffices (∀ x < β, G x = 0) ∧ (∀ x > β, G x = 1) by
    funext x
    by_cases x_lt : x < β
    · have obs : ¬ x ∈ Set.Ici β := by simpa using x_lt
      simp [obs, this.1 _ x_lt]
    · have obs : x ∈ Set.Ici β := by simpa using x_lt
      by_cases x_eq : x = β
      · simp only [obs, Set.indicator_of_mem]
        have key := G.right_continuous
        have key' : ContinuousWithinAt G (Set.Ioi β) β := continuousWithinAt_Ioi_iff_Ici.mpr (key β)
        have aux : ∀ᶠ x in (𝓝[>] β), G x = 1 := by
          filter_upwards [self_mem_nhdsWithin] with x hx using this.2 _ hx
        have wow := Tendsto.congr' aux key'
        rw [tendsto_const_nhds_iff] at wow
        rw [x_eq, wow]
      have x_gt : β < x := lt_of_le_of_ne (le_of_not_lt x_lt) ((Ne.eq_def _ _).symm ▸ x_eq).symm
      simp [obs, this.2 _ x_gt]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact apply_eq_zero_of_tendsto_of_lt a_pos a_lim b_lim F_lim F_lim' hx
  · intro x hx
    exact apply_eq_one_of_tendsto_of_gt a_pos a_lim b_lim F_lim F_lim' hx

open orientationPreservingAffineEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` where `G` is nondegenerate and if `Aₙ`
is a sequence of oriented affine isomorphisms with scaling coefficients `aₙ → +∞`,
then `Aₙ • Fₙ` cannot converge to any c.d.f. -/
lemma not_tendsto_cdf_of_expanding_of_tendsto_not_isDegenerate
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (hG : ¬ G.IsDegenerate) {A : ℕ → AffineIncrEquiv}
    (a_lim : Tendsto (fun n ↦ (A n).val.toAffineMap.coefs_of_field.1) atTop atTop) :
    ¬ ∀ x, ContinuousAt G' x → Tendsto (fun n ↦ ((A n) • (F n)) x) atTop (𝓝 (G' x)) := by
  sorry -- **Issue #40**

end CumulativeDistributionFunction

end preliminaries_for_type_of_cdf


section type_of_cdf

end type_of_cdf
