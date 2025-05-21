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
    G' x = 0 := by
  sorry

open AffineIncrEquiv Set Countable Monotone in
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
    G' x = 1 := by
  have (ε : ℝ) (ε_pos : ε > 0) : G' x > 1 - ε := by

    have dense_cont_pts (H : CumulativeDistributionFunction) :
        Dense {x | ContinuousAt H x} := by
      set S := {x : ℝ | ¬ContinuousAt H x} with hS
      have : Countable S := countable_not_continuousAt H.mono'
      have : Dense Sᶜ := dense_compl (𝕜 := ℝ) this
      simp only [compl, hS, mem_setOf_eq, not_not] at this
      assumption

    -- Choose `x'` s.t. `β < x' < x` and `G'` is continuous at `x'`
    have := (dense_cont_pts G').inter_open_nonempty (Ioo β x)
      isOpen_Ioo (nonempty_Ioo.mpr x_gt)
    obtain ⟨x', ⟨x'_gt, x'_lt⟩, x'_cont⟩ := this
    simp only [mem_setOf_eq] at x'_cont

    -- Choose `z'` s.t. `G(z') > 1 - ε'` where `ε' := ε/2`
    set ε' := ε/2 with hε'
    have G_lim := G.tendsto_atTop
    simp only [tendsto_atTop_nhds] at G_lim
    set I := {y | y > 1 - ε'} with hI
    have : 1 ∈ I := by
      simp only [mem_setOf_eq, sub_lt_self_iff, I, ε']
      positivity
    specialize G_lim I this isOpen_Ioi
    obtain ⟨z', G_lim⟩ := G_lim
    specialize G_lim z' (by linarith)
    simp only [hI, mem_setOf_eq] at G_lim

    -- Choose `z` s.t. `G(z) > 1 - ε'` and `G` is continuous at `z`
    have := (dense_cont_pts G).inter_open_nonempty {z | z' < z}
      isOpen_Ioi nonempty_Ioi
    obtain ⟨z, z_gt, z_cont⟩ := this
    simp only [hI, mem_setOf_eq] at z_gt
    simp only [mem_setOf_eq] at z_cont
    have Gz_gt : 1 - ε' < G z := calc
      1 - ε' < G z' := G_lim
      _ ≤ G z := G.mono' (by linarith)

    -- `Aₙ(z) → β`
    have : Tendsto (λ n ↦ a n * z) atTop (𝓝 (0 * z)) := by
      exact Tendsto.mul_const z a_lim
    simp only [zero_mul] at this
    have A_lim : Tendsto (λ n ↦ a n * z + b n) atTop (𝓝 (0 + β)) := by
      exact Tendsto.add this b_lim
    simp only [zero_add] at A_lim

    -- `Aₙ(z) < x'` for large `n`
    simp only [tendsto_atTop_nhds] at A_lim
    specialize A_lim {y | y < x'} x'_gt isOpen_Iio
    simp only [mem_setOf_eq] at A_lim

    -- `1 - ε' < Fₙ(z)` for large `n`
    specialize F_lim z z_cont
    simp only [tendsto_atTop_nhds] at F_lim
    specialize F_lim {y | 1 - ε' < y} Gz_gt isOpen_Ioi
    simp only [mem_setOf_eq] at F_lim

    -- Shorthand `Fₙ' = Aₙ.Fₙ`
    set F' : ℕ → CumulativeDistributionFunction :=
      λ n ↦ (mkOfCoefs (a_pos n) (b n)) • (F n) with hF'

    -- Assume the opposite to get
    -- `Fₙ'(x') < 1 - ε'` for large `n`
    by_contra
    specialize F_lim' x' x'_cont
    simp only [tendsto_atTop_nhds] at F_lim'
    have := calc
      G' x' ≤ G' x := by exact G'.mono (by linarith)
      _ < 1 - ε' := by linarith
    specialize F_lim' {y | y < 1 - ε'} this isOpen_Iio
    simp only [mem_setOf_eq] at F_lim'

    -- Specialize convergences
    obtain ⟨NA, A_lim⟩ := A_lim
    obtain ⟨NF, F_lim⟩ := F_lim
    obtain ⟨NF', F_lim'⟩ := F_lim'
    set n := NA + NF + NF' with hn
    specialize A_lim n (by linarith)
    specialize F_lim n (by linarith)
    specialize F_lim' n (by linarith)

    -- Contradiction `1 - ε' < Fₙ(z) ≤ Fₙ'(x') < 1 - ε'`
    have := calc
      (F n) z = F' n (a n * z + b n) := by
        simp only [hF', mulAction_apply_eq, apply_eq, inv_coefs_fst,
          coefs_fst_mkOfCoefs, inv_coefs_snd, coefs_snd_mkOfCoefs, neg_mul]
        ring_nf
        have := a_pos n
        field_simp
      _ ≤ F' n x' := (F' n).mono' (by linarith)
    linarith
  have : G' x ≥ 1 := by
    by_contra
    have := this ((1 - G' x) / 2) (by linarith)
    linarith
  have : G' x ≤ 1 := by exact apply_le_one G' x
  linarith

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
    G'.IsDegenerate := by
  rw [isDegenerate_iff]
  use β
  suffices (∀ x < β, G' x = 0) ∧ (∀ x > β, G' x = 1) by
    funext x
    by_cases x_lt : x < β
    · have obs : ¬ x ∈ Set.Ici β := by simpa using x_lt
      simp [obs, this.1 _ x_lt]
    · have obs : x ∈ Set.Ici β := by simpa using x_lt
      by_cases x_eq : x = β
      · simp only [obs, Set.indicator_of_mem]
        have key := G'.right_continuous
        have key' : ContinuousWithinAt G' (Set.Ioi β) β := continuousWithinAt_Ioi_iff_Ici.mpr (key β)
        have aux : ∀ᶠ x in (𝓝[>] β), G' x = 1 := by
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
