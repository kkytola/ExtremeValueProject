/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.AffineTransformation
import ExtremeValueProject.TransformedCDF
import Mathlib

open Filter Set Metric Topology Asymptotics

open scoped Topology

section generalities

-- TODO: Should something like this be in Mathlib?
lemma NormedSpace.tendsto_of_tendsto_of_sub_isLittleO_one {ι : Type*} {L : Filter ι}
    {E : Type*} {v : E} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f g : ι → E}
    (hf : L.Tendsto f (𝓝 v)) (hfg : (fun i ↦ f i - g i) =o[L] (fun _ ↦ (1 : ℝ))) :
    L.Tendsto g (𝓝 v) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hfv : L.Tendsto (fun i ↦ f i - v) (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hf
  rw [← isLittleO_one_iff (F := ℝ)] at hfv
  simpa only [sub_sub_sub_cancel_left, isLittleO_one_iff] using hfv.sub hfg

-- TODO: Should something like this be in Mathlib?
-- Or maybe this is too specialized?
-- Mathlib already has `tendsto_sub_nhds_zero_iff`, but this conbines an `IsLittleO` spelling.
lemma NormedSpace.tendsto_iff_sub_const_isLittleO_one {ι : Type*} {L : Filter ι}
    {E : Type*} {v : E} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f : ι → E} :
    L.Tendsto f (𝓝 v) ↔ (fun i ↦ f i - v) =o[L] (fun _ ↦ (1 : ℝ)) := by
  simp only [isLittleO_one_iff, tendsto_sub_nhds_zero_iff]

end generalities


section limit_relation_manipulation_lemmas

lemma eventually_mul_norm_lt_of_tendsto_smul_of_norm_lt {ι : Type*} {L : Filter ι}
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) {m : ι → ℝ}
    {a : ι → ℝ} (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) {c : ℝ} (hc : ‖v‖ < c) :
    ∀ᶠ i in L, |m i| * ‖f (a i)‖ < c := by
  have norm_lim : L.Tendsto (fun i ↦ ‖m i • (f (a i))‖) (𝓝 ‖v‖) := by
    have obs := continuous_norm.continuousAt (x := v)
    simp only [ContinuousAt] at obs
    exact obs.comp ha
  simp only [norm_smul, Real.norm_eq_abs] at norm_lim
  have : Iio c ∈ 𝓝 ‖v‖ := Iio_mem_nhds (by linarith)
  filter_upwards [norm_lim this] with i hi using hi

lemma tendsto_norm_apply_zero_of_tendsto_atTop_of_tendsto_smul {ι : Type*} {L : Filter ι}
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) :
    L.Tendsto (fun i ↦ ‖f (a i)‖) (𝓝 0) := by
  have bdd : L.Eventually (fun i ↦ |m i| * ‖f (a i)‖ < ‖v‖ + 1) :=
    eventually_mul_norm_lt_of_tendsto_smul_of_norm_lt _ ha (by linarith)
  rw [Metric.tendsto_nhds]
  intro ε ε_pos
  have unbdd : L.Eventually (fun i ↦ m i ≥ (‖v‖ + 1) * ε⁻¹) := by
    exact Tendsto.eventually_ge_atTop m_to_infty ((‖v‖ + 1) * ε⁻¹)
  have unbdd' : L.Eventually (fun i ↦ |m i| ≥ (‖v‖ + 1) * ε⁻¹) := by
    filter_upwards [unbdd] with i hi using le_trans hi (le_abs_self (m i))
  filter_upwards [bdd, unbdd'] with i hib hiu
  simp only [dist_zero_right, norm_norm]
  have mi_pos : 0 < |m i| := by
    linarith [show 0 < (‖v‖ + 1) * ε⁻¹ from mul_pos (by positivity) (Right.inv_pos.mpr ε_pos)]
  apply lt_of_lt_of_le (show ‖f (a i)‖ < (‖v‖ + 1) / |m i| from (lt_div_iff₀' mi_pos).mpr hib)
  rw [div_le_iff₀ mi_pos]
  exact (div_le_iff₀' ε_pos).mp hiu

lemma tendsto_zero_of_tendsto_atTop_of_tendsto_smul {ι : Type*} {L : Filter ι}
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) {s : Set ℝ} (hs : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s)
    (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) :
    Tendsto a L (𝓝 0) := by
  have vanishing := tendsto_norm_apply_zero_of_tendsto_atTop_of_tendsto_smul f m_to_infty ha
  have vanishing' : Tendsto (fun i => f (a i)) L (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr vanishing
  simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, Metric.tendsto_nhds] at vanishing' hs ⊢
  intro δ δ_pos
  obtain ⟨ε, ε_pos, hε⟩ := hs δ δ_pos
  filter_upwards [a_in_s, vanishing' ε ε_pos] with i his hif using hε _ his hif

lemma sub_smul_deriv_isLittleO_of_tendsto_atTop_of_tendsto_smul_apply {ι : Type*} {L : Filter ι}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) (hf : f 0 = 0) {s : Set ℝ}
    (hs : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop) {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s)
    (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) {D : E} (hDf : HasDerivAt f D 0) :
    (fun i ↦ f (a i) - a i • D) =o[L] a := by
  have a_lim : Tendsto a L (𝓝 0) :=
    tendsto_zero_of_tendsto_atTop_of_tendsto_smul f hs m_to_infty a_in_s ha
  have hDf' : (fun x' => f x' - x' • D) =o[𝓝 0] (fun x' => x') := by
    have h := hDf.isLittleO
    simp only [hf, sub_zero] at h
    exact h
  rw [isLittleO_iff] at hDf' ⊢
  intro c c_pos
  specialize hDf' c_pos
  exact Eventually.filter_mono (tendsto_iff_comap.mp a_lim) (hDf'.comap a)

lemma eventually_norm_apply_ge_mul_self_of_tendsto_atTop_of_tendsto_smul_apply
    {ι : Type*} {L : Filter ι} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) (hf : f 0 = 0) {s : Set ℝ}
    (hs : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s)
    (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) {D : E}
    {C : ℝ} (C_lt_D : C < ‖D‖) (hDf : HasDerivAt f D 0) :
    ∀ᶠ i in L, ‖f (a i)‖ ≥ |a i| * C := by
  have key : (fun i ↦ f (a i) - a i • D) =o[L] a :=
    sub_smul_deriv_isLittleO_of_tendsto_atTop_of_tendsto_smul_apply _ hf hs m_to_infty a_in_s ha hDf
  rw [isLittleO_iff] at key
  filter_upwards [key (c := ‖D‖ - C) (by linarith)] with i hi
  have est : ‖f (a i)‖ ≥ ‖a i • D‖ - ‖f (a i) - a i • D‖ := by
    rw [show ‖f (a i)‖ = ‖a i • D + (f (a i) - a i • D)‖ by simp]
    exact norm_sub_le_norm_add (a i • D) (f (a i) - a i • D)
  have aux := sub_le_sub (le_refl ‖a i • D‖) hi
  simp only [norm_smul, mul_comm _ ‖a i‖, ← mul_sub] at aux
  simp only [Real.norm_eq_abs, sub_sub_cancel] at aux
  simp only [norm_smul, Real.norm_eq_abs, ge_iff_le, tsub_le_iff_right] at est
  exact aux.trans <| (sub_le_sub est (le_refl _)).trans (by simp)

lemma mul_isBigO_one_of_tendsto_atTop_of_tendsto_smul_apply {ι : Type*} {L : Filter ι} [NeBot L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E}
    (f : ℝ → E) (hf : f 0 = 0) {s : Set ℝ}
    (hs : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s)
    (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) {D : E} (D_ne_zero : D ≠ 0)
    (hDf : HasDerivAt f D 0) :
    (fun i ↦ m i * a i) =O[L] fun _ ↦ (1 : ℝ) := by
  have norm_D_pos : 0 < ‖D‖ := norm_pos_iff.mpr D_ne_zero
  have aux : ∀ᶠ i in L, ‖f (a i)‖ ≥ |a i| * (‖D‖/2) :=
    eventually_norm_apply_ge_mul_self_of_tendsto_atTop_of_tendsto_smul_apply _ hf hs
      m_to_infty a_in_s ha (show ‖D‖/2 < ‖D‖ by linarith) hDf
  have mfa_isBigO := Tendsto.isBigO_one ℝ ha
  simp only [isBigO_iff, norm_one, mul_one, norm_mul, Real.norm_eq_abs] at mfa_isBigO ⊢
  obtain ⟨C, hC⟩ := mfa_isBigO
  have C_nn : 0 ≤ C := by
    obtain ⟨j, hj⟩ := hC.exists
    exact (norm_nonneg _).trans hj
  use C * (2 * ‖D‖⁻¹)
  filter_upwards [aux, hC] with i hiz hiw
  simp only [norm_smul, Real.norm_eq_abs] at hiw
  have hiz' := (@le_div_iff₀ ℝ _ _ _ |a i| ‖f (a i)‖ (‖D‖ / 2) (by linarith)).mpr hiz
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at hiz'
  apply (mul_le_mul (le_refl |m i|) hiz' (abs_nonneg (a i)) (abs_nonneg (m i))).trans
  rw [← mul_assoc]
  apply mul_le_mul hiw (le_refl (2 * ‖D‖⁻¹)) _ C_nn
  exact mul_nonneg zero_le_two <| inv_nonneg.mpr (norm_nonneg D)

lemma tendsto_mul_smul_deriv_of_tendsto_atTop_of_tendsto_smul_apply
    {ι : Type*} {L : Filter ι} [NeBot L] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} (f : ℝ → E) (hf : f 0 = 0) {s : Set ℝ}
    (hs : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s)
    (ha : L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 v)) {D : E} (D_ne_zero : D ≠ 0)
    (hDf : HasDerivAt f D 0) :
    L.Tendsto (fun i ↦ (m i * a i) • D) (𝓝 v) := by
  have obs : (fun i ↦ f (a i) - a i • D) =o[L] a :=
    sub_smul_deriv_isLittleO_of_tendsto_atTop_of_tendsto_smul_apply _ hf hs m_to_infty a_in_s ha hDf
  have ma_isBigO : (fun i ↦ m i * a i) =O[L] fun _ ↦ (1 : ℝ) :=
    mul_isBigO_one_of_tendsto_atTop_of_tendsto_smul_apply f hf hs m_to_infty a_in_s ha D_ne_zero hDf
  have key₁ : (fun i ↦ (m i) • f (a i) - v) =o[L] (fun i ↦ (1 : ℝ)) :=
    NormedSpace.tendsto_iff_sub_const_isLittleO_one.mp ha
  have key₂ : (fun i ↦ (m i) • f (a i) - m i • (a i • D)) =o[L] (fun i ↦ (1 : ℝ)) := by
    have key₃ := (isBigO_refl m L).smul_isLittleO obs
    simp only [smul_sub, smul_eq_mul] at key₃
    exact key₃.trans_isBigO ma_isBigO
  have key := IsLittleO.sub key₁ key₂
  simp only [sub_sub_sub_cancel_left, isLittleO_one_iff, tendsto_sub_nhds_zero_iff] at key
  convert key using 1
  ext i
  exact mul_smul (m i) (a i) D

lemma tendsto_smul_self_iff_tendsto_of_ne_zero {ι : Type*} {L : Filter ι} [NeBot L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} {v : E} (v_ne_zero : v ≠ 0) {r : ι → ℝ} :
    L.Tendsto (fun i ↦ r i • v) (𝓝 (c • v)) ↔ L.Tendsto r (𝓝 c) := by
  constructor
  · intro rv_lim
    obtain ⟨φ, hφv⟩ : ∃ (φ : E →L[ℝ] ℝ), φ v = 1 := SeparatingDual.exists_eq_one v_ne_zero
    have hb : ContinuousAt φ (c • v) := φ.continuous.continuousAt
    rw [ContinuousAt] at hb
    have key : Tendsto (fun i ↦ φ (r i • v)) L (𝓝 (φ (c • v))) := hb.comp rv_lim
    simpa only [map_smul, hφv, smul_eq_mul, mul_one] using key
  · intro r_lim
    have key : ContinuousAt (fun (t : ℝ) ↦ t • v) c :=
      (continuous_smul.comp (Continuous.prodMk_left v)).continuousAt
    simp only [ContinuousAt] at key
    exact key.comp r_lim

lemma tendsto_smul_apply_smul_deriv_of_tendsto_atTop_of_tendsto_mul
    {ι : Type*} {L : Filter ι} [NeBot L] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : f 0 = 0) {s : Set ℝ} {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : ∀ᶠ i in L, a i ∈ s) {c : ℝ}
    (hma : L.Tendsto (fun i ↦ m i * a i) (𝓝 c)) {D : E} (hDf : HasDerivAt f D 0) :
    L.Tendsto (fun i ↦ m i • (f (a i))) (𝓝 (c • D)) := by
  have hDfa : (fun i ↦ f (a i) - a i • D) =o[L] a := by
    have a_lim : L.Tendsto a (𝓝 0) :=
      tendsto_zero_of_tendsto_atTop_of_tendsto_smul (v := c) id (by aesop) m_to_infty a_in_s hma
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero] at hDf
    simp only [zero_add, hf, sub_zero, ContinuousLinearMap.smulRight_apply,
               ContinuousLinearMap.one_apply] at hDf
    apply IsLittleO.comp_tendsto hDf a_lim
  have ma_isBigO : (fun i ↦ m i * a i) =O[L] fun _ ↦ (1 : ℝ) := by
    apply mul_isBigO_one_of_tendsto_atTop_of_tendsto_smul_apply (v := c) id rfl (by aesop)
            m_to_infty a_in_s ?_ one_ne_zero (hasDerivAt_id' 0)
    simpa [smul_eq_mul] using hma
  have key : (fun i ↦ (m i) • f (a i) - (m i * a i) • D) =o[L] (fun i ↦ (1 : ℝ)) := by
    have key' := (isBigO_refl m L).smul_isLittleO hDfa
    simp only [smul_sub, smul_eq_mul] at key'
    simpa [mul_smul] using key'.trans_isBigO ma_isBigO
  apply NormedSpace.tendsto_of_tendsto_of_sub_isLittleO_one (Tendsto.smul_const hma D)
  exact isLittleO_comm.mp key

lemma tendsto_smul_apply_smul_deriv_of_tendsto_atTop_of_tendsto_smul_apply_smul_deriv
    {ι : Type*} {L : Filter ι} [NeBot L] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₁ f₂ : ℝ → E) (hf₁ : f₁ 0 = 0) (hf₂ : f₂ 0 = 0) {s : Set ℝ}
    (hs₁ : ∀ δ > 0, ∃ ε > 0, ∀ x ∈ s, ‖f₁ x‖ < ε → x ∈ Metric.ball 0 δ)
    {m : ι → ℝ} (m_to_infty : L.Tendsto m atTop)
    {a : ι → ℝ} (a_in_s : L.Eventually fun i ↦ a i ∈ s) {c : ℝ}
    {D₁ D₂ : E} (D₁_ne_zero : D₁ ≠ 0) (hDf₁ : HasDerivAt f₁ D₁ 0) (hDf₂ : HasDerivAt f₂ D₂ 0)
    (ha : L.Tendsto (fun i ↦ m i • (f₁ (a i))) (𝓝 (c • D₁))) :
    L.Tendsto (fun i ↦ m i • (f₂ (a i))) (𝓝 (c • D₂)) := by
  have obs := tendsto_mul_smul_deriv_of_tendsto_atTop_of_tendsto_smul_apply f₁ hf₁ hs₁
                m_to_infty a_in_s ha D₁_ne_zero hDf₁
  have aux := (tendsto_smul_self_iff_tendsto_of_ne_zero D₁_ne_zero).mp obs
  simpa using tendsto_smul_apply_smul_deriv_of_tendsto_atTop_of_tendsto_mul f₂ hf₂
                m_to_infty a_in_s aux hDf₂

end limit_relation_manipulation_lemmas


section actual_limit_relation_manipulation

lemma ev_limit_iff_log_ev_limit {F G : CumulativeDistributionFunction}
    {As : ℕ → AffineIncrEquiv} {x : ℝ} (hGx : G x ∈ Ioo 0 1) :
    (Tendsto (fun n ↦ ((As n • F) x)^n) atTop (𝓝 (G x)))
      ↔ (Tendsto (fun n ↦ n * Real.log (((As n) • F) x)) atTop (𝓝 (Real.log (G x)))) := by
  constructor
  · intro h
    simp only [← Real.log_pow, ← Function.comp_def]
    apply Filter.Tendsto.comp ?_ h
    exact ContinuousAt.tendsto (Real.continuousAt_log (ne_of_gt hGx.left))
  · intro h
    apply Filter.Tendsto.comp (Continuous.tendsto Real.continuous_exp _) at h
    simp only [← Real.log_pow, Real.exp_log hGx.left] at h
    have obs : ∀ᶠ n in atTop, Real.exp (n * Real.log ((As n • F) x)) = ((As n • F) x) ^ n := by
      filter_upwards [h (Ioo_mem_nhds hGx.1 hGx.2), Ioi_mem_atTop 0] with n hn n_pos
      rw [mem_preimage, Function.comp_apply, Real.exp_log] at hn
      rw [← Real.log_pow, Real.exp_log (pow_pos ?_ _)]
      · apply lt_of_le_of_ne ((As n • F).apply_nonneg x)
        exact ((pow_ne_zero_iff ((show 0 < n from n_pos).ne).symm).mp hn.1.ne.symm).symm
      · apply pow_pos
        by_contra con
        simp [le_antisymm (not_lt.mp con) ((As n • F).apply_nonneg x)] at hn
    exact Tendsto.congr' obs (by simpa [Real.log_pow, Function.comp_def] using h)

lemma tendsto_one_of_ev_limit {F G : CumulativeDistributionFunction}
    {As : ℕ → AffineIncrEquiv} {x : ℝ} (hGx : G x ∈ Ioo 0 1)
    (h : Tendsto (fun n ↦ ((As n • F) x)^n) atTop (𝓝 (G x))) :
    Tendsto (fun n ↦ ((As n • F) x)) atTop (𝓝 1) := by
  sorry -- **Issue #28**

lemma log_ev_limit_iff_taylored_ev_limit {F G : CumulativeDistributionFunction}
    {As : ℕ → AffineIncrEquiv} {x : ℝ} (hGx : G x ∈ Ioo 0 1) :
    (Tendsto (fun n ↦ n * Real.log (((As n) • F) x)) atTop (𝓝 (Real.log (G x))))
      ↔ (Tendsto (fun n ↦ n * (1 - (((As n) • F) x))) atTop (𝓝 (-(Real.log (G x))))) := by
  sorry -- **Issue #27**

lemma taylored_ev_limit_iff_oneDivOneSub_limit {F G : CumulativeDistributionFunction}
    {As : ℕ → AffineIncrEquiv} {x : ℝ} (hGx : G x ∈ Ioo 0 1) :
    (Tendsto (fun n ↦ n * (1 - (((As n) • F) x))) atTop (𝓝 (-(Real.log (G x)))))
      ↔ (Tendsto (fun n ↦ 1/(n * (1 - (((As n) • F) x)))) atTop (𝓝 (1/(-(Real.log (G x)))))) := by
  simp only [one_div]
  have log_Gx_ne_zero : Real.log (G x) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hGx.1 hGx.2.ne
  have nlog_Gx_ne_zero := neg_ne_zero.mpr log_Gx_ne_zero
  constructor
  · intro h_lim
    exact Tendsto.inv₀ h_lim nlog_Gx_ne_zero
  · intro h_invlim
    simpa only [inv_inv] using Tendsto.inv₀ h_invlim (inv_ne_zero nlog_Gx_ne_zero)

open ENNReal

theorem tfae_ev_limit_relation {F G : CumulativeDistributionFunction}
    (As : ℕ → AffineIncrEquiv) {x : ℝ} (hGx : G x ∈ Ioo 0 1) :
    List.TFAE
      [Tendsto (fun n ↦ ((As n • F) x)^n) atTop (𝓝 (G x)),
       Tendsto (fun n ↦ n * Real.log (((As n) • F) x)) atTop (𝓝 (Real.log (G x))),
       Tendsto (fun n ↦ n * (1 - (((As n) • F) x))) atTop (𝓝 (-(Real.log (G x)))),
       Tendsto (fun n ↦ 1/(n * (1 - (((As n) • F) x)))) atTop (𝓝 (1/(-(Real.log (G x))))),
       Tendsto (fun (n : ℕ) ↦ (n : ℝ≥0∞)⁻¹ * (((As n) • F).oneDivOneSub x))
          atTop (𝓝 (G.oneDivNegLog x))] := by
  have one_iff_two := ev_limit_iff_log_ev_limit hGx (As := As) (F := F) (G := G)
  have two_iff_three := log_ev_limit_iff_taylored_ev_limit hGx (As := As) (F := F) (G := G)
  have three_iff_four := taylored_ev_limit_iff_oneDivOneSub_limit hGx (As := As) (F := F) (G := G)
  have four_iff_five := oneDivSub_limit_iff hGx (As := As) (F := F) (G := G)
  tfae_finish

end actual_limit_relation_manipulation
