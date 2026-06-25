/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.AffineTransformation
import ExtremeValueProject.PseudoInverses
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog


section auxiliary_log

-- TODO: I tend to think this should be added to Mathlib.
lemma ENNReal.ofReal_log_eq_toENNReal_log_ofReal {x : ℝ} (x_pos : 0 < x) :
    ENNReal.ofReal x.log = (ENNReal.ofReal x).log.toENNReal := by
  simp [show ¬ (x ≤ 0) by linarith]

end auxiliary_log


section extend_cdf

namespace CumulativeDistributionFunction

/-- The natural extension of a c.d.f. to a function `[-∞,+∞] → [0,+∞]`. -/
noncomputable def extend (F : CumulativeDistributionFunction) (x : EReal) :
    ENNReal := match x with
  | ⊥ => 0
  | ⊤ => 1
  | some (some ξ) => ENNReal.ofReal (F ξ)

@[simp] lemma extend_bot (F : CumulativeDistributionFunction) :
    F.extend ⊥ = 0 :=
  rfl

@[simp] lemma extend_top (F : CumulativeDistributionFunction) :
    F.extend ⊤ = 1 :=
  rfl

@[simp] lemma extend_ofReal (F : CumulativeDistributionFunction)
    (x : ℝ) :
    F.extend x = ENNReal.ofReal (F x) :=
  rfl

lemma extend_nonneg (F : CumulativeDistributionFunction) :
    0 ≤ F.extend := by
  intro x
  match x with
  | ⊥ => simp
  | ⊤ => simp
  | some (some ξ) =>
    change 0 ≤ F.extend ξ
    have : 0 ≤ F ξ := apply_nonneg F ξ
    simp_all

lemma extend_le_one (F : CumulativeDistributionFunction) :
    F.extend ≤ 1 := by
  intro x
  match x with
  | ⊥ => simp
  | ⊤ => simp
  | some (some ξ) =>
    change F.extend ξ ≤ 1
    simpa using apply_le_one F ξ

lemma extend_mono (F : CumulativeDistributionFunction) :
    Monotone F.extend := by
  intro x y hxy
  match x with
  | ⊥ => simp
  | ⊤ => simp [eq_top_iff.mpr hxy]
  | some (some ξ) => match y with
    | ⊥ => exact absurd (le_bot_iff.mp hxy) (EReal.coe_ne_bot ξ)
    | ⊤ => simpa using extend_le_one _ _
    | some (some η) =>
      have ξ_le_η : ξ ≤ η := EReal.coe_le_coe_iff.mp hxy
      exact ENNReal.ofReal_le_ofReal (F.mono ξ_le_η)

lemma extend_affine (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    (A • F).extend = F.extend ∘ (A⁻¹).extend := by
  ext x
  simp only [extend, mulAction_apply_eq, Function.comp_apply]
  match x with
  | ⊥ =>
    rw [AffineIncrEquiv.extend_bot]; rfl
  | ⊤ =>
    rw [AffineIncrEquiv.extend_top]; rfl
  | some (some ξ) =>
    have aux : (A • F).extend ξ = F.extend ((A⁻¹).extend ξ) := by
      simp only [extend_ofReal, mulAction_apply_eq, AffineEquiv.extend_ofReal]
      congr
    exact aux

lemma extend_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.extend ⊥ := by
  sorry -- **Issue #30**

lemma extend_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.extend ⊤ := by
  sorry -- **Issue #30**

lemma extend_continuousAt (F : CumulativeDistributionFunction) {x : ℝ}
    (hx : ContinuousAt F x) :
    ContinuousAt F.extend x := by
  sorry -- **Issue #30**

lemma extend_continuousAt_iff (F : CumulativeDistributionFunction) (x : ℝ) :
    ContinuousAt F.extend x ↔ ContinuousAt F x := by
  sorry -- (maybe could be done together with issue 30)

open MeasureTheory

/-- If `F` is the c.d.f. of a probability measure `μ`, then `F x = μ (-∞, x]` for all `x ∈ ℝ`.
The natural analogue of this holds for the extension `F⁺` of `F` to `[-∞,+∞]`: we have
`F⁺ x = μ⁺ [-∞, x]` for all `x ∈ [-∞,+∞]`, where `μ⁺` is the push-forward measure of
`μ` along the inclusion `ℝ ↪ [-∞,+∞]`. -/
lemma extend_apply_eq_map_measure_Iic (F : CumulativeDistributionFunction) (x : EReal) :
    F.extend x = F.measure.map ((↑) : ℝ → EReal) (Set.Iic x) := by
  match x with
  | ⊥ =>
    rw [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    convert show 0 = F.measure ∅ by simp
    · simp
    · ext x ; simp
  | ⊤ =>
    rw [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    simp
  | some (some ξ) =>
    change F.extend ξ = F.measure.map ((↑) : ℝ → EReal) (Set.Iic ξ)
    have aux : F.measure.map ((↑) : ℝ → EReal) (Set.Iic ξ) = F.measure (Set.Iic ξ) := by
      simp [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    rw [aux, extend_ofReal, ← ENNReal.ofReal_toReal (measure_ne_top F.measure _)]
    congr
    exact F.apply_eq_measure_Iic ξ

end CumulativeDistributionFunction

end extend_cdf

noncomputable section transform_cdf
/-!
# Transformed cumulative distribution functions
-/

open Set ENNReal NNReal

section oneDivOneSub

/-- The function `ℝ≥0∞ → ℝ≥0∞` given by `p ↦ 1 / (1-p)`.  -/
def oneDivOneSubAux (p : ℝ≥0∞) := (1 : ℝ≥0∞) / (1 - p)

@[simp] lemma oneDivOneSubAux_zero :
    oneDivOneSubAux 0 = 1 := by
  simp [oneDivOneSubAux]

lemma oneDivOneSubAux_of_ge_one {p : ℝ≥0∞} (hp : 1 ≤ p) :
    oneDivOneSubAux p = ∞ := by
  simp only [oneDivOneSubAux, one_div, inv_eq_top, tsub_eq_zero_of_le hp]

@[simp] lemma oneDivOneSubAux_one :
    oneDivOneSubAux 1 = ∞ :=
  oneDivOneSubAux_of_ge_one (le_refl 1)

lemma oneDivOneSubAux_mono :
    Monotone oneDivOneSubAux := by
  intro p q hpq
  simp only [oneDivOneSubAux, one_div, ENNReal.inv_le_inv]
  exact tsub_le_tsub_left hpq 1

lemma oneDivOneSubAux_strictMonoOn :
    StrictMonoOn oneDivOneSubAux (Iic 1) := by
  intro p hp q hq hpq
  simp only [oneDivOneSubAux, one_div, ENNReal.inv_lt_inv]
  apply ENNReal.sub_lt_of_sub_lt hq (by left ; exact one_ne_top)
  convert hpq
  refine ENNReal.sub_sub_cancel one_ne_top hp

namespace CumulativeDistributionFunction

/-- An auxiliary transform of a cumulative distribution function `F` to a function
`[-∞,+∞] → [0,+∞]` by the formula `x ↦ 1 / (1 - F(x))`. -/
def oneDivOneSub (F : CumulativeDistributionFunction) :
    EReal → ℝ≥0∞ :=
  oneDivOneSubAux ∘ F.extend

lemma oneDivOneSub_apply (F : CumulativeDistributionFunction) (x : EReal) :
    F.oneDivOneSub x = 1 / (1 - F.extend x) :=
  rfl

@[simp] lemma oneDivOneSub_apply_bot (F : CumulativeDistributionFunction) :
    F.oneDivOneSub ⊥ = 1 := by
  simp [oneDivOneSub]

@[simp] lemma oneDivOneSub_apply_top (F : CumulativeDistributionFunction) :
    F.oneDivOneSub ⊤ = ∞ := by
  simp [oneDivOneSub]

@[simp] lemma oneDivOneSub_apply_ofReal (F : CumulativeDistributionFunction) (x : ℝ) :
    F.oneDivOneSub x = 1 / (1 - ENNReal.ofReal (F x)) :=
  rfl

lemma oneDivOneSub_mono (F : CumulativeDistributionFunction) :
    Monotone F.oneDivOneSub :=
  oneDivOneSubAux_mono.comp F.extend_mono

lemma oneDivOneSub_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivOneSub ⊥ := by
  sorry -- **Issue #31**

lemma oneDivOneSub_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivOneSub ⊤ := by
  sorry -- **Issue #31**

lemma oneDivOneSub_continuousAt (F : CumulativeDistributionFunction) {x : ℝ}
    (hx : ContinuousAt F x) :
    ContinuousAt F.oneDivOneSub x := by
  sorry -- **Issue #31**

lemma oneDivOneSub_continuousAt_iff (F : CumulativeDistributionFunction) (x : ℝ) :
    ContinuousAt F.oneDivOneSub x ↔ ContinuousAt F x := by
  sorry -- (maybe could be done together with issue 31)

lemma oneDivOneSub_affine (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    ((A • F).oneDivOneSub) = F.oneDivOneSub ∘ (A⁻¹).extend := by
  ext x
  simp [oneDivOneSub, extend_affine]

/-- A transform of a cumulative distribution function `F` to a function
`[0,+∞] → [-∞,+∞]`: the right-continuous inverse of the function `x ↦ 1 / (1 - F(x))`. -/
def rcInvOneDivOneSub (F : CumulativeDistributionFunction) :
    ℝ≥0∞ → EReal :=
  rcInv (F.oneDivOneSub)

lemma rcInvOneDivOneSub_mono (F : CumulativeDistributionFunction) :
    Monotone F.rcInvOneDivOneSub :=
  rcInv_mono F.oneDivOneSub

-- TODO: What is the good statement about continuity of F.rcInvOneDivOneSub at `u ∈ (1,+∞)`?
-- The hypothesis should be continuity and local increase of `F` at `F⁻¹ (1 - 1/u)`?

lemma rcInvOneDivOneSub_affine (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    ((A • F).rcInvOneDivOneSub) = A.extend ∘ F.rcInvOneDivOneSub := by
  rw [rcInvOneDivOneSub, oneDivOneSub_affine]
  apply rcInv_comp F.oneDivOneSub (A⁻¹).extend ?_
  exact AffineMap.leftOrdContinuous_extend _

end CumulativeDistributionFunction

end oneDivOneSub

section oneDivNegLog

/-- The function `ℝ≥0∞ → ℝ≥0∞` given by `p ↦ 1 / log(p⁻¹) = 1 / (-log(p))`. -/
def oneDivNegLogAux (p : ℝ≥0∞) : ℝ≥0∞ := 1 / (1/p).log.toENNReal

@[simp] lemma oneDivNegLogAux_eq_top_iff {p : ℝ≥0∞} :
    oneDivNegLogAux p = ∞ ↔ 1 ≤ p := by
  simp [oneDivNegLogAux, EReal.toENNReal_eq_zero_iff, log_le_zero_iff]

@[simp] lemma oneDivNegLogAux_eq_zero_iff {p : ℝ≥0∞} :
    oneDivNegLogAux p = 0 ↔ p = 0 := by
  simp [oneDivNegLogAux]

lemma oneDivNegLogAux_mono :
    Monotone oneDivNegLogAux := by
  intro p q hpq
  simp only [oneDivNegLogAux, one_div, ENNReal.inv_le_inv]
  exact EReal.toENNReal_le_toENNReal (by simp [hpq])

lemma oneDivNegLogAux_strictMonoOn :
    StrictMonoOn oneDivNegLogAux (Iic 1) := by
  intro p hp q hq hpq
  simp only [oneDivNegLogAux, one_div, ENNReal.inv_lt_inv]
  exact EReal.toENNReal_lt_toENNReal (by simpa using hq) (by simpa using hpq)

namespace CumulativeDistributionFunction

/-- An auxiliary transform of a cumulative distribution function `F` to a function
`[-∞,+∞] → [0,+∞]` by the formula `x ↦ 1 / log(F(x)⁻¹) = 1 / (-log(F(x))) `. -/
def oneDivNegLog (F : CumulativeDistributionFunction) :
    EReal → ℝ≥0∞ :=
  oneDivNegLogAux ∘ F.extend

lemma oneDivNegLog_apply (F : CumulativeDistributionFunction) (x : EReal) :
    F.oneDivNegLog x = 1 / (1 / (F.extend x)).log.toENNReal :=
  rfl

@[simp] lemma oneDivNegLog_apply_bot (F : CumulativeDistributionFunction) :
    F.oneDivNegLog ⊥ = 0 := by
  simp [oneDivNegLog]

@[simp] lemma oneDivNegLog_apply_top (F : CumulativeDistributionFunction) :
    F.oneDivNegLog ⊤ = ⊤ := by
  simp [oneDivNegLog]

lemma oneDivNegLog_mono (F : CumulativeDistributionFunction) :
    Monotone F.oneDivNegLog :=
  oneDivNegLogAux_mono.comp F.extend_mono

/-- A rewrite lemma for `CumulativeDistributionFunction.oneDivNegLog` in terms of `Real.log`
(assuming the c.d.f. value is positive, `F x > 0`, so real logarithm is well behaved).
Note, however, that this cannot be written with division in `ℝ` if `F x = 1`, because
of division by `log (F x) = 0`; instead, division in `ℝ≥0∞` must be used.
See `CumulativeDistributionFunction.oneDivNegLog_apply_ofReal_of_pos_of_lt_one` for a
(more useful) version assuming `0 < F x < 1`. -/
lemma oneDivNegLog_apply_ofReal_of_pos (F : CumulativeDistributionFunction) {x : ℝ}
    (Fx_pos : 0 < F x) :
    F.oneDivNegLog x = 1 / ENNReal.ofReal (Real.log (F x)⁻¹) := by
  have Fx_inv_ge_one : 1 ≤ (F x)⁻¹ := (one_le_inv₀ Fx_pos).mpr (show F x ≤ 1 from apply_le_one F x)
  have obs := ENNReal.ofReal_log_eq_toENNReal_log_ofReal (show 0 < (F x)⁻¹ by linarith)
  rw [oneDivNegLog, Function.comp_apply, oneDivNegLogAux, obs]
  simp [(ofReal_inv_of_pos Fx_pos).symm]

/-- A rewrite lemma for `CumulativeDistributionFunction.oneDivNegLog` in terms of `Real.log`
(assuming the c.d.f. value is nondegenerate, `0 < F x < 1`, so real logarithm and division by
it are well behaved). -/
lemma oneDivNegLog_apply_ofReal_of_pos_of_lt_one (F : CumulativeDistributionFunction) {x : ℝ}
    (Fx_pos : 0 < F x) (Fx_lt_one : F x < 1) :
    F.oneDivNegLog x = ENNReal.ofReal (1 / (Real.log (F x)⁻¹)) := by
  rw [oneDivNegLog_apply_ofReal_of_pos _ Fx_pos]
  simp only [one_div]
  have Fx_inv_gt_one : 1 < (F x)⁻¹ := (one_lt_inv₀ Fx_pos).mpr Fx_lt_one
  rw [ENNReal.ofReal_inv_of_pos (Real.log_pos Fx_inv_gt_one)]

lemma oneDivNegLog_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivNegLog ⊥ := by
  sorry -- **Issue #32**

lemma oneDivNegLog_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivNegLog ⊤ := by
  sorry -- **Issue #32**

lemma oneDivNegLog_continuousAt (F : CumulativeDistributionFunction) {x : ℝ}
    (hx : ContinuousAt F x) :
    ContinuousAt F.oneDivNegLog x := by
  sorry -- **Issue #32**

lemma oneDivNegLog_continuousAt_iff (F : CumulativeDistributionFunction) (x : ℝ) :
    ContinuousAt F.oneDivNegLog x ↔ ContinuousAt F x := by
  sorry -- (maybe could be done together with issue 32)

lemma oneDivNegLog_affine (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    ((A • F).oneDivNegLog) = F.oneDivNegLog ∘ (A⁻¹).extend := by
  ext x
  simp [oneDivNegLog, extend_affine]

/-- A transform of a cumulative distribution function `F` to a function
`[0,+∞] → [-∞,+∞]`: the right-continuous inverse of the function `x ↦ 1 / log(F(x)⁻¹)`. -/
def rcInvOneDivNegLog (F : CumulativeDistributionFunction) :
    ℝ≥0∞ → EReal :=
  rcInv (F.oneDivNegLog)

lemma rcInvOneDivNegLog_mono (F : CumulativeDistributionFunction) :
    Monotone F.rcInvOneDivNegLog :=
  rcInv_mono F.oneDivNegLog

lemma rcInvOneDivNegLog_affine (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    ((A • F).rcInvOneDivNegLog) = A.extend ∘ F.rcInvOneDivNegLog := by
  rw [rcInvOneDivNegLog, oneDivNegLog_affine]
  apply rcInv_comp F.oneDivNegLog (A⁻¹).extend ?_
  exact AffineMap.leftOrdContinuous_extend _

end CumulativeDistributionFunction

end oneDivNegLog


section equivalent_ev

open Topology Filter

lemma oneDivSub_limit_iff {F G : CumulativeDistributionFunction}
    (As : ℕ → AffineIncrEquiv) {x : ℝ} (hGx : G x ∈ Ioo 0 1) :
    (Tendsto (fun n ↦ 1/(n * (1 - (((As n) • F) x)))) atTop (𝓝 (1/(-(Real.log (G x))))))
      ↔ (Tendsto (fun (n : ℕ) ↦ (n : ℝ≥0∞)⁻¹ * (((As n) • F).oneDivOneSub x))
          atTop (𝓝 (G.oneDivNegLog x))) := by
  constructor
  · intro h
    have key := Tendsto.comp continuous_ofReal.continuousAt h
    rw [← Real.log_inv] at key
    have aux : ENNReal.ofReal (((1 : ℝ) / (Real.log ((G x)⁻¹)))) = G.oneDivNegLog x :=
      (G.oneDivNegLog_apply_ofReal_of_pos_of_lt_one hGx.1 hGx.2).symm
    rw [aux] at key
    have same : ∀ᶠ (n : ℕ) in atTop,
        (ENNReal.ofReal ∘ fun n ↦ 1 / (↑n * (1 - (As n • F) x))) n
          = (↑n)⁻¹ * (As n • F).oneDivOneSub x := by
      have aux_pos' : ∀ᶠ n in atTop, 0 < (1 - (As n • F).toStieltjesFunction x) := by
        have aux_nhd : Ioi 0 ∈ 𝓝 (1 / -Real.log (G x)) :=
          isOpen_Ioi.mem_nhds (by simpa using Real.log_neg hGx.1 hGx.2)
        filter_upwards [h aux_nhd, Ioi_mem_atTop 0] with n hn n_pos
        simp only [one_div, mul_inv_rev, mem_preimage, mem_Ioi] at hn n_pos
        rw [mul_pos_iff_of_pos_right (by simp [n_pos])] at hn
        exact Right.inv_pos.mp hn
      filter_upwards [Ioi_mem_atTop 0, aux_pos'] with n n_pos aux_pos
      simp only [CumulativeDistributionFunction.oneDivOneSub_apply_ofReal,
                 one_div, mul_inv_rev, Function.comp_apply]
      rw [mul_comm _ (_)⁻¹, ENNReal.ofReal_mul (by simp), ENNReal.ofReal_inv_of_pos aux_pos]
      rw [ENNReal.ofReal_sub _ ((As n • F).apply_nonneg x), ofReal_one]
      congr
      simp [ofReal_inv_of_pos (Nat.cast_pos'.mpr n_pos)]
    apply Tendsto.congr' same key
  · intro h
    have aux_nhd : {a | a ≠ ⊤} ∈ 𝓝 (G.oneDivNegLog x) :=
      isOpen_ne_top.mem_nhds (by simpa [CumulativeDistributionFunction.oneDivNegLog] using hGx.2)
    have key := Tendsto.comp (continuousOn_toReal.continuousAt aux_nhd) h
    convert key with n
    · simp only [one_div, mul_inv_rev, CumulativeDistributionFunction.oneDivOneSub_apply_ofReal,
                 Function.comp_apply, toReal_mul, toReal_inv, toReal_natCast]
      rw [mul_comm _ (_)⁻¹]
      congr
      rw [ENNReal.toReal_sub_of_le (ofReal_le_one.mpr (((As n) • F).apply_le_one x)) one_ne_top]
      simp only [toReal_one, _root_.sub_right_inj]
      rw [ENNReal.toReal_ofReal ((As n • F).apply_nonneg x)]
    · rw [← Real.log_inv, G.oneDivNegLog_apply_ofReal_of_pos_of_lt_one hGx.1 hGx.2, toReal_ofReal]
      simpa using Real.log_nonpos (G.apply_nonneg x) (G.apply_le_one x)

end equivalent_ev


end transform_cdf
