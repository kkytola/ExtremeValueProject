/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.RCLike.Basic

open Filter Set Metric Topology Asymptotics

open scoped Topology

section generalities

-- TODO: Should something like this be in Mathlib?
lemma NormedSpace.tendsto_zero_iff_isLittleO_one {ι : Type*} {L : Filter ι}
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f : ι → E} :
    L.Tendsto f (𝓝 0) ↔ (fun i ↦ f i) =o[L] (fun _ ↦ (1 : ℝ)) := by
  simp only [Metric.tendsto_nhds, gt_iff_lt, dist_zero_right, isLittleO_iff, norm_one, mul_one]
  constructor
  · intro h_tends ε ε_pos
    filter_upwards [h_tends ε ε_pos] with i hi using hi.le
  · intro h_littleO ε ε_pos
    filter_upwards [h_littleO (c := ε / 2) (by linarith)] with i hi
    exact lt_of_le_of_lt hi (by linarith)

-- TODO: Should something like this be in Mathlib?
lemma NormedSpace.tendsto_of_tendsto_of_sub_isLittleO_one {ι : Type*} {L : Filter ι}
    {E : Type*} {v : E} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f g : ι → E}
    (hf : L.Tendsto f (𝓝 v)) (hfg : (fun i ↦ f i - g i) =o[L] (fun _ ↦ (1 : ℝ))) :
    L.Tendsto g (𝓝 v) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have hfv : L.Tendsto (fun i ↦ f i - v) (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hf
  rw [tendsto_zero_iff_isLittleO_one] at hfv
  simpa only [sub_sub_sub_cancel_left, isLittleO_one_iff] using hfv.sub hfg

-- TODO: Should something like this be in Mathlib?
-- Or maybe this is too specialized?
-- Mathlib already has `tendsto_sub_nhds_zero_iff`, but this conbines an `IsLittleO` spelling.
lemma NormedSpace.tendsto_iff_sub_const_isLittleO_one {ι : Type*} {L : Filter ι}
    {E : Type*} {v : E} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f : ι → E} :
    L.Tendsto f (𝓝 v) ↔ (fun i ↦ f i - v) =o[L] (fun _ ↦ (1 : ℝ)) := by
  simpa [← tendsto_zero_iff_isLittleO_one] using tendsto_sub_nhds_zero_iff.symm

end generalities
