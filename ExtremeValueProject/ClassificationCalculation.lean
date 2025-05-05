/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib

namespace ExtremeValueProject

section classification_calculation

open Real Set

#check Differentiable
#check deriv

#check ContDiff

/-- Lemma 3.1 (ode-of-order-two-for-Q) -/
lemma ode_of_order_two_for_Q
    {Q α : ℝ → ℝ} (Q_diffble : Differentiable ℝ Q) (hQ0 : Q 0 = 0)
    (hDQ0 : deriv Q 0 = 1) (Q_eqn : ∀ h s, Q (h + s) = Q h * α s + Q s) :
    ContDiff ℝ 2 Q ∧ (∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) := by
  sorry -- **Issue #23**

/-- Lemma 3.2 (solve-Q) -/
lemma solve_Q
    {Q : ℝ → ℝ} {γ : ℝ} (Q_diffble2 : ContDiff ℝ 2 Q) (hQ0 : Q 0 = 0) (hDQ0 : deriv Q 0 = 1)
    (hDQ_pos : ∀ s, 0 < deriv Q s)
    (Q_de : ∀ s, deriv (deriv Q) s = (deriv Q s) * (deriv (deriv Q) 0)) :
    Q = if γ = 0 then (fun s ↦ s) else (fun s ↦ (exp (γ * s) - 1) / γ) := by
  sorry -- **Issue #24**

/-- Lemma 3.4 (solve-E) -/
lemma solve_E
    {E A : ℝ → ℝ} {c γ : ℝ} {hc : c = deriv E 1} (hγ : γ = deriv (deriv (fun s ↦ E (exp s))) 0)
    (A_pos : ∀ τ > 0, 0 < A τ) (E_mono : MonotoneOn E (Ioi 0))
    (E_noncst : ¬ ∃ C, ∀ σ > 0, E σ = C) (hE1 : E 1 = 0)
    (E_eqn : ∀ σ > 0, ∀ τ > 0, E (σ * τ) = E σ * A τ + E τ) :
    E = if γ = 0 then (fun σ ↦ c * log σ) else (fun σ ↦ c * (σ.rpow γ - 1)) := by
  sorry -- **Issue #25**

end classification_calculation

end ExtremeValueProject
