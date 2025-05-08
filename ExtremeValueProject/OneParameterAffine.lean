/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.AffineTransformation

section one_parameter_subgroups_of_affine_transformations

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where `Aₛ x = x + β * s`.
(`β` is a real parameter: each `β` gives a different (but related) homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex₀ (β : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs zero_lt_one (s.toAdd * β)
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp
    ring

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where
`Aₛ x = exp(α * s) * (x - c) + c`.
(`α c` are real parameters: each `α c` give a different homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex (α c : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs (show 0 < Real.exp (s.toAdd * α) from Real.exp_pos _)
              (c * (Real.exp (s.toAdd * α) - 1))
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp [add_mul, Real.exp_add]
    ring

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + β * s`, where `s ∈ ℝ`.
(`β` is a real parameter: each `β ≠ 0` in fact gives the same subgroup) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀' (β : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ β) ⊤

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + s`, where `s ∈ ℝ`. -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀ :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ 1) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_of_ne_zero {β : ℝ} (hβ : β ≠ 0) :
    AffineIncrEquiv.subGroupOfIndex₀' β = AffineIncrEquiv.subGroupOfIndex₀ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_bot :
    AffineIncrEquiv.subGroupOfIndex₀' 0 = ⊥ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex₀_of_no_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) (hA : ∀ x, A x ≠ x) :
    A ∈ subGroupOfIndex₀ := by
  sorry -- **Issue 44**

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = exp(α * s) * (x - c) + c` where `s ∈ ℝ`.
(`α c` are real parameters) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex (α c : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex α c) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex_eq_bot (c : ℝ) :
    subGroupOfIndex 0 c = ⊥ := by
  sorry -- **Issue 45**

@[simp] lemma AffineIncrEquiv.fixed_point_of_mem_subGroupOfIndex (A : AffineIncrEquiv)
    {α c : ℝ} (hA : A ∈ subGroupOfIndex α c):
    A c = c := by
  sorry -- **Issue 45**

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex_iff_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    A ∈ subGroupOfIndex α c ↔ A c = c := by
  sorry -- **Issue 45**

end one_parameter_subgroups_of_affine_transformations
