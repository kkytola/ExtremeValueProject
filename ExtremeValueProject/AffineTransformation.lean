/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.DegenerateCDF
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Order.OrdContinuous
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable



section affine

open Topology Filter Set

/-- Mathlib's definition of an affine map is more general, but it can be shown that an affine
map `A : 𝕜 → 𝕜` of a field `𝕜` is a map of the form `x ↦ a * x + b` for some
coefficients `a b : 𝕜`. The function `AffineMap.coefs_of_field` extracts the pair `⟨a, b⟩`
of such coefficients from an affine map. -/
def AffineMap.coefs_of_field {𝕜 : Type*} [Field 𝕜] (A : 𝕜 →ᵃ[𝕜] 𝕜) : 𝕜 × 𝕜 :=
    ⟨LinearMap.ringLmapEquivSelf 𝕜 𝕜 𝕜 A.linear, A 0⟩

/-- An affine map `A : 𝕜 → 𝕜` is of the form `x ↦ a * x + b` for the values `a b : 𝕜` which
are obtained by `AffineMap.coefs_of_field`. -/
lemma AffineMap.apply_eq_of_field {𝕜 : Type*} [Field 𝕜] (A : 𝕜 →ᵃ[𝕜] 𝕜) (x : 𝕜) :
    A x = A.coefs_of_field.1 * x + A.coefs_of_field.2 := by
  rw [← add_zero x]
  convert A.map_vadd 0 x
  · funext r
    simp [AffineMap.coefs_of_field]
  · simp

lemma AffineEquiv.coefs_of_field_fst_ne_zero {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    A.toAffineMap.coefs_of_field.1 ≠ 0 := by
  intro maybe_zero
  have obs : A 0 = A 1 := by
    change A.toAffineMap 0 = A.toAffineMap 1
    simp_rw [A.toAffineMap.apply_eq_of_field]
    simp [maybe_zero]
  exact zero_ne_one <| A.injective obs

/-- An affine isomorphism `ℝ → ℝ` to be orientation preserving if its linear coefficient
is positive. -/
def AffineEquiv.IsOrientationPreserving (A : ℝ ≃ᵃ[ℝ] ℝ) : Prop :=
  0 < A.toAffineMap.coefs_of_field.1

/-- An affine isomorphism `ℝ → ℝ` to be orientation preserving if and only if it is
an increasing function. -/
lemma AffineEquiv.isOrientationPreserving_iff_mono (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.IsOrientationPreserving ↔ Monotone (fun x ↦ A x) := by
  sorry -- **Issue #2**

-- TODO: Generalize to canonically linearly ordered fields?
/-- The subgroup of affine isomorphishs ℝ → ℝ which are orientation preserving. -/
noncomputable def orientationPreservingAffineEquiv : Subgroup (ℝ ≃ᵃ[ℝ] ℝ) where
  carrier := AffineEquiv.IsOrientationPreserving
  mul_mem' := by sorry -- **Issue #3**
  one_mem' := by sorry -- **Issue #3**
  inv_mem' := by sorry -- **Issue #3**

/-- Orientation preserving affine isomorphisms ℝ → ℝ are continuous. -/
lemma orientationPreservingAffineEquiv.continuous (A : orientationPreservingAffineEquiv) :
    Continuous (A : ℝ → ℝ) := by
  apply (AffineMap.continuous_iff (R := ℝ) (E := ℝ) (F := ℝ) (f := A)).mpr
  exact LinearMap.continuous_of_finiteDimensional _

end affine



section affine_transform_of_cdf

namespace CumulativeDistributionFunction

/-- The action of orientation preserving affine isomorphisms on cumulative distribution
functions, so that for `A : orientationPreservingAffineEquiv` and
`F : CumulativeDistributionFunction` we have `(A • F)(x) = F(A⁻¹ x)`. -/
noncomputable def affineTransform
    (F : CumulativeDistributionFunction) (A : orientationPreservingAffineEquiv) :
    CumulativeDistributionFunction where
  toFun := fun x ↦ F (A⁻¹.val x)
  mono' := sorry -- **Issue #4** (recall `AffineEquiv.isOrientationPreserving_iff_mono`)
  right_continuous' := sorry -- **Issue #4**
  tendsto_atTop := sorry -- **Issue #4**
  tendsto_atBot := sorry -- **Issue #4**

@[simp] lemma affineTransform_apply_eq
    (F : CumulativeDistributionFunction) (A : orientationPreservingAffineEquiv) (x : ℝ):
    (F.affineTransform A) x = F ((A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ) x) := rfl

lemma affineTransform_mul_apply_eq_comp
    (F : CumulativeDistributionFunction) (A B : orientationPreservingAffineEquiv) :
    F.affineTransform (A * B) = (F.affineTransform B).affineTransform A := rfl

@[simp] lemma affineTransform_one_apply (F : CumulativeDistributionFunction) :
    F.affineTransform 1 = F := rfl

/-- The action of orientation preserving affine isomorphisms on cumulative distribution
functions, so that for `A : orientationPreservingAffineEquiv` and
`F : CumulativeDistributionFunction` we have `(A • F)(x) = F(A⁻¹ x)`. -/
noncomputable instance instMulActionOrientationPreservingAffineEquiv :
    MulAction orientationPreservingAffineEquiv CumulativeDistributionFunction where
  smul A F := F.affineTransform A
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma mulAction_apply_eq
    (F : CumulativeDistributionFunction) (A : orientationPreservingAffineEquiv) (x : ℝ):
    (A • F) x = F ((A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ) x) := rfl

-- Lemma: If X is a ℝ-valued random variable with c.d.f. F, then the c.d.f. of A • X is A • F.

/-- An affine transform of a c.d.f. is degenerate iff the c.d.f. itself is degenerate. -/
lemma affine_isDegenerate_iff
    (F : CumulativeDistributionFunction) (A : orientationPreservingAffineEquiv) :
    (A • F).IsDegenerate ↔ F.IsDegenerate := by
  sorry -- **Issue #5**

/-- An affine transform of a c.d.f. is continuious at `A x` if the c.d.f. itself is continuous
at `x`. -/
lemma affine_continuousAt_of_continuousAt
    {F : CumulativeDistributionFunction} {x : ℝ} (F_cont : ContinuousAt F x)
    (A : orientationPreservingAffineEquiv) :
    ContinuousAt (A • F) ((A : ℝ ≃ᵃ[ℝ] ℝ) x) := by
    have hA: Continuous (A : ℝ ≃ᵃ[ℝ] ℝ):= by sorry
    have hA1: ContinuousAt (A : ℝ ≃ᵃ[ℝ] ℝ) (x):= by exact Continuous.continuousAt hA
    unfold ContinuousAt at *
    unfold Filter.Tendsto at *
    simp only [mulAction_apply_eq] at *
    have ha: (A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹ ((A : ℝ ≃ᵃ[ℝ] ℝ) x) = x:= by
        exact (AffineEquiv.apply_eq_iff_eq_symm_apply (A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹).mpr rfl
    have h1: nhds (F ((A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹ ((A : ℝ ≃ᵃ[ℝ] ℝ) x))) = nhds (F x) := by
        exact congrArg nhds (congrArg (↑F.toStieltjesFunction) ha)
    rw[h1]
    sorry



    /-intro u hu
    have ha: Continuous (A : ℝ ≃ᵃ[ℝ] ℝ):= by sorry
    simp only [mulAction_apply_eq] at *
    have hu1: u ∈ nhds (F x):= by
      have ha: (A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹ ((A : ℝ ≃ᵃ[ℝ] ℝ) x) = x:= by
        exact (AffineEquiv.apply_eq_iff_eq_symm_apply (A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹).mpr rfl
      have h1: nhds (F ((A : ℝ ≃ᵃ[ℝ] ℝ)⁻¹ ((A : ℝ ≃ᵃ[ℝ] ℝ) x))) = nhds (F x) := by
        exact congrArg nhds (congrArg (↑F.toStieltjesFunction) ha)
      rw[h1] at hu
      exact hu
    have hu2:  u ∈ Filter.map (↑F.toStieltjesFunction) (nhds x) := by exact F_cont hu1
    have h2:Filter.map (↑(A • F).toStieltjesFunction) (nhds ((A : ℝ ≃ᵃ[ℝ] ℝ) x))=Filter.map (↑F.toStieltjesFunction) (nhds x):= by
      calc
        _ = Filter.map (↑(A • F).toStieltjesFunction) (Filter.map (A : ℝ ≃ᵃ[ℝ] ℝ) (nhds (x))) := by
          have: ha1:  (Filter.map (A : ℝ ≃ᵃ[ℝ] ℝ) (nhds (x)))-/



/-- An affine transform of a c.d.f. is continuious at `A x` if and only if the c.d.f. itself is
continuous at `x`. -/
lemma affine_continuousAt_iff
    (F : CumulativeDistributionFunction) (A : orientationPreservingAffineEquiv) (x : ℝ) :
    ContinuousAt (A • F) x ↔ ContinuousAt F ((A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ) x) := by
  constructor
  · intro AF_cont
    convert affine_continuousAt_of_continuousAt AF_cont A⁻¹
    simp
  · intro F_cont
    convert affine_continuousAt_of_continuousAt F_cont A
    exact (@AffineEquiv.apply_symm_apply ℝ ℝ ℝ ℝ ℝ _ _ _ _ _ _ _ A x).symm

end CumulativeDistributionFunction

section extend

/-- Extend an affine map `ℝ → ℝ` to `[-∞,+∞] → [-∞,+∞]`. -/
noncomputable def AffineMap.extend (A : ℝ →ᵃ[ℝ] ℝ) (x : EReal) : EReal :=
  match x with
  | ⊥ => if A.coefs_of_field.1 > 0 then ⊥
      else if A.coefs_of_field.1 < 0 then ⊤
      else A.coefs_of_field.2
  | ⊤ => if A.coefs_of_field.1 > 0 then ⊤
      else if A.coefs_of_field.1 < 0 then ⊥
      else A.coefs_of_field.2
  | some (some ξ) => A ξ

lemma AffineMap.leftOrdContinuous (A : ℝ →ᵃ[ℝ] ℝ) :
    LeftOrdContinuous A := by
  sorry -- **Issue #7** (Rmk: This should go via a lemma that is being PRd to Mathlib)

lemma AffineMap.rightOrdContinuous (A : ℝ →ᵃ[ℝ] ℝ) :
    RightOrdContinuous A := by
  sorry -- **Issue #7** (Rmk: This should go via a lemma that is being PRd to Mathlib)

lemma AffineMap.leftOrdContinuous_extend (A : ℝ →ᵃ[ℝ] ℝ) :
    LeftOrdContinuous A.extend := by
  sorry -- **Issue #7**

lemma AffineMap.rightOrdContinuous_extend (A : ℝ →ᵃ[ℝ] ℝ) :
    RightOrdContinuous A.extend := by
  sorry -- **Issue #7**

lemma AffineEquiv.extend_bot' (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.toAffineMap.extend ⊥ =
      if 0 < A.toAffineMap.coefs_of_field.1 then ⊥ else ⊤ := by
  have obs : A.toAffineMap.coefs_of_field.1 ≠ 0 :=
    coefs_of_field_fst_ne_zero A
  by_cases hA : 0 < A.toAffineMap.coefs_of_field.1
  · simp [AffineMap.extend, hA]
  · simp only [ne_eq, not_lt] at *
    have hA' : A.toAffineMap.coefs_of_field.1 < 0 := lt_of_le_of_ne hA obs
    simp [AffineMap.extend, hA']

lemma AffineEquiv.extend_top' (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.toAffineMap.extend ⊤ =
      if 0 < A.toAffineMap.coefs_of_field.1 then ⊤ else ⊥ := by
  have obs : A.toAffineMap.coefs_of_field.1 ≠ 0 :=
    coefs_of_field_fst_ne_zero A
  by_cases hA : 0 < A.toAffineMap.coefs_of_field.1
  · simp [AffineMap.extend, hA]
  · simp only [ne_eq, not_lt] at *
    have hA' : A.toAffineMap.coefs_of_field.1 < 0 := lt_of_le_of_ne hA obs
    simp [AffineMap.extend, hA']

--lemma AffineEquiv.extend_ofReal' (A : ℝ ≃ᵃ[ℝ] ℝ) (x : ℝ) :
--    A.toAffineMap.extend x = A x :=
--  rfl

/-- Extend an affine equivalence `ℝ → ℝ` to and equivalence `[-∞,+∞] → [-∞,+∞]`. -/
noncomputable def AffineEquiv.extend (A : ℝ ≃ᵃ[ℝ] ℝ) : EReal ≃ EReal where
  toFun := A.toAffineMap.extend
  invFun := A.symm.toAffineMap.extend
  left_inv x := by
    sorry -- **Issue #8**
  right_inv := by
    sorry -- **Issue #8**

@[simp] lemma AffineEquiv.extend_bot (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.extend ⊥ = if 0 < A.toAffineMap.coefs_of_field.1 then ⊥ else ⊤ :=
  AffineEquiv.extend_bot' A

@[simp] lemma AffineEquiv.extend_top (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.extend ⊤ = if 0 < A.toAffineMap.coefs_of_field.1 then ⊤ else ⊥ :=
  AffineEquiv.extend_top' A

@[simp] lemma AffineEquiv.extend_ofReal (A : ℝ ≃ᵃ[ℝ] ℝ) (x : ℝ):
    A.extend x = A x :=
  rfl

@[simp] lemma AffineEquiv.extend_symm (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.extend.symm = A.symm.extend := by
  sorry -- **Issue #8**

end extend

end affine_transform_of_cdf
