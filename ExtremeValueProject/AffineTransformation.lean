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

/-- An affine equivalence `A : 𝕜 → 𝕜` is of the form `x ↦ a * x + b` for the values `a b : 𝕜`
which are obtained by `AffineEquiv.toAffineMap.coefs_of_field`. -/
lemma AffineEquiv.apply_eq_of_field {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) (x : 𝕜) :
    A x = A.toAffineMap.coefs_of_field.1 * x + A.toAffineMap.coefs_of_field.2 := by
  rw [show A x = A.toAffineMap x from rfl]
  exact AffineMap.apply_eq_of_field A x

lemma AffineEquiv.coefs_of_field_fst_ne_zero {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    A.toAffineMap.coefs_of_field.1 ≠ 0 := by
  intro maybe_zero
  have obs : A 0 = A 1 := by
    change A.toAffineMap 0 = A.toAffineMap 1
    simp_rw [A.toAffineMap.apply_eq_of_field]
    simp [maybe_zero]
  exact zero_ne_one <| A.injective obs

/-- Construct an affine map `𝕜 →ᵃ[𝕜] 𝕜` from coefficients `a b : 𝕜` by the
formula `x ↦ a * x + b`. -/
def AffineMap.mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜] (a b : 𝕜) :
    𝕜 →ᵃ[𝕜] 𝕜 where
  toFun x := a * x + b
  linear :=
    { toFun x := a * x
      map_add' x y := by ring
      map_smul' c x := by simp only [smul_eq_mul, RingHom.id_apply] ; ring }
  map_vadd' p v := by simp only [vadd_eq_add, LinearMap.coe_mk, AddHom.coe_mk] ; ring

@[simp] lemma AffineMap.coefs_of_field_fst_mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜] (a b : 𝕜) :
    (AffineMap.mkOfCoefs_of_field a b).coefs_of_field.1 = a := by
  simp [AffineMap.mkOfCoefs_of_field, AffineMap.coefs_of_field]

@[simp] lemma AffineMap.coefs_of_field_snd_mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜] (a b : 𝕜) :
    (AffineMap.mkOfCoefs_of_field a b).coefs_of_field.2 = b := by
  simp [AffineMap.mkOfCoefs_of_field, AffineMap.coefs_of_field]

lemma AffineMap.mkOfCoefs_of_field_apply_eq {𝕜 : Type*} [Field 𝕜] (a b : 𝕜) (x : 𝕜):
    AffineMap.mkOfCoefs_of_field a b x = a * x + b :=
  rfl

@[simp] lemma AffineMap.mkOfCoefs_of_field_eq_self
    {𝕜 : Type*} [Field 𝕜] (A : 𝕜 →ᵃ[𝕜] 𝕜) :
    AffineMap.mkOfCoefs_of_field A.coefs_of_field.1 A.coefs_of_field.2 = A := by
  ext x
  simp [AffineMap.apply_eq_of_field A x, AffineMap.mkOfCoefs_of_field]

def AffineEquiv.mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜] {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) :
    𝕜 ≃ᵃ[𝕜] 𝕜 where
  toFun := AffineMap.mkOfCoefs_of_field a b
  invFun := AffineMap.mkOfCoefs_of_field a⁻¹ (-a⁻¹ * b)
  left_inv x := by
    simp [AffineMap.mkOfCoefs_of_field, mul_add, ← mul_assoc, inv_mul_cancel₀ a_ne_zero]
  right_inv x := by
    simp [AffineMap.mkOfCoefs_of_field, mul_add, ← mul_assoc, mul_inv_cancel₀ a_ne_zero]
  linear :=
    { toFun x := a * x
      map_add' x y := by ring
      map_smul' c x := by simp only [smul_eq_mul, RingHom.id_apply] ; ring
      invFun x := a⁻¹ * x
      left_inv x := by simp [← mul_assoc, inv_mul_cancel₀ a_ne_zero]
      right_inv x := by simp [← mul_assoc, mul_inv_cancel₀ a_ne_zero] }
  map_vadd' p v := by
    simp only [AffineMap.mkOfCoefs_of_field, AffineMap.coe_mk, neg_mul, vadd_eq_add,
               Equiv.coe_fn_mk, LinearEquiv.coe_mk]
    ring

@[simp] lemma AffineEquiv.mkOfCoefs_of_field_toAffineMap {𝕜 : Type*} [Field 𝕜]
    {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b).toAffineMap
      = AffineMap.mkOfCoefs_of_field a b :=
  rfl

@[simp] lemma AffineEquiv.mkOfCoefs_of_field_symm_eq_mkOfCoefs_of_field
    {𝕜 : Type*} [Field 𝕜] {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b).symm.toAffineMap
      = AffineMap.mkOfCoefs_of_field a⁻¹ (-a⁻¹ * b) :=
  rfl

lemma AffineEquiv.coefs_of_field_fst_mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜]
    {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b).toAffineMap.coefs_of_field.1 = a := by
  simp

lemma AffineEquiv.coefs_of_field_snd_mkOfCoefs_of_field {𝕜 : Type*} [Field 𝕜]
    {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b).toAffineMap.coefs_of_field.2 = b := by
  simp

lemma AffineEquiv.mkOfCoefs_of_field_apply_eq
    {𝕜 : Type*} [Field 𝕜] {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) (x : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b) x = a * x + b :=
  rfl

lemma AffineEquiv.mkOfCoefs_of_field_symm_apply_eq
    {𝕜 : Type*} [Field 𝕜] {a : 𝕜} (a_ne_zero : a ≠ 0) (b : 𝕜) (x : 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field a_ne_zero b).symm x = a⁻¹ * x - a⁻¹ * b := by
  rw [show (mkOfCoefs_of_field a_ne_zero b).symm x = AffineMap.mkOfCoefs_of_field a⁻¹ (-a⁻¹ * b) x
      from rfl]
  simp only [neg_mul, AffineMap.mkOfCoefs_of_field_apply_eq]
  ring

@[simp] lemma AffineEquiv.mkOfCoefs_of_field_eq_self
    {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    AffineEquiv.mkOfCoefs_of_field (coefs_of_field_fst_ne_zero A) A.toAffineMap.coefs_of_field.2
      = A := by
  ext x
  rw [show A x = A.toAffineMap x from rfl, AffineMap.apply_eq_of_field A.toAffineMap x]
  simp [mkOfCoefs_of_field, AffineMap.mkOfCoefs_of_field]

/-- The inverse `A⁻¹` of an affine map `A : 𝕜 → 𝕜` is of the form `x ↦ a * x + b`
is `y ↦ α * x + β` where `α = a⁻¹` and `β = - a⁻¹ * b`. -/
lemma AffineMap.mkOfCoefs_of_field_eq_inv {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    (AffineEquiv.mkOfCoefs_of_field (inv_ne_zero A.coefs_of_field_fst_ne_zero)
      (-(A.toAffineMap.coefs_of_field.1)⁻¹ * A.toAffineMap.coefs_of_field.2))
      = A⁻¹ := by
  ext x
  simp only [show A⁻¹ = A.symm from rfl, neg_mul, AffineEquiv.mkOfCoefs_of_field_apply_eq]
  nth_rw 4 [← AffineEquiv.mkOfCoefs_of_field_eq_self A]
  rw [AffineEquiv.mkOfCoefs_of_field_symm_apply_eq]
  ring

/-- The inverse `A⁻¹` of an affine map `A : 𝕜 → 𝕜` is of the form `x ↦ a * x + b`
is `y ↦ α * x + β` where `α = a⁻¹`. -/
lemma AffineEquiv.inv_coefs_of_field_fst {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    (A⁻¹).toAffineMap.coefs_of_field.1 = (A.toAffineMap.coefs_of_field.1)⁻¹ := by
  simp [← AffineMap.mkOfCoefs_of_field_eq_inv A]

/-- The inverse `A⁻¹` of an affine map `A : 𝕜 → 𝕜` is of the form `x ↦ a * x + b`
is `y ↦ α * x + β` where `β = - a⁻¹ * b`. -/
lemma AffineMap.inv_coefs_of_field_fst {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) (x : 𝕜) :
    (A⁻¹).toAffineMap.coefs_of_field.2
      = -(A.toAffineMap.coefs_of_field.1)⁻¹ * A.toAffineMap.coefs_of_field.2 := by
  simp [← AffineMap.mkOfCoefs_of_field_eq_inv A]

/-- An affine isomorphism `ℝ → ℝ` to be orientation preserving if its linear coefficient
is positive. -/
def AffineEquiv.IsOrientationPreserving (A : ℝ ≃ᵃ[ℝ] ℝ) : Prop :=
  0 < A.toAffineMap.coefs_of_field.1

/-- An affine isomorphism `ℝ → ℝ` to be orientation preserving if and only if it is
an increasing function. -/
lemma AffineEquiv.isOrientationPreserving_iff_mono (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.IsOrientationPreserving ↔ Monotone (fun x ↦ A x) := by
  unfold IsOrientationPreserving
  set a := A.toAffineMap.coefs_of_field.1
  set b := A.toAffineMap.coefs_of_field.2
  have in_other_words (x) : A x = a * x + b := AffineMap.apply_eq_of_field A x
  simp_rw [in_other_words]
  constructor
  · intro a_pos
    intro x y x_le_y
    simpa using (mul_le_mul_iff_of_pos_left a_pos).mpr x_le_y
  · intro mono
    have key := mono zero_le_one
    simp only [mul_zero, zero_add, mul_one, le_add_iff_nonneg_left] at key
    have a_nonzero : a ≠ 0 := by exact coefs_of_field_fst_ne_zero A
    exact lt_of_le_of_ne' key a_nonzero

-- TODO: Generalize to canonically linearly ordered fields?
/-- The subgroup of affine isomorphishs ℝ → ℝ which are orientation preserving. -/
noncomputable def orientationPreservingAffineEquiv : Subgroup (ℝ ≃ᵃ[ℝ] ℝ) where
  carrier := AffineEquiv.IsOrientationPreserving
  mul_mem' := by
    simp_rw [mem_def, AffineEquiv.isOrientationPreserving_iff_mono]
    exact Monotone.comp
  one_mem' := Real.zero_lt_one
  inv_mem' := by
    intro x hx
    apply AffineEquiv.inv_coefs_of_field_fst x ▸ Right.inv_pos.mpr hx
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
  mono' := by
    suffices Monotone fun x ↦  A⁻¹.val x by apply Monotone.comp F.mono' this
    -- simp only [InvMemClass.coe_inv]
    suffices (A.val)⁻¹.IsOrientationPreserving by
      exact (AffineEquiv.isOrientationPreserving_iff_mono (↑A)⁻¹).mp this
    exact orientationPreservingAffineEquiv.inv_mem A.mem
  right_continuous' := by
    intro x
    set g := (fun x => F (A⁻¹.val x)) with g_def

    have w := orientationPreservingAffineEquiv.inv_mem A.mem
    simp only [←InvMemClass.coe_inv] at w
    set B := (A)⁻¹ with B_def
    have Fcont (y): ContinuousWithinAt (F) (Set.Ici y) y := by
      exact StieltjesFunction.right_continuous F y
    have Bcont := orientationPreservingAffineEquiv.continuous B
    change g = F ∘ B at g_def
    set B' := (B.val).toEquiv --with B'_def
    have Bcont' : ContinuousWithinAt (⇑B') (Set.Ici x) x := Continuous.continuousWithinAt Bcont


    have ima: B' '' (Set.Ici x) = (Set.Ici (B' x)) := by
      ext z
      simp only [Set.mem_image_equiv, Set.mem_Ici]
      have monoB: Monotone B' := by
        have t2: B' = fun x ↦ B.val x := rfl
        rw [t2,←AffineEquiv.isOrientationPreserving_iff_mono B]
        exact w

      set q := (B'.symm z) with q_def
      have q_use: B' q = z := by exact Equiv.apply_symm_apply B' z
      rw [←q_use]
      -- refine le_iff_le_iff_lt_iff_lt.mpr ?_
      constructor
      · intro r
        exact monoB r
      · intro l
        by_contra qx
        simp only [not_le] at qx
        have equ: B' x = B' q := le_antisymm l (monoB qx.le)
        rw [←q_use,←equ,Equiv.symm_apply_apply] at q_def
        exact qx.ne q_def

      -- have : B'.symm = B'⁻¹ := rfl
      -- rw [this]
      -- set www := B'⁻¹ z with www_def

      -- reduce
      -- simp

      -- -- simp_rw [←AffineMap.mkOfCoefs_of_field_eq_inv]
      -- #check AffineEquiv.inv_coefs_of_field_fst
      -- unfold B'
      -- simp
      -- rw [B_def]
      -- -- simp only [InvMemClass.coe_inv, AffineEquiv.symm_toEquiv, AffineEquiv.coe_toEquiv]

    set F' := F.toStieltjesFunction.toFun --with F'_def
    -- clear * - g_def
    have FcontB := Fcont (B' x)
    rw [←ima] at FcontB
    rw [g_def]

    unfold ContinuousWithinAt at FcontB ⊢
    unfold Filter.Tendsto at FcontB ⊢

    -- #check nhdsWithin_le_comap
    simp
    rw [←Filter.map_compose]
    simp only [Function.comp_apply]
    suffices
        Filter.map F' (nhdsWithin (B' x) (⇑B' '' Set.Ici x))
        = Filter.map F' (Filter.map (⇑B') (nhdsWithin x (Set.Ici x))) by
      exact le_of_eq_of_le (id (Eq.symm this)) FcontB
    suffices
        (nhdsWithin (B' x) (⇑B' '' Set.Ici x))
        = (Filter.map (⇑B') (nhdsWithin x (Set.Ici x))) by
      exact congrArg (Filter.map F') this

    #check Ioo_mem_nhdsGE_of_mem
    rw [ima]
    ext s
    simp only [Filter.mem_map]

    rw [nhdsWithin_eq]
    -- have : nhds x = (⨅ s ∈ { Ioo | x ∈ s ∧ IsOpen s }, Filter.principal s) := by
    --   sorry
    -- have : (nhdsWithin x (Set.Ici x)) =
    --     (⨅ s ∈ { s  | x ∈ s ∧ IsOpen s }, Filter.principal s) ⊓ (Filter.principal (Set.Ici x))
    --     := by
    --   unfold nhdsWithin
    --   rw [nhds_def]

    --   sorry
    -- apply FcontB.trans'
    -- rw [Filter.map_le_map_iff]

    -- rw [Filter.map_le_iff_le_comap]
    -- apply nhdsWithin_le_comap

    -- rw [←Filter.Tendsto]


    -- rw [Filter.le_def]
    -- simp_rw [Filter.mem_map]
    -- intros X aa
    -- rw [Set.preimage_comp]
    -- set Y := (F' ⁻¹' X)

    -- #check nhdsWithin
    -- #check nhdsWithin_le_of_mem aa
    -- rw [Filter.nhd]

    -- exact Continuous.continuousWithinAt Bcont

    --


    sorry -- **Issue #4**
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
  sorry -- **Issue #6**

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

lemma AffineEquiv.extend_symm_cancel (A : ℝ ≃ᵃ[ℝ] ℝ) (x : EReal) :
    A.symm.toAffineMap.extend (A.toAffineMap.extend x) = x := by
  simp [AffineMap.extend]
  by_cases hA : 0 < A.toAffineMap.coefs_of_field.1
  case' pos =>
    have : 0 < A.symm.toAffineMap.coefs_of_field.1 := by
      rw [show A.symm = A⁻¹ from rfl, inv_coefs_of_field_fst, inv_pos]
      exact hA
    simp [hA, this]
  case' neg =>
    rw [not_lt] at hA
    have obs : A.toAffineMap.coefs_of_field.1 ≠ 0 :=
      coefs_of_field_fst_ne_zero A
    have hA' : A.toAffineMap.coefs_of_field.1 < 0 := lt_of_le_of_ne hA obs
    have : A.symm.toAffineMap.coefs_of_field.1 < 0 := by
      rw [show A.symm = A⁻¹ from rfl, inv_coefs_of_field_fst, inv_neg'']
      exact hA'
    simp [hA', this, lt_asymm]
  all_goals split
  all_goals
  rename_i h
  split at h <;> first | rfl | cases h
  all_goals
  rw [symm_apply_apply]
  rfl

/-- Extend an affine equivalence `ℝ → ℝ` to and equivalence `[-∞,+∞] → [-∞,+∞]`. -/
noncomputable def AffineEquiv.extend (A : ℝ ≃ᵃ[ℝ] ℝ) : EReal ≃ EReal where
  toFun := A.toAffineMap.extend
  invFun := A.symm.toAffineMap.extend
  left_inv := extend_symm_cancel A
  right_inv := extend_symm_cancel A.symm

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
  rfl

end extend

end affine_transform_of_cdf
