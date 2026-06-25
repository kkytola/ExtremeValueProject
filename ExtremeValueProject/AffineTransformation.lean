/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Okko Heiniö ...
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
  convert A.map_vadd 0 x
  · simp
  · simp [AffineMap.coefs_of_field]

lemma AffineMap.coefsOfField_fst_eq_div_sub {𝕜 : Type*} [Field 𝕜] (A : 𝕜 →ᵃ[𝕜] 𝕜)
    {x y : 𝕜} (hxy : x ≠ y) :
    A.coefs_of_field.1 = (A y - A x) / (y - x) := by
  have key : A y - A x = A.coefs_of_field.1 * (y - x) := by simp [apply_eq_of_field A, mul_sub]
  exact eq_div_of_mul_eq (sub_ne_zero_of_ne hxy.symm) key.symm

lemma AffineMap.coefsOfField_snd_eq_apply_sub_mul {𝕜 : Type*} [Field 𝕜] (A : 𝕜 →ᵃ[𝕜] 𝕜) (x : 𝕜) :
    A.coefs_of_field.2 = A x - A.coefs_of_field.1 * x :=
  eq_sub_of_add_eq' (apply_eq_of_field A x).symm

lemma AffineMap.ext_of_coefsOfField {𝕜 : Type*} [Field 𝕜] {A₁ A₂ : 𝕜 →ᵃ[𝕜] 𝕜}
    (h : A₁.coefs_of_field = A₂.coefs_of_field) :
    A₁ = A₂ := by
  ext x ; simp [apply_eq_of_field, h]

/-- If two affine self-maps from a field coincide at two points, then they are equal. -/
lemma AffineMap.ext_of_apply₂ {𝕜 : Type*} [Field 𝕜] {A₁ A₂ : 𝕜 →ᵃ[𝕜] 𝕜} {x y : 𝕜} (hxy : x ≠ y)
    (hx : A₁ x = A₂ x) (hy : A₁ y = A₂ y) :
    A₁ = A₂ := by
  apply ext_of_coefsOfField
  have obs₁ := A₁.coefsOfField_fst_eq_div_sub hxy
  rw [hx, hy, ← A₂.coefsOfField_fst_eq_div_sub hxy] at obs₁
  have obs₂ := A₁.coefsOfField_snd_eq_apply_sub_mul x
  rw [obs₁, hx, ← A₂.coefsOfField_snd_eq_apply_sub_mul x] at obs₂
  exact Prod.ext obs₁ obs₂

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
    simp [AffineMap.mkOfCoefs_of_field]
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

/-- The inverse `A⁻¹` of an affine map `A : 𝕜 → 𝕜` of the form `x ↦ a * x + b`
is `y ↦ α * x + β` where `α = a⁻¹`. -/
lemma AffineEquiv.inv_coefs_of_field_fst {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
    (A⁻¹).toAffineMap.coefs_of_field.1 = (A.toAffineMap.coefs_of_field.1)⁻¹ := by
  simp [← AffineMap.mkOfCoefs_of_field_eq_inv A]

/-- The inverse `A⁻¹` of an affine map `A : 𝕜 → 𝕜` of the form `x ↦ a * x + b`
is `y ↦ α * x + β` where `β = - a⁻¹ * b`. -/
lemma AffineEquiv.inv_coefs_of_field_snd {𝕜 : Type*} [Field 𝕜] (A : 𝕜 ≃ᵃ[𝕜] 𝕜) :
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
  · intro a_pos x y x_le_y
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
    intro a b ha hb
    apply (AffineEquiv.isOrientationPreserving_iff_mono _).mpr
    exact (a.isOrientationPreserving_iff_mono.mp ha).comp (b.isOrientationPreserving_iff_mono.mp hb)
  one_mem' := Real.zero_lt_one
  inv_mem' := by
    intro x hx
    apply AffineEquiv.inv_coefs_of_field_fst x ▸ Right.inv_pos.mpr hx

/-- Orientation preserving affine isomorphisms ℝ → ℝ are continuous. -/
lemma orientationPreservingAffineEquiv.continuous (A : orientationPreservingAffineEquiv) :
    Continuous (A : ℝ → ℝ) := by
  apply (AffineMap.continuous_linear_iff (P := ℝ) (R := ℝ) (Q := ℝ) (f := A)).symm.mpr
  exact LinearMap.continuous_of_finiteDimensional _

lemma orientationPreservingAffineEquiv.monotone (A : orientationPreservingAffineEquiv) :
    Monotone (A : ℝ → ℝ) :=
  (AffineEquiv.isOrientationPreserving_iff_mono ..).mp A.prop

/-- A designated type for orientation preserving affine isomorphisms of `ℝ`. -/
def AffineIncrEquiv := {A : ℝ ≃ᵃ[ℝ] ℝ // A.IsOrientationPreserving}

lemma AffineIncrEquiv.isOrientationPreserving (A : AffineIncrEquiv) :
    A.val.IsOrientationPreserving := A.prop

def AffineIncrEquiv.mk {A : ℝ ≃ᵃ[ℝ] ℝ} (hA : A.IsOrientationPreserving) :
    AffineIncrEquiv :=
  ⟨A, hA⟩

noncomputable def AffineIncrEquiv.mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    AffineIncrEquiv :=
  ⟨AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b, by
    simp [AffineEquiv.IsOrientationPreserving, a_pos]⟩

noncomputable def AffineIncrEquiv.coefs (A : AffineIncrEquiv) :=
  A.val.toAffineMap.coefs_of_field

lemma AffineIncrEquiv.coefs_mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    (AffineIncrEquiv.mkOfCoefs a_pos b).coefs = ⟨a, b⟩ := by
  ext <;> simp_all [mkOfCoefs, coefs]

@[simp] lemma AffineIncrEquiv.coefs_fst_mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    (AffineIncrEquiv.mkOfCoefs a_pos b).coefs.1 = a := by
  simp [AffineIncrEquiv.coefs_mkOfCoefs]

@[simp] lemma AffineIncrEquiv.coefs_snd_mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    (AffineIncrEquiv.mkOfCoefs a_pos b).coefs.2 = b := by
  simp [AffineIncrEquiv.coefs_mkOfCoefs]

lemma AffineIncrEquiv.mem_orientationPreservingAffineEquiv (A : AffineIncrEquiv) :
    A.val ∈ orientationPreservingAffineEquiv := by
  simp

lemma AffineIncrEquiv.coefs_fst_pos (A : AffineIncrEquiv) :
    0 < A.coefs.1 :=
  A.isOrientationPreserving

instance : Group AffineIncrEquiv where
  mul A₁ A₂ := ⟨A₁.val * A₂.val, orientationPreservingAffineEquiv.mul_mem
                  A₁.mem_orientationPreservingAffineEquiv A₂.mem_orientationPreservingAffineEquiv⟩
  mul_assoc A₁ A₂ A₃ := rfl
  one := ⟨1, orientationPreservingAffineEquiv.one_mem⟩
  one_mul A := rfl
  mul_one A := rfl
  npow_zero A := rfl
  npow_succ A n := rfl
  inv A := ⟨A.val⁻¹,
            orientationPreservingAffineEquiv.inv_mem A.mem_orientationPreservingAffineEquiv⟩
  div_eq_mul_inv A₁ A₂ := rfl
  zpow_zero' A := rfl
  zpow_succ' A n := rfl
  zpow_neg' A n := rfl
  inv_mul_cancel A := by
    apply Subtype.ext
    exact inv_mul_cancel A.val

instance : EquivLike AffineIncrEquiv ℝ ℝ where
  coe A := A.val
  inv A := A⁻¹.val
  left_inv A := AffineEquiv.equivLike.left_inv A.val
  right_inv A := AffineEquiv.equivLike.right_inv A.val
  coe_injective' A₁ A₂ hA hAinv := by
    apply Subtype.ext
    exact AffineEquiv.coeFn_inj.mp hA

@[simp] lemma AffineIncrEquiv.one_apply (x : ℝ) :
    (1 : AffineIncrEquiv) x = x :=
  rfl

@[ext] lemma AffineIncrEquiv.ext {A₁ A₂ : AffineIncrEquiv} (h : ∀ x, A₁ x = A₂ x) :
    A₁ = A₂ :=
  Subtype.ext <| AffineEquiv.ext h

@[simp] lemma AffineIncrEquiv.apply_eq (A : AffineIncrEquiv) (x : ℝ) :
    A x = A.coefs.1 * x + A.coefs.2 :=
  A.val.apply_eq_of_field x

lemma AffineIncrEquiv.mkOfCoefs_eq_one :
    (AffineIncrEquiv.mkOfCoefs zero_lt_one 0) = 1 := by
  ext x
  rw [one_apply]
  simp

lemma AffineIncrEquiv.mul_apply_eq_comp_apply (A₁ A₂ : AffineIncrEquiv) (x : ℝ) :
    (A₁ * A₂) x = A₁ (A₂ x) :=
  rfl

lemma AffineIncrEquiv.mono (A : AffineIncrEquiv) :
    Monotone A :=
  (AffineEquiv.isOrientationPreserving_iff_mono A.val).mp A.isOrientationPreserving

/-- We endow the space of orientation-preserving affine isomorphisms of `ℝ` with the topology
of pointwise convergence. (This coincides with the topology of convergence of the coefficients,
see `AffineIncrEquiv.tendsto_nhds_iff_tendsto_coefs`). -/
instance instTopologicalSpaceAffineIncrEquiv :
    TopologicalSpace AffineIncrEquiv :=
  TopologicalSpace.induced (fun A ↦ (A : ℝ → ℝ)) (by infer_instance)

lemma AffineIncrEquiv.continuous_apply (x : ℝ) :
    Continuous fun (A : AffineIncrEquiv) ↦ A x :=
  Continuous.comp (_root_.continuous_apply x) continuous_induced_dom

lemma AffineIncrEquiv.isEmbedding_coeFun :
    IsEmbedding (fun (A : AffineIncrEquiv) ↦ (A : ℝ → ℝ)) where
  eq_induced := rfl
  injective A₁ A₂ hA := by simp_all

lemma AffineIncrEquiv.tendsto_nhds_iff_forall_tendsto_apply {ι : Type*} {L : Filter ι}
    (As : ι → AffineIncrEquiv) (A : AffineIncrEquiv) :
    L.Tendsto As (𝓝 A) ↔ ∀ x, L.Tendsto (fun i ↦ As i x) (𝓝 (A x)) := by
  rw [AffineIncrEquiv.isEmbedding_coeFun.tendsto_nhds_iff]
  exact tendsto_pi_nhds

lemma AffineIncrEquiv.continuous_iff_forall_continuous_apply {Z : Type*} [TopologicalSpace Z]
    (φ : Z → AffineIncrEquiv):
    Continuous φ ↔ ∀ x, Continuous fun z ↦ φ z x := by
  rw [continuous_induced_rng]
  refine ⟨?_, ?_⟩
  · intro h x
    exact Continuous.comp (_root_.continuous_apply x) h
  · intro h
    exact continuous_pi h

lemma AffineIncrEquiv.coefs_fst_eq_div_sub (A : AffineIncrEquiv)
    {x y : ℝ} (hxy : x ≠ y) :
    A.coefs.1 = (A y - A x) / (y - x) :=
  A.val.toAffineMap.coefsOfField_fst_eq_div_sub hxy

lemma AffineIncrEquiv.coefs_snd_eq_apply_sub_mul (A : AffineIncrEquiv) (x : ℝ) :
    A.coefs.2 = A x - A.coefs.1 * x :=
  A.val.toAffineMap.coefsOfField_snd_eq_apply_sub_mul x

@[simp] lemma AffineIncrEquiv.coefs_fst_one :
    (1 : AffineIncrEquiv).coefs.1 = 1 := by
  rw [AffineIncrEquiv.coefs_fst_eq_div_sub 1 zero_ne_one]
  simp only [one_apply]
  simp

@[simp] lemma AffineIncrEquiv.coefs_snd_one :
    (1 : AffineIncrEquiv).coefs.2 = 0 := by
  rw [AffineIncrEquiv.coefs_snd_eq_apply_sub_mul 1 0]
  simp only [one_apply]
  simp

lemma AffineIncrEquiv.ext_of_coefs {A₁ A₂ : AffineIncrEquiv} (h : A₁.coefs = A₂.coefs) :
    A₁ = A₂ := by
  ext x
  simp [h]

@[simp] lemma AffineIncrEquiv.coefs_fst_mul (A₁ A₂ : AffineIncrEquiv) :
    (A₁ * A₂).coefs.1 = A₁.coefs.1 * A₂.coefs.1 := by
  sorry -- **Issue 43**

@[simp] lemma AffineIncrEquiv.coefs_snd_mul (A₁ A₂ : AffineIncrEquiv) :
    (A₁ * A₂).coefs.2 = A₁.coefs.1 * A₂.coefs.2 + A₁.coefs.2 := by
  sorry -- **Issue 43**

/-- The inverse `A⁻¹` of an orientation-preserving affine map `A : ℝ → ℝ` of the
form `x ↦ a * x + b` is `y ↦ α * x + β` where `α = a⁻¹`. -/
@[simp] lemma AffineIncrEquiv.inv_coefs_fst (A : AffineIncrEquiv) :
    (A⁻¹).coefs.1 = (A.coefs.1)⁻¹ :=
  A.val.inv_coefs_of_field_fst

/-- The inverse `A⁻¹` of an orientation-preserving affine map `A : ℝ → ℝ` of the
form `x ↦ a * x + b` is `y ↦ α * x + β` where `β = - a⁻¹ * b`. -/
@[simp] lemma AffineIncrEquiv.inv_coefs_snd (A : AffineIncrEquiv) :
    (A⁻¹).coefs.2 = -(A.coefs.1)⁻¹ * A.coefs.2 :=
  A.val.inv_coefs_of_field_snd

lemma AffineIncrEquiv.coefs_fst_inv_mul (A B : AffineIncrEquiv) :
    (A⁻¹ * B).coefs.1 = A.coefs.1⁻¹ * B.coefs.1 := by
  simp

lemma AffineIncrEquiv.coefs_snd_inv_mul (A B : AffineIncrEquiv) :
    (A⁻¹ * B).coefs.2 = A.coefs.1⁻¹ * (B.coefs.2 - A.coefs.2) := by
  simp
  ring

/-- If `A₁(x) = a₁ x + b₁` and  `A₂(x) = a₂ x + b₂`, then
`(A₁⁻¹ ∘ A₂)(x) = (a₁⁻¹ a₂) x + (b₂ - b₁) / a₁`. -/
lemma AffineIncrEquiv.inv_mul_eq_mkOfCoefs (A₁ A₂ : AffineIncrEquiv) :
    A₁⁻¹ * A₂ = mkOfCoefs (a := A₁.coefs.1⁻¹ * A₂.coefs.1)
        (mul_pos (inv_pos.mpr A₁.isOrientationPreserving) A₂.isOrientationPreserving)
        (A₁.coefs.1⁻¹ * (A₂.coefs.2 - A₁.coefs.2)) := by
  ext x
  rw [apply_eq, coefs_fst_inv_mul, coefs_snd_inv_mul]
  simp

lemma AffineIncrEquiv.continuous_coefs_fst :
    Continuous fun (A : AffineIncrEquiv) ↦ A.coefs.1 := by
  sorry

lemma AffineIncrEquiv.continuous_coefs_snd :
    Continuous fun (A : AffineIncrEquiv) ↦ A.coefs.2 := by
  sorry

lemma AffineIncrEquiv.tendsto_nhds_iff_tendsto_coefs {ι : Type*} {L : Filter ι}
    {As : ι → AffineIncrEquiv} (A : AffineIncrEquiv):
    L.Tendsto As (𝓝 A) ↔
      L.Tendsto (fun i ↦ (As i).coefs.1) (𝓝 A.coefs.1) ∧
      L.Tendsto (fun i ↦ (As i).coefs.2) (𝓝 A.coefs.2) := by
  constructor
  · intro As_lim
    refine ⟨?_, ?_⟩
    · apply Tendsto.comp AffineIncrEquiv.continuous_coefs_fst.continuousAt As_lim
    · apply Tendsto.comp AffineIncrEquiv.continuous_coefs_snd.continuousAt As_lim
  · intro ⟨h₁, h₂⟩
    apply (tendsto_nhds_iff_forall_tendsto_apply ..).mpr
    intro x
    simp only [apply_eq]
    apply Tendsto.add _ h₂
    exact Tendsto.mul h₁ tendsto_const_nhds

/-- The map `A ↦ A⁻¹` is continuous on the type `AffineIncrEquiv` of orientation-preserving
affine isomorphisms of `ℝ`. -/
lemma AffineIncrEquiv.continuous_inv :
    Continuous fun (A : AffineIncrEquiv) ↦ A⁻¹ := by
  sorry -- **Issue #56** (affine-inversion-continuous)

/-- The map `A ↦ A⁻¹` as a homeomorphism of the type `AffineIncrEquiv` of orientation-preserving
affine isomorphisms of `ℝ`. -/
def AffineIncrEquiv.invHomeomorph :
    AffineIncrEquiv ≃ₜ AffineIncrEquiv where
  toFun A := A⁻¹
  invFun A := A⁻¹
  left_inv A := by simp
  right_inv A := by simp
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

@[simp] lemma AffineIncrEquiv.invHomeomorph_symm :
    invHomeomorph.symm = invHomeomorph := by
  ext1 A
  simp_rw [invHomeomorph]
  simp

@[simp] lemma AffineIncrEquiv.invHomeomorph_sq :
    invHomeomorph.trans invHomeomorph = .refl _ := by
  ext1 A
  simp_rw [invHomeomorph]
  simp

open Real in
/-- The space of orientation-preserving affine isomorphisms of ℝ is homeomorphic to ℝ². -/
noncomputable def AffineIncrEquiv.homeomorph_prod :
    AffineIncrEquiv ≃ₜ ℝ × ℝ where
  toFun A := ⟨log A.coefs.1, A.coefs.2⟩
  invFun p := mkOfCoefs (exp_pos p.1) p.2
  left_inv := by
    sorry -- **Issue #53** (affine-metrizable)
  right_inv := by
    sorry -- **Issue #53** (affine-metrizable)
  continuous_toFun := by
    sorry -- **Issue #53** (affine-metrizable)
  continuous_invFun := by
    sorry -- **Issue #53** (affine-metrizable)

/-- The topology of pointwise convergece on orientation-preserving affine isomorphisms of ℝ is
metrizable. -/
instance AffineIncrEquiv.metrizableSpace :
    TopologicalSpace.MetrizableSpace AffineIncrEquiv :=
  homeomorph_prod.isEmbedding.metrizableSpace

end affine



section affine_transform_of_cdf

namespace CumulativeDistributionFunction

/-- The action of orientation preserving affine isomorphisms on cumulative distribution
functions, so that for `A : AffineIncrEquiv` and `F : CumulativeDistributionFunction` we have
`(A • F)(x) = F(A⁻¹ x)`. -/
noncomputable def affineTransform
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    CumulativeDistributionFunction where
  toFun := fun x ↦ F (A⁻¹ x)
  mono' := F.mono'.comp (A⁻¹).mono
  right_continuous' := by
    have orientationPreservingAffineEquiv_image_Ici (B : AffineIncrEquiv) (x : ℝ) :
        Set.Ici (B x) = B '' (Set.Ici x) := by
      have B_Binv (z) : B (B⁻¹ z) = z := (AffineEquiv.apply_eq_iff_eq_symm_apply _).mpr rfl
      have Binv_B (z) : B⁻¹ (B z) = z := (AffineEquiv.apply_eq_iff_eq_symm_apply _).mpr rfl
      ext z
      refine ⟨fun hBz ↦ ?_, fun hBiz ↦ ?_⟩
      · refine ⟨B⁻¹ z, by simpa only [Binv_B, Set.mem_Ici] using (B⁻¹).mono hBz, B_Binv z⟩
      · obtain ⟨w, hw, Bw_eq⟩ := hBiz
        simpa [← Bw_eq] using B.mono hw
    intro x
    exact (F.right_continuous (A⁻¹ x)).comp
      (orientationPreservingAffineEquiv.continuous A⁻¹).continuousWithinAt
      (orientationPreservingAffineEquiv_image_Ici A⁻¹ x ▸ Set.mapsTo_image A⁻¹.val (Set.Ici x))
  tendsto_atTop := by
    apply Filter.Tendsto.comp F.tendsto_atTop
    · refine Monotone.tendsto_atTop_atTop (A⁻¹).mono ?A_inv_is_top_unbounded
      intro b
      refine ⟨A b, le_of_eq (EquivLike.left_inv A b).symm⟩
  tendsto_atBot := by
    apply Filter.Tendsto.comp F.tendsto_atBot
    · refine Monotone.tendsto_atBot_atBot (A⁻¹).mono ?A_inv_is_bottom_unbounded
      · intro b
        refine ⟨A b, le_of_eq <| EquivLike.apply_inv_apply ..⟩

@[simp] lemma affineTransform_apply_eq
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) (x : ℝ) :
    (F.affineTransform A) x = F (A⁻¹ x) := rfl

lemma affineTransform_mul_apply_eq_comp
    (F : CumulativeDistributionFunction) (A B : AffineIncrEquiv) :
    F.affineTransform (A * B) = (F.affineTransform B).affineTransform A := rfl

@[simp] lemma affineTransform_one_apply (F : CumulativeDistributionFunction) :
    F.affineTransform 1 = F := rfl

/-- The action of orientation preserving affine isomorphisms on cumulative distribution
functions, so that for `A : AffineIncrEquiv` and `F : CumulativeDistributionFunction` we
have `(A • F)(x) = F(A⁻¹ x)`. -/
noncomputable instance instMulActionAffineIncrEquiv :
    MulAction AffineIncrEquiv CumulativeDistributionFunction where
  smul A F := F.affineTransform A
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma mulAction_apply_eq
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) (x : ℝ):
    (A • F) x = F (A⁻¹ x) := rfl

@[simp] lemma mulAction_apply_eq_self_apply
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) (x : ℝ) :
    (A • F) (A x) = F x := by
  simp only [CumulativeDistributionFunction.mulAction_apply_eq]
  congr
  exact EquivLike.left_inv A x

-- Lemma: If X is a ℝ-valued random variable with c.d.f. F, then the c.d.f. of A • X is A • F.

/-- An affine transform of a c.d.f. is degenerate iff the c.d.f. itself is degenerate. -/
lemma affine_isDegenerate_iff
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) :
    (A • F).IsDegenerate ↔ F.IsDegenerate :=
  Iff.symm A.val.toEquiv.forall_congr_left

/-- An affine transform of a c.d.f. is continuious at `A x` if the c.d.f. itself is continuous
at `x`. -/
lemma affine_continuousAt_of_continuousAt
    {F : CumulativeDistributionFunction} {x : ℝ} (F_cont : ContinuousAt F x)
    (A : AffineIncrEquiv) :
    ContinuousAt (A • F) (A x) := by
  apply ContinuousAt.comp _ ((A⁻¹).val.continuous_of_finiteDimensional).continuousAt
  convert F_cont
  exact EquivLike.apply_inv_apply ..

/-- An affine transform of a c.d.f. is continuious at `A x` if and only if the c.d.f. itself is
continuous at `x`. -/
lemma affine_continuousAt_iff
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) (x : ℝ) :
    ContinuousAt (A • F) x ↔ ContinuousAt F (A⁻¹ x) := by
  constructor
  · intro AF_cont
    convert affine_continuousAt_of_continuousAt AF_cont A⁻¹
    simp
  · intro F_cont
    convert affine_continuousAt_of_continuousAt F_cont A
    exact (EquivLike.right_inv A x).symm

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
  · simp [AffineMap.extend, hA]; rfl
  · simp only [ne_eq, not_lt] at *
    have hA' : A.toAffineMap.coefs_of_field.1 < 0 := lt_of_le_of_ne hA obs
    simp [AffineMap.extend, hA']; rfl

lemma AffineEquiv.extend_top' (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.toAffineMap.extend ⊤ =
      if 0 < A.toAffineMap.coefs_of_field.1 then ⊤ else ⊥ := by
  have obs : A.toAffineMap.coefs_of_field.1 ≠ 0 :=
    coefs_of_field_fst_ne_zero A
  by_cases hA : 0 < A.toAffineMap.coefs_of_field.1
  · simp [AffineMap.extend, hA]; rfl
  · simp only [ne_eq, not_lt] at *
    have hA' : A.toAffineMap.coefs_of_field.1 < 0 := lt_of_le_of_ne hA obs
    simp [AffineMap.extend, hA']; rfl

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

/-- Extend an affine equivalence `ℝ → ℝ` to an equivalence `[-∞,+∞] → [-∞,+∞]`. -/
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

@[simp] lemma AffineEquiv.extend_ofReal (A : ℝ ≃ᵃ[ℝ] ℝ) (x : ℝ) :
    A.extend x = A x :=
  rfl

@[simp] lemma AffineEquiv.extend_symm (A : ℝ ≃ᵃ[ℝ] ℝ) :
    A.extend.symm = A.symm.extend := by
  rfl

/-- Extend an orientation-preserving affine equivalence `ℝ → ℝ` to an
equivalence `[-∞,+∞] → [-∞,+∞]`. -/
noncomputable abbrev AffineIncrEquiv.extend (A : AffineIncrEquiv) : EReal ≃ EReal :=
    A.val.extend

@[simp] lemma AffineIncrEquiv.extend_bot (A : AffineIncrEquiv) :
    A.extend ⊥ = ⊥ := by
  simp [show 0 < A.val.toAffineMap.coefs_of_field.1 from A.isOrientationPreserving]

@[simp] lemma AffineIncrEquiv.extend_top (A : AffineIncrEquiv) :
    A.extend ⊤ = ⊤ := by
  simp [show 0 < A.val.toAffineMap.coefs_of_field.1 from A.isOrientationPreserving]

@[simp] lemma AffineIncrEquiv.extend_ofReal (A : AffineIncrEquiv) (x : ℝ) :
    A.extend x = A x :=
  rfl

@[simp] lemma AffineIncrEquiv.extend_symm (A : AffineIncrEquiv) :
    A.extend.symm = (A⁻¹).extend :=
  AffineEquiv.extend_symm A.val

end extend

end affine_transform_of_cdf
