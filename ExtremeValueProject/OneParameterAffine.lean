/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Joel Kronqvist, ...
-/
import Mathlib
import ExtremeValueProject.AffineTransformation

section cauchy_hamel_functional_equation

open Real Set Pointwise MeasureTheory

namespace RealAdditive

variable {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
include f f_add

lemma map_zero : f 0 = 0 := by
  suffices h : f 0 + f 0 = f 0 by simpa using congrArg (· - f 0) h
  simp [← f_add 0 0]

def homomorphism : ℝ →+ ℝ where
  toFun := f
  map_zero' := map_zero f_add
  map_add' := f_add

lemma map_neg' (x : ℝ) : f (- x) = - f x := map_neg (homomorphism f_add) x

lemma map_sub' (t₁ t₂ : ℝ) : f (t₁ - t₂) = f t₁ - f t₂ :=
  map_sub (homomorphism f_add) t₁ t₂

lemma map_nmul (n : ℕ) (x : ℝ) : f (n * x) = n * f x := by
  repeat rw [← nsmul_eq_mul]
  exact map_nsmul (homomorphism f_add) n x

lemma map_zmul (z : ℤ) (x : ℝ) : f (z * x) = z * f x := by
  repeat rw [← zsmul_eq_mul]
  exact map_zsmul (homomorphism f_add) z x

lemma map_inv_nat (n : ℕ) (n_ne_zero : n ≠ 0) (x : ℝ) :
    f ((n : ℝ)⁻¹ * x) = (n : ℝ)⁻¹ * f x := by
  rify at n_ne_zero
  apply mul_left_cancel₀ n_ne_zero
  rw [← map_nmul f_add]
  field_simp

lemma map_rat (q : ℚ) (x : ℝ) : f (q * x) = q * f x := by
  rw [← Rat.num_div_den q]
  push_cast
  calc f (q.num / q.den * x)
    _ = f (q.num * ((q.den : ℝ)⁻¹ * x)) := by field_simp
    _ = q.num * f ((q.den : ℝ)⁻¹ * x) := map_zmul f_add q.num ((q.den : ℝ)⁻¹ * x)
    _ = q.num * ((q.den : ℝ)⁻¹ * f x) := by rw [map_inv_nat f_add q.den q.den_nz x]
    _ = q.num / q.den * f x := by field_simp

end RealAdditive

lemma eq_iUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃ x ∈ U, connectedComponentIn U x := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [iUnion_subset_iff]
    intro x x_in_U
    exact connectedComponentIn_subset U x

lemma eq_sUnion_connectedComponentIn (U : Set ℝ) :
    U = ⋃₀ {C | ∃ x ∈ U, C = connectedComponentIn U x} := by
  apply subset_antisymm
  · intro x x_in_U
    simpa using ⟨x, x_in_U, mem_connectedComponentIn x_in_U⟩
  · simp only [sUnion_subset_iff, mem_setOf_eq, forall_exists_index, and_imp]
    intro C x x_in_U hC
    simpa [hC] using connectedComponentIn_subset U x

-- TODO: This seems to be missing in Mathlib. Compare with `connectedComponent_disjoint`.
lemma connectedComponentIn_disjoint {α : Type*} [TopologicalSpace α] {s : Set α} {x y : α}
    (h : connectedComponentIn s x ≠ connectedComponentIn s y) :
    Disjoint (connectedComponentIn s x) (connectedComponentIn s y) :=
  Set.disjoint_left.2 fun _ hzx hzy ↦
    h <| (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm

-- TODO: Maybe not really needed; we have `connectedComponentIn_disjoint`.
lemma pairwise_disjoint_connectedComponentIn (U : Set ℝ) :
    {C | ∃ x ∈ U, C = connectedComponentIn U x}.Pairwise Disjoint := by
  intro C hC D hD hCD
  obtain ⟨x, x_in_U, C_eq⟩ := hC
  obtain ⟨y, y_in_U, D_eq⟩ := hD
  rw [C_eq, D_eq] at hCD ⊢
  exact connectedComponentIn_disjoint hCD

-- TODO: Is this missing from Mathlib?
lemma IsOpen.isOpen_connectedComponentIn {α : Type*} [TopologicalSpace α]
    {s : Set α} (s_loc_conn : LocallyConnectedSpace s) (s_open : IsOpen s) {x : α} :
    IsOpen (connectedComponentIn s x) := by
  by_cases hxs : x ∉ s
  · simp [connectedComponentIn, hxs]
  rw [not_not] at hxs
  simp only [connectedComponentIn, hxs, ↓reduceDIte]
  obtain ⟨U, U_open, hU⟩ := @isOpen_connectedComponent s _ s_loc_conn ⟨x, hxs⟩
  have obs : Subtype.val '' connectedComponent ⟨x, hxs⟩ = U ∩ s := by
    ext y
    simp only [mem_image, Subtype.exists, exists_and_right, exists_eq_right, mem_inter_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨y_in_s, hy⟩
      exact ⟨by simpa [← hU] using hy, y_in_s⟩
    · intro ⟨y_in_U, y_in_s⟩
      exact ⟨y_in_s, by simpa [← hU] using y_in_U⟩
  simpa [obs] using U_open.inter s_open

private lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen_of_nonempty
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A)
    (As_nonemp : ∀ A ∈ As, A.Nonempty)  :
    As.Countable := by
  obtain ⟨s, s_ctble, s_dense⟩ := sep.exists_countable_dense
  have aux (A) (hA : A ∈ As) : ∃ x ∈ s, x ∈ A :=
    s_dense.exists_mem_open (As_open A hA) (As_nonemp A hA)
  set g : As → s := fun A ↦ ⟨(aux A.val A.prop).choose, (aux A.val A.prop).choose_spec.1⟩ with def_g
  have hg (A : As) : (g A).val ∈ A.val := (aux A.val A.prop).choose_spec.2
  have g_inj : Function.Injective g := by
    intro A B hAB
    by_contra maybe_ne
    apply (As_disj A.prop B.prop (Subtype.coe_ne_coe.mpr maybe_ne)).notMem_of_mem_left (hg A)
    simpa [← hAB] using (hg B)
  rw [Set.countable_iff_exists_injective] at s_ctble ⊢
  obtain ⟨f, f_inj⟩ := s_ctble
  refine ⟨f ∘ g, f_inj.comp g_inj⟩

-- TODO: Is this missing from Mathlib?
lemma TopologicalSpace.SeparableSpace.countable_of_disjoint_of_isOpen
    {α : Type*} [TopologicalSpace α] (sep : SeparableSpace α) {As : Set (Set α)}
    (As_disj : As.Pairwise Disjoint) (As_open : ∀ A ∈ As, IsOpen A) :
    As.Countable := by
  suffices (As \ {∅}).Countable from
    Countable.mono (show As ⊆ (As \ {∅}) ∪ {∅} by simp) (this.union (countable_singleton ∅))
  apply countable_of_disjoint_of_isOpen_of_nonempty sep
  · exact As_disj.mono sdiff_subset
  · exact fun A hA ↦ As_open A (mem_of_mem_sdiff hA)
  · intro A hA
    simp only [mem_sdiff, mem_singleton_iff] at hA
    exact nonempty_iff_ne_empty.mpr hA.2

lemma ConnectedComponents.mk_eq_mk_iff {α : Type*} [TopologicalSpace α] {x y : α} :
    ConnectedComponents.mk x = ConnectedComponents.mk y
      ↔ connectedComponent x = connectedComponent y := by
  simp_all only [coe_eq_coe]

lemma ConnectedComponents.mk_out_eq {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
    ConnectedComponents.mk (Quot.out C) = C :=
  Quotient.out_eq _

--lemma ConnectedComponents.out_mem_connectedComponent {α : Type*} [TopologicalSpace α] (C : ConnectedComponents α) :
--    (Quot.out C) ∈ connectedComponent (Quot.out C) := by
--  exact mem_connectedComponent

lemma TopologicalSpace.SeparableSpace.countable_connectedComponents {α : Type*} [TopologicalSpace α]
    [LocallyConnectedSpace α] (sep : SeparableSpace α) :
    Countable (ConnectedComponents α) := by
  set φ : ConnectedComponents α → Set α := (fun A ↦ connectedComponent (Quot.out A)) with def_φ
  set As : Set (Set α) := Set.range φ with def_As
  have key := @countable_of_disjoint_of_isOpen α _ sep As ?_ ?_
  · obtain ⟨f, f_inj⟩ := Set.countable_iff_exists_injective.mp key
    apply (countable_iff_exists_injective _).mpr ⟨fun C ↦ f (rangeFactorization φ C), f_inj.comp ?_⟩
    intro C₁ C₂ hC
    simp only [rangeFactorization, Subtype.mk.injEq, φ, As] at hC
    exact Quotient.out_equiv_out.mp hC
  · intro A₁ hA₁ A₂ hA₂ hA_ne
    simp only [mem_range, As, φ] at hA₁ hA₂
    obtain ⟨C₁, hC₁⟩ := hA₁
    obtain ⟨C₂, hC₂⟩ := hA₂
    rw [← hC₁, ← hC₂] at hA_ne ⊢
    exact connectedComponent_disjoint hA_ne
  · intro A hA
    simp only [def_As, mem_range, As, φ] at hA
    obtain ⟨C, hAC⟩ := hA
    simpa [← hAC] using isOpen_connectedComponent

-- TODO: Missing from Mathlib?
open TopologicalSpace in
lemma IsOpen.separableSpace {α : Type*} [TopologicalSpace α] [SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    SeparableSpace s := by
  obtain ⟨c, c_ctble, c_dense⟩ := ‹SeparableSpace α›.exists_countable_dense
  refine ⟨⟨(↑) ⁻¹' c, c_ctble.preimage Subtype.val_injective, ?_⟩⟩
  simpa [Subtype.dense_iff] using c_dense.open_subset_closure_inter s_open

open TopologicalSpace in
lemma IsOpen.countable_setOf_connectedComponentIn
    {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α] [sep : SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    Countable {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} := by
  have : LocallyConnectedSpace s := s_open.locallyConnectedSpace
  have sep_s : SeparableSpace s := s_open.separableSpace
  have key := SeparableSpace.countable_connectedComponents (α := s) inferInstance
  let ψ : {C : Set α | ∃ x ∈ s, C = connectedComponentIn s x} → ConnectedComponents s :=
    fun C ↦ ConnectedComponents.mk
            ⟨(mem_setOf_eq.mp C.prop).choose, (mem_setOf_eq.mp C.prop).choose_spec.1⟩

  have ψ_inj : Function.Injective ψ := by
    intro C₁ C₂ hψC
    ext1
    have aux₁ := (mem_setOf_eq.mp C₁.prop).choose_spec
    have aux₂ := (mem_setOf_eq.mp C₂.prop).choose_spec
    rw [aux₁.2, aux₂.2]
    simp only [ψ, ConnectedComponents.coe_eq_coe] at hψC
    rw [connectedComponentIn_eq_image aux₁.1, connectedComponentIn_eq_image aux₂.1]
    exact congr_arg (Subtype.val '' ·) hψC
  exact Function.Injective.countable ψ_inj

-- TODO: Hopefully this is not needed and `Real.convex_iff_isPreconnected` is enough.
lemma Real.eq_Ioo_or_Iio_or_Ioi_or_univ_of_isOpen_of_isConnected
    {U : Set ℝ} (U_open : IsOpen U) (U_conn : IsConnected U) :
    (∃ a b, U = Ioo a b) ∨ (∃ b, U = Iio b) ∨ (∃ a, U = Ioi a) ∨ U = univ := by
  sorry

lemma exists_interval_measure_inter_gt_mul_measure
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A) (A_fin : volume A < ⊤)
    {r : ENNReal} (r_lt_one : r < 1) :
    ∃ (J : Set ℝ), IsConnected J ∧ (interior A).Nonempty ∧ volume (J ∩ A) > r * volume J := by
  sorry

lemma isPreconnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsPreconnected J := by
  sorry

lemma isConnected_of_Ioo_subset_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (J_ge : Ioo a b ⊆ J) (J_le : J ⊆ Icc a b) :
    IsConnected J :=
  ⟨(nonempty_Ioo.mpr hab).mono J_ge, isPreconnected_of_Ioo_subset_of_subset_Icc J_ge J_le⟩

lemma union_add_self_subset_Icc_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (J_le : J ⊆ Icc a b) (t : ℝ) :
    J ∪ ({t} + J) ⊆ Icc (min a (a + t)) (max b (b + t)) := by
  intro x hx
  cases' hx with hx hx
  · exact ⟨min_le_of_left_le (J_le hx).1, le_max_of_le_left (J_le hx).2⟩
  · refine ⟨min_le_of_right_le ?_, le_max_of_le_right ?_⟩
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).1]
    · simp only [singleton_add, image_add_left, mem_preimage] at hx
      linarith [(J_le hx).2]

lemma Ioo_subset_union_add_self_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    Ioo (min a (a + t)) (max b (b + t)) ⊆ J ∪ ({t} + J) := by
  sorry -- TODO: Add issue.

lemma volume_union_add_self_ge_of_Ioo_subset
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_ge : Ioo a b ⊆ J) (t : ℝ) (ht : |t| < b - a) :
    ENNReal.ofReal (b - a + |t|) ≤ volume (J ∪ ({t} + J)) := by
  sorry

lemma volume_union_add_self_le_of_subset_Icc
    {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (J_le : J ⊆ Icc a b) (t : ℝ) :
    volume (J ∪ ({t} + J)) ≤ ENNReal.ofReal (b - a + |t|) := by
  sorry

lemma exists_Ioo_subset_diff_self_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by
  sorry

lemma exists_Ioo_subset_diff_of_measure_pos {A B : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    (B_mble : MeasurableSet B) (B_pos : 0 < volume B) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A - B := by
  sorry

lemma exists_Ioo_subset_add_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A + A := by
  obtain ⟨a, b, a_lt_b, hab⟩ := exists_Ioo_subset_diff_of_measure_pos
        A_mble A_pos A_mble.neg (by simpa only [Measure.measure_neg] using A_pos)
  refine ⟨a, b, a_lt_b, by simpa only [sub_neg_eq_add] using hab⟩

lemma eq_top_of_subgroup_of_measure_pos {S : AddSubgroup ℝ}
    {A : Set ℝ} (A_le_S : A ⊆ S) (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    S = ⊤ := by
  sorry

lemma exists_forall_ub_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂)= f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, f x ≤ c := by
  obtain ⟨x₁, x₂, x₁_lt_x₂, h_Ioo⟩ := exists_Ioo_subset_add_of_measure_pos A_mble A_pos
  let y := (x₁ + x₂) / 2
  let δ := (x₂ - x₁) / 2
  use δ; constructor; positivity
  use 2*M - f y
  intro t abs_t_lt_δ
  obtain ⟨a, ha, b, hb, h_add_y_t⟩ := (by grind : y + t ∈ A + A)
  calc
        f t
    _ = f (a + b - y) := by rw [(by linarith : t = a + b - y)]
    _ = f a + f b - f y := by rw [RealAdditive.map_sub' f_add, f_add]
    _ ≤ 2*M - f y := by
      grw [f_bdd_on_A a ha, f_bdd_on_A b hb, two_mul]

lemma exists_forall_lb_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, c ≤ f x := by
  obtain ⟨x₁, x₂, x₁_lt_x₂, h_Ioo⟩ := exists_Ioo_subset_add_of_measure_pos A_mble A_pos
  obtain ⟨δ, hδ, c, ub_forall⟩ :=
    exists_forall_ub_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  use δ ; constructor; exact hδ
  use (-c)
  intro t abs_t_lt_δ
  have hf := ub_forall (-t) (by simpa only [neg_mem_Ioo_iff, neg_neg] using abs_t_lt_δ)
  calc
        - c
    _ ≤ - f (-t) := by linarith
    _ = f t := by simp [RealAdditive.map_neg' f_add]

lemma exists_forall_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, |f x| ≤ c := by
  obtain ⟨δ₁, hδ₁, c₁, f_ub⟩ :=
    exists_forall_ub_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  obtain ⟨δ₂, hδ₂, c₂, f_lb⟩ :=
    exists_forall_lb_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  use (min δ₁ δ₂); constructor; positivity
  use (max |c₁| |c₂|)
  intro x hx
  rw [Set.mem_Ioo, neg_lt, lt_min_iff, lt_min_iff] at hx
  obtain ⟨⟨neg_x_lt_δ₁, neg_x_lt_δ₂⟩, x_lt_δ₁, x_lt_δ₂⟩ := hx
  have hx₁ : x ∈ Ioo (-δ₁) δ₁ := by
       rw [Set.mem_Ioo]
       exact And.intro (neg_lt_of_neg_lt neg_x_lt_δ₁) x_lt_δ₁
  have hx₂ : x ∈ Ioo (-δ₂) δ₂ := by
       rw [Set.mem_Ioo]
       exact And.intro (neg_lt_of_neg_lt neg_x_lt_δ₂) x_lt_δ₂
  apply abs_le.mpr; constructor
  · calc
      - max |c₁| |c₂| ≤ - |c₂| := by grw [@Std.right_le_max _ _ _ _ _ |c₁| |c₂|]
      _ ≤ c₂ := neg_abs_le c₂
      _ ≤ f x := f_lb x hx₂
  · calc
      f x ≤ c₁ := f_ub x hx₁
      _ ≤ |c₁| := le_abs_self c₁
      _ ≤ max |c₁| |c₂|:= Std.left_le_max

open Topology in
lemma exists_nhd_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ B ∈ 𝓝 (0 : ℝ), ∃ c, ∀ x ∈ B, |f x| ≤ c := by
  obtain ⟨δ, δ_pos, hδ⟩ :=
    exists_forall_abs_le_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  exact ⟨Ioo (-δ) δ, Ioo_mem_nhds (by linarith) δ_pos, hδ⟩


open Filter Topology

lemma linear_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) (x : ℝ) :
    f x = (f 1) * x := by
  suffices h : |f x - x * f 1| = 0 by simpa [sub_eq_zero, mul_comm x (f 1)] using h
  rcases exists_nhd_abs_le_of_additive_of_le_on_measure_pos f_add A_mble
                                                            A_pos f_bdd_on_A
    with ⟨B, B_in_nhds_0, c, f_bdd_on_B⟩
  rcases mem_nhds_iff_exists_Ioo_subset.mp B_in_nhds_0
    with ⟨a, b, ⟨zero_in_Ioo, Ioo_subset_B⟩⟩
  obtain ⟨a_neg, b_pos⟩ := Set.mem_Ioo.mp zero_in_Ioo
  let δ := min |a| |b|
  have δ_pos : 0 < δ := lt_min (abs_pos_of_neg a_neg) (abs_pos_of_pos b_pos)
  have f_bdd_within
      {x : ℝ} (n : ℕ) (n_ne_zero : n ≠ 0) (x_in_Ioo : |x| < δ / n) :
        |f x| ≤ c / n := by
    have n_pos : (0 : ℝ ) < (n : ℝ) :=
      Nat.cast_pos'.mpr (Nat.zero_lt_of_ne_zero n_ne_zero)
    suffices h : |n * f x| ≤ c by simpa [le_div_iff₀' n_pos] using h
    have x_in_Ioo : |n * x| < δ := by simpa using (lt_div_iff₀' n_pos).mp x_in_Ioo
    have x_in_Ioo : n * x ∈ Ioo a b := by
      have l : -δ < n * x := by exact neg_lt_of_abs_lt x_in_Ioo
      have r : n * x < δ := by exact lt_of_abs_lt x_in_Ioo
      have nx_δ_Ioo : n * x ∈ Ioo (-δ) δ := Set.mem_Ioo.mpr ⟨l, r⟩
      have sub_Ioo : Ioo (-δ) δ ⊆ Ioo a b := by
        apply Set.Ioo_subset_Ioo
        · grw [le_neg, ← abs_of_neg a_neg, ← min_le_left |a| |b|]
        · grw [← abs_of_pos b_pos, ← min_le_right |a| |b|]
      exact mem_Ioo.mpr (sub_Ioo nx_δ_Ioo)
    rw [← RealAdditive.map_nmul f_add n x]
    exact f_bdd_on_B (n * x) (Ioo_subset_B x_in_Ioo)
  have hh (n : ℕ) (n_pos : 0 < n) : ∃ q : ℚ, |x - q| < δ / n := by
    rify at n_pos
    exact exists_rat_near x (div_pos δ_pos n_pos)
  have ub  : ∀ᶠ (n : ℕ) in atTop, |f x - x * f 1| ≤ (c + δ * |f 1|) / n := by
    filter_upwards [Ioi_mem_atTop 0] with n hn
    have n_pos : 0 < n := Set.mem_Ioi.mp hn
    have n_ne_zero : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
    rcases hh n n_pos with ⟨q, hq⟩
    have hq_symm : |q - x| < δ / n := by
        rw [abs_sub_comm]
        exact hq
    calc |f x - x * f 1|
      _ = |f (x - q) + q * f 1 - x * f 1| := by
        simp [RealAdditive.map_sub' f_add, ← RealAdditive.map_rat f_add]
      _ = |f (x - q) + (q - x) * f 1| := by group
      _ ≤ |f (x - q)| + |(q - x)| * |f 1| := by grw [abs_add_le, abs_mul]
      _ ≤ c / n + |(q - x)| * |f 1| :=
        add_le_add_left (f_bdd_within n n_ne_zero hq) (|q - x| * |f 1|)
      _ ≤ c / n + (δ / n) * |f 1| := by
        by_cases h_zero : 0 = |f 1|
        · simp [← h_zero]
        · have h_zero : 0 < |f 1| := lt_of_le_of_ne (abs_nonneg (f 1)) h_zero
          suffices h : |q - x| * |f 1| < (δ / ↑n) * |f 1| by linarith
          exact (mul_lt_mul_iff_left₀ h_zero).mpr hq_symm
      _ = (c + δ * |f 1|) / n := by field_simp
  have tendsto_zero : Filter.Tendsto (fun n : ℕ ↦ |f x - x * f 1|) atTop (𝓝 0) :=
    have lb : ∀ᶠ n : ℕ in atTop, 0 ≤ |f x - x * f 1| := by
      filter_upwards [Ioi_mem_atTop 0] with _ _
      exact abs_nonneg (f x - x * f 1)
    have ub_tendsto_zero :
        Filter.Tendsto (fun n : ℕ ↦ (c + δ * |f 1|) * (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (c + δ * |f 1|)
    squeeze_zero' lb ub ub_tendsto_zero
  exact tendsto_const_nhds_iff.mp tendsto_zero

open ENNReal in
lemma linear_of_additive_of_measurable
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂) (f_mble : Measurable f) (x : ℝ) :
    f x = (f 1) * x := by
  set As : ℕ → Set ℝ := fun n ↦ {y | f y ≤ n} with def_As
  have cover : ⋃ n, As n = ⊤ := by
    ext x
    simp [exists_nat_ge (f x), def_As]
  have As_mble (n : ℕ) : MeasurableSet (As n) := f_mble measurableSet_Iic
  obtain ⟨n, hn⟩ : ∃ n, 0 < volume (As n) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simp [cover]
  exact linear_of_additive_of_le_on_measure_pos f_add (As_mble n) hn (M := n) (by simp [def_As]) x

/-- A measurable additive map ℝ → ℝ is linear.
(The only measurable solutions to the Cauchy-Hamel functional equation are the obvious ones.) -/
lemma eq_const_mul_of_additive_of_measurable {f : ℝ → ℝ}
    (f_add : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ + f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ α * s := by
  use f 1
  ext x
  exact linear_of_additive_of_measurable f_add f_mble x

/-- A measurable multiplicative map ℝ → (0,+∞) is of the form s ↦ exp(α * s) for some α ∈ ℝ.
(The only measurable solutions to the multiplicative version of the Cauchy-Hamel functional
equation are the obvious ones.) -/
lemma eq_exp_const_mul_of_multiplicative_of_measurable {f : ℝ → ℝ} (f_pos : ∀ s, 0 < f s)
    (f_multiplicative : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ * f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ exp (α * s) := by
  let g := fun s ↦ log (f s)
  have f_eq_exp_g (s) : f s = exp (g s) := by
    simpa [g] using (exp_log (f_pos s)).symm
  have g_mble : Measurable g := measurable_log.comp f_mble
  have g_additive (s₁ s₂) : g (s₁ + s₂) = g s₁ + g s₂ := by
    simpa only [g, f_multiplicative] using log_mul (f_pos _).ne.symm (f_pos _).ne.symm
  obtain ⟨α, key⟩ := eq_const_mul_of_additive_of_measurable g_additive g_mble
  refine ⟨α, by ext s ; rw [f_eq_exp_g, key]⟩

lemma eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable
    {α : ℝ} (α_ne_zero : α ≠ 0) {b : ℝ → ℝ}
    (b_eqn : ∀ s t : ℝ, b (s + t) = rexp (α * s) * b t + b s) :
    ∃ c : ℝ, ∀ t : ℝ, b t = c * (1 - rexp (α * t)) := by
  have b_zero : b 0 = 0 := by simpa using b_eqn 0 0
  let c := - (b 1 / (rexp (α * 1) - 1))
  have refactored (s t : ℝ) :
      (rexp (α * s) - 1) * b t = (rexp (α * t) - 1) * b s := calc
        (rexp (α * s) - 1) * b t
    _ = rexp (α * s) * b t + b s - b t - b s := by ring
    _ = b (s + t) - b t - b s                := by rw [b_eqn]
    _ = b (t + s) - b t - b s                := by rw [add_comm s t]
    _ = rexp (α * t) * b s + b t - b t - b s := by rw [b_eqn]
    _ = (rexp (α * t) - 1) * b s             := by ring
  use c
  intro t
  by_cases t_zero : t = 0
  · simp [t_zero, b_zero]
  · have aux : (rexp (α * 1) - 1) ≠ 0 := by simp [sub_eq_zero, α_ne_zero]
    calc  b t
      _ = b t * ((rexp (α * 1) - 1) / (rexp (α * 1) - 1))     := by rw [div_self aux] ; ring
      _ = (rexp (α * 1) - 1) * b t / (rexp (α * 1) - 1)       := by ring
      _ = (rexp (α * t) - 1) * b 1 / (rexp (α * 1) - 1)       :=
        congrArg (· / (rexp (α * 1) - 1)) (refactored 1 t)
      _ = c * (1 - rexp (α * t))                              := by ring

end cauchy_hamel_functional_equation


section one_parameter_subgroups_of_affine_transformations

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where `Aₛ x = x + β * s`.
(`β` is a real parameter: each `β` gives a different (but related) homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex₀ (β : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs zero_lt_one (β * s.toAdd)
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
  toFun s := .mkOfCoefs (show 0 < Real.exp (α * s.toAdd) from Real.exp_pos _)
              (c * (1 - Real.exp (α * s.toAdd)))
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp [mul_add, Real.exp_add]
    ring

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_fst {β s : ℝ} :
    (homOfIndex₀ β s).coefs.1 = 1 := by
  simp [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs]

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_snd {β s : ℝ} :
    (homOfIndex₀ β s).coefs.2 = β * s := by
  simp only [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_fst {α c s : ℝ} :
    (homOfIndex α c s).coefs.1 = Real.exp (α * s) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs, Real.exp_eq_exp]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_snd {α c s : ℝ} :
    (homOfIndex α c s).coefs.2 = c * (1 - Real.exp (α * s)) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero' (β : ℝ) :
    homOfIndex₀ β (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero (β : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex₀_zero_apply' (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_zero_apply (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_add (β : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex₀ β (s₁ + s₂) = homOfIndex₀ β s₁ * homOfIndex₀ β s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_inv (β : ℝ) (s : ℝ) :
    (homOfIndex₀ β s)⁻¹ = homOfIndex₀ β (-s) := by
  have obs := homOfIndex₀_add β s (-s)
  simp only [add_neg_cancel, homOfIndex₀_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex₀_add_apply {β : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex₀ β (s₁ + s₂) x = homOfIndex₀ β s₁ (homOfIndex₀ β s₂ x) := by
  simp only [homOfIndex₀_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex₀_eq_homOfIndex₀_one_mul {β s : ℝ} :
    homOfIndex₀ β s = homOfIndex₀ 1 (β * s) := by
  ext x
  simp [mul_comm]

lemma AffineIncrEquiv.conjugate_homOfIndex₀ (A : AffineIncrEquiv) (β : ℝ) (s : ℝ) :
    A * homOfIndex₀ β s * A⁻¹ = homOfIndex₀ (β * A.coefs.1) s := by
  sorry -- **Issue #46**

lemma AffineIncrEquiv.homOfIndex_zero_ext_of_coefs
    {A₁ : AffineIncrEquiv} {t β : ℝ} (h : A₁.coefs = ((homOfIndex₀ β) t).coefs) :
    A₁ = (homOfIndex₀ β) t := by
  ext x
  simp [h]

@[simp] lemma AffineIncrEquiv.homOfIndex_zero' (α c : ℝ) :
    homOfIndex α c (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex_zero (α c : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex_zero_apply' (α c : ℝ) (x : ℝ) :
    homOfIndex α c (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_zero_apply (α c : ℝ) (x : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_add (α c : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex α c (s₁ + s₂) = homOfIndex α c s₁ * homOfIndex α c s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex_inv (α c : ℝ) (s : ℝ) :
    (homOfIndex α c s)⁻¹ = homOfIndex α c (-s) := by
  have obs := homOfIndex_add α c s (-s)
  simp only [add_neg_cancel, homOfIndex_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex_add_apply {α c : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex α c (s₁ + s₂) x = homOfIndex α c s₁ (homOfIndex α c s₂ x) := by
  simp only [homOfIndex_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex_eq_homOfIndex_one_mul {α c s : ℝ} :
    homOfIndex α c s = homOfIndex 1 c (α * s) := by
  ext x
  simp

lemma AffineIncrEquiv.conjugate_homOfIndex (A : AffineIncrEquiv) (α c : ℝ) (s : ℝ) :
    A * homOfIndex α c s * A⁻¹ = homOfIndex α (A c) s := by
  sorry -- **Issue #46**

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
  obtain ⟨s, _, hs⟩ := hA
  simp only [← hs, apply_eq, homOfIndex_coefs_fst, homOfIndex_coefs_snd]
  ring

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex_iff_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    A ∈ subGroupOfIndex α c ↔ A c = c := by
  sorry -- **Issue 45**

/-- Functional equation for scaling coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_fst
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.1 = (f s₁).coefs.1 * (f s₂).coefs.1 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

/-- Functional equation for translation coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_snd
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.2 = (f s₁).coefs.1 * (f s₂).coefs.2 + (f s₁).coefs.2 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

open Real

lemma eq_of_functional_eqn_of_ne_zero {f : ℝ → ℝ} {α : ℝ} (α_ne_zero : α ≠ 0)
    (f_eqn : ∀ s₁ s₂, f (s₁ + s₂) = exp (α * s₁) * f s₂ + f s₁) :
    ∃ c, f = fun s ↦ c * (1 - exp (α * s)) := by
  sorry

/-- We endow the space of orientation-preserving affine isomorphisms of `ℝ` with the Borel
σ-algebra of the topology of pointwise convergence. -/
instance : MeasurableSpace AffineIncrEquiv := borel AffineIncrEquiv

instance : BorelSpace AffineIncrEquiv := ⟨rfl⟩

lemma AffineIncrEquiv.measurable_coefs_fst :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.1) :=
  continuous_coefs_fst.measurable

lemma AffineIncrEquiv.measurable_coefs_snd :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.2) :=
  continuous_coefs_snd.measurable

lemma AffineIncrEquiv.continuous_mkOfCoefs :
    Continuous fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  apply (continuous_induced_rng ..).mpr
  exact continuous_pi (by continuity)

lemma AffineIncrEquiv.measurable_mkOfCoefs :
    Measurable fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  have _bs1 : BorelSpace {a : ℝ // 0 < a} := Subtype.borelSpace _
  have _bs2 : BorelSpace ({a : ℝ // 0 < a} × ℝ) := Prod.borelSpace
  exact continuous_mkOfCoefs.measurable

lemma AffineIncrEquiv.continuous_of_continuous_coefs {Z : Type*} [TopologicalSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Continuous fun z ↦ (f z).coefs.1)
    (f_snd_cont : Continuous fun z ↦ (f z).coefs.2) :
    Continuous f := by
  convert AffineIncrEquiv.continuous_mkOfCoefs.comp <|
    show Continuous fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      continuity
  ext z x
  simp

lemma AffineIncrEquiv.measurable_of_measurable_coefs {Z : Type*} [MeasurableSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Measurable fun z ↦ (f z).coefs.1)
    (f_snd_cont : Measurable fun z ↦ (f z).coefs.2) :
    Measurable f := by
  convert AffineIncrEquiv.measurable_mkOfCoefs.comp <|
    show Measurable fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      measurability
  ext z x
  simp

instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)

instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

lemma measurable_toAdd :
    Measurable (fun (s : Multiplicative ℝ) ↦ s.toAdd) :=
  continuous_toAdd.measurable

lemma measurable_toMultiplicative :
    Measurable (fun (s : ℝ) ↦ Multiplicative.ofAdd s) :=
  continuous_ofAdd.measurable

noncomputable def AffineIncrEquiv.hom_coef_fst
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) :=
  fun s ↦ (f s).coefs.1

noncomputable def AffineIncrEquiv.hom_coef_snd
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) :=
  fun s ↦ (f s).coefs.2

lemma AffineIncrEquiv.hom_ext
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv)
    (g : MonoidHom (Multiplicative ℝ) AffineIncrEquiv)
    (fst_coefs_eq : hom_coef_fst f = hom_coef_fst g)
    (snd_coefs_eq : hom_coef_snd f = hom_coef_snd g) : f = g := by
  ext s x; simp
  change hom_coef_fst f s * x + hom_coef_snd f s
       = hom_coef_fst g s * x + hom_coef_snd g s
  rw [fst_coefs_eq, snd_coefs_eq]

lemma AffineIncrEquiv.homOfIndex_iff_ext
    {α c : ℝ}
    {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv}
    (coef_1_eq : hom_coef_fst f = λ s : ℝ ↦ Real.exp (α * s))
    (coef_2_eq : hom_coef_snd f = λ s : ℝ ↦ c * (1 - Real.exp (α * s))) :
      f = AffineIncrEquiv.homOfIndex α c := by
  apply AffineIncrEquiv.hom_ext
  · rw [coef_1_eq]
    unfold hom_coef_fst
    simp; rfl
  · rw [coef_2_eq]
    unfold hom_coef_snd
    simp; rfl

lemma AffineIncrEquiv.homOfIndex₀_iff_ext
    {β : ℝ} {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv}
    (coef_1_one : hom_coef_fst f = 1)
    (coef_2_eq_t_β : hom_coef_snd f = fun s ↦ β * s) :
      f = homOfIndex₀ β := by
  apply AffineIncrEquiv.hom_ext
  · rw [coef_1_one]
    unfold hom_coef_fst
    simp; rfl
  · rw [coef_2_eq_t_β]
    unfold hom_coef_snd
    ext s
    simp

/-- Characterization of homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (f_mble : Measurable f) :
    (∃ β, f = homOfIndex₀ β) ∨ (∃ α c, f = homOfIndex α c) := by
  let a (s : ℝ) : ℝ := (f s).coefs.1
  let b (s : ℝ) : ℝ := (f s).coefs.2
  have a_pos (s : ℝ) : 0 < a s := (f s).coefs_fst_pos
  have a_hom (s t : ℝ) : a (s + t) = a s * a t :=
    AffineIncrEquiv.homomorphism_coef_eqn_fst f s t
  have b_hom (s t : ℝ) : b (s + t) = a s * b t + b s :=
    AffineIncrEquiv.homomorphism_coef_eqn_snd f s t
  have a_mble : Measurable a := AffineIncrEquiv.measurable_coefs_fst.comp f_mble
  have b_mble : Measurable b := AffineIncrEquiv.measurable_coefs_snd.comp f_mble
  obtain ⟨α, a_eq_exp_α_s⟩ : ∃ α, a = fun s ↦ rexp (α * s) :=
    eq_exp_const_mul_of_multiplicative_of_measurable a_pos a_hom a_mble
  by_cases α_zero : α = 0
  · left
    have a_eq_one : a = 1 := by
      ext t
      simp [a_eq_exp_α_s, α_zero]
    have b_hom' (s t : ℝ) : b (s + t) = b s + b t := by
      simpa [a_eq_exp_α_s, α_zero, add_comm t s] using b_hom t s
    obtain ⟨β, b_eq_β_mul_s⟩ : ∃ α, b = fun s => α * s :=
      eq_const_mul_of_additive_of_measurable b_hom' b_mble
    use β
    suffices ∀ (s x : ℝ), (f s).coefs.1 * x + (f s).coefs.2 = x + β * s by aesop
    exact fun s x ↦ show a s * x + b s = x + β * s by simp [a_eq_one, b_eq_β_mul_s]
  · right
    rw [a_eq_exp_α_s] at b_hom
    obtain ⟨c, b_eq_c_mul_exp⟩ :=
      eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable α_zero b_hom
    use α, c
    suffices ∀ (s : ℝ), f s = homOfIndex α c s by ext s : 2 ; exact this s
    refine fun s ↦ AffineIncrEquiv.ext_of_coefs (Prod.eq_iff_fst_eq_snd_eq.mpr ?_)
    exact ⟨by simpa using congr_fun a_eq_exp_α_s s, by simpa using b_eq_c_mul_exp s⟩

/-- Characterization of nontrivial homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization_of_nontrivial
    {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv} (f_nontriv : ¬ f = 1)
    (f_mble : Measurable f) :
    (∃ β, β ≠ 0 ∧ f = homOfIndex₀ β) ∨ (∃ α c, α ≠ 0 ∧ f = homOfIndex α c) := by
  cases' homomorphism_from_Real_characterization f f_mble with h₀ h₁
  · obtain ⟨β, hβ⟩ := h₀
    refine Or.inl ⟨β, ?_, hβ⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [hβ, maybe_zero]
  · obtain ⟨α, c, h⟩ := h₁
    refine Or.inr ⟨α, c, ?_, h⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [h, maybe_zero]

end one_parameter_subgroups_of_affine_transformations
