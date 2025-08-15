/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OrdContinuous
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib

open Set

noncomputable section order_continuity_vs_continuity
/-!
# Left/right-order-continuous functions are (topologically) left/right-continuous

Below is an extended version of PR #23309 to Mathlib: here we do the pointwise
`ContinuousAt` case with weaker assumptions, and the converse implication as well.
These are auxiliary results for the ExtremeValueProject.
-/

section ConditionallyCompleteLinearOrder

variable {R S : Type*} [LinearOrder R] [LinearOrder S] [DenselyOrdered R]

lemma forall_isLUB_imp_isLUB_image_iff_isLUB_image_Iio {f : R → S} (f_mono : Monotone f) {x : R} :
    (∀ (s : Set R), IsLUB s x → IsLUB (f '' s) (f x)) ↔ IsLUB (f '' Iio x) (f x) := by
  constructor
  · intro f_lcont
    exact f_lcont _ isLUB_Iio
  · intro h s hx
    refine ⟨by simpa [mem_upperBounds] using fun a ha ↦ f_mono (hx.1 ha), ?_⟩
    intro y hy
    apply h.2
    simp only [mem_lowerBounds, mem_upperBounds, mem_image, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂] at hy ⊢
    intro a a_lt
    obtain ⟨b, b_in_s, hb⟩ : ∃ b ∈ s, a < b := by rwa [mem_Iio, lt_isLUB_iff hx] at a_lt
    by_contra con
    apply lt_irrefl _ <| (not_le.mp con).trans_le <| (f_mono hb.le).trans (hy b b_in_s)

lemma forall_isGLB_imp_isGLB_image_iff_isGLB_image_Ioi {f : R → S} (f_mono : Monotone f) {x : R} :
    (∀ (s : Set R), IsGLB s x → IsGLB (f '' s) (f x)) ↔ IsGLB (f '' Ioi x) (f x) :=
  forall_isLUB_imp_isLUB_image_iff_isLUB_image_Iio (R := Rᵒᵈ) (S := Sᵒᵈ) <|
    by exact fun _ _ hx ↦ f_mono hx

lemma leftOrdContinuous_iff_forall_isLUB_image_Iio {f : R → S} (f_mono : Monotone f) :
    LeftOrdContinuous f ↔ ∀ (x : R), IsLUB (f '' Iio x) (f x) := by
  simp_rw [← forall_isLUB_imp_isLUB_image_iff_isLUB_image_Iio f_mono, LeftOrdContinuous]
  aesop

lemma rightOrdContinuous_iff_forall_isGLB_image_Ioi {f : R → S} (f_mono : Monotone f) :
    RightOrdContinuous f ↔ ∀ (x : R), IsGLB (f '' Ioi x) (f x) :=
  leftOrdContinuous_iff_forall_isLUB_image_Iio (R := Rᵒᵈ) (S := Sᵒᵈ) <|
    by exact fun _ _ hx ↦ f_mono hx

open Topology

lemma Monotone.isLUB_image_Iio_of_continuousWithinAt_Iic' {R S : Type*}
    [PartialOrder R] [TopologicalSpace R] [PartialOrder S] [TopologicalSpace S]
    [ClosedIicTopology S] {f : R → S} (f_mono : Monotone f) {x : R}
    (hx : (𝓝[<] x).NeBot) (f_cont : ContinuousWithinAt f (Iic x) x) :
    IsLUB (f '' Iio x) (f x) := by
  rw [← continuousWithinAt_Iio_iff_Iic] at f_cont
  refine ⟨?_, ?_⟩
  · simpa [mem_upperBounds] using fun a ha ↦ f_mono ha.le
  · simp only [mem_lowerBounds, mem_upperBounds, mem_image, mem_Iio, forall_exists_index,
               and_imp, forall_apply_eq_imp_iff₂]
    intro y hy
    apply le_of_tendsto_of_frequently f_cont
    apply Filter.frequently_iff.mpr
    intro U hU
    obtain ⟨t, ht⟩ := Filter.Eventually.exists (Filter.inter_mem hU self_mem_nhdsWithin)
    exact ⟨t, ht.1, hy _ ht.2⟩

lemma Monotone.isLUB_image_Iio_of_continuousWithinAt_Iic {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R]
    [PartialOrder S] [TopologicalSpace S] [ClosedIicTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hx : ¬ IsMin x)
    (f_cont : ContinuousWithinAt f (Iic x) x) :
    IsLUB (f '' Iio x) (f x) := by
  apply f_mono.isLUB_image_Iio_of_continuousWithinAt_Iic' _ f_cont
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [closure_Iio' (Iio_nonempty.mpr hx)]
  exact right_mem_Iic

lemma Monotone.continuousWithinAt_Iic_of_isLUB_image_Iio {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
    [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hf : IsLUB (f '' Iio x) (f x)) :
    ContinuousWithinAt f (Iic x) x := by
  rw [ContinuousWithinAt, OrderTopology.topology_eq_generate_intervals (α := S)]
  simp_rw [TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_nhdsWithin]
  rintro V ⟨z, rfl | rfl⟩ hxz
  -- The case `V = Ioi z`.
  · obtain ⟨_, ⟨a, hax, rfl⟩, hza⟩ := (lt_isLUB_iff <| hf).mp hxz
    exact ⟨Ioi a, isOpen_Ioi, hax, fun b hab ↦ hza.trans_le <| f_mono hab.1.le⟩
  -- The case `V = Iio z`.
  · exact ⟨univ, isOpen_univ, trivial, fun a ha ↦ (f_mono ha.2).trans_lt hxz⟩

lemma Monotone.continuousWithinAt_Iic_iff_isLUB_image_Iio' {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
    [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hx : (𝓝[<] x).NeBot) :
    ContinuousWithinAt f (Iic x) x ↔ IsLUB (f '' Iio x) (f x) :=
  ⟨isLUB_image_Iio_of_continuousWithinAt_Iic' f_mono hx,
   f_mono.continuousWithinAt_Iic_of_isLUB_image_Iio⟩

lemma Monotone.continuousWithinAt_Ici_iff_isGLB_image_Ioi' {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
    [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hx : (𝓝[>] x).NeBot) :
    ContinuousWithinAt f (Ici x) x ↔ IsGLB (f '' Ioi x) (f x) :=
  continuousWithinAt_Iic_iff_isLUB_image_Iio' (R := Rᵒᵈ) (S := Sᵒᵈ)
    (fun _ _ hx ↦ by exact f_mono hx) hx

lemma Monotone.continuousWithinAt_Iic_iff_isLUB_image_Iio {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R]
    [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hx : ¬ IsMin x) :
    ContinuousWithinAt f (Iic x) x ↔ IsLUB (f '' Iio x) (f x) :=
  ⟨isLUB_image_Iio_of_continuousWithinAt_Iic f_mono hx,
   f_mono.continuousWithinAt_Iic_of_isLUB_image_Iio⟩

lemma Monotone.continuousWithinAt_Ici_iff_isGLB_image_Ioi {R S : Type*}
    [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R]
    [LinearOrder S] [TopologicalSpace S] [OrderTopology S]
    {f : R → S} (f_mono : Monotone f) {x : R} (hx : ¬ IsMax x) :
    ContinuousWithinAt f (Ici x) x ↔ IsGLB (f '' Ioi x) (f x) :=
  continuousWithinAt_Iic_iff_isLUB_image_Iio (R := Rᵒᵈ) (S := Sᵒᵈ)
    (fun _ _ hx ↦ by exact f_mono hx) hx

variable {X : Type*} [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X]
variable {Y : Type*} [ConditionallyCompleteLinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
variable [DenselyOrdered X] {f : X → Y} {x : X}

/-- A topologically left-continuous function is order-theoretically left-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered and has no minimum. -/
lemma Monotone.leftOrdContinuous_of_forall_continuousWithinAt_Iic [NoMinOrder X]
    (f_mono : Monotone f) (hf : ∀ x, ContinuousWithinAt f (Iic x) x) :
    LeftOrdContinuous f := by
  refine (leftOrdContinuous_iff_forall_isLUB_image_Iio f_mono).mpr ?_
  intro x
  have key := @continuousWithinAt_Iic_iff_isLUB_image_Iio' X Y _ _ _ _ _ _ f f_mono x (nhdsLT_neBot x)
  simpa [← key] using hf x

/-- A topologically right-continuous function is order-theoretically right-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered and has no maximum. -/
lemma Monotone.rightOrdContinuous_of_forall_continuousWithinAt_Ici [NoMaxOrder X]
    (f_mono : Monotone f) (hf : ∀ x, ContinuousWithinAt f (Ici x) x) :
    RightOrdContinuous f :=
  leftOrdContinuous_of_forall_continuousWithinAt_Iic (X := Xᵒᵈ) (Y := Yᵒᵈ)
    (fun _ _ hx ↦ by exact f_mono hx) hf

end ConditionallyCompleteLinearOrder

end order_continuity_vs_continuity


noncomputable section modification
/-!
# Left-continuous and right-continuous modifications of functions
-/

variable {R S : Type*}

/-- Left-continuous modification of F. -/
def lcMod [Preorder R] [SupSet S] (F : R → S) (x : R) := sSup (F '' Iio x)

/-- right-continuous modification of F. -/
def rcMod [Preorder R] [InfSet S] (F : R → S) (x : R) := sInf (F '' Ioi x)

lemma lcMod_mono [Preorder R] [CompleteSemilatticeSup S] (F : R → S) :
    Monotone (lcMod F) :=
  fun _ _ hx ↦ sSup_le_sSup <| image_mono <| Iio_subset_Iio hx

lemma rcMod_mono [Preorder R] [CompleteSemilatticeInf S] (F : R → S) :
    Monotone (rcMod F) :=
  fun _ _ hx ↦ sInf_le_sInf <| image_mono <| Ioi_subset_Ioi hx

lemma lcMod_apply_le_self_apply [Preorder R] [CompleteSemilatticeSup S] {F : R → S}
    (F_mono : Monotone F) (x : R) :
    lcMod F x ≤ F x := by
  apply sSup_le
  intro y ⟨x', x'_lt, Fx'_eq_y⟩
  simpa [← Fx'_eq_y] using F_mono x'_lt.le

lemma self_apply_le_rcMod_apply [Preorder R] [CompleteSemilatticeInf S] {F : R → S}
    (F_mono : Monotone F) (x : R) :
    F x ≤ rcMod F x :=
  lcMod_apply_le_self_apply (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F) (by exact fun _ _ hx ↦ F_mono hx) x

lemma lcMod_le_self [Preorder R] [CompleteSemilatticeSup S] {F : R → S} (F_mono : Monotone F) :
    lcMod F ≤ F :=
  fun x ↦ lcMod_apply_le_self_apply F_mono x

lemma self_le_rcMod [Preorder R] [CompleteSemilatticeInf S] {F : R → S} (F_mono : Monotone F) :
    F ≤ rcMod F :=
  fun x ↦ self_apply_le_rcMod_apply F_mono x

lemma le_lcMod_apply_of_lt [Preorder R] [CompleteSemilatticeSup S] (F : R → S) {x' x : R}
    (h : x' < x) :
    F x' ≤ lcMod F x :=
  le_sSup (mem_image_of_mem F h)

lemma rcMod_apply_le_of_lt [Preorder R] [CompleteSemilatticeInf S] (F : R → S) {x' x : R}
    (h : x < x') :
    rcMod F x ≤ F x' :=
  sInf_le (mem_image_of_mem F h)

/-- The left-continuous modification of a function is left-continuous. -/
lemma leftOrdContinuous_lcMod [LinearOrder R] [CompleteSemilatticeSup S] (F : R → S) :
    LeftOrdContinuous (lcMod F) := by
  intro s lub_s h_lub_s
  refine ⟨?_, ?_⟩
  · simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x x_in_s
    exact lcMod_mono _ (h_lub_s.1 x_in_s)
  · simp only [mem_lowerBounds, mem_upperBounds, mem_image, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂]
    intro y hy
    apply sSup_le
    intro z ⟨x, hx, Fx_eq_z⟩
    rw [← Fx_eq_z]
    obtain ⟨x', x'_in_s, x_lt_x'⟩ : ∃ x' ∈ s, x < x' := by
      by_contra con
      simp only [not_exists, not_and, not_lt] at con
      exact lt_irrefl _ (hx.trans_le (h_lub_s.2 con))
    exact (le_lcMod_apply_of_lt F x_lt_x').trans (hy x' x'_in_s)

/-- The right-continuous modification of a function is right-continuous. -/
lemma rightOrdContinuous_rcMod [LinearOrder R] [CompleteSemilatticeInf S](F : R → S) :
    RightOrdContinuous (rcMod F) :=
  leftOrdContinuous_lcMod (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F)

section OrderTopology

open Topology Filter

variable {R S : Type*}

lemma lcMod_apply_eq_self_apply' [CompleteLattice R] [TopologicalSpace R]
    [CompleteLattice S] [TopologicalSpace S] [ClosedIicTopology S]
    {F : R → S} (F_mono : Monotone F) {x : R}
    (hFx : ContinuousAt F x) (lt_x_neBot : (𝓝[<] x).NeBot) :
    lcMod F x = F x := by
  apply le_antisymm (lcMod_apply_le_self_apply F_mono x)
  have aux : Filter.Tendsto F (𝓝[<] x) (𝓝 (F x)) := tendsto_nhdsWithin_of_tendsto_nhds hFx
  apply le_of_tendsto_of_frequently aux (b := lcMod F x)
  apply Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with z hz using le_lcMod_apply_of_lt F hz

lemma lcMod_apply_eq_self_apply
    [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R]
    [CompleteLattice S] [TopologicalSpace S] [ClosedIicTopology S] {F : R → S}
    (F_mono : Monotone F) {x : R} (hFx : ContinuousAt F x) (x_ne_bot : ¬ IsMin x) :
    lcMod F x = F x := by
  apply lcMod_apply_eq_self_apply' F_mono hFx
  exact nhdsWithin_Iio_self_neBot' (Iio_nonempty.mpr x_ne_bot)

lemma rcMod_apply_eq_self_apply' [CompleteLattice R] [TopologicalSpace R]
    [CompleteLattice S] [TopologicalSpace S] [ClosedIciTopology S]
    {F : R → S} (F_mono : Monotone F) (x : R)
    (hFx : ContinuousAt F x) (gt_x_neBot : (𝓝[>] x).NeBot) :
    rcMod F x = F x :=
  lcMod_apply_eq_self_apply' (R := Rᵒᵈ) (S := Sᵒᵈ) (fun _ _ hx ↦ by exact F_mono hx) hFx gt_x_neBot

lemma rcMod_apply_eq_self_apply
    [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R] [DenselyOrdered R]
    [CompleteLattice S] [TopologicalSpace S] [ClosedIciTopology S] {F : R → S}
    (F_mono : Monotone F) (x : R) (hFx : ContinuousAt F x) (x_ne_top : ¬ IsMax x) :
    rcMod F x = F x :=
  lcMod_apply_eq_self_apply (R := Rᵒᵈ) (S := Sᵒᵈ) (fun _ _ hx ↦ by exact F_mono hx) hFx x_ne_top

variable [CompleteLattice R] [CompleteLattice S]

end OrderTopology

end modification
