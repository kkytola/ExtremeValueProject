/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OrdContinuous
import Mathlib.Topology.Order.DenselyOrdered
import ExtremeValueProject.OrderContinuity

open Set


noncomputable section pseudoinverses
/-!
# Left-continuous and right-continuous (pseudo)inverses
-/

variable {R S : Type*} [CompleteLinearOrder R] [CompleteLinearOrder S]

/-- The left-continuous pseudoinverse of a function `F`, given by
`(lcInv F)(y) := inf {x | F x ≥ y}`. -/
def lcInv (F : R → S) (y : S) := sInf {x | y ≤ F x}

/-- The right-continuous pseudoinverse of a function `F`, given by
`(rcInv F)(y) := sup {x | F x ≤ y}`. -/
def rcInv (F : R → S) (y : S) := sSup {x | F x ≤ y}

lemma rcInv_eq_lcInv_dual (F : R → S) :
    rcInv F = @lcInv Rᵒᵈ Sᵒᵈ _ _ F :=
  rfl

variable {F : R → S}

lemma lcInv_le_of_apply_ge {x : R} {y : S} (h : y ≤ F x) :
    lcInv F y ≤ x :=
  sInf_le h

lemma lcInv_ge_of_apply_lt {x : R} {y : S} (F_mono : Monotone F) (h : F x < y) :
    x ≤ lcInv F y := by
  apply le_sInf
  intro b hb
  by_contra con
  exact lt_irrefl _ <| (hb.trans (F_mono (not_le.mp con).le)).trans_lt h

lemma forall_apply_ge_of_lcInv_le {x : R} {y : S} (F_mono : Monotone F) (h : lcInv F y ≤ x)
    {x' : R} (x_lt_x' : x < x') :
    y ≤ F x' := by
  by_contra con
  have obs (z : R) (hz : z ∈ {z | y ≤ F z}) : x' ≤ z := by
    by_contra con'
    exact lt_irrefl _ <| ((not_le.mp con).trans_le hz).trans_le (F_mono (not_le.mp con').le)
  exact lt_irrefl _ <| (h.trans_lt x_lt_x').trans_le (le_sInf obs)

lemma forall_apply_lt_of_lcInv_ge {x : R} {y : S} (h : x ≤ lcInv F y) {x' : R} (x'_lt_x : x' < x) :
    F x' < y := by
  by_contra con
  have key := sInf_le (show x' ∈ {z | y ≤ F z} from not_lt.mp con)
  exact lt_irrefl _ <| (key.trans_lt x'_lt_x).trans_le h

lemma lcInv_lt_iff_exists_apply_ge {x : R} {y : S} :
    lcInv F y < x ↔ ∃ x' < x, y ≤ F x' := by
  rw [lcInv, sInf_lt_iff]
  exact ⟨fun ⟨a, ha, a_lt⟩ ↦ ⟨a, a_lt, ha⟩, fun ⟨a, a_lt, ha⟩ ↦ ⟨a, ha, a_lt⟩⟩

lemma exists_apply_lt_of_lcInv_gt [DenselyOrdered R] {x : R} {y : S} (h : x < lcInv F y) :
    ∃ x' > x, F x' < y := by
  obtain ⟨w, x_lt_w, w_lt⟩ := exists_between h
  by_contra con
  simp only [gt_iff_lt, not_exists, not_and, not_lt] at con
  exact lt_irrefl _ <| (lcInv_le_of_apply_ge (con w x_lt_w)).trans_lt w_lt

lemma lcInv_gt_of_exists_apply_lt [DenselyOrdered R] (F_mono : Monotone F) {x : R} {y : S}
    {x' : R} (x_lt_x' : x' > x) (h : F x' < y) :
    x < lcInv F y := by
  obtain ⟨w, x_lt_w, w_lt_x'⟩ := exists_between x_lt_x'
  by_contra con
  have bad : w ∈ lowerBounds {x | y ≤ F x} := by
    intro a ha
    by_contra con'
    exact lt_irrefl _ <|
          ((ha.trans (F_mono (not_le.mp con').le)).trans (F_mono w_lt_x'.le)).trans_lt h
  exact lt_irrefl _ <| (((isGLB_sInf {x | y ≤ F x}).2 bad).trans (not_lt.mp con)).trans_lt x_lt_w

lemma apply_lt_of_lt_lcInv {F : R → S} {y : S} {x : R} (hx : x < lcInv F y) :
    F x < y := by
  by_contra con
  exact lt_irrefl _ <| hx.trans_le (sInf_le (not_lt.mp con))

lemma lt_apply_of_rcInv_lt {F : R → S} {y : S} {x : R} (hx : rcInv F y < x) :
    y < F x :=
  apply_lt_of_lt_lcInv (R := Rᵒᵈ) (S := Sᵒᵈ) hx

/-- Note: The forward implication holds without monotonicity assumption;
see `exists_apply_lt_of_lcInv_gt`. -/
lemma lcInv_gt_iff_exists_apply_lt [DenselyOrdered R] (F_mono : Monotone F) {x : R} {y : S} :
    x < lcInv F y ↔ ∃ x' > x, F x' < y := by
  constructor
  · exact exists_apply_lt_of_lcInv_gt
  · intro ⟨x', x_lt_x', h⟩
    apply lcInv_gt_of_exists_apply_lt F_mono x_lt_x' h

/-- The function `lcInv F` is increasing. -/
lemma lcInv_mono (F : R → S) :
    Monotone (lcInv F) := by
  intro y₁ y₂ hy
  have key : {x | y₂ ≤ F x} ⊆ {x | y₁ ≤ F x} := fun x hx ↦ le_trans hy hx
  apply sInf_le_sInf key

/-- The function `rcInv F` is increasing. -/
lemma rcInv_mono (F : R → S) :
    Monotone (rcInv F) := by
  intro y₁ y₂ hy
  apply sSup_le_sSup fun x hx ↦ le_trans hx hy

lemma lcInv_apply_self_le (x : R) :
    (lcInv F) (F x) ≤ x :=
  sInf_le <| by simpa only [Set.mem_setOf_eq] using le_rfl

lemma le_rcInv_apply_self (x : R) :
    x ≤ (rcInv F) (F x) :=
  @lcInv_apply_self_le Rᵒᵈ Sᵒᵈ _ _ F x

lemma le_sInf_setOf_lcInv_ge {F : R → S} (x x' : R) (hx : x' < x) :
    F x' ≤ sInf {y | x ≤ lcInv F y} := by
  have aux : (lcInv F) (F x') < x := (sInf_le (by simp)).trans_lt hx
  apply le_sInf fun y hy ↦ ?_
  simp only [mem_setOf_eq] at hy
  by_contra con
  simp only [ge_iff_le, not_le] at con
  simpa using (hy.trans (lcInv_mono F con.le)).trans_lt aux

lemma sSup_setOf_rcInv_le_le {F : R → S} (x x' : R) (hx : x < x') :
    sSup {y | rcInv F y ≤ x} ≤ F x' :=
  @le_sInf_setOf_lcInv_ge Rᵒᵈ Sᵒᵈ _ _ F x x' hx

lemma sInf_setOf_lcInv_ge_ge_sSup (x : R) :
    sInf {y | x ≤ lcInv F y} ≥ sSup (F '' Iio x) := by
  apply sSup_le
  intro y ⟨x', hxx', hyx'⟩
  rw [← hyx']
  exact le_sInf_setOf_lcInv_ge _ _ hxx'

lemma sSup_setOf_rcInv_le_le_sInf (x : R) :
    sSup {y | rcInv F y ≤ x} ≤ sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_ge_sSup Rᵒᵈ Sᵒᵈ _ _ F x

lemma lcInv_ge_of_sSup_lt (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    lcInv F z ≥ x := by
  have aux (x' : R) (hx : x' < x) : F x' < z := by
    apply (le_sSup ?_).trans_lt hz
    exact mem_image_of_mem F hx
  apply le_sInf
  intro x' hx'
  by_contra con'
  simpa using hx'.trans_lt (aux _ (not_le.mp con'))

lemma rcInv_le_of_lt_sInf (x : R) (z : S) (hz : z < sInf (F '' Ioi x)) :
    rcInv F z ≤ x :=
  @lcInv_ge_of_sSup_lt Rᵒᵈ Sᵒᵈ _ _ F x z hz

lemma ge_sInf_setOf_lcInv_ge (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    z ≥ sInf {y | x ≤ lcInv F y} := by
  apply sInf_le
  exact lcInv_ge_of_sSup_lt _ _ hz

lemma le_sSup_setOf_rcInv_le (x : R) (z : S) (hz : z < sInf (F '' Ioi x)) :
    z ≤ sSup {y | rcInv F y ≤ x} :=
  @ge_sInf_setOf_lcInv_ge Rᵒᵈ Sᵒᵈ _ _ F x z hz

lemma sInf_setOf_lcInv_ge_le_sSup (x : R) [DenselyOrdered S] :
    sInf {y | x ≤ lcInv F y} ≤ sSup (F '' Iio x) := by
  suffices ∀ z, sSup (F '' Iio x) < z → sInf {y | x ≤ lcInv F y} ≤ z by
    have obs : sInf {y | x ≤ lcInv F y} ≤ sInf {z | sSup (F '' Iio x) < z} :=
      le_sInf fun z hz ↦ this _ hz
    apply obs.trans (le_of_eq ?_)
    apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact fun z hz ↦ le_of_lt hz
    · exact fun z hz ↦ exists_between hz
  exact ge_sInf_setOf_lcInv_ge x

lemma sSup_setOf_rcInv_le_ge_sInf (x : R) [DenselyOrdered S] :
    sSup {y | rcInv F y ≤ x} ≥ sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_le_sSup Rᵒᵈ Sᵒᵈ _ _ F x _

/-- If `G` is the left-continuous pseudoinverse of `F`, then we have
`inf {y | G(y) ≥ x} = sup {F(x') | x' < x}`. -/
theorem sInf_setOf_lcInv_ge_eq_sSup [DenselyOrdered S] (x : R) :
    sInf {y | x ≤ lcInv F y} = sSup (F '' Iio x) :=
  le_antisymm (sInf_setOf_lcInv_ge_le_sSup x) (sInf_setOf_lcInv_ge_ge_sSup x)

/-- If `G` is the right-continuous pseudoinverse of `F`, then we have
`sup {y | x ≤ G(y)} = inf {F(x') | x' > x}`. -/
theorem sSup_setOf_rcInv_le_eq_sInf [DenselyOrdered S] (x : R) :
    sSup {y | rcInv F y ≤ x} = sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_eq_sSup Rᵒᵈ Sᵒᵈ _ _ F _ x

/-- The double left-continuous inverse `lcInv (lcInv F)` of `F` is the left-continuous
modification `lcMod` of `F`. -/
theorem lcInv_lcInv_apply_eq_lcMod_apply [DenselyOrdered S] (x : R) :
    lcInv (lcInv F) x = lcMod F x :=
  sInf_setOf_lcInv_ge_eq_sSup _

/-- The double right-continuous inverse `rcInv (rcInv F)` of `F` is the right-continuous
modification `rcMod` of `F`. -/
theorem rcInv_rcInv_apply_eq_rcMod_apply [DenselyOrdered S] (x : R) :
    rcInv (rcInv F) x = rcMod F x :=
  sSup_setOf_rcInv_le_eq_sInf _

/-- The double left-continuous inverse `lcInv (lcInv F)` of `F` is the left-continuous
modification `lcMod` of `F`. -/
theorem lcInv_lcInv_eq_lcMod [DenselyOrdered S] :
    lcInv (lcInv F) = lcMod F := by
  ext x
  exact lcInv_lcInv_apply_eq_lcMod_apply x

/-- The double right-continuous inverse `rcInv (rcInv F)` of `F` is the right-continuous
modification `rcMod` of `F`. -/
theorem rcInv_rcInv_eq_rcMod [DenselyOrdered S] :
    rcInv (rcInv F) = rcMod F := by
  ext x
  exact rcInv_rcInv_apply_eq_rcMod_apply x

/-- The left-continuous (pseudo-)inverse is left-continuous. -/
lemma leftOrdContinuous_lcInv [DenselyOrdered R] (F_mono : Monotone F) :
    LeftOrdContinuous (lcInv F) := by
  -- TODO: Improve this proof?
  intro s lub_s h_lub_s
  refine ⟨?_, ?_⟩
  · simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x x_in_s
    exact lcInv_mono _ (h_lub_s.1 x_in_s)
  · intro u hu
    simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂] at hu
    by_contra con
    simp only [not_le] at con
    obtain ⟨z, u_lt_z, z_lt⟩ := exists_between con
    have obs_z : F z ∈ upperBounds s := by
      intro y' y'_in_s
      by_contra maybe
      simp only [not_le] at maybe
      have z_le : lcInv F y' ≥ z := by
        apply le_sInf
        intro x' le_Fx'
        by_contra con'
        simp only [not_le] at con'
        apply lt_irrefl _ ((le_Fx'.trans (F_mono con'.le)).trans_lt maybe)
      exact lt_irrefl _ (u_lt_z.trans_le (z_le.trans (hu _ y'_in_s)))
    have oops : F z < lub_s := by
      by_contra maybe
      simp only [not_lt] at maybe
      have le_z : z ≥ lcInv F lub_s := sInf_le maybe
      exact lt_irrefl _ (z_lt.trans_le le_z)
    exact lt_irrefl _ (oops.trans_le (h_lub_s.2 obs_z))

/-- The right-continuous (pseudo-)inverse is right-continuous. -/
lemma rightOrdContinuous_lcInv [DenselyOrdered R] (F_mono : Monotone F) :
    RightOrdContinuous (rcInv F) :=
  leftOrdContinuous_lcInv (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F) (fun _ _ hx ↦ F_mono hx)

variable (F)

lemma Equiv.monotone_symm {R S : Type*} [LinearOrder R] [PartialOrder S] (φ : R ≃ S)
    (φ_mono : Monotone φ) :
    Monotone φ.symm := by
  intro x₁ x₂ hx₁₂
  by_contra con
  have obs := φ_mono (not_le.mp con).le
  simp only [Equiv.apply_symm_apply] at obs
  simp [show x₁ = x₂ from le_antisymm hx₁₂ obs] at con

lemma Equiv.monotone_of_monotone_symm {R S : Type*} [PartialOrder R] [LinearOrder S] (φ : R ≃ S)
    (symm_mono : Monotone φ.symm) :
    Monotone φ :=
  φ.symm.monotone_symm symm_mono

variable {T : Type*} [CompleteLinearOrder T]

lemma comp_lcInv (F : R → S) (φ : S ≃ T) (hφ : Monotone φ) :
    lcInv (φ ∘ F) = (lcInv F) ∘ φ.symm := by
  ext y
  simp only [lcInv, Function.comp_apply]
  congr
  ext x
  exact ⟨fun h' ↦ by simpa using (φ.monotone_symm hφ) h', fun h ↦ by simpa using hφ h⟩

lemma symm_comp_lcInv (F : R → S) (φ : T ≃ S) (hφ : Monotone φ) :
    lcInv (φ.symm ∘ F) = (lcInv F) ∘ φ :=
  comp_lcInv _ _ (φ.monotone_symm hφ)

lemma comp_rcInv (F : R → S) (φ : S ≃ T) (hφ : Monotone φ) :
    rcInv (φ ∘ F) = (rcInv F) ∘ φ.symm :=
  comp_lcInv (R := Rᵒᵈ) (S := Sᵒᵈ) (T := Tᵒᵈ) F φ (fun _ _ hx ↦ by exact hφ hx)

lemma symm_comp_rcInv (F : R → S) (φ : T ≃ S) (hφ : Monotone φ) :
    rcInv (φ.symm ∘ F) = (rcInv F) ∘ φ :=
  comp_rcInv _ _ (φ.monotone_symm hφ)

lemma lcInv_comp_symm (φ : R ≃ T) (hφ : RightOrdContinuous φ) :
    lcInv (F ∘ φ.symm) = φ ∘ (lcInv F) := by
  ext y
  simp only [lcInv, Function.comp_apply, RightOrdContinuous.map_sInf' hφ _]
  congr
  ext x
  simp only [mem_setOf_eq]
  grind

lemma lcInv_comp (φ : T ≃ R) (hφ : RightOrdContinuous φ.symm) :
    lcInv (F ∘ φ) = φ.symm ∘ (lcInv F) :=
  lcInv_comp_symm F φ.symm hφ

lemma rcInv_comp_symm (φ : R ≃ T) (hφ : LeftOrdContinuous φ) :
    rcInv (F ∘ φ.symm) = φ ∘ (rcInv F) :=
  lcInv_comp_symm (R := Rᵒᵈ) (S := Sᵒᵈ) (T := Tᵒᵈ) F φ hφ

lemma rcInv_comp (φ : T ≃ R) (hφ : LeftOrdContinuous φ.symm) :
    rcInv (F ∘ φ) = φ.symm ∘ (rcInv F) :=
  rcInv_comp_symm F φ.symm hφ

section DenselyOrdered

variable [DenselyOrdered R]

lemma LeftOrdContinuous.self_lcInv_le {F : R → S} (F_lcont : LeftOrdContinuous F) (y : S) :
    F (lcInv F y) ≤ y := by
  apply (F_lcont (isLUB_Iio (a := (lcInv F y)))).2
  simpa [mem_upperBounds] using fun x hx ↦ (apply_lt_of_lt_lcInv hx).le

lemma RightOrdContinuous.self_rcInv_ge {F : R → S} {y : S} (F_rcont : RightOrdContinuous F) :
    y ≤ F (rcInv F y) :=
  LeftOrdContinuous.self_lcInv_le (R := Rᵒᵈ) (S := Sᵒᵈ) F_rcont y

lemma RightOrdContinuous.self_lcInv_ge {F : R → S} (F_rcont : RightOrdContinuous F) (y : S) :
    y ≤ F (lcInv F y) := by
  apply (F_rcont (isGLB_Ioi (a := (lcInv F y)))).2
  simp only [mem_lowerBounds, mem_image, mem_Ioi, forall_exists_index, and_imp,
             forall_apply_eq_imp_iff₂]
  intro x hx
  rw [lcInv, sInf_lt_iff] at hx
  obtain ⟨z, hz, z_lt_x⟩ := hx
  exact hz.trans (F_rcont.mono z_lt_x.le)

lemma LeftOrdContinuous.self_rcInv_le {F : R → S} (F_lcont : LeftOrdContinuous F) (y : S) :
    F (rcInv F y) ≤ y :=
  RightOrdContinuous.self_lcInv_ge (R := Rᵒᵈ) (S := Sᵒᵈ) F_lcont y

end DenselyOrdered

end pseudoinverses
