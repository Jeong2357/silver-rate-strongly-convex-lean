-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingMarkedCount
import StrongSilver.InitialMarkedCount
import StrongSilver.ScheduleCutSublist
import StrongSilver.ScalarRampSuffix

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem three_test_indicator_le {b m e L M F : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (hM : 0 < M) (hF : 0 < F) :
    (if decide (b ≤ L ∧ m ≤ M ∧ e ≤ F) then (0 : ℝ) else 1) ≤
      (if L ≤ b then (1 : ℝ) else 0)+m/M+e/F := by
  have hm0 := div_nonneg hm hM.le
  have he0 := div_nonneg he hF.le
  have hi0 : (0 : ℝ) ≤ if L ≤ b then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  by_cases hg : b ≤ L ∧ m ≤ M ∧ e ≤ F
  · simp only [hg,true_and,decide_true,↓reduceIte]
    linarith only [hm0,he0,hi0]
  · simp only [hg,decide_false,Bool.false_eq_true,↓reduceIte]
    by_cases hp : L ≤ b
    · rw [if_pos hp]
      linarith only [hm0,he0]
    · rw [if_neg hp]
      by_cases hmass : m ≤ M
      · have hlarge : F ≤ e := by
          by_contra hn
          exact hg ⟨(lt_of_not_ge hp).le,hmass,(lt_of_not_ge hn).le⟩
        have hh := (one_le_div hF).mpr hlarge
        linarith only [hh,hm0]
      · have hh := (one_le_div hM).mpr (le_of_not_ge hmass)
        linarith only [hh,he0]

theorem three_test_marked_count {L M T F : ℝ} (hM : 0 < M) (hT : 0 < T) (hF : 0 < F)
    (qs : List CutPhase) :
    (badPhaseCount (fun q : CutPhase => decide (q.pivot ≤ L ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ M ∧
      negativeLogSum q.gap T ≤ F)) qs : ℝ) ≤
      (qs.map fun q => if L ≤ q.pivot then (1 : ℝ) else 0).sum+
        (qs.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum/M+
        (qs.map fun q => negativeLogSum q.gap T).sum/F := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hh := three_test_indicator_le (b := q.pivot) (L := L)
      (Scalar.SignedIntervals.positiveMass_nonneg q.gap) (negativeLogSum_nonnegative hT q.gap) hM hF
    simp only [badPhaseCount_cons,Nat.cast_add,List.map_cons,List.sum_cons,add_div]
    have hcast : ((if decide (q.pivot ≤ L ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ M ∧
        negativeLogSum q.gap T ≤ F) then 0 else 1 : ℕ) : ℝ) =
      (if decide (q.pivot ≤ L ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ M ∧
        negativeLogSum q.gap T ≤ F) then (0 : ℝ) else 1) := by split_ifs <;> norm_num
    rw [hcast]
    linarith only [hh,ih]

/-- All phase gap charges are disjoint parts of the unselected schedule. -/
theorem ScheduleCut.unselected_weight_sum (C : ScheduleCut) (w : ℝ → ℝ) :
    (C.unselected.map w).sum = (C.phases.map fun q => (q.gap.map w).sum).sum+(C.terminal.map w).sum := by
  rcases C with ⟨qs,t⟩
  induction qs with
  | nil => simp [unselected,gaps]
  | cons q qs ih =>
    simp only [unselected,gaps,List.map_cons,List.cons_append,List.flatten_cons,List.map_append,
      List.sum_append,List.sum_cons] at ih ⊢
    linarith only [ih]

theorem ScheduleCut.gap_weight_le_word (C : ScheduleCut) (w : ℝ → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (C.phases.map fun q => (q.gap.map w).sum).sum ≤ (C.word.map w).sum := by
  have hh := C.word_sum w
  have hu := C.unselected_weight_sum w
  have ht := list_weight_nonnegative w hw C.terminal
  have hp : 0 ≤ (C.phases.map fun q => w q.pivot).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact hw q.pivot
  linarith only [hh,hu,ht,hp]

theorem ScheduleCut.gap_negativeLogSum_le (C : ScheduleCut) {T : ℝ} (hT : 0 < T) :
    (C.phases.map fun q => negativeLogSum q.gap T).sum ≤ negativeLogSum C.word T := by
  apply C.gap_weight_le_word
  intro b
  split_ifs
  · exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hT.le))
  · exact le_rfl

theorem ScheduleCut.pivot_count_weight_le (C : ScheduleCut) (L : ℝ) :
    (C.phases.map fun q => if L ≤ q.pivot then (1 : ℝ) else 0).sum ≤ (countAbove C.word L : ℝ) := by
  have hh := C.selected_weight_le (fun b => if L ≤ b then (1 : ℝ) else 0) (by intro b; split_ifs <;> norm_num)
  have he : (C.word.map fun b => if L ≤ b then (1 : ℝ) else 0).sum = (countAbove C.word L : ℝ) := by
    induction C.word with
    | nil => simp [countAbove]
    | cons b h ih => simp only [List.map_cons,List.sum_cons,countAbove_cons,Nat.cast_add,← ih]; split_ifs <;> simp
  exact hh.trans_eq he

theorem cut_three_test_marked_count {L M T F : ℝ} (hM : 0 < M) (hT : 0 < T) (hF : 0 < F)
    (C : ScheduleCut) :
    (badPhaseCount (fun q : CutPhase => decide (q.pivot ≤ L ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ M ∧
      negativeLogSum q.gap T ≤ F)) C.phases : ℝ) ≤
      (countAbove C.word L : ℝ)+Scalar.SignedIntervals.positiveMass C.unselected/M+negativeLogSum C.word T/F := by
  have hh := three_test_marked_count (L := L) hM hT hF C.phases
  have hp := C.pivot_count_weight_le L
  have hmass := C.unselected_positiveMass
  have ht := Scalar.SignedIntervals.positiveMass_nonneg C.terminal
  have hmg : (C.phases.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum ≤
      Scalar.SignedIntervals.positiveMass C.unselected := by linarith only [hmass,ht]
  have hm := div_le_div_of_nonneg_right hmg hM.le
  have hn := div_le_div_of_nonneg_right (C.gap_negativeLogSum_le hT) hF.le
  linarith only [hh,hp,hm,hn]

end
end StrongSilver
