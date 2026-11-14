-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.EligiblePivotPrefixes

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem bool_eq_of_true_iff (a b : Bool) (hh : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Selectors need agree only at the actual indexed schedule values. -/
theorem cutScheduleFrom_congr_values {f g : ℕ → ℝ → Bool} (i : ℕ) (h : List ℝ)
    (he : ∀ p : Fin h.length, f (i+p.val) h[p] = g (i+p.val) h[p]) :
    cutScheduleFrom f i h = cutScheduleFrom g i h := by
  induction h generalizing i with
  | nil => rfl
  | cons a h ih =>
    have hhead := he ⟨0,by simp⟩
    simp only [Fin.getElem_fin,List.getElem_cons_zero,Nat.add_zero] at hhead
    have htail : ∀ p : Fin h.length, f ((i+1)+p.val) h[p] = g ((i+1)+p.val) h[p] := by
      intro p
      have hh := he p.succ
      simpa only [Fin.getElem_fin,Fin.val_succ,List.getElem_cons_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh
    simp only [cutScheduleFrom,hhead,ih (i+1) htail]

theorem cutSchedule_congr_values {f g : ℕ → ℝ → Bool} (h : List ℝ)
    (he : ∀ p : Fin h.length, f p.val h[p] = g p.val h[p]) : cutSchedule f h = cutSchedule g h := by
  apply cutScheduleFrom_congr_values 0 h
  intro p
  simpa only [Nat.zero_add] using he p

theorem positionCut_nil_closed (h : List ℝ) (B : ℝ) :
    positionCut (fun _ b => decide (B ≤ b)) h [] = closedCut B h := by
  rw [positionCut,selectedWith_nil]
  rfl

/-- Each nonempty sorted prefix is exactly one of the partial-tie cuts
allowed in the paper. -/
theorem ordered_positionCut_partialTie (h : List ℝ) (A B : ℝ)
    {i : ℕ} (hi : i < (sortedScheduleIndices h (eligibleIndices h Finset.univ A B)).length) :
    positionCut (fun _ b => decide (B ≤ b)) h ((orderedPositions h (eligibleIndices h Finset.univ A B)).take (i+1)) =
      partialTieCut h[(sortedScheduleIndices h (eligibleIndices h Finset.univ A B))[i]]
        (((sortedScheduleIndices h (eligibleIndices h Finset.univ A B))[i]).val+1) h := by
  unfold positionCut partialTieCut
  apply cutSchedule_congr_values
  intro p
  apply bool_eq_of_true_iff
  have hh := selectedWith_eligible_prefix h Finset.univ A B hi p (by simp)
  simpa only [decide_eq_true_eq,Nat.lt_succ_iff] using hh

theorem ordered_positionCut_final (h : List ℝ) {A B : ℝ} (hAB : A < B) :
    positionCut (fun _ b => decide (B ≤ b)) h (orderedPositions h (eligibleIndices h Finset.univ A B)) = fullCut A h := by
  unfold positionCut fullCut
  apply cutSchedule_congr_values
  intro p
  apply bool_eq_of_true_iff
  simp only [selectedWith,Bool.or_eq_true,decide_eq_true_eq,orderedPositions,fin_val_mem_map,
    mem_sortedScheduleIndices,eligibleIndices,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hp
    rcases hp with ⟨ha,_⟩ | hb
    · exact ha
    · exact hAB.trans_le hb
  · intro hp
    by_cases hb : B ≤ h[p]
    · exact Or.inr hb
    · exact Or.inl ⟨hp,lt_of_not_ge hb⟩

end
end StrongSilver
