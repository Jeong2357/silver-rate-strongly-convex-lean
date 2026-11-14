-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutConcatenation
import StrongSilver.PhaseRefinement
import StrongSilver.TrackedPhaseNumbering

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem cutScheduleFrom_phase_word (choose : ℕ → ℝ → Bool) (i : ℕ) (q : CutPhase) (h : List ℝ)
    (hpiv : choose (i+q.gap.length) q.pivot = true) :
    cutScheduleFrom choose i (q.word++h) =
      ⟨refinePhase choose (q.withIndex (i+q.gap.length))++
        (cutScheduleFrom choose (i+q.word.length) h).phases,
        (cutScheduleFrom choose (i+q.word.length) h).terminal⟩ := by
  have hi : i+q.word.length = (i+q.gap.length)+1 := by simp only [CutPhase.word,List.length_append,List.length_singleton]; omega
  change cutScheduleFrom choose i ((q.gap++[q.pivot])++h) = _
  rw [List.append_assoc,cutScheduleFrom_append]
  simp only [List.singleton_append,cutScheduleFrom,hpiv,↓reduceIte,ScheduleCut.concat_before_selected]
  simp only [refinePhase,CutPhase.withIndex,Nat.add_sub_cancel,hi,List.append_assoc,List.singleton_append]

theorem cutScheduleFrom_numbered_phases (choose : ℕ → ℝ → Bool) (i : ℕ) (qs : List CutPhase)
    (hpiv : ∀ q ∈ qs, ∀ j : ℕ, choose j q.pivot = true) :
    cutScheduleFrom choose i (qs.flatMap CutPhase.word) =
      ⟨(numberTrackedPhases i qs).flatMap (refinePhase choose),[]⟩ := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih =>
    have hq := hpiv q (by simp) (i+q.gap.length)
    have ht := ih (i+q.word.length) (fun z hz => hpiv z (List.mem_cons_of_mem q hz))
    rw [List.flatMap_cons,cutScheduleFrom_phase_word choose i q _ hq,ht]
    rfl

/-- Original tracked pivots stay selected under every lower threshold;
only the interiors of their actual gaps are refined. -/
theorem cut_numbered_phases_of_selected_pivots {B : ℝ} (choose : ℕ → ℝ → Bool)
    (hchoose : ∀ j b, B ≤ b → choose j b = true) (i : ℕ) (qs : List CutPhase)
    (hpiv : ∀ q ∈ qs, B ≤ q.pivot) :
    cutScheduleFrom choose i (qs.flatMap CutPhase.word) =
      ⟨(numberTrackedPhases i qs).flatMap (refinePhase choose),[]⟩ :=
  cutScheduleFrom_numbered_phases choose i qs (fun q hq j => hchoose j q.pivot (hpiv q hq))

end
end StrongSilver
