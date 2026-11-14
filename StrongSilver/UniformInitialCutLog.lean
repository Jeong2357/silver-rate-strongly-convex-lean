-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedCompressedLog
import StrongSilver.OrderedValueSelectors
import StrongSilver.EventualUniformTail

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

/-- One original reservation supplies a uniform actual log bound after
every insertion in the compressed tracked schedule. -/
theorem eventually_uniform_initial_cut_log : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ P : ℝ, ∀ C : ScheduleCut, ∀ R : InitialReservation κ B μ C,
      A ≤ B → 2 ≤ B → B ≤ κ → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      (∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ P ∧ P ≤ t^((199 : ℝ)/200)) →
      (∀ q ∈ C.phases, B ≤ q.pivot) → (∀ b ∈ C.unselected, 0 < b → b ≤ B) →
      (∀ b ∈ C.word, 1-μ*b ≠ 0) → D κ C.word ≤ 1 →
      let G := R.compressedSchedule
      let ps := orderedPositions G (eligibleIndices G Finset.univ A B)
      ∀ i ≤ ps.length, -initialStableLogRemainder κ B μ (initialMarkedGood κ B μ) R.assembly C.terminal-
        (1200/Real.log A)*((countAbove G B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P 0 (positionCut (fun _ b => decide (B ≤ b)) G (ps.take i))-Real.log P := by
  filter_upwards [eventually_all_larger eventually_reserved_compressed_log,eventually_gt_atTop (1 : ℝ)]
    with A hall hA
  intro κ B μ P C R hAB hB hBκ hκA hκ hμ hμu hcap hpad hpiv hgap hcrit hD
  dsimp only
  let G := R.compressedSchedule
  let ps := orderedPositions G (eligibleIndices G Finset.univ A B)
  intro i hi
  obtain ⟨t,choose,hAt,htB,he,hselected,hunselected,hBselected⟩ := ordered_positionCut_value_selector G hAB hi
  have hA0 := zero_lt_one.trans hA
  have ht0 := hA0.trans_le hAt
  have hκt : κ ≤ t^((1003 : ℝ)/1000) := hκA.trans (Real.rpow_le_rpow hA0.le hAt (by norm_num))
  have hlocal := hall t hAt κ B μ P C R choose htB hB hBκ hκt hκ hμ hμu hcap
    (hpad t hAt htB).1 (hpad t hAt htB).2 hpiv hgap hselected (fun j b hb _ => hunselected j b hb) hBselected hcrit hD
  rw [← he] at hlocal
  have hcount : ((positionCut (fun _ b => decide (B ≤ b)) G (ps.take i)).phases.length : ℝ) =
      (countAbove G B : ℝ)+(i : ℝ) := by exact_mod_cast ordered_positionCut_count G A B hi
  have hlogs := Real.log_le_log hA0 hAt
  have hratio : 1200*((positionCut (fun _ b => decide (B ≤ b)) G (ps.take i)).phases.length : ℝ)/Real.log t ≤
      1200*((positionCut (fun _ b => decide (B ≤ b)) G (ps.take i)).phases.length : ℝ)/Real.log A :=
    div_le_div_of_nonneg_left (by positivity) (Real.log_pos hA) hlogs
  rw [hcount] at hlocal hratio
  linear_combination hlocal+hratio

end
end StrongSilver
