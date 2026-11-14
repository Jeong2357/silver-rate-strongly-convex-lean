-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedCompressedCut
import StrongSilver.InitialStableRefinedLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

/-- Actual initial-cut log bounds expressed in the canonical cuts of the
compressed tracked schedule, with the original reservation fixed. -/
theorem eventually_reserved_compressed_log : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ P : ℝ, ∀ C : ScheduleCut, ∀ R : InitialReservation κ B μ C, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → 2 ≤ B → B ≤ κ → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ C.phases, B ≤ q.pivot) → (∀ b ∈ C.unselected, 0 < b → b ≤ B) →
      (∀ j b, choose j b = true → A ≤ b) → (∀ j b, choose j b = false → 0 < b → b ≤ A) →
      (∀ j b, B ≤ b → choose j b = true) →
      (∀ b ∈ C.word, 1-μ*b ≠ 0) → D κ C.word ≤ 1 →
      -1200*((cutSchedule choose R.compressedSchedule).phases.length : ℝ)/Real.log A-
        initialStableLogRemainder κ B μ (initialMarkedGood κ B μ) R.assembly C.terminal ≤
        cutLogProduct (cappedStep μ B) P 0 (cutSchedule choose R.compressedSchedule)-Real.log P := by
  filter_upwards [eventually_initial_stable_refined_log] with A hbound
  intro κ B μ P C R choose hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU hpiv hgap hselected hunselected hBselected hcrit hD
  have hg : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B :=
    fun q hq b hb => hgap b (ScheduleCut.mem_gap_unselected hq hb)
  have ht : ∀ b ∈ C.terminal, 0 < b → b ≤ B :=
    fun b hb => hgap b (ScheduleCut.mem_terminal_unselected hb)
  have hh := hbound κ B μ (3*κ/4) P (initialMarkedGood κ B μ) (fun _ hq => initialMarkedGood_budget hq)
    R.assembly R.wellFormed R.counted choose C.terminal hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU
    hselected hunselected (R.phase_gap_cap hg) ht (by simpa only [R.source_word] using hcrit)
    (by simpa only [R.source_word] using hD)
  rw [R.compressed_log_eq hpiv choose hBselected]
  have he := R.compressed_cut hpiv choose hBselected
  rw [he]
  exact hh

end
end StrongSilver
