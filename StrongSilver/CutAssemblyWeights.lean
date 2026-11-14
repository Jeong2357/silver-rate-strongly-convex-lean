-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutTrace

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem list_weight_nonnegative (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) (h : List ℝ) : 0 ≤ (h.map w).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
  exact hw b

namespace CutAssembly

theorem weight_partition (s : CutAssembly) (w : CutPhase → ℝ) :
    (s.phases.map w).sum = (s.tracked.map w).sum+(s.reserved.map w).sum := by
  induction s <;> simp_all [phases,tracked,reserved,List.map_append,List.sum_append] <;> ring

/-- No actual step is charged to two different exceptional blocks. -/
theorem block_weight_bound (s : CutAssembly) (t : List ℝ) (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (((s.erase t).blockWords.map fun I => (I.map w).sum).sum) ≤ (s.reserved.flatMap CutPhase.word |>.map w).sum := by
  induction s with
  | ordinaryEnd q => simp [erase,WorkingAssembly.blockWords,reserved]
  | ordinary q s ih => simpa only [erase,WorkingAssembly.blockWords,reserved] using ih
  | block q I c s ih =>
    have hq := list_weight_nonnegative w hw q.word
    have hc := hw c.pivot
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq
    simp only [erase,WorkingAssembly.blockWords,reserved,List.flatMap_cons,List.flatMap_append,
      List.map_cons,List.sum_cons,List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [ih,hq,hc]
  | blockEnd q I c =>
    have hq := list_weight_nonnegative w hw q.word
    have hc := hw c.pivot
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq
    simp only [erase,WorkingAssembly.blockWords,reserved,List.flatMap_cons,List.flatMap_append,
      List.flatMap_nil,List.map_cons,List.sum_cons,List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hq,hc]
  | noConnector q I =>
    have hq := list_weight_nonnegative w hw q.word
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq
    simp only [erase,WorkingAssembly.blockWords,reserved,List.flatMap_cons,
      List.map_cons,List.sum_cons,List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hq]

theorem block_inverse_bound (s : CutAssembly) (t : List ℝ) (μ : ℝ) :
    (((s.erase t).blockWords.map fun I => inverseCharge μ I).sum) ≤ inverseCharge μ (s.reserved.flatMap CutPhase.word) := by
  simpa only [inverseCharge] using s.block_weight_bound t (fun a => inverseLogKernel (1-μ*a))
    (fun _ => inverseLogKernel_nonneg _)

end CutAssembly

theorem CompleteCutAssembly.weight_partition (s : CompleteCutAssembly) (w : CutPhase → ℝ) :
    (s.phases.map w).sum = (s.tracked.map w).sum+(s.reserved.map w).sum := by
  cases s with
  | scalar I => simp [phases,tracked,reserved]
  | positive s => exact s.weight_partition w
  | leadingBlock I c s =>
    simp only [phases,tracked,reserved,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
    rw [s.weight_partition w]
    ring
  | leadingEnd I c => simp [phases,tracked,reserved]

end
end StrongSilver
