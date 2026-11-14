-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialLogPriceBound
import StrongSilver.CutAssemblyWeights

namespace StrongSilver.InitialCutAssembly
open Real
noncomputable section
set_option maxHeartbeats 2200000

def blockWords : InitialCutAssembly → List (List ℝ)
  | .terminal => []
  | .tracked _ s => s.blockWords
  | .block _ I c _ s => (I.flatMap CutPhase.word++c.gap)::s.blockWords
  | .terminalBlock _ I c => [I.flatMap CutPhase.word++c.gap]
  | .noConnector _ I => [I.flatMap CutPhase.word]

def blockCount : InitialCutAssembly → ℕ
  | .terminal => 0
  | .tracked _ s => s.blockCount
  | .block _ _ _ _ s => 1+s.blockCount
  | .terminalBlock _ _ _ => 1
  | .noConnector _ _ => 1

theorem blockCount_le_reserved (s : InitialCutAssembly) : s.blockCount ≤ s.reserved.length := by
  induction s <;> simp_all [blockCount,reserved] <;> omega

theorem weight_partition (s : InitialCutAssembly) (w : CutPhase → ℝ) :
    (s.phases.map w).sum = (s.trackedPhases.map w).sum+(s.reserved.map w).sum := by
  induction s <;> simp_all [phases,trackedPhases,reserved,List.map_append,List.sum_append] <;> ring

theorem block_weight_bound (s : InitialCutAssembly) (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (s.blockWords.map fun I => (I.map w).sum).sum ≤ (s.reserved.flatMap CutPhase.word |>.map w).sum := by
  induction s with
  | terminal => simp [blockWords,reserved]
  | tracked q s ih => exact ih
  | block q I c d s ih =>
    have hq := list_weight_nonnegative w hw q.word
    have hc := hw c.pivot
    have hd := list_weight_nonnegative w hw d.word
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq hd
    simp only [blockWords,reserved,List.flatMap_cons,List.flatMap_append,List.map_cons,List.sum_cons,
      List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [ih,hq,hc,hd]
  | terminalBlock q I c =>
    have hq := list_weight_nonnegative w hw q.word
    have hc := hw c.pivot
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq
    simp only [blockWords,reserved,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,List.map_cons,List.sum_cons,
      List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hq,hc]
  | noConnector q I =>
    have hq := list_weight_nonnegative w hw q.word
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hq
    simp only [blockWords,reserved,List.flatMap_cons,List.map_cons,List.sum_cons,
      List.map_append,List.sum_append,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hq]

theorem logCost_raw {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hK : 1 ≤ κ/B)
    (A μ P : ℝ) (refine : CutPhase → List CutPhase) (t : List ℝ) (s : InitialCutAssembly) :
    s.logCost A κ B μ P refine t ≤
      2*((s.trackedPhases.flatMap refine).map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
      4*μ*Scalar.SignedIntervals.positiveMass t+initialLogPriceConstant*(s.blockCount : ℝ)*(1+Real.log (κ/B))+
      2*(s.blockWords.map fun I => inverseCharge μ I).sum+
      2*(s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum := by
  induction s with
  | terminal => simp [logCost,trackedPhases,blockCount,blockWords]
  | tracked q s ih =>
    simp only [logCost,trackedPhases,blockCount,blockWords,List.flatMap_cons,List.map_append,List.sum_append]
    linarith only [ih]
  | block q I c d s ih =>
    have hp := (initial_log_price_bounds hκ hB hK μ (I.flatMap CutPhase.word++c.gap) t).1
    simp only [logCost,trackedPhases,blockCount,blockWords,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [ih,hp]
  | terminalBlock q I c =>
    have hp := (initial_log_price_bounds hκ hB hK μ (I.flatMap CutPhase.word++c.gap) t).2.1
    simpa only [logCost,trackedPhases,blockCount,blockWords,List.flatMap_nil,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,
      Nat.cast_one,mul_zero,zero_mul,mul_one,zero_add,add_zero] using hp
  | noConnector q I =>
    have hp := (initial_log_price_bounds hκ hB hK μ (I.flatMap CutPhase.word) t).2.2
    simpa only [logCost,trackedPhases,blockCount,blockWords,List.flatMap_nil,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,
      Nat.cast_one,mul_zero,zero_mul,mul_one,zero_add,add_zero] using hp

end
end StrongSilver.InitialCutAssembly
