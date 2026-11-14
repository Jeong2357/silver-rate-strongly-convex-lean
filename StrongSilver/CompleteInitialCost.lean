-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteInitialLog
import StrongSilver.InitialInverseCharge
import StrongSilver.RefinementMassBudget

namespace StrongSilver.CompleteInitialCutAssembly
open Real
noncomputable section
set_option maxHeartbeats 2600000

def blockWords : CompleteInitialCutAssembly → List (List ℝ)
  | .scalar I => [I.flatMap CutPhase.word]
  | .positive s => s.blockWords
  | .leadingBlock I c _ s => (I.flatMap CutPhase.word++c.gap)::s.blockWords
  | .leadingEnd I c => [I.flatMap CutPhase.word++c.gap]

def blockCount : CompleteInitialCutAssembly → ℕ
  | .scalar _ => 0
  | .positive s => s.blockCount
  | .leadingBlock _ _ _ s => 1+s.blockCount
  | .leadingEnd _ _ => 1

theorem blockCount_le_reserved (s : CompleteInitialCutAssembly) : s.blockCount ≤ s.reserved.length := by
  cases s with
  | scalar I => exact Nat.zero_le _
  | positive s => exact s.blockCount_le_reserved
  | leadingBlock I c d s =>
    have hh := s.blockCount_le_reserved
    simp only [blockCount,reserved,List.length_append,List.length_cons]
    omega
  | leadingEnd I c => simp [blockCount,reserved]

theorem block_weight_bound (s : CompleteInitialCutAssembly) (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (s.blockWords.map fun I => (I.map w).sum).sum ≤ (s.reserved.flatMap CutPhase.word |>.map w).sum := by
  cases s with
  | scalar I => simp [blockWords,reserved]
  | positive s => exact s.block_weight_bound w hw
  | leadingBlock I c d s =>
    have hh := s.block_weight_bound w hw
    have hc := hw c.pivot
    have hd := list_weight_nonnegative w hw d.word
    simp only [CutPhase.word,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hd
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.flatMap_append,List.flatMap_cons,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hh,hc,hd]
  | leadingEnd I c =>
    have hc := hw c.pivot
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hc]

theorem block_inverse_bound (s : CompleteInitialCutAssembly) (μ : ℝ) :
    (s.blockWords.map fun I => inverseCharge μ I).sum ≤ inverseCharge μ (s.reserved.flatMap CutPhase.word) := by
  simpa only [inverseCharge] using s.block_weight_bound (fun a => inverseLogKernel (1-μ*a))
    (fun _ => inverseLogKernel_nonneg _)

theorem block_growth_budget {κ μ : ℝ} (hκ : 0 < κ) (hμ : 1/κ ≤ μ) (s : CompleteInitialCutAssembly) :
    (s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum ≤
      phaseGapMass s.reserved/κ+(s.reserved.length : ℝ) := by
  have hh := s.block_weight_bound (smallPositiveStep μ) (smallPositiveStep_nonneg μ)
  change (s.blockWords.map fun I => smallPositiveSum μ I).sum ≤ smallPositiveSum μ (s.reserved.flatMap CutPhase.word) at hh
  have hb := hh.trans (phases_small_sum_budget hκ hμ s.reserved)
  have hdiv := div_le_div_of_nonneg_right hb hκ.le
  have he : (phaseGapMass s.reserved+κ*(s.reserved.length : ℝ))/κ = phaseGapMass s.reserved/κ+(s.reserved.length : ℝ) := by field_simp
  exact (logs_scaled_small_sum_le hκ μ s.blockWords).trans (hdiv.trans_eq he)

theorem reserved_weight_le (s : CompleteInitialCutAssembly) (w : CutPhase → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (s.reserved.map w).sum ≤ (s.phases.map w).sum := by
  have hh := s.weight_partition w
  have hp : 0 ≤ (s.trackedPhases.map w).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    exact hw q
  linarith only [hh,hp]

theorem reserved_inverse_budget {κ μ B : ℝ}
    (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*κ)) (hcap : μ*B ≤ 1/2)
    (s : CompleteInitialCutAssembly) (t : List ℝ) (hgap : ∀ q ∈ s.reserved, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    inverseCharge μ (s.reserved.flatMap CutPhase.word) ≤
      2*μ*phaseGapMass s.reserved+2*(s.reserved.length : ℝ)+largeInverseCharge κ (s.word t) μ := by
  have hh := phases_initial_inverse_budget hκ hμ hμu hcap s.reserved hgap
  let w : ℝ → ℝ := fun b => if κ/2 < b then inverseLogKernel (1-μ*b) else 0
  have hw : ∀ b, 0 ≤ w b := by intro b; dsimp only [w]; split_ifs <;> first | exact inverseLogKernel_nonneg _ | exact le_rfl
  have hreserve := s.reserved_weight_le (fun q => w q.pivot) (fun q => hw q.pivot)
  have hwhole := (ScheduleCut.mk s.phases t).selected_weight_le w hw
  change (s.phases.map fun q => w q.pivot).sum ≤ largeInverseCharge κ (s.word t) μ at hwhole
  exact hh.trans (add_le_add le_rfl (hreserve.trans hwhole))

theorem logCost_raw {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (hK : 1 ≤ κ/B)
    (A μ P : ℝ) (choose : ℕ → ℝ → Bool) (t : List ℝ) (s : CompleteInitialCutAssembly) :
    s.logCost A κ B μ P choose t ≤
      2*((s.trackedPhases.flatMap (refinePhase choose)).map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
      4*μ*Scalar.SignedIntervals.positiveMass t+initialLogPriceConstant*(s.blockCount : ℝ)*(1+Real.log (κ/B))+
      2*(s.blockWords.map fun I => inverseCharge μ I).sum+
      2*(s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum := by
  cases s with
  | scalar I =>
    have hg := log_one_add_nonnegative (div_nonneg (smallPositiveSum_nonneg μ (I.flatMap CutPhase.word)) hκ.le)
    simp only [logCost,trackedPhases,blockWords,blockCount,List.flatMap_nil,List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,
      Nat.cast_zero,mul_zero,zero_mul,add_zero,zero_add]
    linarith only [hg]
  | positive s => exact s.logCost_raw hκ hB hK A μ P (refinePhase choose) t
  | leadingBlock I c d s =>
    have hh := s.logCost_raw hκ hB hK A μ P (refinePhase choose) t
    have hp := (initial_log_price_bounds hκ hB hK μ (I.flatMap CutPhase.word++c.gap) t).1
    simp only [logCost,trackedPhases,blockWords,blockCount,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,hp]
  | leadingEnd I c =>
    have hlog := Real.log_nonneg hK
    have hb := initialLogPriceConstant_bounds
    have hp := mul_nonneg (sub_nonneg.mpr hb.1) hlog
    simp only [logCost,trackedPhases,blockWords,blockCount,List.flatMap_nil,List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,
      Nat.cast_one,mul_zero,zero_mul,mul_one,add_zero,zero_add]
    norm_num at hb ⊢
    nlinarith only [hb.2.2.2.2,hp,hlog]

end
end StrongSilver.CompleteInitialCutAssembly
