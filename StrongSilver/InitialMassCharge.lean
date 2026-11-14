-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAssemblyCost
import StrongSilver.WorkingGlobalLogBudget

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1600000

theorem smallPositiveStep_le_kappa {κ μ : ℝ} (hκ : 0 < κ) (hμ : 1/κ ≤ μ) (b : ℝ) :
    smallPositiveStep μ b ≤ κ := by
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ).trans_le hμ
  have hmul := (div_le_iff₀ hκ).mp hμ
  have hinv : 1/μ ≤ κ := (div_le_iff₀ hμ0).mpr (by nlinarith only [hmul])
  unfold smallPositiveStep
  split_ifs with hb
  · exact hb.2.le.trans hinv
  · exact hκ.le

theorem phases_small_sum_budget {κ μ : ℝ} (hκ : 0 < κ) (hμ : 1/κ ≤ μ) (qs : List CutPhase) :
    smallPositiveSum μ (qs.flatMap CutPhase.word) ≤ phaseGapMass qs+κ*(qs.length : ℝ) := by
  induction qs with
  | nil => simp [smallPositiveSum,phaseGapMass]
  | cons q qs ih =>
    have hg := smallPositiveSum_le_positiveMass μ q.gap
    have hp := smallPositiveStep_le_kappa hκ hμ q.pivot
    simp only [List.flatMap_cons,CutPhase.word,smallPositiveSum_append,phaseGapMass,List.map_cons,
      List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    have hs : smallPositiveSum μ [q.pivot] = smallPositiveStep μ q.pivot := by simp [smallPositiveSum]
    rw [hs]
    change smallPositiveSum μ (qs.flatMap CutPhase.word) ≤
      (qs.map fun z => Scalar.SignedIntervals.positiveMass z.gap).sum+κ*(qs.length : ℝ) at ih
    nlinarith only [ih,hg,hp]

theorem logs_scaled_small_sum_le {κ : ℝ} (hκ : 0 < κ) (μ : ℝ) (blocks : List (List ℝ)) :
    (blocks.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum ≤
      (blocks.map fun I => smallPositiveSum μ I).sum/κ := by
  induction blocks with
  | nil => simp
  | cons I Is ih =>
    have hS := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+smallPositiveSum μ I/κ by linarith only [hS])
    simp only [List.map_cons,List.sum_cons]
    rw [add_div]
    linarith only [hh,ih]

theorem InitialCutAssembly.block_growth_budget {κ μ : ℝ} (hκ : 0 < κ) (hμ : 1/κ ≤ μ) (s : InitialCutAssembly) :
    (s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum ≤
      phaseGapMass s.reserved/κ+(s.reserved.length : ℝ) := by
  have hh := s.block_weight_bound (smallPositiveStep μ) (smallPositiveStep_nonneg μ)
  change (s.blockWords.map fun I => smallPositiveSum μ I).sum ≤ smallPositiveSum μ (s.reserved.flatMap CutPhase.word) at hh
  have hb := hh.trans (phases_small_sum_budget hκ hμ s.reserved)
  have hdiv := div_le_div_of_nonneg_right hb hκ.le
  have he : (phaseGapMass s.reserved+κ*(s.reserved.length : ℝ))/κ = phaseGapMass s.reserved/κ+(s.reserved.length : ℝ) := by field_simp
  exact (logs_scaled_small_sum_le hκ μ s.blockWords).trans (hdiv.trans_eq he)

end
end StrongSilver
