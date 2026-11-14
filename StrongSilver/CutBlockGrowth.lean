-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutAssemblyWeights
import StrongSilver.LogOnePlusBudget

namespace StrongSilver.CutAssembly
noncomputable section
set_option maxHeartbeats 1400000

theorem block_growth_bound (s : CutAssembly) (t : List ℝ) (μ : ℝ) :
    (((s.erase t).blockWords.map fun I => Real.log (1+smallPositiveSum μ I)).sum) ≤
      (s.reserved.map phaseGrowthCharge).sum := by
  induction s with
  | ordinaryEnd q => simp [erase,WorkingAssembly.blockWords,reserved]
  | ordinary q s ih => simpa only [erase,WorkingAssembly.blockWords,reserved] using ih
  | block q I c s ih =>
    have hI := log_one_add_block_mass μ I c.gap
    have hq := phaseGrowthCharge_nonnegative q
    have hc : Real.log (1+Scalar.SignedIntervals.positiveMass c.gap) ≤ phaseGrowthCharge c :=
      le_add_of_nonneg_right (log_one_add_nonnegative (le_max_right c.pivot 0))
    simp only [erase,WorkingAssembly.blockWords,reserved,List.map_cons,List.map_append,List.sum_cons,List.sum_append]
    linarith only [ih,hI,hq,hc]
  | blockEnd q I c =>
    have hI := log_one_add_block_mass μ I c.gap
    have hq := phaseGrowthCharge_nonnegative q
    have hc : Real.log (1+Scalar.SignedIntervals.positiveMass c.gap) ≤ phaseGrowthCharge c :=
      le_add_of_nonneg_right (log_one_add_nonnegative (le_max_right c.pivot 0))
    simp only [erase,WorkingAssembly.blockWords,reserved,List.map_cons,List.map_append,List.sum_cons,List.sum_append,List.map_nil,List.sum_nil]
    linarith only [hI,hq,hc]
  | noConnector q I =>
    have hI := log_one_add_block_mass μ I []
    simp only [List.append_nil,Scalar.SignedIntervals.positiveMass,List.map_nil,List.sum_nil,
      add_zero,Real.log_one] at hI
    have hq := phaseGrowthCharge_nonnegative q
    simp only [erase,WorkingAssembly.blockWords,reserved,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil]
    linarith only [hI,hq]

end
end StrongSilver.CutAssembly
