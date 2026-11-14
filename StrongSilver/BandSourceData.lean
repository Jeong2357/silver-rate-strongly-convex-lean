-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandIntegralEstimates

namespace StrongSilver
noncomputable section

/-- Numeric and stability conditions on an original signed schedule.
There are no gain, integral, trajectory, or convergence hypotheses.
The final counterexample argument must discharge every field. -/
structure BandSourceData (κ B cap μ critical u : ℝ) (h : List ℝ) : Prop where
  kappa_gt_one : 1 < κ
  threshold_gt_one : 1 < B
  threshold_le_cap : B ≤ cap
  cap_le_kappa : cap ≤ κ
  threshold_small : B ≤ κ/128
  scale_upper : u ≤ firstAverageLogScale B
  curvature_lower : 1/κ ≤ μ
  curvature_upper : μ ≤ 2/κ
  curvature_threshold : μ*B ≤ 1/10000
  noncritical : ∀ z ∈ h, 1-μ*z ≠ 0
  critical_charge : inverseChargeAbove (κ/4) h μ ≤ critical
  critical_rank : critical ≤ 34*weightedCount h cap*cap^(-nu)
  distance_stable : D κ h ≤ 1
  threshold_count : 1 ≤ countAbove h B
  rank_lower : κ^nu ≤ weightedCount h cap

namespace BandSourceData
variable {κ B cap μ critical u : ℝ} {h : List ℝ}

theorem mu_positive (H : BandSourceData κ B cap μ critical u h) : 0 < μ :=
  (one_div_pos.mpr (zero_lt_one.trans H.kappa_gt_one)).trans_le H.curvature_lower

theorem curvature_half (H : BandSourceData κ B cap μ critical u h) : μ*B ≤ 1/2 := by
  linarith only [H.curvature_threshold]

end BandSourceData
end
end StrongSilver
