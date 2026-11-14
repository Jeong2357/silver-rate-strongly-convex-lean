-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalParameters
import StrongSilver.FourPhaseFamilyRenewal
import StrongSilver.FourPhaseJoiningMargins

namespace StrongSilver.FourPhase.LocalParameters
noncomputable section
set_option maxHeartbeats 1800000

theorem localFamily_renewal (D : LocalParameters) : FourPhaseSuffixBounds D.localFamily (source D.shape) D.T 0 := by
  unfold localFamily
  exact queryFamily_renewal D.geometry.regular D.offset_nonnegative
    (D.geometry.a_upper.trans (by norm_num)) D.geometry.masses_lower D.offset_upper D.time_positive
    (fun j : D.QueryIndex => j.1) D.queryScale D.querySlack D.queryScale_lower D.querySlack_nonnegative
    D.geometry.total_upper D.geometry.time0_lower D.geometry.time1_lower

theorem localFamily_gate (D : LocalParameters) {η : ℝ} (hη : 0 ≤ η) (hζ : 512*η ≤ D.ζ) :
    D.localFamily.Gate (source D.shape) η := by
  have hbudget : η*‖source D.shape‖^2 ≤ a D.shape*D.ζ :=
    gate_intercept_margin D.geometry.a_lower D.offset_nonnegative hη D.geometry.source_norm_upper hζ
  unfold localFamily
  exact queryFamily_gate D.geometry.regular D.offset_nonnegative
    (D.geometry.a_upper.trans (by norm_num)) D.geometry.masses_lower D.offset_upper D.time_positive
    (fun j : D.QueryIndex => j.1) D.queryScale D.querySlack D.queryScale_lower D.querySlack_nonnegative
    D.geometry.time0_lower D.geometry.time1_lower hη hbudget

end
end StrongSilver.FourPhase.LocalParameters
