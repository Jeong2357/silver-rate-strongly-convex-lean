-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianNormalizedSchedule
import StrongSilver.FourPhaseUniformJoiningBudgets

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3000000

/-- The sharp exterior time margins follow from actual signed products
on every balanced group, with one absolute tolerance. -/
theorem exists_uniform_exterior_time_radius : ∃ δ > 0,
    ∀ G : FourGapGroup, ∀ μ T b ε B : ℝ,
    BalancedGroupData G μ T b ε → ε+μ*T ≤ δ → 0 ≤ B → μ*B ≤ 1/2 →
    100 ≤ b → drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ b/100 → μ*b ≤ 1/10000 →
    (19/20:ℝ)*(cappedStep μ B b) ≤ T*lastExcess μ T G.gaps (G.pivots b) ∧
      T*lastExcess μ T G.gaps (G.pivots b) ≤ 2*b := by
  obtain ⟨C,hC,δ,hδ,hconstruct⟩ := exists_normalized_group_schedule
  refine ⟨δ,hδ,?_⟩
  intro G μ T b ε B D hnear hB hμB hb hd hμb
  obtain ⟨S,hSμ,hST,hSgap,hSpivot,_⟩ := hconstruct G μ T b ε B D hnear hB hμB
  have hsmall : μ*absoluteMass (boundedWord G.gaps (G.pivots b)) ≤ 1/4 := by
    simpa only [hSμ,hSgap,hSpivot] using S.small_total
  have hTpos := zero_lt_one.trans_le D.scale_lower
  have hds : μ*drawdown ((G.gaps 3).map (logarithmicStep μ)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hd D.mu_positive.le
    nlinarith only [hh,hμb]
  have he := actual_last_excess_error D.mu_positive hTpos G.gaps (G.pivots b) hsmall
    (by change 0 ≤ b; linarith only [hb]) hds
  change |T*lastExcess μ T G.gaps (G.pivots b)-(b-1-drawdown ((G.gaps 3).map (logarithmicStep μ)))| ≤
    μ*(drawdown ((G.gaps 3).map (logarithmicStep μ)))^2+2*μ*b*drawdown ((G.gaps 3).map (logarithmicStep μ)) at he
  obtain ⟨hφ,hφe⟩ := capped_step_error_le_square D.mu_positive hB (by linarith only [hb]) hμB
  exact last_excess_strong_scale D.mu_positive hTpos hb (drawdown_nonneg _) hd hμb hφ hφe he

end
end StrongSilver.ScheduleTree.FourGapGroup
