-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandIntegralEstimates
import StrongSilver.InitialCapArbitrarilySmall

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- The integrated upper budgets use precisely the same curvature and
quarter-scale charge as the averaged power lower bound. They hold for
every band between the actual stopping and initial scales. -/
theorem CounterexampleSequence.eventually_uniform_band_integrals {a : ℝ}
    (ha : 0 < a) (hamax : a ≤ 1/128) (S : CounterexampleSequence a) :
    ∀ᶠ j : ℕ in atTop,
    ∀ μ : ℝ, 1/S.kappa j ≤ μ → μ ≤ 9/(8*S.kappa j) →
    (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) →
    inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4):ℝ) →
    ∀ u : ℝ,
    finalAverageLogScale (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length:ℝ)) ≤ u →
    u ≤ firstAverageLogScale (S.threshold j) →
    BandIntegralBounds (S.kappa j) (S.threshold j) (a*S.kappa j) μ u (S.schedules j) := by
  obtain ⟨u₀,hbounds⟩ := eventually_atTop.mp eventually_band_integral_estimates
  have hY := finalAverageLogScale_escape.comp S.ratio_escape
  filter_upwards [hY.eventually_ge_atTop u₀,S.threshold_escape.eventually_gt_atTop (1:ℝ),
    S.ratio_escape.eventually_ge_atTop (1:ℝ)] with j hYj hB hratio
  intro μ hμ hμu hcrit hcritical u hYu hU
  have hκ : 1 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hκ0 := zero_lt_one.trans hκ
  have hcap0 := mul_pos ha hκ0
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hμUpper : μ ≤ 2/S.kappa j := by
    have hh := (le_div_iff₀ (show 0 < 8*S.kappa j by positivity)).mp hμu
    apply (le_div_iff₀ hκ0).mpr
    nlinarith only [hh]
  have hcapκ : a*S.kappa j ≤ S.kappa j := by
    have hh := mul_le_mul_of_nonneg_right (hamax.trans (by norm_num : (1:ℝ)/128 ≤ 1)) hκ0.le
    simpa only [one_mul] using hh
  have hμB : μ*S.threshold j ≤ 1/2 := by
    have hh := S.curvature_threshold_bound j hμ0.le hμu
    linarith only [hh,hamax]
  have hcapQuarter : a*S.kappa j ≤ S.kappa j/4 := by
    have hh := mul_le_mul_of_nonneg_right (hamax.trans (by norm_num : (1:ℝ)/128 ≤ 1/4)) hκ0.le
    nlinarith only [hh]
  have hcountRank := (countAbove_rank_bound (S.schedules j) hcap0 le_rfl)
  have hcountMono := countAbove_antitone (S.schedules j) hcapQuarter
  have hcriticalRank : 34*(countAbove (S.schedules j) (S.kappa j/4):ℝ) ≤
      34*weightedCount (S.schedules j) (a*S.kappa j)*(a*S.kappa j)^(-nu) := by
    have hmono : (countAbove (S.schedules j) (S.kappa j/4):ℝ) ≤ (countAbove (S.schedules j) (a*S.kappa j):ℝ) := by
      exact_mod_cast hcountMono
    nlinarith only [hmono,hcountRank]
  have hcountB : 1 ≤ countAbove (S.schedules j) (S.threshold j) := by
    by_contra hn
    have hz : countAbove (S.schedules j) (S.threshold j) = 0 := by omega
    have hh := S.threshold_maximizes j
    rw [hz,Nat.cast_zero,mul_zero] at hh
    have hp := S.weight_positive j
    linarith only [hh,hp]
  have hn : (0:ℝ) < (S.schedules j).length := by exact_mod_cast S.length_pos j
  have hW : ((S.schedules j).length:ℝ) ≤ weightedCount (S.schedules j) (a*S.kappa j) := by
    have hh := (le_div_iff₀ hn).mp hratio
    simpa only [one_mul] using hh
  have hκW := (S.length_large j).trans hW
  exact hbounds u (hYj.trans hYu) (S.kappa j) (S.threshold j) (a*S.kappa j) μ
    (34*(countAbove (S.schedules j) (S.kappa j/4):ℝ)) (S.schedules j) hκ hB (S.threshold_le_cap j) hcapκ hU
    hμ hμUpper hμB hcrit hcritical hcriticalRank (S.distance_le_one j) hcountB hκW

end
end StrongSilver
