-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandSourceData
import StrongSilver.InitialCapArbitrarilySmall

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 6000000

/-- Every field of the band source data holds for every scale of the
same counterexample schedule and the curvature chosen for its lower bound. -/
theorem CounterexampleSequence.eventually_uniform_band_source {a : ℝ}
    (ha : 0 < a) (hamax : a ≤ 1/1000000) (S : CounterexampleSequence a) :
    ∀ᶠ j : ℕ in atTop,
    ∀ μ : ℝ, 1/S.kappa j ≤ μ → μ ≤ 9/(8*S.kappa j) →
    (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) →
    inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4):ℝ) →
    ∀ u : ℝ, u ≤ firstAverageLogScale (S.threshold j) →
    BandSourceData (S.kappa j) (S.threshold j) (a*S.kappa j) μ
      (34*(countAbove (S.schedules j) (S.kappa j/4):ℝ)) u (S.schedules j) := by
  filter_upwards [S.threshold_escape.eventually_gt_atTop (1:ℝ),S.ratio_escape.eventually_ge_atTop (1:ℝ)]
    with j hB hratio
  intro μ hμ hμu hcrit hcritical u hU
  have hκ : 1 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hκ0 := zero_lt_one.trans hκ
  have hcap0 := mul_pos ha hκ0
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hμUpper : μ ≤ 2/S.kappa j := by
    have hh := (le_div_iff₀ (show 0 < 8*S.kappa j by positivity)).mp hμu
    apply (le_div_iff₀ hκ0).mpr
    nlinarith only [hh]
  have hcapκ : a*S.kappa j ≤ S.kappa j := by
    have hh := mul_le_mul_of_nonneg_right (hamax.trans (by norm_num : (1:ℝ)/1000000 ≤ 1)) hκ0.le
    simpa only [one_mul] using hh
  have hcapSmall : a*S.kappa j ≤ S.kappa j/128 := by
    have hh := mul_le_mul_of_nonneg_right (hamax.trans (by norm_num : (1:ℝ)/1000000 ≤ 1/128)) hκ0.le
    nlinarith only [hh]
  have hμB : μ*S.threshold j ≤ 1/10000 := by
    have hh := S.curvature_threshold_bound j hμ0.le hμu
    linarith only [hh,hamax]
  have hcapQuarter : a*S.kappa j ≤ S.kappa j/4 := by
    have hh := mul_le_mul_of_nonneg_right (hamax.trans (by norm_num : (1:ℝ)/1000000 ≤ 1/4)) hκ0.le
    nlinarith only [hh]
  have hcountRank := countAbove_rank_bound (S.schedules j) hcap0 le_rfl
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
  exact ⟨hκ,hB,S.threshold_le_cap j,hcapκ,(S.threshold_le_cap j).trans hcapSmall,hU,hμ,hμUpper,hμB,
    hcrit,hcritical,hcriticalRank,S.distance_le_one j,hcountB,(S.length_large j).trans hW⟩

end
end StrongSilver
