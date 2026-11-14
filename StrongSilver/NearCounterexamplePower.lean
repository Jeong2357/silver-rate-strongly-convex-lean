-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NearInitialCompressedPower
import StrongSilver.RefinedPowerDomination
import StrongSilver.FullCutPaddingRank
import StrongSilver.CounterexampleThresholds
import StrongSilver.ClosedCutAsFull

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2600000

/-- Near branch of Lemma 3.9 on the original full cuts: all reserved and
terminal gaps are restored, and the common large pad is removed. -/
theorem CounterexampleSequence.eventually_near_full_cut_power {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16)
    (S : CounterexampleSequence a) : ∀ᶠ j : ℕ in atTop,
    (S.kappa j)^(1-initialPowerEpsilon) ≤ S.threshold j →
    ∃ μ : ℝ, 1/S.kappa j ≤ μ ∧ μ ≤ 9/(8*S.kappa j) ∧ (∀ b ∈ S.schedules j, 1-μ*b ≠ 0) ∧
      inverseChargeAbove (S.kappa j/4) (S.schedules j) μ ≤ 34*(countAbove (S.schedules j) (S.kappa j/4) : ℝ) ∧
      ∀ A : ℝ, (S.threshold j)^(1-initialPowerXi) ≤ A → A < S.threshold j →
        (powerLogMinimum/16)*weightedCount (S.schedules j) (a*S.kappa j) ≤
          cutPower (cappedStep μ (S.threshold j)) 1 0 (fullCut A (S.schedules j)) := by
  have hr : (initialPowerXi-(13 : ℝ)/1000)*nu < 0 :=
    mul_neg_of_neg_of_pos (by linarith only [initialPowerXi_upper]) nu_positive
  have ht : Tendsto (fun B : ℝ => 2*B^((initialPowerXi-(13 : ℝ)/1000)*nu)) atTop (𝓝 0) := by
    simpa only [neg_neg,mul_zero] using (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).const_mul 2
  have hpad := (tendsto_order.1 ht).2 (powerLogMinimum/16) (by have hh := powerLogMinimum_positive; positivity)
  filter_upwards [S.threshold_escape.eventually (eventually_near_initial_compressed_power ha hamax htrack herror),
    S.threshold_escape.eventually hpad,S.threshold_escape.eventually (eventually_gt_atTop (1 : ℝ))]
    with j hfactory hpadding hB1
  intro hnear
  have hκ : 1 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hmax : weightedCount (S.schedules j) (a*S.kappa j) =
      (countAbove (S.schedules j) (S.threshold j) : ℝ)*(S.threshold j)^nu := by
    simpa only [mul_comm] using (S.threshold_maximizes j).symm
  obtain ⟨μ,R,hμ,hμu,hcrit,hquarter,hpowers⟩ := hfactory (S.kappa j) (S.schedules j) hκ (S.threshold_le_cap j) hnear hmax (S.distance_le_one j)
  refine ⟨μ,hμ,hμu,hcrit,hquarter,?_⟩
  intro A hfloor hAB
  have hξ1 : initialPowerXi < 1 := initialPowerXi_upper.trans_lt (by norm_num)
  have hA1 : 1 < A := (Real.one_lt_rpow hB1 (sub_pos.mpr hξ1)).trans_le hfloor
  have hA0 := zero_lt_one.trans hA1
  have hcountB : 1 ≤ countAbove (S.schedules j) (S.threshold j) := by
    have hh := S.weight_positive j
    have hp := Real.rpow_pos_of_pos (S.threshold_positive j) nu
    have hc : (0 : ℝ) < (countAbove (S.schedules j) (S.threshold j) : ℝ) := by nlinarith only [hh,hmax,hp]
    exact_mod_cast hc
  have hcountA : 1 ≤ countAbove (S.schedules j) A := hcountB.trans (countAbove_antitone (S.schedules j) hAB.le)
  have htransfer := R.compressed_full_cut_power_le (cappedStep μ (S.threshold j))
    (Real.rpow_pos_of_pos (S.threshold_positive j) ((987 : ℝ)/1000)).le hAB (fun _ hq => closedCut_pivot hq)
  have hword : (closedCut (S.threshold j) (S.schedules j)).word = S.schedules j := cutSchedule_word _ _
  rw [hword] at htransfer
  have hlargePad := (hpowers A hfloor hAB).trans htransfer
  have hraw := full_cut_remove_padding_rank (cappedStep μ (S.threshold j)) hA0 (S.threshold_positive j)
    (hAB.le.trans (S.threshold_le_cap j)) hfloor (by norm_num : (0 : ℝ) ≤ 0) (S.schedules j) hcountA hlargePad
  rw [Real.zero_rpow nu_positive.ne'] at hraw
  have hcost := mul_le_mul_of_nonneg_left hpadding.le (S.weight_positive j).le
  linear_combination hraw+hcost

end
end StrongSilver
