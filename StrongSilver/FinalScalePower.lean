-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutPowerCrudeUpper
import StrongSilver.CounterexampleThresholds

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2200000

def finalCutoffExponent : ℝ := 1/(2*nu)
def finalPowerError (R : ℝ) : ℝ := 4*R^(finalCutoffExponent-1)+R⁻¹

theorem finalCutoffExponent_bounds : 0 < finalCutoffExponent ∧ finalCutoffExponent < 1 := by
  have hν := nu_positive
  have hνlarge := nu_gt_three_quarters
  constructor
  · unfold finalCutoffExponent; positivity
  · unfold finalCutoffExponent
    exact (div_lt_one (by positivity : 0 < 2*nu)).mpr (by linarith only [hνlarge])

theorem finalPowerError_tendsto_zero : Tendsto finalPowerError atTop (𝓝 0) := by
  have hp : Tendsto (fun R : ℝ => R^(finalCutoffExponent-1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr finalCutoffExponent_bounds.2)
  have hh := (hp.const_mul 4).add tendsto_inv_atTop_zero
  simp only [mul_zero,add_zero] at hh
  exact hh

/-- The final averaging scale has uniformly negligible power. A linear
mass estimate is sufficient here; no Jensen inequality is needed. -/
theorem CounterexampleSequence.eventually_final_cut_power_small {a c : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (S : CounterexampleSequence a) (hc : 0 < c) : ∀ᶠ j : ℕ in atTop,
    ∀ μ A : ℝ, 0 < μ → μ ≤ 9/(8*S.kappa j) → 1 ≤ A → A ≤ S.threshold j →
      A ≤ (weightedCount (S.schedules j) (a*S.kappa j)/((S.schedules j).length : ℝ))^finalCutoffExponent →
      cutPower (cappedStep μ (S.threshold j)) 1 (S.kappa j) (fullCut A (S.schedules j)) ≤
        c*weightedCount (S.schedules j) (a*S.kappa j) := by
  have herror := (tendsto_order.1 (finalPowerError_tendsto_zero.comp S.ratio_escape)).2 c hc
  filter_upwards [herror] with j hj
  intro μ A hμ hμu hA hAB hAmax
  have hκ0 : 0 < S.kappa j := lt_of_lt_of_le (by norm_num) (S.kappa_ge_two j)
  have hB0 := S.threshold_positive j
  have hh := mul_le_mul hμu (S.threshold_le_cap j) hB0.le (show 0 ≤ 9/(8*S.kappa j) by positivity)
  have he : (9/(8*S.kappa j))*(a*S.kappa j) = (9/8)*a := by field_simp <;> ring
  rw [he] at hh
  have hμB : μ*S.threshold j ≤ 1/2 := by nlinarith only [hh,hamax]
  have hupper := full_cut_power_crude_upper hμ hB0 hμB hA hAB hκ0.le (S.schedules j) (S.length_pos j)
  let W := weightedCount (S.schedules j) (a*S.kappa j)
  let n := ((S.schedules j).length : ℝ)
  let R := W/n
  have hn : 0 < n := by
    have hh : (1 : ℝ) ≤ n := by
      change (1 : ℝ) ≤ ((S.schedules j).length : ℝ)
      exact_mod_cast S.length_pos j
    linarith only [hh]
  have hW : 0 < W := S.weight_positive j
  have hR : 0 < R := div_pos hW hn
  change finalPowerError R < c at hj
  have hRn : R*n = W := div_mul_cancel₀ W hn.ne'
  have hpow : R^(finalCutoffExponent-1)*R = R^finalCutoffExponent := by
    calc
      _ = R^(finalCutoffExponent-1)*R^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  have hnpow : n*R^finalCutoffExponent = W*R^(finalCutoffExponent-1) := by
    calc
      _ = (R*n)*R^(finalCutoffExponent-1) := by rw [← hpow]; ring
      _ = _ := by rw [hRn]
  have hninv : n = W*R⁻¹ := by rw [← hRn]; field_simp
  have hAcharge := mul_le_mul_of_nonneg_left hAmax (show 0 ≤ 4*n by positivity)
  have htotal : cutPower (cappedStep μ (S.threshold j)) 1 (S.kappa j) (fullCut A (S.schedules j)) ≤ W*finalPowerError R := by
    calc
      _ ≤ 4*n*A+(S.kappa j)^nu := hupper
      _ ≤ 4*n*R^finalCutoffExponent+n := add_le_add hAcharge (S.length_large j)
      _ = _ := by
        change 4*n*R^finalCutoffExponent+n = W*(4*R^(finalCutoffExponent-1)+R⁻¹)
        linear_combination 4*hnpow+hninv
  have hsmall : W*finalPowerError R ≤ c*W := by
    have hh := mul_le_mul_of_nonneg_left hj.le hW.le
    simpa only [mul_comm] using hh
  exact htotal.trans hsmall

end
end StrongSilver
