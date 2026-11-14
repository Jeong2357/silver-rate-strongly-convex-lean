-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerLogFloor

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

def initialPowerSigma : ℝ := 1/100000
def initialPowerTau : ℝ := 1/100000
def initialPowerUpsilon : ℝ := 1/50000
def initialPowerEpsilon : ℝ := 1/10000
def initialPowerXi : ℝ := min (1/1000000) (powerLogMinimum/(1000000*splitCoefficient))

theorem initialPowerXi_positive : 0 < initialPowerXi := by
  exact lt_min (by norm_num) (div_pos powerLogMinimum_positive (by have hh := split_coefficient_positive; positivity))

theorem initialPowerXi_upper : initialPowerXi ≤ 1/1000000 := min_le_left _ _

theorem initialPowerXi_count_margin :
    splitCoefficient*((4800/(1-initialPowerXi))*initialPowerXi) < powerLogMinimum/4 := by
  have hx := initialPowerXi_positive
  have hxu := initialPowerXi_upper
  have hc := split_coefficient_positive
  have hm := powerLogMinimum_positive
  have hd : 0 < 1-initialPowerXi := by linarith only [hxu]
  have hinv : 1/(1-initialPowerXi) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith only [hxu])
  have hbound := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4800*splitCoefficient*initialPowerXi by positivity)
  have hsmall : initialPowerXi ≤ powerLogMinimum/(1000000*splitCoefficient) := min_le_right _ _
  have hs := (le_div_iff₀ (show 0 < 1000000*splitCoefficient by positivity)).mp hsmall
  ring_nf at hbound hs ⊢
  nlinarith only [hbound,hs,hm]

theorem initialPowerSigma_decay :
    nu+(1-initialPowerXi)*(-nu*(1+initialPowerSigma)) < 0 := by
  have hc : initialPowerXi*(1+initialPowerSigma)-initialPowerSigma < 0 := by
    unfold initialPowerSigma
    linarith only [initialPowerXi_upper]
  have hh := mul_neg_of_pos_of_neg nu_positive hc
  nlinarith only [hh]

theorem initialPowerTau_decay : nu+(1-initialPowerXi)*(-nu-initialPowerTau) < 0 := by
  have hmul := mul_nonneg initialPowerXi_positive.le (sub_nonneg.mpr nu_lt_one.le)
  have hu := initialPowerXi_upper
  unfold initialPowerTau
  nlinarith only [hmul,hu]

theorem initialPowerUpsilon_decay :
    nu+(1-initialPowerXi)*(-nu*(1+initialPowerUpsilon)) < 0 := by
  have hc : initialPowerXi*(1+initialPowerUpsilon)-initialPowerUpsilon < 0 := by
    unfold initialPowerUpsilon
    linarith only [initialPowerXi_upper]
  have hh := mul_neg_of_pos_of_neg nu_positive hc
  nlinarith only [hh]

theorem initialPower_time_separation : (1-initialPowerEpsilon)*(1+initialPowerUpsilon) < 1 := by
  norm_num [initialPowerEpsilon,initialPowerUpsilon]

theorem initialPower_near_scale :
    1 ≤ (1-initialPowerEpsilon)*(1-initialPowerXi)*((1003 : ℝ)/1000) := by
  unfold initialPowerEpsilon
  linarith only [initialPowerXi_upper]

end
end StrongSilver
