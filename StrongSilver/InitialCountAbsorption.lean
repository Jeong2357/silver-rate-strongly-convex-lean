-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPowerExponents
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000

theorem initialPowerXi_count_margin_strong :
    splitCoefficient*((4800/(1-initialPowerXi))*initialPowerXi) < powerLogMinimum/16 := by
  have hx := initialPowerXi_positive
  have hxu := initialPowerXi_upper
  have hc := split_coefficient_positive
  have hm := powerLogMinimum_positive
  have hd : 0 < 1-initialPowerXi := by linarith only [hxu]
  have hinv : 1/(1-initialPowerXi) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith only [hxu])
  have hb := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4800*splitCoefficient*initialPowerXi by positivity)
  have hsmall : initialPowerXi ≤ powerLogMinimum/(1000000*splitCoefficient) := min_le_right _ _
  have hs := (le_div_iff₀ (show 0 < 1000000*splitCoefficient by positivity)).mp hsmall
  ring_nf at hb hs ⊢
  nlinarith only [hb,hs,hm]

theorem eventually_initial_count_loss_small : ∀ᶠ B : ℝ in atTop,
    splitCoefficient*((4800/(1-initialPowerXi))*(1/Real.log B+initialPowerXi)) ≤ powerLogMinimum/16 := by
  have hl : Tendsto (fun B : ℝ => 1/Real.log B) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ht := ((hl.add_const initialPowerXi).const_mul (4800/(1-initialPowerXi))).const_mul splitCoefficient
  simp only [zero_add] at ht
  exact ((tendsto_order.1 ht).2 _ initialPowerXi_count_margin_strong).mono (fun _ hb => hb.le)

end
end StrongSilver
