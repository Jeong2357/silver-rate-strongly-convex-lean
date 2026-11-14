-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AveragingScales

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

def bandSigma (η : ℝ) : ℝ := η/16
def bandTau (η : ℝ) : ℝ := η/128
def bandUpsilon (η : ℝ) : ℝ := η/4
def bandPowerGap (η : ℝ) : ℝ := η/(1-η)

theorem band_exponent_bounds {η : ℝ} (hη : 0 < η) (hηmax : η ≤ 1/100) :
    0 < bandSigma η ∧ bandSigma η ≤ 1/200 ∧
    0 < bandTau η ∧ bandTau η ≤ 1/1000 ∧
    bandSigma η < bandUpsilon η ∧ bandTau η < bandUpsilon η ∧
    bandUpsilon η ≤ 1/50 ∧ bandUpsilon η ≤ bandPowerGap η := by
  have hd : 0 < 1-η := by linarith only [hηmax]
  have hg : η ≤ η/(1-η) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hη]
  unfold bandSigma bandTau bandUpsilon bandPowerGap
  exact ⟨by positivity,by linarith only [hηmax],by positivity,by linarith only [hηmax],
    by linarith only [hη],by linarith only [hη],by linarith only [hηmax],by linarith only [hg,hη]⟩

theorem firstAverageEta_small : firstAverageEta ≤ 1/100 := by
  have hh := initialPowerXi_upper
  unfold firstAverageEta
  linarith only [hh]

/-- The original upper cutoff constraint gives the exact power gap
used to discharge all working rank errors uniformly across a band. -/
theorem band_cutoff_power_gap {η A B : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hA : 0 < A) (hB : 0 < B) (hupper : A ≤ B^(1-η)) : A^(1+bandPowerGap η) ≤ B := by
  have hd := sub_pos.mpr hη1
  have hq := div_pos hη hd
  have hh := Real.rpow_le_rpow hA.le hupper (show 0 ≤ 1+bandPowerGap η by unfold bandPowerGap; linarith only [hq])
  rw [← Real.rpow_mul hB.le] at hh
  have he : (1-η)*(1+bandPowerGap η) = 1 := by
    unfold bandPowerGap
    field_simp [hd.ne'] <;> ring
  rwa [he,Real.rpow_one] at hh

end
end StrongSilver
