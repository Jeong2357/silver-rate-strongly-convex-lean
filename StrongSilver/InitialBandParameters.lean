-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseBudget
import StrongSilver.NegativeLogHalfScale

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

/-- The concrete numerical conditions (3.26) discharge the initial analytic
budget, using the original cutoff as the planar scale. -/
theorem initial_budget_of_kappa_band {κ B μ b : ℝ} (hκ : 1 ≤ κ) (hB : 0 < B)
    (hBκ : B ≤ κ/4) (hμlower : 1/κ ≤ μ) (hμupper : μ ≤ 9/(8*κ))
    (hb : B ≤ b) (hbκ : b ≤ κ/2) (h : List ℝ)
    (hS : Scalar.SignedIntervals.positiveMass h ≤ κ) (hE : negativeLogSum h κ ≤ 1)
    (hcap : ∀ c ∈ h, 0 < c → c ≤ B) : InitialPhaseBudget B μ b (3*κ/4) κ B h := by
  have hκ0 : 0 < κ := zero_lt_one.trans_le hκ
  have hT : 0 < 3*κ/4 := by positivity
  have hμ : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμlower
  have hμκ : μ*κ ≤ 9/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hμupper
    nlinarith only [hh]
  have hET := negativeLogSum_half_scale hκ0 hT (by linarith only [hκ0]) h
  refine {
    mu_positive := hμ
    kappa_large := hκ
    cutoff_lower := le_rfl
    B_positive := hB
    B_le_kappa := by linarith only [hBκ,hκ0]
    pivot_lower := hb
    pivot_upper := hbκ
    pivot_lt_time := by linarith only [hbκ,hκ0]
    time_lower := by linarith only [hκ0]
    time_upper := by linarith only [hκ0]
    cap_ratio := (div_le_iff₀ hT).mpr (by linarith only [hBκ,hκ0])
    curvature := by nlinarith only [hμκ]
    mass := hS
    gap_cap := hcap
    negative_charge := by linarith only [hET,hE]
  }

end
end StrongSilver
