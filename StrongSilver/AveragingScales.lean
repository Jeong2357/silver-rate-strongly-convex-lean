-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPowerExponents
import StrongSilver.PowerMargins

namespace StrongSilver
open Real Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

def firstAverageEta : ℝ := initialPowerXi/8
def firstAverageLogScale (B : ℝ) : ℝ := (1-2*firstAverageEta)*Real.log B
def finalAverageLogScale (R : ℝ) : ℝ := Real.log R/(4*nu)

theorem firstAverageEta_bounds : 0 < firstAverageEta ∧ firstAverageEta < 1/8 := by
  have hl := initialPowerXi_positive
  have hu := initialPowerXi_upper
  unfold firstAverageEta
  constructor <;> linarith only [hl,hu]

theorem firstAverageLogScale_escape : Tendsto firstAverageLogScale atTop atTop := by
  have hc : 0 < 1-2*firstAverageEta := by have hh := firstAverageEta_bounds.2; linarith only [hh]
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (M/(1-2*firstAverageEta))] with B hB
  simpa only [firstAverageLogScale,mul_comm] using (div_le_iff₀ hc).mp hB

theorem finalAverageLogScale_escape : Tendsto finalAverageLogScale atTop atTop := by
  have hc : 0 < 4*nu := by have hh := nu_positive; positivity
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (M*(4*nu))] with R hR
  exact (le_div_iff₀ hc).mpr hR

/-- The entire first averaging window lies in the initial threshold
interval and strictly below the starting cutoff. -/
theorem eventually_first_average_window : ∀ᶠ B : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
    B^(1-initialPowerXi) ≤ Real.exp (firstAverageLogScale B+t*Real.sqrt (firstAverageLogScale B)) ∧
    Real.exp (firstAverageLogScale B+t*Real.sqrt (firstAverageLogScale B)) < B := by
  have hη := firstAverageEta_bounds.1
  have hηu := firstAverageEta_bounds.2
  have hηsq : 0 < firstAverageEta^2 := sq_pos_of_pos hη
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1/(firstAverageEta^2))] with B hB hlog
  intro t ht
  have hB0 := zero_lt_one.trans hB
  have hU := Real.log_pos hB
  have hprod := mul_le_mul_of_nonneg_left hlog hηsq.le
  have he : firstAverageEta^2*(1/(firstAverageEta^2)) = 1 := by field_simp
  rw [he] at hprod
  have hprodU := mul_le_mul_of_nonneg_right hprod hU.le
  have hroot : Real.sqrt (Real.log B) ≤ firstAverageEta*Real.log B := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hη.le hU.le)).mp
    rw [Real.sq_sqrt hU.le]
    nlinarith only [hprodU]
  have hu0 : 0 ≤ firstAverageLogScale B := by
    unfold firstAverageLogScale
    exact mul_nonneg (by linarith only [hηu]) hU.le
  have huU : firstAverageLogScale B ≤ Real.log B := by
    unfold firstAverageLogScale
    nlinarith only [mul_nonneg hη.le hU.le]
  have hsqrt := (Real.sqrt_le_sqrt huU).trans hroot
  have ht0 := mul_nonneg ht.1 (Real.sqrt_nonneg (firstAverageLogScale B))
  have ht1 := mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg (firstAverageLogScale B))
  have hηU := mul_pos hη hU
  have hlo : (1-initialPowerXi)*Real.log B ≤ firstAverageLogScale B+t*Real.sqrt (firstAverageLogScale B) := by
    unfold firstAverageLogScale firstAverageEta at *
    nlinarith only [ht0,mul_nonneg initialPowerXi_positive.le hU.le]
  have hhi : firstAverageLogScale B+t*Real.sqrt (firstAverageLogScale B) < Real.log B := by
    unfold firstAverageLogScale at *
    nlinarith only [ht1,hsqrt,hηU]
  constructor
  · rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    nlinarith only [hlo]
  · exact (Real.exp_lt_exp.mpr hhi).trans_eq (Real.exp_log hB0)

end
end StrongSilver
