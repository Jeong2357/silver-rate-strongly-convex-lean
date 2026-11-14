-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutObservables
import StrongSilver.CutPowerPadding
import StrongSilver.WeightedTelescoping

namespace StrongSilver
open Real Set MeasureTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem cutPower_reserve_mono (φ : ℝ → ℝ) {P r s : ℝ} (hP : 0 ≤ P) (hr : 0 ≤ r) (hrs : r ≤ s)
    (C : ScheduleCut) : cutPower φ P r C ≤ cutPower φ P s C := by
  rw [cutPower_eq_phase_sum,cutPower_eq_phase_sum]
  apply add_le_add le_rfl
  exact Real.rpow_le_rpow (add_nonneg (add_nonneg (gapPrefix_nonnegative φ C.terminal) hP) hr)
    (add_le_add le_rfl hrs) nu_positive.le

def averagedCutPower (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)

def averagedPowerDecrease (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u v : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, (cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)-
    cutPower φ 1 κ (fullCut (Real.exp (v+t*Real.sqrt v)) h))

theorem averagedCutPower_integrable (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u : ℝ) :
    IntervalIntegrable (fun t : ℝ => cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)) volume 0 1 := by
  have hc : Continuous (fun t : ℝ => Real.exp (u+t*Real.sqrt u)) := by fun_prop
  exact cutObservable_intervalIntegrable (cutPower φ 1 κ) 0 h _ hc.measurable 0 1

theorem averagedPowerDecrease_eq_sub (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u v : ℝ) :
    averagedPowerDecrease φ κ h u v = averagedCutPower φ κ h u-averagedCutPower φ κ h v := by
  exact intervalIntegral.integral_sub (averagedCutPower_integrable φ κ h u) (averagedCutPower_integrable φ κ h v)

/-- Exact finite telescoping of the actual averaged threshold powers. -/
theorem averaged_power_telescoping (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, averagedPowerDecrease φ κ h (u i) (u (i+1))) =
      averagedCutPower φ κ h (u 0)-averagedCutPower φ κ h (u m) := by
  simp_rw [averagedPowerDecrease_eq_sub]
  exact sum_successive_differences (fun i => averagedCutPower φ κ h (u i)) m

theorem averagedCutPower_lower (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u L : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, L ≤ cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)) :
    L ≤ averagedCutPower φ κ h u := by
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) intervalIntegrable_const
    (averagedCutPower_integrable φ κ h u) hbound
  simpa [averagedCutPower] using hh

theorem averagedCutPower_upper (φ : ℝ → ℝ) (κ : ℝ) (h : List ℝ) (u U : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, cutPower φ 1 κ (fullCut (Real.exp (u+t*Real.sqrt u)) h) ≤ U) :
    averagedCutPower φ κ h u ≤ U := by
  have hh := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (averagedCutPower_integrable φ κ h u) intervalIntegrable_const hbound
  simpa [averagedCutPower] using hh

end
end StrongSilver
