-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LogarithmicCutoff

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

/-- The fixed band pad satisfies every working-phase exponent bound
throughout the common logarithmic window. -/
theorem band_pad_bounds {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u)
    (hlo : (999:ℝ)/1000*u ≤ Real.log A) (hhi : Real.log A ≤ (1001:ℝ)/1000*u)
    (hlog2 : Real.log 2 ≤ u/1000) :
    A^((49:ℝ)/50) ≤ Real.exp ((987:ℝ)/1000*u) ∧
      Real.exp ((987:ℝ)/1000*u) ≤ A^((199:ℝ)/200) ∧
      2*Real.exp ((987:ℝ)/1000*u) ≤ A := by
  have h1 : ((49:ℝ)/50)*Real.log A ≤ (987:ℝ)/1000*u := by nlinarith only [hhi,hu]
  have h2 : (987:ℝ)/1000*u ≤ ((199:ℝ)/200)*Real.log A := by nlinarith only [hlo,hu]
  have h3 : Real.log 2+(987:ℝ)/1000*u ≤ Real.log A := by nlinarith only [hlo,hlog2,hu]
  constructor
  · rw [Real.rpow_def_of_pos hA]
    exact Real.exp_le_exp.mpr (by nlinarith only [h1])
  constructor
  · rw [Real.rpow_def_of_pos hA]
    exact Real.exp_le_exp.mpr (by nlinarith only [h2])
  · have hh := Real.exp_le_exp.mpr h3
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2),Real.exp_log hA] at hh
    exact hh

/-- Every pivot in the enlarged band is still above A^.998 for every
cutoff A in that same window. -/
theorem band_selected_lower {A b u : ℝ} (hA : 0 < A) (hb : 0 < b) (hu : 0 ≤ u)
    (hblo : (999:ℝ)/1000*u ≤ Real.log b) (hAhi : Real.log A ≤ (1001:ℝ)/1000*u) :
    A^((499:ℝ)/500) ≤ b := by
  rw [Real.rpow_def_of_pos hA,← Real.exp_log hb]
  apply Real.exp_le_exp.mpr
  nlinarith only [hblo,hAhi,hu]

end
end StrongSilver
