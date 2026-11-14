-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Constants
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 5000000

/-- Distribution function of a uniform logarithmic threshold window. -/
def thresholdRamp (u s : ℝ) : ℝ := min 1 (max 0 ((s-u)/Real.sqrt u))

/-- Averaged inclusion weight between the lower and upper windows. -/
def smoothedBandWeight (u v s : ℝ) : ℝ := thresholdRamp v s-thresholdRamp u s

theorem thresholdRamp_bounds (u s : ℝ) : 0 ≤ thresholdRamp u s ∧ thresholdRamp u s ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem clamp_unit_abs_sub (a b : ℝ) : |min 1 (max 0 a)-min 1 (max 0 b)| ≤ |a-b| := by
  have hLip : LipschitzWith 1 (fun x : ℝ => min 1 (max 0 x)) :=
    (LipschitzWith.id.const_max 0).const_min 1
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hLip.dist_le_mul a b

theorem thresholdRamp_lipschitz {u : ℝ} (hu : 0 < u) (a b : ℝ) :
    |thresholdRamp u a-thresholdRamp u b| ≤ |a-b|/Real.sqrt u := by
  have hh := clamp_unit_abs_sub ((a-u)/Real.sqrt u) ((b-u)/Real.sqrt u)
  have he : (a-u)/Real.sqrt u-(b-u)/Real.sqrt u = (a-b)/Real.sqrt u := by ring
  rw [he,abs_div,abs_of_pos (Real.sqrt_pos.mpr hu)] at hh
  exact hh

theorem thresholdRamp_zero {u s : ℝ} (hu : 0 < u) (hs : s ≤ u) : thresholdRamp u s = 0 := by
  have hh : (s-u)/Real.sqrt u ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) (Real.sqrt_nonneg _)
  simp only [thresholdRamp,max_eq_left hh,min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

theorem thresholdRamp_one {u s : ℝ} (hu : 0 < u) (hs : u+Real.sqrt u ≤ s) : thresholdRamp u s = 1 := by
  have hh : 1 ≤ (s-u)/Real.sqrt u := (le_div_iff₀ (Real.sqrt_pos.mpr hu)).mpr (by linarith only [hs])
  have hh0 : 0 ≤ (s-u)/Real.sqrt u := zero_le_one.trans hh
  rw [thresholdRamp,max_eq_right hh0,min_eq_left hh]

/-- Separated smoothing windows give weights between zero and one. -/
theorem smoothedBandWeight_bounds {u v s : ℝ} (hu : 0 < u) (hv : 0 < v) (hsep : v+Real.sqrt v ≤ u) :
    0 ≤ smoothedBandWeight u v s ∧ smoothedBandWeight u v s ≤ 1 := by
  have hU := thresholdRamp_bounds u s
  have hV := thresholdRamp_bounds v s
  unfold smoothedBandWeight
  constructor
  · by_cases hs : s ≤ u
    · rw [thresholdRamp_zero hu hs]
      simpa only [sub_zero] using hV.1
    · have hs' : v+Real.sqrt v ≤ s := hsep.trans (le_of_not_ge hs)
      rw [thresholdRamp_one hv hs']
      exact sub_nonneg.mpr hU.2
  · linarith only [hV.2,hU.1]

theorem smoothedBandWeight_support {u v s : ℝ} (hu : 0 < u) (hv : 0 < v) (hsep : v+Real.sqrt v ≤ u)
    (hs : smoothedBandWeight u v s ≠ 0) : v < s ∧ s < u+Real.sqrt u := by
  constructor
  · by_contra hn
    have hLow : s ≤ v := le_of_not_gt hn
    have hVU : v ≤ u := by linarith only [hsep,Real.sqrt_nonneg v]
    exact hs (by rw [smoothedBandWeight,thresholdRamp_zero hv hLow,thresholdRamp_zero hu (hLow.trans hVU),sub_self])
  · by_contra hn
    have hHigh := le_of_not_gt hn
    have hLow : v+Real.sqrt v ≤ s := hsep.trans ((le_add_of_nonneg_right (Real.sqrt_nonneg u)).trans hHigh)
    exact hs (by rw [smoothedBandWeight,thresholdRamp_one hv hLow,thresholdRamp_one hu hHigh,sub_self])

theorem smoothedBandWeight_lipschitz {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (a b : ℝ) :
    |smoothedBandWeight u v a-smoothedBandWeight u v b| ≤
      (1/Real.sqrt u+1/Real.sqrt v)*|a-b| := by
  have hTri : |smoothedBandWeight u v a-smoothedBandWeight u v b| ≤
      |thresholdRamp v a-thresholdRamp v b|+|thresholdRamp u a-thresholdRamp u b| := by
    have he : smoothedBandWeight u v a-smoothedBandWeight u v b =
        (thresholdRamp v a-thresholdRamp v b)+(-(thresholdRamp u a-thresholdRamp u b)) := by
      unfold smoothedBandWeight
      ring
    rw [he]
    simpa only [abs_neg] using abs_add_le (thresholdRamp v a-thresholdRamp v b) (-(thresholdRamp u a-thresholdRamp u b))
  have hU := thresholdRamp_lipschitz hu a b
  have hV := thresholdRamp_lipschitz hv a b
  linear_combination hTri+hU+hV

end
end StrongSilver
