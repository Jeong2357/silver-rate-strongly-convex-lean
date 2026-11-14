-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandGoodUnitPower
import StrongSilver.SilverAveragingKernel

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 7000000

theorem throughSum_nonnegative (f : ScheduleTree → ℝ) (hf : ∀ t, 0 ≤ f t) (n : ℕ) (t : ScheduleTree) :
    0 ≤ throughSum f n t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih =>
    cases t with
    | leaf word => exact le_rfl
    | split l b r => exact add_nonneg (add_nonneg (hf _) (ih l)) (ih r)

theorem throughSum_mono_add (f : ScheduleTree → ℝ) (hf : ∀ t, 0 ≤ f t) (n k : ℕ) (t : ScheduleTree) :
    throughSum f n t ≤ throughSum f (n+k) t := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [show n+(k+1) = (n+k)+1 by omega,throughSum_succ]
    exact ih.trans (le_add_of_nonneg_right (levelSum_nonnegative f hf _ t))

def bandThreePrefixPower (B μ u : ℝ) (q : ScheduleNode) : ℝ :=
  (1-1/Real.sqrt 2)*bandGapPrefixPower B μ u (fourPhaseDepth u) q+
    bandGapPrefixPower B μ u (fourPhaseDepth u+1) q+
    (1/Real.sqrt 2)*bandGapPrefixPower B μ u (fourPhaseDepth u+2) q

/-- The three depth-prefix coefficients recover the actual S_d;
absolute gains and local curvature contribute only the stated errors. -/
theorem eventually_band_three_prefix_power : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ, ∀ q : ScheduleNode,
    BandSourceData κ B cap μ critical u h → q ∈ labels ((cartesian h).indexedTree 0 κ) →
    GoodThrough (bandGoodBool B μ u) (fourPhaseDepth u+3) (q.source.indexedTree q.start q.reserve) →
    bandThreePrefixPower B μ u q ≤ splitCoefficient*max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) q.source) 0+
      2*splitCoefficient*bandTolerance u*throughSum (fun t => |rootGain (cappedStep μ B) t|) (fourPhaseDepth u+2) q.source+
      96*splitCoefficient*Real.exp (-u/100)*(2:ℝ)^fourPhaseDepth u := by
  filter_upwards [eventually_band_good_prefix_power,eventually_gt_atTop (0:ℝ)] with u H hu
  intro κ B cap μ critical h q S hq hg
  let φ := cappedStep μ B
  let d := fourPhaseDepth u
  let s := 1/Real.sqrt 2
  let a := 1-s
  have hs0 : 0 ≤ s := (one_div_pos.mpr (zero_lt_one.trans sqrt_two_bounds.1)).le
  have hs1 : s ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) sqrt_two_bounds.1.le).trans_eq (by norm_num)
  have ha0 : 0 ≤ a := sub_nonneg.mpr hs1
  have hδ : 0 ≤ bandTolerance u := (Real.rpow_pos_of_pos hu _).le
  have hCf := split_coefficient_positive
  have h0 := H κ B cap μ critical h q d S hq (goodThrough_mono (by omega) hg)
  have h1 := H κ B cap μ critical h q (d+1) S hq (goodThrough_mono (by omega) hg)
  have h2 := H κ B cap μ critical h q (d+2) S hq (goodThrough_mono (by omega) hg)
  have h0s := mul_le_mul_of_nonneg_left h0 ha0
  have h2s := mul_le_mul_of_nonneg_left h2 hs0
  let f := fun t : ScheduleTree => |rootGain φ t|
  have hAbs0 := throughSum_mono_add f (fun _ => abs_nonneg _) d 2 q.source
  have hAbs1 := throughSum_mono_add f (fun _ => abs_nonneg _) (d+1) 1 q.source
  have hAbs0s := mul_le_mul_of_nonneg_left hAbs0 ha0
  have hAbsBudget : a*throughSum f d q.source+throughSum f (d+1) q.source+s*throughSum f (d+2) q.source ≤
      2*throughSum f (d+2) q.source := by
    dsimp only [a]
    linear_combination hAbs0s+hAbs1
  have hAbsScale := mul_le_mul_of_nonneg_left hAbsBudget (mul_nonneg hCf.le hδ)
  have hPow : a*(2:ℝ)^d+(2:ℝ)^(d+1)+s*(2:ℝ)^(d+2) ≤ 6*(2:ℝ)^d := by
    have hh := mul_le_mul_of_nonneg_right hs1 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)
    dsimp only [a]
    rw [pow_succ,show d+2 = (d+1)+1 by omega,pow_succ,pow_succ]
    nlinarith only [hh]
  have hPowScale := mul_le_mul_of_nonneg_left hPow (show 0 ≤ 16*splitCoefficient*Real.exp (-u/100) by positivity)
  have hGain := silverDepthGain_three_windows φ d q.source
  have hMax := mul_le_mul_of_nonneg_left (le_max_left (silverDepthGain φ d q.source) (0:ℝ)) hCf.le
  dsimp only [bandThreePrefixPower,φ,d,s,a,f] at h0s h1 h2s hAbsScale hPowScale hGain hMax ⊢
  linear_combination h0s+h1+h2s+hAbsScale+hPowScale-splitCoefficient*hGain+hMax

end
end StrongSilver
