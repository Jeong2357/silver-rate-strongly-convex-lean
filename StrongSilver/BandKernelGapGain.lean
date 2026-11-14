-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandThreePrefixPower
import StrongSilver.BandSelectedBoundary

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8500000

def bandKernelGapPower (B μ u y : ℝ) (q : ScheduleNode) : ℝ :=
  (1-1/Real.sqrt 2)*bandGapWindowPower B μ u y (fourPhaseDepth u) q+
    bandGapWindowPower B μ u y (fourPhaseDepth u+1) q+
    (1/Real.sqrt 2)*bandGapWindowPower B μ u y (fourPhaseDepth u+2) q

theorem bandDepthBoundaryCost_nonnegative (B μ u y : ℝ) (k : ℕ) (q : ScheduleNode) :
    0 ≤ bandDepthBoundaryCost B μ u y k q := by
  classical
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

/-- The actual height kernel on an available gap is controlled by
its S_d gain, source absolute gains, an exponential pad error and
three explicit boundary-strip costs. -/
theorem eventually_band_kernel_gap_gain : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical y : ℝ, ∀ h : List ℝ, ∀ R : List CutPhase,
    BandSourceData κ B cap μ critical u h → ∀ q r : LinkedGap,
    (q,r) ∈ bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h R y →
    bandKernelGapPower B μ u y q.node ≤ splitCoefficient*max (silverDepthGain (cappedStep μ B) (fourPhaseDepth u) q.node.source) 0+
      2*splitCoefficient*bandTolerance u*throughSum (fun t => |rootGain (cappedStep μ B) t|) (fourPhaseDepth u+2) q.node.source+
      96*splitCoefficient*Real.exp (-u/100)*(2:ℝ)^fourPhaseDepth u+
      bandDepthBoundaryCost B μ u y (fourPhaseDepth u) q.node+
      bandDepthBoundaryCost B μ u y (fourPhaseDepth u+1) q.node+
      bandDepthBoundaryCost B μ u y (fourPhaseDepth u+2) q.node := by
  filter_upwards [eventually_band_three_prefix_power,eventually_band_gap_depth_comparison] with u hPrefix hWindow
  intro κ B cap μ critical y h R S q r hp
  let d := fourPhaseDepth u
  let s := 1/Real.sqrt 2
  let a := 1-s
  have hs0 : 0 ≤ s := (one_div_pos.mpr (zero_lt_one.trans sqrt_two_bounds.1)).le
  have hs1 : s ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) sqrt_two_bounds.1.le).trans_eq (by norm_num)
  have ha0 : 0 ≤ a := sub_nonneg.mpr hs1
  have ha1 : a ≤ 1 := by dsimp only [a]; linarith only [hs0]
  have hPre := bandPostReservedPairs_pre hp
  have hSub := bandPostReservedPairs_adjacent_sublist κ B μ u (Real.log u/200) (d+1) h R y
  have hq := (adjacentOccurrences_members (hSub.subset hp)).1
  have hMem := linkedFrontier_internal_mem hq (bandGoodBool_internal hPre.1.1.1)
  have h0 := mul_le_mul_of_nonneg_left (hWindow κ B cap μ critical y h R S q r hp d (by omega)) ha0
  have h1 := hWindow κ B cap μ critical y h R S q r hp (d+1) (by omega)
  have h2 := mul_le_mul_of_nonneg_left (hWindow κ B cap μ critical y h R S q r hp (d+2) (by omega)) hs0
  have hP := hPrefix κ B cap μ critical h q.node S hMem hPre.2.2
  have hB0 := mul_le_mul_of_nonneg_right ha1 (bandDepthBoundaryCost_nonnegative B μ u y d q.node)
  have hB2 := mul_le_mul_of_nonneg_right hs1 (bandDepthBoundaryCost_nonnegative B μ u y (d+2) q.node)
  dsimp only [bandKernelGapPower,bandThreePrefixPower,d,s,a] at h0 h1 h2 hP hB0 hB2 ⊢
  linear_combination h0+h1+h2+hP+hB0+hB2

end
end StrongSilver
