-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandEligibleUpper
import StrongSilver.CappedPivotMoments
import StrongSilver.ParentedScheduleNodes

namespace StrongSilver
open Real Filter ScheduleTree
noncomputable section
set_option maxHeartbeats 4800000

def bandPivotWeight (B μ u b : ℝ) : ℝ :=
  if bandEligible μ B u 0 b then Real.exp (nu*Real.log (cappedStep μ B b-bandPad u)) else 0

theorem bandPivotWeight_nonnegative (B μ u b : ℝ) : 0 ≤ bandPivotWeight B μ u b := by
  unfold bandPivotWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The total transformed weight in the outer band is O(W u), with
an absolute constant, for the original word including repeated pivots. -/
theorem eventually_band_word_weight_budget : ∀ᶠ u : ℝ in atTop,
    ∀ B cap μ : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    (h.map (bandPivotWeight B μ u)).sum ≤ 4*weightedCount h cap*u := by
  filter_upwards [eventually_eligible_band_step,eventually_eligible_band_step_upper,eventually_ge_atTop (1:ℝ)]
    with u hstep hupper hu
  intro B cap μ h hB hBcap hU hμ hμB
  let A := Real.exp ((999:ℝ)/1000*u)
  let V := Real.exp ((1001:ℝ)/1000*u)
  let T := min B V
  have hA : 0 < A := Real.exp_pos _
  have hV : 0 < V := Real.exp_pos _
  have hT : 0 < T := lt_min (zero_lt_one.trans hB) hV
  have hW := weightedCount_nonneg h cap
  have hP : 0 ≤ bandPad u := (Real.exp_pos _).le
  have heligible (b : ℝ) (hb : bandEligible μ B u 0 b = true) : A ≤ b ∧ b ≤ T ∧ 0 < b := by
    obtain ⟨hb0,hlo,hhi,_⟩ := hstep B μ b 0 hB hU hμ hμB hb
    have hAb := Real.exp_le_exp.mpr hlo
    have hbV := Real.exp_le_exp.mpr hhi
    rw [Real.exp_log hb0] at hAb hbV
    exact ⟨hAb,le_min (hupper B μ b 0 hB hU hμ hμB hb) hbV,hb0⟩
  by_cases hAT : A ≤ T
  · have hnonneg (b : ℝ) : 0 ≤ cappedPowerAbove A T b := by
      unfold cappedPowerAbove
      split_ifs with hb
      · exact (Real.rpow_pos_of_pos (lt_min (hA.trans_le hb) hT) nu).le
      · exact le_rfl
    have hpoint : ∀ b ∈ h, bandPivotWeight B μ u b ≤ 2*cappedPowerAbove A T b := by
      intro b hb
      unfold bandPivotWeight
      by_cases he : bandEligible μ B u 0 b = true
      · rw [if_pos he]
        obtain ⟨hAb,hbT,hb0⟩ := heligible b he
        have hφ : 0 < cappedStep μ B b-bandPad u := sub_pos.mpr (of_decide_eq_true he).1
        have hw := capped_pivot_power_le_two hμ hμB hb0 (hbT.trans (min_le_left _ _)) hP hφ.le
        have hweight : Real.exp (nu*Real.log (cappedStep μ B b-bandPad u)) = (cappedStep μ B b-bandPad u)^nu := by
          rw [Real.rpow_def_of_pos hφ,mul_comm]
        rw [hweight,cappedPowerAbove,if_pos hAb,min_eq_left hbT]
        exact hw
      · rw [if_neg he]
        exact mul_nonneg (by norm_num) (hnonneg b)
    have hsum := List.sum_le_sum hpoint
    rw [List.sum_map_mul_left] at hsum
    have hmoment := powerMoment_log_bound hA hAT ((min_le_left B V).trans hBcap) h
    have hlog : Real.log (T/A) ≤ u/500 := by
      rw [Real.log_div hT.ne' hA.ne']
      have ht := Real.log_le_log hT (min_le_right B V)
      dsimp only [A,V] at *
      rw [Real.log_exp] at ht ⊢
      linarith only [ht]
    have hlast : 2*(weightedCount h cap*(1+Real.log (T/A))) ≤ 4*weightedCount h cap*u := by
      have hlin : 1+Real.log (T/A) ≤ 2*u := by linarith only [hlog,hu]
      have hh := mul_le_mul_of_nonneg_left hlin hW
      nlinarith only [hh]
    exact hsum.trans ((mul_le_mul_of_nonneg_left hmoment (by norm_num : (0:ℝ) ≤ 2)).trans hlast)
  · have hz : (h.map (bandPivotWeight B μ u)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
      apply if_neg
      intro he
      have hh := heligible b he
      exact hAT (hh.1.trans hh.2.1)
    rw [hz]
    positivity

theorem parentedPivotWeight_le_word (w : ℝ → ℝ) (hw : ∀ b, 0 ≤ w b) (κ : ℝ) (t : ScheduleTree) :
    ((parentedNodes 0 κ none t).map fun q => w q.node.pivot).sum ≤ (t.word.map w).sum := by
  have he := congrArg (fun qs : List ScheduleNode => (qs.map fun q => w q.pivot).sum)
    (parentedNodes_erase 0 κ none t)
  simp only [List.map_map,Function.comp_def] at he
  exact he.trans_le (indexedTree_pivot_weight_le_word w hw 0 κ t)

theorem eventually_band_node_weight_budget : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    ((parentedNodes 0 κ none (cartesian h)).map fun q => bandPivotWeight B μ u q.node.pivot).sum ≤
      4*weightedCount h cap*u := by
  filter_upwards [eventually_band_word_weight_budget] with u H
  intro κ B cap μ h hB hcap hU hμ hμB
  have hh := parentedPivotWeight_le_word (bandPivotWeight B μ u) (bandPivotWeight_nonnegative B μ u) κ (cartesian h)
  rw [cartesian_word] at hh
  exact hh.trans (H B cap μ h hB hcap hU hμ hμB)

end
end StrongSilver
