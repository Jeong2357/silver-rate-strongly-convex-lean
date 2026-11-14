-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPositiveGainBudget
import StrongSilver.PositionedWindowSums

namespace StrongSilver
open ScheduleTree Real
noncomputable section
set_option maxHeartbeats 3600000

def protectedBandHigh (u : ℝ) : ℝ := outerBandHigh u-3*visibilitySpacing

/-- On this actual band, eligibility is automatic for the protected
height window. Arbitrary reserve-dependent sums retain every occurrence. -/
theorem band_protected_window_sum (κ B μ u : ℝ) (h : List ℝ) (F : ScheduleTree × ℝ → ℝ) :
    ((bandProtectedNodes κ B μ u h).map fun q => F (q.node.source,q.node.reserve)).sum =
      ((nodesInHeightWindow (cappedStep μ B) (bandPad u) κ (outerBandLow u) (protectedBandHigh u) (cartesian h)).map F).sum := by
  classical
  rw [← positioned_window_sum]
  unfold bandProtectedNodes protectedWindowNodes
  rw [list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro q hq
  by_cases hp : bandPad u < cappedStep μ B q.node.pivot
  · have he (hw : outerBandLow u < parentedHeight (cappedStep μ B) (bandPad u) q ∧
        parentedHeight (cappedStep μ B) (bandPad u) q ≤ protectedBandHigh u) :
        bandEligible μ B u q.node.pivotIndex q.node.pivot = true := by
      apply decide_eq_true
      exact ⟨hp,hw.1.le,by change parentedHeight (cappedStep μ B) (bandPad u) q ≤ outerBandHigh u; dsimp only [protectedBandHigh] at hw; linarith only [hw.2,visibilitySpacing_positive]⟩
    by_cases hw : outerBandLow u < parentedHeight (cappedStep μ B) (bandPad u) q ∧
        parentedHeight (cappedStep μ B) (bandPad u) q ≤ protectedBandHigh u
    · have hhi : parentedHeight (cappedStep μ B) (bandPad u) q+3*visibilitySpacing ≤ outerBandHigh u := by
        dsimp only [protectedBandHigh] at hw
        linarith only [hw.2]
      simp only [hp,he hw,hw.1,hw.2,hhi,and_self,decide_true,↓reduceIte]
    · have hcond : ¬ (bandPad u < cappedStep μ B q.node.pivot ∧
          bandEligible μ B u q.node.pivotIndex q.node.pivot = true ∧ outerBandLow u < parentedHeight (cappedStep μ B) (bandPad u) q ∧
          parentedHeight (cappedStep μ B) (bandPad u) q+3*visibilitySpacing ≤ outerBandHigh u) := by
        intro hh
        apply hw
        exact ⟨hh.2.2.1,by dsimp only [protectedBandHigh]; linarith only [hh.2.2.2]⟩
      rw [decide_eq_false hcond]
      simp only [Bool.false_eq_true,↓reduceIte,hp,true_and,hw]
  · simp only [hp,false_and,decide_false,Bool.false_eq_true,↓reduceIte]

end
end StrongSilver
