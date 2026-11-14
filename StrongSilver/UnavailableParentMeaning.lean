-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandParentExclusions

namespace StrongSilver
open ScheduleTree Real
noncomputable section
set_option maxHeartbeats 5000000

theorem missing_indicator_of_bad_actual_child (G : ScheduleNode → Bool) {p c : ScheduleNode}
    (he : ScheduleChild p c) (hp : G p = true) (hc : G c ≠ true) :
    missingGoodChildIndicator G p = 1 := by
  obtain ⟨l,r,b,hs,hl | hr⟩ := he
  · have hEq : c = (⟨p.start,l,0⟩ : ScheduleNode) := by
      cases c
      simp_all
    have hMissing : ¬ (G ⟨p.start,l,0⟩ = true ∧ G ⟨p.start+l.word.length+1,r,p.reserve⟩ = true) := by
      intro hh
      exact hc (hEq ▸ hh.1)
    unfold missingGoodChildIndicator missingGoodChildWeight
    rw [hs]
    change (if G p = true ∧ ¬ (G ⟨p.start,l,0⟩ = true ∧ G ⟨p.start+l.word.length+1,r,p.reserve⟩ = true) then (1:ℝ) else 0) = 1
    exact if_pos ⟨hp,hMissing⟩
  · have hEq : c = (⟨p.start+l.word.length+1,r,p.reserve⟩ : ScheduleNode) := by
      cases c
      simp_all
    have hMissing : ¬ (G ⟨p.start,l,0⟩ = true ∧ G ⟨p.start+l.word.length+1,r,p.reserve⟩ = true) := by
      intro hh
      exact hc (hEq ▸ hh.2)
    unfold missingGoodChildIndicator missingGoodChildWeight
    rw [hs]
    change (if G p = true ∧ ¬ (G ⟨p.start,l,0⟩ = true ∧ G ⟨p.start+l.word.length+1,r,p.reserve⟩ = true) then (1:ℝ) else 0) = 1
    exact if_pos ⟨hp,hMissing⟩

/-- A protected parent or actual child failing goodness is covered by
the same unavailable-parent indicator used in the integral budget. -/
theorem unavailable_parent_covers_bad_edge {B μ u : ℝ} {p c : ScheduleNode}
    (he : ScheduleChild p c) (hpred : bandProtectedPredicate B μ u p)
    (hbad : ¬ (bandGoodBool B μ u p = true ∧ bandGoodBool B μ u c = true)) :
    1 ≤ bandUnavailableIndicator B μ u p := by
  classical
  by_cases hp : bandGoodBool B μ u p = true
  · have hc : bandGoodBool B μ u c ≠ true := fun hh => hbad ⟨hp,hh⟩
    have hMissing := missing_indicator_of_bad_actual_child (bandGoodBool B μ u) he hp hc
    have hBad := bandBadIndicator_nonnegative B μ u p
    unfold bandUnavailableIndicator
    rw [hMissing]
    linarith only [hBad]
  · have hnotGood : ¬ PaddedGood (cappedStep μ B) (bandPad u) p.reserve (bandTolerance u) p.source :=
      fun hh => hp ((bandGoodBool_iff B μ u p).mpr ⟨hh,hpred⟩)
    have hBad : bandBadIndicator B μ u p = 1 := by
      unfold bandBadIndicator
      exact if_pos ⟨hpred,hnotGood⟩
    have hMissing := missingGoodChildIndicator_nonnegative (bandGoodBool B μ u) p
    unfold bandUnavailableIndicator
    rw [hBad]
    linarith only [hMissing]

end
end StrongSilver
