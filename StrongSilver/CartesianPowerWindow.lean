-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCutStepFunction

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2800000

/-- Exact power telescoping over a height window, including all ties
with multiplicity and the terminal reserve. -/
theorem cartesian_power_window_difference {P κ : ℝ} (hP : 0 < P)
    (t : ScheduleTree) (hc : t.Cartesian) (a b : ℝ) (hab : a ≤ b) :
    ((t.paddedEvents P κ).map fun q =>
      if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedRootDecrease id P q.2 q.1 else 0).sum =
      cutPower id P κ (fullCut (P+Real.exp b) t.word)-cutPower id P κ (fullCut (P+Real.exp a) t.word) := by
  have hh := finite_jump_difference (paddedHeight P) (fun q => paddedRootDecrease id P q.2 q.1)
    ((gapPrefix id t.word+P+κ)^nu) a b (t.paddedEvents P κ) hab
  rw [← full_cut_power_stepObservable hP t hc b,← full_cut_power_stepObservable hP t hc a] at hh
  exact hh.symm

end
end StrongSilver.ScheduleTree
