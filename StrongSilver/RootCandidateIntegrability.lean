-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandRootCandidates

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5400000

theorem rootCandidateBadIndicator_abs_upper (B μ u width : ℝ) (q : LinkedGap) (y : ℝ) :
    |rootCandidateBadIndicator B μ u width q y| ≤ 1 := by
  classical
  unfold rootCandidateBadIndicator
  split_ifs <;> norm_num

theorem rootCandidateBadIndicator_measurable (B μ u width : ℝ) (q : LinkedGap) :
    Measurable (rootCandidateBadIndicator B μ u width q) := by
  classical
  cases hp : q.following with
  | none =>
    have he : rootCandidateBadIndicator B μ u width q = fun _ => (1:ℝ) := by
      funext y
      simp [rootCandidateBadIndicator,BandRootCandidate,hp]
    rw [he]
    exact measurable_const
  | some p =>
    by_cases hr : GoodLinkedRoot B μ u q
    · by_cases hg : bandGoodBool B μ u p = true
      · have he : rootCandidateBadIndicator B μ u width q = fun y =>
            if cappedStep μ B p.pivot ≤ bandPad u+Real.exp (y+width) then (0:ℝ) else 1 := by
          funext y
          simp only [rootCandidateBadIndicator,BandRootCandidate,hp,Option.some.injEq,exists_eq_left',hr,hg,true_and]
        rw [he]
        exact Measurable.ite ((isClosed_le continuous_const
          (continuous_const.add (Real.continuous_exp.comp (continuous_id.add continuous_const)))).measurableSet)
          measurable_const measurable_const
      · have he : rootCandidateBadIndicator B μ u width q = fun _ => (1:ℝ) := by
          funext y
          simp [rootCandidateBadIndicator,BandRootCandidate,hp,hg]
        rw [he]
        exact measurable_const
    · have he : rootCandidateBadIndicator B μ u width q = fun _ => (1:ℝ) := by
        funext y
        simp [rootCandidateBadIndicator,BandRootCandidate,hr]
      rw [he]
      exact measurable_const

theorem rootCandidateExclusionObservable_integrable (κ B μ u width a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (rootCandidateExclusionObservable κ B μ u width h) volume a b := by
  have hBase := linkedDynamicObservable_integrable (rootCandidateBadIndicator B μ u width)
    (rootCandidateBadIndicator_measurable B μ u width) (rootCandidateBadIndicator_abs_upper B μ u width)
    (cappedStep μ B) (bandPad u) 0 κ none none (cartesian h) a b
  exact hBase.continuousOn_mul (by fun_prop)

end
end StrongSilver
