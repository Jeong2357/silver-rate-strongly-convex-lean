-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandLinkedIncompleteBudget
import StrongSilver.RootCandidateIntegrability

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6400000

def candidateDepthBadIndicator (B μ u width : ℝ) (n : ℕ) (q : LinkedGap) (y : ℝ) : ℝ := by
  classical
  exact if GoodThrough (bandGoodBool B μ u) (n+2) (q.node.source.indexedTree q.node.start q.node.reserve) then 0 else
    1-rootCandidateBadIndicator B μ u width q y

def candidateDepthFailureObservable (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) : ℝ :=
  Real.exp (nu*y)*linkedDynamicObservable (candidateDepthBadIndicator B μ u width n) (cappedStep μ B) (bandPad u) 0 κ none none (cartesian h) y

theorem candidateDepthBadIndicator_measurable (B μ u width : ℝ) (n : ℕ) (q : LinkedGap) :
    Measurable (candidateDepthBadIndicator B μ u width n q) := by
  classical
  by_cases hd : GoodThrough (bandGoodBool B μ u) (n+2) (q.node.source.indexedTree q.node.start q.node.reserve)
  · have he : candidateDepthBadIndicator B μ u width n q = fun _ => (0:ℝ) := by
      funext y
      exact if_pos hd
    rw [he]
    exact measurable_const
  · have he : candidateDepthBadIndicator B μ u width n q = fun y => 1-rootCandidateBadIndicator B μ u width q y := by
      funext y
      exact if_neg hd
    rw [he]
    exact measurable_const.sub (rootCandidateBadIndicator_measurable B μ u width q)

theorem candidateDepthBadIndicator_abs_upper (B μ u width : ℝ) (n : ℕ) (q : LinkedGap) (y : ℝ) :
    |candidateDepthBadIndicator B μ u width n q y| ≤ 1 := by
  classical
  unfold candidateDepthBadIndicator rootCandidateBadIndicator
  split_ifs <;> norm_num

theorem candidateDepthFailureObservable_integrable (κ B μ u width a b : ℝ) (n : ℕ) (h : List ℝ) :
    IntervalIntegrable (candidateDepthFailureObservable κ B μ u width n h) volume a b := by
  have hi := linkedDynamicObservable_integrable (candidateDepthBadIndicator B μ u width n)
    (candidateDepthBadIndicator_measurable B μ u width n) (candidateDepthBadIndicator_abs_upper B μ u width n)
    (cappedStep μ B) (bandPad u) 0 κ none none (cartesian h) a b
  exact hi.continuousOn_mul (by fun_prop)

theorem candidateDepthFailureObservable_upper (κ B μ u width : ℝ) (n : ℕ) (h : List ℝ) (y : ℝ) :
    candidateDepthFailureObservable κ B μ u width n h y ≤ linkedIncompleteObservable κ B μ u n h y := by
  classical
  unfold candidateDepthFailureObservable linkedDynamicObservable linkedIncompleteObservable
  rw [← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro q hq
  unfold candidateDepthBadIndicator
  by_cases hd : GoodThrough (bandGoodBool B μ u) (n+2) (q.node.source.indexedTree q.node.start q.node.reserve)
  · simp only [if_pos hd,hd,not_true_eq_false,and_false,↓reduceIte,mul_zero,le_refl]
  · rw [if_neg hd]
    by_cases hc : BandRootCandidate B μ u width q y
    · have hr := hc.1
      simp [rootCandidateBadIndicator,hc,hr,hd]
    · simp only [rootCandidateBadIndicator,if_neg hc,sub_self,mul_zero]
      split_ifs <;> positivity

/-- The actual S(y) roots failing the complete-depth condition cost
O(W u^(9/10) 2^d), with no unproved depth budget retained. -/
theorem eventually_band_candidate_depth_failures : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b width : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, candidateDepthFailureObservable κ B μ u width (fourPhaseDepth u+1) h y) ≤
      C*weightedCount h cap*u^((9:ℝ)/10)*(2:ℝ)^fourPhaseDepth u := by
  obtain ⟨C,hC,H⟩ := eventually_band_linked_incomplete_budget
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with u hBudget
  intro κ B cap μ critical a b width h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hEq : linkedIncompleteObservable κ B μ u (fourPhaseDepth u+1) h = fun y => incompleteVisibleTotal
      (bandGoodBool B μ u) (nodePaddedHeight (cappedStep μ B) (bandPad u)) nu (fourPhaseDepth u+1) none ((cartesian h).indexedTree 0 κ) y := by
    funext y
    exact linkedIncompleteObservable_eq _ h hB hμ0 hμB
  have hInt : IntervalIntegrable (linkedIncompleteObservable κ B μ u (fourPhaseDepth u+1) h) volume a b := by
    rw [hEq]
    exact incompleteVisibleTotal_integrable _ _ _ _ _ _ _ _
  have hI := intervalIntegral.integral_mono_on hab
    (candidateDepthFailureObservable_integrable κ B μ u width a b (fourPhaseDepth u+1) h) hInt
    (fun y _ => candidateDepthFailureObservable_upper κ B μ u width (fourPhaseDepth u+1) h y)
  exact hI.trans (hBudget κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW)

end
end StrongSilver
