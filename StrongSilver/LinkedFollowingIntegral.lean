-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingSum
import StrongSilver.SelectedNodeIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5400000

def linkedFollowingObservable (φ : ℝ → ℝ) (P κ v : ℝ) (F : ScheduleNode → ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  ((linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)).map fun q =>
    Real.exp (v*y)*optionalNodeCharge F q.following).sum

theorem linkedFollowingObservable_eq (φ : ℝ → ℝ) (hφ : Monotone φ) (P κ v : ℝ)
    (F : ScheduleNode → ℝ) (h : List ℝ) (y : ℝ) :
    linkedFollowingObservable φ P κ v F h y =
      selectedNodeObservable φ P v F (labels ((cartesian h).indexedTree 0 κ)) y := by
  unfold linkedFollowingObservable selectedNodeObservable
  rw [List.sum_map_mul_left,linkedFrontier_following_sum φ hφ (P+Real.exp y) F 0 κ none none (cartesian h) (cartesian_valid h)]
  simp only [optionalNodeCharge,add_zero]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro q _
  split_ifs <;> simp

theorem linkedFollowingObservable_integrable (φ : ℝ → ℝ) (hφ : Monotone φ) (P κ v a b : ℝ)
    (F : ScheduleNode → ℝ) (h : List ℝ) :
    IntervalIntegrable (linkedFollowingObservable φ P κ v F h) volume a b := by
  have he : linkedFollowingObservable φ P κ v F h = selectedNodeObservable φ P v F (labels ((cartesian h).indexedTree 0 κ)) := by
    funext y
    exact linkedFollowingObservable_eq φ hφ P κ v F h y
  rw [he]
  exact selectedNodeObservable_integrable φ P v a b F _

/-- Weighted cutoff cost of any nonnegative following-pivot charge,
paid by the corresponding indexed original vertex weights. -/
theorem linkedFollowingObservable_integral_upper (φ : ℝ → ℝ) (hφ : Monotone φ) (P κ v a b : ℝ)
    (F : ScheduleNode → ℝ) (h : List ℝ) (hv : 0 ≤ v) (hF : ∀ q, 0 ≤ F q) (hab : a ≤ b) :
    v*(∫ y in a..b, linkedFollowingObservable φ P κ v F h y) ≤
      ((labels ((cartesian h).indexedTree 0 κ)).map fun q => Real.exp (v*nodePaddedHeight φ P q)*F q).sum := by
  have he : linkedFollowingObservable φ P κ v F h = selectedNodeObservable φ P v F (labels ((cartesian h).indexedTree 0 κ)) := by
    funext y
    exact linkedFollowingObservable_eq φ hφ P κ v F h y
  rw [he]
  exact selectedNodeObservable_integral_upper φ P v a b F _ hv hF hab

end
end StrongSilver
