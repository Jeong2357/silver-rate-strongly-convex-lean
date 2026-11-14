-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FrozenFrontierCount
import StrongSilver.LinkedObservable
import StrongSilver.FiniteFilteredSums
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6200000

theorem list_filter_length_real {α : Type*} (p : α → Bool) (xs : List α) :
    ((xs.filter p).length:ℝ) = (xs.map fun x => if p x then (1:ℝ) else 0).sum := by
  simpa only [List.map_const',List.sum_replicate,nsmul_eq_mul,mul_one] using list_filter_sum_eq p (fun _ => 1) xs

def frozenFrontierObservable (φ : ℝ → ℝ) (P κ v top : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  Real.exp (v*y)*(((linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)).filter fun q =>
    @decide (ParentedScheduleNode.parentAbove φ (P+Real.exp top) q.parent) (Classical.propDecidable _)).length:ℝ)

theorem frozenFrontierObservable_integrable (φ : ℝ → ℝ) (P κ v top a b : ℝ) (h : List ℝ) :
    IntervalIntegrable (frozenFrontierObservable φ P κ v top h) volume a b := by
  classical
  let F := fun q : LinkedGap => if ParentedScheduleNode.parentAbove φ (P+Real.exp top) q.parent then (1:ℝ) else 0
  have hBase := linkedObservable_integrable F φ 0 κ none none (cartesian h)
    (fun y => P+Real.exp y) (by fun_prop) a b
  have hWeighted := hBase.continuousOn_mul (show ContinuousOn (fun y : ℝ => Real.exp (v*y)) (uIcc a b) by fun_prop)
  have he : frozenFrontierObservable φ P κ v top h = fun y =>
      Real.exp (v*y)*linkedObservable F φ 0 κ none none (cartesian h) (P+Real.exp y) := by
    funext y
    unfold frozenFrontierObservable
    rw [list_filter_length_real]
    simp only [decide_eq_true_eq,linkedObservable,F]
  rw [he]
  exact hWeighted

/-- The weighted integral of gaps already present at the top cut is
paid by the top frontier size, independently of the lower endpoint. -/
theorem frozenFrontierObservable_integral_upper (φ : ℝ → ℝ) (hφ : Monotone φ)
    (P κ v a b : ℝ) (h : List ℝ) (hv : 0 ≤ v) (hab : a ≤ b) :
    v*(∫ y in a..b, frozenFrontierObservable φ P κ v b h y) ≤
      Real.exp (v*b)*((indexedFrontier φ (P+Real.exp b) 0 κ (cartesian h)).length:ℝ) := by
  let N : ℝ := (indexedFrontier φ (P+Real.exp b) 0 κ (cartesian h)).length
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hEach (y : ℝ) (hy : y ∈ Icc a b) : frozenFrontierObservable φ P κ v b h y ≤ Real.exp (v*y)*N := by
    have hs : P+Real.exp y ≤ P+Real.exp b := add_le_add (le_refl P) (Real.exp_le_exp.mpr hy.2)
    have hn := frozen_frontier_count φ hφ hs 0 κ none none (cartesian h) (cartesian_valid h)
    have hnR : (((linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)).filter fun q =>
      @decide (ParentedScheduleNode.parentAbove φ (P+Real.exp b) q.parent) (Classical.propDecidable _)).length:ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn
    exact mul_le_mul_of_nonneg_left hnR (Real.exp_pos _).le
  have hExpInt : IntervalIntegrable (fun y : ℝ => Real.exp (v*y)) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b
  have hInt := intervalIntegral.integral_mono_on hab
    (frozenFrontierObservable_integrable φ P κ v b a b h) (hExpInt.mul_const N) hEach
  rw [intervalIntegral.integral_mul_const] at hInt
  have hScale := mul_le_mul_of_nonneg_left hInt hv
  have hExp := scaled_exponential_integral v a b
  have hNonneg := mul_nonneg (Real.exp_pos (v*a)).le hN
  dsimp only [N] at hScale hNonneg ⊢
  linear_combination hScale+N*hExp+hNonneg

end
end StrongSilver
