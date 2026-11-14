-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LongVisibleNodes

namespace StrongSilver
open ScheduleTree ParentedScheduleNode Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4600000

local instance (φ : ℝ → ℝ) (s : ℝ) (q : ParentedScheduleNode) : Decidable (q.Visible φ s) := Classical.propDecidable _
local instance (φ : ℝ → ℝ) (P s : ℝ) (q : ParentedScheduleNode) : Decidable (parentWindowClear φ P s q) := Classical.propDecidable _

private theorem sum_filter_map_eq {α : Type*} (p : α → Bool) (f : α → ℝ) (xs : List α) :
    ((xs.filter p).map f).sum = (xs.map fun x => if p x then f x else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x = true
    · simp only [List.filter_cons,hx,↓reduceIte,List.map_cons,List.sum_cons,ih]
    · simp only [List.filter_cons,Bool.eq_false_iff.mpr hx,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons,zero_add,ih]

/-- The weighted fixed-width interval sum is dominated pointwise by
the actual visible-root sum. Every list is an occurrence list. -/
theorem long_visibility_kernel_le (φ : ℝ → ℝ) {P κ a b s : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (price : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) (y : ℝ) :
    visibilityKernelSum (parentedHeight φ P) (fun q => visibleNodeScore φ P price eligible q.node) nu s
      (longVisibleNodes φ P κ a b s eligible t) y ≤
      Real.exp (nu*y)*(((parentedNodes 0 κ none t).filter fun q => decide (q.Visible φ (P+Real.exp y))).map
        fun q => visibleNodeScore φ P price eligible q.node).sum := by
  unfold visibilityKernelSum longVisibleNodes
  rw [sum_filter_map_eq,sum_filter_map_eq,← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro q hq
  have hScore := visibleNodeScore_nonnegative φ hP price eligible q.node (parentedNodes_reserve_nonnegative hκ hq)
  have hNonneg : 0 ≤ Real.exp (nu*y)*(if decide (q.Visible φ (P+Real.exp y)) then visibleNodeScore φ P price eligible q.node else 0) := by
    apply mul_nonneg (Real.exp_pos _).le
    split_ifs
    · exact hScore
    · exact le_rfl
  split
  · rename_i hsel
    have hmem : q ∈ longVisibleNodes φ P κ a b s eligible t := List.mem_filter.mpr ⟨hq,hsel⟩
    rw [visibilityWindowKernel_eq nu s (parentedHeight φ P q) y hs]
    by_cases hy : parentedHeight φ P q+s ≤ y ∧ y < parentedHeight φ P q+2*s
    · have hv := longVisibleNodes_visible hs hmem hy
      rw [if_pos hy,decide_eq_true hv,if_pos rfl]
      ring_nf
      exact le_rfl
    · rw [if_neg hy,mul_zero]
      exact hNonneg
  · exact hNonneg

/-- Integrated weighted visibility on actual Cartesian gaps. The
right-hand side is the same full-cut savings and positive-sum deficit
which occur in the proved band integral estimate. -/
theorem long_visibility_integral_budget (φ : ℝ → ℝ) (hφ : Monotone φ) {P κ a b s : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hs : 0 ≤ s) (hab : a ≤ b) (hzero : φ 0 ≤ 0)
    (price : ℝ) (eligible : ℕ → ℝ → Bool) (t : ScheduleTree) (hc : t.Cartesian)
    (hInt : IntervalIntegrable (fun y => Real.exp (nu*y)*
      (totalGapSavingsMaximum φ P κ price eligible (heightCut φ P y t.word)+
        (cutLogProduct (positivePartStep φ) P κ (heightCut φ P y t.word)-cutLogProduct φ P κ (heightCut φ P y t.word)))) volume a b) :
    visibilityWindowFactor nu s*((longVisibleNodes φ P κ a b s eligible t).map fun q =>
      Real.exp (nu*parentedHeight φ P q)*visibleNodeScore φ P price eligible q.node).sum ≤
      nu*(∫ y in a..b, Real.exp (nu*y)*
        (totalGapSavingsMaximum φ P κ price eligible (heightCut φ P y t.word)+
          (cutLogProduct (positivePartStep φ) P κ (heightCut φ P y t.word)-cutLogProduct φ P κ (heightCut φ P y t.word)))) := by
  apply finite_visibility_integral_budget (parentedHeight φ P) (fun q => visibleNodeScore φ P price eligible q.node)
    nu s a b (longVisibleNodes φ P κ a b s eligible t) _ hab nu_positive.le hs
    (fun _ hq => longVisibleNodes_window hq) hInt
  intro y hy
  exact (long_visibility_kernel_le φ hP hκ hs price eligible t y).trans
    (mul_le_mul_of_nonneg_left (visible_gap_budget φ hφ hP hκ hzero price eligible t hc) (Real.exp_pos _).le)

end
end StrongSilver
