-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrderedPositions
import Mathlib.Data.List.Pairwise

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1400000

theorem stepAt_nonnegative (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x) (i : ℕ) : 0 ≤ stepAt xs i := by
  by_cases hi : i < xs.length
  · rw [stepAt_eq hi]
    exact hx xs[i] (List.getElem_mem hi)
  · simp [stepAt,List.getElem?_eq_none (le_of_not_gt hi)]

theorem stepAt_le_bound {b : ℝ} (hb : 0 ≤ b) (xs : List ℝ) (hx : ∀ x ∈ xs, x ≤ b) (i : ℕ) : stepAt xs i ≤ b := by
  by_cases hi : i < xs.length
  · rw [stepAt_eq hi]
    exact hx xs[i] (List.getElem_mem hi)
  · simpa [stepAt,List.getElem?_eq_none (le_of_not_gt hi)] using hb

def refinementWeights (base : ℝ) (xs : List ℝ) : ℕ → ℝ
  | 0 => base
  | i+1 => stepAt xs i

@[simp] theorem refinementWeights_zero (b : ℝ) (xs : List ℝ) : refinementWeights b xs 0 = b := rfl

theorem refinementWeights_step (b : ℝ) (xs : List ℝ) {i : ℕ} (hi : i < xs.length) :
    refinementWeights b xs (i+1) = xs[i] := stepAt_eq hi

theorem refinementWeights_end (b : ℝ) (xs : List ℝ) : refinementWeights b xs (xs.length+1) = 0 := by
  simp [refinementWeights,stepAt]

theorem refinementWeights_nonnegative {b : ℝ} (hb : 0 ≤ b) (xs : List ℝ) (hx : ∀ x ∈ xs, 0 ≤ x) (i : ℕ) :
    0 ≤ refinementWeights b xs i := by
  cases i with
  | zero => exact hb
  | succ i => exact stepAt_nonnegative xs hx i

/-- Nonincreasing weights are extended by zero after the last insertion. -/
theorem refinementWeights_decreasing {b : ℝ} (hb : 0 ≤ b) (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x) (hbound : ∀ x ∈ xs, x ≤ b) (hs : xs.Pairwise (· ≥ ·)) (i : ℕ) :
    refinementWeights b xs (i+1) ≤ refinementWeights b xs i := by
  cases i with
  | zero => exact stepAt_le_bound hb xs hbound 0
  | succ i =>
    change stepAt xs (i+1) ≤ stepAt xs i
    by_cases hn : i+1 < xs.length
    · have hi : i < xs.length := by omega
      have hh := hs.rel_get_of_lt (a := ⟨i,hi⟩) (b := ⟨i+1,hn⟩) (Nat.lt_succ_self i)
      simpa only [stepAt_eq hi,stepAt_eq hn,List.get_eq_getElem] using hh
    · have hzero : stepAt xs (i+1) = 0 := by simp [stepAt,List.getElem?_eq_none (le_of_not_gt hn)]
      rw [hzero]
      exact stepAt_nonnegative xs hx i

end
end StrongSilver
