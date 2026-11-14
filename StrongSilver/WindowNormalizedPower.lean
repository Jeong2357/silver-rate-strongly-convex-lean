-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WindowRefinementSavings

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 3600000

def normalizedNodeExcess (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleNode) : ℝ :=
  nodeExcess φ P (q.source,q.reserve)/Real.exp (nu*nodePaddedHeight φ P q)

def normalizedNodeDecrease (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleNode) : ℝ :=
  paddedRootDecrease φ P q.reserve q.source/Real.exp (nu*nodePaddedHeight φ P q)

theorem normalized_node_identity (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleNode) :
    normalizedNodeDecrease φ P q = splitCoefficient*paddedRootGain φ P q.reserve q.source-normalizedNodeExcess φ P q := by
  unfold normalizedNodeDecrease normalizedNodeExcess nodeExcess nodePaddedHeight
  field_simp [Real.exp_ne_zero] <;> ring

/-- The normalized power sum of all vertices in an actual cutoff gap
is controlled by the finite gap refinement saving and its insertion
count, minus the complete nonnegative excess sum. -/
theorem window_normalized_power_bound {φ : ℝ → ℝ} (hφ : StrictMono φ) {P κ low A price : ℝ}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ P) (hA : 0 ≤ A) (hcut : φ A = P+Real.exp low)
    (start : ℕ) (t : ScheduleTree) (hc : t.Cartesian) (eligible : ℕ → ℝ → Bool)
    (hEligible : ∀ j : ℕ, ∀ b ∈ t.word, A < b → eligible j b = true) :
    ((labels (indexedHeightWindow φ P low start κ t)).map (normalizedNodeDecrease φ P)).sum ≤
      splitCoefficient*gapSavingsMaximum φ P κ price start t.word eligible+
      splitCoefficient*price*((indexedHeightWindow φ P low start κ t).numNodes:ℝ)-
      ((labels (indexedHeightWindow φ P low start κ t)).map (normalizedNodeExcess φ P)).sum := by
  have hgain := window_gain_le_gap_savings (price := price) hφ hP hκ hzero hA hcut start t hc eligible hEligible
  have hsum : ∀ qs : List ScheduleNode,
      (qs.map (normalizedNodeDecrease φ P)).sum = splitCoefficient*(qs.map fun q => paddedRootGain φ P q.reserve q.source).sum-
        (qs.map (normalizedNodeExcess φ P)).sum := by
    intro qs
    induction qs with
    | nil => simp
    | cons q qs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [normalized_node_identity]
      linear_combination ih
  rw [hsum]
  have hh := mul_le_mul_of_nonneg_left hgain split_coefficient_positive.le
  linear_combination hh

end
end StrongSilver
