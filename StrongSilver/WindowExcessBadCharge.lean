-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WindowNormalizedPower
import StrongSilver.PaddedNodeCharges
import StrongSilver.WindowBadCount
import StrongSilver.ActualParentMembership

namespace StrongSilver
open ScheduleTree BinaryForest
noncomputable section
set_option maxHeartbeats 4200000

/-- Every bad occurrence in an actual cutoff-height forest pays the
same normalized c delta^2 excess. This is the absorption term of
Section 4.6, with the original scalar excess and reserve. -/
theorem window_excess_bad_charge : ∃ c > 0,
    ∀ φ : ℝ → ℝ, ∀ P κ low δ : ℝ, ∀ start : ℕ, ∀ t : ScheduleTree,
    Monotone φ → 0 < P → 0 ≤ κ → φ 0 ≤ 0 → 0 ≤ δ → δ ≤ 1 → t.Cartesian →
    c*δ^2*(badNodeCount (rootGood (nodeBalancedBool φ P δ)) (indexedHeightWindow φ P low start κ t):ℝ) ≤
      ((labels (indexedHeightWindow φ P low start κ t)).map (normalizedNodeExcess φ P)).sum := by
  classical
  obtain ⟨c,hc,H⟩ := node_unbalanced_charge
  refine ⟨c,hc,?_⟩
  intro φ P κ low δ start t hφ hP hκ hzero hδ hδ1 ht
  rw [badNodeCount_real_eq_label_sum]
  have hpoint : ∀ q ∈ labels (indexedHeightWindow φ P low start κ t),
      c*δ^2*(if nodeBalancedBool φ P δ q then (0:ℝ) else 1) ≤ normalizedNodeExcess φ P q := by
    intro q hq
    have hqs := hq
    rw [indexed_height_window_labels φ hφ P low start κ t ht] at hqs
    obtain ⟨hOriginal,hsel⟩ := List.mem_filter.mp hqs
    have hroot := (of_decide_eq_true hsel).1
    have hres := indexedTree_reserve_nonnegative hκ hOriginal
    have hE := nodeExcess_nonnegative φ hP hres hzero q.source hroot
    have hw := Real.exp_pos (nu*nodePaddedHeight φ P q)
    by_cases hb : PaddedBalanced φ P q.reserve δ q.source
    · have hbool : nodeBalancedBool φ P δ q = true := decide_eq_true hb
      rw [hbool,if_pos rfl,mul_zero]
      exact div_nonneg hE hw.le
    · have hbool : nodeBalancedBool φ P δ q = false := decide_eq_false hb
      rw [hbool,if_neg Bool.false_ne_true,mul_one]
      apply (le_div_iff₀ hw).mpr
      have hh := H φ P q.reserve δ q.source hP hres hzero hroot hδ hδ1 hb
      dsimp only [nodePaddedHeight]
      linear_combination hh
  have hh := List.sum_le_sum hpoint
  rw [List.sum_map_mul_left] at hh
  exact hh

end
end StrongSilver
