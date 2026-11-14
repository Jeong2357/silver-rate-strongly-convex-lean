-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2500000

theorem list_filter_prop_sum_eq {α : Type*} (p : α → Prop) [DecidablePred p] (F : α → ℝ) (xs : List α) :
    ((xs.filter fun x => decide (p x)).map F).sum = (xs.map fun x => if p x then F x else 0).sum := by
  rw [list_filter_sum_eq]
  congr 1
  apply List.map_congr_left
  intro x hx
  by_cases hp : p x
  · rw [decide_eq_true hp,if_pos hp]
    rfl
  · rw [decide_eq_false hp,if_neg hp]
    rfl

end
end StrongSilver
