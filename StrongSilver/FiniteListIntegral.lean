-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace StrongSilver
open MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 3200000

theorem intervalIntegrable_list_sum (F : α → ℝ → ℝ) (xs : List α) (a b : ℝ)
    (hF : ∀ x ∈ xs, IntervalIntegrable (F x) volume a b) :
    IntervalIntegrable (fun y => (xs.map fun x => F x y).sum) volume a b := by
  induction xs with
  | nil => exact intervalIntegrable_const
  | cons x xs ih =>
    exact (hF x (List.mem_cons_self)).add (ih (fun z hz => hF z (List.mem_cons_of_mem x hz)))

theorem integral_list_sum (F : α → ℝ → ℝ) (xs : List α) (a b : ℝ)
    (hF : ∀ x ∈ xs, IntervalIntegrable (F x) volume a b) :
    (∫ y in a..b, (xs.map fun x => F x y).sum) = (xs.map fun x => ∫ y in a..b, F x y).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hTail := fun z hz => hF z (List.mem_cons_of_mem x hz)
    change (∫ y in a..b, F x y+(xs.map fun z => F z y).sum) = _
    rw [intervalIntegral.integral_add (hF x List.mem_cons_self) (intervalIntegrable_list_sum F xs a b hTail),ih hTail]
    rfl

end
end StrongSilver
