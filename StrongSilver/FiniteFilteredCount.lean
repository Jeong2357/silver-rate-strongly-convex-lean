-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFrontierGeneralIntegral

namespace StrongSilver
open Set MeasureTheory
noncomputable section
variable {α : Type*}
set_option maxHeartbeats 4400000

def filteredCount (p : α → ℝ → Prop) (xs : List α) (y : ℝ) : ℝ :=
  ((xs.filter fun x => @decide (p x y) (Classical.propDecidable _)).length:ℝ)

theorem filteredCount_measurable (p : α → ℝ → Prop) (hp : ∀ x, MeasurableSet {y | p x y}) (xs : List α) :
    Measurable (filteredCount p xs) := by
  classical
  induction xs with
  | nil =>
    have he : filteredCount p [] = fun _ => (0:ℝ) := by funext y; simp [filteredCount]
    rw [he]
    exact measurable_const
  | cons x xs ih =>
    have he : filteredCount p (x::xs) = fun y => if p x y then 1+filteredCount p xs y else filteredCount p xs y := by
      funext y
      by_cases hx : p x y <;> simp [filteredCount,hx,Nat.cast_add,Nat.cast_one] <;> ring
    rw [he]
    exact Measurable.ite (hp x) (measurable_const.add ih) ih

theorem filteredCount_abs_le_length (p : α → ℝ → Prop) (xs : List α) (y : ℝ) :
    |filteredCount p xs y| ≤ (xs.length:ℝ) := by
  have hn : 0 ≤ filteredCount p xs y := Nat.cast_nonneg _
  rw [abs_of_nonneg hn]
  unfold filteredCount
  exact_mod_cast (List.length_filter_le (fun x => @decide (p x y) (Classical.propDecidable _)) xs)

theorem filteredCount_integrable (p : α → ℝ → Prop) (hp : ∀ x, MeasurableSet {y | p x y})
    (xs : List α) (a b : ℝ) : IntervalIntegrable (filteredCount p xs) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by exact measure_Ioc_lt_top) (filteredCount_measurable p hp xs).aestronglyMeasurable.restrict (xs.length:ℝ)
  exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using filteredCount_abs_le_length p xs y)

end
end StrongSilver
