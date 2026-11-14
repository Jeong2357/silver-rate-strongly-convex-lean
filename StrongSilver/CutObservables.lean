-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace StrongSilver
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 2000000

/-- Any real observable of a finite threshold cut is measurable, even
though no measurable structure on the cut metadata is required. -/
theorem measurable_cutObservable (F : ScheduleCut → ℝ) (i : ℕ) (h : List ℝ) :
    Measurable (fun A : ℝ => F (cutScheduleFrom (fun _ b => decide (A < b)) i h)) := by
  classical
  induction h generalizing F i with
  | nil => simpa only [cutScheduleFrom] using (measurable_const : Measurable (fun _ : ℝ => F ⟨[],[]⟩))
  | cons a h ih =>
    have hs := ih (fun C => F (C.prependSelected i a)) (i+1)
    have hu := ih (fun C => F (C.prependUnselected a)) (i+1)
    simpa only [cutScheduleFrom,decide_eq_true_eq,apply_ite] using Measurable.ite (p := fun A : ℝ => A < a) measurableSet_Iio hs hu

def cutObservableBound (F : ScheduleCut → ℝ) (i : ℕ) : List ℝ → ℝ
  | [] => |F ⟨[],[]⟩|
  | a::h => max (cutObservableBound (fun C => F (C.prependSelected i a)) (i+1) h)
      (cutObservableBound (fun C => F (C.prependUnselected a)) (i+1) h)

theorem cutObservableBound_nonnegative (F : ScheduleCut → ℝ) (i : ℕ) (h : List ℝ) :
    0 ≤ cutObservableBound F i h := by
  induction h generalizing F i with
  | nil => exact abs_nonneg _
  | cons a h ih => exact (ih _ _).trans (le_max_left _ _)

theorem cutObservable_abs_le (F : ScheduleCut → ℝ) (i : ℕ) (h : List ℝ) (A : ℝ) :
    |F (cutScheduleFrom (fun _ b => decide (A < b)) i h)| ≤ cutObservableBound F i h := by
  induction h generalizing F i with
  | nil => exact le_rfl
  | cons a h ih =>
    by_cases hc : A < a
    · simpa only [cutScheduleFrom,hc,decide_true,↓reduceIte,cutObservableBound] using
        (ih (fun C => F (C.prependSelected i a)) (i+1)).trans (le_max_left _ _)
    · simpa only [cutScheduleFrom,hc,decide_false,Bool.false_eq_true,↓reduceIte,cutObservableBound] using
        (ih (fun C => F (C.prependUnselected a)) (i+1)).trans (le_max_right _ _)

/-- Finite cut observables remain interval integrable after any measurable
reparameterization of the threshold. -/
theorem cutObservable_intervalIntegrable (F : ScheduleCut → ℝ) (i : ℕ) (h : List ℝ)
    (q : ℝ → ℝ) (hq : Measurable q) (a b : ℝ) :
    IntervalIntegrable (fun t => F (cutScheduleFrom (fun _ x => decide (q t < x)) i h)) volume a b := by
  have hm : Measurable (fun t => F (cutScheduleFrom (fun _ x => decide (q t < x)) i h)) := by
    simpa only [Function.comp_def] using (measurable_cutObservable F i h).comp hq
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (by exact measure_Ioc_lt_top) hm.aestronglyMeasurable.restrict (cutObservableBound F i h)
  exact Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using cutObservable_abs_le F i h (q t))

end
end StrongSilver
