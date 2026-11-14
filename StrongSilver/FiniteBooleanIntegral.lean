-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteBooleanEvaluation

namespace StrongSilver
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4400000

theorem intervalIntegrable_measurable_ite (f g : ℝ → ℝ) (p : ℝ → Prop) [DecidablePred p]
    (hp : MeasurableSet {x | p x}) (hf : Measurable f) (hg : Measurable g) (a b : ℝ)
    (hfi : IntervalIntegrable f volume a b) (hgi : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun x => if p x then f x else g x) volume a b := by
  have hm : Measurable (fun x => if p x then f x else g x) := Measurable.ite hp hf hg
  apply (hfi.abs.add hgi.abs).mono_fun' hm.aestronglyMeasurable.restrict
  filter_upwards [] with x
  simp only [Real.norm_eq_abs]
  split_ifs
  · exact le_add_of_nonneg_right (abs_nonneg (g x))
  · exact le_add_of_nonneg_left (abs_nonneg (f x))

/-- A finite measurable decision tree preserves interval integrability
of each of its fixed outcome functions. -/
theorem intervalIntegrable_finite_boolean_evaluation (tests : List (ℝ → Bool))
    (hTests : ∀ t ∈ tests, MeasurableSet {y | t y = true})
    (F : List Bool → ℝ → ℝ) (hF : ∀ bs, Measurable (F bs)) (a b : ℝ)
    (hFi : ∀ bs, IntervalIntegrable (F bs) volume a b) :
    IntervalIntegrable (fun y => F (tests.map fun t => t y) y) volume a b := by
  induction tests generalizing F with
  | nil => exact hFi []
  | cons t ts ih =>
    have hTail : ∀ s ∈ ts, MeasurableSet {y | s y = true} := fun s hs => hTests s (List.mem_cons_of_mem t hs)
    let ft := fun y => F (true::(ts.map fun s => s y)) y
    let ff := fun y => F (false::(ts.map fun s => s y)) y
    have htm : Measurable ft := measurable_finite_boolean_evaluation ts hTail (fun bs => F (true::bs)) (fun bs => hF (true::bs))
    have hfm : Measurable ff := measurable_finite_boolean_evaluation ts hTail (fun bs => F (false::bs)) (fun bs => hF (false::bs))
    have hti : IntervalIntegrable ft volume a b := ih hTail (fun bs => F (true::bs)) (fun bs => hF (true::bs)) (fun bs => hFi (true::bs))
    have hfi : IntervalIntegrable ff volume a b := ih hTail (fun bs => F (false::bs)) (fun bs => hF (false::bs)) (fun bs => hFi (false::bs))
    have hRes := intervalIntegrable_measurable_ite ft ff (fun y => t y = true) (hTests t (by simp)) htm hfm a b hti hfi
    have he : (fun y => F ((t::ts).map fun s => s y) y) = fun y => if t y = true then ft y else ff y := by
      funext y
      cases ht : t y <;> simp [ht,ft,ff]
    rw [he]
    exact hRes

end
end StrongSilver
