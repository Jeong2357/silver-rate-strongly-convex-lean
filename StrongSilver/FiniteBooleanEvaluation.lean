-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutObservables

namespace StrongSilver
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4200000

/-- A finite list of measurable Boolean decisions may select any real
observable, provided each fixed decision list has a measurable score.
No measurable structure on the selected metadata is required. -/
theorem measurable_finite_boolean_evaluation (tests : List (ℝ → Bool))
    (hTests : ∀ t ∈ tests, MeasurableSet {y | t y = true})
    (F : List Bool → ℝ → ℝ) (hF : ∀ bs, Measurable (F bs)) :
    Measurable (fun y => F (tests.map fun t => t y) y) := by
  induction tests generalizing F with
  | nil => exact hF []
  | cons t ts ih =>
    have hTail : ∀ s ∈ ts, MeasurableSet {y | s y = true} := fun s hs => hTests s (List.mem_cons_of_mem t hs)
    have ht := ih hTail (fun bs => F (true::bs)) (fun bs => hF (true::bs))
    have hf := ih hTail (fun bs => F (false::bs)) (fun bs => hF (false::bs))
    have hMeas : Measurable (fun y => if t y = true then F (true::(ts.map fun s => s y)) y else
        F (false::(ts.map fun s => s y)) y) := Measurable.ite (hTests t (by simp)) ht hf
    have he : (fun y => F ((t::ts).map fun s => s y) y) = fun y =>
        if t y = true then F (true::(ts.map fun s => s y)) y else F (false::(ts.map fun s => s y)) y := by
      funext y
      cases ht : t y <;> simp [ht]
    rw [he]
    exact hMeas

end
end StrongSilver
