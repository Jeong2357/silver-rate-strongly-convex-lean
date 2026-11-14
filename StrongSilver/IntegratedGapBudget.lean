-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IntegralPositivePart
import StrongSilver.CutObservables

namespace StrongSilver
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 2600000

/-- Finite cut observables remain integrable after multiplication by a
continuous cutoff weight. Their values need not themselves be continuous. -/
theorem weighted_cutObservable_intervalIntegrable (F : ScheduleCut → ℝ) (i : ℕ) (h : List ℝ)
    (q w : ℝ → ℝ) (hq : Measurable q) (hw : Continuous w) (a b : ℝ) :
    IntervalIntegrable (fun y => w y*F (cutScheduleFrom (fun _ x => decide (q y < x)) i h)) volume a b :=
  (cutObservable_intervalIntegrable F i h q hq a b).continuousOn_mul hw.continuousOn

/-- The remaining terms in (4.10) follow from the positive-log integral
and the uniform log/refinement error. The functions here are the
exponentially weighted actual cut observables in the application. -/
theorem integrated_gap_budget {f g r : ℝ → ℝ} {a b e M : ℝ}
    (hab : a ≤ b) (he : 0 ≤ e)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hr : IntervalIntegrable r volume a b)
    (hlower : ∀ y ∈ Icc a b, -e ≤ f y)
    (horder : ∀ y ∈ Icc a b, f y ≤ g y)
    (hsavings : ∀ y ∈ Icc a b, r y ≤ f y+e)
    (hpositive : (∫ y in a..b, max (g y) 0) ≤ M) :
    (∫ y in a..b, max (g y) 0+r y+(g y-f y)) ≤ 3*M+2*e*(b-a) := by
  have hgp := intervalIntegrable_positive_part hg
  have hleft : IntervalIntegrable (fun y => max (g y) 0+r y+(g y-f y)) volume a b :=
    (hgp.add hr).add (hg.sub hf)
  have hright : IntervalIntegrable (fun y => 3*max (g y) 0+2*e) volume a b :=
    (hgp.const_mul 3).add intervalIntegrable_const
  have hpoint : ∀ y ∈ Icc a b, max (g y) 0+r y+(g y-f y) ≤ 3*max (g y) 0+2*e := by
    intro y hy
    have hs := hsavings y hy
    have ho := horder y hy
    have hl := hlower y hy
    have hm := le_max_left (g y) 0
    linarith only [hs,ho,hl,hm]
  have hi := intervalIntegral.integral_mono_on hab hleft hright hpoint
  rw [intervalIntegral.integral_add (hgp.const_mul 3) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  nlinarith only [hi,hpositive]

end
end StrongSilver
