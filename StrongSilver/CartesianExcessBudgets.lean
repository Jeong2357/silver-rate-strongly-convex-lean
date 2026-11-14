-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianExcessIntegral
import StrongSilver.IntegralPositivePart

namespace StrongSilver.ScheduleTree
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 3600000

/-- Finite forms of (4.9) and the positive-log part of (4.10), obtained
from the exact original-cut jump identity and uniform endpoint budgets. -/
theorem cartesian_excess_budgets {P κ M e : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (he : 0 ≤ e)
    (t : ScheduleTree) (hc : t.Cartesian) (center a b : ℝ) (hab : a ≤ b)
    (hlower : ∀ y ∈ Icc a b,
      -e ≤ Real.exp (nu*y)*(cutLogProduct id P κ (fullCut (P+Real.exp y) t.word)-center))
    (hupper : Real.exp (nu*b)*(cutLogProduct id P κ (fullCut (P+Real.exp b) t.word)-center) ≤ M)
    (hpower : cutPower id P κ (fullCut (P+Real.exp a) t.word) ≤ M) :
    let budget := splitCoefficient*(M+e)+M+splitCoefficient*nu*e*(b-a)
    ((t.paddedEvents P κ).map fun q => if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedEventExcess P q else 0).sum ≤ budget ∧
    splitCoefficient*nu*(∫ y in a..b, max (Real.exp (nu*y)*
      (cutLogProduct id P κ (fullCut (P+Real.exp y) t.word)-center)) 0) ≤ budget := by
  let f := fun y => Real.exp (nu*y)*(cutLogProduct id P κ (fullCut (P+Real.exp y) t.word)-center)
  let excess := ((t.paddedEvents P κ).map fun q =>
    if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedEventExcess P q else 0).sum
  have hI : IntervalIntegrable f volume a b := by
    have hi := weighted_stepObservable_intervalIntegrable (paddedHeight P) (fun q => paddedRootGain id P q.2 q.1)
      (Real.log (gapPrefix id t.word+P+κ)-center) nu (t.paddedEvents P κ) a b
    have hfun : (fun y => Real.exp (nu*y)*stepObservable (paddedHeight P) (fun q => paddedRootGain id P q.2 q.1)
        (Real.log (gapPrefix id t.word+P+κ)-center) (t.paddedEvents P κ) y) = f := by
      funext y
      rw [stepObservable_sub_base,← full_cut_log_stepObservable hP hκ t hc y]
    rwa [hfun] at hi
  have hEnonneg : 0 ≤ excess := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact paddedEventExcess_nonnegative hP hκ hq
    · exact le_rfl
  have hPafter : 0 ≤ cutPower id P κ (fullCut (P+Real.exp b) t.word) := by
    unfold cutPower
    apply List.sum_nonneg
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    exact Real.rpow_nonneg (cutMasses_positive id hP hκ _ z hz).le _
  have hidentity := cartesian_excess_integral_identity hP hκ t hc center a b hab
  change excess+splitCoefficient*nu*(∫ y in a..b, f y) = _ at hidentity
  have hlowA := hlower a ⟨le_rfl,hab⟩
  have hend : splitCoefficient*(f b-f a) ≤ splitCoefficient*(M+e) :=
    mul_le_mul_of_nonneg_left (by change _ ≤ M at hupper; change -e ≤ f a at hlowA; linarith only [hupper,hlowA]) split_coefficient_positive.le
  have hbudget : excess+splitCoefficient*nu*(∫ y in a..b, f y) ≤ splitCoefficient*(M+e)+M := by
    change excess+splitCoefficient*nu*(∫ y in a..b, f y) = splitCoefficient*(f b-f a)+
      cutPower id P κ (fullCut (P+Real.exp a) t.word)-cutPower id P κ (fullCut (P+Real.exp b) t.word) at hidentity
    linarith only [hidentity,hend,hpower,hPafter]
  have hIntLower := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := -e)) hI hlower
  rw [intervalIntegral.integral_const] at hIntLower
  have hcf : 0 ≤ splitCoefficient*nu := mul_nonneg split_coefficient_positive.le nu_positive.le
  have hIntLower' := mul_le_mul_of_nonneg_left hIntLower hcf
  have hpos := positive_part_integral_le_of_lower hab he hI hlower
  have hpos' := mul_le_mul_of_nonneg_left hpos hcf
  dsimp only
  constructor
  · change excess ≤ _
    simp only [smul_eq_mul] at hIntLower'
    nlinarith only [hbudget,hIntLower']
  · change splitCoefficient*nu*(∫ y in a..b, max (f y) 0) ≤ _
    nlinarith only [hbudget,hpos',hEnonneg]

end
end StrongSilver.ScheduleTree
