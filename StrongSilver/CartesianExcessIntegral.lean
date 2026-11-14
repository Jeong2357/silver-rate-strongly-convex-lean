-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianCutStepFunction
import StrongSilver.FiniteExcessIntegral
import StrongSilver.PaddedSplitInput

namespace StrongSilver.ScheduleTree
open Real Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3200000

def paddedEventExcess (P : ℝ) (q : ScheduleTree × ℝ) : ℝ :=
  splitCoefficient*Real.exp (nu*paddedHeight P q)*paddedRootGain id P q.2 q.1-paddedRootDecrease id P q.2 q.1

/-- Every event excess is the scalar excess of its original signed
left and right words with the correct terminal reserve. -/
theorem paddedEventExcess_realized {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    {t : ScheduleTree} {q : ScheduleTree × ℝ} (hq : q ∈ t.paddedEvents P κ) :
    ∃ S : PaddedSplitInput, S.excess = paddedEventExcess P q ∧
      S.weight = Real.exp (nu*paddedHeight P q) := by
  have hnode : q ∈ t.reservedNodes κ := (List.mem_filter.mp hq).1
  have hpivot : P < q.1.rootStep := of_decide_eq_true (List.mem_filter.mp hq).2
  have hres := reservedNodes_reserve_nonnegative hκ hnode
  obtain ⟨l,r,b,heq⟩ := reservedNodes_internal hnode
  rcases q with ⟨node,res⟩
  change node = .split l b r at heq
  subst node
  change P < b at hpivot
  let S : PaddedSplitInput := ⟨l.word,r.word,b,P,res,hP,hres,hpivot⟩
  have hw : S.weight = Real.exp (nu*paddedHeight P ((.split l b r),res)) := by
    change (b-P)^nu = Real.exp (nu*Real.log (b-P))
    rw [Real.rpow_def_of_pos (sub_pos.mpr hpivot),mul_comm]
  refine ⟨S,?_,hw⟩
  have hg : S.gain = paddedRootGain id P res (.split l b r) := by
    simp only [PaddedSplitInput.gain,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.t,
      PaddedSplitInput.z,paddedRootGain,gapPrefix,List.map_id,S,id_eq]
  have hd : S.decrease = paddedRootDecrease id P res (.split l b r) := by
    simp only [PaddedSplitInput.decrease,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.z,
      paddedRootDecrease,gapPrefix,List.map_id,S,id_eq]
  have hh := S.decrease_identity
  rw [hw,hg,hd] at hh
  unfold paddedEventExcess
  linarith only [hh]

theorem paddedEventExcess_nonnegative {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    {t : ScheduleTree} {q : ScheduleTree × ℝ} (hq : q ∈ t.paddedEvents P κ) : 0 ≤ paddedEventExcess P q := by
  obtain ⟨S,he,hw⟩ := paddedEventExcess_realized hP hκ hq
  rw [← he]
  exact S.excess_nonnegative

/-- The exact excess integral formula (4.9), before applying the
uniform rank estimates, for the actual full threshold cuts. -/
theorem cartesian_excess_integral_identity {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (t : ScheduleTree) (hc : t.Cartesian) (center a b : ℝ) (hab : a ≤ b) :
    ((t.paddedEvents P κ).map fun q => if a < paddedHeight P q ∧ paddedHeight P q ≤ b then paddedEventExcess P q else 0).sum+
      splitCoefficient*nu*(∫ y in a..b, Real.exp (nu*y)*(cutLogProduct id P κ (fullCut (P+Real.exp y) t.word)-center)) =
    splitCoefficient*(Real.exp (nu*b)*(cutLogProduct id P κ (fullCut (P+Real.exp b) t.word)-center)-
      Real.exp (nu*a)*(cutLogProduct id P κ (fullCut (P+Real.exp a) t.word)-center))+
      cutPower id P κ (fullCut (P+Real.exp a) t.word)-cutPower id P κ (fullCut (P+Real.exp b) t.word) := by
  have hh := finite_excess_integral_identity (paddedHeight P) (fun q => paddedRootGain id P q.2 q.1)
    (fun q => paddedRootDecrease id P q.2 q.1) (Real.log (gapPrefix id t.word+P+κ))
    ((gapPrefix id t.word+P+κ)^nu) center splitCoefficient nu a b (t.paddedEvents P κ) hab
  simp only [← full_cut_log_stepObservable hP hκ t hc,← full_cut_power_stepObservable hP t hc] at hh
  exact hh

end
end StrongSilver.ScheduleTree
