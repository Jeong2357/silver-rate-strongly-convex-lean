-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothedStepObservable
import StrongSilver.CartesianCutStepFunction
import StrongSilver.AveragedCutPower

namespace StrongSilver
open ScheduleTree Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6500000

namespace ScheduleTree

theorem reservedNodes_source_cartesian {κ : ℝ} {t : ScheduleTree} (hc : t.Cartesian)
    {q : ScheduleTree × ℝ} (hq : q ∈ t.reservedNodes κ) : q.1.Cartesian := by
  induction t generalizing κ with
  | leaf word => simp [reservedNodes] at hq
  | split l b r il ir =>
    simp only [reservedNodes,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl | hl | hr
    · exact hc
    · exact il hc.1 hl
    · exact ir hc.2.1 hr

theorem reservedNodes_root_positive {κ : ℝ} {t : ScheduleTree} (hc : t.Cartesian)
    {q : ScheduleTree × ℝ} (hq : q ∈ t.reservedNodes κ) : 0 < q.1.rootStep := by
  have hSource := reservedNodes_source_cartesian hc hq
  obtain ⟨l,r,b,hs⟩ := reservedNodes_internal hq
  rw [hs] at hSource ⊢
  exact hSource.2.2.1

/-- The exact power step observable in original log-threshold scale,
with every original split occurrence and terminal reserve retained. -/
theorem full_cut_logheight_power_step (φ : ℝ → ℝ) (P κ x : ℝ) (t : ScheduleTree) (hc : t.Cartesian) :
    cutPower φ P κ (fullCut (Real.exp x) t.word) =
      stepObservable (fun q : ScheduleTree × ℝ => Real.log q.1.rootStep)
        (fun q => paddedRootDecrease φ P q.2 q.1) ((gapPrefix φ t.word+P+κ)^nu) (t.reservedNodes κ) x := by
  have hh := full_cut_power_jump_formula (φ:=φ) (P:=P) (κ:=κ) (Real.exp_pos x).le t hc 0
  rw [splitSumAbove_eq_node_sum _ _ _ t hc] at hh
  have hEq : ((t.reservedNodes κ).map fun q => if Real.exp x < q.1.rootStep then paddedRootDecrease φ P q.2 q.1 else 0).sum =
      ((t.reservedNodes κ).map fun q => if x < Real.log q.1.rootStep then paddedRootDecrease φ P q.2 q.1 else 0).sum := by
    congr 1
    apply List.map_congr_left
    intro q hq
    have hIff : x < Real.log q.1.rootStep ↔ Real.exp x < q.1.rootStep :=
      Real.lt_log_iff_exp_lt (reservedNodes_root_positive hc hq)
    simp only [hIff]
  rw [hEq] at hh
  rw [ScheduleTree.stepObservable_eq_base_sub_sum]
  exact hh

end ScheduleTree

/-- Exact formula (4.2), with an arbitrary pad. No generic-position
or distinct-step assumption is used. -/
theorem averaged_original_power_jumps (φ : ℝ → ℝ) (P κ u v : ℝ) (h : List ℝ) (hu : 0 < u) (hv : 0 < v) :
    (∫ t in (0:ℝ)..1, (cutPower φ P κ (fullCut (Real.exp (u+t*Real.sqrt u)) h)-
      cutPower φ P κ (fullCut (Real.exp (v+t*Real.sqrt v)) h))) =
    (((cartesian h).reservedNodes κ).map fun q => smoothedBandWeight u v (Real.log q.1.rootStep)*paddedRootDecrease φ P q.2 q.1).sum := by
  have ht := cartesian_valid h
  have hWord := cartesian_word h
  conv_lhs =>
    arg 1
    ext t
    rw [← hWord,full_cut_logheight_power_step φ P κ _ _ ht,full_cut_logheight_power_step φ P κ _ _ ht]
  exact smoothed_stepObservable_difference _ _ _ u v _ hu hv

end
end StrongSilver
