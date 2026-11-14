-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialGlobalCostBudget
import StrongSilver.WorkingCutBound

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

def initialCutLoss (A κ B μ : ℝ) (good : CutPhase → Bool) (s : CompleteInitialCutAssembly)
    (choose : ℕ → ℝ → Bool) (t : List ℝ) : ℝ :=
  2400*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A+
  6*μ*(phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t)+
  (7*(initialLogPriceConstant+6))*(badPhaseCount good s.phases : ℝ)*(1+Real.log (κ/B))+
  2*largeInverseCharge κ (s.word t) μ

/-- Initial-cut realization after summing all reserved-block prices.
Only tracked factors are retained; every actual original step is executed. -/
theorem eventually_initial_cut_distance_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ C : ScheduleCut, ∀ choose : ℕ → ℝ → Bool,
      A ≤ B → 2 ≤ B → B ≤ κ → κ ≤ A^((1003 : ℝ)/1000) →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B) →
      (∀ b ∈ C.terminal, 0 < b → b ≤ B) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
      ∃ s : CompleteInitialCutAssembly, s.phases = C.phases ∧ s.WellFormed good ∧ s.Counted good ∧
        s.reserved.length ≤ 7*badPhaseCount good C.phases ∧
        ENNReal.ofReal (Real.exp (-initialCutLoss A κ B μ good s choose C.terminal)*
          (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2) ≤ D κ C.word := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),CompleteInitialCutAssembly.eventually_phaseValid,
    CompleteInitialCutAssembly.eventually_distance_lower,eventually_initial_refined_parameters]
    with A hA hvalid hlower hparams
  intro κ B μ T P good hW C choose hAB hB hBκ hκA hκ hμ hμu hcap hPL hPU hselected hunselected hgap ht hcritical
  have hκ0 := zero_lt_one.trans_le hκ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hμ1 : μ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hB hμ0.le
    nlinarith only [hh,hcap]
  obtain ⟨s,hph,hs,hc,hcount⟩ := exists_complete_initial_cutAssembly good C.phases
  have hword : s.word C.terminal = C.word := by simp only [CompleteInitialCutAssembly.word,hph,ScheduleCut.word]
  have hcrit' : ∀ b ∈ s.word C.terminal, 1-μ*b ≠ 0 := by simpa only [hword] using hcritical
  have hv := hvalid κ B μ T P good hW s hs choose C.terminal hAB hB hκA hPL hPU hselected hunselected hcrit'
  have hr := s.rate_positive (t := C.terminal) hA hκ0 hB0 hv
  have hlog := s.log_rate (t := C.terminal) hA hκ0 hB0 hv
  have hOrd : ∀ z ∈ s.trackedPhases.flatMap (refinePhase choose), OrdinaryPhaseParameters A μ z.pivot T P z.gap := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := List.mem_flatMap.mp hz
    exact hparams κ B μ T P q choose hAB hκA hPL hPU (hW q (s.tracked_good hs q hq)) hselected hunselected z hz
  have hgaps : ∀ q ∈ s.reserved, ∀ b ∈ q.gap, 0 < b → b ≤ B := by
    intro q hq
    have hh := CompleteInitialCutAssembly.mem_reserved hq
    rw [hph] at hh
    exact hgap q hh
  have hcost := s.logCost_global_budget (zero_lt_one.trans hA) hκ0 hB0 ((one_le_div hB0).mpr hBκ)
    hμ hμu hcap good hs hc choose C.terminal hOrd hgaps
  change s.logCost A κ B μ P choose C.terminal ≤ initialCutLoss A κ B μ good s choose C.terminal at hcost
  rw [s.referenceLog_eq_sum μ P choose] at hlog
  have hlogLower : 2*((s.trackedPhases.flatMap (refinePhase choose)).map
      fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
      initialCutLoss A κ B μ good s choose C.terminal ≤ Real.log (s.rate A κ B μ P choose C.terminal) := by
    linarith only [hlog,hcost]
  have hprod := exp_two_log_sum (fun q : CutPhase => (q.pivot-P)/(transformedGapMaximum μ q.gap+P))
    (s.trackedPhases.flatMap (refinePhase choose)) (fun q hq => (hOrd q hq).padded_ratio_positive hA)
  have he := Real.exp_le_exp.mpr hlogLower
  rw [Real.exp_log hr,sub_eq_add_neg,Real.exp_add,hprod] at he
  have hrBound : Real.exp (-initialCutLoss A κ B μ good s choose C.terminal)*
      (cutReferenceProduct μ P (s.trackedPhases.flatMap (refinePhase choose)))^2 ≤ s.rate A κ B μ P choose C.terminal := by
    simpa only [cutReferenceProduct,mul_comm] using he
  refine ⟨s,hph,hs,hc,hcount,?_⟩
  have hactual := hlower κ B μ T P good hW s hs choose C.terminal hAB hB hκA hκ hμ hμ1 hcap
    hPL hPU hselected hunselected ht hcrit'
  simpa only [hword] using (ENNReal.ofReal_le_ofReal hrBound).trans hactual

end
end StrongSilver
