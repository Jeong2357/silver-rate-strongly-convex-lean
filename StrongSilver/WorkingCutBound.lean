-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingGlobalLogBudget

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

def cutReferenceProduct (μ P : ℝ) (qs : List CutPhase) : ℝ :=
  (qs.map fun q => (q.pivot-P)/(transformedGapMaximum μ q.gap+P)).prod

def workingCutLoss (A κ μ T P σ τ : ℝ) (C : ScheduleCut) : ℝ :=
  2400*(C.phases.length : ℝ)/Real.log A+4*μ*Scalar.SignedIntervals.positiveMass C.unselected+
  304*(badPhaseCount (ordinaryPhaseGood A μ T P) C.phases : ℝ)*Real.log A+
  2*inverseChargeAbove (κ/4) C.word μ+4*largeLogESum C.word (A^(1+σ))+
  4*(Scalar.SignedIntervals.positiveMass C.unselected/A^(1+τ))

theorem exp_two_log_sum {α : Type*} (f : α → ℝ) (qs : List α) (hf : ∀ q ∈ qs, 0 < f q) :
    Real.exp (2*(qs.map fun q => Real.log (f q)).sum) = (qs.map f).prod^2 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq := hf q (by simp)
    have ht := ih (fun z hz => hf z (List.mem_cons_of_mem q hz))
    simp only [List.map_cons,List.sum_cons,List.prod_cons]
    rw [show 2*(Real.log (f q)+(qs.map fun q => Real.log (f q)).sum) =
      (Real.log (f q)+Real.log (f q))+2*(qs.map fun q => Real.log (f q)).sum by ring,
      Real.exp_add,Real.exp_add,Real.exp_log hq,ht]
    ring

/-- A complete working-cut realization with explicit absolute constants.
The count in the loss is defined from the ordinary numerical class, and
the reservation and actual trajectory are constructed in the proof. -/
theorem eventually_working_cut_distance_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P σ τ : ℝ, ∀ C : ScheduleCut,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ ≤ 2/κ → μ*A ≤ 1/2 → 1 ≤ P →
      0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 →
      (∀ q ∈ C.phases, P < q.pivot) →
      (∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
      (∀ b ∈ C.terminal, 0 < b → b ≤ A) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
      ENNReal.ofReal (Real.exp (-workingCutLoss A κ μ T P σ τ C)*(cutReferenceProduct μ P C.phases)^2) ≤ D κ C.word := by
  classical
  filter_upwards [eventually_gt_atTop (1 : ℝ),CompleteCutAssembly.eventually_full_log_cost_budget,
    CompleteCutAssembly.eventually_distance_lower,CompleteCutAssembly.eventually_phaseValid]
    with A hA hcost hlower hvalid
  intro κ μ T P σ τ C hκ hμ hμ1 hμu hcap hP hσ hσ1 hτ hτ1 hpiv hgap ht hcritical
  let good := ordinaryPhaseGood A μ T P
  have hW : ∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap := fun _ hq => of_decide_eq_true hq
  obtain ⟨s,hph,hs,hcounted,hcount⟩ := exists_complete_cutAssembly good C.phases
  have hword : s.word C.terminal = C.word := by simp only [CompleteCutAssembly.word,hph,ScheduleCut.word]
  have hgap' : ∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A := by simpa only [hph] using hgap
  have hpiv' : ∀ q ∈ s.phases, P < q.pivot := by simpa only [hph] using hpiv
  have hcrit' : ∀ b ∈ s.word C.terminal, 1-μ*b ≠ 0 := by simpa only [hword] using hcritical
  have hv := hvalid μ T P good hW s hs C.terminal ht hcrit'
  have hr := s.rate_positive hA hv
  have hl := hlower κ μ T P good hW s hs C.terminal hκ hμ hμ1 hcap ht hcrit'
  have hb := hcost κ μ T P σ τ good hW s hs hcounted C.terminal hκ hμ hμ1 hμu hcap hP
    hσ hσ1 hτ hτ1 hpiv' hgap' ht hcrit'
  have hmass := C.unselected_positiveMass
  change Scalar.SignedIntervals.positiveMass C.unselected = phaseGapMass C.phases+Scalar.SignedIntervals.positiveMass C.terminal at hmass
  have hbudget : 2*(C.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
      Real.log (s.rate A μ P C.terminal) ≤ workingCutLoss A κ μ T P σ τ C := by
    simpa only [hph,hword,← hmass,workingCutLoss,good] using hb
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).trans_le hμ
  have hratio : ∀ q ∈ C.phases, 0 < (q.pivot-P)/(transformedGapMaximum μ q.gap+P) := by
    intro q hq
    have hm := transformed_gap_nonnegative_of_cap hμ0 hcap q.gap (hgap q hq)
    exact div_pos (sub_pos.mpr (hpiv q hq)) (by linarith only [hm,hP])
  have hprod := exp_two_log_sum (fun q : CutPhase => (q.pivot-P)/(transformedGapMaximum μ q.gap+P)) C.phases hratio
  have he := Real.exp_le_exp.mpr (show
      2*(C.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
        workingCutLoss A κ μ T P σ τ C ≤ Real.log (s.rate A μ P C.terminal) by linarith only [hbudget])
  rw [Real.exp_log hr,sub_eq_add_neg,Real.exp_add,hprod] at he
  have hreal : Real.exp (-workingCutLoss A κ μ T P σ τ C)*(cutReferenceProduct μ P C.phases)^2 ≤ s.rate A μ P C.terminal := by
    simpa only [cutReferenceProduct,mul_comm] using he
  simpa only [hword] using (ENNReal.ofReal_le_ofReal hreal).trans hl

end
end StrongSilver
