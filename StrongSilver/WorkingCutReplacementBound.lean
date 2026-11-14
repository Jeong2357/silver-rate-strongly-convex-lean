-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutReplacement
import StrongSilver.WorkingCutBound

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4000000

/-- One reservation is chosen from the original cut before any local
gain is requested. Every actual replacement witness then satisfies the
same full working-cut logarithmic budget, including all exceptional and
terminal costs. This is the finite construction bound used in (4.6). -/
theorem eventually_working_cut_replacement_bound : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P σ τ : ℝ, ∀ C : ScheduleCut,
    1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ ≤ 2/κ → μ*A ≤ 1/2 → 1 ≤ P →
    0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 →
    (∀ q ∈ C.phases, P < q.pivot) →
    (∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
    (∀ b ∈ C.terminal, 0 < b → b ≤ A) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
    ∃ s : CompleteCutAssembly, s.phases = C.phases ∧
      s.WellFormed (ordinaryPhaseGood A μ T P) ∧ s.Counted (ordinaryPhaseGood A μ T P) ∧
      s.reserved.length ≤ 4*badPhaseCount (ordinaryPhaseGood A μ T P) C.phases ∧
      ∀ gain : ℝ, s.ReplacementWitness A μ P C.terminal gain → D κ C.word ≤ 1 →
      2*(C.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum+gain ≤
        workingCutLoss A κ μ T P σ τ C := by
  classical
  filter_upwards [eventually_gt_atTop (1:ℝ),CompleteCutAssembly.eventually_phaseValid,
    CompleteCutAssembly.eventually_full_log_cost_budget,CompleteCutAssembly.eventually_stable_replacement_test]
    with A hA hvalid hcost htest
  intro κ μ T P σ τ C hκ hμ hμ1 hμu hcap hP hσ hσ1 hτ hτ1 hpiv hgap ht hcritical
  let good := ordinaryPhaseGood A μ T P
  have hW : ∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap := fun q hq => of_decide_eq_true hq
  obtain ⟨s,hph,hs,hcounted,hcount⟩ := exists_complete_cutAssembly good C.phases
  have hword : s.word C.terminal = C.word := by simp only [CompleteCutAssembly.word,hph,ScheduleCut.word]
  have hpiv' : ∀ q ∈ s.phases, P < q.pivot := by simpa only [hph] using hpiv
  have hgap' : ∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A := by simpa only [hph] using hgap
  have hcrit' : ∀ b ∈ s.word C.terminal, 1-μ*b ≠ 0 := by simpa only [hword] using hcritical
  have hv := hvalid μ T P good hW s hs C.terminal ht hcrit'
  have hprice := hcost κ μ T P σ τ good hW s hs hcounted C.terminal hκ hμ hμ1 hμu hcap hP
    hσ hσ1 hτ hτ1 hpiv' hgap' ht hcrit'
  have hmass := C.unselected_positiveMass
  change Scalar.SignedIntervals.positiveMass C.unselected = phaseGapMass C.phases+Scalar.SignedIntervals.positiveMass C.terminal at hmass
  have hprice' : 2*(C.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
      Real.log (s.rate A μ P C.terminal) ≤ workingCutLoss A κ μ T P σ τ C := by
    simpa only [hph,hword,← hmass,workingCutLoss,good] using hprice
  refine ⟨s,hph,hs,hcounted,hcount,?_⟩
  intro gain hwitness hD
  have hD' : D κ (s.word C.terminal) ≤ 1 := by simpa only [hword] using hD
  have hgain := htest κ μ T P good hW s hs C.terminal gain hκ hμ hμ1 hcap ht hcrit' hwitness hD'
  have hlog := s.log_rate hA hv
  linarith only [hgain,hlog,hprice']

end
end StrongSilver
