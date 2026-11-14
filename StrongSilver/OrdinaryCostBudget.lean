-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutAssembly
import StrongSilver.TransformedGapBudget
import StrongSilver.PhaseCurvatureBounds

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem OrdinaryPhaseParameters.transformed_mass_le {A μ b T P : ℝ} {h : List ℝ}
    (W : OrdinaryPhaseParameters A μ b T P h) (hA : 0 < A) :
    transformedGapMaximum μ h ≤ 2*Scalar.SignedIntervals.positiveMass h := by
  have hc := W.mu_cap hA
  have hh := transformedGapMaximum_le_positive_mass W.mu_positive (by linarith only [hc] : μ*A < 1) h W.gap_cap
  have hmass := Scalar.SignedIntervals.positiveMass_nonneg h
  have hfrac : Scalar.SignedIntervals.positiveMass h/(1-μ*A) ≤ 2*Scalar.SignedIntervals.positiveMass h := by
    apply (div_le_iff₀ (by linarith only [hc] : 0 < 1-μ*A)).mpr
    have hm := mul_nonneg hmass (show 0 ≤ 1/2-μ*A by linarith only [hc])
    nlinarith only [hm]
  exact hh.trans hfrac

theorem ordinary_cost_sum_le {A μ T P : ℝ} (hA : 0 < A) (hμ : 0 ≤ μ) (qs : List CutPhase)
    (hgood : ∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap) :
    2*(qs.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum ≤
      2400*(qs.length : ℝ)/Real.log A+4*μ*(qs.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have htail := ih (fun z hz => hgood z (List.mem_cons_of_mem q hz))
    have hm := mul_le_mul_of_nonneg_left ((hgood q (by simp)).transformed_mass_le hA) hμ
    have hhead : 2*(1200/Real.log A+μ*transformedGapMaximum μ q.gap) ≤
        2400/Real.log A+4*μ*Scalar.SignedIntervals.positiveMass q.gap := by
      calc
        _ = 2400/Real.log A+2*μ*transformedGapMaximum μ q.gap := by ring
        _ ≤ _ := by nlinarith only [hm]
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      _ = 2*(1200/Real.log A+μ*transformedGapMaximum μ q.gap)+
          2*(qs.map fun z => 1200/Real.log A+μ*transformedGapMaximum μ z.gap).sum := by ring
      _ ≤ (2400/Real.log A+4*μ*Scalar.SignedIntervals.positiveMass q.gap)+
          (2400*(qs.length : ℝ)/Real.log A+4*μ*(qs.map fun z => Scalar.SignedIntervals.positiveMass z.gap).sum) := add_le_add hhead htail
      _ = _ := by ring

theorem CutAssembly.tracked_good {good : CutPhase → Bool} {s : CutAssembly} (hs : s.WellFormed good) :
    ∀ q ∈ s.tracked, good q = true := by
  induction s with
  | ordinaryEnd q => simpa only [tracked,WellFormed,List.mem_singleton,forall_eq] using hs
  | ordinary q s ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hs.1
    · exact ih hs.2 z hz
  | block q I c s ih => exact ih hs.2.2
  | blockEnd q I c => simp [tracked]
  | noConnector q I => simp [tracked]

theorem CompleteCutAssembly.tracked_good {good : CutPhase → Bool} {s : CompleteCutAssembly} (hs : s.WellFormed good) :
    ∀ q ∈ s.tracked, good q = true := by
  cases s with
  | scalar I => simp [tracked]
  | positive s => exact s.tracked_good hs
  | leadingBlock I c s => exact s.tracked_good hs.2
  | leadingEnd I c => simp [tracked]

end
end StrongSilver
