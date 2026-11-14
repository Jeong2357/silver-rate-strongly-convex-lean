-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TraceLogPrices

namespace StrongSilver.WorkingAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 2200000

def referenceLog (μ P : ℝ) : WorkingAssembly → ℝ
  | .ordinaryEnd q _ => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))
  | .ordinary q s => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))+s.referenceLog μ P
  | .block _ _ _ s => s.referenceLog μ P
  | .blockEnd _ _ _ _ => 0
  | .noConnector _ _ _ => 0

def logCost (A μ P : ℝ) : WorkingAssembly → ℝ
  | .ordinaryEnd q t => 4*(μ*Scalar.SignedIntervals.positiveMass t)+
      2*(1200/Real.log A+μ*transformedGapMaximum μ q.gap)
  | .ordinary q s => 2*(1200/Real.log A+μ*transformedGapMaximum μ q.gap)+s.logCost A μ P
  | .block _ I _ s => 50*Real.log A+2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I)+s.logCost A μ P
  | .blockEnd _ I _ t => 4*(μ*Scalar.SignedIntervals.positiveMass t)+
      Real.log (4*A^(19 : ℝ)*(1200000 : ℝ)^2)+2*(inverseCharge μ I+Real.log (1+smallPositiveSum μ I))
  | .noConnector _ I t => 2*inverseCharge μ I+4*μ*Scalar.SignedIntervals.positiveMass t+Real.log (2*A^(19 : ℝ))

theorem rate_positive {A μ T P : ℝ} {s : WorkingAssembly} (hA : 1 < A) (hs : s.Valid A μ T P) :
    0 < s.rate A μ P := by
  have hA0 := zero_lt_one.trans hA
  induction s with
  | ordinaryEnd q t =>
    exact mul_pos (Real.exp_pos _) (sq_pos_of_pos (hs.1.reference_factor_positive hA))
  | ordinary q s ih =>
    exact mul_pos (ih hs.2) (sq_pos_of_pos (hs.1.reference_factor_positive hA))
  | block q I c s ih =>
    exact div_pos (ih hs.2.2.2.2.2) (sq_pos_of_pos (workingBlockFactor_positive hA0 μ I))
  | blockEnd q I c t => exact workingTerminalRate_positive hA0 μ I t
  | noConnector q I t => exact workingNoConnectorRate_positive hA0 μ I t

theorem log_rate {A μ T P : ℝ} {s : WorkingAssembly} (hA : 1 < A) (hs : s.Valid A μ T P) :
    Real.log (s.rate A μ P) = 2*s.referenceLog μ P-s.logCost A μ P := by
  have hA0 := zero_lt_one.trans hA
  induction s with
  | ordinaryEnd q t =>
    rw [rate,Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero 2 (hs.1.reference_factor_positive hA).ne'),
      Real.log_exp,Real.log_pow,hs.1.log_reference_factor hA]
    simp only [referenceLog,logCost]
    ring
  | ordinary q s ih =>
    rw [rate,Real.log_mul (rate_positive hA hs.2).ne' (pow_ne_zero 2 (hs.1.reference_factor_positive hA).ne'),
      Real.log_pow,hs.1.log_reference_factor hA,ih hs.2]
    simp only [referenceLog,logCost]
    ring
  | block q I c s ih =>
    rw [rate,Real.log_div (rate_positive hA hs.2.2.2.2.2).ne' (pow_ne_zero 2 (workingBlockFactor_positive hA0 μ I).ne'),
      Real.log_pow,log_workingBlockFactor hA0,ih hs.2.2.2.2.2]
    simp only [referenceLog,logCost]
    ring
  | blockEnd q I c t =>
    rw [rate,log_workingTerminalRate hA0]
    simp only [referenceLog,logCost]
    ring
  | noConnector q I t =>
    rw [rate,log_workingNoConnectorRate hA0]
    simp only [referenceLog,logCost]
    ring

theorem referenceLog_eq_sum (μ P : ℝ) (s : WorkingAssembly) :
    s.referenceLog μ P = (s.tracked.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum := by
  induction s <;> simp_all [referenceLog,tracked]

/-- The exact assembled last-iterate lower bound controls the retained
reference product for every stable schedule represented by the assembly. -/
theorem eventually_stable_reference_log : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → D κ s.word ≤ 1 → 2*s.referenceLog μ P ≤ s.logCost A μ P := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_stable_rate] with A hA hstable
  intro κ μ T P s hs hκ hμ hμ1 hD
  have hh := Real.log_le_log (rate_positive hA hs) (hstable κ μ T P s hs hκ hμ hμ1 hD)
  rw [Real.log_one,log_rate hA hs] at hh
  linarith only [hh]

end
end StrongSilver.WorkingAssembly
