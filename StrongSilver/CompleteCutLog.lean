-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutLogCost

namespace StrongSilver.CompleteCutAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

def referenceLog (μ P : ℝ) (t : List ℝ) : CompleteCutAssembly → ℝ
  | .scalar _ => 0
  | .positive s => (s.erase t).referenceLog μ P
  | .leadingBlock _ _ s => (s.erase t).referenceLog μ P
  | .leadingEnd _ _ => 0

def logCost (A μ P : ℝ) (t : List ℝ) : CompleteCutAssembly → ℝ
  | .scalar I => 2*inverseCharge μ (I.flatMap CutPhase.word)+4*μ*Scalar.SignedIntervals.positiveMass t
  | .positive s => (s.erase t).logCost A μ P
  | .leadingBlock I c s => 50*Real.log A+2*inverseCharge μ (I.flatMap CutPhase.word++c.gap)+
      2*Real.log (1+smallPositiveSum μ (I.flatMap CutPhase.word++c.gap))+(s.erase t).logCost A μ P
  | .leadingEnd I c => 4*μ*Scalar.SignedIntervals.positiveMass t+Real.log (4*(1200000 : ℝ)^2)+
      2*(inverseCharge μ (I.flatMap CutPhase.word++c.gap)+Real.log (1+smallPositiveSum μ (I.flatMap CutPhase.word++c.gap)))

def PhaseValid (A μ T P : ℝ) (t : List ℝ) : CompleteCutAssembly → Prop
  | .scalar _ => True
  | .positive s => (s.erase t).Valid A μ T P
  | .leadingBlock _ _ s => (s.erase t).Valid A μ T P
  | .leadingEnd _ _ => True

theorem referenceLog_eq_sum (μ P : ℝ) (t : List ℝ) (s : CompleteCutAssembly) :
    s.referenceLog μ P t = (s.tracked.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum := by
  cases s <;> simp only [referenceLog,tracked,WorkingAssembly.referenceLog_eq_sum,CutAssembly.erase_tracked,List.map_nil,List.sum_nil]

theorem openTerminalRate_positive (μ : ℝ) (I t : List ℝ) : 0 < openTerminalRate μ I t := by
  have hs := smallPositiveSum_nonneg μ I
  unfold openTerminalRate
  positivity

theorem log_openTerminalRate (μ : ℝ) (I t : List ℝ) :
    Real.log (openTerminalRate μ I t) = -4*(μ*Scalar.SignedIntervals.positiveMass t)-Real.log (4*(1200000 : ℝ)^2)-
      2*(inverseCharge μ I+Real.log (1+smallPositiveSum μ I)) := by
  have hs : 0 < 1+smallPositiveSum μ I := by linarith only [smallPositiveSum_nonneg μ I]
  rw [openTerminalRate,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by norm_num) (by positivity),Real.log_pow,
    Real.log_mul (Real.exp_ne_zero _) hs.ne',Real.log_exp]
  norm_num
  ring

theorem rate_positive {A μ T P : ℝ} {t : List ℝ} {s : CompleteCutAssembly}
    (hA : 1 < A) (hs : s.PhaseValid A μ T P t) : 0 < s.rate A μ P t := by
  cases s with
  | scalar I => exact Real.exp_pos _
  | positive s => exact WorkingAssembly.rate_positive hA hs
  | leadingBlock I c s =>
    exact div_pos (WorkingAssembly.rate_positive hA hs)
      (sq_pos_of_pos (workingBlockFactor_positive (zero_lt_one.trans hA) μ _))
  | leadingEnd I c => exact openTerminalRate_positive μ _ t

theorem log_rate {A μ T P : ℝ} {t : List ℝ} {s : CompleteCutAssembly}
    (hA : 1 < A) (hs : s.PhaseValid A μ T P t) :
    Real.log (s.rate A μ P t) = 2*s.referenceLog μ P t-s.logCost A μ P t := by
  have hA0 := zero_lt_one.trans hA
  cases s with
  | scalar I => simp only [rate,referenceLog,logCost,Real.log_exp]; ring
  | positive s => exact WorkingAssembly.log_rate hA hs
  | leadingBlock I c s =>
    rw [rate,Real.log_div (WorkingAssembly.rate_positive hA hs).ne'
      (pow_ne_zero 2 (workingBlockFactor_positive hA0 μ _).ne'),Real.log_pow,
      log_workingBlockFactor hA0,WorkingAssembly.log_rate hA hs]
    simp only [referenceLog,logCost]
    ring
  | leadingEnd I c =>
    rw [rate,log_openTerminalRate]
    simp only [referenceLog,logCost]
    ring

theorem eventually_phaseValid : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CompleteCutAssembly, s.WellFormed good → ∀ t : List ℝ,
      (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) → s.PhaseValid A μ T P t := by
  filter_upwards [CutAssembly.eventually_valid_erase] with A hvalid
  intro μ T P good hW s hs t ht hcritical
  cases s with
  | scalar I => trivial
  | leadingEnd I c => trivial
  | positive s =>
    apply hvalid μ T P good hW s hs t ht
    change ∀ a ∈ s.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0 at hcritical
    simpa only [CutAssembly.erase_word] using hcritical
  | leadingBlock I c s =>
    apply hvalid μ T P good hW s hs.2 t ht
    intro a ha
    rw [CutAssembly.erase_word] at ha
    apply hcritical a
    rw [prefix_word]
    exact List.mem_append_right _ ha

theorem eventually_stable_reference_log : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CompleteCutAssembly, s.WellFormed good → ∀ t : List ℝ,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ*A ≤ 1/2 →
      (∀ a ∈ t, 0 < a → a ≤ A) → (∀ a ∈ s.word t, 1-μ*a ≠ 0) → D κ (s.word t) ≤ 1 →
      2*s.referenceLog μ P t ≤ s.logCost A μ P t := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_phaseValid,eventually_distance_lower] with A hA hvalid hlower
  intro κ μ T P good hW s hs t hκ hμ hμ1 hcap ht hcritical hD
  have hv := hvalid μ T P good hW s hs t ht hcritical
  have hl := (hlower κ μ T P good hW s hs t hκ hμ hμ1 hcap ht hcritical).trans hD
  have hr := rate_positive hA hv
  have hr1 := ENNReal.toReal_mono ENNReal.one_ne_top hl
  simp only [ENNReal.toReal_ofReal hr.le,ENNReal.toReal_one] at hr1
  have hh := Real.log_le_log hr hr1
  rw [Real.log_one,log_rate hA hv] at hh
  linarith only [hh]

end
end StrongSilver.CompleteCutAssembly
