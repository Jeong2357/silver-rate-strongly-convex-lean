-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteInitialCutTrace
import StrongSilver.InitialAssemblyLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

theorem initialOpenTerminalRate_positive {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    0 < initialOpenTerminalRate κ B μ I t := by
  have hK := div_pos hκ hB
  have hS := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le
  unfold initialOpenTerminalRate
  positivity

theorem log_initialOpenTerminalRate {κ B : ℝ} (hκ : 0 < κ) (hB : 0 < B) (μ : ℝ) (I t : List ℝ) :
    Real.log (initialOpenTerminalRate κ B μ I t) = -4*μ*Scalar.SignedIntervals.positiveMass t-
      (Real.log (4*(1200000 : ℝ)^2)+2*Real.log (κ/B)+2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ)) := by
  have hK := div_pos hκ hB
  have hs : 0 < 1+smallPositiveSum μ I/κ := by have hh := div_nonneg (smallPositiveSum_nonneg μ I) hκ.le; linarith only [hh]
  have he : 4*(1200000*(κ/B))^2 = (4*(1200000 : ℝ)^2)*(κ/B)^2 := by ring
  rw [initialOpenTerminalRate,he,Real.log_div (Real.exp_ne_zero _) (by positivity),Real.log_exp,
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_mul (Real.exp_ne_zero _) hs.ne',Real.log_exp]
  norm_num
  ring

namespace CompleteInitialCutAssembly

def referenceLog (μ P : ℝ) (choose : ℕ → ℝ → Bool) : CompleteInitialCutAssembly → ℝ
  | .scalar _ => 0
  | .positive s => s.referenceLog μ P (refinePhase choose)
  | .leadingBlock _ _ _ s => s.referenceLog μ P (refinePhase choose)
  | .leadingEnd _ _ => 0

def logCost (A κ B μ P : ℝ) (choose : ℕ → ℝ → Bool) (t : List ℝ) : CompleteInitialCutAssembly → ℝ
  | .scalar I => 2*inverseCharge μ (I.flatMap CutPhase.word)+4*μ*Scalar.SignedIntervals.positiveMass t
  | .positive s => s.logCost A κ B μ P (refinePhase choose) t
  | .leadingBlock I c _ s => initialReservedLogPrice κ B μ (I.flatMap CutPhase.word++c.gap)+s.logCost A κ B μ P (refinePhase choose) t
  | .leadingEnd I c => 4*μ*Scalar.SignedIntervals.positiveMass t+Real.log (4*(1200000 : ℝ)^2)+2*Real.log (κ/B)+
      2*inverseCharge μ (I.flatMap CutPhase.word++c.gap)+2*Real.log (1+smallPositiveSum μ (I.flatMap CutPhase.word++c.gap)/κ)

def PhaseValid (A κ B μ T P : ℝ) (choose : ℕ → ℝ → Bool) : CompleteInitialCutAssembly → Prop
  | .scalar _ => True
  | .positive s => s.Valid A κ B μ T P (refinePhase choose)
  | .leadingBlock _ _ _ s => s.Valid A κ B μ T P (refinePhase choose)
  | .leadingEnd _ _ => True

theorem referenceLog_eq_sum (μ P : ℝ) (choose : ℕ → ℝ → Bool) (s : CompleteInitialCutAssembly) :
    s.referenceLog μ P choose = ((s.trackedPhases.flatMap (refinePhase choose)).map
      fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum := by
  cases s <;> simp only [referenceLog,trackedPhases,InitialCutAssembly.referenceLog_eq_sum,List.flatMap_nil,List.map_nil,List.sum_nil]

theorem rate_positive {A κ B μ T P : ℝ} {choose : ℕ → ℝ → Bool} {t : List ℝ} {s : CompleteInitialCutAssembly}
    (hA : 1 < A) (hκ : 0 < κ) (hB : 0 < B) (hs : s.PhaseValid A κ B μ T P choose) : 0 < s.rate A κ B μ P choose t := by
  cases s with
  | scalar I => exact Real.exp_pos _
  | positive s => exact InitialCutAssembly.rate_positive hA hκ hB hs
  | leadingBlock I c d s => exact initialReservedRate_positive hκ hB (InitialCutAssembly.rate_positive hA hκ hB hs) μ _
  | leadingEnd I c => exact initialOpenTerminalRate_positive hκ hB μ _ t

theorem log_rate {A κ B μ T P : ℝ} {choose : ℕ → ℝ → Bool} {t : List ℝ} {s : CompleteInitialCutAssembly}
    (hA : 1 < A) (hκ : 0 < κ) (hB : 0 < B) (hs : s.PhaseValid A κ B μ T P choose) :
    Real.log (s.rate A κ B μ P choose t) = 2*s.referenceLog μ P choose-s.logCost A κ B μ P choose t := by
  cases s with
  | scalar I => simp only [rate,referenceLog,logCost,Real.log_exp]; ring
  | positive s => exact InitialCutAssembly.log_rate hA hκ hB hs
  | leadingBlock I c d s =>
    rw [rate,log_initialReservedRate hκ hB (InitialCutAssembly.rate_positive hA hκ hB hs),InitialCutAssembly.log_rate hA hκ hB hs]
    simp only [referenceLog,logCost,initialReservedLogPrice]
    ring
  | leadingEnd I c =>
    rw [rate,log_initialOpenTerminalRate hκ hB]
    simp only [referenceLog,logCost]
    ring

theorem eventually_phaseValid : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ T P : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → InitialPhaseBudget B μ q.pivot T κ B q.gap) →
      ∀ s : CompleteInitialCutAssembly, s.WellFormed good → ∀ choose : ℕ → ℝ → Bool, ∀ t : List ℝ,
      A ≤ B → 2 ≤ B → κ ≤ A^((1003 : ℝ)/1000) →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ i b, choose i b = true → A ≤ b) → (∀ i b, choose i b = false → 0 < b → b ≤ A) →
      (∀ a ∈ s.word t, 1-μ*a ≠ 0) → s.PhaseValid A κ B μ T P choose := by
  filter_upwards [eventually_initial_refined_parameters] with A hparams
  intro κ B μ T P good hW s hs choose t hAB hB hκA hPL hPU hselected hunselected hcritical
  have buildValid (S : InitialCutAssembly) (hS : S.WellFormed good)
      (hcrit : ∀ a ∈ S.phases.flatMap CutPhase.word++t, 1-μ*a ≠ 0) : S.Valid A κ B μ T P (refinePhase choose) := by
    apply S.valid_of_wellFormed hB hW hS (refinePhase choose) ?_ t hcrit
    intro q hq
    exact hparams κ B μ T P q choose hAB hκA hPL hPU (hW q (S.tracked_good hS q hq)) hselected hunselected
  cases s with
  | scalar I => trivial
  | leadingEnd I c => trivial
  | positive S => exact buildValid S hs hcritical
  | leadingBlock I c d S =>
    apply buildValid S hs.2.2
    intro a ha
    apply hcritical a
    rw [leading_word]
    exact List.mem_append_right _ (List.mem_append_right _ ha)

end CompleteInitialCutAssembly
end
end StrongSilver
