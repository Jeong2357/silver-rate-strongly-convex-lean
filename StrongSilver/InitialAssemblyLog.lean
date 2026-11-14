-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialAssemblyTrace
import StrongSilver.InitialTraceLogPrices

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

theorem log_ordinaryPhaseProduct {A μ T P : ℝ} (hA : 1 < A) (qs : List CutPhase)
    (hW : ∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap) :
    Real.log (ordinaryPhaseProduct A μ P qs) =
      (qs.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-
        (qs.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum := by
  induction qs with
  | nil => simp [ordinaryPhaseProduct]
  | cons q qs ih =>
    have hq := hW q (by simp)
    have ht : ∀ z ∈ qs, OrdinaryPhaseParameters A μ z.pivot T P z.gap := fun z hz => hW z (List.mem_cons_of_mem q hz)
    have hprod : ordinaryPhaseProduct A μ P (q::qs) = ordinaryReferenceFactor A μ q.pivot P q.gap*ordinaryPhaseProduct A μ P qs := by
      simp [ordinaryPhaseProduct]
    rw [hprod,Real.log_mul (hq.reference_factor_positive hA).ne' (ordinaryPhaseProduct_positive hA ht).ne',
      hq.log_reference_factor hA,ih ht]
    simp only [List.map_cons,List.sum_cons]
    ring

def initialReservedLogPrice (κ B μ : ℝ) (I : List ℝ) : ℝ :=
  Real.log initialEntryConstant+2*Real.log initialBlockConstant+16*Real.log (κ/B)+
    2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ)

def initialTerminalLogPrice (κ B μ : ℝ) (I t : List ℝ) : ℝ :=
  4*μ*Scalar.SignedIntervals.positiveMass t+Real.log (4*initialEntryConstant*(1200000 : ℝ)^2)+6*Real.log (κ/B)+
    2*inverseCharge μ I+2*Real.log (1+smallPositiveSum μ I/κ)

def initialNoConnectorLogPrice (κ B μ : ℝ) (I t : List ℝ) : ℝ :=
  2*inverseCharge μ I+4*μ*Scalar.SignedIntervals.positiveMass t+Real.log (2*initialEntryConstant)+4*Real.log (κ/B)

namespace InitialCutAssembly

def referenceLog (μ P : ℝ) (refine : CutPhase → List CutPhase) : InitialCutAssembly → ℝ
  | .terminal => 0
  | .tracked q s => ((refine q).map fun z => Real.log ((z.pivot-P)/(transformedGapMaximum μ z.gap+P))).sum+s.referenceLog μ P refine
  | .block _ _ _ _ s => s.referenceLog μ P refine
  | .terminalBlock _ _ _ => 0
  | .noConnector _ _ => 0

def logCost (A κ B μ P : ℝ) (refine : CutPhase → List CutPhase) (t : List ℝ) : InitialCutAssembly → ℝ
  | .terminal => 4*μ*Scalar.SignedIntervals.positiveMass t
  | .tracked q s => 2*((refine q).map fun z => 1200/Real.log A+μ*transformedGapMaximum μ z.gap).sum+s.logCost A κ B μ P refine t
  | .block _ I c _ s => initialReservedLogPrice κ B μ (I.flatMap CutPhase.word++c.gap)+s.logCost A κ B μ P refine t
  | .terminalBlock _ I c => initialTerminalLogPrice κ B μ (I.flatMap CutPhase.word++c.gap) t
  | .noConnector _ I => initialNoConnectorLogPrice κ B μ (I.flatMap CutPhase.word) t

theorem referenceLog_eq_sum (μ P : ℝ) (refine : CutPhase → List CutPhase) (s : InitialCutAssembly) :
    s.referenceLog μ P refine = ((s.trackedPhases.flatMap refine).map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum := by
  induction s <;> simp_all [referenceLog,trackedPhases,List.map_append,List.sum_append]

theorem rate_positive {A κ B μ T P : ℝ} {refine : CutPhase → List CutPhase} {t : List ℝ} {s : InitialCutAssembly}
    (hA : 1 < A) (hκ : 0 < κ) (hB : 0 < B) (hs : s.Valid A κ B μ T P refine) : 0 < s.rate A κ B μ P refine t := by
  induction s with
  | terminal => exact Real.exp_pos _
  | tracked q s ih => exact mul_pos (ih hs.2) (sq_pos_of_pos (ordinaryPhaseProduct_positive hA hs.1))
  | block q I c d s ih => exact initialReservedRate_positive hκ hB (ih hs.2.2.2.2.2.2.2) μ _
  | terminalBlock q I c => exact initialTerminalRate_positive hκ hB μ _ t
  | noConnector q I => exact initialNoConnectorRate_positive hκ hB μ _ t

theorem log_rate {A κ B μ T P : ℝ} {refine : CutPhase → List CutPhase} {t : List ℝ} {s : InitialCutAssembly}
    (hA : 1 < A) (hκ : 0 < κ) (hB : 0 < B) (hs : s.Valid A κ B μ T P refine) :
    Real.log (s.rate A κ B μ P refine t) = 2*s.referenceLog μ P refine-s.logCost A κ B μ P refine t := by
  induction s with
  | terminal => simp only [rate,referenceLog,logCost,Real.log_exp]; ring
  | tracked q s ih =>
    rw [rate,Real.log_mul (rate_positive hA hκ hB hs.2).ne' (pow_ne_zero 2 (ordinaryPhaseProduct_positive hA hs.1).ne'),
      Real.log_pow,log_ordinaryPhaseProduct hA _ hs.1,ih hs.2]
    simp only [referenceLog,logCost]
    ring
  | block q I c d s ih =>
    have hv := hs.2.2.2.2.2.2.2
    rw [rate,log_initialReservedRate hκ hB (rate_positive hA hκ hB hv),ih hv]
    simp only [referenceLog,logCost,initialReservedLogPrice]
    ring
  | terminalBlock q I c =>
    rw [rate,log_initialTerminalRate hκ hB]
    simp only [referenceLog,logCost,initialTerminalLogPrice]
    ring
  | noConnector q I =>
    rw [rate,log_initialNoConnectorRate hκ hB]
    simp only [referenceLog,logCost,initialNoConnectorLogPrice]
    ring

end InitialCutAssembly
end
end StrongSilver
