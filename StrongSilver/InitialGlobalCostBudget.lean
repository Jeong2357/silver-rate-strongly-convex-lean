-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteInitialCost

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2400000

theorem CompleteInitialCutAssembly.mem_reserved {s : CompleteInitialCutAssembly} {q : CutPhase}
    (hq : q ∈ s.reserved) : q ∈ s.phases := by
  have aux {S : InitialCutAssembly} {z : CutPhase} (hz : z ∈ S.reserved) : z ∈ S.phases := by
    induction S <;> simp only [InitialCutAssembly.reserved,InitialCutAssembly.phases,List.mem_cons,
      List.mem_append,List.mem_singleton,List.not_mem_nil] at * <;> aesop
  cases s with
  | scalar I => exact hq
  | positive S => exact aux hq
  | leadingBlock I c d S =>
    simp only [reserved,List.mem_append,List.mem_cons] at hq
    simp only [phases,List.mem_append,List.mem_cons]
    rcases hq with hI | rfl | rfl | hs
    · exact Or.inl hI
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (aux hs)))
  | leadingEnd I c => exact hq

theorem CompleteInitialCutAssembly.tracked_good {good : CutPhase → Bool} {s : CompleteInitialCutAssembly}
    (hs : s.WellFormed good) : ∀ q ∈ s.trackedPhases, good q = true := by
  cases s with
  | scalar I => simp [trackedPhases]
  | positive S => exact S.tracked_good hs
  | leadingBlock I c d S => exact S.tracked_good hs.2.2
  | leadingEnd I c => simp [trackedPhases]

/-- The total initial-block loss is controlled by the original unselected
mass and the marked count, even after arbitrary tracked-only refinement. -/
theorem CompleteInitialCutAssembly.logCost_global_budget {A κ B μ T P : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hB : 0 < B) (hK : 1 ≤ κ/B)
    (hμ : 1/κ ≤ μ) (hμu : μ ≤ 9/(8*κ)) (hcap : μ*B ≤ 1/2)
    (good : CutPhase → Bool) (s : CompleteInitialCutAssembly) (hs : s.WellFormed good) (hc : s.Counted good)
    (choose : ℕ → ℝ → Bool) (t : List ℝ)
    (hOrd : ∀ q ∈ s.trackedPhases.flatMap (refinePhase choose), OrdinaryPhaseParameters A μ q.pivot T P q.gap)
    (hgap : ∀ q ∈ s.reserved, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    s.logCost A κ B μ P choose t ≤
      2400*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A+
      6*μ*(phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t)+
      (7*(initialLogPriceConstant+6))*(badPhaseCount good s.phases : ℝ)*(1+Real.log (κ/B))+
      2*largeInverseCharge κ (s.word t) μ := by
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ).trans_le hμ
  let R := phaseGapMass s.reserved
  let N := (s.reserved.length : ℝ)
  let J := (badPhaseCount good s.phases : ℝ)
  let L := 1+Real.log (κ/B)
  let U := phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t
  have hL : 1 ≤ L := by have hh := Real.log_nonneg hK; dsimp only [L]; linarith only [hh]
  have hL0 := zero_lt_one.trans_le hL
  have hC := initialLogPriceConstant_positive
  have hraw := s.logCost_raw hκ hB hK A μ P choose t
  have hord := ordinary_cost_sum_le hA hμ0.le (s.trackedPhases.flatMap (refinePhase choose)) hOrd
  have hinv := (s.block_inverse_bound μ).trans (s.reserved_inverse_budget hκ hμ0.le hμu hcap t hgap)
  have hgrowth := s.block_growth_budget hκ hμ
  have hR0 : 0 ≤ R := phaseGapMass_nonnegative _
  have hRμ : R/κ ≤ μ*R := by
    have hh := mul_le_mul_of_nonneg_right hμ hR0
    have he : (1/κ)*R = R/κ := by ring
    rwa [he] at hh
  have hMass := s.refined_gapMass_budget choose
  have hMassScaled := mul_le_mul_of_nonneg_left hMass (show 0 ≤ 6*μ by positivity)
  have hTr := mul_nonneg hμ0.le (phaseGapMass_nonnegative (s.trackedPhases.flatMap (refinePhase choose)))
  have hTerm := mul_nonneg hμ0.le (Scalar.SignedIntervals.positiveMass_nonneg t)
  have hCurv : 4*μ*phaseGapMass (s.trackedPhases.flatMap (refinePhase choose))+6*μ*R+
      4*μ*Scalar.SignedIntervals.positiveMass t ≤ 6*μ*U := by
    dsimp only [R,U]
    nlinarith only [hMassScaled,hTr,hTerm]
  have hBcount : (s.blockCount : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast s.blockCount_le_reserved
  have hBcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBcount hC.le) hL0.le
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNcost : 6*N ≤ 6*N*L := by nlinarith only [mul_nonneg hN0 (show 0 ≤ L-1 by linarith only [hL])]
  have hNbound : N ≤ 7*J := by dsimp only [N,J]; exact_mod_cast s.reserved_count_bound hs hc
  have hJcost : (initialLogPriceConstant+6)*N*L ≤ (7*(initialLogPriceConstant+6))*J*L := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNbound (by linarith only [hC] : 0 ≤ initialLogPriceConstant+6)) hL0.le
    nlinarith only [hh]
  change 2*((s.trackedPhases.flatMap (refinePhase choose)).map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum ≤
    2400*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A+
      4*μ*phaseGapMass (s.trackedPhases.flatMap (refinePhase choose)) at hord
  change (s.blockWords.map fun I => inverseCharge μ I).sum ≤ 2*μ*R+2*N+largeInverseCharge κ (s.word t) μ at hinv
  change (s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum ≤ R/κ+N at hgrowth
  change s.logCost A κ B μ P choose t ≤
    2400*((s.trackedPhases.flatMap (refinePhase choose)).length : ℝ)/Real.log A+6*μ*U+
      (7*(initialLogPriceConstant+6))*J*L+2*largeInverseCharge κ (s.word t) μ
  change s.logCost A κ B μ P choose t ≤
    2*((s.trackedPhases.flatMap (refinePhase choose)).map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
    4*μ*Scalar.SignedIntervals.positiveMass t+initialLogPriceConstant*(s.blockCount : ℝ)*L+
    2*(s.blockWords.map fun I => inverseCharge μ I).sum+2*(s.blockWords.map fun I => Real.log (1+smallPositiveSum μ I/κ)).sum at hraw
  nlinarith only [hraw,hord,hinv,hgrowth,hRμ,hCurv,hBcost,hNcost,hJcost]

end
end StrongSilver
