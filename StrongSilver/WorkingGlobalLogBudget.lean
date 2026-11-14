-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutReferenceBudget
import StrongSilver.PhaseGrowthBudget

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

def phaseGapMass (qs : List CutPhase) : ℝ :=
  (qs.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum

theorem phaseGapMass_nonnegative (qs : List CutPhase) : 0 ≤ phaseGapMass qs := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
  exact Scalar.SignedIntervals.positiveMass_nonneg q.gap

theorem CompleteCutAssembly.tracked_length_le (s : CompleteCutAssembly) : s.tracked.length ≤ s.phases.length := by
  have hh := s.length_partition
  omega

/-- The sum of the explicit construction prices has the working-cut form.
The marked count is the number of phases outside the ordinary parameter
class; the next step bounds that count by the three numerical tests. -/
theorem CompleteCutAssembly.eventually_full_log_cost_budget : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P σ τ : ℝ, ∀ good : CutPhase → Bool,
      (∀ q, good q = true → OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : CompleteCutAssembly, s.WellFormed good → s.Counted good → ∀ t : List ℝ,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → μ ≤ 2/κ → μ*A ≤ 1/2 → 1 ≤ P →
      0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 →
      (∀ q ∈ s.phases, P < q.pivot) →
      (∀ q ∈ s.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
      (∀ b ∈ t, 0 < b → b ≤ A) → (∀ b ∈ s.word t, 1-μ*b ≠ 0) →
      2*(s.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-Real.log (s.rate A μ P t) ≤
        2400*(s.phases.length : ℝ)/Real.log A+
        4*μ*(phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t)+
        304*(badPhaseCount good s.phases : ℝ)*Real.log A+
        2*inverseChargeAbove (κ/4) (s.word t) μ+4*largeLogESum (s.word t) (A^(1+σ))+
        4*((phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t)/A^(1+τ)) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    CompleteCutAssembly.eventually_phaseValid,CompleteCutAssembly.eventually_logCost_reserved]
    with A hA hlog hvalid hcost
  intro κ μ T P σ τ good hW s hs hc t hκ hμ hμ1 hμu hcap hP hσ hσ1 hτ hτ1 hpiv hgap ht hcritical
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hlog0 : 0 < Real.log A := zero_lt_one.trans_le hlog
  let U := phaseGapMass s.phases+Scalar.SignedIntervals.positiveMass t
  let R := phaseGapMass s.reserved
  let N := (s.reserved.length : ℝ)
  let J := (badPhaseCount good s.phases : ℝ)
  have hv := hvalid μ T P good hW s hs t ht hcritical
  have hrateLog := s.log_rate (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hA) hv
  have hstab : 2*s.referenceLog μ P t ≤ Real.log (s.rate A μ P t)+s.logCost A μ P t := by linarith only [hrateLog]
  have hrestore := s.reference_restore hμ0 hcap hP t hpiv hgap
  have hraw := hcost μ P s t
  have hord := ordinary_cost_sum_le hA0 hμ0.le s.tracked (fun q hq => hW q (s.tracked_good hs q hq))
  have hinv := s.reserved_inverse_budget hκ0 hμ0.le hμu hcap t
    (fun q hq => hgap q (CompleteCutAssembly.mem_reserved hq))
  have hgrowth := s.reserved_growth_budget hA hσ hσ1 hτ hτ1 t
  have htrackCount : 2400*(s.tracked.length : ℝ)/Real.log A ≤ 2400*(s.phases.length : ℝ)/Real.log A := by
    apply div_le_div_of_nonneg_right _ hlog0.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact_mod_cast s.tracked_length_le
  have hRle : R ≤ U := by
    have hh := s.weight_partition (fun q => Scalar.SignedIntervals.positiveMass q.gap)
    have htr := phaseGapMass_nonnegative s.tracked
    have hterm := Scalar.SignedIntervals.positiveMass_nonneg t
    change phaseGapMass s.phases = phaseGapMass s.tracked+phaseGapMass s.reserved at hh
    dsimp only [R,U]
    linarith only [hh,htr,hterm]
  have hRfrac : 4*(R/A^(1+τ)) ≤ 4*(U/A^(1+τ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hRle (Real.rpow_pos_of_pos hA0 _).le) (by norm_num)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hNbound : N ≤ 4*J := by
    dsimp only [N,J]
    exact_mod_cast s.reserved_count_bound hs hc
  have hB : (s.blockCount : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast s.blockCount_le_reserved
  have hBcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 50)) hlog0.le
  have hNcost : 2*N ≤ 2*N*Real.log A := by nlinarith only [mul_nonneg hN0 (show 0 ≤ Real.log A-1 by linarith only [hlog])]
  have hJcost : 76*N*Real.log A ≤ 304*J*Real.log A := by
    have hh := mul_le_mul_of_nonneg_right hNbound hlog0.le
    nlinarith only [hh]
  have hUeq : 4*μ*(phaseGapMass s.tracked+R+Scalar.SignedIntervals.positiveMass t) = 4*μ*U := by
    have hh := s.weight_partition (fun q => Scalar.SignedIntervals.positiveMass q.gap)
    change phaseGapMass s.phases = phaseGapMass s.tracked+R at hh
    dsimp only [U]
    rw [hh]
  change 2*(s.tracked.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum ≤
    2400*(s.tracked.length : ℝ)/Real.log A+4*μ*phaseGapMass s.tracked at hord
  change inverseCharge μ (s.reserved.flatMap CutPhase.word) ≤ 2*μ*R+N+inverseChargeAbove (κ/4) (s.word t) μ at hinv
  change (s.reserved.map phaseGrowthCharge).sum ≤ 6*N*Real.log A+R/A^(1+τ)+largeLogESum (s.word t) (A^(1+σ)) at hgrowth
  change 2*(s.phases.map fun q => Real.log ((q.pivot-P)/(transformedGapMaximum μ q.gap+P))).sum-Real.log (s.rate A μ P t) ≤
    2400*(s.phases.length : ℝ)/Real.log A+4*μ*U+304*J*Real.log A+
      2*inverseChargeAbove (κ/4) (s.word t) μ+4*largeLogESum (s.word t) (A^(1+σ))+4*(U/A^(1+τ))
  nlinarith only [hstab,hrestore,hraw,hord,hinv,hgrowth,htrackCount,hRfrac,hBcost,hNcost,hJcost,hUeq]

end
end StrongSilver
