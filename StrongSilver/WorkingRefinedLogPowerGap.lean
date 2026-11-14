-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPowerGapError
import StrongSilver.FullCutPaddingRank

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- Uniform logarithmic lower bound for arbitrary refined working cuts.
The selected-count charge is retained explicitly for the refinement
savings test; the remaining rank error is completely discharged. -/
theorem eventually_refined_working_log_power_gap {σ τ υ q : ℝ}
    (hσ : 0 < σ) (hσmax : σ ≤ 1/200) (hτ : 0 < τ) (hτmax : τ ≤ 1/1000)
    (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) (hυq : υ ≤ q) :
    ∀ᶠ A : ℝ in atTop, ∀ κ B cap μ P critical : ℝ, ∀ C : ScheduleCut,
    1 < κ → A^(1+q) ≤ B → B ≤ cap → cap ≤ κ →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    A^((49:ℝ)/50) ≤ P → P ≤ A^((199:ℝ)/200) →
    (∀ p ∈ C.phases, A^((499:ℝ)/500) ≤ p.pivot) →
    (∀ p ∈ C.phases, 2*P ≤ p.pivot) →
    (∀ b ∈ C.unselected, 0 < b → b ≤ A) →
    (∀ b ∈ C.word, 1-μ*b ≠ 0) →
    inverseChargeAbove (κ/4) C.word μ ≤ critical →
    critical ≤ 34*weightedCount C.word cap*cap^(-nu) → D κ C.word ≤ 1 →
    -1200*(C.phases.length:ℝ)/Real.log A-weightedCount C.word cap*A^(-nu)/Real.log A ≤
      cutLogProduct (cappedStep μ B) P κ C-Real.log κ := by
  obtain ⟨Cneg,hCneg,Ctail,hCtail,hlower⟩ := eventually_working_stable_rank_log hσ hσmax hτ hτmax hσυ hτυ hυmax
  have hυ : 0 < υ := hσ.trans hσυ
  have hq : 0 < q := hυ.trans_le hυq
  filter_upwards [hlower,eventually_workingPowerGapMargin_small hq hσ hτ hυ Cneg Ctail,
    eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with A hbound hmargin hA he hlog
  intro κ B cap μ P critical C hκ hgap hBcap hcapκ hμ hμu hμB hPL hPU hpiv hpiv2 hsmall hcrit hcritical hcriticalRank hD
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hlog0 := Real.log_pos hA1
  have hAB : A ≤ B := by
    have hp := Real.rpow_le_rpow_of_exponent_le hA1.le (show (1:ℝ) ≤ 1+q by linarith only [hq])
    have hAA : A ≤ A^(1+q) := by simpa only [Real.rpow_one] using hp
    exact hAA.trans hgap
  have hB0 := hA0.trans_le hAB
  have hAcap := hAB.trans hBcap
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hT : A^(1+υ) ≤ B := (Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith only [hυq])).trans hgap
  have hL : A^(1+σ) ≤ B := (Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith only [hσυ,hυq])).trans hgap
  have hμT : μ*A^(1+υ) ≤ 31/32 := by
    have hh := (mul_le_mul_of_nonneg_left hT hμ0.le).trans hμB
    linarith only [hh]
  have hlow := hbound κ B cap μ P critical C hκ hAB hBcap hcapκ (hL.trans hBcap) (hT.trans hBcap)
    hμ hμu hμT hμB hPL hPU hpiv hpiv2 hsmall hcrit hcritical hD
  have herror := workingRankLogError_power_gap (Cneg := Cneg) (τ := τ) (υ := υ) hA he hlog hB0 hgap hBcap hμ0.le hμB
    (weightedCount_nonneg C.word cap) hCtail.le hσ.le (hσmax.trans (by norm_num)) hcriticalRank
  have herrorSmall := mul_le_mul_of_nonneg_left hmargin
    (mul_nonneg (weightedCount_nonneg C.word cap) (Real.rpow_pos_of_pos hA0 (-nu)).le)
  linear_combination hlow+herror+herrorSmall

end
end StrongSilver
