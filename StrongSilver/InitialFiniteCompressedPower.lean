-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UniformInitialCutLog
import StrongSilver.InitialTrackedPowerReserve
import StrongSilver.CompressedPowerFromReserve

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

theorem initialStableErrorCoefficient_nonnegative {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1) :
    0 ≤ initialStableErrorCoefficient a := by
  have hd : 0 < 1-nu := by linarith [nu_lt_one]
  have hn := nu_positive
  have hc := initialMarkedRankConstant_positive
  have hp := initialStablePriceConstant_positive
  have hl := Real.log_nonneg ((one_le_div ha).mpr hamax)
  unfold initialStableErrorCoefficient initialMarkedLogCoefficient
  positivity

/-- The initial tracked reserve survives every eligible insertion; the
entire non-count remainder is paid by the absolute cap coefficient. -/
theorem eventually_initial_finite_compressed_power : ∀ᶠ A : ℝ in atTop,
    ∀ a κ B μ P : ℝ, ∀ C : ScheduleCut, ∀ R : InitialReservation κ B μ C,
      0 < a → a ≤ 1/128 → 1 ≤ a*κ → A < B → 2 ≤ B → B ≤ a*κ → κ ≤ A^((1003 : ℝ)/1000) → 1 ≤ κ →
      1/κ ≤ μ → μ ≤ 9/(8*κ) → μ*B ≤ 1/2 →
      (∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ P ∧ P ≤ t^((199 : ℝ)/200)) → 2*P ≤ A →
      (∀ q ∈ C.phases, B ≤ q.pivot) → (∀ b ∈ C.unselected, b < B) →
      (∀ b ∈ C.word, 1-μ*b ≠ 0) → D κ C.word ≤ 1 →
      largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) →
      7*initialMarkedLogCoefficient a ≤ 1/2 →
      weightedCount C.word (a*κ) = (C.phases.length : ℝ)*B^nu →
      (powerLogMinimum/4)*weightedCount C.word (a*κ)-splitCoefficient*
        (2*weightedCount C.word (a*κ)*initialStableErrorCoefficient a+
          4*(1200/Real.log A)*weightedCount C.word (a*κ)*(1+Real.log (B/A))) ≤
        cutPower (cappedStep μ B) P 0 (fullCut A R.compressedSchedule)-P^nu := by
  filter_upwards [eventually_uniform_initial_cut_log,eventually_gt_atTop (1 : ℝ)] with A hlog hA
  intro a κ B μ P C R ha hamax hcap hAB hB hBcap hκA hκ hμ hμu hμB hpad hmargin hpiv hgap hcrit hD hlarge hsmall hmax
  have hA0 := zero_lt_one.trans hA
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hcκ : a*κ ≤ κ := by have hh := mul_le_mul_of_nonneg_right hamax hκ0.le; nlinarith only [hh,hκ0]
  have hBκ := hBcap.trans hcκ
  have hP : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le (hpad A le_rfl hAB.le).1
  have hPbase : P ≤ B/2 := by linarith only [hmargin,hAB]
  have hφA : P < cappedStep μ B A := by
    have hh := cappedStep_ge hμ0 (by linarith only [hμB] : μ*B < 1) A
    linarith only [hh,hP,hmargin]
  have hφB : P < cappedStep μ B B := hφA.trans_le (cappedStep_monotone hμ0 (by linarith only [hμB]) hAB.le)
  have hgapPositive : ∀ b ∈ C.unselected, 0 < b → b ≤ B := fun b hb _ => (hgap b hb).le
  have hgapPhase : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b < B :=
    fun q hq b hb => hgap b (ScheduleCut.mem_gap_unselected hq hb)
  have hreserve := (R.initial_reserve_lower ha hamax hκ0 hcap hB0 hBcap hμ0 (by linarith only [hμB]) hPbase
    hgapPositive hD hsmall hmax).trans (R.compressed_initial_reserve hμ0 (by linarith only [hμB]) hP hφB hpiv hgapPhase)
  have hlogs := hlog κ B μ P C R hAB.le hB hBκ hκA hκ hμ hμu hμB hpad hpiv hgapPositive hcrit hD
  let W := weightedCount C.word (a*κ)
  let E := W*initialStableErrorCoefficient a/B^nu
  have hE0 : 0 ≤ E := div_nonneg (mul_nonneg (weightedCount_nonneg C.word (a*κ))
    (initialStableErrorCoefficient_nonnegative ha (hamax.trans (by norm_num)))) (Real.rpow_pos_of_pos hB0 nu).le
  have hscaled := initialStableLogRemainder_scaled ha hamax hκ0 hcap hB0 hBcap hμ0.le hμu C R hgapPositive hD hlarge
  have hErem : initialStableLogRemainder κ B μ (initialMarkedGood κ B μ) R.assembly C.terminal ≤ E := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hB0 nu)).mpr
    linear_combination hscaled
  have hL : let G := R.compressedSchedule
      let ps := orderedPositions G (eligibleIndices G Finset.univ A B)
      ∀ i ≤ ps.length, -E-(1200/Real.log A)*((countAbove G B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P 0 (positionCut (fun _ b => decide (B ≤ b)) G (ps.take i))-Real.log P := by
    dsimp only
    intro i hi
    exact (sub_le_sub_right (neg_le_neg hErem) _).trans (hlogs i hi)
  have hh := compressed_power_from_reserve hμ0 hA0 hAB hBcap hμB hP hφA hE0
    (div_nonneg (by norm_num) (Real.log_pos hA).le) R.compressedSchedule C.word R.compressed_sublist hreserve hL
  have he : E*B^nu = W*initialStableErrorCoefficient a := by
    dsimp only [E]
    field_simp
  linear_combination hh+2*splitCoefficient*he

end
end StrongSilver
