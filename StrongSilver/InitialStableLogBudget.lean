-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedCompressedCut
import StrongSilver.InitialStableRefinedLog
import StrongSilver.InitialMarkedLogBudget

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

def initialStablePriceConstant : ℝ := 7*(initialLogPriceConstant+6)/2+32

theorem initialStablePriceConstant_positive : 0 < initialStablePriceConstant := by
  have hh := initialLogPriceConstant_positive
  unfold initialStablePriceConstant
  positivity

def initialMarkedLogCoefficient (a : ℝ) : ℝ :=
  initialMarkedRankConstant*Real.sqrt a*(1+Real.log (1/a)+1/nu)+(a/(1-nu))*(2+Real.log (1/a))

def initialStableErrorCoefficient (a : ℝ) : ℝ :=
  ((63/8)/(1-nu))*a+initialStablePriceConstant*initialMarkedLogCoefficient a

/-- All reserved costs use the original marked count and original mass;
renumbering the tracked phases introduces no additional charge. -/
theorem initialStableLogRemainder_bound {κ B μ cap : ℝ} (hκ : 0 < κ) (hB : 0 < B)
    (hBκ : B ≤ κ) (hBcap : B ≤ cap) (hμ : 0 ≤ μ) (C : ScheduleCut) (R : InitialReservation κ B μ C)
    (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B)
    (hlarge : largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)) :
    initialStableLogRemainder κ B μ (initialMarkedGood κ B μ) R.assembly C.terminal ≤
      7*μ*(weightedCount C.word cap*B^(1-nu)/(1-nu))+
        initialStablePriceConstant*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B)) := by
  have hmass := C.unselected_positiveMass_rank_bound hB hBcap hgap
  have hclip := clippedMass_rank_bound C.word hB hBcap
  have hbad : (badPhaseCount (initialMarkedGood κ B μ) R.assembly.phases : ℝ) ≤
      (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by exact_mod_cast R.bad_count
  have hlog := Real.log_nonneg ((one_le_div hB).mpr hBκ)
  have hprice0 : 0 ≤ 7*(initialLogPriceConstant+6)/2 := by have hh := initialLogPriceConstant_positive; positivity
  have hp := mul_le_mul_of_nonneg_left hbad (show 0 ≤ (7*(initialLogPriceConstant+6)/2)*(1+Real.log (κ/B)) by positivity)
  have hj : (0 : ℝ) ≤ (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1+Real.log (κ/B) by linarith only [hlog]) (show 0 ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 3*μ by positivity)
  have hc := mul_le_mul_of_nonneg_left hclip (show 0 ≤ 4*μ by positivity)
  unfold initialStableLogRemainder initialStablePriceConstant
  rw [R.source_word,R.source_gap_mass]
  linear_combination hp+hl+hm+hc+hlarge

/-- The near-cutoff logarithmic remainder, multiplied by B^nu, is bounded
by W times a coefficient depending only on the absolute cap parameter. -/
theorem initialStableLogRemainder_scaled {a κ B μ : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (hB : 0 < B) (hBcap : B ≤ a*κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*κ))
    (C : ScheduleCut) (R : InitialReservation κ B μ C)
    (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) (hD : D κ C.word ≤ 1)
    (hlarge : largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)) :
    B^nu*initialStableLogRemainder κ B μ (initialMarkedGood κ B μ) R.assembly C.terminal ≤
      weightedCount C.word (a*κ)*initialStableErrorCoefficient a := by
  have hcκ : a*κ ≤ κ := by have hh := mul_le_mul_of_nonneg_right hamax hκ.le; nlinarith only [hh,hκ]
  have hb := initialStableLogRemainder_bound hκ hB (hBcap.trans hcκ) hBcap hμ C R hgap hlarge
  have hs := mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hB nu).le
  have hj := initial_marked_log_budget ha hamax hκ hcap hB hBcap C hgap hD
  have hjs := mul_le_mul_of_nonneg_left hj initialStablePriceConstant_positive.le
  have hmass : B^nu*B^(1-nu) = B := by rw [← Real.rpow_add hB,show nu+(1-nu) = (1 : ℝ) by ring,Real.rpow_one]
  have hμB : μ*B ≤ (9/8)*a := by
    have hh := mul_le_mul hμu hBcap hB.le (by positivity : 0 ≤ 9/(8*κ))
    calc
      _ ≤ (9/(8*κ))*(a*κ) := hh
      _ = _ := by field_simp <;> ring
  have hd : 0 < 1-nu := by linarith [nu_lt_one]
  have hW := weightedCount_nonneg C.word (a*κ)
  have hcurv := mul_le_mul_of_nonneg_right hμB (show 0 ≤ (7/(1-nu))*weightedCount C.word (a*κ) by positivity)
  have hscaled : B^nu*(7*μ*(weightedCount C.word (a*κ)*B^(1-nu)/(1-nu))) =
      (7/(1-nu))*weightedCount C.word (a*κ)*(μ*B) := by
    calc
      _ = (7/(1-nu))*weightedCount C.word (a*κ)*μ*(B^nu*B^(1-nu)) := by ring
      _ = _ := by rw [hmass]; ring
  unfold initialStableErrorCoefficient initialMarkedLogCoefficient
  linear_combination hs+hjs+hcurv+hscaled

end
end StrongSilver
