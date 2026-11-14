-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPowerGapError

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 6800000

/-- A uniform marked-phase rank bound sufficient for the reservation
count. All ordinary-phase tests and numerical errors are discharged
from the original stable signed schedule. -/
theorem eventually_working_marked_rank_decay {σ τ υ q : ℝ}
    (hσ : 0 < σ) (hσmax : σ ≤ 1/200) (hτ : 0 < τ) (hτmax : τ ≤ 1/1000)
    (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) (hυq : υ ≤ q) :
    ∀ᶠ A : ℝ in atTop, ∀ κ B cap μ P : ℝ, ∀ C : ScheduleCut,
    1 < κ → A^(1+q) ≤ B → B ≤ cap → cap ≤ κ →
    0 < μ → μ*B ≤ 1/2 → A^((49:ℝ)/50) ≤ P → P ≤ A^((199:ℝ)/200) →
    (∀ p ∈ C.phases, A^((499:ℝ)/500) ≤ p.pivot) →
    (∀ b ∈ C.unselected, 0 < b → b ≤ A) → D κ C.word ≤ 1 →
    (badPhaseCount (ordinaryPhaseGood A μ (A^(1+υ)) P) C.phases:ℝ) ≤
      weightedCount C.word cap*A^(-nu)/Real.log A := by
  obtain ⟨Cn,hCn,hmarks⟩ := stable_cut_three_test_rank_bound
  have hυ : 0 < υ := hσ.trans hσυ
  have hq : 0 < q := hυ.trans_le hυq
  filter_upwards [eventually_working_marked_count hσ hσmax hτ hτmax hσυ hτυ hυmax,
    eventually_workingPowerGapMargin_small hq hσ hτ hυ Cn 0,eventually_ge_atTop (4:ℝ),
    eventually_ge_atTop (Real.exp 1),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with A hMarked hMargin hA he hlog
  intro κ B cap μ P C hκ hgap hBcap hcapκ hμ hμB hPL hPU hpiv hsmall hD
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hAB : A ≤ B := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA1.le (show (1:ℝ) ≤ 1+q by linarith only [hq])
    exact (by simpa only [Real.rpow_one] using hh : A ≤ A^(1+q)).trans hgap
  have hB := hA0.trans_le hAB
  have hLcap : A^(1+σ) ≤ cap :=
    ((Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith only [hσυ,hυq])).trans hgap).trans hBcap
  have hTcap : A^(1+υ) ≤ cap :=
    ((Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith only [hυq])).trans hgap).trans hBcap
  have hTκ := hTcap.trans hcapκ
  have hTAB : A^(1+υ) ≤ B := (Real.rpow_le_rpow_of_exponent_le hA1.le (by linarith only [hυq])).trans hgap
  have hμT : μ*A^(1+υ) ≤ 31/32 := by
    have hh := (mul_le_mul_of_nonneg_left hTAB hμ.le).trans hμB
    linarith only [hh]
  have hT : 4 ≤ A^(1+υ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA1.le (show (1:ℝ) ≤ 1+υ by linarith only [hυ])
    exact hA.trans (by simpa only [Real.rpow_one] using hh)
  have hM : 0 < A^(1+τ) := Real.rpow_pos_of_pos hA0 _
  have hL : 0 < A^(1+σ) := Real.rpow_pos_of_pos hA0 _
  have hF : 0 < (1/250:ℝ)*Real.log A := by positivity
  have hWord : (∀ p ∈ C.phases, ∀ b ∈ p.gap, 0 < b → b ≤ A) :=
    fun p hp b hb => hsmall b ((ScheduleCut.gap_sublist_unselected hp).subset hb)
  have hCompare := hMarked μ P C.phases hμ hμT hPL hPU hpiv hWord
  have hCount := hmarks κ A (A^(1+σ)) (A^(1+τ)) (A^(1+υ)) ((1/250)*Real.log A) cap
    hκ hA0 (hAB.trans hBcap) hL hLcap hM hT hTκ hTcap hF C hsmall hD
  change (badPhaseCount (workingPhaseTests A σ τ υ) C.phases:ℝ) ≤ _ at hCount
  let W := weightedCount C.word cap
  let R := W*(A^(1+σ))^(-nu)+(W*A^(1-nu)/(1-nu))/A^(1+τ)+Cn*W*(A^(1+υ))^(-nu)/((1/250)*Real.log A)
  have hW : 0 ≤ W := weightedCount_nonneg C.word cap
  have hDen : 0 < 1-nu := sub_pos.mpr nu_lt_one
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hScale := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 152*Real.log A by linarith only [hlog]) hR
  have hTail : 0 ≤ 2*(W*A^(1-nu)/(1-nu))/A^(1+τ) := by positivity
  have hError : (badPhaseCount (workingPhaseTests A σ τ υ) C.phases:ℝ) ≤
      workingRankLogError Cn 0 A B 0 σ τ υ W 0 := by
    unfold workingRankLogError
    simp only [zero_mul,mul_zero,zero_add,add_zero]
    change _ ≤ 152*Real.log A*R+2*(W*A^(1-nu)/(1-nu))/A^(1+τ)
    change _ ≤ R at hCount
    linear_combination hCount+hScale+hTail
  have hcap0 : 0 < cap := hB.trans_le hBcap
  have hA2 : 2 ≤ A := (by norm_num : (2:ℝ) ≤ 4).trans hA
  have hErrorUpper := workingRankLogError_power_gap (Cneg:=Cn) (Ctail:=0) (σ:=σ) (τ:=τ) (υ:=υ) (q:=q)
    (W:=W) (critical:=0) (μ:=0) hA2 he hlog hB hgap hBcap (le_refl (0:ℝ)) (by norm_num) hW
    (le_refl (0:ℝ)) hσ.le (hσmax.trans (by norm_num)) (by positivity)
  have hSmall := mul_le_mul_of_nonneg_left hMargin (mul_nonneg hW (Real.rpow_pos_of_pos hA0 (-nu)).le)
  have hCompareReal : (badPhaseCount (ordinaryPhaseGood A μ (A^(1+υ)) P) C.phases:ℝ) ≤
      (badPhaseCount (workingPhaseTests A σ τ υ) C.phases:ℝ) := by exact_mod_cast hCompare
  change _ ≤ W*A^(-nu)/Real.log A
  linear_combination hCompareReal+hError+hErrorUpper+hSmall

end
end StrongSilver
