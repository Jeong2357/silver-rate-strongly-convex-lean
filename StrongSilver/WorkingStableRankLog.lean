-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingMarkedCount
import StrongSilver.CutRankBudgets
import StrongSilver.StableCutLogBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2800000

def workingRankLogError (Cneg Ctail A B μ σ τ υ W critical : ℝ) : ℝ :=
  6*μ*(W*B^(1-nu)/(1-nu))+
    152*Real.log A*(W*(A^(1+σ))^(-nu)+(W*A^(1-nu)/(1-nu))/A^(1+τ)+
      Cneg*W*(A^(1+υ))^(-nu)/((1/250)*Real.log A))+
    critical+2*Ctail*W*(A^(1+σ))^(-nu)*Real.log (Real.exp 1+A^(1+σ))+
    2*(W*A^(1-nu)/(1-nu))/A^(1+τ)

/-- Actual working-cut trajectories and the rank budgets imply the log
lower bound used in the first-cut reserve argument. -/
theorem eventually_working_stable_rank_log {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∃ Cneg > 0, ∃ Ctail > 0, ∀ᶠ A : ℝ in atTop, ∀ κ B cap μ P critical : ℝ, ∀ C : ScheduleCut,
      1 < κ → A ≤ B → B ≤ cap → cap ≤ κ → A^(1+σ) ≤ cap → A^(1+υ) ≤ cap →
      1/κ ≤ μ → μ ≤ 2/κ → μ*A^(1+υ) ≤ 31/32 → μ*B ≤ 1/2 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ C.phases, A^((499 : ℝ)/500) ≤ q.pivot) → (∀ q ∈ C.phases, 2*P ≤ q.pivot) →
      (∀ b ∈ C.unselected, 0 < b → b ≤ A) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
      inverseChargeAbove (κ/4) C.word μ ≤ critical → D κ C.word ≤ 1 →
      -1200*(C.phases.length : ℝ)/Real.log A-
        workingRankLogError Cneg Ctail A B μ σ τ υ (weightedCount C.word cap) critical ≤
      cutLogProduct (cappedStep μ B) P κ C-Real.log κ := by
  obtain ⟨Cneg,hCneg,hmarks⟩ := stable_cut_three_test_rank_bound
  obtain ⟨Ctail,hCtail,htail⟩ := stable_large_log_e_bound
  refine ⟨Cneg,hCneg,Ctail,hCtail,?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    eventually_working_cut_numerical_bound hσ hσmax hτ hτmax hσυ hτυ hυmax] with A hA hbound
  intro κ B cap μ P critical C hκ hAB hBcap hcapκ hLcap hTcap hμ hμu hμT hcap hPL hPU hpiv hpiv2 hgap hcrit hcritical hD
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hB := hA0.trans_le hAB
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hP : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le hPL
  have hlog := Real.log_pos hA1
  have hM : 0 < A^(1+τ) := Real.rpow_pos_of_pos hA0 _
  have hL : 4 ≤ A^(1+σ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA1.le (show (1 : ℝ) ≤ 1+σ by linarith only [hσ])
    exact hA.trans (by simpa only [Real.rpow_one] using hh)
  have hT : 4 ≤ A^(1+υ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA1.le (show (1 : ℝ) ≤ 1+υ by linarith only [hσ,hσυ])
    exact hA.trans (by simpa only [Real.rpow_one] using hh)
  have hgapPhase : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A :=
    fun _ hq b hb => hgap b ((ScheduleCut.gap_sublist_unselected hq).subset hb)
  have ht : ∀ b ∈ C.terminal, 0 < b → b ≤ A :=
    fun b hb => hgap b (C.terminal_sublist_unselected.subset hb)
  have hlower := hbound κ μ P C hκ.le hμ hμu hμT hPL hPU hpiv hgapPhase ht hcrit
  have hgapB : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b ≤ B := by
    intro q hq b hb
    by_cases hb0 : 0 < b
    · exact (hgapPhase q hq b hb hb0).trans hAB
    · exact (le_of_not_gt hb0).trans hB.le
  have hstable := stable_full_capped_cut_log hκ0 hμ0 hB hcap hP C hpiv2 hgapB hlower hD
  have hmark := hmarks κ A (A^(1+σ)) (A^(1+τ)) (A^(1+υ)) ((1/250)*Real.log A) cap
    hκ hA0 (hAB.trans hBcap) (lt_of_lt_of_le (by norm_num) hL) hLcap hM hT (hTcap.trans hcapκ) hTcap
    (by positivity) C hgap hD
  change (badPhaseCount (workingPhaseTests A σ τ υ) C.phases : ℝ) ≤ _ at hmark
  have hgrowth := htail κ (A^(1+σ)) cap hκ hL (hLcap.trans hcapκ) hLcap C.word hD
  have hUA := C.unselected_positiveMass_rank_bound hA0 (hAB.trans hBcap) hgap
  have hUB := C.unselected_positiveMass_rank_bound hB hBcap (fun b hb hb0 => (hgap b hb hb0).trans hAB)
  have hclip := clippedMass_rank_bound C.word hB hBcap
  have hm := mul_le_mul_of_nonneg_left hmark (show 0 ≤ 152*Real.log A by positivity)
  have hu := mul_le_mul_of_nonneg_left hUB (show 0 ≤ 2*μ by positivity)
  have hc := mul_le_mul_of_nonneg_left hclip (show 0 ≤ 4*μ by positivity)
  have hdiv := div_le_div_of_nonneg_right hUA hM.le
  have herror : workingNumericalCutLoss A κ μ σ τ υ C/2+4*μ*clippedMass C.word B ≤
      1200*(C.phases.length : ℝ)/Real.log A+
        workingRankLogError Cneg Ctail A B μ σ τ υ (weightedCount C.word cap) critical := by
    unfold workingNumericalCutLoss workingRankLogError
    linear_combination hm+hu+hc+2*hdiv+2*hgrowth+hcritical
  linear_combination hstable+herror

end
end StrongSilver
