-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MaximizingCutRefinement
import StrongSilver.WorkingRefinedLogPowerGap

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4000000

/-- The maximizing refinements in all gaps satisfy (4.7) at once.
Every chosen refinement is an actual cut of the original signed word;
its complete trajectory and rank error come from the working-cut bound. -/
theorem eventually_full_cut_refinement_savings {σ τ υ q : ℝ}
    (hσ : 0 < σ) (hσmax : σ ≤ 1/200) (hτ : 0 < τ) (hτmax : τ ≤ 1/1000)
    (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) (hυq : υ ≤ q) :
    ∀ᶠ A : ℝ in atTop, ∀ κ B cap μ P critical price : ℝ, ∀ h : List ℝ,
    ∀ eligible : ℕ → ℝ → Bool,
    1 < κ → A^(1+q) ≤ B → B ≤ cap → cap ≤ κ →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    A^((49:ℝ)/50) ≤ P → P ≤ A^((199:ℝ)/200) → 2*P ≤ A →
    1200/Real.log A ≤ price →
    (∀ j b, eligible j b = true → A^((499:ℝ)/500) ≤ b ∧ 2*P ≤ b) →
    (∀ b ∈ h, 1-μ*b ≠ 0) →
    inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    totalGapSavingsMaximum (cappedStep μ B) P κ price eligible (fullCut A h) ≤
      cutLogProduct (cappedStep μ B) P κ (fullCut A h)-Real.log κ+
        1201*weightedCount h cap*A^(-nu)/Real.log A := by
  filter_upwards [eventually_refined_working_log_power_gap hσ hσmax hτ hτmax hσυ hτυ hυmax hυq,
    eventually_gt_atTop (1:ℝ)] with A hbound hA
  intro κ B cap μ P critical price h eligible hκ hgap hBcap hcapκ hμ hμu hμB hPL hPU hPA hprice heligible hcrit hcritical hcriticalRank hD
  let C := fullCut A h
  let R := maximizingCutRefinement (cappedStep μ B) P κ price eligible C
  have hA0 := zero_lt_one.trans hA
  have hlog := Real.log_pos hA
  have hword : R.word = h := (maximizingCutRefinement_word _ _ _ _ _ C).trans (cutSchedule_word _ _)
  have horig : ∀ p ∈ C.phases, A^((499:ℝ)/500) ≤ p.pivot ∧ 2*P ≤ p.pivot := by
    intro p hp
    have hlow : A^((499:ℝ)/500) ≤ A := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA.le (by norm_num : (499:ℝ)/500 ≤ 1)
    exact ⟨hlow.trans (fullCut_pivot hp).le,hPA.trans (fullCut_pivot hp).le⟩
  have hselected := maximizingCutRefinement_selected_property (cappedStep μ B) P κ price eligible C
    (fun _ b => A^((499:ℝ)/500) ≤ b ∧ 2*P ≤ b) horig heligible
  have hunselected : ∀ b ∈ R.unselected, 0 < b → b ≤ A :=
    maximizingCutRefinement_unselected_property _ _ _ _ _ C (fun b => 0 < b → b ≤ A)
      (fun b hb _ => fullCut_unselected hb)
  have hlow := hbound κ B cap μ P critical R hκ hgap hBcap hcapκ hμ hμu hμB hPL hPU
    (fun p hp => (hselected p hp).1) (fun p hp => (hselected p hp).2) hunselected
    (by simpa only [hword] using hcrit) (by simpa only [hword] using hcritical)
    (by simpa only [hword] using hcriticalRank) (by simpa only [hword] using hD)
  rw [hword] at hlow
  have hcountNat : C.phases.length ≤ R.phases.length := by
    have hh := refineCutGaps_count (maximizingPhaseSelector (cappedStep μ B) P price eligible)
      (maximizingTerminalCut (cappedStep μ B) P κ price eligible C) C.phases
    change _ ≤ (refineCutGaps _ _ C.phases).phases.length
    omega
  have hcountReal : (C.phases.length:ℝ) ≤ (R.phases.length:ℝ) := by exact_mod_cast hcountNat
  have hprice' := mul_le_mul_of_nonneg_right hprice (sub_nonneg.mpr hcountReal)
  have hq : 0 < q := (hσ.trans hσυ).trans_le hυq
  have hAA : A ≤ A^(1+q) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA.le
      (show (1:ℝ) ≤ 1+q by linarith only [hq])
  have hk := (fullCut_count_le_countAbove h A).trans (countAbove_rank_bound h hA0 ((hAA.trans hgap).trans hBcap))
  have hk' := mul_le_mul_of_nonneg_left hk (show 0 ≤ 1200/Real.log A by positivity)
  have hidentity := maximizingCutRefinement_savings (cappedStep μ B) P κ price eligible C
  linear_combination hidentity+hlow+hprice'+hk'

end
end StrongSilver
