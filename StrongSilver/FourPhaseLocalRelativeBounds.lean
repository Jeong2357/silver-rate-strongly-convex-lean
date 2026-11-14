-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalBudget
import StrongSilver.FourPhaseNegativeQueryTime
import StrongSilver.FourPhaseRelativeFootBounds
import StrongSilver.FourPhaseLocalInvariants

namespace StrongSilver.FourPhase.LocalParameters
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2600000

theorem first_querySlack_upper (D : LocalParameters) (J : JoiningScaleConditions D)
    {H : ℝ} (hH : H ≤ D.T*lastExcess D.μ D.T D.gap D.pivot/2)
    (hN : ∀ i : Fin 3, 1000*lastExcess D.μ D.T D.gap D.pivot*negativeMass (D.gap i.castSucc) ≤ H)
    (i : Fin 3) (k : Fin (phaseWord D.gap D.pivot i.castSucc).length) : D.querySlack ⟨i.castSucc,k⟩ ≤ 7 := by
  have hk : 0 < lastExcess D.μ D.T D.gap D.pivot := by linarith only [J.last_excess_lower]
  have hmul : (2000*negativeMass (D.gap i.castSucc))*lastExcess D.μ D.T D.gap D.pivot ≤
      D.T*lastExcess D.μ D.T D.gap D.pivot := by nlinarith only [hN i,hH]
  have hbudget := (mul_le_mul_iff_left₀ hk).mp hmul
  have hmass := negativeMass_nonnegative (D.gap i.castSucc)
  have hfrac : 4*negativeMass (D.gap i.castSucc)/D.T ≤ 1 :=
    (div_le_one D.time_positive).mpr (by nlinarith only [hbudget,hmass])
  have htime := negative_queryTime_prefix_mass D.mu_positive D.time_positive
    (carry_positive D.mu_positive.le D.gap D.pivot D.small_total i.castSucc) (D.gap i.castSucc)
    (gap_small_steps D.mu_positive.le D.gap D.pivot D.small_total i.castSucc)
    (D.gap_negative_charge i.castSucc) k.val (D.queryScale_lower ⟨i.castSucc,k⟩)
  have hT : totalTime D.shape ≤ 6 := by
    have hh := D.geometry.total_upper
    have hq := D.geometry.regular.q_positive
    change totalTime D.shape+q D.shape ≤ 6 at hh
    change 0 < q D.shape at hq
    linarith only [hh,hq]
  have hmi : phaseMass D.shape i.castSucc ≤ 6 :=
    (first_mass_upper D.geometry.regular i).trans hT
  change phaseMass D.shape i.castSucc-queryTime D.μ D.T (carry D.μ D.gap D.pivot i.castSucc)
    (quadraticMultiplier D.μ ((D.gap i.castSucc).take k.val)) ≤ _
  linarith only [htime,hfrac,hmi]

theorem localFamily_relative_inner_bounds (D : LocalParameters) (J : JoiningScaleConditions D)
    {H : ℝ} (hH : H ≤ D.T*lastExcess D.μ D.T D.gap D.pivot/2)
    (hN : ∀ i : Fin 3, 1000*lastExcess D.μ D.T D.gap D.pivot*negativeMass (D.gap i.castSucc) ≤ H)
    (j : D.QueryIndex) :
    inner ℝ (source D.shape) (D.localFamily.z j) ≤ 26*‖source D.shape‖^2 ∧
    inner ℝ (source D.shape) (D.localFamily.g j) ≤ (1/D.T)*‖source D.shape‖^2 := by
  have hT : totalTime D.shape ≤ 6 := by
    have hh := D.geometry.total_upper
    have hq := D.geometry.regular.q_positive
    change totalTime D.shape+q D.shape ≤ 6 at hh
    change 0 < q D.shape at hq
    linarith only [hh,hq]
  constructor
  · have hfirst (i : Fin 3) (k : Fin (phaseWord D.gap D.pivot i.castSucc).length) :
        inner ℝ (source D.shape) (D.localFamily.z ⟨i.castSucc,k⟩) ≤ 26*‖source D.shape‖^2 := by
      exact source_query_relative_upper D.geometry.regular D.geometry.time0_lower D.geometry.time1_lower hT
        i.castSucc (by linarith only [D.queryScale_lower ⟨i.castSucc,k⟩])
        (carry_prefix_bounds D.mu_positive.le D.gap D.pivot D.small_total i.castSucc k.val).2
        (D.querySlack_nonnegative ⟨i.castSucc,k⟩) (D.first_querySlack_upper J hH hN i k)
    rcases j with ⟨i,k⟩
    fin_cases i
    · exact hfirst 0 k
    · exact hfirst 1 k
    · exact hfirst 2 k
    · have hh : inner ℝ (source D.shape) (D.localFamily.z ⟨3,k⟩) = 0 :=
        last_query_source_zero D.geometry.regular
      change inner ℝ (source D.shape) (D.localFamily.z ⟨3,k⟩) ≤ _
      rw [hh]
      exact mul_nonneg (by norm_num) (sq_nonneg _)
  · change inner ℝ (source D.shape) ((1/D.T) • slope D.shape j.1) ≤ _
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left
      (source_slopes_upper D.geometry.regular D.geometry.time0_lower D.geometry.time1_lower j.1)
      (one_div_pos.mpr D.time_positive).le

end
end StrongSilver.FourPhase.LocalParameters
