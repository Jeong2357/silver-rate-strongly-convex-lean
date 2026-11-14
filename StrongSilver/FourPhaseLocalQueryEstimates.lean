-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalParameters
import StrongSilver.FourPhaseAxisPrefixBound
import StrongSilver.FourPhaseStartAxis

namespace StrongSilver.FourPhase.LocalParameters
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

theorem gap_negative_charge (D : LocalParameters) (i : Fin 4) : D.μ*negativeMass (D.gap i) ≤ 1 := by
  have hsub : (D.gap i).Sublist (boundedWord D.gap D.pivot) :=
    (List.sublist_append_right _ _).trans (prior_gap_sublist_bounded D.gap D.pivot i)
  have hmass := (negativeMass_le_absoluteMass (D.gap i)).trans (absoluteMass_sublist_le hsub)
  have hh := (mul_le_mul_of_nonneg_left hmass D.mu_positive.le).trans D.small_total
  linarith only [hh]

theorem first_local_axis_bound (D : LocalParameters) (hμ1 : D.μ ≤ 1)
    (i : Fin 3) (k : Fin (phaseWord D.gap D.pivot i.castSucc).length) :
    max (inner ℝ axis (D.localFamily.z ⟨i.castSucc,k⟩)) 0 ≤ 2*a D.shape*negativeMass (D.gap i.castSucc)/D.T := by
  have hray : phaseState D.μ D.T (carry D.μ D.gap D.pivot i.castSucc)
      (phaseStart D.shape i.castSucc) (slope D.shape i.castSucc)
      (quadraticMultiplier D.μ ((D.gap i.castSucc).take k.val))-(1/D.T) • slope D.shape i.castSucc =
      D.localFamily.z ⟨i.castSucc,k⟩ :=
    (productShape_orbit_ray D.mu_positive D.time_positive D.gap D.pivot D.small_total D.ζ i.castSucc k.val).2
  rw [← hray]
  have hg : inner ℝ axis (slope D.shape i.castSucc) = a D.shape :=
    (real_inner_comm _ _).trans (slope_axis i)
  exact phase_prefix_axis_mass_bound D.mu_positive hμ1 D.time_positive
    (carry_positive D.mu_positive.le D.gap D.pivot D.small_total i.castSucc).le D.geometry.regular.a_positive.le
    _ _ (first_starts_axis_nonpositive D.geometry.regular i) hg (D.gap i.castSucc)
    (gap_small_steps D.mu_positive.le D.gap D.pivot D.small_total i.castSucc) (D.gap_negative_charge i.castSucc) k.val

theorem first_local_value_lower (D : LocalParameters) (i : Fin 3)
    (k : Fin (phaseWord D.gap D.pivot i.castSucc).length) :
    1/64 ≤ planeValue D.shape i.castSucc (D.localFamily.z ⟨i.castSucc,k⟩) := by
  have hscale := D.queryScale_lower ⟨i.castSucc,k⟩
  have hslack := D.querySlack_nonnegative ⟨i.castSucc,k⟩
  have hh := first_queries_height_bound D.geometry.regular D.offset_nonnegative D.geometry.masses_lower i
    (show 0 ≤ D.queryScale ⟨i.castSucc,k⟩ by linarith only [hscale]) hslack
  have ha := D.geometry.regular.a_positive
  have hca := mul_le_mul_of_nonneg_right hscale ha.le
  have hza := mul_le_mul_of_nonneg_left D.offset_upper ha.le
  change _ ≤ inner ℝ (slope D.shape i.castSucc)
    (D.queryScale ⟨i.castSucc,k⟩ • (foot D.shape i.castSucc+D.querySlack ⟨i.castSucc,k⟩ • slope D.shape i.castSucc))-
    a D.shape*D.ζ
  change D.queryScale ⟨i.castSucc,k⟩*a D.shape*(1/2:ℝ) ≤ _ at hh
  have hal := D.geometry.a_lower
  dsimp only [shape] at hh hca hza hal ⊢
  nlinarith only [hh,hca,hza,hal]

theorem last_local_axis_nonpositive (D : LocalParameters)
    (k : Fin (phaseWord D.gap D.pivot 3).length) : inner ℝ axis (D.localFamily.z ⟨3,k⟩) ≤ 0 := by
  change inner ℝ axis (D.queryScale ⟨3,k⟩ • (foot3 D.shape+D.querySlack ⟨3,k⟩ • slope3 D.shape)) ≤ 0
  rw [foot3_formula,slope3,point_smul,point_add,point_smul,axis_inner_point]
  have hc : 0 ≤ D.queryScale ⟨3,k⟩ := by linarith only [D.queryScale_lower ⟨3,k⟩]
  have hs := D.querySlack_nonnegative ⟨3,k⟩
  have hz : D.shape 7 = D.ζ := rfl
  rw [hz]
  have hh := mul_nonneg hc (add_nonneg D.offset_nonnegative hs)
  nlinarith only [hh]

end
end StrongSilver.FourPhase.LocalParameters
