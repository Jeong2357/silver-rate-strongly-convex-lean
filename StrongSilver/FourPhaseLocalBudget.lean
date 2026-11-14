-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalQueryEstimates
import StrongSilver.FourPhaseLocalJoiningScale
import StrongSilver.FourPhaseJoiningMargins

namespace StrongSilver.FourPhase.LocalParameters
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2200000

/-- The numerical retained-ray budget for every local contact follows
from the original negative steps, including the last selected step of
either sign. -/
theorem local_retained_budget (D : LocalParameters) (J : JoiningScaleConditions D)
    {H : ℝ} (hH : 0 < H)
    (hN : ∀ i : Fin 3, 1000*lastExcess D.μ D.T D.gap D.pivot*negativeMass (D.gap i.castSucc) ≤ H)
    (j : D.QueryIndex) :
    (11*D.T*D.joiningScale/(10*H))*max (inner ℝ axis (D.localFamily.z j)) 0 ≤
      planeValue D.shape j.1 (D.localFamily.z j) := by
  have hK := D.joiningScale_bounds J
  have hk : 0 < lastExcess D.μ D.T D.gap D.pivot := by linarith only [J.last_excess_lower]
  have hμ1 : D.μ ≤ 1 := by linarith only [J.mu_upper]
  have ha : a D.shape ≤ 1/2 := D.geometry.a_upper.trans (by norm_num)
  have hfirst (i : Fin 3) (k : Fin (phaseWord D.gap D.pivot i.castSucc).length) :
      (11*D.T*D.joiningScale/(10*H))*max (inner ℝ axis (D.localFamily.z ⟨i.castSucc,k⟩)) 0 ≤
      planeValue D.shape i.castSucc (D.localFamily.z ⟨i.castSucc,k⟩) :=
    retained_query_budget_margin D.time_positive hH hk hK.1.le
      D.geometry.regular.a_positive.le ha hK.2.2.1 (negativeMass_nonnegative _) (hN i)
      (D.first_local_axis_bound hμ1 i k) (D.first_local_value_lower i k)
  rcases j with ⟨i,k⟩
  fin_cases i
  · exact hfirst 0 k
  · exact hfirst 1 k
  · exact hfirst 2 k
  · have haxis := D.last_local_axis_nonpositive k
    change _*max (inner ℝ axis (D.localFamily.z ⟨3,k⟩)) 0 ≤ planeValue D.shape 3 (D.localFamily.z ⟨3,k⟩)
    rw [max_eq_right haxis,mul_zero]
    exact last_queries_value_nonnegative D.geometry.regular D.offset_nonnegative ha
      (D.queryScale_lower ⟨3,k⟩) (D.querySlack_nonnegative ⟨3,k⟩)

end
end StrongSilver.FourPhase.LocalParameters
