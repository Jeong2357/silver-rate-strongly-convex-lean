-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseContinuity

namespace StrongSilver.FourPhase
open Filter
open scoped Topology
noncomputable section

/-- A closed coordinate box on which every algebraic regularity condition
of the four-phase construction holds. -/
theorem exists_regular_box : ∃ ε > 0, ∀ x : Shape,
    (∀ i, |x i-reference i| ≤ ε) → Regular x := by
  obtain ⟨δ,hδ,hbox⟩ := Metric.eventually_nhds_iff.mp eventually_regular_reference
  refine ⟨δ/2,half_pos hδ,fun x hx => hbox ?_⟩
  have hd : dist x reference ≤ δ/2 := (dist_pi_le_iff (half_pos hδ).le).mpr
    (fun i => by simpa only [Real.dist_eq] using hx i)
  exact hd.trans_lt (by linarith only [hδ])

@[fun_prop] theorem continuousAt_gainCoefficient_reference :
    ContinuousAt gainCoefficient reference := by
  have hden : reference 5*totalTime reference ≠ 0 := by
    rw [reference_k1,totalTime_reference]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) rho_positive.ne')
  unfold gainCoefficient
  exact (continuous_leftMass.continuousAt.mul continuous_t2.continuousAt).div
    ((continuous_apply 5).continuousAt.mul continuous_totalTime.continuousAt) hden

end
end StrongSilver.FourPhase
