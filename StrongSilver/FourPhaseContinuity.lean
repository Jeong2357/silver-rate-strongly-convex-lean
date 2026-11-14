-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseReference
import StrongSilver.FourPhaseRegular
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace StrongSilver.FourPhase
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000

@[fun_prop] theorem continuous_t0 : Continuous t0 := by unfold t0; fun_prop
@[fun_prop] theorem continuous_t1 : Continuous t1 := by unfold t1; fun_prop
@[fun_prop] theorem continuous_t2 : Continuous t2 := by unfold t2; fun_prop
@[fun_prop] theorem continuous_totalTime : Continuous totalTime := by unfold totalTime; fun_prop
@[fun_prop] theorem continuous_leftMass : Continuous leftMass := by unfold leftMass; fun_prop
@[fun_prop] theorem continuous_rightMass : Continuous rightMass := by unfold rightMass; fun_prop
@[fun_prop] theorem continuous_totalMass : Continuous totalMass := by unfold totalMass; fun_prop
@[fun_prop] theorem continuous_q : Continuous q := by unfold q; fun_prop
@[fun_prop] theorem continuous_upperTime : Continuous upperTime := by unfold upperTime; fun_prop

@[fun_prop] theorem continuousAt_a_reference : ContinuousAt a reference := by
  have hT : totalTime reference ≠ 0 := by rw [totalTime_reference]; exact mul_ne_zero (by norm_num) rho_positive.ne'
  unfold a
  fun_prop (disch := assumption)

@[fun_prop] theorem continuousAt_bodyScale_reference : ContinuousAt bodyScale reference := by
  unfold bodyScale
  fun_prop

@[fun_prop] theorem continuousAt_b1sq_reference : ContinuousAt b1sq reference := by
  have hT : totalTime reference ≠ 0 := by rw [totalTime_reference]; exact mul_ne_zero (by norm_num) rho_positive.ne'
  have hU : upperTime reference ≠ 0 := by rw [upperTime_reference]; exact rho_positive.ne'
  unfold b1sq
  fun_prop (disch := assumption)

@[fun_prop] theorem continuousAt_b2sq_reference : ContinuousAt b2sq reference := by
  have hk : reference 6 ≠ 0 := by rw [reference_k2]; exact inv_ne_zero rho_positive.ne'
  have hU : upperTime reference ≠ 0 := by rw [upperTime_reference]; exact rho_positive.ne'
  unfold b2sq
  exact continuousAt_bodyScale_reference.mul
    ((continuousAt_const.div (continuous_apply 6).continuousAt hk).sub
      (continuousAt_const.div continuous_upperTime.continuousAt hU))

@[fun_prop] theorem continuousAt_theta_reference : ContinuousAt theta reference := by
  have hk : reference 5 ≠ 0 := by norm_num
  unfold theta
  fun_prop (disch := assumption)

@[fun_prop] theorem continuousAt_r2_reference : ContinuousAt r2 reference := by
  have ht : t0 reference ≠ 0 := by rw [t0_reference]; have hh := rho_bounds.1; linarith only [hh]
  have hb : b2sq reference ≠ 0 := by rw [b2sq_reference]; exact rho_positive.ne'
  unfold r2
  exact (((continuous_apply 1).continuousAt.mul continuousAt_theta_reference).sub
    ((continuous_totalTime.continuousAt.mul continuousAt_b1sq_reference).div
      continuousAt_b2sq_reference hb)).div continuous_t0.continuousAt ht

theorem regular_reference : Regular reference := by
  have hr := rho_bounds.1
  have hr0 := rho_positive
  have hd : 0 < 2*(rho-1) := by linarith only [hr]
  have hi : 0 < 1/(2*(rho-1)) := div_pos (by norm_num) hd
  have hi1 : 1/(2*(rho-1)) < 1 := (div_lt_one hd).mpr (by linarith only [hr])
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_,by norm_num,?_,?_,?_,?_,?_,?_⟩
  · simpa only [reference_k0] using inv_pos.mpr hr0
  · simpa only [reference_k2] using inv_pos.mpr hr0
  · rw [q_reference]; norm_num
  · rw [theta_reference]; linarith only [hr]
  · rw [r2_reference]; linarith only [hi1]
  · rw [r2_reference]; linarith only [hi]
  · rw [reference_k0,reference_m1]
    simpa only [one_div] using (div_lt_one hr0).mpr (show 1 < rho by linarith only [hr])

theorem eventually_regular_reference : ∀ᶠ x : Shape in 𝓝 reference, Regular x := by
  have R := regular_reference
  have hc (i : Fin 8) : Continuous (fun x : Shape => x i) := continuous_apply i
  have h0 := (tendsto_order.1 ((hc 0).tendsto reference)).1 0 R.m0_positive
  have h1 := (tendsto_order.1 ((hc 1).tendsto reference)).1 0 R.m1_positive
  have h2 := (tendsto_order.1 ((hc 2).tendsto reference)).1 0 R.m2_positive
  have h3 := (tendsto_order.1 ((hc 3).tendsto reference)).1 0 R.m3_positive
  have h4 := (tendsto_order.1 ((hc 4).tendsto reference)).1 0 R.k0_positive
  have h5 := (tendsto_order.1 ((hc 5).tendsto reference)).1 0 R.k1_positive
  have h6 := (tendsto_order.1 ((hc 6).tendsto reference)).1 0 R.k2_positive
  have hq := (tendsto_order.1 (continuous_q.tendsto reference)).1 0 R.q_positive
  have ht := (tendsto_order.1 continuousAt_theta_reference).1 1 R.theta_gt_one
  have hr0 := (tendsto_order.1 continuousAt_r2_reference).1 0 R.r2_positive
  have hr1 := (tendsto_order.1 continuousAt_r2_reference).2 1 R.r2_lt_one
  have hdiff : Continuous (fun x : Shape => x 1-x 4) := by fun_prop
  have hd := (tendsto_order.1 (hdiff.tendsto reference)).1 0 (sub_pos.mpr R.m1_gt_k0)
  filter_upwards [h0,h1,h2,h3,h4,h5,h6,hq,ht,hr0,hr1,hd]
    with x hx0 hx1 hx2 hx3 hx4 hx5 hx6 hxq hxt hxr0 hxr1 hxd
  exact ⟨hx0,hx1,hx2,hx3,hx4,hx5,hx6,hxq,hxt,hxr0,hxr1,lt_of_sub_pos hxd⟩

end
end StrongSilver.FourPhase
