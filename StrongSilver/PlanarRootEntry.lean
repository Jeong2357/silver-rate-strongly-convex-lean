-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarSignedGrowth
import StrongSilver.LocalPhaseEstimates

namespace StrongSilver.LocalPhaseCertificate
open Complex Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

/-- A large actual step forces a large planar starting norm. Growth
before that step is charged only to the original negative-step mass. -/
theorem planar_start_lower_at_root {A μ b T e : ℝ} {h : List ℝ}
    (L : LocalPhaseCertificate A μ b T e h) (i : Fin h.length)
    (hroot : 1 < h.get i) (hμ : μ ≤ 1/2)
    (hsmall : μ*negativeMass h ≤ 1/4) (hnegative : negativeMass h ≤ h.get i/16) :
    h.get i/8 ≤ ‖L.R‖ := by
  let x := iterate (h.take i.val) L.planar.physical L.R
  let y := iterate (h.take (i.val+1)) L.planar.physical L.R
  have hx : x ∈ L.planar.domain := L.planar_states i.val (by omega)
  have hy : y ∈ L.planar.domain := L.planar_states (i.val+1) (by omega)
  have hu : y = x-h.get i • L.planar.physical x := iterate_prefix_succ h _ _ i
  have hxn : x ≠ 0 := by
    intro he
    have htail : iterate (h.drop i.val) L.planar.physical x = (⟨planarEpsilon A,1⟩ : ℂ) := by
      change iterate (h.drop i.val) _ (iterate (h.take i.val) _ _) = _
      rw [← iterate_append,List.take_append_drop]
      exact L.planar_run
    have hz : L.planar.physical 0 = 0 := L.planar.physical_gradient_zero
    rw [he,iterate_fixed _ _ _ hz] at htail
    have him := congrArg Complex.im htail
    norm_num at him
  have hrootnorm := L.planar.root_state_norm_lower hx hy hxn hroot hμ (L.small_steps _ (List.get_mem h i)) hu
  have hprefix : ∀ j : ℕ, j ≤ (h.take i.val).length →
      iterate ((h.take i.val).take j) L.planar.physical L.R ∈ L.planar.domain := by
    intro j hj
    rw [List.take_take]
    apply L.planar_states
    omega
  have hgrowth := L.planar.signed_trajectory_norm_growth (h.take i.val) L.R hprefix
  have hN := negativeMass_take_le h i.val
  have hnp := negativeMass_nonnegative (h.take i.val)
  have hn := mul_nonneg L.mu_positive.le hnp
  have hcharge := (mul_le_mul_of_nonneg_left hN L.mu_positive.le).trans hsmall
  have hexp := Real.abs_exp_sub_one_le (x := μ*negativeMass (h.take i.val))
    (by rw [abs_of_nonneg hn]; linarith only [hcharge])
  rw [abs_of_nonneg hn] at hexp
  have hexp2 : Real.exp (μ*negativeMass (h.take i.val)) ≤ 2 := by
    have hh := le_abs_self (Real.exp (μ*negativeMass (h.take i.val))-1)
    nlinarith only [hh,hexp,hcharge]
  have hbase : 0 ≤ ‖L.R‖+2*negativeMass (h.take i.val) := by nlinarith only [norm_nonneg L.R,hnp]
  have hsum : ‖L.R‖+2*negativeMass (h.take i.val) ≤ ‖L.R‖+2*negativeMass h := by nlinarith only [hN]
  have hbound := mul_le_mul hexp2 hsum hbase (by norm_num : (0:ℝ) ≤ 2)
  change h.get i/2 ≤ ‖x‖ at hrootnorm
  change ‖x‖ ≤ _ at hgrowth
  nlinarith only [hrootnorm,hgrowth,hbound,hnegative]

end
end StrongSilver.LocalPhaseCertificate
