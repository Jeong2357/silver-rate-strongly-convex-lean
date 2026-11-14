-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardTrajectory

namespace StrongSilver
open Set Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem backward_norm_of_iterate {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (g : V → V) (hginner : ∀ x, 0 ≤ inner ℝ (g x) x) (hgbound : ∀ x, ‖g x‖ ≤ M)
    (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0) (x y : V)
    (hend : iterate h (stronglyConvexGradient μ g) x = y) :
    ‖x‖ ≤ Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*M*smallPositiveSum μ h) := by
  induction h generalizing x with
  | nil => simpa only [iterate_nil,inverseCharge,smallPositiveSum,List.map_nil,List.sum_nil,Real.exp_zero,mul_zero,add_zero,one_mul] using congrArg norm hend |>.le
  | cons b h ih =>
    let z := x-b • stronglyConvexGradient μ g x
    have hz : iterate h (stronglyConvexGradient μ g) z = y := by simpa only [iterate_cons] using hend
    have hzb := ih (fun c hc => hcritical c (List.mem_cons_of_mem b hc)) z hz
    have hxb := backward_step_divided_bound hμ hμ1 g x (hginner x) (hgbound x) (hcritical b List.mem_cons_self)
    change ‖x‖ ≤ Real.exp (inverseLogKernel (1-μ*b))*(‖z‖+(1-μ)*M*smallPositiveStep μ b) at hxb
    have hetail : 1 ≤ Real.exp (inverseCharge μ h) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (inverseCharge_nonneg μ h)
    have hc : 0 ≤ (1-μ)*M*smallPositiveStep μ b :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hμ1) hM) (smallPositiveStep_nonneg μ b)
    have hcb := mul_le_mul_of_nonneg_right hetail hc
    simp only [inverseCharge,smallPositiveSum,List.map_cons,List.sum_cons,Real.exp_add]
    have he : 0 ≤ Real.exp (inverseLogKernel (1-μ*b)) := (Real.exp_pos _).le
    have hscale := mul_le_mul_of_nonneg_left hzb he
    have hscale2 := mul_le_mul_of_nonneg_left hcb he
    change ‖x‖ ≤ Real.exp (inverseLogKernel (1-μ*b))*Real.exp (inverseCharge μ h)*
      (‖y‖+(1-μ)*M*(smallPositiveStep μ b+smallPositiveSum μ h))
    nlinarith only [hxb,hscale,hscale2]

end
end StrongSilver
