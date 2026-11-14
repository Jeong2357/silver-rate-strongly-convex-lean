-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.StrongMoreau
import StrongSilver.InverseLogKernel

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def smallPositiveStep (μ h : ℝ) : ℝ := if 0 < h ∧ h < 1/μ then h else 0

theorem smallPositiveStep_nonneg (μ h : ℝ) : 0 ≤ smallPositiveStep μ h := by
  unfold smallPositiveStep
  split_ifs with hh
  · exact hh.1.le
  · exact le_rfl

theorem backward_step_norm_bound {μ h M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (g : V → V) (x : V) (hg : 0 ≤ inner ℝ (g x) x) (hM : ‖g x‖ ≤ M) :
    |1-μ*h| * ‖x‖ ≤ ‖x-h • stronglyConvexGradient μ g x‖+(1-μ)*M*smallPositiveStep μ h := by
  let y := x-h • stronglyConvexGradient μ g x
  have hy : y = (1-μ*h) • x-(h*(1-μ)) • g x := by dsimp [y,stronglyConvexGradient]; module
  have hiy : inner ℝ y x = (1-μ*h)*‖x‖^2-h*(1-μ)*inner ℝ (g x) x := by
    rw [hy,inner_sub_left,real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
  by_cases hh : 0 < h ∧ h < 1/μ
  · have hq : 0 ≤ 1-μ*h := by
      have hh' := (lt_div_iff₀ hμ).mp hh.2
      nlinarith
    have hc : 0 ≤ h*(1-μ) := mul_nonneg hh.1.le (sub_nonneg.mpr hμ1)
    have he : (1-μ*h) • x = y+(h*(1-μ)) • g x := by rw [hy]; module
    rw [smallPositiveStep,if_pos hh,abs_of_nonneg hq]
    change (1-μ*h)*‖x‖ ≤ ‖y‖+(1-μ)*M*h
    calc
      _ = ‖(1-μ*h) • x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq]
      _ = ‖y+(h*(1-μ)) • g x‖ := congrArg norm he
      _ ≤ ‖y‖+‖(h*(1-μ)) • g x‖ := norm_add_le _ _
      _ ≤ ‖y‖+(1-μ)*M*h := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
        nlinarith only [mul_le_mul_of_nonneg_left hM hc]
  · rw [smallPositiveStep,if_neg hh,mul_zero,add_zero]
    change |1-μ*h| * ‖x‖ ≤ ‖y‖
    by_cases hx : ‖x‖ = 0
    · rw [hx,mul_zero]
      exact norm_nonneg _
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    by_cases hh0 : h ≤ 0
    · have hq : 0 ≤ 1-μ*h := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos hμ.le hh0]
      have hc : h*(1-μ)*inner ℝ (g x) x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hh0 (sub_nonneg.mpr hμ1)) hg
      have hi := real_inner_le_norm y x
      rw [hiy] at hi
      rw [abs_of_nonneg hq]
      nlinarith only [hi,hc,hxpos]
    · have hhpos : 0 < h := lt_of_not_ge hh0
      have hlarge : 1/μ ≤ h := le_of_not_gt (fun hlt => hh ⟨hhpos,hlt⟩)
      have hq : 1-μ*h ≤ 0 := by
        have hh' := (div_le_iff₀ hμ).mp hlarge
        nlinarith
      have hc : 0 ≤ h*(1-μ)*inner ℝ (g x) x :=
        mul_nonneg (mul_nonneg hhpos.le (sub_nonneg.mpr hμ1)) hg
      have hi := real_inner_le_norm (-y) x
      rw [inner_neg_left,norm_neg,hiy] at hi
      rw [abs_of_nonpos hq]
      nlinarith only [hi,hc,hxpos]

theorem inverse_factor_le_exp_kernel {t : ℝ} (ht : t ≠ 0) :
    |t|⁻¹ ≤ Real.exp (inverseLogKernel t) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  rw [inverseLogKernel_eq]
  calc
    _ = Real.exp (-Real.log |t|) := by rw [Real.exp_neg,Real.exp_log habs]
    _ ≤ Real.exp (max 0 (-Real.log t)) := by
      apply Real.exp_le_exp.mpr
      simpa only [Real.log_abs] using le_max_right (0 : ℝ) (-Real.log t)

theorem exp_kernel_one_le (t : ℝ) : 1 ≤ Real.exp (inverseLogKernel t) := by
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (inverseLogKernel_nonneg t)

end
end StrongSilver
