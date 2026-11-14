-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGainAggregation
import StrongSilver.ExponentialStepIntegral
import StrongSilver.Constants

namespace StrongSilver
open ScheduleTree Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5000000

/-- The nonincreasing depth coefficients have only three nonzero
successive differences, so the averaging kernel is three rectangles. -/
def depthWindowIndicator (k : ℕ) (s : ℝ) : ℝ := if 0 ≤ s ∧ s < (k:ℝ)*Real.log rho then 1 else 0

def silverAveragingKernel (d : ℕ) (s : ℝ) : ℝ :=
  (1-1/Real.sqrt 2)*depthWindowIndicator d s+
    depthWindowIndicator (d+1) s+(1/Real.sqrt 2)*depthWindowIndicator (d+2) s

def silverKernelMass (d : ℕ) : ℝ :=
  ((3+3*(1/Real.sqrt 2))*(2:ℝ)^d-2)/nu

theorem silverKernelMass_bounds (d : ℕ) : (2:ℝ)^d/nu ≤ silverKernelMass d ∧ silverKernelMass d ≤ 6*(2:ℝ)^d/nu := by
  have hS := sqrt_two_bounds
  have hInv : 0 < 1/Real.sqrt 2 := one_div_pos.mpr (zero_lt_one.trans hS.1)
  have hInv1 : 1/Real.sqrt 2 ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hS.1.le).trans_eq (by norm_num)
  have hPow : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
  unfold silverKernelMass
  constructor
  · apply div_le_div_of_nonneg_right _ nu_positive.le
    nlinarith only [hPow,mul_nonneg hInv.le (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)]
  · apply div_le_div_of_nonneg_right _ nu_positive.le
    have hh := mul_le_mul_of_nonneg_right hInv1 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)
    nlinarith only [hh]

theorem silverKernelMass_positive (d : ℕ) : 0 < silverKernelMass d :=
  (div_pos (pow_pos (by norm_num : (0:ℝ) < 2) d) nu_positive).trans_le (silverKernelMass_bounds d).1

theorem silverAveragingKernel_nonnegative (d : ℕ) (s : ℝ) : 0 ≤ silverAveragingKernel d s := by
  have hS := sqrt_two_bounds
  have hInv : 0 ≤ 1/Real.sqrt 2 := (one_div_pos.mpr (zero_lt_one.trans hS.1)).le
  have hInv1 : 1/Real.sqrt 2 ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hS.1.le).trans_eq (by norm_num)
  have hw (k : ℕ) : 0 ≤ depthWindowIndicator k s := by unfold depthWindowIndicator; split_ifs <;> norm_num
  exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hInv1) (hw d)) (hw (d+1))) (mul_nonneg hInv (hw (d+2)))

/-- The kernel's depth sum is exactly S_d, including d=0. -/
theorem silverDepthGain_three_windows (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) :
    silverDepthGain φ d t = (1-1/Real.sqrt 2)*throughSum (rootGain φ) d t+
      throughSum (rootGain φ) (d+1) t+(1/Real.sqrt 2)*throughSum (rootGain φ) (d+2) t := by
  rw [silverDepthGain_coefficients,throughSum_succ _ (d+1),throughSum_succ _ d]
  ring

/-- Weighted height-window integrability is finite and exact. -/
theorem depthWindowIndicator_integrable (k : ℕ) (z v a b : ℝ) :
    IntervalIntegrable (fun y => depthWindowIndicator k (y-z)*Real.exp (v*y)) volume a b := by
  have he : (fun y => depthWindowIndicator k (y-z)*Real.exp (v*y)) = fun y =>
      (if y < z+(k:ℝ)*Real.log rho then Real.exp (v*y) else 0)-(if y < z then Real.exp (v*y) else 0) := by
    funext y
    have hk : 0 ≤ (k:ℝ)*Real.log rho := mul_nonneg (Nat.cast_nonneg _) log_rho_positive.le
    by_cases hy : y < z
    · have hhi : y < z+(k:ℝ)*Real.log rho := by linarith only [hy,hk]
      have hneg : ¬ (0 ≤ y-z) := by linarith only [hy]
      simp only [depthWindowIndicator,hneg,false_and,hy,hhi,↓reduceIte,zero_mul,sub_self]
    · have hlo : 0 ≤ y-z := by linarith only [le_of_not_gt hy]
      have hiff : y-z < (k:ℝ)*Real.log rho ↔ y < z+(k:ℝ)*Real.log rho := by constructor <;> intro hh <;> linarith only [hh]
      simp only [depthWindowIndicator,hlo,true_and,hiff,hy,↓reduceIte,sub_zero]
      split_ifs <;> ring
  rw [he]
  exact (exponential_step_intervalIntegrable v _ a b).sub (exponential_step_intervalIntegrable v z a b)

end
end StrongSilver
