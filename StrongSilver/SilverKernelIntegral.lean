-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverAveragingKernel

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5500000

theorem depthWindowIndicator_eq_steps (k : ℕ) (z v y : ℝ) :
    depthWindowIndicator k (y-z)*Real.exp (v*y) =
      (if y < z+(k:ℝ)*Real.log rho then Real.exp (v*y) else 0)-(if y < z then Real.exp (v*y) else 0) := by
  have hk : 0 ≤ (k:ℝ)*Real.log rho := mul_nonneg (Nat.cast_nonneg _) log_rho_positive.le
  by_cases hy : y < z
  · have hhi : y < z+(k:ℝ)*Real.log rho := by linarith only [hy,hk]
    have hneg : ¬ (0 ≤ y-z) := by linarith only [hy]
    simp only [depthWindowIndicator,hneg,false_and,hy,hhi,↓reduceIte,zero_mul,sub_self]
  · have hlo : 0 ≤ y-z := by linarith only [le_of_not_gt hy]
    have hiff : y-z < (k:ℝ)*Real.log rho ↔ y < z+(k:ℝ)*Real.log rho := by constructor <;> intro hh <;> linarith only [hh]
    simp only [depthWindowIndicator,hlo,true_and,hiff,hy,↓reduceIte,sub_zero]
    split_ifs <;> ring

theorem weighted_depth_window_integral (k : ℕ) (v z a b : ℝ) (hab : a ≤ b)
    (ha : a ≤ z) (hb : z+(k:ℝ)*Real.log rho ≤ b) :
    v*(∫ y in a..b, depthWindowIndicator k (y-z)*Real.exp (v*y)) =
      Real.exp (v*z)*(Real.exp (v*((k:ℝ)*Real.log rho))-1) := by
  have hk : z ≤ z+(k:ℝ)*Real.log rho := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) log_rho_positive.le)
  have h1 := exponential_step_integral v a b (z+(k:ℝ)*Real.log rho) hab
  have h2 := exponential_step_integral v a b z hab
  rw [min_eq_right hb,min_eq_left (ha.trans hk)] at h1
  rw [min_eq_right (hk.trans hb),min_eq_left ha] at h2
  have he : (fun y => depthWindowIndicator k (y-z)*Real.exp (v*y)) = fun y =>
      (if y < z+(k:ℝ)*Real.log rho then Real.exp (v*y) else 0)-(if y < z then Real.exp (v*y) else 0) :=
    funext (depthWindowIndicator_eq_steps k z v)
  rw [he,intervalIntegral.integral_sub (exponential_step_intervalIntegrable v _ a b) (exponential_step_intervalIntegrable v z a b)]
  rw [mul_add,Real.exp_add] at h1
  linear_combination h1-h2

theorem silver_exp_nat_spacing (k : ℕ) : Real.exp (nu*((k:ℝ)*Real.log rho)) = (2:ℝ)^k := by
  have hbase : Real.exp (nu*Real.log rho) = 2 := by
    simpa only [Real.rpow_def_of_pos rho_positive,mul_comm] using rho_rpow_nu
  rw [show nu*((k:ℝ)*Real.log rho) = (k:ℝ)*(nu*Real.log rho) by ring,Real.exp_nat_mul,hbase]

theorem silverAveragingKernel_integrable (d : ℕ) (z v a b : ℝ) :
    IntervalIntegrable (fun y => silverAveragingKernel d (y-z)*Real.exp (v*y)) volume a b := by
  have he : (fun y => silverAveragingKernel d (y-z)*Real.exp (v*y)) = fun y =>
      (1-1/Real.sqrt 2)*(depthWindowIndicator d (y-z)*Real.exp (v*y))+
        depthWindowIndicator (d+1) (y-z)*Real.exp (v*y)+
        (1/Real.sqrt 2)*(depthWindowIndicator (d+2) (y-z)*Real.exp (v*y)) := by
    funext y
    unfold silverAveragingKernel
    ring
  rw [he]
  exact (((depthWindowIndicator_integrable d z v a b).const_mul _).add
    (depthWindowIndicator_integrable (d+1) z v a b)).add ((depthWindowIndicator_integrable (d+2) z v a b).const_mul _)

/-- The exact kernel normalization, with exponential weight, uses
only three finite intervals and the identity rho^nu = 2. -/
theorem silverKernel_integral (d : ℕ) (z a b : ℝ) (hab : a ≤ b)
    (ha : a ≤ z) (hb : z+((d+2:ℕ):ℝ)*Real.log rho ≤ b) :
    (∫ y in a..b, silverAveragingKernel d (y-z)*Real.exp (nu*y)) = silverKernelMass d*Real.exp (nu*z) := by
  have hSub (k : ℕ) (hk : k ≤ d+2) : z+(k:ℝ)*Real.log rho ≤ b := by
    have hkr : (k:ℝ) ≤ ((d+2:ℕ):ℝ) := by exact_mod_cast hk
    have hh := mul_le_mul_of_nonneg_right hkr log_rho_positive.le
    linarith only [hh,hb]
  have h0 := weighted_depth_window_integral d nu z a b hab ha (hSub d (by omega))
  have h1 := weighted_depth_window_integral (d+1) nu z a b hab ha (hSub (d+1) (by omega))
  have h2 := weighted_depth_window_integral (d+2) nu z a b hab ha (hSub (d+2) (by omega))
  rw [silver_exp_nat_spacing] at h0 h1 h2
  have he : (fun y => silverAveragingKernel d (y-z)*Real.exp (nu*y)) = fun y =>
      (1-1/Real.sqrt 2)*(depthWindowIndicator d (y-z)*Real.exp (nu*y))+
        depthWindowIndicator (d+1) (y-z)*Real.exp (nu*y)+
        (1/Real.sqrt 2)*(depthWindowIndicator (d+2) (y-z)*Real.exp (nu*y)) := by
    funext y
    unfold silverAveragingKernel
    ring
  rw [he,intervalIntegral.integral_add
    (((depthWindowIndicator_integrable d z nu a b).const_mul _).add (depthWindowIndicator_integrable (d+1) z nu a b))
    ((depthWindowIndicator_integrable (d+2) z nu a b).const_mul _),
    intervalIntegral.integral_add ((depthWindowIndicator_integrable d z nu a b).const_mul _)
      (depthWindowIndicator_integrable (d+1) z nu a b),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold silverKernelMass
  conv_rhs => rw [div_mul_eq_mul_div]
  apply (eq_div_iff nu_positive.ne').mpr
  rw [pow_succ] at h1
  rw [show d+2 = (d+1)+1 by omega,pow_succ,pow_succ] at h2
  linear_combination (1-1/Real.sqrt 2)*h0+h1+(1/Real.sqrt 2)*h2

end
end StrongSilver
