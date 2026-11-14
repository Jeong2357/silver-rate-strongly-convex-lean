-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverKernelIntegral

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4000000

/-- Truncating any kernel interval only decreases its nonnegative
exponentially weighted mass. -/
theorem silverKernel_integral_upper (d : ℕ) (z a b : ℝ) (hab : a ≤ b) :
    (∫ y in a..b, silverAveragingKernel d (y-z)*Real.exp (nu*y)) ≤ silverKernelMass d*Real.exp (nu*z) := by
  let aa := min a z
  let bb := max b (z+((d+2:ℕ):ℝ)*Real.log rho)
  have hOuter : aa ≤ bb := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  have hNonneg (y : ℝ) : 0 ≤ silverAveragingKernel d (y-z)*Real.exp (nu*y) :=
    mul_nonneg (silverAveragingKernel_nonnegative d (y-z)) (Real.exp_pos _).le
  have hSub := intervalIntegral.integral_mono_interval (min_le_left a z) hab (le_max_left b _)
    (Filter.Eventually.of_forall hNonneg) (silverAveragingKernel_integrable d z nu aa bb)
  exact hSub.trans_eq (silverKernel_integral d z aa bb hOuter (min_le_right _ _) (le_max_right _ _))

/-- The three-rectangle kernel is zero outside its finite support. -/
theorem silverAveragingKernel_support {d : ℕ} {s : ℝ} (hs : silverAveragingKernel d s ≠ 0) :
    0 ≤ s ∧ s < ((d+2:ℕ):ℝ)*Real.log rho := by
  have hω := log_rho_positive
  by_contra hn
  apply hs
  unfold silverAveragingKernel
  have hK (k : ℕ) (hk : k ≤ d+2) : depthWindowIndicator k s = 0 := by
    unfold depthWindowIndicator
    apply if_neg
    intro hh
    apply hn
    have hkr : (k:ℝ) ≤ ((d+2:ℕ):ℝ) := by exact_mod_cast hk
    exact ⟨hh.1,hh.2.trans_le (mul_le_mul_of_nonneg_right hkr hω.le)⟩
  rw [hK d (by omega),hK (d+1) (by omega),hK (d+2) (by omega)]
  ring

end
end StrongSilver
