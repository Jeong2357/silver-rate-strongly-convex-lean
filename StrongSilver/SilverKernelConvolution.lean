-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SilverKernelUpper
import StrongSilver.WeightedConvolutionError

namespace StrongSilver
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6500000

/-- A single original signed jump is approximated by its normalized
finite silver-kernel convolution. The source weight only needs full
support containment when that event's weight is nonzero. -/
theorem silver_kernel_convolution_error (d : ℕ) (z a b χe Δ lip : ℝ) (χ : ℝ → ℝ)
    (hab : a ≤ b) (hlip : 0 ≤ lip) (hχ : Continuous χ)
    (hContain : χe ≠ 0 → a ≤ z ∧ z+((d+2:ℕ):ℝ)*Real.log rho ≤ b)
    (hLip : ∀ y ∈ Icc a b, |χe-χ y| ≤ lip*|y-z|) :
    |χe*Δ-(Δ/(silverKernelMass d*Real.exp (nu*z)))*
      (∫ y in a..b, χ y*(silverAveragingKernel d (y-z)*Real.exp (nu*y)))| ≤
      lip*(((d+2:ℕ):ℝ)*Real.log rho)*|Δ| := by
  let kernel := fun y => silverAveragingKernel d (y-z)*Real.exp (nu*y)
  let m := silverKernelMass d*Real.exp (nu*z)
  let ε := lip*(((d+2:ℕ):ℝ)*Real.log rho)
  have hm : 0 < m := mul_pos (silverKernelMass_positive d) (Real.exp_pos _)
  have hε : 0 ≤ ε := mul_nonneg hlip (mul_nonneg (Nat.cast_nonneg _) log_rho_positive.le)
  have hk := silverAveragingKernel_integrable d z nu a b
  have hχk : IntervalIntegrable (fun y => χ y*kernel y) volume a b := hk.continuousOn_mul hχ.continuousOn
  have hk0 (y : ℝ) : 0 ≤ kernel y := mul_nonneg (silverAveragingKernel_nonnegative _ _) (Real.exp_pos _).le
  have hMass : χe*(∫ y in a..b, kernel y) = χe*m := by
    by_cases hz : χe = 0
    · simp only [hz,zero_mul]
    · obtain ⟨ha,hb⟩ := hContain hz
      rw [silverKernel_integral d z a b hab ha hb]
  have hDiff : ∀ y ∈ Icc a b, kernel y ≠ 0 → |χe-χ y| ≤ ε := by
    intro y hy hNonzero
    have hK : silverAveragingKernel d (y-z) ≠ 0 := by
      intro hz
      apply hNonzero
      simp only [kernel,hz,zero_mul]
    have hSupport := silverAveragingKernel_support hK
    have hNorm : |y-z| ≤ ((d+2:ℕ):ℝ)*Real.log rho := by
      rw [abs_of_nonneg hSupport.1]
      exact hSupport.2.le
    exact (hLip y hy).trans (mul_le_mul_of_nonneg_left hNorm hlip)
  exact weighted_convolution_error kernel χ a b m ε χe Δ hab hm hε hk hχk (fun y _ => hk0 y) hMass
    (silverKernel_integral_upper d z a b hab) hDiff

end
end StrongSilver
