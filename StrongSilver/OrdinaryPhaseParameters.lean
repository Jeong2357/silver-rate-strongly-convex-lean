-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingOldGate
import StrongSilver.WorkingPhaseNorm
import StrongSilver.PhaseScalarScale
import StrongSilver.SupportedPathError
import StrongSilver.NormRatioBound

namespace StrongSilver
noncomputable section

/-- Numerical conditions used uniformly by ordinary phases, including the
working bands and the initial-cutoff range. -/
structure OrdinaryPhaseParameters (A μ b T P : ℝ) (h : List ℝ) : Prop where
  mu_positive : 0 < μ
  b_lt_T : b < T
  gap_cap : ∀ c ∈ h, 0 < c → c ≤ A
  pivot_lower : A^((499 : ℝ)/500) ≤ b
  pivot_upper : b ≤ A^((201 : ℝ)/200)
  pad_lower : A^((49 : ℝ)/50) ≤ P
  pad_upper : P ≤ A^((199 : ℝ)/200)
  cap_ratio : A/T ≤ 1/2
  curvature : μ*T ≤ 31/32
  mass_time : Scalar.SignedIntervals.positiveMass h/T ≤ 2
  mass_pivot : Scalar.SignedIntervals.positiveMass h/b ≤ A^((3 : ℝ)/1000)
  mass_bound : Scalar.SignedIntervals.positiveMass h ≤ A^((1003 : ℝ)/1000)
  time_bound : T ≤ A^((51 : ℝ)/50)
  negative_charge : negativeLogSum h T ≤ (1/250)*Real.log A

end
end StrongSilver
