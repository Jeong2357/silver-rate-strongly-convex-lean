-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPlanarAllBounds
import StrongSilver.ScalarGrowthBudget

namespace StrongSilver
open Real Filter
noncomputable section

/-- Quantitative initial-cutoff conditions. These are numerical conditions on
an actual gap and its selected step, to be discharged from (3.26). -/
structure InitialPhaseBudget (A μ b T κ B : ℝ) (h : List ℝ) : Prop where
  mu_positive : 0 < μ
  kappa_large : 1 ≤ κ
  cutoff_lower : A ≤ B
  B_positive : 0 < B
  B_le_kappa : B ≤ κ
  pivot_lower : B ≤ b
  pivot_upper : b ≤ κ/2
  pivot_lt_time : b < T
  time_lower : κ/2 ≤ T
  time_upper : T ≤ κ
  cap_ratio : A/T ≤ 1/2
  curvature : μ*T ≤ 31/32
  mass : Scalar.SignedIntervals.positiveMass h ≤ κ
  gap_cap : ∀ c ∈ h, 0 < c → c ≤ A
  negative_charge : negativeLogSum h T ≤ 2

namespace InitialPhaseBudget
variable {A μ b T κ B : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
include W
set_option maxHeartbeats 1000000

theorem kappa_positive : 0 < κ := zero_lt_one.trans_le W.kappa_large
theorem time_positive : 0 < T := (div_pos W.kappa_positive (by norm_num : (0 : ℝ) < 2)).trans_le W.time_lower
theorem pivot_positive : 0 < b := W.B_positive.trans_le W.pivot_lower
theorem ratio_ge_one : 1 ≤ κ/B := (one_le_div W.B_positive).mpr W.B_le_kappa

theorem mass_time : Scalar.SignedIntervals.positiveMass h/T ≤ 2 :=
  (div_le_iff₀ W.time_positive).mpr (by linarith [W.mass,W.time_lower])

theorem mass_pivot : Scalar.SignedIntervals.positiveMass h/b ≤ κ/B := by
  apply (div_le_div_iff₀ W.pivot_positive W.B_positive).mpr
  have h1 := mul_le_mul_of_nonneg_right W.mass W.B_positive.le
  have h2 := mul_le_mul_of_nonneg_left W.pivot_lower W.kappa_positive.le
  nlinarith only [h1,h2]

theorem growth : scalarRampGrowth T A b h ≤ (2*Real.exp 4)*(κ/B) :=
  scalarRampGrowth_budget_bound W.time_positive W.pivot_positive W.ratio_ge_one W.cap_ratio h W.mass_time W.mass_pivot

theorem planar_all_norm {e : ℝ} (L : LocalPhaseCertificate A μ b T e h) (i : ℕ) :
    ‖iterate (h.take i) L.planar.physical L.R‖ ≤ (4*Real.exp 4)*κ := by
  have hh := L.planar_all_norm_bound W.cap_ratio W.curvature W.mass_time i
  have hs : 2+2*Scalar.SignedIntervals.positiveMass h ≤ 4*κ := by linarith [W.mass,W.kappa_large]
  have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos 4).le
  nlinarith only [hh,hm]

theorem q_lower {e : ℝ} (L : LocalPhaseCertificate A μ b T e h) :
    1/(32*Real.exp 4) ≤ quadraticMultiplier μ h*(1-μ*b) :=
  L.working_q_lower W.cap_ratio W.curvature W.mass_time

end InitialPhaseBudget

theorem eventually_exists_initial_phase : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h : List ℝ, InitialPhaseBudget A μ b T κ B h →
      Nonempty (LocalPhaseCertificate A μ b T 1 h) := by
  filter_upwards [eventually_ge_atTop (8 : ℝ),eventually_exists_local_phase] with A hA hex
  intro μ b T κ B h W
  have hT := W.time_positive
  have hAT := (div_le_iff₀ hT).mp W.cap_ratio
  have hA0 : 0 < A := by linarith only [hA]
  have hAT' : A < T := by linarith only [hAT,hT]
  have hmul := mul_le_mul_of_nonneg_left hAT W.mu_positive.le
  have hμA : μ*A ≤ 1 := by nlinarith only [hmul,W.curvature]
  exact hex μ b T 1 W.mu_positive hμA (hA.trans (W.cutoff_lower.trans W.pivot_lower))
    W.pivot_lt_time hAT' zero_lt_one (by linarith [W.curvature]) h W.gap_cap

end
end StrongSilver
