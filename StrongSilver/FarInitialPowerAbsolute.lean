-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FarInitialPower
import StrongSilver.InitialPowerExponents

namespace StrongSilver
open Real Filter
noncomputable section

theorem eventually_far_initial_padded_power_absolute {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128) :
    ∀ᶠ B : ℝ in atTop, ∀ κ : ℝ, ∀ h : List ℝ,
      1 < κ → B ≤ a*κ → B ≤ κ^(1-initialPowerEpsilon) →
      weightedCount h (a*κ) = (countAbove h B : ℝ)*B^nu → D κ h ≤ 1 →
      ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
        inverseChargeAbove (κ/4) h μ ≤ 34*(countAbove h (κ/4) : ℝ) ∧
        ∀ A : ℝ, B^(1-initialPowerXi) ≤ A → A < B →
          (powerLogMinimum/4)*weightedCount h (a*κ) ≤
            cutPower (cappedStep μ B) (B^((987 : ℝ)/1000)) κ (fullCut A h) := by
  exact eventually_far_initial_padded_power (σ := initialPowerSigma) (τ := initialPowerTau)
    (υ := initialPowerUpsilon) (ξ := initialPowerXi) (ε := initialPowerEpsilon) ha hamax
    (by norm_num [initialPowerSigma]) (by norm_num [initialPowerSigma])
    (by norm_num [initialPowerTau]) (by norm_num [initialPowerTau])
    (by norm_num [initialPowerSigma,initialPowerUpsilon]) (by norm_num [initialPowerTau,initialPowerUpsilon])
    (by norm_num [initialPowerUpsilon]) initialPowerXi_positive
    (initialPowerXi_upper.trans (by norm_num)) (by norm_num [initialPowerEpsilon]) (by norm_num [initialPowerEpsilon])
    initialPower_time_separation initialPowerSigma_decay initialPowerTau_decay initialPowerUpsilon_decay initialPowerXi_count_margin

end
end StrongSilver
