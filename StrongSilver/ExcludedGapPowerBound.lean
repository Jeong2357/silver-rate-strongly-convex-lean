-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WindowExcessBadCharge
import StrongSilver.BandWindowForestCount
import StrongSilver.BandPerVertexAbsorption

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 4800000

/-- The excluded-gap estimate in Section 4.6. All selected vertices of
one actual cutoff gap are refined together; the per-vertex price is
absorbed by the normalized excess of unbalanced vertices. -/
theorem eventually_excluded_gap_power_bound : ∀ᶠ u : ℝ in atTop,
    ∀ φ : ℝ → ℝ, ∀ P κ y A : ℝ, ∀ start k : ℕ, ∀ t : ScheduleTree, ∀ eligible : ℕ → ℝ → Bool,
    StrictMono φ → 0 < P → 0 ≤ κ → φ 0 ≤ 0 → 0 ≤ A →
    φ A = P+Real.exp (y-(k:ℝ)*Real.log rho) → k ≤ fourPhaseDepth u+2 → t.Cartesian →
    φ t.rootStep ≤ P+Real.exp y →
    (∀ j : ℕ, ∀ b ∈ t.word, A < b → eligible j b = true) →
    ((labels (indexedHeightWindow φ P (y-(k:ℝ)*Real.log rho) start κ t)).map (normalizedNodeDecrease φ P)).sum ≤
      splitCoefficient*gapSavingsMaximum φ P κ (2400/u) start t.word eligible+
        (76800*splitCoefficient)*(2:ℝ)^fourPhaseDepth u/u := by
  obtain ⟨c,hc,hcharge⟩ := window_excess_bad_charge
  have hC : 0 ≤ 76800*splitCoefficient := mul_nonneg (by norm_num) split_coefficient_positive.le
  filter_upwards [eventually_band_window_forest_count,eventually_band_forest_spacing,
    eventually_band_per_vertex_absorption hC hc,eventually_gt_atTop (0:ℝ)] with u hCount hSpacing hSmall hu
  intro φ P κ y A start k t eligible hφ hP hκ hzero hA hcut hk ht hupper hEligible
  let V := indexedHeightWindow φ P (y-(k:ℝ)*Real.log rho) start κ t
  let bad := badNodeCount (rootGood (nodeBalancedBool φ P (bandTolerance u))) V
  let M : ℝ := 32*(2:ℝ)^fourPhaseDepth u
  let price : ℝ := splitCoefficient*(2400/u)
  have hNat := hCount φ P κ y start k t hφ.monotone hP hκ hzero hk ht hupper
  have hReal : (V.numNodes:ℝ) ≤ M*((bad:ℝ)+1) := by
    dsimp only [V,bad,M]
    dsimp only at hNat
    exact_mod_cast hNat
  have hE := hcharge φ P κ (y-(k:ℝ)*Real.log rho) (bandTolerance u) start t hφ.monotone hP hκ hzero
    hSpacing.1 (hSpacing.2.1.trans (by norm_num)) ht
  have hPrice : 0 ≤ price := mul_nonneg split_coefficient_positive.le (by positivity)
  have hSmall' : price*M ≤ c*(bandTolerance u)^2 := by
    dsimp only [price,M]
    linear_combination hSmall
  have hAbsorb := finite_forest_price_absorption (Nat.cast_nonneg bad) hPrice hReal hE hSmall'
  have hPower := window_normalized_power_bound (price := 2400/u) hφ hP hκ (hzero.trans hP.le) hA hcut start t ht eligible hEligible
  change ((labels V).map (normalizedNodeDecrease φ P)).sum ≤ _
  dsimp only [V,bad,M,price] at hAbsorb hPower ⊢
  linear_combination hPower+hAbsorb

end
end StrongSilver
