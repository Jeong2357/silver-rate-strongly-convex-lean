-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IndexedWindowExactLabels
import StrongSilver.BandForestDepth

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter
noncomputable section
set_option maxHeartbeats 3400000

/-- The actual cutoff-height forest satisfies the O(2^d) node count
used to absorb the per-pivot error in Section 4.6. The depth and tolerance
rounding conditions are discharged uniformly, rather than assumed. -/
theorem eventually_band_window_forest_count : ∀ᶠ u : ℝ in atTop,
    ∀ φ : ℝ → ℝ, ∀ P κ y : ℝ, ∀ start k : ℕ, ∀ t : ScheduleTree,
    Monotone φ → 0 < P → 0 ≤ κ → φ 0 ≤ 0 → k ≤ fourPhaseDepth u+2 → t.Cartesian →
    φ t.rootStep ≤ P+Real.exp y →
    let V := indexedHeightWindow φ P (y-(k:ℝ)*Real.log rho) start κ t
    V.numNodes ≤ 32*2^fourPhaseDepth u*(badNodeCount (rootGood (nodeBalancedBool φ P (bandTolerance u))) V+1) := by
  filter_upwards [eventually_band_forest_spacing] with u H
  intro φ P κ y start k t hφ hP hκ hzero hk hc hupper
  dsimp only
  have hspan : y-(y-(k:ℝ)*Real.log rho) < ((k+2:ℕ):ℝ)*(Real.log rho-11*bandTolerance u) := by
    simpa only [sub_sub_cancel] using H.2.2.2 k hk
  have hh := indexed_height_window_node_bound (start := start) (m := k+2) hφ hP hκ hzero H.1 H.2.1 H.2.2.1 hspan t hc hupper
  have hpow : 2^(k+2+1) ≤ 32*2^fourPhaseDepth u := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k+2+1 ≤ fourPhaseDepth u+5 by omega)
    have he : 2^(fourPhaseDepth u+5) = 32*2^fourPhaseDepth u := by rw [Nat.pow_add]; norm_num <;> ring
    exact hp.trans_eq he
  exact hh.trans (Nat.mul_le_mul_right _ hpow)

end
end StrongSilver
