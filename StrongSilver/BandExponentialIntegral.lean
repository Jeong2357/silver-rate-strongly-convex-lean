-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandTopFrontier
import StrongSilver.ExponentialStepIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 4400000

theorem indexedFrontier_length_ge_one (φ : ℝ → ℝ) (s : ℝ) (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    (1:ℝ) ≤ ((indexedFrontier φ s start κ t).length:ℝ) := by
  have hNonempty := linkedFrontier_nonempty φ s start κ none none t
  have hPositive : 0 < (linkedFrontier φ s start κ none none t).length := List.length_pos_iff.mpr hNonempty
  have hLength := congrArg List.length (linkedFrontier_erase φ s start κ none none t)
  rw [List.length_map] at hLength
  have hNat : 1 ≤ (indexedFrontier φ s start κ t).length := by omega
  exact_mod_cast hNat

/-- The one unmatched terminal pair costs O(W) in the cutoff integral. -/
theorem eventually_band_exponential_integral : ∀ᶠ u : ℝ in atTop,
    ∀ B cap μ a b : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 → a ≤ b →
    b ∈ Icc (outerBandLow u) (outerBandHigh u) → 1 ≤ countAbove h B →
    (∫ y in a..b, Real.exp (nu*y)) ≤ (4/nu)*weightedCount h cap := by
  filter_upwards [eventually_band_top_frontier] with u H
  intro B cap μ a b h hB hBcap hU hμ hμB hab hb hcount
  have hTop := H 0 B cap μ b h hB hBcap hU hμ hμB hb hcount
  have hN := indexedFrontier_length_ge_one (cappedStep μ B) (bandPad u+Real.exp b) 0 0 (cartesian h)
  have hMul := mul_le_mul_of_nonneg_left hN (Real.exp_pos (nu*b)).le
  simp only [mul_one] at hMul
  dsimp only [bandIndexedFrontier] at hTop
  have hExp := scaled_exponential_integral nu a b
  have hBound : nu*(∫ y in a..b, Real.exp (nu*y)) ≤ 4*weightedCount h cap := by
    linear_combination hExp+hMul+hTop+(Real.exp_pos (nu*a)).le
  calc
    _ ≤ (4*weightedCount h cap)/nu := (le_div_iff₀ nu_positive).mpr (by linear_combination hBound)
    _ = (4/nu)*weightedCount h cap := by ring

end
end StrongSilver
