-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandProtectedWindowSums
import StrongSilver.OriginalPowerWindow

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
set_option maxHeartbeats 4200000

theorem cutPower_nonnegative (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (C : ScheduleCut) :
    0 ≤ cutPower φ P κ C := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hx
  exact (Real.rpow_pos_of_pos (cutMasses_positive φ hP hκ C m hm) _).le

theorem eventually_protectedBand_order : ∀ᶠ u : ℝ in atTop, outerBandLow u ≤ protectedBandHigh u := by
  have hspacing := visibilitySpacing_positive
  filter_upwards [eventually_ge_atTop ((3*visibilitySpacing)^2),eventually_ge_atTop (0:ℝ)] with u hu hu0
  have hs : 3*visibilitySpacing ≤ Real.sqrt u := by
    apply (Real.le_sqrt (by positivity : 0 ≤ 3*visibilitySpacing) hu0).mpr
    exact hu
  have hr := zero_lt_one.trans bandRatio_bounds.1
  have hd : u/bandRatio ≤ u := by
    apply (div_le_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_left bandRatio_bounds.1.le hu0
    simpa only [mul_one] using hh
  dsimp only [outerBandLow,protectedBandHigh,outerBandHigh]
  linarith only [hs,hd,Real.sqrt_nonneg u]

/-- The signed power jumps on the protected actual window telescope
with both endpoints included according to the full-cut convention. -/
theorem band_protected_power_difference {κ B μ u : ℝ} {h : List ℝ}
    (hB : 0 ≤ B) (hμ : 0 < μ) (hcap : μ*B < 1) (horder : outerBandLow u ≤ protectedBandHigh u)
    (hbranch : ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
      cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y) :
    ((bandProtectedNodes κ B μ u h).map fun q => paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source).sum =
      bandSignedPower κ B μ u (protectedBandHigh u) h-bandSignedPower κ B μ u (outerBandLow u) h := by
  rw [band_protected_window_sum κ B μ u h (fun q => paddedRootDecrease (cappedStep μ B) (bandPad u) q.2 q.1)]
  rw [original_power_window_difference (P := bandPad u) (κ := κ)
    (by simp only [cappedStep,if_pos hB,logarithmicStep_zero]) (Real.exp_pos _)
    (cartesian h) (capped_map_cartesian hμ hB hcap (cartesian_valid h)) _ _ horder]
  have hhi : protectedBandHigh u ≤ outerBandHigh u := by
    unfold protectedBandHigh
    linarith only [visibilitySpacing_positive]
  have hcutlo := band_heightCut_eq hμ hcap (hbranch _ ⟨le_rfl,horder.trans hhi⟩) h
  have hcuthi := band_heightCut_eq hμ hcap (hbranch _ ⟨horder,hhi⟩) h
  rw [cartesian_word,hcutlo,hcuthi]
  rfl

end
end StrongSilver
