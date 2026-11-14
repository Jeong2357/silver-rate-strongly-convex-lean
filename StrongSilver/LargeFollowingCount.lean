-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingIntegral
import StrongSilver.TransformedPivotRank
import StrongSilver.BandFrontierMassBudget

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 6000000

def largeFollowingObservable (φ : ℝ → ℝ) (P κ v width : ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  linkedFollowingObservable φ P κ v (fun q => if P+Real.exp (y+width) < φ q.pivot then 1 else 0) h y

/-- A large following pivot is already selected. Thus its gap count is
exactly the corresponding indexed original pivot count. -/
theorem largeFollowingObservable_eq (φ : ℝ → ℝ) (hφ : Monotone φ) (P κ v width : ℝ)
    (hwidth : 0 ≤ width) (h : List ℝ) (y : ℝ) :
    largeFollowingObservable φ P κ v width h y =
      Real.exp (v*y)*((labels ((cartesian h).indexedTree 0 κ)).map fun q =>
        if P+Real.exp (y+width) < φ q.pivot then (1:ℝ) else 0).sum := by
  rw [largeFollowingObservable,linkedFollowingObservable_eq φ hφ]
  unfold selectedNodeObservable
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro q _
  by_cases hh : P+Real.exp (y+width) < φ q.pivot
  · have hs : P+Real.exp y < φ q.pivot := by
      have he := Real.exp_le_exp.mpr (show y ≤ y+width by linarith only [hwidth])
      linarith only [he,hh]
    simp only [if_pos hh,if_pos hs,mul_one]
  · simp only [if_neg hh,mul_zero,ite_self]

/-- Pointwise rank estimate for the large-following-pivot exclusion in
(4.25). The shifted cutoff lies in the actual outer window. -/
theorem eventually_band_large_following_count : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y width : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 → 0 ≤ width →
    y+width ∈ Icc (outerBandLow u) (outerBandHigh u) →
    largeFollowingObservable (cappedStep μ B) (bandPad u) κ nu width h y ≤
      2*weightedCount h cap*Real.exp (-nu*width) := by
  filter_upwards [eventually_outer_band_log_window] with u hWindow
  intro κ B cap μ y width h hB hBcap hU hμ hμB hwidth hy
  have W := hWindow B μ (y+width) hB hU hμ hμB hy
  have hsize := logarithmicCutoff_size hμ (show (0:ℝ) ≤ bandPad u by exact (Real.exp_pos _).le) W.2.1
  have hη := firstAverageEta_bounds.1
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAcut : logarithmicCutoff μ (bandPad u) (y+width) ≤ cap :=
    (W.2.2.2.2.2.2.2.2.1.trans hBpower).trans hBcap
  have hAcap : Real.exp (y+width)/2 ≤ cap := by
    have hp := Real.exp_pos ((987:ℝ)/1000*u)
    change 0 < bandPad u at hp
    linarith only [hsize.1,hAcut,hp]
  have hRank := transformed_pivot_rank (κ:=κ) hμ (zero_lt_one.trans hB) hμB
    (show (0:ℝ) ≤ bandPad u by exact (Real.exp_pos _).le) hAcap h
  have hm := mul_le_mul_of_nonneg_left hRank (Real.exp_pos (-nu*width)).le
  have hExp : Real.exp (-nu*width)*Real.exp (nu*(y+width)) = Real.exp (nu*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc,hExp] at hm
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  rw [largeFollowingObservable_eq (cappedStep μ B) hφ _ _ _ _ hwidth]
  exact hm.trans_eq (by ring)

end
end StrongSilver
