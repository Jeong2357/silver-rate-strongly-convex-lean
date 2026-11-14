-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LongVisibilityBudget
import StrongSilver.BandIntegralEstimates

namespace StrongSilver
open ScheduleTree ParentedScheduleNode Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5200000

def bandLongVisibleNodes (κ B μ u s : ℝ) (h : List ℝ) : List ParentedScheduleNode :=
  longVisibleNodes (cappedStep μ B) (bandPad u) κ (outerBandLow u) (outerBandHigh u) s (bandEligible μ B u) (cartesian h)

/-- The visibility estimate uses the same transformed signed schedule,
curvature and cutoff window as the proved full-band integral bound. -/
theorem band_long_visibility_bound {κ B cap μ u s : ℝ} {h : List ℝ}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hμ : 0 < μ) (hcap : μ*B < 1) (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hbranch : ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
      cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y)
    (H : BandIntegralBounds κ B cap μ u h) :
    visibilityWindowFactor nu s*((bandLongVisibleNodes κ B μ u s h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*
        visibleNodeScore (cappedStep μ B) (bandPad u) (2400/u) (bandEligible μ B u) q.node).sum ≤
      nu*bandIntegralConstant*weightedCount h cap := by
  let a := outerBandLow u
  let b := outerBandHigh u
  let φ := cappedStep μ B
  let P := bandPad u
  let R := fun y => bandRefinementSavings κ B μ u y h
  let L := fun y => bandSignedLog κ B μ u y h
  let S := fun y => bandPositiveLog κ B μ u y h
  let F := fun y => Real.exp (nu*y)*
    (totalGapSavingsMaximum φ P κ (2400/u) (bandEligible μ B u) (heightCut φ P y (cartesian h).word)+
      (cutLogProduct (positivePartStep φ) P κ (heightCut φ P y (cartesian h).word)-
        cutLogProduct φ P κ (heightCut φ P y (cartesian h).word)))
  let G := fun y => Real.exp (nu*y)*R y+(Real.exp (nu*y)*S y-Real.exp (nu*y)*L y)
  let Z := fun y => max (Real.exp (nu*y)*S y) 0+Real.exp (nu*y)*R y+
    (Real.exp (nu*y)*S y-Real.exp (nu*y)*L y)
  have hab : a ≤ b := outerBand_order hu
  have hR := bandRefinementSavings_weighted_integrable κ B μ u a b h
  have hL := bandSignedLog_weighted_integrable κ B μ u a b h
  have hS := bandPositiveLog_weighted_integrable κ B μ u a b h
  have hG : IntervalIntegrable G volume a b := hR.add (hS.sub hL)
  have hFG : ∀ y ∈ Icc a b, F y = G y := by
    intro y hy
    have hcut := band_heightCut_eq hμ hcap (hbranch y hy) h
    dsimp only [F,G,R,L,S,φ,P]
    rw [cartesian_word,hcut]
    unfold bandRefinementSavings bandPositiveLog bandSignedLog
    ring
  have hF : IntervalIntegrable F volume a b := hG.congr_uIoo (by
    intro y hy
    rw [uIoo_of_le hab] at hy
    exact (hFG y ⟨hy.1.le,hy.2.le⟩).symm)
  have hZ : IntervalIntegrable Z volume a b := by
    exact ((intervalIntegrable_positive_part hS).add hR).add (hS.sub hL)
  have hInt := long_visibility_integral_budget φ (cappedStep_monotone hμ hcap) (Real.exp_pos _) hκ hs hab
    (by dsimp only [φ]; simp only [cappedStep,if_pos hB,logarithmicStep_zero,le_refl])
    (2400/u) (bandEligible μ B u) (cartesian h) (cartesian_valid h) hF
  have heq : (∫ y in a..b, F y) = ∫ y in a..b, G y := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro y hy
    exact hFG y ⟨hy.1.le,hy.2.le⟩
  have hCompare := intervalIntegral.integral_mono_on hab hG hZ (by
    intro y hy
    have hz : 0 ≤ max (Real.exp (nu*y)*S y) 0 := le_max_right _ _
    dsimp only [G,Z]
    linarith only [hz])
  have hUpper : (∫ y in a..b, Z y) ≤ bandIntegralConstant*weightedCount h cap := H.all_gap_upper
  change _ ≤ nu*(∫ y in a..b, F y) at hInt
  rw [heq] at hInt
  have h1 := mul_le_mul_of_nonneg_left (hCompare.trans hUpper) nu_positive.le
  exact hInt.trans (by simpa only [mul_assoc] using h1)

end
end StrongSilver
