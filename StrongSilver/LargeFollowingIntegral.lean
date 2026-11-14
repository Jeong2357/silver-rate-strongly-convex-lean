-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LargeFollowingCount
import StrongSilver.BandBinGeometry

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5800000

theorem largeFollowingObservable_integrable (φ : ℝ → ℝ) (hφ : Monotone φ) (P κ v width a b : ℝ)
    (hwidth : 0 ≤ width) (h : List ℝ) :
    IntervalIntegrable (largeFollowingObservable φ P κ v width h) volume a b := by
  let ψ := fun x => P+(φ x-P)/Real.exp width
  have he : largeFollowingObservable φ P κ v width h =
      selectedNodeObservable ψ P v (fun _ => 1) (labels ((cartesian h).indexedTree 0 κ)) := by
    funext y
    rw [largeFollowingObservable_eq φ hφ P κ v width hwidth h y]
    unfold selectedNodeObservable
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    have hh : P+Real.exp (y+width) < φ q.pivot ↔ P+Real.exp y < ψ q.pivot := by
      dsimp only [ψ]
      rw [Real.exp_add]
      constructor
      · intro hh
        have hdiv : Real.exp y < (φ q.pivot-P)/Real.exp width :=
          (lt_div_iff₀ (Real.exp_pos width)).mpr (by linarith only [hh])
        linarith only [hdiv]
      · intro hh
        have hdiv : Real.exp y < (φ q.pivot-P)/Real.exp width := by linarith only [hh]
        have hmul := (lt_div_iff₀ (Real.exp_pos width)).mp hdiv
        linarith only [hmul]
    simp only [hh]
    split_ifs <;> simp
  rw [he]
  exact selectedNodeObservable_integrable ψ P v a b (fun _ => 1) _

/-- Uniform weighted integral of the large-following-pivot exclusion,
with the fixed paper choice gamma=1/100 and width=gamma*log(u)/2. -/
theorem eventually_band_large_following_integral : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ a b : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 → a ≤ b →
    outerBandLow u ≤ a → b+Real.log u/200 ≤ outerBandHigh u →
    (∫ y in a..b, largeFollowingObservable (cappedStep μ B) (bandPad u) κ nu (Real.log u/200) h y) ≤
      4*weightedCount h cap*u^(1-nu/200) := by
  filter_upwards [eventually_band_large_following_count,eventually_band_bin_geometry,
    eventually_sqrt_affine_le_linear (by norm_num : (0:ℝ) < 1) 4 0,eventually_ge_atTop (1:ℝ)]
    with u hPoint hGeometry hSqrt hu
  intro κ B cap μ a b h hB hBcap hU hμ hμB hab ha hb
  have hu0 := zero_lt_one.trans_le hu
  have hWidth : 0 ≤ Real.log u/200 := div_nonneg (Real.log_nonneg hu) (by norm_num)
  have hφ := cappedStep_monotone (B:=B) hμ (by linarith only [hμB])
  have hEach (y : ℝ) (hy : y ∈ Icc a b) :
      largeFollowingObservable (cappedStep μ B) (bandPad u) κ nu (Real.log u/200) h y ≤
        2*weightedCount h cap*Real.exp (-nu*(Real.log u/200)) := by
    apply hPoint κ B cap μ y (Real.log u/200) h hB hBcap hU hμ hμB hWidth
    constructor <;> linarith only [ha,hb,hy.1,hy.2,hWidth]
  have hInt := intervalIntegral.integral_mono_on hab
    (largeFollowingObservable_integrable (cappedStep μ B) hφ (bandPad u) κ nu (Real.log u/200) a b hWidth h)
    intervalIntegrable_const hEach
  rw [intervalIntegral.integral_const,smul_eq_mul] at hInt
  have hHigh : outerBandHigh u ≤ 2*u := by unfold outerBandHigh; linarith only [hSqrt]
  have hLow : 0 ≤ outerBandLow u := (by norm_num : (0:ℝ) ≤ 1).trans hGeometry.1
  have hLen : b-a ≤ 2*u := by linarith only [ha,hb,hHigh,hLow,hWidth]
  have hCoeff : 0 ≤ 2*weightedCount h cap*Real.exp (-nu*(Real.log u/200)) := by
    have hW := weightedCount_nonneg h cap
    positivity
  have hLength := mul_le_mul_of_nonneg_right hLen hCoeff
  have hExp : Real.exp (-nu*(Real.log u/200)) = u^(-nu/200) := by
    rw [Real.rpow_def_of_pos hu0]
    congr 1
    ring
  have hPow : u*u^(-nu/200) = u^(1-nu/200) := by
    rw [show 1-nu/200 = 1+(-nu/200) by ring,Real.rpow_add hu0,Real.rpow_one]
  rw [hExp] at hInt hLength
  have hFinal := hInt.trans hLength
  convert hFinal using 1 <;> first | rfl | (rw [← hPow]; ring)

end
end StrongSilver
