-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BadRootParentCount
import StrongSilver.BandTopFrontier

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set MeasureTheory
noncomputable section
set_option maxHeartbeats 6000000

/-- Integrated bad-root/bad-parent exclusion count in (4.25), with
both boundary-frontier and unavailable-parent costs discharged. -/
theorem eventually_band_bad_root_parent : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical a b : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → a ≤ b → outerBandLow u < a →
    b+3*visibilitySpacing ≤ outerBandHigh u →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    (∫ y in a..b, badRootParentObservable κ B μ u h y) ≤ C*weightedCount h cap*u^((9:ℝ)/10) := by
  obtain ⟨Cp,hCp,Hp⟩ := eventually_band_parent_exclusions
  refine ⟨Cp+4/nu,by have hν := nu_positive; positivity,?_⟩
  filter_upwards [Hp,eventually_band_top_frontier,eventually_ge_atTop (1:ℝ)] with u hParent hTop hu
  intro κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab ha hb hcrit hcritical hcriticalRank hD hcount hκW
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hφ := cappedStep_monotone (B:=B) hμ0 (by linarith only [hμB])
  have hTopWindow : b ∈ Icc (outerBandLow u) (outerBandHigh u) := by
    constructor
    · exact ha.le.trans hab
    · linarith only [hb,visibilitySpacing_positive]
  have hT := hTop κ B cap μ b h hB hBcap hU hμ0 hμB hTopWindow hcount
  dsimp only [bandIndexedFrontier] at hT
  have hF := frozenFrontierObservable_integral_upper (cappedStep μ B) hφ (bandPad u) κ nu a b h nu_positive.le hab
  have hF' : (∫ y in a..b, frozenFrontierObservable (cappedStep μ B) (bandPad u) κ nu b h y) ≤
      4*weightedCount h cap/nu := by
    apply (le_div_iff₀ nu_positive).mpr
    change _ ≤ _ at hF
    linear_combination hF+hT
  have hP := hParent κ B cap μ critical a b h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hab hcrit hcritical hcriticalRank hD hcount hκW
  have hPoint (y : ℝ) (hy : y ∈ Icc a b) := bad_root_parent_pointwise (κ:=κ) (B:=B) (μ:=μ) (h:=h)
    (ha.trans_le hy.1) hb
  have hI := intervalIntegral.integral_mono_on hab
    (badRootParentObservable_integrable κ B μ u a b h)
    ((frozenFrontierObservable_integrable (cappedStep μ B) (bandPad u) κ nu b a b h).add
      (linkedParentObservable_integrable (cappedStep μ B) (bandPad u) κ nu a b (bandUnavailableIndicator B μ u) h)) hPoint
  rw [intervalIntegral.integral_add
    (frozenFrontierObservable_integrable (cappedStep μ B) (bandPad u) κ nu b a b h)
    (linkedParentObservable_integrable (cappedStep μ B) (bandPad u) κ nu a b (bandUnavailableIndicator B μ u) h)] at hI
  have hPower : (1:ℝ) ≤ u^((9:ℝ)/10) := Real.one_le_rpow hu (by norm_num)
  have hRate := mul_le_mul_of_nonneg_left hPower
    (show 0 ≤ 4*weightedCount h cap/nu by have hW := weightedCount_nonneg h cap; have hν := nu_positive; positivity)
  linear_combination hI+hF'+hP+hRate

end
end StrongSilver
