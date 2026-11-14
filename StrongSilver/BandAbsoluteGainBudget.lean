-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandProtectedPower
import StrongSilver.ProtectedExcessBudget
import StrongSilver.FiniteSignedGainBudget

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
set_option maxHeartbeats 6200000

/-- Both absolute sums in (4.13) on the actual protected band. The
positive gain, endpoint power and excess budgets are all derived from
the original stable signed schedule. -/
theorem eventually_band_absolute_gain_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 →
    (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    1 ≤ countAbove h B → κ^nu ≤ weightedCount h cap →
    ((bandProtectedNodes κ B μ u h).map fun q =>
      Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)*
        |paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source|).sum+
    ((bandProtectedNodes κ B μ u h).map fun q =>
      |paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source|).sum ≤ C*weightedCount h cap := by
  obtain ⟨Cg,hCg,hpositive⟩ := eventually_band_positive_gain_budget
  let C := (1+splitCoefficient)*(2*Cg+bandPowerUpperConstant/splitCoefficient)+bandExcessConstant
  have hC : 0 < C := by
    have hc := split_coefficient_positive
    have hE := bandExcessConstant_positive
    have hden : 0 < 1-nu := by linarith only [nu_lt_one]
    have hPower : 0 < bandPowerUpperConstant := by unfold bandPowerUpperConstant; positivity
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hpositive,eventually_band_integral_estimates,eventually_band_pointwise_bounds,
    eventually_outer_band_log_window,eventually_protectedBand_order,eventually_ge_atTop (0:ℝ)]
    with u hPositive hInt hPoint hWindow hOrder hu
  intro κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hκ0 := zero_lt_one.trans hκ
  have hB0 := zero_lt_one.trans hB
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hcap1 : μ*B < 1 := by linarith only [hμB]
  have hzero : cappedStep μ B 0 ≤ 0 := by simp only [cappedStep,if_pos hB0.le,logarithmicStep_zero,le_refl]
  have HInt := hInt κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have HPositive := hPositive κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have HPoint := hPoint κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD hcount hκW
  have hOuterOrder := outerBand_order hu
  have hbranch : ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
      cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y := by
    intro y hy
    exact (hWindow B μ y hB hU hμ0 hμB hy).2.2.2.2.2.2.2.2.2.2
  let qs := bandProtectedNodes κ B μ u h
  let w := fun q : ParentedScheduleNode => Real.exp (nu*parentedHeight (cappedStep μ B) (bandPad u) q)
  let g := fun q : ParentedScheduleNode => paddedRootGain (cappedStep μ B) (bandPad u) q.node.reserve q.node.source
  let E := fun q : ParentedScheduleNode => nodeExcess (cappedStep μ B) (bandPad u) (q.node.source,q.node.reserve)
  let Δ := fun q : ParentedScheduleNode => paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source
  have hExcess := protected_excess_le_window (φ := cappedStep μ B) (P := bandPad u) (a := outerBandLow u) (b := outerBandHigh u) (Real.exp_pos _) hκ0.le hzero (bandEligible μ B u) (cartesian h)
  rw [band_windowNodeExcess_sum hκ0.le hB0.le] at hExcess
  have hEUpper : (qs.map E).sum ≤ bandExcessConstant*weightedCount h cap := hExcess.trans HInt.excess_upper
  have hENonneg : ∀ q ∈ qs, 0 ≤ E q := by
    intro q hq
    have hh := of_decide_eq_true (List.mem_filter.mp hq).2
    exact nodeExcess_nonnegative (cappedStep μ B) (Real.exp_pos _)
      (parentedNodes_reserve_nonnegative hκ0.le (List.mem_filter.mp hq).1) hzero q.node.source hh.1
  have hΔ (q : ParentedScheduleNode) : Δ q = splitCoefficient*w q*g q-E q := by
    dsimp only [Δ,w,g,E,nodeExcess,parentedHeight]
    ring
  have HPower := band_protected_power_difference (κ := κ) (h := h) hB0.le hμ0 hcap1 hOrder hbranch
  have hPowerLower : 0 ≤ bandSignedPower κ B μ u (protectedBandHigh u) h :=
    cutPower_nonnegative (cappedStep μ B) (Real.exp_pos _) hκ0.le _
  have hLow := HPoint (outerBandLow u) ⟨le_rfl,hOuterOrder⟩
  have hPowerUpper := hLow.power_order.trans hLow.positive_power_upper
  have hPower : -(bandPowerUpperConstant*weightedCount h cap) ≤ (qs.map Δ).sum := by
    change _ ≤ ((bandProtectedNodes κ B μ u h).map fun q => paddedRootDecrease (cappedStep μ B) (bandPad u) q.node.reserve q.node.source).sum
    rw [HPower]
    linarith only [hPowerLower,hPowerUpper]
  have H := finite_absolute_gain_budget qs w g E Δ (Cg*weightedCount h cap)
    (bandPowerUpperConstant*weightedCount h cap) (bandExcessConstant*weightedCount h cap)
    (fun _ _ => (Real.exp_pos _).le) hENonneg (fun q _ => hΔ q) HPositive hPower hEUpper
  change (qs.map fun q => w q*|g q|).sum+(qs.map fun q => |Δ q|).sum ≤ _
  dsimp only [C]
  linear_combination H.1+H.2

end
end StrongSilver
