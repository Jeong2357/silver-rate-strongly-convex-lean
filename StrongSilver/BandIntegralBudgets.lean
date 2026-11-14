-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPointwiseBounds
import StrongSilver.BandObservableIntegrability
import StrongSilver.BandCutTrees

namespace StrongSilver
open Real Filter Set MeasureTheory ScheduleTree
noncomputable section
set_option maxHeartbeats 5200000

def bandEndpointConstant : ℝ := bandLogUpperConstant+bandPowerUpperConstant

def bandExcessConstant : ℝ := splitCoefficient*(bandEndpointConstant+4804)+bandEndpointConstant+9608*splitCoefficient*nu

def bandIntegralConstant : ℝ := 3*bandExcessConstant/(splitCoefficient*nu)+19216

def bandExcessSum (κ B cap μ u : ℝ) (h : List ℝ) : ℝ :=
  (((bandSignedTree μ B h).paddedEvents (bandPad u) κ).map fun q =>
    if outerBandLow u < paddedHeight (bandPad u) q ∧ paddedHeight (bandPad u) q ≤ outerBandHigh u
    then paddedEventExcess (bandPad u) q else 0).sum

structure BandIntegralBounds (κ B cap μ u : ℝ) (h : List ℝ) : Prop where
  excess_upper : bandExcessSum κ B cap μ u h ≤ bandExcessConstant*weightedCount h cap
  positive_log_upper : splitCoefficient*nu*(∫ y in outerBandLow u..outerBandHigh u,
    max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0) ≤ bandExcessConstant*weightedCount h cap
  all_gap_upper : (∫ y in outerBandLow u..outerBandHigh u,
    max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0+
      Real.exp (nu*y)*bandRefinementSavings κ B μ u y h+
      (Real.exp (nu*y)*bandPositiveLog κ B μ u y h-Real.exp (nu*y)*bandSignedLog κ B μ u y h)) ≤
    bandIntegralConstant*weightedCount h cap

/-- The exact Cartesian excess identities are applied to the actual
signed and positive-part transformed schedules. All refined-gap terms
are controlled on the same original cutoff window. -/
theorem band_integral_bounds_of_pointwise {κ B cap μ u : ℝ} {h : List ℝ}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hμ : 0 < μ) (hcap : μ*B < 1) (hu : 1 ≤ u)
    (hlength : outerBandHigh u-outerBandLow u ≤ 2*u)
    (hbranch : ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u),
      cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y)
    (H : ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u), BandCutBounds κ B cap μ u y h) :
    BandIntegralBounds κ B cap μ u h := by
  let a := outerBandLow u
  let b := outerBandHigh u
  let W := weightedCount h cap
  let e := 4804*W/u
  let M := bandEndpointConstant*W
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hW : 0 ≤ W := weightedCount_nonneg h cap
  have hP : 0 < bandPad u := Real.exp_pos _
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hab : a ≤ b := outerBand_order hu0.le
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have hden : 0 < 1-nu := by linarith only [nu_lt_one]
  have hClog : 0 ≤ bandLogUpperConstant := by unfold bandLogUpperConstant; positivity
  have hCpower : 0 ≤ bandPowerUpperConstant := by unfold bandPowerUpperConstant; positivity
  have hLogM : bandLogUpperConstant*W ≤ M := by
    dsimp only [M,bandEndpointConstant]
    have hh := mul_nonneg hCpower hW
    nlinarith only [hh]
  have hPowerM : bandPowerUpperConstant*W ≤ M := by
    dsimp only [M,bandEndpointConstant]
    have hh := mul_nonneg hClog hW
    nlinarith only [hh]
  have hcut (y : ℝ) (hy : y ∈ Icc a b) := band_heightCut_eq hμ hcap (hbranch y hy) h
  have horder (y : ℝ) (hy : y ∈ Icc a b) :=
    mul_le_mul_of_nonneg_left (H y hy).log_order (Real.exp_pos (nu*y)).le
  have hsourceLower (y : ℝ) (hy : y ∈ Icc a b) : -e ≤ Real.exp (nu*y)*bandSignedLog κ B μ u y h := by
    have hh := (H y hy).signed_log_lower
    dsimp only [e,W]
    linear_combination hh
  have hsignedLower (y : ℝ) (hy : y ∈ Icc a b) :
      -e ≤ Real.exp (nu*y)*(cutLogProduct id (bandPad u) κ
        (fullCut (bandPad u+Real.exp y) (bandSignedTree μ B h).word)-Real.log κ) := by
    rw [bandSignedTree_log (hcut y hy)]
    exact hsourceLower y hy
  have hpositiveLower (y : ℝ) (hy : y ∈ Icc a b) :
      -e ≤ Real.exp (nu*y)*(cutLogProduct id (bandPad u) κ
        (fullCut (bandPad u+Real.exp y) (bandPositiveTree μ B h).word)-Real.log κ) := by
    rw [bandPositiveTree_log (hcut y hy)]
    exact (hsourceLower y hy).trans (horder y hy)
  have hsignedUpper : Real.exp (nu*b)*(cutLogProduct id (bandPad u) κ
      (fullCut (bandPad u+Real.exp b) (bandSignedTree μ B h).word)-Real.log κ) ≤ M := by
    rw [bandSignedTree_log (hcut b hb)]
    exact ((horder b hb).trans (H b hb).positive_log_upper).trans hLogM
  have hpositiveUpper : Real.exp (nu*b)*(cutLogProduct id (bandPad u) κ
      (fullCut (bandPad u+Real.exp b) (bandPositiveTree μ B h).word)-Real.log κ) ≤ M := by
    rw [bandPositiveTree_log (hcut b hb)]
    exact (H b hb).positive_log_upper.trans hLogM
  have hsignedPower : cutPower id (bandPad u) κ
      (fullCut (bandPad u+Real.exp a) (bandSignedTree μ B h).word) ≤ M := by
    rw [bandSignedTree_power (hcut a ha)]
    exact ((H a ha).power_order.trans (H a ha).positive_power_upper).trans hPowerM
  have hpositivePower : cutPower id (bandPad u) κ
      (fullCut (bandPad u+Real.exp a) (bandPositiveTree μ B h).word) ≤ M := by
    rw [bandPositiveTree_power (hcut a ha)]
    exact (H a ha).positive_power_upper.trans hPowerM
  have hsigned := cartesian_excess_budgets hP hκ he (bandSignedTree μ B h)
    (bandSignedTree_cartesian hμ hB hcap h) (Real.log κ) a b hab hsignedLower hsignedUpper hsignedPower
  have hpositive := cartesian_excess_budgets hP hκ he (bandPositiveTree μ B h)
    (bandPositiveTree_cartesian hμ hB hcap h) (Real.log κ) a b hab hpositiveLower hpositiveUpper hpositivePower
  have heSmall : e ≤ 4804*W := by
    apply (div_le_iff₀ hu0).mpr
    have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ 4804*W by positivity)
    simpa only [mul_one] using hh
  have heSpan : e*(b-a) ≤ 9608*W := by
    have hh := mul_le_mul_of_nonneg_left hlength he
    have hid : e*(2*u) = 9608*W := by dsimp only [e]; field_simp [hu0.ne'] <;> ring
    rw [hid] at hh
    exact hh
  have hcf : 0 < splitCoefficient*nu := mul_pos split_coefficient_positive nu_positive
  have hBudget : splitCoefficient*(M+e)+M+splitCoefficient*nu*e*(b-a) ≤ bandExcessConstant*W := by
    have h1 := mul_le_mul_of_nonneg_left heSmall split_coefficient_positive.le
    have h2 := mul_le_mul_of_nonneg_left heSpan hcf.le
    dsimp only [M,bandExcessConstant]
    linear_combination h1+h2
  have hSignedE : bandExcessSum κ B cap μ u h ≤ bandExcessConstant*W := hsigned.1.trans hBudget
  have hIntEq : (∫ y in a..b, max (Real.exp (nu*y)*(cutLogProduct id (bandPad u) κ
      (fullCut (bandPad u+Real.exp y) (bandPositiveTree μ B h).word)-Real.log κ)) 0) =
      ∫ y in a..b, max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0 := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab
    intro y hy
    dsimp only
    rw [bandPositiveTree_log (hcut y ⟨hy.1.le,hy.2.le⟩)]
  have hPositive := hpositive.2.trans hBudget
  rw [hIntEq] at hPositive
  have hPositiveReal : (∫ y in a..b, max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0) ≤
      (bandExcessConstant/(splitCoefficient*nu))*W := by
    rw [show bandExcessConstant/(splitCoefficient*nu)*W = bandExcessConstant*W/(splitCoefficient*nu) by ring]
    apply (le_div_iff₀ hcf).mpr
    linear_combination hPositive
  have hGap := integrated_gap_budget hab he (bandSignedLog_weighted_integrable κ B μ u a b h)
    (bandPositiveLog_weighted_integrable κ B μ u a b h) (bandRefinementSavings_weighted_integrable κ B μ u a b h)
    hsourceLower horder (fun y hy => (H y hy).savings_upper) hPositiveReal
  refine ⟨hSignedE,hPositive,?_⟩
  unfold bandIntegralConstant
  change _ ≤ (3*bandExcessConstant/(splitCoefficient*nu)+19216)*W
  linear_combination hGap+2*heSpan

end
end StrongSilver
