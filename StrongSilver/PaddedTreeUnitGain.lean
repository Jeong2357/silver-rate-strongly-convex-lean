-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UnitOffsetPowerDecrease
import StrongSilver.PaddedNodeDrawdown

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3600000

theorem paddedInput_pad (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) : (paddedInput φ hP hκ hzero t hroot).pad = P := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r => rfl

theorem paddedInput_reserve (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) : (paddedInput φ hP hκ hzero t hroot).reserve = κ := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r => rfl

/-- The offset-one logarithm is exactly the root gain used in the
actual Cartesian group trajectory construction. -/
theorem paddedInput_unitGain (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0)
    (t : ScheduleTree) (hroot : P < φ t.rootStep) :
    (paddedInput φ hP hκ hzero t hroot).unitOffsetGain = rootGain φ t := by
  cases t with
  | leaf hw => exact False.elim (not_lt_of_ge (hzero.trans hP.le) hroot)
  | split l b r =>
    simp only [paddedInput,PaddedSplitInput.unitOffsetGain,splitGain,rootGain,adjustedExcess,gapDrawdown,
      prefixMass,transformedWord,word,List.map_append,List.map_cons]

theorem padded_balanced_unit_power {φ : ℝ → ℝ} {P δ : ℝ} {t : ScheduleTree}
    (hP : 1 ≤ P) (hzero : φ 0 ≤ 0) (hsmall : P ≤ (φ t.rootStep-P)/4)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (hb : PaddedBalanced φ P 0 δ t) :
    paddedRootDecrease φ P 0 t ≤
      splitCoefficient*Real.exp (nu*nodeHeight φ P (t,0))*rootGain φ t+
      splitCoefficient*δ*Real.exp (nu*nodeHeight φ P (t,0))*|rootGain φ t|+
      16*splitCoefficient*Real.exp (nu*nodeHeight φ P (t,0))*(P/(φ t.rootStep-P)) := by
  have hP0 := zero_lt_one.trans_le hP
  let S := paddedInput φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive
  have hpad : 1 ≤ S.pad := by rw [paddedInput_pad]; exact hP
  have hsize : S.pad ≤ S.t/4 := by rw [paddedInput_pad,paddedInput_time]; exact hsmall
  have hres : S.reserve = 0 := paddedInput_reserve φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive δ).mpr hb
  have hh := PaddedSplitInput.unit_offset_power_decrease hpad hsize hres hδ hδmax hbal
  rwa [paddedInput_decrease,paddedInput_height_weight,paddedInput_unitGain,paddedInput_pad,paddedInput_time] at hh

theorem padded_balanced_unit_gain_error {φ : ℝ → ℝ} {P δ : ℝ} {t : ScheduleTree}
    (hP : 1 ≤ P) (hzero : φ 0 ≤ 0) (hsmall : P ≤ (φ t.rootStep-P)/4)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4) (hb : PaddedBalanced φ P 0 δ t) :
    |rootGain φ t-paddedRootGain φ P 0 t| ≤
      2*nodeLeftDrawdown φ t/(φ t.rootStep-P)+8*P/(φ t.rootStep-P) := by
  have hP0 := zero_lt_one.trans_le hP
  let S := paddedInput φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive
  have hpad : 1 ≤ S.pad := by rw [paddedInput_pad]; exact hP
  have hsize : S.pad ≤ S.t/4 := by rw [paddedInput_pad,paddedInput_time]; exact hsmall
  have hres : S.reserve = 0 := paddedInput_reserve φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP0 (le_refl (0:ℝ)) hzero t hb.root_positive δ).mpr hb
  have hh := PaddedSplitInput.unit_offset_original_gain_error hpad hsize hres hδ hδmax hbal
  rwa [paddedInput_unitGain,paddedInput_gain,paddedInput_left_drawdown,paddedInput_pad,paddedInput_time] at hh

end
end StrongSilver.ScheduleTree
