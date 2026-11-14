-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialFiniteCompressedPower
import StrongSilver.InitialCountAbsorption
import StrongSilver.InitialBandLogCharge
import StrongSilver.StrictQuarterCurvature

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 3000000

/-- Near-cutoff initial power on the tracked schedule, with one curvature
and one reservation fixed before varying the cutoff. -/
theorem eventually_near_initial_compressed_power {a : ℝ} (ha : 0 < a) (hamax : a ≤ 1/128)
    (htrack : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (herror : 2*splitCoefficient*initialStableErrorCoefficient a ≤ powerLogMinimum/16) :
    ∀ᶠ B : ℝ in atTop, ∀ κ : ℝ, ∀ h : List ℝ,
      1 < κ → B ≤ a*κ → κ^(1-initialPowerEpsilon) ≤ B →
      weightedCount h (a*κ) = (countAbove h B : ℝ)*B^nu → D κ h ≤ 1 →
      ∃ μ : ℝ, ∃ R : InitialReservation κ B μ (closedCut B h),
        1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
        inverseChargeAbove (κ/4) h μ ≤ 34*(countAbove h (κ/4) : ℝ) ∧
        ∀ A : ℝ, B^(1-initialPowerXi) ≤ A → A < B →
          (powerLogMinimum/8)*weightedCount h (a*κ) ≤
            cutPower (cappedStep μ B) (B^((987 : ℝ)/1000)) 0 (fullCut A R.compressedSchedule)-
              (B^((987 : ℝ)/1000))^nu := by
  have hξ1 : initialPowerXi < 1 := initialPowerXi_upper.trans_lt (by norm_num)
  have hfloorEscape := tendsto_rpow_atTop (sub_pos.mpr hξ1)
  filter_upwards [hfloorEscape.eventually (eventually_all_larger eventually_initial_finite_compressed_power),
    hfloorEscape.eventually (eventually_ge_atTop (4 : ℝ)),eventually_ge_atTop (2 : ℝ),
    eventually_initial_band_pad_margin (initialPowerXi_upper.trans (by norm_num)),eventually_initial_count_loss_small]
    with B hfactory hfloor4 hB hmargin hcountSmall
  intro κ h hκ hBcap hnear hmax hD
  have hκ0 := zero_lt_one.trans hκ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB
  have hBκ : B ≤ κ/4 := by
    have hh := mul_le_mul_of_nonneg_right hamax hκ0.le
    nlinarith only [hh,hBcap,hκ0]
  let C := closedCut B h
  have hword : C.word = h := cutSchedule_word _ _
  have hpiv : ∀ q ∈ C.phases, B ≤ q.pivot := fun _ hq => closedCut_pivot hq
  have hgap : ∀ b ∈ C.unselected, b < B := fun _ hb => closedCut_unselected hb
  have hgapPositive : ∀ b ∈ C.unselected, 0 < b → b ≤ B := fun b hb _ => (hgap b hb).le
  have hgapPhase : ∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ B :=
    fun q hq b hb => hgapPositive b (ScheduleCut.mem_gap_unselected hq hb)
  obtain ⟨μ,hμ,hμu,hcrit,hcharge,hquarter⟩ := exists_strict_common_curvature_with_quarter_bound hκ0 h
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hκμ := (le_div_iff₀ (show 0 < 8*κ by positivity)).mp hμu
  have hmB := mul_le_mul_of_nonneg_left hBκ hμ0.le
  have hμB : μ*B ≤ 1/2 := by nlinarith only [hκμ,hmB]
  have hlargeCount := C.strictLarge_le_initial_marked hκ0 (show B < κ/2 by linarith only [hBκ,hκ0]) hgapPositive
  rw [hword] at hlargeCount
  have hlargeReal : ((strictLargeSteps κ h).length : ℝ) ≤ (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by exact_mod_cast hlargeCount
  have hlarge : largeInverseCharge κ C.word μ ≤ 32*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by
    rw [hword]
    linear_combination hcharge+32*hlargeReal
  obtain ⟨R⟩ := nonempty_initial_reservation hκ.le hB hBκ hμ hμu C hpiv hgapPhase
  have hmaxC : weightedCount C.word (a*κ) = (C.phases.length : ℝ)*B^nu := by
    simpa only [hword,C,closedCut_count] using hmax
  refine ⟨μ,R,hμ,hμu,hcrit,hquarter,?_⟩
  intro A hfloor hAB
  have hA0 : 0 < A := (Real.rpow_pos_of_pos hB0 (1-initialPowerXi)).trans_le hfloor
  have hκA := near_initial_band_kappa_bound hB1.le hκ0 (by norm_num [initialPowerEpsilon]) hnear hfloor initialPower_near_scale
  have hpad : ∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ B^((987 : ℝ)/1000) ∧
      B^((987 : ℝ)/1000) ≤ t^((199 : ℝ)/200) :=
    fun t hAt htB => initial_band_pad_bounds hB1.le initialPowerXi_positive.le
      (initialPowerXi_upper.trans (by norm_num)) (hfloor.trans hAt) htB
  have hpower := hfactory A hfloor a κ B μ (B^((987 : ℝ)/1000)) C R ha hamax
    (show 1 ≤ a*κ by linarith only [hB,hBcap]) hAB hB hBcap hκA hκ.le hμ hμu hμB hpad
    (hmargin.trans hfloor) hpiv hgap (by simpa only [hword] using hcrit) (by simpa only [hword] using hD) hlarge htrack hmaxC
  rw [hword] at hpower
  have hlogCharge := initial_band_selected_log_charge hB1 hξ1 hfloor hAB.le
  have hW := weightedCount_nonneg h (a*κ)
  have hc := split_coefficient_positive
  have hfee := mul_le_mul_of_nonneg_left hlogCharge (show 0 ≤ 4*splitCoefficient*weightedCount h (a*κ) by positivity)
  have hcountFee := mul_le_mul_of_nonneg_left hcountSmall hW
  have herrorFee := mul_le_mul_of_nonneg_left herror hW
  linear_combination hpower+hfee+hcountFee+herrorFee

end
end StrongSilver
